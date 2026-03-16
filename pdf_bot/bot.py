import os
import json
import csv
import io
import asyncio
import logging
import time
import hashlib
from datetime import datetime
from typing import Dict, Any, List, Optional, Tuple

import requests
from aiogram import Bot, Dispatcher, types
from aiogram.types import (
    ReplyKeyboardMarkup, KeyboardButton,
    InlineKeyboardMarkup, InlineKeyboardButton,
    LabeledPrice
)
from aiogram.utils import executor

from google.oauth2.service_account import Credentials
from googleapiclient.discovery import build


# =========================
# НАСТРОЙКИ
# =========================

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()

# Таблица ТОВАРОВ (публичная, CSV):
PRODUCTS_CSV_URL = "https://docs.google.com/spreadsheets/d/1V1LCKR13JNply4LAEfJBtYNAE854Zr8aBBMTUTC2kPA/gviz/tq?tqx=out:csv"

# Таблица ПОКУПОК (приватная):
PURCHASES_SHEET_ID = os.getenv(
    "PURCHASES_SHEET_ID",
    "1SHhqCUS4c_-vPkaY5R38975RjlRLU0y-RvICQ7zrze0"
).strip()

# JSON сервисного аккаунта целиком, одной строкой, из Railway Variables
GOOGLE_SERVICE_ACCOUNT_JSON = os.getenv("GOOGLE_SERVICE_ACCOUNT_JSON", "").strip()

# Админ и поддержка
ADMIN_CHAT_ID = 8491241832
AUTHOR_USERNAME = "art_kids_support"  # без @

# Telegram Stars
CURRENCY = "XTR"
PROVIDER_TOKEN = ""  # для Stars пусто

# Crypto Pay
CRYPTO_PAY_TOKEN = os.getenv("CRYPTO_PAY_TOKEN", "").strip()
CRYPTO_PAY_BASE_URL = os.getenv("CRYPTO_PAY_BASE_URL", "https://pay.crypt.bot/api").strip()
CRYPTO_PAY_DEFAULT_ASSET = os.getenv("CRYPTO_PAY_DEFAULT_ASSET", "USDT").strip().upper()

# Бесплатная категория (точно как в таблице!)
FREE_CATEGORY_NAME = "🎁 Бесплатные материалы"

# Таймауты
HTTP_TIMEOUT = 15

# Кеши
PRODUCTS_CACHE_TTL = 60
PURCHASES_CACHE_TTL = 60

if not BOT_TOKEN:
    raise RuntimeError("Не задан BOT_TOKEN")


# =========================
# ЛОГИ
# =========================

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("artkids_bot")

logger.info("CRYPTO PAY TOKEN LOADED: %s", bool(CRYPTO_PAY_TOKEN))
logger.info("CRYPTO PAY BASE URL: %s", CRYPTO_PAY_BASE_URL)
logger.info("CRYPTO PAY DEFAULT ASSET: %s", CRYPTO_PAY_DEFAULT_ASSET)

bot = Bot(token=BOT_TOKEN.strip())
dp = Dispatcher(bot)


# =========================
# БЛОКИРОВКИ ПРОТИВ ДВОЙНЫХ ПОКУПОК
# FIX #2: asyncio.Lock на каждую пару user_id:product_id
# =========================

_purchase_locks: Dict[str, asyncio.Lock] = {}
_purchase_locks_meta: Dict[str, float] = {}
_LOCK_TTL = 300  # 5 минут, потом чистим


def _get_purchase_lock(user_id: int, product_id: str) -> asyncio.Lock:
    key = f"{user_id}:{product_id}"
    now = time.time()

    # Чистим старые локи чтобы не росла память
    expired = [k for k, ts in _purchase_locks_meta.items() if now - ts > _LOCK_TTL]
    for k in expired:
        _purchase_locks.pop(k, None)
        _purchase_locks_meta.pop(k, None)

    if key not in _purchase_locks:
        _purchase_locks[key] = asyncio.Lock()
    _purchase_locks_meta[key] = now
    return _purchase_locks[key]


# =========================
# UI: МЕНЮ / КНОПКИ
# =========================

def main_menu() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        resize_keyboard=True,
        keyboard=[
            [KeyboardButton("📚 Каталог")],
            [KeyboardButton("📂 Мои покупки")],
        ]
    )


def help_inline_kb() -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    kb.add(
        InlineKeyboardButton(
            text="✉️ Написать автору",
            url=f"https://t.me/{AUTHOR_USERNAME}"
        )
    )
    return kb


# =========================
# GOOGLE SHEETS API (ПОКУПКИ)
# =========================

_SCOPES = ["https://www.googleapis.com/auth/spreadsheets"]
_sheets_service = None
_purchases_sheet_title: Optional[str] = None


def _build_sheets_service():
    """Синхронная инициализация сервиса — вызывать через run_in_executor."""
    global _sheets_service
    if _sheets_service is not None:
        return _sheets_service

    if not GOOGLE_SERVICE_ACCOUNT_JSON:
        raise RuntimeError("Не задан GOOGLE_SERVICE_ACCOUNT_JSON")

    creds_info = json.loads(GOOGLE_SERVICE_ACCOUNT_JSON)
    creds = Credentials.from_service_account_info(creds_info, scopes=_SCOPES)
    _sheets_service = build("sheets", "v4", credentials=creds, cache_discovery=False)
    return _sheets_service


async def get_sheets_service():
    """FIX #9: асинхронная обёртка — не блокирует event loop."""
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, _build_sheets_service)


async def get_purchases_sheet_title() -> str:
    global _purchases_sheet_title
    if _purchases_sheet_title:
        return _purchases_sheet_title

    service = await get_sheets_service()

    def _get():
        meta = service.spreadsheets().get(spreadsheetId=PURCHASES_SHEET_ID).execute()
        sheets = meta.get("sheets", [])
        if not sheets:
            raise RuntimeError("В таблице покупок нет листов.")
        return sheets[0]["properties"]["title"]

    loop = asyncio.get_event_loop()
    _purchases_sheet_title = await loop.run_in_executor(None, _get)
    return _purchases_sheet_title


# =========================
# ТОВАРЫ (CSV)
# =========================

_products_cache: Tuple[float, List[Dict[str, Any]]] = (0.0, [])


def _to_int(value: Any, default: int = 0) -> int:
    try:
        s = str(value).strip()
        if s == "":
            return default
        return int(s)
    except Exception:
        return default


def _to_str(value: Any, default: str = "") -> str:
    if value is None:
        return default
    return str(value).strip()


def _to_bool(value: Any) -> bool:
    return str(value).strip().lower() in ("true", "1", "yes", "y", "да")


def _to_float_safe(value: Any, default: float = 0.0) -> float:
    """
    FIX #5: безопасное преобразование в float.
    Строки вида "1.5 USDT" не вызывают ValueError — считаются платными.
    """
    if value is None:
        return default
    s = str(value).strip()
    if s == "":
        return default
    try:
        return float(s)
    except (ValueError, TypeError):
        # Если строка нечисловая (например "1.5 USDT") — точно не 0, считаем платным
        return 1.0


def load_products() -> List[Dict[str, Any]]:
    """
    Колонки:
    product_id | title | description | price_xtr | price_crypto | crypto_asset |
    file_id | active | category | preview_file_id
    """
    global _products_cache
    ts, cached = _products_cache
    if cached and (time.time() - ts) < PRODUCTS_CACHE_TTL:
        return cached

    try:
        r = requests.get(PRODUCTS_CSV_URL, timeout=HTTP_TIMEOUT)
        r.raise_for_status()
        r.encoding = "utf-8"
        csv_text = r.text.strip()
        if not csv_text:
            logger.warning("CSV товаров пуст (нет доступа/не опубликовано).")
            return []
    except Exception as e:
        logger.exception("Не удалось загрузить CSV товаров: %s", e)
        return []

    products: List[Dict[str, Any]] = []
    reader = csv.DictReader(io.StringIO(csv_text))

    for row in reader:
        try:
            if not _to_bool(row.get("active", "")):
                continue

            pid = _to_str(row.get("product_id", ""))
            title = _to_str(row.get("title", ""))
            desc = _to_str(row.get("description", ""))
            file_id = _to_str(row.get("file_id", ""))
            preview_file_id = _to_str(row.get("preview_file_id", ""))
            category = _to_str(row.get("category", ""), "Без категории")

            if not pid or not title or not file_id:
                continue

            price_xtr = _to_int(row.get("price_xtr", ""), 0)
            if price_xtr < 0:
                continue

            price_crypto_raw = _to_str(row.get("price_crypto", ""))
            crypto_asset = _to_str(row.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()

            products.append({
                "product_id": pid,
                "title": title,
                "description": desc or "PDF файл",
                "price_xtr": price_xtr,
                "price_crypto": price_crypto_raw,
                "crypto_asset": crypto_asset,
                "file_id": file_id,
                "preview_file_id": preview_file_id,
                "category": category,
            })
        except Exception:
            logger.exception("Ошибка разбора строки товара")
            continue

    _products_cache = (time.time(), products)
    return products


def is_free_product(p: Dict[str, Any]) -> bool:
    cat = str(p.get("category", "")).strip()
    price_xtr = int(p.get("price_xtr", 0) or 0)
    # FIX #5: используем безопасный парсинг float
    price_crypto = _to_float_safe(p.get("price_crypto", 0))
    return (price_xtr == 0 and price_crypto == 0) or (cat == FREE_CATEGORY_NAME)


def can_buy_with_crypto(product: Dict[str, Any]) -> bool:
    if is_free_product(product):
        return False
    amount = _to_str(product.get("price_crypto", ""))
    asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET)
    return bool(CRYPTO_PAY_TOKEN and amount and asset)


def get_crypto_amount_and_asset(product: Dict[str, Any]) -> Tuple[str, str]:
    amount = _to_str(product.get("price_crypto", ""))
    asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()

    if not amount:
        raise RuntimeError(
            f"Для товара {product.get('product_id')} не задана колонка price_crypto"
        )
    if not asset:
        asset = CRYPTO_PAY_DEFAULT_ASSET

    return amount, asset


# =========================
# SAFE callback_data для категорий
# FIX #4: не делаем clear() — только обновляем ключи
# =========================

_cat_key_to_name: Dict[str, str] = {}


def _cat_key(name: str) -> str:
    return hashlib.sha1(name.encode("utf-8")).hexdigest()[:10]


def categories_keyboard(categories: List[str]) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    # FIX #4: не чистим весь словарь, просто добавляем/обновляем ключи
    for c in categories:
        c_clean = _to_str(c)
        key = _cat_key(c_clean)
        _cat_key_to_name[key] = c_clean
        kb.add(InlineKeyboardButton(text=c_clean, callback_data=f"catk:{key}"))
    return kb


def products_keyboard(products: List[Dict[str, Any]], category_key: str) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    for p in products:
        emoji = "🎁" if is_free_product(p) else "⭐"
        btn_text = f"{emoji} {p['title']}"
        kb.add(
            InlineKeyboardButton(
                text=btn_text,
                callback_data=f"item:{p['product_id']}:{category_key}"
            )
        )
    return kb


# =========================
# ЛОГ ПОКУПОК (с file_id в таблицу)
# =========================

_purchases_cache: Tuple[float, List[Dict[str, str]]] = (0.0, [])


def _sync_read_all_purchases_rows(service, sheet_title: str) -> List[Dict[str, str]]:
    """Синхронное чтение строк — вызывать через run_in_executor."""
    rng = f"{sheet_title}!A:Z"
    resp = service.spreadsheets().values().get(
        spreadsheetId=PURCHASES_SHEET_ID,
        range=rng
    ).execute()

    values = resp.get("values", [])
    if not values or len(values) < 2:
        return []

    headers = values[0]
    rows = values[1:]

    result: List[Dict[str, str]] = []
    for r in rows:
        d = {}
        for i, h in enumerate(headers):
            d[h] = r[i] if i < len(r) else ""
        result.append(d)
    return result


async def get_purchases_cached(force: bool = False) -> List[Dict[str, str]]:
    """FIX #9: асинхронная обёртка для чтения покупок."""
    global _purchases_cache
    ts, cached = _purchases_cache
    if not force and cached and (time.time() - ts) < PURCHASES_CACHE_TTL:
        return cached

    service = await get_sheets_service()
    sheet_title = await get_purchases_sheet_title()
    loop = asyncio.get_event_loop()
    rows = await loop.run_in_executor(None, _sync_read_all_purchases_rows, service, sheet_title)
    _purchases_cache = (time.time(), rows)
    return rows


async def user_has_purchase(user_id: int, product_id: str) -> bool:
    rows = await get_purchases_cached()
    uid = str(user_id)
    pid = str(product_id)
    for r in rows:
        if r.get("user_id") == uid and r.get("product_id") == pid:
            return True
    return False


async def get_user_purchase_row(user_id: int, product_id: str) -> Optional[Dict[str, str]]:
    rows = await get_purchases_cached()
    uid = str(user_id)
    pid = str(product_id)
    found = None
    for r in rows:
        if r.get("user_id") == uid and r.get("product_id") == pid:
            found = r
    return found


def _sync_append_purchase(service, sheet_title: str, row: list):
    """Синхронная запись строки — вызывать через run_in_executor."""
    service.spreadsheets().values().append(
        spreadsheetId=PURCHASES_SHEET_ID,
        range=f"{sheet_title}!A:H",
        valueInputOption="USER_ENTERED",
        insertDataOption="INSERT_ROWS",
        body={"values": [row]}
    ).execute()


async def append_purchase_row(user: types.User, product: Dict[str, Any], price_label: str) -> bool:
    """
    FIX #9: асинхронная запись через run_in_executor.
    Пишем A:H:
    date | user_id | username | full_name | product_id | product_title | price_xtr | file_id
    """
    try:
        service = await get_sheets_service()
        sheet_title = await get_purchases_sheet_title()

        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        username = f"@{user.username}" if user.username else ""

        row = [
            now,
            str(user.id),
            username,
            user.full_name,
            product["product_id"],
            product["title"],
            str(price_label),
            product.get("file_id", ""),
        ]

        loop = asyncio.get_event_loop()
        await loop.run_in_executor(None, _sync_append_purchase, service, sheet_title, row)

        global _purchases_cache
        _purchases_cache = (0.0, [])
        return True

    except Exception as e:
        logger.exception("Не удалось записать покупку в таблицу: %s", e)
        return False


# =========================
# CRYPTO PAY API
# =========================

def crypto_headers() -> Dict[str, str]:
    if not CRYPTO_PAY_TOKEN:
        raise RuntimeError("Не задан CRYPTO_PAY_TOKEN")
    return {"Crypto-Pay-API-Token": CRYPTO_PAY_TOKEN}


def crypto_create_invoice(product: Dict[str, Any], user: types.User) -> Dict[str, Any]:
    amount, asset = get_crypto_amount_and_asset(product)
    payload = f"crypto:{user.id}:{product['product_id']}"

    data = {
        "asset": asset,
        "amount": amount,
        "description": f"{product['title']} | PDF файл",
        "payload": payload,
        "expires_in": 3600,
        "allow_comments": False,
        "allow_anonymous": True
    }

    r = requests.post(
        f"{CRYPTO_PAY_BASE_URL}/createInvoice",
        json=data,
        headers=crypto_headers(),
        timeout=HTTP_TIMEOUT
    )
    r.raise_for_status()
    result = r.json()

    if not result.get("ok"):
        raise RuntimeError(f"Crypto Pay createInvoice error: {result}")

    return result["result"]


def crypto_get_invoice(invoice_id: int) -> Optional[Dict[str, Any]]:
    # FIX #1: invoice_ids должен быть СПИСКОМ, а не строкой
    r = requests.post(
        f"{CRYPTO_PAY_BASE_URL}/getInvoices",
        json={"invoice_ids": [invoice_id]},
        headers=crypto_headers(),
        timeout=HTTP_TIMEOUT
    )
    r.raise_for_status()
    result = r.json()

    if not result.get("ok"):
        raise RuntimeError(f"Crypto Pay getInvoices error: {result}")

    items = result.get("result", {}).get("items", [])
    if not items:
        return None
    return items[0]


# =========================
# ОБЩАЯ ВЫДАЧА ТОВАРА
# FIX #2: asyncio.Lock против двойных покупок
# =========================

async def grant_product_to_user(
    chat_id: int,
    user: types.User,
    product: Dict[str, Any],
    price_label: str
) -> bool:
    pid = product["product_id"]
    lock = _get_purchase_lock(user.id, pid)

    async with lock:
        # Проверяем ВНУТРИ лока — защита от двойной записи
        if await user_has_purchase(user.id, pid):
            await bot.send_document(chat_id, product["file_id"])
            return True

        saved = await append_purchase_row(user=user, product=product, price_label=price_label)
        if not saved:
            return False

        await bot.send_document(chat_id, product["file_id"])
        return True


async def notify_admin_purchase(
    user: types.User,
    product: Dict[str, Any],
    payment_text: str,
    invoice_id: Optional[int] = None
):
    try:
        username = f"@{user.username}" if user.username else "нет"
        admin_text = (
            "💰 <b>Новая покупка!</b>\n\n"
            f"📄 <b>Товар:</b> {product['title']}\n"
            f"💳 <b>Оплата:</b> {payment_text}\n"
        )

        if invoice_id is not None:
            admin_text += f"🧾 <b>Invoice ID:</b> <code>{invoice_id}</code>\n"

        admin_text += (
            f"\n👤 <b>Покупатель:</b>\n"
            f"ID: <code>{user.id}</code>\n"
            f"Имя: {user.full_name}\n"
            f"Username: {username}"
        )

        await bot.send_message(ADMIN_CHAT_ID, admin_text, parse_mode="HTML")
    except Exception as e:
        logger.exception("Не удалось уведомить админа: %s", e)


# =========================
# START / HELP
# FIX #8: /start с deep link обрабатывается корректно
# =========================

START_TEXT = (
    "👋 Привет!\n"
    "В этом боте собраны развивающие PDF для детей 🎨📚\n\n"
    "Здесь вы найдёте:\n"
    "🎨 Разукрашки и творческие задания\n"
    "📖 Обучающие и научные сказки\n"
    "🧠 Развивающие игры и вопросы\n\n"
    "👇 Нажмите «Каталог», чтобы выбрать материалы"
)


@dp.message_handler(commands=["start"])
async def cmd_start(message: types.Message):
    # FIX #8: обрабатываем deep link вида /start buy_stars_p001
    args = message.get_args()
    if args and args.startswith("buy_stars_"):
        pid = args.replace("buy_stars_", "", 1).strip()
        product = next((p for p in load_products() if p["product_id"] == pid), None)
        if product:
            await message.answer(START_TEXT, reply_markup=main_menu())
            text = format_product_card(product)
            kb = product_action_kb(product, category_key=_cat_key(_to_str(product.get("category", ""))))
            preview_id = _to_str(product.get("preview_file_id"))
            if preview_id:
                try:
                    await bot.send_photo(
                        chat_id=message.chat.id,
                        photo=preview_id,
                        caption=text,
                        reply_markup=kb,
                        parse_mode="HTML"
                    )
                    return
                except Exception:
                    pass
            await message.answer(text, reply_markup=kb, parse_mode="HTML")
            return

    await message.answer(START_TEXT, reply_markup=main_menu())


@dp.message_handler(commands=["help", "support"])
async def cmd_help(message: types.Message):
    await message.answer(
        "Если нужен совет или возникла трудность — напишите автору 👇",
        reply_markup=help_inline_kb()
    )


@dp.message_handler(lambda m: m.text and "Каталог" in m.text)
async def show_categories(message: types.Message):
    products = load_products()
    if not products:
        await message.answer("Пока нет доступных материалов.", reply_markup=main_menu())
        return

    categories = sorted(set(_to_str(p.get("category", "")) for p in products if p.get("category")))
    await message.answer("📚 Выберите категорию:", reply_markup=categories_keyboard(categories))


# =========================
# МОИ ПОКУПКИ
# =========================

@dp.message_handler(lambda m: m.text == "📂 Мои покупки")
async def show_my_purchases(message: types.Message):
    await send_my_purchases(message.chat.id, message.from_user)


async def send_my_purchases(chat_id: int, user: types.User):
    rows = await get_purchases_cached()
    uid = str(user.id)
    user_rows = [r for r in rows if r.get("user_id") == uid]

    if not user_rows:
        kb = InlineKeyboardMarkup().add(InlineKeyboardButton("📚 Каталог", callback_data="open:catalog"))
        await bot.send_message(
            chat_id,
            "У вас пока нет покупок 🙌\n\nПерейдите в каталог, чтобы выбрать материалы.",
            reply_markup=kb
        )
        return

    products = load_products()
    prod_map = {p["product_id"]: p for p in products}

    seen = set()
    unique_rows = []
    for r in user_rows:
        pid = _to_str(r.get("product_id"))
        if pid and pid not in seen:
            seen.add(pid)
            unique_rows.append(r)

    await bot.send_message(chat_id, "📂 Ваши покупки:")

    for r in unique_rows:
        pid = _to_str(r.get("product_id"))
        title = _to_str(r.get("product_title")) or prod_map.get(pid, {}).get("title", "PDF")

        price_from_row = _to_str(r.get("price_xtr"))
        is_free_row = (price_from_row == "" or price_from_row == "0")

        emoji = "🎁" if is_free_row else "⭐"
        meta = "🎁 Бесплатно" if is_free_row else f"💳 {price_from_row}"

        kb = InlineKeyboardMarkup().add(
            InlineKeyboardButton(f"{emoji} Скачать", callback_data=f"dl:{pid}")
        )
        await bot.send_message(chat_id, f"📄 {title}\n{meta}", reply_markup=kb)


@dp.callback_query_handler(lambda c: c.data == "open:catalog")
async def cb_open_catalog(call: types.CallbackQuery):
    await call.answer()
    products = load_products()
    if not products:
        await bot.send_message(call.message.chat.id, "Пока нет доступных материалов.", reply_markup=main_menu())
        return
    categories = sorted(set(_to_str(p.get("category", "")) for p in products if p.get("category")))
    await bot.send_message(call.message.chat.id, "📚 Выберите категорию:", reply_markup=categories_keyboard(categories))


# =========================
# КАТЕГОРИЯ -> ТОВАРЫ
# =========================

@dp.callback_query_handler(lambda c: c.data.startswith("catk:"))
async def cb_category(call: types.CallbackQuery):
    key = call.data.split("catk:", 1)[1].strip()
    category = _cat_key_to_name.get(key)

    if not category:
        products_all = load_products()
        cats = sorted(set(_to_str(p.get("category", "")) for p in products_all if p.get("category")))
        for c in cats:
            _cat_key_to_name[_cat_key(c)] = c
        category = _cat_key_to_name.get(key)

    if not category:
        await call.answer("Категория устарела. Откройте каталог заново.", show_alert=True)
        return

    products = [p for p in load_products() if _to_str(p.get("category", "")) == category]
    if not products:
        await call.answer("Пока пусто.", show_alert=True)
        return

    await call.message.answer(f"📂 {category}", reply_markup=products_keyboard(products, category_key=key))
    await call.answer()


# =========================
# ПРЕДПРОСМОТР ТОВАРА + ЛОКАЛЬНАЯ КНОПКА "НАЗАД"
# =========================

def product_action_kb(product: Dict[str, Any], category_key: str) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)

    pid = product["product_id"]
    price_xtr = int(product.get("price_xtr", 0) or 0)
    price_crypto_raw = str(product.get("price_crypto", "")).strip()
    crypto_asset = str(product.get("crypto_asset", "")).strip().upper()

    if price_xtr > 0:
        kb.add(
            InlineKeyboardButton(
                f"⭐ Купить за {price_xtr} Stars",
                callback_data=f"paystars:{pid}"
            )
        )

    if price_crypto_raw and crypto_asset:
        kb.add(
            InlineKeyboardButton(
                f"💰 Купить за {price_crypto_raw} {crypto_asset}",
                callback_data=f"paycrypto:{pid}"
            )
        )

    if price_xtr == 0 and not price_crypto_raw:
        kb.add(
            InlineKeyboardButton(
                "🎁 Скачать бесплатно",
                callback_data=f"get:{pid}"
            )
        )

    kb.add(
        InlineKeyboardButton(
            "⬅️ Назад к списку",
            callback_data=f"back_items:{category_key}"
        )
    )

    return kb


def format_product_card(product: Dict[str, Any]) -> str:
    title = product.get("title", "PDF")
    desc = _to_str(product.get("description"), "PDF файл")

    price_xtr = int(product.get("price_xtr", 0) or 0)
    price_crypto_raw = _to_str(product.get("price_crypto", ""))
    crypto_asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()

    if is_free_product(product):
        price_line = "🎁 Бесплатно"
    elif price_xtr > 0:
        price_line = f"⭐ Цена: {price_xtr} Stars"
    else:
        price_line = "💰 Оплата криптой"

    crypto_line = ""
    if price_crypto_raw and crypto_asset:
        crypto_line = f"\n₿ Криптой: {price_crypto_raw} {crypto_asset}"

    return f"📄 <b>{title}</b>\n\n{desc}\n\n{price_line}{crypto_line}"


@dp.callback_query_handler(lambda c: c.data.startswith("item:"))
async def cb_item(call: types.CallbackQuery):
    parts = call.data.split(":")
    if len(parts) < 3:
        await call.answer("Кнопка устарела. Откройте каталог заново.", show_alert=True)
        return

    pid = parts[1].strip()
    category_key = parts[2].strip()

    product = next((p for p in load_products() if p["product_id"] == pid), None)
    if not product:
        await call.answer("Материал не найден.", show_alert=True)
        return

    await call.answer()

    text = format_product_card(product)
    kb = product_action_kb(product, category_key=category_key)
    preview_id = _to_str(product.get("preview_file_id"))

    if preview_id:
        try:
            await bot.send_photo(
                chat_id=call.message.chat.id,
                photo=preview_id,
                caption=text,
                reply_markup=kb,
                parse_mode="HTML"
            )
        except Exception as e:
            logger.exception("Не удалось отправить превью, fallback на текст: %s", e)
            await bot.send_message(
                call.message.chat.id,
                text,
                reply_markup=kb,
                parse_mode="HTML"
            )
    else:
        await bot.send_message(
            call.message.chat.id,
            text,
            reply_markup=kb,
            parse_mode="HTML"
        )


@dp.callback_query_handler(lambda c: c.data.startswith("back_items:"))
async def cb_back_items(call: types.CallbackQuery):
    category_key = call.data.split("back_items:", 1)[1].strip()
    category = _cat_key_to_name.get(category_key)

    if not category:
        products_all = load_products()
        cats = sorted(set(_to_str(p.get("category", "")) for p in products_all if p.get("category")))
        for c in cats:
            _cat_key_to_name[_cat_key(c)] = c
        category = _cat_key_to_name.get(category_key)

    if not category:
        await call.answer("Категория устарела. Откройте каталог заново.", show_alert=True)
        return

    products = [p for p in load_products() if _to_str(p.get("category", "")) == category]
    if not products:
        await call.answer("В категории пока нет товаров.", show_alert=True)
        return

    text = f"📂 {category}"
    kb = products_keyboard(products, category_key=category_key)

    try:
        msg = call.message
        if msg.photo:
            # FIX #6: добавлен parse_mode
            await msg.edit_caption(caption=text, reply_markup=kb, parse_mode="HTML")
        else:
            await msg.edit_text(text, reply_markup=kb, parse_mode="HTML")
    except Exception as e:
        logger.exception("edit back_items failed, fallback to answer(): %s", e)
        await call.message.answer(text, reply_markup=kb)

    await call.answer()


# =========================
# ДЕЙСТВИЯ: бесплатно / STARS / CRYPTO
# =========================

@dp.callback_query_handler(lambda c: c.data.startswith("get:"))
async def cb_get_free(call: types.CallbackQuery):
    pid = call.data.split("get:", 1)[1].strip()
    product = next((p for p in load_products() if p["product_id"] == pid), None)
    if not product:
        await call.answer("Материал не найден.", show_alert=True)
        return
    if not is_free_product(product):
        await call.answer("Этот материал платный.", show_alert=True)
        return

    user = call.from_user
    await call.answer()

    ok = await grant_product_to_user(
        chat_id=call.message.chat.id,
        user=user,
        product=product,
        price_label="0"
    )
    if not ok:
        await bot.send_message(call.message.chat.id, "Не удалось сохранить покупку. Попробуйте ещё раз позже.")


@dp.callback_query_handler(lambda c: c.data.startswith("paystars:"))
async def cb_pay_stars(call: types.CallbackQuery):
    pid = call.data.split("paystars:", 1)[1].strip()
    product = next((p for p in load_products() if p["product_id"] == pid), None)
    if not product:
        await call.answer("Материал не найден.", show_alert=True)
        return
    if is_free_product(product):
        await call.answer("Этот материал бесплатный.", show_alert=True)
        return

    user = call.from_user
    if await user_has_purchase(user.id, pid):
        await call.answer()
        await bot.send_document(call.message.chat.id, product["file_id"])
        return

    try:
        await bot.send_invoice(
            chat_id=call.message.chat.id,
            title=product["title"],
            description=product["description"],
            payload=f"buystars:{pid}",
            provider_token=PROVIDER_TOKEN,
            currency=CURRENCY,
            prices=[LabeledPrice(label=product["title"], amount=int(product["price_xtr"]))],
            start_parameter=f"buy_stars_{pid}"
        )
        await call.answer()
    except Exception as e:
        logger.exception("Ошибка send_invoice (Stars): %s", e)
        await call.answer("Не удалось создать счёт Stars. Проверь настройки бота.", show_alert=True)


@dp.callback_query_handler(lambda c: c.data.startswith("paycrypto:"))
async def cb_pay_crypto(call: types.CallbackQuery):
    pid = call.data.split("paycrypto:", 1)[1].strip()
    product = next((p for p in load_products() if p["product_id"] == pid), None)
    if not product:
        await call.answer("Материал не найден.", show_alert=True)
        return
    if is_free_product(product):
        await call.answer("Этот материал бесплатный.", show_alert=True)
        return

    user = call.from_user
    if await user_has_purchase(user.id, pid):
        await call.answer()
        await bot.send_document(call.message.chat.id, product["file_id"])
        return

    if not CRYPTO_PAY_TOKEN:
        await call.answer("Крипто-оплата пока не настроена.", show_alert=True)
        return

    try:
        amount, asset = get_crypto_amount_and_asset(product)
        invoice = crypto_create_invoice(product, user)
        invoice_id = invoice["invoice_id"]
        pay_url = invoice.get("bot_invoice_url") or invoice.get("pay_url")

        kb = InlineKeyboardMarkup(row_width=1)
        kb.add(
            InlineKeyboardButton("💸 Оплатить в CryptoBot", url=pay_url),
            InlineKeyboardButton("✅ Я оплатил, проверить", callback_data=f"checkcrypto:{pid}:{invoice_id}")
        )

        await bot.send_message(
            call.message.chat.id,
            (
                f"₿ Счёт создан\n\n"
                f"📄 Товар: {product['title']}\n"
                f"💰 Сумма: {amount} {asset}\n\n"
                f"1. Нажмите «Оплатить в CryptoBot»\n"
                f"2. После оплаты нажмите «Я оплатил, проверить»"
            ),
            reply_markup=kb
        )
        await call.answer()

    except Exception as e:
        logger.exception("Ошибка создания crypto invoice: %s", e)
        await call.answer("Не удалось создать crypto-счёт.", show_alert=True)


@dp.callback_query_handler(lambda c: c.data.startswith("checkcrypto:"))
async def cb_check_crypto(call: types.CallbackQuery):
    try:
        _, pid, invoice_id_raw = call.data.split(":", 2)
        invoice_id = int(invoice_id_raw)
    except Exception:
        await call.answer("Некорректная кнопка.", show_alert=True)
        return

    product = next((p for p in load_products() if p["product_id"] == pid), None)
    if not product:
        await call.answer("Материал не найден.", show_alert=True)
        return

    user = call.from_user

    if await user_has_purchase(user.id, pid):
        await call.answer()
        await bot.send_document(call.message.chat.id, product["file_id"])
        return

    try:
        # FIX #1 применён внутри crypto_get_invoice — передаём список
        invoice = crypto_get_invoice(invoice_id)
        if not invoice:
            await call.answer("Счёт не найден.", show_alert=True)
            return

        status = _to_str(invoice.get("status", ""))
        payload = _to_str(invoice.get("payload", ""))

        expected_payload = f"crypto:{user.id}:{pid}"
        if payload != expected_payload:
            await call.answer("Этот счёт не принадлежит этому товару.", show_alert=True)
            return

        if status != "paid":
            await call.answer(f"Счёт пока не оплачен. Статус: {status}", show_alert=True)
            return

        amount, asset = get_crypto_amount_and_asset(product)

        ok = await grant_product_to_user(
            chat_id=call.message.chat.id,
            user=user,
            product=product,
            price_label=f"{amount} {asset}"
        )
        if not ok:
            await call.answer("Оплата есть, но не удалось сохранить покупку. Напишите в поддержку.", show_alert=True)
            return

        await notify_admin_purchase(
            user=user,
            product=product,
            payment_text=f"{amount} {asset} через CryptoBot",
            invoice_id=invoice_id
        )

        await call.answer("Оплата подтверждена!")
    except Exception as e:
        logger.exception("Ошибка проверки crypto invoice: %s", e)
        await call.answer("Не удалось проверить оплату.", show_alert=True)


# =========================
# СКАЧАТЬ ИЗ МОИХ ПОКУПОК (не зависит от active)
# =========================

@dp.callback_query_handler(lambda c: c.data.startswith("dl:"))
async def cb_download(call: types.CallbackQuery):
    pid = call.data.split("dl:", 1)[1].strip()
    user = call.from_user

    purchase_row = await get_user_purchase_row(user.id, pid)
    if not purchase_row:
        await call.answer("Покупка не найдена. Откройте «Мои покупки» заново.", show_alert=True)
        return

    file_id_from_row = _to_str(purchase_row.get("file_id"))

    if not file_id_from_row:
        product = next((p for p in load_products() if p["product_id"] == pid), None)
        if not product:
            await call.answer("Не удалось получить файл. Напишите в поддержку через /help.", show_alert=True)
            return
        file_id_from_row = product["file_id"]

    await call.answer()
    await bot.send_document(call.message.chat.id, file_id_from_row)


# =========================
# STARS PAYMENT
# FIX #3: total_amount для Stars — это количество звёзд (не копейки)
# =========================

@dp.pre_checkout_query_handler(lambda q: True)
async def pre_checkout(pre_checkout_q: types.PreCheckoutQuery):
    await bot.answer_pre_checkout_query(pre_checkout_q.id, ok=True)


@dp.message_handler(content_types=types.ContentType.SUCCESSFUL_PAYMENT)
async def successful_payment(message: types.Message):
    payload = message.successful_payment.invoice_payload
    if not payload.startswith("buystars:"):
        await message.answer("Оплата получена, но товар не распознан.")
        return

    pid = payload.split("buystars:", 1)[1].strip()
    product = next((p for p in load_products() if p["product_id"] == pid), None)
    if not product:
        await message.answer("Оплата получена, но материал сейчас недоступен.")
        return

    # FIX #3: для XTR (Stars) total_amount = кол-во звёзд напрямую.
    # В таблице price_xtr должно быть целое число звёзд (например: 100).
    expected = int(product["price_xtr"])
    paid_amount = int(message.successful_payment.total_amount)

    if paid_amount != expected:
        logger.warning(
            "Stars mismatch: expected=%s paid=%s product=%s user=%s",
            expected, paid_amount, pid, message.from_user.id
        )
        await message.answer("Ошибка суммы оплаты. Напишите автору через /help.")
        return

    user = message.from_user

    ok = await grant_product_to_user(
        chat_id=message.chat.id,
        user=user,
        product=product,
        price_label=f"{expected} Stars"
    )
    if not ok:
        await message.answer("Оплата получена, но не удалось сохранить покупку. Напишите в поддержку.")
        return

    await notify_admin_purchase(
        user=user,
        product=product,
        payment_text=f"{expected} Stars"
    )


# =========================
# ADMIN: refresh caches + debug file_id (doc/photo)
# FIX #7: user_id передаётся как список
# =========================

@dp.message_handler(commands=["refresh"], user_id=[ADMIN_CHAT_ID])
async def cmd_refresh(message: types.Message):
    global _products_cache, _purchases_cache, _purchases_sheet_title
    _products_cache = (0.0, [])
    _purchases_cache = (0.0, [])
    _purchases_sheet_title = None
    logger.info("Admin triggered cache refresh")
    await message.answer("✅ Кеши очищены. Следующая загрузка будет с нуля.")


@dp.message_handler(content_types=types.ContentType.DOCUMENT, user_id=[ADMIN_CHAT_ID])
async def debug_get_file_id_doc(message: types.Message):
    await message.reply(
        f"📄 file_id:\n<code>{message.document.file_id}</code>",
        parse_mode="HTML"
    )


@dp.message_handler(content_types=types.ContentType.PHOTO, user_id=[ADMIN_CHAT_ID])
async def debug_get_file_id_photo(message: types.Message):
    photo = message.photo[-1]
    await message.reply(
        f"🖼 preview_file_id:\n<code>{photo.file_id}</code>",
        parse_mode="HTML"
    )


if __name__ == "__main__":
    executor.start_polling(dp, skip_updates=True)
