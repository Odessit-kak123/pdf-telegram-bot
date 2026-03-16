import os
import re
import json
import csv
import io
import asyncio
import logging
import time
import hashlib
import sqlite3
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

try:
    from google.oauth2.service_account import Credentials
    from googleapiclient.discovery import build
    _GOOGLE_LIBS_AVAILABLE = True
except ImportError:
    _GOOGLE_LIBS_AVAILABLE = False
    # logger ещё не создан на этом этапе — предупреждение выведем позже


# =========================
# НАСТРОЙКИ
# =========================

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()

# Таблица ТОВАРОВ (публичная, CSV):
PRODUCTS_CSV_URL = "https://docs.google.com/spreadsheets/d/1V1LCKR13JNply4LAEfJBtYNAE854Zr8aBBMTUTC2kPA/gviz/tq?tqx=out:csv"

# SQLite база покупок (хранится на Railway Volume или рядом с bot.py)
DB_PATH = os.getenv("DB_PATH", "purchases.db").strip()

# Google Sheets — только для резервного зеркалирования покупок (необязательно)
# Если GOOGLE_SERVICE_ACCOUNT_JSON не задан, зеркалирование просто отключается.
PURCHASES_SHEET_ID = os.getenv("PURCHASES_SHEET_ID", "").strip()
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

if not _GOOGLE_LIBS_AVAILABLE:
    logger.warning("google-auth / googleapiclient не установлены — зеркало в Sheets отключено")

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

# Шаг 3: защита от дублирующих crypto-invoice
_crypto_invoice_created_at: Dict[str, float] = {}


_CRYPTO_INVOICE_COOLDOWN = 60   # секунд между созданиями invoice для одного товара
_CRYPTO_INVOICE_MAX_AGE = 3600  # старше 1 часа — чистим из словаря


def _cleanup_invoice_cooldown() -> None:
    """Удаляет устаревшие записи cooldown. Вызывать изредка."""
    cutoff = time.time() - _CRYPTO_INVOICE_MAX_AGE
    expired = [k for k, ts in _crypto_invoice_created_at.items() if ts < cutoff]
    for k in expired:
        del _crypto_invoice_created_at[k]
    if expired:
        logger.debug("Cleaned %d expired invoice cooldown entries", len(expired))


def _get_purchase_lock(user_id: int, product_id: str) -> asyncio.Lock:
    key = f"{user_id}:{product_id}"
    now = time.time()

    # Чистим старые локи, но ТОЛЬКО если они уже не заняты
    expired = [
        k for k, ts in _purchase_locks_meta.items()
        if now - ts > _LOCK_TTL and not _purchase_locks.get(k, None) or
           (k in _purchase_locks and not _purchase_locks[k].locked() and now - ts > _LOCK_TTL)
    ]
    for k in expired:
        lock_obj = _purchase_locks.get(k)
        if lock_obj is None or not lock_obj.locked():
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
# SQLite: БАЗА ПОКУПОК
# Заменяет Google Sheets как основное хранилище.
# Google Sheets опционально используется для зеркала/отчётности.
# =========================

def init_db() -> None:
    """Создаёт таблицу purchases если её нет. Вызывать при старте."""
    with sqlite3.connect(DB_PATH) as conn:
        conn.execute("""
            CREATE TABLE IF NOT EXISTS purchases (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                date         TEXT    NOT NULL,
                user_id      TEXT    NOT NULL,
                username     TEXT,
                full_name    TEXT,
                product_id   TEXT    NOT NULL,
                product_title TEXT,
                price_label  TEXT,
                file_id      TEXT,
                UNIQUE(user_id, product_id)
            )
        """)
        conn.commit()
    logger.info("SQLite DB ready: %s", DB_PATH)


# =========================
# Google Sheets: ЗЕРКАЛО (необязательно)
# =========================

_SCOPES = ["https://www.googleapis.com/auth/spreadsheets"]
_sheets_service = None
_purchases_sheet_title: Optional[str] = None


def _build_sheets_service():
    global _sheets_service
    if _sheets_service is not None:
        return _sheets_service
    if not GOOGLE_SERVICE_ACCOUNT_JSON or not _GOOGLE_LIBS_AVAILABLE:
        return None
    creds_info = json.loads(GOOGLE_SERVICE_ACCOUNT_JSON)
    creds = Credentials.from_service_account_info(creds_info, scopes=_SCOPES)
    _sheets_service = build("sheets", "v4", credentials=creds, cache_discovery=False)
    return _sheets_service


async def _mirror_to_sheets(row: list) -> None:
    """Зеркалирование покупки в Google Sheets. Молча игнорирует ошибки."""
    if not GOOGLE_SERVICE_ACCOUNT_JSON or not PURCHASES_SHEET_ID:
        return
    try:
        loop = asyncio.get_running_loop()
        service = await loop.run_in_executor(None, _build_sheets_service)
        if not service:
            return

        def _get_title():
            global _purchases_sheet_title
            if _purchases_sheet_title:
                return _purchases_sheet_title
            meta = service.spreadsheets().get(spreadsheetId=PURCHASES_SHEET_ID).execute()
            sheets = meta.get("sheets", [])
            if not sheets:
                return None
            _purchases_sheet_title = sheets[0]["properties"]["title"]
            return _purchases_sheet_title

        sheet_title = await loop.run_in_executor(None, _get_title)
        if not sheet_title:
            return

        def _append():
            service.spreadsheets().values().append(
                spreadsheetId=PURCHASES_SHEET_ID,
                range=f"{sheet_title}!A:H",
                valueInputOption="USER_ENTERED",
                insertDataOption="INSERT_ROWS",
                body={"values": [row]}
            ).execute()

        await loop.run_in_executor(None, _append)
    except Exception as e:
        logger.warning("Зеркало Sheets недоступно (не критично): %s", e)


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
    Безопасное преобразование в float.
    Корректно обрабатывает строки вида "1.5 USDT" — извлекает число из начала.
    Мусор типа "abc", "бесплатно" возвращает default и логирует warning.
    """
    if value is None:
        return default
    s = str(value).strip()
    if s == "":
        return default
    # Сначала пробуем простой float
    try:
        return float(s)
    except (ValueError, TypeError):
        pass
    # Пробуем вытащить первое число из строки: "1.5 USDT" -> 1.5
    m = re.match(r"^\s*([0-9]+(?:[.,][0-9]+)?)", s)
    if m:
        num_str = m.group(1).replace(",", ".")
        try:
            result = float(num_str)
            logger.debug("_to_float_safe: извлёк %.4f из %r", result, s)
            return result
        except ValueError:
            pass
    # Настоящий мусор — логируем и возвращаем default (НЕ считаем платным автоматически)
    logger.warning("_to_float_safe: не удалось разобрать %r, возвращаю default=%.1f", s, default)
    return default


def _sync_fetch_csv() -> str:
    """Синхронная загрузка CSV товаров — вызывать через run_in_executor."""
    r = requests.get(PRODUCTS_CSV_URL, timeout=HTTP_TIMEOUT)
    r.raise_for_status()
    r.encoding = "utf-8"
    return r.text.strip()


async def load_products() -> List[Dict[str, Any]]:
    """
    Колонки:
    product_id | title | description | price_xtr | price_crypto | crypto_asset |
    file_id | active | category | preview_file_id

    Загрузка CSV через run_in_executor — не блокирует event loop.
    """
    global _products_cache
    ts, cached = _products_cache
    if cached and (time.time() - ts) < PRODUCTS_CACHE_TTL:
        return cached

    try:
        loop = asyncio.get_running_loop()
        csv_text = await loop.run_in_executor(None, _sync_fetch_csv)
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
    for c in categories:
        c_clean = _to_str(c)
        key = _cat_key(c_clean)
        _cat_key_to_name[key] = c_clean
        kb.add(InlineKeyboardButton(text=c_clean, callback_data=f"catk:{key}"))
    kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))
    return kb


def products_keyboard(products: List[Dict[str, Any]], category_key: str) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    for p in products:
        if is_free_product(p):
            emoji = "🎁"
        elif int(p.get("price_xtr", 0) or 0) > 0:
            emoji = "⭐"
        else:
            emoji = "💰"
        btn_text = f"{emoji} {p['title']}"
        kb.add(
            InlineKeyboardButton(
                text=btn_text,
                callback_data=f"item:{p['product_id']}:{category_key}"
            )
        )
    kb.add(InlineKeyboardButton("🔙 К категориям", callback_data="open:catalog"))
    kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))
    return kb


# =========================
# SQLite CRUD: ПОКУПКИ
# =========================

def _db_user_has_purchase(user_id: int, product_id: str) -> bool:
    with sqlite3.connect(DB_PATH) as conn:
        row = conn.execute(
            "SELECT 1 FROM purchases WHERE user_id=? AND product_id=?",
            (str(user_id), str(product_id))
        ).fetchone()
    return row is not None


def _db_get_user_purchases(user_id: int) -> List[Dict[str, str]]:
    with sqlite3.connect(DB_PATH) as conn:
        conn.row_factory = sqlite3.Row
        rows = conn.execute(
            "SELECT * FROM purchases WHERE user_id=? ORDER BY date DESC",
            (str(user_id),)
        ).fetchall()
    return [dict(r) for r in rows]


def _db_get_purchase(user_id: int, product_id: str) -> Optional[Dict[str, str]]:
    with sqlite3.connect(DB_PATH) as conn:
        conn.row_factory = sqlite3.Row
        row = conn.execute(
            "SELECT * FROM purchases WHERE user_id=? AND product_id=?",
            (str(user_id), str(product_id))
        ).fetchone()
    return dict(row) if row else None


def _db_insert_purchase(user: "types.User", product: Dict[str, Any], price_label: str) -> bool:
    """
    INSERT OR IGNORE — если запись уже есть (user_id, product_id UNIQUE), ничего не произойдёт.
    Возвращает True если запись была добавлена, False если уже существовала.
    """
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    username = f"@{user.username}" if user.username else ""
    try:
        with sqlite3.connect(DB_PATH) as conn:
            cursor = conn.execute(
                """INSERT OR IGNORE INTO purchases
                   (date, user_id, username, full_name, product_id, product_title, price_label, file_id)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
                (
                    now,
                    str(user.id),
                    username,
                    user.full_name,
                    product["product_id"],
                    product["title"],
                    str(price_label),
                    product.get("file_id", ""),
                )
            )
            conn.commit()
            return cursor.rowcount > 0
    except Exception as e:
        logger.exception("SQLite insert error: %s", e)
        return False


async def user_has_purchase(user_id: int, product_id: str) -> bool:
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _db_user_has_purchase, user_id, product_id)


async def get_user_purchase_row(user_id: int, product_id: str) -> Optional[Dict[str, str]]:
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _db_get_purchase, user_id, product_id)


async def append_purchase_row(user: types.User, product: Dict[str, Any], price_label: str) -> bool:
    """
    Записывает покупку в SQLite (INSERT OR IGNORE — без дублей на уровне БД).
    Параллельно зеркалирует в Google Sheets если настроено.
    """
    loop = asyncio.get_running_loop()
    inserted = await loop.run_in_executor(None, _db_insert_purchase, user, product, price_label)

    if inserted:
        # Зеркало в Sheets — опционально, ошибки не критичны
        mirror_row = [
            datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            str(user.id),
            f"@{user.username}" if user.username else "",
            user.full_name,
            product["product_id"],
            product["title"],
            str(price_label),
            product.get("file_id", ""),
        ]
        asyncio.create_task(_mirror_to_sheets(mirror_row))

    return True  # Даже если дубль — файл всё равно выдаём


# =========================
# CRYPTO PAY API
# =========================

def crypto_headers() -> Dict[str, str]:
    if not CRYPTO_PAY_TOKEN:
        raise RuntimeError("Не задан CRYPTO_PAY_TOKEN")
    return {"Crypto-Pay-API-Token": CRYPTO_PAY_TOKEN}


def _sync_crypto_create_invoice(data: dict) -> Dict[str, Any]:
    """Синхронный HTTP-запрос к Crypto Pay — вызывать через run_in_executor."""
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


def _sync_crypto_get_invoice(invoice_id: int) -> Optional[Dict[str, Any]]:
    """Синхронный HTTP-запрос к Crypto Pay — вызывать через run_in_executor."""
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
    return items[0] if items else None


async def crypto_create_invoice(product: Dict[str, Any], user: types.User) -> Dict[str, Any]:
    """Асинхронное создание invoice — не блокирует event loop."""
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

    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _sync_crypto_create_invoice, data)


async def crypto_get_invoice(invoice_id: int) -> Optional[Dict[str, Any]]:
    """Асинхронная проверка invoice — не блокирует event loop."""
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _sync_crypto_get_invoice, invoice_id)


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
    "👋 <b>Привет!</b>\n\n"
    "Здесь собраны развивающие PDF-материалы для детей 🎨📚\n\n"
    "🎨 Разукрашки и творческие задания\n"
    "📖 Обучающие и научные сказки\n"
    "🧠 Развивающие игры и вопросы\n"
    "🎁 Бесплатные материалы\n\n"
    "Выберите раздел 👇"
)


def start_inline_kb() -> InlineKeyboardMarkup:
    """Красивое inline-меню вместо ReplyKeyboard на старте."""
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(
        InlineKeyboardButton("📚 Каталог", callback_data="open:catalog"),
        InlineKeyboardButton("📂 Мои покупки", callback_data="open:purchases"),
    )
    kb.add(
        InlineKeyboardButton("✉️ Поддержка", url=f"https://t.me/{AUTHOR_USERNAME}")
    )
    return kb


@dp.message_handler(commands=["start"])
async def cmd_start(message: types.Message):
    # FIX #8: обрабатываем deep link вида /start buy_stars_p001
    args = message.get_args()
    if args and args.startswith("buy_stars_"):
        pid = args.replace("buy_stars_", "", 1).strip()
        _all_products = await load_products()
        product = next((p for p in _all_products if p["product_id"] == pid), None)
        if product:
            await message.answer(START_TEXT, reply_markup=start_inline_kb(), parse_mode="HTML")
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

    await message.answer(START_TEXT, reply_markup=start_inline_kb(), parse_mode="HTML")


@dp.message_handler(commands=["help", "support"])
async def cmd_help(message: types.Message):
    await message.answer(
        "Если нужен совет или возникла трудность — напишите автору 👇",
        reply_markup=help_inline_kb()
    )


@dp.message_handler(lambda m: m.text and "Каталог" in m.text)
async def show_categories(message: types.Message):
    products = await load_products()
    if not products:
        await message.answer("Пока нет доступных материалов.")
        return

    categories = sorted(set(_to_str(p.get("category", "")) for p in products if p.get("category")))
    sent = await message.answer(
        "📚 <b>Каталог</b>\n\nВыберите категорию:",
        reply_markup=categories_keyboard(categories),
        parse_mode="HTML"
    )



# =========================
# МОИ ПОКУПКИ
# =========================

@dp.message_handler(lambda m: m.text == "📂 Мои покупки")
async def show_my_purchases(message: types.Message):
    await send_my_purchases(message.chat.id, message.from_user)


async def send_my_purchases(chat_id: int, user: types.User):
    loop = asyncio.get_running_loop()
    user_rows = await loop.run_in_executor(None, _db_get_user_purchases, user.id)

    if not user_rows:
        kb = InlineKeyboardMarkup(row_width=1)
        kb.add(InlineKeyboardButton("📚 Перейти в каталог", callback_data="open:catalog"))
        kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))
        await bot.send_message(
            chat_id,
            "📂 <b>Мои покупки</b>\n\nУ вас пока нет покупок 🙌\nПерейдите в каталог, чтобы выбрать материалы.",
            reply_markup=kb,
            parse_mode="HTML"
        )
        return

    products = await load_products()
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

        price_from_row = _to_str(r.get("price_label") or r.get("price_xtr"))
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
    products = await load_products()
    if not products:
        await call.message.answer("Пока нет доступных материалов.")
        return
    categories = sorted(set(_to_str(p.get("category", "")) for p in products if p.get("category")))
    text = "📚 <b>Каталог</b>\n\nВыберите категорию:"
    kb = categories_keyboard(categories)
    try:
        await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")
    except Exception:
        await call.message.answer(text, reply_markup=kb, parse_mode="HTML")



@dp.callback_query_handler(lambda c: c.data == "open:purchases")
async def cb_open_purchases(call: types.CallbackQuery):
    await call.answer()
    await send_my_purchases(call.message.chat.id, call.from_user)


@dp.callback_query_handler(lambda c: c.data == "open:start")
async def cb_open_start(call: types.CallbackQuery):
    await call.answer()
    try:
        await call.message.edit_text(START_TEXT, reply_markup=start_inline_kb(), parse_mode="HTML")
    except Exception:
        await call.message.answer(START_TEXT, reply_markup=start_inline_kb(), parse_mode="HTML")


# =========================
# КАТЕГОРИЯ -> ТОВАРЫ
# =========================

@dp.callback_query_handler(lambda c: c.data.startswith("catk:"))
async def cb_category(call: types.CallbackQuery):
    key = call.data.split("catk:", 1)[1].strip()
    category = _cat_key_to_name.get(key)

    if not category:
        products_all = await load_products()
        cats = sorted(set(_to_str(p.get("category", "")) for p in products_all if p.get("category")))
        for c in cats:
            _cat_key_to_name[_cat_key(c)] = c
        category = _cat_key_to_name.get(key)

    if not category:
        await call.answer("Категория устарела. Откройте каталог заново.", show_alert=True)
        return

    _all_products = await load_products()
    products = [p for p in _all_products if _to_str(p.get("category", "")) == category]
    if not products:
        await call.answer("Пока пусто.", show_alert=True)
        return

    text = f"📂 <b>{category}</b>\n\nВыберите материал:"
    kb = products_keyboard(products, category_key=key)
    try:
        await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")
    except Exception:
        await call.message.answer(text, reply_markup=kb, parse_mode="HTML")
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
    kb.add(
        InlineKeyboardButton(
            "🏠 Главная",
            callback_data="open:start"
        )
    )

    return kb


def format_product_card(product: Dict[str, Any]) -> str:
    title = product.get("title", "PDF")
    desc = _to_str(product.get("description"), "PDF файл")

    price_xtr = int(product.get("price_xtr", 0) or 0)
    price_crypto_raw = _to_str(product.get("price_crypto", ""))
    crypto_asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()
    category = _to_str(product.get("category", ""))

    # Цена
    if is_free_product(product):
        price_line = "🎁 <b>Бесплатно</b>"
    elif price_xtr > 0 and price_crypto_raw:
        price_line = f"⭐ <b>{price_xtr} Stars</b>  |  💰 <b>{price_crypto_raw} {crypto_asset}</b>"
    elif price_xtr > 0:
        price_line = f"⭐ <b>{price_xtr} Stars</b>"
    else:
        price_line = f"💰 <b>{price_crypto_raw} {crypto_asset}</b>"

    # Категория badge
    cat_line = f"\n<i>📂 {category}</i>" if category else ""

    return (
        f"📄 <b>{title}</b>{cat_line}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{desc}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{price_line}"
    )


@dp.callback_query_handler(lambda c: c.data.startswith("item:"))
async def cb_item(call: types.CallbackQuery):
    parts = call.data.split(":")
    if len(parts) < 3:
        await call.answer("Кнопка устарела. Откройте каталог заново.", show_alert=True)
        return

    pid = parts[1].strip()
    category_key = parts[2].strip()

    _all_products = await load_products()
    product = next((p for p in _all_products if p["product_id"] == pid), None)
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
        products_all = await load_products()
        cats = sorted(set(_to_str(p.get("category", "")) for p in products_all if p.get("category")))
        for c in cats:
            _cat_key_to_name[_cat_key(c)] = c
        category = _cat_key_to_name.get(category_key)

    if not category:
        await call.answer("Категория устарела. Откройте каталог заново.", show_alert=True)
        return

    _all_products = await load_products()
    products = [p for p in _all_products if _to_str(p.get("category", "")) == category]
    if not products:
        await call.answer("В категории пока нет товаров.", show_alert=True)
        return

    text = f"📂 <b>{category}</b>\n\nВыберите материал:"
    kb = products_keyboard(products, category_key=category_key)

    try:
        msg = call.message
        if msg.photo:
            # Карточка с фото — убираем кнопки чтобы она выглядела "закрытой"
            try:
                await msg.edit_reply_markup(reply_markup=InlineKeyboardMarkup())
            except Exception:
                pass
            # Список идёт следующим сообщением
            await bot.send_message(msg.chat.id, text, reply_markup=kb, parse_mode="HTML")
        else:
            await msg.edit_text(text, reply_markup=kb, parse_mode="HTML")
    except Exception as e:
        logger.exception("edit back_items failed: %s", e)
        await bot.send_message(call.message.chat.id, text, reply_markup=kb, parse_mode="HTML")

    await call.answer()


# =========================
# ДЕЙСТВИЯ: бесплатно / STARS / CRYPTO
# =========================

@dp.callback_query_handler(lambda c: c.data.startswith("get:"))
async def cb_get_free(call: types.CallbackQuery):
    pid = call.data.split("get:", 1)[1].strip()
    _all_products = await load_products()
    product = next((p for p in _all_products if p["product_id"] == pid), None)
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
    _all_products = await load_products()
    product = next((p for p in _all_products if p["product_id"] == pid), None)
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
    _all_products = await load_products()
    product = next((p for p in _all_products if p["product_id"] == pid), None)
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

    # Шаг 3: защита от дублирующих invoice — проверяем cooldown
    dedup_key = f"{user.id}:{pid}"
    last_created = _crypto_invoice_created_at.get(dedup_key, 0)
    if time.time() - last_created < _CRYPTO_INVOICE_COOLDOWN:
        await call.answer(
            "Счёт уже был создан недавно. Подождите минуту или нажмите «Я оплатил, проверить» выше.",
            show_alert=True
        )
        return

    try:
        amount, asset = get_crypto_amount_and_asset(product)
        invoice = await crypto_create_invoice(product, user)
        _crypto_invoice_created_at[dedup_key] = time.time()
        _cleanup_invoice_cooldown()  # Чистим устаревшие записи попутно
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

    _all_products = await load_products()
    product = next((p for p in _all_products if p["product_id"] == pid), None)
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
        invoice = await crypto_get_invoice(invoice_id)
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

        # Проверяем что сумма и валюта в invoice совпадают с товаром
        invoice_amount = _to_str(invoice.get("amount", ""))
        invoice_asset = _to_str(invoice.get("asset", "")).upper()
        if invoice_amount and invoice_amount != amount:
            logger.warning(
                "Invoice amount mismatch: expected=%s got=%s user=%s product=%s",
                amount, invoice_amount, user.id, pid
            )
            await call.answer("Сумма оплаты не совпадает с ценой товара. Напишите в поддержку.", show_alert=True)
            return
        if invoice_asset and invoice_asset != asset:
            logger.warning(
                "Invoice asset mismatch: expected=%s got=%s user=%s product=%s",
                asset, invoice_asset, user.id, pid
            )
            await call.answer("Валюта оплаты не совпадает. Напишите в поддержку.", show_alert=True)
            return

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
        _all_products = await load_products()
        product = next((p for p in _all_products if p["product_id"] == pid), None)
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
    _all_products = await load_products()
    product = next((p for p in _all_products if p["product_id"] == pid), None)
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
    global _products_cache, _purchases_sheet_title
    _products_cache = (0.0, [])
    _purchases_sheet_title = None
    logger.info("Admin triggered cache refresh")
    await message.answer("✅ Кеш товаров очищен. Следующая загрузка CSV будет с нуля.")


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


# =========================
# WEBHOOK / POLLING — автовыбор
# =========================

WEBHOOK_HOST = os.getenv("RAILWAY_PUBLIC_DOMAIN", "").strip()
WEBHOOK_PATH = f"/webhook/{BOT_TOKEN}"
WEBHOOK_URL = f"https://{WEBHOOK_HOST}{WEBHOOK_PATH}" if WEBHOOK_HOST else ""
WEBAPP_PORT = int(os.getenv("PORT", 8080))


async def on_startup(dp):
    init_db()
    if WEBHOOK_URL:
        await bot.set_webhook(WEBHOOK_URL)
        logger.info("Webhook set: %s", WEBHOOK_URL)
    else:
        logger.info("No RAILWAY_PUBLIC_DOMAIN — using polling")


async def on_shutdown(dp):
    if WEBHOOK_URL:
        await bot.delete_webhook()


if __name__ == "__main__":
    if WEBHOOK_URL:
        # aiogram 2.x встроенный webhook через executor
        executor.start_webhook(
            dispatcher=dp,
            webhook_path=WEBHOOK_PATH,
            on_startup=on_startup,
            on_shutdown=on_shutdown,
            skip_updates=True,
            host="0.0.0.0",
            port=WEBAPP_PORT,
        )
    else:
        init_db()
        executor.start_polling(dp, skip_updates=True)
