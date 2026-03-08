import csv
import io
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
# НАСТРОЙКИ (8559074588:AAG8xcsaS0f5s-GNvLCP64Ejcg5vhOj6dpI)
# =========================

BOT_TOKEN = "8559074588:AAG8xcsaS0f5s-GNvLCP64Ejcg5vhOj6dpI"

# Таблица ТОВАРОВ (публичная, CSV):
PRODUCTS_CSV_URL = "https://docs.google.com/spreadsheets/d/1V1LCKR13JNply4LAEfJBtYNAE854Zr8aBBMTUTC2kPA/gviz/tq?tqx=out:csv"

# Таблица ПОКУПОК (приватная):
PURCHASES_SHEET_ID = "1SHhqCUS4c_-vPkaY5R38975RjlRLU0y-RvICQ7zrze0"

# Путь к JSON ключу service account
SERVICE_ACCOUNT_JSON_PATH = "artkids-bot-dd8894a2e080.json"

# Админ и поддержка
ADMIN_CHAT_ID = 8491241832
AUTHOR_USERNAME = "art_kids_support"  # без @

# Telegram Stars
CURRENCY = "XTR"
PROVIDER_TOKEN = ""  # для Stars пусто

# Бесплатная категория (точно как в таблице!)
FREE_CATEGORY_NAME = "🎁 Бесплатные материалы"

# Таймауты
HTTP_TIMEOUT = 15

# Кеши
PRODUCTS_CACHE_TTL = 60
PURCHASES_CACHE_TTL = 60


# =========================
# ЛОГИ
# =========================

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("artkids_bot")

bot = Bot(token=BOT_TOKEN.strip())
dp = Dispatcher(bot)


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

def get_sheets_service():
    global _sheets_service
    if _sheets_service is not None:
        return _sheets_service

    creds = Credentials.from_service_account_file(
        SERVICE_ACCOUNT_JSON_PATH,
        scopes=_SCOPES
    )
    _sheets_service = build("sheets", "v4", credentials=creds, cache_discovery=False)
    return _sheets_service

def get_purchases_sheet_title() -> str:
    global _purchases_sheet_title
    if _purchases_sheet_title:
        return _purchases_sheet_title

    service = get_sheets_service()
    meta = service.spreadsheets().get(spreadsheetId=PURCHASES_SHEET_ID).execute()
    sheets = meta.get("sheets", [])
    if not sheets:
        raise RuntimeError("В таблице покупок нет листов.")

    _purchases_sheet_title = sheets[0]["properties"]["title"]
    return _purchases_sheet_title


# =========================
# ТОВАРЫ (CSV)
# =========================

_products_cache: Tuple[float, List[Dict[str, Any]]] = (0.0, [])

def load_products() -> List[Dict[str, Any]]:
    """
    Колонки:
    product_id | title | description | price_xtr | file_id | active | category | preview_file_id
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
            active_raw = str(row.get("active", "")).strip().lower()
            is_active = active_raw in ("true", "1", "yes", "y", "да")
            if not is_active:
                continue

            pid = str(row.get("product_id", "")).strip()
            title = str(row.get("title", "")).strip()
            desc = str(row.get("description", "")).strip()
            file_id = str(row.get("file_id", "")).strip()
            preview_file_id = str(row.get("preview_file_id", "")).strip()
            category = str(row.get("category", "")).strip() or "Без категории"

            if not pid or not title or not file_id:
                continue

            price_raw = str(row.get("price_xtr", "")).strip()
            price = int(price_raw) if price_raw != "" else 0
            if price < 0:
                continue

            products.append({
                "product_id": pid,
                "title": title,
                "description": desc or "PDF файл",
                "price_xtr": price,
                "file_id": file_id,
                "preview_file_id": preview_file_id,
                "category": category,
            })
        except Exception:
            continue

    _products_cache = (time.time(), products)
    return products

def is_free_product(p: Dict[str, Any]) -> bool:
    cat = str(p.get("category", "")).strip()
    return (int(p.get("price_xtr", 0)) == 0) or (cat == FREE_CATEGORY_NAME)


# =========================
# SAFE callback_data для категорий
# =========================

_cat_key_to_name: Dict[str, str] = {}

def _cat_key(name: str) -> str:
    return hashlib.sha1(name.encode("utf-8")).hexdigest()[:10]

def categories_keyboard(categories: List[str]) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    _cat_key_to_name.clear()

    for c in categories:
        c_clean = str(c).strip()
        key = _cat_key(c_clean)
        _cat_key_to_name[key] = c_clean
        kb.add(InlineKeyboardButton(text=c_clean, callback_data=f"catk:{key}"))

    # Глобальную "Назад" НЕ делаем (по UX-решению)
    return kb

def products_keyboard(products: List[Dict[str, Any]], category_key: str) -> InlineKeyboardMarkup:
    """
    Передаём category_key, чтобы кнопка item:PID знала, куда возвращаться.
    """
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

def _read_all_purchases_rows() -> List[Dict[str, str]]:
    service = get_sheets_service()
    sheet_title = get_purchases_sheet_title()
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

def get_purchases_cached(force: bool = False) -> List[Dict[str, str]]:
    global _purchases_cache
    ts, cached = _purchases_cache
    if not force and cached and (time.time() - ts) < PURCHASES_CACHE_TTL:
        return cached
    rows = _read_all_purchases_rows()
    _purchases_cache = (time.time(), rows)
    return rows

def user_has_purchase(user_id: int, product_id: str) -> bool:
    rows = get_purchases_cached()
    uid = str(user_id)
    pid = str(product_id)
    for r in rows:
        if r.get("user_id") == uid and r.get("product_id") == pid:
            return True
    return False

def get_user_purchase_row(user_id: int, product_id: str) -> Optional[Dict[str, str]]:
    rows = get_purchases_cached()
    uid = str(user_id)
    pid = str(product_id)
    found = None
    for r in rows:
        if r.get("user_id") == uid and r.get("product_id") == pid:
            found = r
    return found

def append_purchase_row(user: types.User, product: Dict[str, Any], price_xtr: int) -> bool:
    """
    Пишем A:H:
    date | user_id | username | full_name | product_id | product_title | price_xtr | file_id
    """
    try:
        service = get_sheets_service()
        sheet_title = get_purchases_sheet_title()

        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        username = f"@{user.username}" if user.username else ""

        row = [
            now,
            str(user.id),
            username,
            user.full_name,
            product["product_id"],
            product["title"],
            str(price_xtr),
            product.get("file_id", ""),
        ]

        service.spreadsheets().values().append(
            spreadsheetId=PURCHASES_SHEET_ID,
            range=f"{sheet_title}!A:H",
            valueInputOption="USER_ENTERED",
            insertDataOption="INSERT_ROWS",
            body={"values": [row]}
        ).execute()

        global _purchases_cache
        _purchases_cache = (0.0, [])
        return True

    except Exception as e:
        logger.exception("Не удалось записать покупку в таблицу: %s", e)
        return False


# =========================
# START / HELP
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

    categories = sorted(set(str(p.get("category", "")).strip() for p in products if p.get("category")))
    await message.answer("📚 Выберите категорию:", reply_markup=categories_keyboard(categories))


# =========================
# МОИ ПОКУПКИ
# =========================

@dp.message_handler(lambda m: m.text == "📂 Мои покупки")
async def show_my_purchases(message: types.Message):
    await send_my_purchases(message.chat.id, message.from_user)

async def send_my_purchases(chat_id: int, user: types.User):
    rows = get_purchases_cached()
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
        pid = (r.get("product_id") or "").strip()
        if pid and pid not in seen:
            seen.add(pid)
            unique_rows.append(r)

    await bot.send_message(chat_id, "📂 Ваши покупки:")

    for r in unique_rows:
        pid = (r.get("product_id") or "").strip()
        title = (r.get("product_title") or "").strip() or (prod_map.get(pid, {}).get("title", "PDF"))

        price_from_row = (r.get("price_xtr") or "").strip()
        is_free_row = (price_from_row == "" or price_from_row == "0")

        emoji = "🎁" if is_free_row else "⭐"
        meta = "🎁 Бесплатно" if is_free_row else f"⭐ {price_from_row} ⭐"

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
    categories = sorted(set(str(p.get("category", "")).strip() for p in products if p.get("category")))
    await bot.send_message(call.message.chat.id, "📚 Выберите категорию:", reply_markup=categories_keyboard(categories))


# =========================
# КАТЕГОРИЯ -> ТОВАРЫ
# =========================

@dp.callback_query_handler(lambda c: c.data.startswith("catk:"))
async def cb_category(call: types.CallbackQuery):
    key = call.data.split("catk:", 1)[1].strip()
    category = _cat_key_to_name.get(key)

    # восстановление мапы на случай перезапуска
    if not category:
        products_all = load_products()
        cats = sorted(set(str(p.get("category", "")).strip() for p in products_all if p.get("category")))
        for c in cats:
            _cat_key_to_name[_cat_key(c)] = c
        category = _cat_key_to_name.get(key)

    if not category:
        await call.answer("Категория устарела. Откройте каталог заново.", show_alert=True)
        return

    products = [p for p in load_products() if str(p.get("category", "")).strip() == category]
    if not products:
        await call.answer("Пока пусто.", show_alert=True)
        return

    # Важно: передаём category_key, чтобы работал локальный "Назад"
    await call.message.answer(f"📂 {category}", reply_markup=products_keyboard(products, category_key=key))
    await call.answer()


# =========================
# ПРЕДПРОСМОТР ТОВАРА + ЛОКАЛЬНАЯ КНОПКА "НАЗАД"
# =========================

def product_action_kb(product: Dict[str, Any], category_key: str) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    pid = product["product_id"]

    if is_free_product(product):
        kb.add(InlineKeyboardButton("🎁 Скачать бесплатно", callback_data=f"get:{pid}"))
    else:
        kb.add(InlineKeyboardButton(f"⭐ Купить за {product['price_xtr']} ⭐", callback_data=f"pay:{pid}"))

    # ✅ ЛОКАЛЬНАЯ "Назад" только в карточке товара
    kb.add(InlineKeyboardButton("⬅️ Назад к списку", callback_data=f"back_items:{category_key}"))
    return kb

def format_product_card(product: Dict[str, Any]) -> str:
    title = product.get("title", "PDF")
    desc = (product.get("description") or "").strip() or "PDF файл"
    price_line = "🎁 Бесплатно" if is_free_product(product) else f"⭐ Цена: {int(product.get('price_xtr', 0))} ⭐"
    return f"📄 <b>{title}</b>\n\n{desc}\n\n{price_line}"

@dp.callback_query_handler(lambda c: c.data.startswith("item:"))
async def cb_item(call: types.CallbackQuery):
    # Ожидаем формат: item:PID:CATKEY
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
    preview_id = (product.get("preview_file_id") or "").strip()

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

    # восстановление мапы после перезапуска
    if not category:
        products_all = load_products()
        cats = sorted(set(str(p.get("category", "")).strip() for p in products_all if p.get("category")))
        for c in cats:
            _cat_key_to_name[_cat_key(c)] = c
        category = _cat_key_to_name.get(category_key)

    if not category:
        await call.answer("Категория устарела. Откройте каталог заново.", show_alert=True)
        return

    products = [p for p in load_products() if str(p.get("category", "")).strip() == category]
    if not products:
        await call.answer("В категории пока нет товаров.", show_alert=True)
        return

    text = f"📂 {category}"
    kb = products_keyboard(products, category_key=category_key)

    try:
        msg = call.message

        # 🧠 если сообщение было с фото → редактируем caption
        if msg.photo:
            await msg.edit_caption(caption=text, reply_markup=kb)

        # 🧠 если обычное текстовое сообщение
        else:
            await msg.edit_text(text, reply_markup=kb)

    except Exception as e:
        # fallback — новое сообщение (на всякий случай)
        logger.exception("edit back_items failed, fallback to answer(): %s", e)
        await call.message.answer(text, reply_markup=kb)

    await call.answer()




# =========================
# ДЕЙСТВИЯ: бесплатно / оплатить
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
    if user_has_purchase(user.id, pid):
        await call.answer()
        await bot.send_document(call.message.chat.id, product["file_id"])
        return

    await call.answer()
    await bot.send_document(call.message.chat.id, product["file_id"])
    append_purchase_row(user=user, product=product, price_xtr=0)

@dp.callback_query_handler(lambda c: c.data.startswith("pay:"))
async def cb_pay(call: types.CallbackQuery):
    pid = call.data.split("pay:", 1)[1].strip()
    product = next((p for p in load_products() if p["product_id"] == pid), None)
    if not product:
        await call.answer("Материал не найден.", show_alert=True)
        return
    if is_free_product(product):
        await call.answer("Этот материал бесплатный.", show_alert=True)
        return

    user = call.from_user
    if user_has_purchase(user.id, pid):
        await call.answer()
        await bot.send_document(call.message.chat.id, product["file_id"])
        return

    try:
        await bot.send_invoice(
            chat_id=call.message.chat.id,
            title=product["title"],
            description=product["description"],
            payload=f"buy:{pid}",
            provider_token=PROVIDER_TOKEN,
            currency=CURRENCY,
            prices=[LabeledPrice(label=product["title"], amount=int(product["price_xtr"]))],
            start_parameter=f"buy_{pid}"
        )
        await call.answer()
    except Exception as e:
        logger.exception("Ошибка send_invoice: %s", e)
        await call.answer("Не удалось создать счёт. Проверь Stars в настройках бота.", show_alert=True)


# =========================
# СКАЧАТЬ ИЗ МОИХ ПОКУПОК (не зависит от active)
# =========================

@dp.callback_query_handler(lambda c: c.data.startswith("dl:"))
async def cb_download(call: types.CallbackQuery):
    pid = call.data.split("dl:", 1)[1].strip()
    user = call.from_user

    purchase_row = get_user_purchase_row(user.id, pid)
    if not purchase_row:
        await call.answer("Покупка не найдена. Откройте «Мои покупки» заново.", show_alert=True)
        return

    file_id_from_row = (purchase_row.get("file_id") or "").strip()

    # fallback для старых строк без file_id
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
# =========================

@dp.pre_checkout_query_handler(lambda q: True)
async def pre_checkout(pre_checkout_q: types.PreCheckoutQuery):
    await bot.answer_pre_checkout_query(pre_checkout_q.id, ok=True)

@dp.message_handler(content_types=types.ContentType.SUCCESSFUL_PAYMENT)
async def successful_payment(message: types.Message):
    payload = message.successful_payment.invoice_payload
    if not payload.startswith("buy:"):
        await message.answer("Оплата получена, но товар не распознан.")
        return

    pid = payload.split("buy:", 1)[1].strip()
    product = next((p for p in load_products() if p["product_id"] == pid), None)
    if not product:
        await message.answer("Оплата получена, но материал сейчас недоступен.")
        return

    expected = int(product["price_xtr"])
    paid_amount = int(message.successful_payment.total_amount)
    if paid_amount != expected:
        await message.answer("Ошибка суммы оплаты. Напишите автору через /help.")
        return

    user = message.from_user
    if user_has_purchase(user.id, pid):
        await bot.send_document(message.chat.id, product["file_id"])
        return

    await bot.send_document(message.chat.id, product["file_id"])
    append_purchase_row(user=user, product=product, price_xtr=expected)

    # Уведомление админу (только платные)
    try:
        username = f"@{user.username}" if user.username else "нет"
        admin_text = (
            "💰 <b>Новая покупка!</b>\n\n"
            f"📄 <b>Товар:</b> {product['title']}\n"
            f"⭐ <b>Цена:</b> {expected} ⭐\n\n"
            f"👤 <b>Покупатель:</b>\n"
            f"ID: <code>{user.id}</code>\n"
            f"Имя: {user.full_name}\n"
            f"Username: {username}"
        )
        await bot.send_message(ADMIN_CHAT_ID, admin_text, parse_mode="HTML")
    except Exception as e:
        logger.exception("Не удалось уведомить админа: %s", e)


# =========================
# ADMIN: refresh caches + debug file_id (doc/photo)
# =========================

@dp.message_handler(commands=["refresh"], user_id=ADMIN_CHAT_ID)
async def cmd_refresh(message: types.Message):
    global _products_cache, _purchases_cache, _purchases_sheet_title, _cat_key_to_name
    _products_cache = (0.0, [])
    _purchases_cache = (0.0, [])
    _purchases_sheet_title = None
    _cat_key_to_name.clear()
    await message.answer("✅ Кеши очищены. Следующая загрузка будет “с нуля”.")

@dp.message_handler(content_types=types.ContentType.DOCUMENT, user_id=ADMIN_CHAT_ID)
async def debug_get_file_id_doc(message: types.Message):
    await message.reply(
        f"📄 file_id:\n<code>{message.document.file_id}</code>",
        parse_mode="HTML"
    )

@dp.message_handler(content_types=types.ContentType.PHOTO, user_id=ADMIN_CHAT_ID)
async def debug_get_file_id_photo(message: types.Message):
    photo = message.photo[-1]
    await message.reply(
        f"🖼 preview_file_id:\n<code>{photo.file_id}</code>",
        parse_mode="HTML"
    )


if __name__ == "__main__":
    executor.start_polling(dp, skip_updates=True)
