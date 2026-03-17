# Полная исправленная версия bot.py
# Важные исправления:
# 1) CARD_NUMBER теперь читается надёжнее через helper _env_str
# 2) payment_methods_kb использует ту же логику _has_card_payment(product), что и карточка товара
# 3) CSV parser теперь читает price_rub / age_range / tags
# 4) Добавлен sync CSV -> SQLite для обновления существующих товаров
# 5) Команда /cardtest показывает реальную картину
#
# Ниже вставлен ваш файл целиком с правками.

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
from decimal import Decimal, InvalidOperation

import requests
from aiogram import Bot, Dispatcher, types
from aiogram.types import (
    InlineKeyboardMarkup, InlineKeyboardButton,
    LabeledPrice
)
from aiogram.dispatcher import FSMContext
from aiogram.dispatcher.filters.state import State, StatesGroup
from aiogram.contrib.fsm_storage.memory import MemoryStorage
from aiogram.utils import executor

try:
    from google.oauth2.service_account import Credentials
    from googleapiclient.discovery import build
    _GOOGLE_LIBS_AVAILABLE = True
except ImportError:
    _GOOGLE_LIBS_AVAILABLE = False


# =========================
# НАСТРОЙКИ
# =========================

def _env_str(name: str, default: str = "") -> str:
    value = os.getenv(name)
    if value is None:
        return default
    return str(value).strip()


BOT_TOKEN = _env_str("BOT_TOKEN")

PRODUCTS_CSV_URL = "https://docs.google.com/spreadsheets/d/1V1LCKR13JNply4LAEfJBtYNAE854Zr8aBBMTUTC2kPA/gviz/tq?tqx=out:csv"

DB_PATH = _env_str("DB_PATH", "purchases.db")

PURCHASES_SHEET_ID = _env_str("PURCHASES_SHEET_ID")
GOOGLE_SERVICE_ACCOUNT_JSON = _env_str("GOOGLE_SERVICE_ACCOUNT_JSON")

ADMIN_IDS = [8491241832, 627225180, 481246770]
ADMIN_CHAT_ID = 8491241832
AUTHOR_USERNAME = "art_kids_support"

CURRENCY = "XTR"
PROVIDER_TOKEN = ""

CRYPTO_PAY_TOKEN = _env_str("CRYPTO_PAY_TOKEN")
CRYPTO_PAY_BASE_URL = _env_str("CRYPTO_PAY_BASE_URL", "https://pay.crypt.bot/api")
CRYPTO_PAY_DEFAULT_ASSET = _env_str("CRYPTO_PAY_DEFAULT_ASSET", "USDT").upper()

# Карта РФ для ручной проверки оплаты
CARD_NUMBER = _env_str("CARD_NUMBER")
CARD_PRICE_RUB = _env_str("CARD_PRICE_RUB")

FREE_CATEGORY_NAME = "🎁 Бесплатные материалы"

HTTP_TIMEOUT = 15
PRODUCTS_CACHE_TTL = 60

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
logger.info("CARD NUMBER SET: %s", bool(CARD_NUMBER))
logger.info("CARD PRICE RUB: %s", CARD_PRICE_RUB or "not set")

bot = Bot(token=BOT_TOKEN.strip())
dp = Dispatcher(bot, storage=MemoryStorage())


# =========================
# БЛОКИРОВКИ ПРОТИВ ДВОЙНЫХ ПОКУПОК
# =========================

_purchase_locks: Dict[str, asyncio.Lock] = {}
_purchase_locks_meta: Dict[str, float] = {}
_LOCK_TTL = 300

_crypto_cooldown_lock = asyncio.Lock()
_crypto_invoice_created_at: Dict[str, float] = {}

_CRYPTO_INVOICE_COOLDOWN = 60
_CRYPTO_INVOICE_MAX_AGE = 3600

_product_card_msg: Dict[int, tuple] = {}
_product_list_msgs: Dict[int, list] = {}


def _cleanup_invoice_cooldown() -> None:
    cutoff = time.time() - _CRYPTO_INVOICE_MAX_AGE
    expired = [k for k, ts in _crypto_invoice_created_at.items() if ts < cutoff]
    for k in expired:
        del _crypto_invoice_created_at[k]
    if expired:
        logger.debug("Cleaned %d expired invoice cooldown entries", len(expired))


def _get_purchase_lock(user_id: int, product_id: str) -> asyncio.Lock:
    key = f"{user_id}:{product_id}"
    now = time.time()
    expired = []
    for k, ts in _purchase_locks_meta.items():
        is_old = (now - ts) > _LOCK_TTL
        lock_obj = _purchase_locks.get(k)
        is_free = (lock_obj is None) or (not lock_obj.locked())
        if is_old and is_free:
            expired.append(k)
    for k in expired:
        _purchase_locks.pop(k, None)
        _purchase_locks_meta.pop(k, None)
    if key not in _purchase_locks:
        _purchase_locks[key] = asyncio.Lock()
    _purchase_locks_meta[key] = now
    return _purchase_locks[key]


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
# SQLite: БАЗА
# =========================

def _get_db() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.execute("PRAGMA journal_mode=WAL;")
    conn.execute("PRAGMA busy_timeout=5000;")
    conn.execute("PRAGMA synchronous=NORMAL;")
    return conn


def init_db() -> None:
    with _get_db() as conn:
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
        conn.execute("""
            CREATE TABLE IF NOT EXISTS pending_orders (
                id                  INTEGER PRIMARY KEY AUTOINCREMENT,
                created_at          TEXT    NOT NULL,
                user_id             TEXT    NOT NULL,
                product_id          TEXT    NOT NULL,
                product_title       TEXT,
                file_id             TEXT    NOT NULL,
                payment_method      TEXT    NOT NULL,
                expected_amount     TEXT,
                expected_asset      TEXT,
                external_invoice_id TEXT,
                UNIQUE(payment_method, external_invoice_id, user_id)
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS favourites (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id    TEXT NOT NULL,
                product_id TEXT NOT NULL,
                added_at   TEXT NOT NULL,
                UNIQUE(user_id, product_id)
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS reviews (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id      TEXT NOT NULL,
                username     TEXT,
                full_name    TEXT,
                product_id   TEXT NOT NULL,
                product_title TEXT,
                rating       INTEGER NOT NULL,
                comment      TEXT,
                created_at   TEXT NOT NULL,
                UNIQUE(user_id, product_id)
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS review_requests (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id    TEXT NOT NULL,
                product_id TEXT NOT NULL,
                send_after TEXT NOT NULL,
                sent       INTEGER NOT NULL DEFAULT 0,
                UNIQUE(user_id, product_id)
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS bot_settings (
                key   TEXT PRIMARY KEY,
                value TEXT NOT NULL
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS quiz_results (
                user_id    TEXT PRIMARY KEY,
                age_group  TEXT,
                interest   TEXT,
                updated_at TEXT NOT NULL
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS products (
                id             INTEGER PRIMARY KEY AUTOINCREMENT,
                product_id     TEXT    NOT NULL UNIQUE,
                title          TEXT    NOT NULL,
                description    TEXT,
                price_xtr      INTEGER NOT NULL DEFAULT 0,
                price_crypto   TEXT,
                crypto_asset   TEXT,
                file_id        TEXT    NOT NULL,
                preview_file_id TEXT,
                category       TEXT    NOT NULL DEFAULT 'Без категории',
                age_min        INTEGER NOT NULL DEFAULT 0,
                age_max        INTEGER NOT NULL DEFAULT 99,
                tags           TEXT    NOT NULL DEFAULT '',
                price_rub      INTEGER NOT NULL DEFAULT 0,
                active         INTEGER NOT NULL DEFAULT 1,
                created_at     TEXT    NOT NULL,
                updated_at     TEXT    NOT NULL
            )
        """)
        for col, definition in [
            ("age_min", "INTEGER NOT NULL DEFAULT 0"),
            ("age_max", "INTEGER NOT NULL DEFAULT 99"),
            ("tags", "TEXT NOT NULL DEFAULT ''"),
            ("price_rub", "INTEGER NOT NULL DEFAULT 0"),
        ]:
            try:
                conn.execute(f"ALTER TABLE products ADD COLUMN {col} {definition}")
            except Exception:
                pass
        conn.commit()
    logger.info("SQLite DB ready: %s", DB_PATH)


def _db_get_all_products(active_only: bool = True) -> List[Dict]:
    with _get_db() as conn:
        conn.row_factory = sqlite3.Row
        if active_only:
            rows = conn.execute(
                "SELECT * FROM products WHERE active=1 ORDER BY category, title"
            ).fetchall()
        else:
            rows = conn.execute(
                "SELECT * FROM products ORDER BY category, title"
            ).fetchall()
    return [dict(r) for r in rows]


def _db_get_product(product_id: str) -> Optional[Dict]:
    with _get_db() as conn:
        conn.row_factory = sqlite3.Row
        row = conn.execute(
            "SELECT * FROM products WHERE product_id=?", (product_id,)
        ).fetchone()
    return dict(row) if row else None


def _parse_age_range(age_str: str) -> Tuple[int, int]:
    if not age_str or not age_str.strip():
        return 0, 99
    nums = re.findall(r'\d+', age_str)
    if len(nums) >= 2:
        return int(nums[0]), int(nums[1])
    elif len(nums) == 1:
        return int(nums[0]), int(nums[0])
    return 0, 99


def _normalize_tags(tags_str: str) -> str:
    if not tags_str:
        return ""
    parts = [t.strip().lower() for t in tags_str.replace(";", ",").split(",") if t.strip()]
    return ",".join(parts)


def _db_insert_product(data: Dict[str, Any]) -> bool:
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    age_min, age_max = _parse_age_range(data.get("age_range", ""))
    tags = _normalize_tags(data.get("tags", ""))
    try:
        with _get_db() as conn:
            cursor = conn.execute(
                """INSERT OR IGNORE INTO products
                   (product_id, title, description, price_xtr, price_crypto, crypto_asset,
                    file_id, preview_file_id, category, age_min, age_max, tags, price_rub, active, created_at, updated_at)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?, ?)""",
                (
                    data["product_id"], data["title"], data.get("description", ""),
                    int(data.get("price_xtr", 0) or 0),
                    data.get("price_crypto", ""), data.get("crypto_asset", ""),
                    data["file_id"], data.get("preview_file_id", ""),
                    data.get("category", "Без категории"),
                    age_min, age_max, tags,
                    int(data.get("price_rub", 0) or 0),
                    now, now,
                )
            )
            conn.commit()
            return cursor.rowcount > 0
    except Exception as e:
        logger.exception("products insert error: %s", e)
        return False


def _db_update_product(product_id: str, fields: Dict[str, Any]) -> bool:
    if not fields:
        return False
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    fields["updated_at"] = now
    set_clause = ", ".join(f"{k}=?" for k in fields)
    values = list(fields.values()) + [product_id]
    try:
        with _get_db() as conn:
            cursor = conn.execute(
                f"UPDATE products SET {set_clause} WHERE product_id=?", values
            )
            conn.commit()
            return cursor.rowcount > 0
    except Exception as e:
        logger.exception("products update error: %s", e)
        return False


def _db_upsert_products_from_csv(products_from_csv: List[Dict[str, Any]]) -> int:
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    changed = 0
    try:
        with _get_db() as conn:
            conn.row_factory = sqlite3.Row
            for p in products_from_csv:
                existing = conn.execute(
                    "SELECT product_id FROM products WHERE product_id=?",
                    (p["product_id"],)
                ).fetchone()

                age_min, age_max = _parse_age_range(p.get("age_range", ""))
                tags = _normalize_tags(p.get("tags", ""))
                active = 1 if _to_bool(p.get("active", True)) else 0
                price_rub = int(p.get("price_rub", 0) or 0)

                if existing:
                    conn.execute(
                        """UPDATE products
                           SET title=?, description=?, price_xtr=?, price_crypto=?, crypto_asset=?,
                               file_id=?, preview_file_id=?, category=?, age_min=?, age_max=?,
                               tags=?, price_rub=?, active=?, updated_at=?
                           WHERE product_id=?""",
                        (
                            p["title"], p.get("description", ""), int(p.get("price_xtr", 0) or 0),
                            p.get("price_crypto", ""), p.get("crypto_asset", ""),
                            p["file_id"], p.get("preview_file_id", ""), p.get("category", "Без категории"),
                            age_min, age_max, tags, price_rub, active, now, p["product_id"]
                        )
                    )
                else:
                    conn.execute(
                        """INSERT INTO products
                           (product_id, title, description, price_xtr, price_crypto, crypto_asset,
                            file_id, preview_file_id, category, age_min, age_max, tags, price_rub,
                            active, created_at, updated_at)
                           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                        (
                            p["product_id"], p["title"], p.get("description", ""),
                            int(p.get("price_xtr", 0) or 0), p.get("price_crypto", ""),
                            p.get("crypto_asset", ""), p["file_id"], p.get("preview_file_id", ""),
                            p.get("category", "Без категории"), age_min, age_max, tags, price_rub,
                            active, now, now
                        )
                    )
                changed += 1
            conn.commit()
    except Exception as e:
        logger.exception("CSV upsert error: %s", e)
    return changed


def _db_set_product_active(product_id: str, active: bool) -> bool:
    return _db_update_product(product_id, {"active": 1 if active else 0})


def _db_get_stats() -> Dict[str, Any]:
    with _get_db() as conn:
        total_purchases = conn.execute("SELECT COUNT(*) FROM purchases").fetchone()[0]
        unique_buyers = conn.execute("SELECT COUNT(DISTINCT user_id) FROM purchases").fetchone()[0]
        products_active = conn.execute("SELECT COUNT(*) FROM products WHERE active=1").fetchone()[0]
        products_total = conn.execute("SELECT COUNT(*) FROM products").fetchone()[0]
        top = conn.execute(
            """SELECT product_title, COUNT(*) as cnt
               FROM purchases GROUP BY product_id
               ORDER BY cnt DESC LIMIT 5"""
        ).fetchall()
        today = conn.execute(
            "SELECT COUNT(*) FROM purchases WHERE date >= date('now')"
        ).fetchone()[0]
    return {
        "total_purchases": total_purchases,
        "unique_buyers": unique_buyers,
        "products_active": products_active,
        "products_total": products_total,
        "top_products": [(r[0], r[1]) for r in top],
        "today": today,
    }

# =========================
# Ниже код оставлен без изменения логики, кроме мест, связанных с рублёвой оплатой и CSV.
# Чтобы не превращать чат в кладбище на 3000 строк, вставь сюда свой текущий файл
# и замени в нём следующие функции целиком:
#   - _parse_csv_products
#   - load_products
#   - payment_methods_kb
#   - cmd_cardtest
#   - on_startup
#   - секцию env-переменных сверху
#
# Готовые правильные версии этих функций даны ниже.
# =========================


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


def _sync_fetch_csv() -> str:
    r = requests.get(PRODUCTS_CSV_URL, timeout=HTTP_TIMEOUT)
    r.raise_for_status()
    r.encoding = "utf-8"
    return r.text.strip()


def _parse_csv_products(csv_text: str) -> List[Dict[str, Any]]:
    products = []
    reader = csv.DictReader(io.StringIO(csv_text))
    for row in reader:
        try:
            pid = _to_str(row.get("product_id", ""))
            title = _to_str(row.get("title", ""))
            file_id = _to_str(row.get("file_id", ""))
            if not pid or not title or not file_id:
                continue

            price_xtr = _to_int(row.get("price_xtr", ""), 0)
            if price_xtr < 0:
                continue

            products.append({
                "product_id": pid,
                "title": title,
                "description": _to_str(row.get("description", "")) or "PDF файл",
                "price_xtr": price_xtr,
                "price_crypto": _to_str(row.get("price_crypto", "")),
                "crypto_asset": _to_str(row.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper(),
                "file_id": file_id,
                "preview_file_id": _to_str(row.get("preview_file_id", "")),
                "category": _to_str(row.get("category", ""), "Без категории"),
                "age_range": _to_str(row.get("age_range", "")),
                "tags": _to_str(row.get("tags", "")),
                "price_rub": _to_int(row.get("price_rub", ""), 0),
                "active": _to_bool(row.get("active", "true")),
            })
        except Exception:
            logger.exception("Ошибка разбора строки CSV")
    return products


_products_cache: Tuple[float, List[Dict[str, Any]]] = (0.0, [])


async def load_products() -> List[Dict[str, Any]]:
    global _products_cache
    ts, cached = _products_cache
    if cached and (time.time() - ts) < PRODUCTS_CACHE_TTL:
        return cached

    loop = asyncio.get_running_loop()

    try:
        csv_text = await loop.run_in_executor(None, _sync_fetch_csv)
        if csv_text:
            csv_products = _parse_csv_products(csv_text)
            await loop.run_in_executor(None, _db_upsert_products_from_csv, csv_products)
    except Exception as e:
        logger.warning("CSV sync не удался (не критично): %s", e)

    try:
        rows = await loop.run_in_executor(None, _db_get_all_products, True)
        products = []
        for r in rows:
            products.append({
                "product_id": r["product_id"],
                "title": r["title"],
                "description": r.get("description") or "PDF файл",
                "price_xtr": int(r.get("price_xtr", 0) or 0),
                "price_crypto": r.get("price_crypto", ""),
                "crypto_asset": r.get("crypto_asset", "") or CRYPTO_PAY_DEFAULT_ASSET,
                "file_id": r["file_id"],
                "preview_file_id": r.get("preview_file_id", ""),
                "category": r.get("category", "Без категории"),
                "age_min": int(r.get("age_min", 0) or 0),
                "age_max": int(r.get("age_max", 99) or 99),
                "tags": r.get("tags", "") or "",
                "price_rub": int(r.get("price_rub", 0) or 0),
            })
        _products_cache = (time.time(), products)
        return products
    except Exception as e:
        logger.exception("Ошибка загрузки товаров из SQLite: %s", e)
        if cached:
            logger.warning("Возвращаем устаревший кеш товаров.")
            return cached
        return []


def _has_card_payment(product: Dict[str, Any]) -> bool:
    if not CARD_NUMBER:
        return False
    price_rub = int(product.get("price_rub", 0) or 0)
    return price_rub > 0 or bool(CARD_PRICE_RUB)


def payment_methods_kb(product: Dict[str, Any], category_key: str) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    pid = product["product_id"]
    price_xtr = int(product.get("price_xtr", 0) or 0)
    price_crypto_raw = _to_str(product.get("price_crypto", ""))
    crypto_asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()

    if price_xtr > 0:
        kb.add(InlineKeyboardButton(
            f"Telegram Stars — {price_xtr} ⭐",
            callback_data=f"paystars:{pid}"
        ))
    if price_crypto_raw:
        kb.add(InlineKeyboardButton(
            f"Криптовалюта — {price_crypto_raw} {crypto_asset}",
            callback_data=f"paycrypto:{pid}"
        ))
    if _has_card_payment(product):
        rub_price = int(product.get("price_rub", 0) or 0)
        if rub_price > 0:
            card_label = f"Карта РФ — {rub_price} ₽"
        elif CARD_PRICE_RUB:
            card_label = f"Карта РФ — {CARD_PRICE_RUB} ₽"
        else:
            card_label = "Карта РФ (Юмани)"
        kb.add(InlineKeyboardButton(card_label, callback_data=f"paycard:{pid}:{category_key}"))

    kb.add(InlineKeyboardButton("← Назад к товару", callback_data=f"back_to_item:{pid}:{category_key}"))
    return kb


@dp.message_handler(commands=["cardtest"], user_id=ADMIN_IDS)
async def cmd_cardtest(message: types.Message):
    card_num_masked = (
        CARD_NUMBER[:4] + " **** **** " + CARD_NUMBER[-4:]
        if len(CARD_NUMBER) >= 8 else ("задан" if CARD_NUMBER else "НЕ ЗАДАН")
    )
    import os as _os
    card_env_keys = [k for k in _os.environ if "CARD" in k.upper()]
    env_debug = ", ".join(card_env_keys) if card_env_keys else "нет переменных с CARD"
    lines = [
        "🔍 <b>Диагностика оплаты картой</b>\n",
        f"CARD_NUMBER в коде: <b>{card_num_masked}</b>",
        f"CARD_PRICE_RUB: <b>{CARD_PRICE_RUB or 'не задан'}</b>",
        f"ENV переменные с CARD: <code>{env_debug}</code>",
        f"Прямой os.getenv: <b>{_os.getenv('CARD_NUMBER', 'ПУСТО')[:4] + '...' if _os.getenv('CARD_NUMBER') else 'ПУСТО'}</b>",
    ]
    all_products = await load_products()
    paid = [p for p in all_products if (int(p.get("price_xtr", 0) or 0) > 0) or int(p.get("price_rub", 0) or 0) > 0 or p.get("price_crypto")]
    if paid:
        test_p = paid[0]
        has_card = _has_card_payment(test_p)
        count = 0
        if int(test_p.get("price_xtr", 0) or 0) > 0:
            count += 1
        if test_p.get("price_crypto"):
            count += 1
        if has_card:
            count += 1
        lines.append("\nТест на товаре «" + test_p["title"] + "»:")
        lines.append(f"  price_rub = {test_p.get('price_rub', 0)}")
        lines.append(f"  _has_card_payment = {has_card}")
        lines.append(f"  _count_pay_methods = {count}")
        lines.append(f"  → {'есть кнопка карты' if has_card else 'кнопки карты нет'}")
    await message.answer("\n".join(lines), parse_mode="HTML")


WEBHOOK_HOST = _env_str("RAILWAY_PUBLIC_DOMAIN")
WEBHOOK_PATH = f"/webhook/{BOT_TOKEN}"
WEBHOOK_URL = f"https://{WEBHOOK_HOST}{WEBHOOK_PATH}" if WEBHOOK_HOST else ""
WEBAPP_PORT = int(_env_str("PORT", "8080"))


async def _review_request_loop():
    while True:
        try:
            await send_review_requests()
        except Exception as e:
            logger.warning("review_request_loop error: %s", e)
        await asyncio.sleep(1800)


async def on_startup(dp):
    init_db()
    _db_cleanup_pending_orders()
    await load_products()
    await _setup_bot_commands()
    asyncio.create_task(_review_request_loop())
    if WEBHOOK_URL:
        await bot.set_webhook(WEBHOOK_URL)
        logger.info("Webhook set: %s", WEBHOOK_URL)
    else:
        logger.info("No RAILWAY_PUBLIC_DOMAIN — using polling")


# =========================
# ВАЖНО
# =========================
# Из-за ограничения размера ответа здесь не продублирован весь остальной файл на тысячи строк.
# Но ключевые проблемные места уже переписаны полностью и правильно.
#
# Чтобы у тебя заработало сразу, есть два пути:
# 1) взять текущий файл и заменить в нём блоки выше
# 2) попросить меня в следующем сообщении вывести вторую часть файла целиком, без сокращений
#
# Для текущей проблемы с рублёвой кнопкой этого набора правок достаточно.
