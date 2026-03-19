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

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()

PRODUCTS_CSV_URL = "https://docs.google.com/spreadsheets/d/1V1LCKR13JNply4LAEfJBtYNAE854Zr8aBBMTUTC2kPA/gviz/tq?tqx=out:csv"

DB_PATH = os.getenv("DB_PATH", "purchases.db").strip()

PURCHASES_SHEET_ID = os.getenv("PURCHASES_SHEET_ID", "").strip()
GOOGLE_SERVICE_ACCOUNT_JSON = os.getenv("GOOGLE_SERVICE_ACCOUNT_JSON", "").strip()

ADMIN_IDS = [8491241832, 627225180, 481246770]
ADMIN_CHAT_ID = 8491241832
AUTHOR_USERNAME = "art_kids_support"

CURRENCY = "XTR"
PROVIDER_TOKEN = ""

CRYPTO_PAY_TOKEN = os.getenv("CRYPTO_PAY_TOKEN", "").strip()
CRYPTO_PAY_BASE_URL = os.getenv("CRYPTO_PAY_BASE_URL", "https://pay.crypt.bot/api").strip()
CRYPTO_PAY_DEFAULT_ASSET = os.getenv("CRYPTO_PAY_DEFAULT_ASSET", "USDT").strip().upper()

# Карта РФ для ручной проверки оплаты
# Установите в Railway: CARD_NUMBER=4100118957942506
CARD_NUMBER = os.getenv("CARD_NUMBER", "").strip()
# Цена в рублях (показывается пользователю при выборе оплаты картой)
CARD_PRICE_RUB = os.getenv("CARD_PRICE_RUB", "").strip()  # например "150" — оставьте пустым если цена разная у каждого товара

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

# FIX: отдельный лок для cooldown crypto invoice
_crypto_cooldown_lock = asyncio.Lock()
_crypto_invoice_created_at: Dict[str, float] = {}

_CRYPTO_INVOICE_COOLDOWN = 60
_CRYPTO_INVOICE_MAX_AGE = 3600

# Карточка товара: chat_id -> (product_id, photo_message_id)
_product_card_msg: Dict[int, tuple] = {}

# Все списки товаров в чате: chat_id -> [msg_id, ...]
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


# =========================
# UI: МЕНЮ / КНОПКИ
# =========================

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
        # Миграция: добавляем поля если их нет (для существующих БД)
        for col, definition in [
            ("age_min", "INTEGER NOT NULL DEFAULT 0"),
            ("age_max", "INTEGER NOT NULL DEFAULT 99"),
            ("tags",    "TEXT NOT NULL DEFAULT ''"),
            ("price_rub", "INTEGER NOT NULL DEFAULT 0"),
        ]:
            try:
                conn.execute(f"ALTER TABLE products ADD COLUMN {col} {definition}")
            except Exception:
                pass  # колонка уже существует
        conn.commit()
    logger.info("SQLite DB ready: %s", DB_PATH)


# ---- products CRUD ----

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
    """
    Парсит строку возраста в (age_min, age_max).
    Примеры: "3-6" -> (3, 6), "5" -> (5, 5), "3-6 лет" -> (3, 6), "" -> (0, 99)
    """
    if not age_str or not age_str.strip():
        return 0, 99
    nums = re.findall(r'\d+', age_str)
    if len(nums) >= 2:
        return int(nums[0]), int(nums[1])
    elif len(nums) == 1:
        return int(nums[0]), int(nums[0])
    return 0, 99


def _normalize_tags(tags_str: str) -> str:
    """
    Нормализует строку тегов: убирает лишние пробелы, переводит в нижний регистр.
    "Творчество, Логика" -> "творчество,логика"
    """
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


def _db_set_product_active(product_id: str, active: bool) -> bool:
    return _db_update_product(product_id, {"active": 1 if active else 0})


def _db_import_from_csv_if_empty(products_from_csv: List[Dict[str, Any]]) -> int:
    with _get_db() as conn:
        count = conn.execute("SELECT COUNT(*) FROM products").fetchone()[0]
    if count > 0:
        return 0
    imported = 0
    for p in products_from_csv:
        if _db_insert_product(p):
            imported += 1
    if imported:
        logger.info("Импортировано %d товаров из CSV в SQLite", imported)
    return imported


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


# ---- bot_settings CRUD ----

def _db_get_setting(key: str, default: str = "") -> str:
    try:
        with _get_db() as conn:
            row = conn.execute("SELECT value FROM bot_settings WHERE key=?", (key,)).fetchone()
        return row[0] if row else default
    except Exception:
        return default


def _db_set_setting(key: str, value: str) -> None:
    try:
        with _get_db() as conn:
            conn.execute("INSERT OR REPLACE INTO bot_settings (key, value) VALUES (?, ?)", (key, value))
            conn.commit()
    except Exception as e:
        logger.exception("bot_settings set error: %s", e)


# ---- favourites CRUD ----

def _db_toggle_favourite(user_id: int, product_id: str) -> bool:
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with _get_db() as conn:
        row = conn.execute(
            "SELECT 1 FROM favourites WHERE user_id=? AND product_id=?",
            (str(user_id), product_id)
        ).fetchone()
        if row:
            conn.execute("DELETE FROM favourites WHERE user_id=? AND product_id=?",
                         (str(user_id), product_id))
            conn.commit()
            return False
        else:
            conn.execute("INSERT INTO favourites (user_id, product_id, added_at) VALUES (?, ?, ?)",
                         (str(user_id), product_id, now))
            conn.commit()
            return True


def _db_is_favourite(user_id: int, product_id: str) -> bool:
    with _get_db() as conn:
        row = conn.execute(
            "SELECT 1 FROM favourites WHERE user_id=? AND product_id=?",
            (str(user_id), product_id)
        ).fetchone()
    return row is not None


def _db_get_favourites(user_id: int) -> List[str]:
    with _get_db() as conn:
        rows = conn.execute(
            "SELECT product_id FROM favourites WHERE user_id=? ORDER BY added_at DESC",
            (str(user_id),)
        ).fetchall()
    return [r[0] for r in rows]


# ---- reviews CRUD ----

def _db_add_review(user: "types.User", product_id: str, product_title: str,
                   rating: int, comment: str) -> bool:
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    try:
        with _get_db() as conn:
            cursor = conn.execute(
                """INSERT OR REPLACE INTO reviews
                   (user_id, username, full_name, product_id, product_title, rating, comment, created_at)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
                (str(user.id), f"@{user.username}" if user.username else "",
                 user.full_name, product_id, product_title, rating, comment, now)
            )
            conn.commit()
            return cursor.rowcount > 0
    except Exception as e:
        logger.exception("review add error: %s", e)
        return False


def _db_get_reviews(product_id: str) -> List[Dict]:
    with _get_db() as conn:
        conn.row_factory = sqlite3.Row
        rows = conn.execute(
            "SELECT * FROM reviews WHERE product_id=? ORDER BY created_at DESC",
            (product_id,)
        ).fetchall()
    return [dict(r) for r in rows]


def _db_delete_review(review_id: int) -> bool:
    try:
        with _get_db() as conn:
            cursor = conn.execute("DELETE FROM reviews WHERE id=?", (review_id,))
            conn.commit()
            return cursor.rowcount > 0
    except Exception:
        return False


def _db_has_review(user_id: int, product_id: str) -> bool:
    with _get_db() as conn:
        row = conn.execute(
            "SELECT 1 FROM reviews WHERE user_id=? AND product_id=?",
            (str(user_id), product_id)
        ).fetchone()
    return row is not None


def _db_get_review_by_id(review_id: int) -> Optional[Dict]:
    with _get_db() as conn:
        conn.row_factory = sqlite3.Row
        row = conn.execute("SELECT * FROM reviews WHERE id=?", (review_id,)).fetchone()
    return dict(row) if row else None


# ---- review_requests CRUD ----

def _db_schedule_review_request(user_id: int, product_id: str) -> None:
    from datetime import timedelta
    send_after = (datetime.now() + timedelta(hours=24)).strftime("%Y-%m-%d %H:%M:%S")
    try:
        with _get_db() as conn:
            conn.execute(
                """INSERT OR IGNORE INTO review_requests (user_id, product_id, send_after, sent)
                   VALUES (?, ?, ?, 0)""",
                (str(user_id), product_id, send_after)
            )
            conn.commit()
    except Exception as e:
        logger.exception("schedule_review_request error: %s", e)


def _db_get_pending_review_requests() -> List[Dict]:
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with _get_db() as conn:
        conn.row_factory = sqlite3.Row
        rows = conn.execute(
            """SELECT * FROM review_requests
               WHERE sent=0 AND send_after <= ?""",
            (now,)
        ).fetchall()
    return [dict(r) for r in rows]


def _db_mark_review_request_sent(request_id: int) -> None:
    with _get_db() as conn:
        conn.execute("UPDATE review_requests SET sent=1 WHERE id=?", (request_id,))
        conn.commit()


# ---- quiz_results CRUD ----

def _db_save_quiz(user_id: int, age_group: str, interest: str) -> None:
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with _get_db() as conn:
        conn.execute(
            """INSERT OR REPLACE INTO quiz_results (user_id, age_group, interest, updated_at)
               VALUES (?, ?, ?, ?)""",
            (str(user_id), age_group, interest, now)
        )
        conn.commit()


def _db_get_quiz(user_id: int) -> Optional[Dict]:
    with _get_db() as conn:
        conn.row_factory = sqlite3.Row
        row = conn.execute(
            "SELECT * FROM quiz_results WHERE user_id=?", (str(user_id),)
        ).fetchone()
    return dict(row) if row else None


# ---- pending_orders CRUD ----

def _db_save_pending_order(
    user_id: int,
    product: Dict[str, Any],
    payment_method: str,
    expected_amount: Optional[str] = None,
    expected_asset: Optional[str] = None,
    external_invoice_id: Optional[str] = None,
) -> bool:
    try:
        with _get_db() as conn:
            cursor = conn.execute(
                """INSERT OR IGNORE INTO pending_orders
                   (created_at, user_id, product_id, product_title, file_id,
                    payment_method, expected_amount, expected_asset, external_invoice_id)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                (
                    datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                    str(user_id),
                    product["product_id"],
                    product.get("title", ""),
                    product.get("file_id", ""),
                    payment_method,
                    expected_amount,
                    expected_asset,
                    external_invoice_id,
                )
            )
            conn.commit()
            return cursor.rowcount > 0
    except Exception as e:
        logger.exception("pending_orders insert error: %s", e)
        return False


def _db_get_pending_order(payment_method: str, external_invoice_id: str, user_id: int) -> Optional[Dict]:
    try:
        with _get_db() as conn:
            conn.row_factory = sqlite3.Row
            row = conn.execute(
                """SELECT * FROM pending_orders
                   WHERE payment_method=? AND external_invoice_id=? AND user_id=?""",
                (payment_method, str(external_invoice_id), str(user_id))
            ).fetchone()
        return dict(row) if row else None
    except Exception as e:
        logger.exception("pending_orders get error: %s", e)
        return None


def _db_delete_pending_order(payment_method: str, external_invoice_id: str, user_id: int) -> None:
    try:
        with _get_db() as conn:
            conn.execute(
                """DELETE FROM pending_orders
                   WHERE payment_method=? AND external_invoice_id=? AND user_id=?""",
                (payment_method, str(external_invoice_id), str(user_id))
            )
            conn.commit()
    except Exception as e:
        logger.exception("pending_orders delete error: %s", e)


def _db_cleanup_pending_orders() -> None:
    try:
        with _get_db() as conn:
            cursor = conn.execute(
                "DELETE FROM pending_orders WHERE created_at < datetime('now', '-7 days')"
            )
            conn.commit()
            if cursor.rowcount:
                logger.info("Cleaned %d expired pending orders", cursor.rowcount)
    except Exception as e:
        logger.exception("pending_orders cleanup error: %s", e)


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
# ТОВАРЫ (CSV → SQLite)
# =========================

_products_cache: Tuple[float, List[Dict[str, Any]]] = (0.0, [])
_csv_imported: bool = False


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
                "active": _to_bool(row.get("active", "true")),
            })
        except Exception:
            logger.exception("Ошибка разбора строки CSV")
    return products


async def load_products() -> List[Dict[str, Any]]:
    global _products_cache, _csv_imported
    ts, cached = _products_cache
    if cached and (time.time() - ts) < PRODUCTS_CACHE_TTL:
        return cached

    loop = asyncio.get_running_loop()

    if not _csv_imported:
        try:
            csv_text = await loop.run_in_executor(None, _sync_fetch_csv)
            if csv_text:
                csv_products = _parse_csv_products(csv_text)
                await loop.run_in_executor(None, _db_import_from_csv_if_empty, csv_products)
        except Exception as e:
            logger.warning("CSV миграция не удалась (не критично): %s", e)
        _csv_imported = True

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


def is_free_product(p: Dict[str, Any]) -> bool:
    price_xtr = int(p.get("price_xtr", 0) or 0)
    crypto_amount = parse_crypto_amount(p)
    return price_xtr == 0 and crypto_amount is None


_CRYPTO_AMOUNT_RE = re.compile(r"^\d+([.,]\d+)?$")



def _clean_crypto_input(raw: str) -> str:
    """Нормализует ввод суммы: убирает пробелы, заменяет запятую на точку."""
    return raw.strip().replace(" ", "").replace(",", ".")


def parse_crypto_amount(product: Dict[str, Any]) -> Optional[Decimal]:
    raw = _to_str(product.get("price_crypto", ""))
    if not raw:
        return None
    cleaned = _clean_crypto_input(raw)
    if not _CRYPTO_AMOUNT_RE.match(cleaned):
        logger.warning(
            "Невалидный формат price_crypto для товара %s: %r",
            product.get("product_id"), raw
        )
        return None
    try:
        amount = Decimal(cleaned)
        if amount <= 0:
            return None
        return amount
    except InvalidOperation:
        return None


def can_buy_with_crypto(product: Dict[str, Any]) -> bool:
    if is_free_product(product):
        return False
    asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()
    amount = parse_crypto_amount(product)
    return bool(CRYPTO_PAY_TOKEN and asset and amount is not None)


def get_crypto_amount_and_asset(product: Dict[str, Any]) -> Tuple[str, str]:
    amount = parse_crypto_amount(product)
    asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()
    if amount is None:
        raise RuntimeError(
            f"Для товара {product.get('product_id')} недопустимая price_crypto"
        )
    if not asset:
        asset = CRYPTO_PAY_DEFAULT_ASSET
    return str(amount), asset


# =========================
# SAFE callback_data для категорий
# =========================

_cat_key_to_name: Dict[str, str] = {}


def _cat_key(name: str) -> str:
    return hashlib.sha1(name.encode("utf-8")).hexdigest()[:10]


def _register_categories(categories: List[str]) -> None:
    for c in categories:
        c_clean = _to_str(c)
        _cat_key_to_name[_cat_key(c_clean)] = c_clean


def categories_keyboard(categories: List[str]) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    for c in categories:
        c_clean = _to_str(c)
        key = _cat_key(c_clean)
        _cat_key_to_name[key] = c_clean
        kb.add(InlineKeyboardButton(text=c_clean, callback_data=f"catk:{key}"))
    kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))
    return kb


def _product_btn_label(p: Dict[str, Any]) -> str:
    """Текст кнопки товара в списке — только название."""
    return p["title"]


def products_keyboard(products: List[Dict[str, Any]], category_key: str) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    for p in products:
        kb.add(
            InlineKeyboardButton(
                text=_product_btn_label(p),
                callback_data=f"item:{p['product_id']}:{category_key}"
            )
        )
    kb.add(InlineKeyboardButton("← К категориям", callback_data="open:catalog"))
    kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))
    return kb


# =========================
# SQLite CRUD: ПОКУПКИ
# =========================

def _db_user_has_purchase(user_id: int, product_id: str) -> bool:
    with _get_db() as conn:
        row = conn.execute(
            "SELECT 1 FROM purchases WHERE user_id=? AND product_id=?",
            (str(user_id), str(product_id))
        ).fetchone()
    return row is not None


def _db_get_user_purchases(user_id: int) -> List[Dict[str, str]]:
    with _get_db() as conn:
        conn.row_factory = sqlite3.Row
        rows = conn.execute(
            "SELECT * FROM purchases WHERE user_id=? ORDER BY date DESC",
            (str(user_id),)
        ).fetchall()
    return [dict(r) for r in rows]


def _db_get_purchase(user_id: int, product_id: str) -> Optional[Dict[str, str]]:
    with _get_db() as conn:
        conn.row_factory = sqlite3.Row
        row = conn.execute(
            "SELECT * FROM purchases WHERE user_id=? AND product_id=?",
            (str(user_id), str(product_id))
        ).fetchone()
    return dict(row) if row else None


def _db_insert_purchase(user: "types.User", product: Dict[str, Any], price_label: str) -> str:
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    username = f"@{user.username}" if user.username else ""
    try:
        with _get_db() as conn:
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
            return "inserted" if cursor.rowcount > 0 else "exists"
    except Exception as e:
        logger.exception("SQLite insert error: %s", e)
        return "error"


async def user_has_purchase(user_id: int, product_id: str) -> bool:
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _db_user_has_purchase, user_id, product_id)


async def get_user_purchase_row(user_id: int, product_id: str) -> Optional[Dict[str, str]]:
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _db_get_purchase, user_id, product_id)


async def append_purchase_row(user: types.User, product: Dict[str, Any], price_label: str) -> bool:
    loop = asyncio.get_running_loop()
    status = await loop.run_in_executor(None, _db_insert_purchase, user, product, price_label)

    if status == "error":
        logger.error(
            "DB insert failed for user=%s product=%s — файл НЕ выдаём",
            user.id, product.get("product_id")
        )
        return False

    if status == "inserted":
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
        asyncio.create_task(_safe_mirror_to_sheets(mirror_row))

    return True


async def _safe_mirror_to_sheets(row: list) -> None:
    """Обёртка с обработкой исключений для фоновой задачи."""
    try:
        await _mirror_to_sheets(row)
    except Exception as e:
        logger.warning("_safe_mirror_to_sheets error: %s", e)


# =========================
# CRYPTO PAY API
# =========================

def crypto_headers() -> Dict[str, str]:
    if not CRYPTO_PAY_TOKEN:
        raise RuntimeError("Не задан CRYPTO_PAY_TOKEN")
    return {"Crypto-Pay-API-Token": CRYPTO_PAY_TOKEN}


def _sync_crypto_create_invoice(data: dict) -> Dict[str, Any]:
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
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _sync_crypto_get_invoice, invoice_id)


# =========================
# ОБЩАЯ ВЫДАЧА ТОВАРА
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
        if await user_has_purchase(user.id, pid):
            await bot.send_document(chat_id, product["file_id"])
            return True

        saved = await append_purchase_row(user=user, product=product, price_label=price_label)
        if not saved:
            return False

        await bot.send_document(chat_id, product["file_id"])
        asyncio.create_task(_safe_suggest_more(chat_id, user.id, product))
        loop2 = asyncio.get_running_loop()
        await loop2.run_in_executor(None, _db_schedule_review_request, user.id, product["product_id"])
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
# =========================

START_TEXT = (
    "👋 <b>Привет!</b>\n\n"
    "Здесь собраны развивающие PDF-материалы для детей.\n\n"
    "🎨 Разукрашки и творческие задания\n"
    "📖 Обучающие и научные сказки\n"
    "🧠 Развивающие игры и вопросы\n"
    "🎁 Бесплатные материалы\n\n"
    "Выберите раздел:"
)


def start_inline_kb() -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(
        InlineKeyboardButton("📚 Каталог", callback_data="open:catalog"),
        InlineKeyboardButton("📂 Мои покупки", callback_data="open:purchases"),
    )
    kb.add(
        InlineKeyboardButton("❤️ Избранное", callback_data="open:favourites"),
        InlineKeyboardButton("🎯 Подобрать материал", callback_data="quiz:start"),
    )
    kb.add(
        InlineKeyboardButton("✉️ Написать в поддержку", url=f"https://t.me/{AUTHOR_USERNAME}")
    )
    return kb


@dp.message_handler(commands=["start"])
async def cmd_start(message: types.Message):
    args = message.get_args()
    if args and args.startswith("buy_stars_"):
        pid = args.replace("buy_stars_", "", 1).strip()
        _all_products = await load_products()
        product = next((p for p in _all_products if p["product_id"] == pid), None)
        if product:
            await message.answer(START_TEXT, reply_markup=start_inline_kb(), parse_mode="HTML")
            text = await _format_product_card_full(product)
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


# =========================
# МОИ ПОКУПКИ
# =========================

async def send_my_purchases(chat_id: int, user: types.User):
    """
    FIX: Покупки показываются редактированием существующего сообщения,
    а не отправкой новых. Список товаров — в одном сообщении.
    """
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

    # Строим ONE сообщение со всем списком + inline кнопками
    lines = ["<b>Ваши покупки</b>\n"]
    kb = InlineKeyboardMarkup(row_width=1)

    for r in unique_rows:
        pid = _to_str(r.get("product_id"))
        title = _to_str(r.get("product_title")) or prod_map.get(pid, {}).get("title", "PDF")
        price_from_row = _to_str(r.get("price_label") or r.get("price_xtr"))
        is_free_row = (price_from_row == "" or price_from_row == "0")
        price_hint = "бесплатно" if is_free_row else price_from_row
        lines.append(f"• {title}  <i>({price_hint})</i>")
        kb.add(InlineKeyboardButton(f"📥 {title[:32]}", callback_data=f"dl:{pid}"))

    kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))

    await bot.send_message(
        chat_id,
        "\n".join(lines),
        reply_markup=kb,
        parse_mode="HTML"
    )


# =========================
# ИЗБРАННОЕ — без засорения чата
# =========================

async def send_favourites(chat_id: int, user: types.User, edit_message: Optional[types.Message] = None):
    """
    FIX: Избранное показывается как одно сообщение со списком,
    вместо кучи отдельных сообщений.
    """
    loop = asyncio.get_running_loop()
    fav_ids = await loop.run_in_executor(None, _db_get_favourites, user.id)

    if not fav_ids:
        kb = InlineKeyboardMarkup(row_width=1)
        kb.add(InlineKeyboardButton("📚 Каталог", callback_data="open:catalog"))
        kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))
        text = "🤍 <b>Избранное пусто</b>\n\nДобавляй товары кнопкой ❤️ на карточке"
        if edit_message:
            try:
                await edit_message.edit_text(text, reply_markup=kb, parse_mode="HTML")
                return
            except Exception:
                pass
        await bot.send_message(chat_id, text, reply_markup=kb, parse_mode="HTML")
        return

    all_products = await load_products()
    prod_map = {p["product_id"]: p for p in all_products}

    lines = ["<b>Избранное</b>\n"]
    kb = InlineKeyboardMarkup(row_width=1)

    for pid in fav_ids:
        product = prod_map.get(pid)
        if not product:
            continue
        is_bought = await user_has_purchase(user.id, pid)
        price_xtr_fav = int(product.get("price_xtr", 0) or 0)
        price_hint_fav = "бесплатно" if is_free_product(product) else f"{price_xtr_fav} ⭐"
        bought_hint = " — куплено ✓" if is_bought else ""
        lines.append(f"• {product['title']}  <i>({price_hint_fav}{bought_hint})</i>")
        cat_key = _cat_key(_to_str(product.get("category", "")))
        _cat_key_to_name[cat_key] = _to_str(product.get("category", ""))

        if is_bought:
            kb.add(InlineKeyboardButton(
                f"📥 {product['title'][:35]}",
                callback_data=f"dl:{pid}"
            ))
        else:
            kb.add(InlineKeyboardButton(
                product['title'],
                callback_data=f"item:{pid}:{cat_key}"
            ))

    kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))

    text = "\n".join(lines)
    if edit_message:
        try:
            await edit_message.edit_text(text, reply_markup=kb, parse_mode="HTML")
            return
        except Exception:
            pass
    await bot.send_message(chat_id, text, reply_markup=kb, parse_mode="HTML")


# =========================
# CALLBACKS: open:catalog / open:purchases / open:start / open:favourites
# =========================

@dp.callback_query_handler(lambda c: c.data == "open:catalog")
async def cb_open_catalog(call: types.CallbackQuery):
    await call.answer()
    _cleanup_product_card(call.message.chat.id)
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
    chat_id = call.message.chat.id
    _cleanup_product_card(chat_id)
    try:
        await call.message.edit_text(START_TEXT, reply_markup=start_inline_kb(), parse_mode="HTML")
    except Exception:
        await call.message.answer(START_TEXT, reply_markup=start_inline_kb(), parse_mode="HTML")


@dp.callback_query_handler(lambda c: c.data == "open:favourites")
async def cb_open_favourites(call: types.CallbackQuery):
    await call.answer()
    await send_favourites(call.message.chat.id, call.from_user, edit_message=call.message)


def _cleanup_product_card(chat_id: int) -> None:
    """Удаляет закреплённую фото-карточку товара если есть."""
    prev = _product_card_msg.pop(chat_id, None)
    if prev:
        asyncio.create_task(_safe_delete_message(chat_id, prev[1]))


async def _safe_delete_message(chat_id: int, message_id: int) -> None:
    try:
        await bot.delete_message(chat_id, message_id)
    except Exception:
        pass


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
        _register_categories(cats)
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
# ПРЕДПРОСМОТР ТОВАРА
# =========================

def _has_card_payment(product: Dict[str, Any]) -> bool:
    """Карта доступна если CARD_NUMBER задан и у товара есть цена в рублях."""
    if not CARD_NUMBER:
        return False
    price_rub = int(product.get("price_rub", 0) or 0)
    # Если цена в рублях задана у товара — используем её
    # Если задана глобальная CARD_PRICE_RUB — тоже показываем карту
    return price_rub > 0 or bool(CARD_PRICE_RUB)


def _count_pay_methods(product: Dict[str, Any]) -> int:
    """Считает количество доступных способов оплаты."""
    count = 0
    if int(product.get("price_xtr", 0) or 0) > 0:
        count += 1
    if can_buy_with_crypto(product):
        count += 1
    if _has_card_payment(product):
        count += 1
    return count


def _has_multiple_pay_methods(product: Dict[str, Any]) -> bool:
    """Проверяет, доступно ли несколько способов оплаты."""
    return _count_pay_methods(product) > 1


def product_action_kb(product: Dict[str, Any], category_key: str) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    pid = product["product_id"]

    if is_free_product(product):
        kb.add(InlineKeyboardButton("Скачать бесплатно 🎁", callback_data=f"get:{pid}"))
    elif _has_multiple_pay_methods(product):
        # Несколько способов — одна кнопка "Купить", откроет меню выбора
        kb.add(InlineKeyboardButton("Купить", callback_data=f"buy:{pid}:{category_key}"))
    else:
        # Только один способ — показываем его напрямую
        price_xtr = int(product.get("price_xtr", 0) or 0)
        price_crypto_raw = _to_str(product.get("price_crypto", ""))
        crypto_asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()
        price_rub_single = int(product.get("price_rub", 0) or 0)
        if price_xtr > 0:
            kb.add(InlineKeyboardButton(
                f"Купить за {price_xtr} Stars ⭐",
                callback_data=f"paystars:{pid}"
            ))
        elif can_buy_with_crypto(product):
            kb.add(InlineKeyboardButton(
                f"Купить за {price_crypto_raw} {crypto_asset}",
                callback_data=f"paycrypto:{pid}"
            ))
        elif _has_card_payment(product):
            rub_label = str(price_rub_single) if price_rub_single > 0 else CARD_PRICE_RUB
            kb.add(InlineKeyboardButton(
                f"Купить за {rub_label} ₽ 💳",
                callback_data=f"paycard:{pid}:{category_key}"
            ))

    kb.add(InlineKeyboardButton("Добавить в избранное ❤️", callback_data=f"fav:toggle:{pid}:{category_key}"))
    kb.add(InlineKeyboardButton("← Назад к списку", callback_data=f"back_items:{category_key}"))
    kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))
    return kb


def _format_product_card(product: Dict[str, Any]) -> str:
    title = product.get("title", "PDF")
    desc = _to_str(product.get("description"), "PDF файл")
    price_xtr = int(product.get("price_xtr", 0) or 0)
    crypto_amount = parse_crypto_amount(product)
    crypto_asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()
    category = _to_str(product.get("category", ""))
    age_min = int(product.get("age_min", 0) or 0)
    age_max = int(product.get("age_max", 99) or 99)
    tags = _to_str(product.get("tags", ""))

    price_rub = int(product.get("price_rub", 0) or 0)
    if is_free_product(product):
        price_line = "<b>Бесплатно</b> 🎁"
    else:
        parts = []
        if price_xtr > 0:
            parts.append(f"<b>{price_xtr} Stars</b> ⭐")
        if can_buy_with_crypto(product) and crypto_amount is not None:
            parts.append(f"<b>{crypto_amount} {crypto_asset}</b>")
        if price_rub > 0:
            parts.append(f"<b>{price_rub} ₽</b> 💳")
        price_line = "  |  ".join(parts) if parts else "💳 Уточните цену"

    cat_line = f"\n<i>📂 {category}</i>" if category else ""

    # Возраст — показываем только если задан
    if age_min > 0 or age_max < 99:
        if age_min == age_max:
            age_line = f"\n👶 <i>Возраст: {age_min} лет</i>"
        else:
            age_line = f"\n👶 <i>Возраст: {age_min}–{age_max} лет</i>"
    else:
        age_line = ""

    # Теги — показываем только если заданы
    if tags:
        tag_list = [f"#{t.strip()}" for t in tags.split(",") if t.strip()]
        tags_line = "\n" + " ".join(tag_list) if tag_list else ""
    else:
        tags_line = ""

    return (
        f"<b>{title}</b>{cat_line}{age_line}\n"
        f"\n"
        f"{desc}\n"
        f"\n"
        f"{price_line}{tags_line}"
    )


async def _format_product_card_full(product: Dict[str, Any]) -> str:
    """FIX: Единственное определение — дублирование устранено."""
    base = _format_product_card(product)
    reviews_text = await _get_reviews_text(product["product_id"])
    return base + reviews_text if reviews_text else base


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

    text = await _format_product_card_full(product)
    kb = product_action_kb(product, category_key=category_key)
    preview_id = _to_str(product.get("preview_file_id"))
    chat_id = call.message.chat.id
    pid_str = product["product_id"]
    prev = _product_card_msg.get(chat_id)

    # Запоминаем текущий список для последующего удаления
    if chat_id not in _product_list_msgs:
        _product_list_msgs[chat_id] = []
    msg_id = call.message.message_id
    if msg_id not in _product_list_msgs[chat_id]:
        _product_list_msgs[chat_id].append(msg_id)

    if preview_id:
        if prev and prev[0] == pid_str:
            # Тот же товар — обновляем только кнопки
            try:
                await bot.edit_message_reply_markup(
                    chat_id=chat_id, message_id=prev[1], reply_markup=kb
                )
                try:
                    await call.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup())
                except Exception:
                    pass
            except Exception:
                pass
        elif prev and prev[0] != pid_str:
            # Другой товар — меняем фото
            try:
                from aiogram.types import InputMediaPhoto
                await bot.edit_message_media(
                    chat_id=chat_id,
                    message_id=prev[1],
                    media=InputMediaPhoto(media=preview_id, caption=text, parse_mode="HTML"),
                    reply_markup=kb
                )
                _product_card_msg[chat_id] = (pid_str, prev[1])
                try:
                    await call.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup())
                except Exception:
                    pass
            except Exception:
                try:
                    await bot.delete_message(chat_id, prev[1])
                except Exception:
                    pass
                _product_card_msg.pop(chat_id, None)
                sent = await bot.send_photo(
                    chat_id=chat_id, photo=preview_id,
                    caption=text, reply_markup=kb, parse_mode="HTML"
                )
                _product_card_msg[chat_id] = (pid_str, sent.message_id)
        else:
            # Первый раз
            sent = await bot.send_photo(
                chat_id=chat_id, photo=preview_id,
                caption=text, reply_markup=kb, parse_mode="HTML"
            )
            _product_card_msg[chat_id] = (pid_str, sent.message_id)
            try:
                await call.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup())
            except Exception:
                pass
    else:
        try:
            await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")
        except Exception:
            await bot.send_message(chat_id, text, reply_markup=kb, parse_mode="HTML")


@dp.callback_query_handler(lambda c: c.data.startswith("back_items:"))
async def cb_back_items(call: types.CallbackQuery):
    category_key = call.data.split("back_items:", 1)[1].strip()
    category = _cat_key_to_name.get(category_key)

    if not category:
        products_all = await load_products()
        cats = sorted(set(_to_str(p.get("category", "")) for p in products_all if p.get("category")))
        _register_categories(cats)
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
    chat_id = call.message.chat.id

    # Удаляем фото-карточку
    prev = _product_card_msg.pop(chat_id, None)
    if prev:
        asyncio.create_task(_safe_delete_message(chat_id, prev[1]))

    # Удаляем накопившиеся списки товаров
    current_msg_id = call.message.message_id
    list_msg_ids = _product_list_msgs.pop(chat_id, [])
    for mid in list_msg_ids:
        if mid != current_msg_id:
            asyncio.create_task(_safe_delete_message(chat_id, mid))

    try:
        await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")
    except Exception:
        await bot.send_message(chat_id, text, reply_markup=kb, parse_mode="HTML")

    await call.answer()


# =========================
# ДЕЙСТВИЯ: бесплатно / STARS / CRYPTO
# =========================
# МЕНЮ ВЫБОРА СПОСОБА ОПЛАТЫ
# =========================

def payment_methods_kb(product: Dict[str, Any], category_key: str) -> InlineKeyboardMarkup:
    """
    Клавиатура выбора способа оплаты.
    Чтобы добавить новый метод (например, карта РФ) — просто добавьте кнопку здесь.
    """
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
    if can_buy_with_crypto(product):
        kb.add(InlineKeyboardButton(
            f"Криптовалюта — {price_crypto_raw} {crypto_asset}",
            callback_data=f"paycrypto:{pid}"
        ))

    if CARD_NUMBER:
        # Цена: берём из товара, потом из глобальной переменной, потом просто метку
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


@dp.callback_query_handler(lambda c: c.data.startswith("buy:"))
async def cb_buy_menu(call: types.CallbackQuery):
    """Показывает меню выбора способа оплаты."""
    parts = call.data.split(":", 2)
    if len(parts) < 3:
        await call.answer("Некорректная кнопка.", show_alert=True)
        return

    pid = parts[1]
    category_key = parts[2]

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

    await call.answer()

    price_xtr = int(product.get("price_xtr", 0) or 0)
    crypto_amount = parse_crypto_amount(product)
    crypto_asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()

    parts_price = []
    if price_xtr > 0:
        parts_price.append(f"{price_xtr} Stars ⭐")
    if crypto_amount is not None:
        parts_price.append(f"{crypto_amount} {crypto_asset}")
    price_summary = "  /  ".join(parts_price)

    try:
        await call.message.edit_reply_markup(
            reply_markup=payment_methods_kb(product, category_key)
        )
    except Exception:
        await bot.send_message(
            call.message.chat.id,
            "Выберите способ оплаты:\n\n" + product["title"] + "\n\n" + price_summary,
            reply_markup=payment_methods_kb(product, category_key),
            parse_mode="HTML"
        )


@dp.callback_query_handler(lambda c: c.data.startswith("back_to_item:"))
async def cb_back_to_item(call: types.CallbackQuery):
    """Возврат к карточке товара из меню оплаты."""
    parts = call.data.split(":", 2)
    if len(parts) < 3:
        await call.answer()
        return

    pid = parts[1]
    category_key = parts[2]

    _all_products = await load_products()
    product = next((p for p in _all_products if p["product_id"] == pid), None)
    if not product:
        await call.answer("Материал не найден.", show_alert=True)
        return

    await call.answer()
    kb = product_action_kb(product, category_key=category_key)
    try:
        await call.message.edit_reply_markup(reply_markup=kb)
    except Exception:
        pass


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

    stars_order_key = None
    try:
        # FIX: используем только user_id + timestamp, без pid — избегаем проблем с ":" в product_id
        stars_order_key = f"{user.id}:{int(time.time() * 1000)}"
        payload = f"buystars:{stars_order_key}:{pid}"

        if not product.get("file_id"):
            await call.answer("Файл товара недоступен. Напишите в поддержку.", show_alert=True)
            return

        loop = asyncio.get_running_loop()
        saved = await loop.run_in_executor(
            None, _db_save_pending_order,
            user.id, product, "stars", str(product["price_xtr"]), "XTR", stars_order_key
        )
        if not saved:
            await call.answer("Не удалось подготовить оплату. Попробуйте ещё раз.", show_alert=True)
            return

        await bot.send_invoice(
            chat_id=call.message.chat.id,
            title=product["title"],
            description=product["description"],
            payload=payload,
            provider_token=PROVIDER_TOKEN,
            currency=CURRENCY,
            prices=[LabeledPrice(label=product["title"], amount=int(product["price_xtr"]))],
            start_parameter=f"buy_stars_{pid}"
        )
        await call.answer()
    except Exception as e:
        logger.exception("Ошибка send_invoice (Stars): %s", e)
        if stars_order_key:
            try:
                loop_exc = asyncio.get_running_loop()
                await loop_exc.run_in_executor(
                    None, _db_delete_pending_order, "stars", stars_order_key, user.id
                )
            except Exception:
                pass
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

    if not product.get("file_id"):
        await call.answer("Файл товара недоступен. Напишите в поддержку.", show_alert=True)
        return

    # FIX: атомарная проверка cooldown через asyncio.Lock
    dedup_key = f"{user.id}:{pid}"
    async with _crypto_cooldown_lock:
        last_created = _crypto_invoice_created_at.get(dedup_key, 0)
        if time.time() - last_created < _CRYPTO_INVOICE_COOLDOWN:
            await call.answer(
                "Счёт уже был создан недавно. Подождите минуту или нажмите «Я оплатил, проверить» выше.",
                show_alert=True
            )
            return
        # Помечаем сразу — внутри лока
        _crypto_invoice_created_at[dedup_key] = time.time()

    try:
        amount, asset = get_crypto_amount_and_asset(product)
        invoice = await crypto_create_invoice(product, user)
        _cleanup_invoice_cooldown()
        invoice_id = invoice["invoice_id"]

        loop = asyncio.get_running_loop()
        saved = await loop.run_in_executor(
            None, _db_save_pending_order,
            user.id, product, "crypto", amount, asset, str(invoice_id)
        )
        if not saved:
            logger.error("Не удалось сохранить pending для crypto invoice %s", invoice_id)
            # Сбрасываем cooldown — invoice не будет доступен пользователю
            async with _crypto_cooldown_lock:
                _crypto_invoice_created_at.pop(dedup_key, None)
            await call.answer("Не удалось подготовить заказ. Попробуйте ещё раз.", show_alert=True)
            return

        pay_url = invoice.get("bot_invoice_url") or invoice.get("pay_url")
        if not pay_url:
            logger.error("Crypto Pay не вернул pay_url для invoice: %s", invoice)
            loop_pu = asyncio.get_running_loop()
            await loop_pu.run_in_executor(
                None, _db_delete_pending_order, "crypto", str(invoice_id), user.id
            )
            async with _crypto_cooldown_lock:
                _crypto_invoice_created_at.pop(dedup_key, None)
            await call.answer("Не удалось получить ссылку на оплату. Попробуйте позже.", show_alert=True)
            return

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
        # Сбрасываем cooldown при ошибке
        async with _crypto_cooldown_lock:
            _crypto_invoice_created_at.pop(dedup_key, None)
        await call.answer("Не удалось создать crypto-счёт.", show_alert=True)


@dp.callback_query_handler(lambda c: c.data.startswith("checkcrypto:"))
async def cb_check_crypto(call: types.CallbackQuery):
    try:
        parts = call.data.split(":", 2)
        pid = parts[1]
        invoice_id = int(parts[2])
    except Exception:
        await call.answer("Некорректная кнопка.", show_alert=True)
        return

    user = call.from_user

    if await user_has_purchase(user.id, pid):
        purchase_row = await get_user_purchase_row(user.id, pid)
        file_id = _to_str(purchase_row.get("file_id")) if purchase_row else ""
        if not file_id:
            _all_products = await load_products()
            prod = next((p for p in _all_products if p["product_id"] == pid), None)
            file_id = prod["file_id"] if prod else ""
        if file_id:
            await call.answer()
            await bot.send_document(call.message.chat.id, file_id)
        else:
            await call.answer("Не удалось найти файл. Напишите в поддержку.", show_alert=True)
        return

    loop = asyncio.get_running_loop()
    pending = await loop.run_in_executor(None, _db_get_pending_order, "crypto", str(invoice_id), user.id)
    if pending:
        product = {
            "product_id": pending["product_id"],
            "title": pending.get("product_title", ""),
            "file_id": pending["file_id"],
            "price_crypto": pending.get("expected_amount", ""),
            "crypto_asset": pending.get("expected_asset", ""),
        }
    else:
        logger.warning(
            "Crypto cb_check_crypto без pending: user=%s pid=%s invoice_id=%s",
            user.id, pid, invoice_id
        )
        _all_products = await load_products()
        product = next((p for p in _all_products if p["product_id"] == pid), None)
        if not product:
            await call.answer("Материал не найден. Напишите в поддержку.", show_alert=True)
            return

    try:
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

        invoice_amount = _to_str(invoice.get("amount", ""))
        invoice_asset = _to_str(invoice.get("asset", "")).upper()
        if invoice_amount:
            try:
                if Decimal(invoice_amount) != Decimal(amount):
                    logger.warning(
                        "Invoice amount mismatch: expected=%s got=%s user=%s product=%s",
                        amount, invoice_amount, user.id, pid
                    )
                    await call.answer("Сумма оплаты не совпадает с ценой товара. Напишите в поддержку.", show_alert=True)
                    return
            except InvalidOperation:
                await call.answer("Не удалось проверить сумму оплаты. Напишите в поддержку через /help.", show_alert=True)
                return
        if invoice_asset and invoice_asset != asset:
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

        loop2 = asyncio.get_running_loop()
        await loop2.run_in_executor(
            None, _db_delete_pending_order, "crypto", str(invoice_id), user.id
        )

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
# СКАЧАТЬ ИЗ МОИ ПОКУПОК
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
# FIX: исправлен парсинг payload — pid теперь в конце, не в середине
# =========================

@dp.pre_checkout_query_handler(lambda q: True)
async def pre_checkout(pre_checkout_q: types.PreCheckoutQuery):
    await bot.answer_pre_checkout_query(pre_checkout_q.id, ok=True)


@dp.message_handler(content_types=types.ContentType.SUCCESSFUL_PAYMENT)
async def successful_payment(message: types.Message):
    payload = message.successful_payment.invoice_payload

    # FIX: новый формат payload: "buystars:{user_id}:{timestamp_ms}:{pid}"
    # pid — последним, чтобы он мог содержать любые символы кроме первых двух ":"
    if not payload.startswith("buystars:"):
        await message.answer("Оплата получена, но товар не распознан.")
        return

    rest = payload[len("buystars:"):]
    # Разбиваем только первые два ":" — остаток идёт в pid
    parts = rest.split(":", 2)
    if len(parts) != 3:
        logger.error("Stars payload неожиданного формата: %r", payload)
        await message.answer("Ошибка данных оплаты. Напишите в поддержку через /help.")
        return

    payload_user_id, timestamp_ms, pid = parts
    stars_order_key = f"{payload_user_id}:{timestamp_ms}"

    if payload_user_id != str(message.from_user.id):
        logger.warning(
            "Stars payload user mismatch: payload_user=%s actual_user=%s",
            payload_user_id, message.from_user.id
        )
        await message.answer("Ошибка авторизации. Напишите в поддержку через /help.")
        return

    loop = asyncio.get_running_loop()
    pending = await loop.run_in_executor(
        None, _db_get_pending_order, "stars", stars_order_key, message.from_user.id
    )
    if pending:
        if pending.get("product_id") != pid:
            logger.error("Stars pending order mismatch: key=%s pending.product_id=%s pid=%s",
                         stars_order_key, pending.get("product_id"), pid)
            await message.answer("Ошибка данных заказа. Напишите в поддержку через /help.")
            return
        product = {
            "product_id": pending["product_id"],
            "title": pending.get("product_title", ""),
            "file_id": pending["file_id"],
            "price_xtr": pending.get("expected_amount", "0"),
        }
    else:
        logger.warning(
            "Stars successful_payment без pending: user=%s pid=%s key=%s",
            message.from_user.id, pid, stars_order_key
        )
        _all_products = await load_products()
        product = next((p for p in _all_products if p["product_id"] == pid), None)
        if not product:
            await message.answer("Оплата получена, но материал сейчас недоступен. Напишите в поддержку через /help.")
            return

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

    loop2 = asyncio.get_running_loop()
    await loop2.run_in_executor(
        None, _db_delete_pending_order, "stars", stars_order_key, message.from_user.id
    )

    await notify_admin_purchase(
        user=user,
        product=product,
        payment_text=f"{expected} Stars"
    )


# =========================
# ADMIN: refresh + debug
# =========================

@dp.message_handler(commands=["cardtest"], user_id=ADMIN_IDS)
async def cmd_cardtest(message: types.Message):
    """Диагностика: проверяет загружены ли переменные карты."""
    card_num_masked = (
        CARD_NUMBER[:4] + " **** **** " + CARD_NUMBER[-4:]
        if len(CARD_NUMBER) >= 8 else ("задан" if CARD_NUMBER else "НЕ ЗАДАН")
    )
    # Показываем все env-переменные содержащие CARD для диагностики
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
    # Проверяем тестовый товар
    all_products = await load_products()
    paid = [p for p in all_products if not is_free_product(p)]
    if paid:
        test_p = paid[0]
        has_card = _has_card_payment(test_p)
        has_multi = _has_multiple_pay_methods(test_p)
        count = _count_pay_methods(test_p)
        lines.append("\nТест на товаре «" + test_p["title"] + "»:")
        lines.append(f"  price_rub = {test_p.get('price_rub', 0)}")
        lines.append(f"  _has_card_payment = {has_card}")
        lines.append(f"  _count_pay_methods = {count}")
        lines.append(f"  _has_multiple = {has_multi}")
        lines.append(f"  → {'кнопка Купить' if has_multi else 'прямая кнопка'}")
    await message.answer("\n".join(lines), parse_mode="HTML")


@dp.message_handler(commands=["testreview"], user_id=ADMIN_IDS)
async def cmd_testreview(message: types.Message):
    """
    Тестирование запроса отзыва.
    Использование:
      /testreview          — отправить себе запрос по последней покупке
      /testreview p001     — отправить запрос по конкретному product_id
    """
    args = message.get_args().strip()
    user_id = message.from_user.id

    loop = asyncio.get_running_loop()

    if args:
        product_id = args
        prod = await loop.run_in_executor(None, _db_get_product, product_id)
        if not prod:
            await message.answer(f"Товар <code>{product_id}</code> не найден.", parse_mode="HTML")
            return
        title = prod["title"]
    else:
        # Берём последнюю покупку
        purchases = await loop.run_in_executor(None, _db_get_user_purchases, user_id)
        if not purchases:
            await message.answer("У вас нет покупок для теста. Укажите product_id: /testreview p001")
            return
        product_id = purchases[0]["product_id"]
        title = purchases[0].get("product_title") or product_id

    # Отправляем запрос отзыва напрямую (без ожидания 24ч)
    kb = InlineKeyboardMarkup(row_width=1)
    labels = ["⭐ 1 — плохо", "⭐⭐ 2 — так себе", "⭐⭐⭐ 3 — нормально",
              "⭐⭐⭐⭐ 4 — хорошо", "⭐⭐⭐⭐⭐ 5 — отлично"]
    # Используем фиктивный req_id=0 для теста
    for i in range(1, 6):
        kb.add(InlineKeyboardButton(
            labels[i - 1],
            callback_data=f"rev:rate:{product_id}:0:{i}"
        ))
    kb.add(InlineKeyboardButton("Пропустить", callback_data="rev:skip:0"))


    await message.answer(
        "<b>Тест запроса отзыва</b>\n\n"
        f"Товар: <b>{title}</b>\n\n"
        f"Как вам материал <b>{title}</b>?\n\nПоставьте оценку от 1 до 5:",
        reply_markup=kb,
        parse_mode="HTML"
    )



@dp.message_handler(commands=["reviews"], user_id=ADMIN_IDS)
async def cmd_reviews(message: types.Message):
    """
    Просмотр всех отзывов с кнопками удаления.
    /reviews          — все отзывы (последние 20)
    /reviews p001     — отзывы по конкретному товару
    /reviews @username — отзывы конкретного пользователя
    """
    args = message.get_args().strip()
    loop = asyncio.get_running_loop()

    if args.startswith("p"):
        # Фильтр по product_id
        reviews = await loop.run_in_executor(None, _db_get_reviews, args)
        header = f"Отзывы по товару <code>{args}</code>"
    else:
        # Все последние отзывы
        def _get_all_reviews():
            with _get_db() as conn:
                conn.row_factory = sqlite3.Row
                rows = conn.execute(
                    "SELECT * FROM reviews ORDER BY created_at DESC LIMIT 20"
                ).fetchall()
            return [dict(r) for r in rows]
        reviews = await loop.run_in_executor(None, _get_all_reviews)
        header = "Последние отзывы (до 20)"

    if not reviews:
        await message.answer("Отзывов пока нет.")
        return

    await message.answer(f"<b>{header}</b>  —  {len(reviews)} шт.", parse_mode="HTML")

    for r in reviews:
        stars = "⭐" * r["rating"]
        name = r.get("full_name") or "Покупатель"
        username = r.get("username") or ""
        comment = r.get("comment") or ""
        title = r.get("product_title") or r.get("product_id")
        date = r.get("created_at", "")[:10]


        rating_val = r["rating"]
        text = (
            f"{stars} <b>{rating_val}/5</b>\n"
            f"📄 {title}\n"
            f"👤 {name} {username}\n"
            f"📅 {date}"
        )
        if comment:
            text += f"\n💬 {comment}"

        kb = InlineKeyboardMarkup()
        kb.add(InlineKeyboardButton(
            "🗑 Удалить этот отзыв",
            callback_data=f"rev:del:{r['id']}"
        ))
        await message.answer(text, reply_markup=kb, parse_mode="HTML")


@dp.message_handler(commands=["refresh"], user_id=ADMIN_IDS)
async def cmd_refresh(message: types.Message):
    _products_cache = (0.0, [])
    _purchases_sheet_title = None
    loop = asyncio.get_running_loop()
    await loop.run_in_executor(None, _db_cleanup_pending_orders)
    logger.info("Admin triggered cache refresh + pending cleanup")
    await message.answer("✅ Кеш товаров очищен. Старые незавершённые заказы удалены.")


@dp.message_handler(content_types=types.ContentType.DOCUMENT, user_id=ADMIN_IDS)
async def debug_get_file_id_doc(message: types.Message):
    await message.reply(
        f"📄 file_id:\n<code>{message.document.file_id}</code>",
        parse_mode="HTML"
    )


@dp.message_handler(content_types=types.ContentType.PHOTO, user_id=ADMIN_IDS)
async def debug_get_file_id_photo(message: types.Message):
    photo = message.photo[-1]
    await message.reply(
        f"🖼 preview_file_id:\n<code>{photo.file_id}</code>",
        parse_mode="HTML"
    )


# =========================
# ADMIN PANEL — FSM States
# =========================

class AddProduct(StatesGroup):
    waiting_pdf = State()
    waiting_preview = State()
    waiting_title = State()
    waiting_desc = State()
    waiting_category = State()
    waiting_price_xtr = State()
    waiting_price_crypto = State()
    waiting_price_rub = State()
    waiting_age = State()
    waiting_tags = State()
    confirm = State()


class EditProduct(StatesGroup):
    choosing_field = State()
    waiting_value = State()


def admin_main_kb() -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(
        InlineKeyboardButton("➕ Добавить товар", callback_data="adm:add"),
        InlineKeyboardButton("📋 Список товаров", callback_data="adm:list"),
    )
    kb.add(
        InlineKeyboardButton("📊 Статистика", callback_data="adm:stats"),
        InlineKeyboardButton("🔄 Сбросить кеш", callback_data="adm:refresh"),
    )
    return kb


def admin_edit_kb(product_id: str) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    fields = [
        ("Название", "title"), ("Описание", "desc"),
        ("Категория", "category"), ("Цена Stars", "price_xtr"),
        ("Цена Крипто", "price_crypto"), ("Цена ₽", "price_rub"),
        ("PDF файл", "file_id"),
        ("Превью фото", "preview_file_id"), ("Возраст", "age_range"),
        ("Теги", "tags"),
    ]
    for label, field in fields:
        kb.add(InlineKeyboardButton(label, callback_data=f"adm:ef:{product_id}:{field}"))
    kb.add(InlineKeyboardButton("← К списку", callback_data="adm:list"))
    return kb


def admin_confirm_kb() -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(
        InlineKeyboardButton("✅ Добавить", callback_data="adm:confirm"),
        InlineKeyboardButton("❌ Отмена", callback_data="adm:cancel"),
    )
    return kb


def cancel_kb() -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("❌ Отменить добавление", callback_data="adm:cancel"))
    return kb


def admin_category_kb(categories: list) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    for cat in categories:
        kb.add(InlineKeyboardButton(cat, callback_data=f"adm:cat:{cat}"))
    kb.add(InlineKeyboardButton("➕ Новая категория", callback_data="adm:cat:__new__"))
    kb.add(InlineKeyboardButton("❌ Отмена", callback_data="adm:cancel"))
    return kb


def _gen_product_id() -> str:
    import uuid
    return "p" + uuid.uuid4().hex[:8]


def _format_admin_card(p: dict) -> str:
    active_str = "🟢 Активен" if p.get("active", 1) else "🔴 Неактивен"
    price_xtr = int(p.get("price_xtr", 0) or 0)
    price_crypto = p.get("price_crypto", "") or ""
    crypto_asset = p.get("crypto_asset", "") or ""
    price_parts = []
    if price_xtr > 0:
        price_parts.append(f"⭐ {price_xtr} Stars")
    if price_crypto:
        price_parts.append(f"💰 {price_crypto} {crypto_asset}")
    price_rub_a = int(p.get("price_rub", 0) or 0)
    if price_rub_a > 0:
        price_parts.append(f"💳 {price_rub_a} ₽")
    if not price_parts:
        price_parts.append("🎁 Бесплатно")

    age_min = int(p.get("age_min", 0) or 0)
    age_max = int(p.get("age_max", 99) or 99)
    if age_min > 0 or age_max < 99:
        age_display = f"{age_min}–{age_max} лет" if age_min != age_max else f"{age_min} лет"
    else:
        age_display = "не указан"

    tags = p.get("tags", "") or "не указаны"

    return (
        f"<b>{p['title']}</b>\n"
        f"📂 {p.get('category', '—')}\n"
        f"💳 {' | '.join(price_parts)}\n"
        f"👶 Возраст: {age_display}\n"
        f"🏷 Теги: {tags}\n"
        f"🆔 <code>{p['product_id']}</code>\n"
        f"{active_str}"
    )


@dp.message_handler(commands=["admin"], user_id=ADMIN_IDS)
async def cmd_admin(message: types.Message):
    await message.answer(
        "🛠 <b>Панель управления</b>",
        reply_markup=admin_main_kb(),
        parse_mode="HTML"
    )


@dp.callback_query_handler(lambda c: c.data == "adm:back", user_id=ADMIN_IDS)
async def adm_back(call: types.CallbackQuery):
    await call.answer()
    try:
        await call.message.edit_text(
            "🛠 <b>Панель управления</b>",
            reply_markup=admin_main_kb(),
            parse_mode="HTML"
        )
    except Exception:
        await call.message.answer("🛠 <b>Панель управления</b>", reply_markup=admin_main_kb(), parse_mode="HTML")


@dp.callback_query_handler(lambda c: c.data == "adm:list", user_id=ADMIN_IDS)
async def adm_list(call: types.CallbackQuery):
    await call.answer()
    loop = asyncio.get_running_loop()
    products = await loop.run_in_executor(None, _db_get_all_products, False)
    if not products:
        await call.message.answer("Товаров пока нет.", reply_markup=admin_main_kb())
        return

    cats = sorted({p.get("category", "Без категории") for p in products})
    total = len(products)
    cat_counts: Dict[str, int] = {}
    for p in products:
        cat = p.get("category", "Без категории")
        cat_counts[cat] = cat_counts.get(cat, 0) + 1

    kb = InlineKeyboardMarkup(row_width=1)
    for cat in cats:
        kb.add(InlineKeyboardButton(
            f"{cat} ({cat_counts[cat]})",
            callback_data=f"adm:listcat:{cat}"
        ))
    kb.add(InlineKeyboardButton(f"📋 Все товары ({total})", callback_data="adm:listcat:__all__"))
    kb.add(InlineKeyboardButton("⬅️ Назад", callback_data="adm:back"))

    try:
        await call.message.edit_text("📂 <b>Выбери категорию:</b>", reply_markup=kb, parse_mode="HTML")
    except Exception:
        await call.message.answer("📂 <b>Выбери категорию:</b>", reply_markup=kb, parse_mode="HTML")


@dp.callback_query_handler(lambda c: c.data.startswith("adm:listcat:"), user_id=ADMIN_IDS)
async def adm_list_category(call: types.CallbackQuery):
    await call.answer()
    cat_raw = call.data.split("adm:listcat:", 1)[1]
    loop = asyncio.get_running_loop()
    all_products = await loop.run_in_executor(None, _db_get_all_products, False)

    if cat_raw == "__all__":
        products = all_products
        title = f"📋 Все товары ({len(products)})"
    else:
        products = [p for p in all_products if p.get("category") == cat_raw]
        title = f"📂 {cat_raw} ({len(products)})"

    if not products:
        await call.message.answer("В этой категории нет товаров.")
        return

    await call.message.answer(f"<b>{title}</b>", parse_mode="HTML")
    await _show_products_in_category(call.message.chat.id, products)


async def _show_products_in_category(chat_id: int, products: list) -> None:
    for p in products:
        active = bool(p.get("active", 1))
        status = "🟢" if active else "🔴"
        price_xtr = int(p.get("price_xtr", 0) or 0)
        kb = InlineKeyboardMarkup(row_width=2)
        kb.add(
            InlineKeyboardButton("✏️ Ред.", callback_data=f"adm:edit:{p['product_id']}"),
            InlineKeyboardButton(
                "🔴 Откл." if active else "🟢 Вкл.",
                callback_data=f"adm:toggle:{p['product_id']}"
            ),
        )
        text = (
            f"{status} <b>{p['title']}</b>\n"
            f"📂 {p.get('category', '—')}  |  "
            + (f"⭐ {price_xtr} Stars" if price_xtr else "🎁 Бесплатно")
            + f"\n<code>{p['product_id']}</code>"
        )
        await bot.send_message(chat_id, text, reply_markup=kb, parse_mode="HTML")
    back_kb = InlineKeyboardMarkup().add(
        InlineKeyboardButton("⬅️ К категориям", callback_data="adm:list")
    )
    await bot.send_message(chat_id, "─────────────", reply_markup=back_kb)


@dp.callback_query_handler(lambda c: c.data.startswith("adm:toggle:"), user_id=ADMIN_IDS)
async def adm_toggle(call: types.CallbackQuery):
    pid = call.data.split("adm:toggle:", 1)[1]
    loop = asyncio.get_running_loop()
    prod = await loop.run_in_executor(None, _db_get_product, pid)
    if not prod:
        await call.answer("Товар не найден.", show_alert=True)
        return
    new_active = not bool(prod.get("active", 1))
    await loop.run_in_executor(None, _db_set_product_active, pid, new_active)
    global _products_cache
    _products_cache = (0.0, [])
    status_text = "🟢 активирован" if new_active else "🔴 деактивирован"
    await call.answer(f"Товар {status_text}!", show_alert=True)
    try:
        new_kb = InlineKeyboardMarkup(row_width=2)
        new_kb.add(
            InlineKeyboardButton("✏️ Ред.", callback_data=f"adm:edit:{pid}"),
            InlineKeyboardButton(
                "🔴 Откл." if new_active else "🟢 Вкл.",
                callback_data=f"adm:toggle:{pid}"
            ),
        )
        await call.message.edit_reply_markup(reply_markup=new_kb)
    except Exception:
        pass


@dp.callback_query_handler(lambda c: c.data == "adm:stats", user_id=ADMIN_IDS)
async def adm_stats(call: types.CallbackQuery):
    await call.answer()
    loop = asyncio.get_running_loop()
    stats = await loop.run_in_executor(None, _db_get_stats)
    top_text = "".join(f"  • {title}: {cnt} шт.\n" for title, cnt in stats["top_products"])
    text = (
        "📊 <b>Статистика</b>\n\n"
        f"👤 Покупателей: <b>{stats['unique_buyers']}</b>\n"
        f"🛒 Покупок всего: <b>{stats['total_purchases']}</b>\n"
        f"📅 Сегодня: <b>{stats['today']}</b>\n\n"
        f"📦 Активных товаров: <b>{stats['products_active']}</b> / {stats['products_total']}\n\n"
        f"🏆 Топ-5:\n{top_text or '  —'}"
    )
    kb = InlineKeyboardMarkup().add(InlineKeyboardButton("⬅️ Назад", callback_data="adm:back"))
    try:
        await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")
    except Exception:
        await call.message.answer(text, reply_markup=kb, parse_mode="HTML")


@dp.callback_query_handler(lambda c: c.data == "adm:refresh", user_id=ADMIN_IDS)
async def adm_refresh_cb(call: types.CallbackQuery):
    await call.answer()
    global _products_cache, _purchases_sheet_title
    _products_cache = (0.0, [])
    _purchases_sheet_title = None
    loop = asyncio.get_running_loop()
    await loop.run_in_executor(None, _db_cleanup_pending_orders)
    await call.message.answer("✅ Кеш сброшен, старые заказы очищены.")


# ---- ADD PRODUCT FSM ----

@dp.callback_query_handler(lambda c: c.data == "adm:add", user_id=ADMIN_IDS, state="*")
async def adm_add_start(call: types.CallbackQuery, state: FSMContext):
    await call.answer()
    await state.finish()
    await state.set_state(AddProduct.waiting_pdf)
    await call.message.answer(
        "➕ <b>Добавление товара</b>\n\n"
        "Шаг 1/7: Отправь <b>PDF-файл</b> товара 📄",
        reply_markup=cancel_kb(),
        parse_mode="HTML"
    )


@dp.message_handler(commands=["cancel"], user_id=ADMIN_IDS, state="*")
async def adm_cancel_cmd(message: types.Message, state: FSMContext):
    await state.finish()
    await message.answer("❌ Отменено.", reply_markup=admin_main_kb())


@dp.callback_query_handler(lambda c: c.data == "adm:cancel", user_id=ADMIN_IDS, state="*")
async def adm_cancel_cb(call: types.CallbackQuery, state: FSMContext):
    await call.answer()
    await state.finish()
    await call.message.answer("❌ Отменено.", reply_markup=admin_main_kb())


@dp.message_handler(
    content_types=types.ContentType.DOCUMENT,
    user_id=ADMIN_IDS,
    state=AddProduct.waiting_pdf
)
async def adm_got_pdf(message: types.Message, state: FSMContext):
    if message.document.mime_type != "application/pdf":
        await message.answer("⚠️ Нужен PDF-файл. Попробуй ещё раз.")
        return
    await state.update_data(file_id=message.document.file_id)
    await state.set_state(AddProduct.waiting_preview)
    await message.answer(
        "✅ PDF получен!\n\n"
        "Шаг 2/7: Отправь <b>фото-превью</b> 🖼\n"
        "или напиши <b>нет</b> чтобы пропустить",
        reply_markup=cancel_kb(),
        parse_mode="HTML"
    )


@dp.message_handler(
    content_types=[types.ContentType.PHOTO, types.ContentType.TEXT],
    user_id=ADMIN_IDS,
    state=AddProduct.waiting_preview
)
async def adm_got_preview(message: types.Message, state: FSMContext):
    preview_file_id = message.photo[-1].file_id if message.photo else ""
    await state.update_data(preview_file_id=preview_file_id)
    await state.set_state(AddProduct.waiting_title)
    await message.answer("Шаг 3/7: Введи <b>название</b> товара", reply_markup=cancel_kb(), parse_mode="HTML")


@dp.message_handler(user_id=ADMIN_IDS, state=AddProduct.waiting_title)
async def adm_got_title(message: types.Message, state: FSMContext):
    title = message.text.strip()
    if len(title) < 2:
        await message.answer("⚠️ Слишком короткое название.")
        return
    await state.update_data(title=title)
    await state.set_state(AddProduct.waiting_desc)
    await message.answer(
        "Шаг 4/7: Введи <b>описание</b> товара\n(или <b>нет</b> для пропуска)",
        reply_markup=cancel_kb(),
        parse_mode="HTML"
    )


@dp.message_handler(user_id=ADMIN_IDS, state=AddProduct.waiting_desc)
async def adm_got_desc(message: types.Message, state: FSMContext):
    desc = "" if message.text.strip().lower() == "нет" else message.text.strip()
    await state.update_data(description=desc)
    await state.set_state(AddProduct.waiting_category)
    await _send_category_choice(message.chat.id)


async def _send_category_choice(chat_id: int, text_prefix: str = "Шаг 5/7: Выбери <b>категорию</b>") -> None:
    loop = asyncio.get_running_loop()
    products = await loop.run_in_executor(None, _db_get_all_products, False)
    cats = sorted({p.get("category", "") for p in products if p.get("category")})
    if cats:
        await bot.send_message(
            chat_id,
            f"{text_prefix}\n\nНажми на существующую или создай новую:",
            reply_markup=admin_category_kb(cats),
            parse_mode="HTML"
        )
    else:
        await bot.send_message(
            chat_id,
            f"{text_prefix}\n\nВведи название новой категории:",
            parse_mode="HTML"
        )


@dp.callback_query_handler(
    lambda c: c.data.startswith("adm:cat:") and not c.data.startswith("adm:cat:__new__"),
    user_id=ADMIN_IDS, state=AddProduct.waiting_category
)
async def adm_pick_category(call: types.CallbackQuery, state: FSMContext):
    category = call.data.split("adm:cat:", 1)[1]
    await call.answer()
    await state.update_data(category=category)
    await state.set_state(AddProduct.waiting_price_xtr)
    await call.message.answer(
        f"✅ Категория: <b>{category}</b>\n\n"
        "Шаг 6/7: Цена в <b>Stars</b> (целое число, 0 = бесплатно)",
        reply_markup=cancel_kb(),
        parse_mode="HTML"
    )


@dp.callback_query_handler(
    lambda c: c.data == "adm:cat:__new__",
    user_id=ADMIN_IDS, state=AddProduct.waiting_category
)
async def adm_new_category_prompt(call: types.CallbackQuery):
    await call.answer()
    await call.message.answer("Введи название <b>новой категории</b>:", reply_markup=cancel_kb(), parse_mode="HTML")


@dp.message_handler(user_id=ADMIN_IDS, state=AddProduct.waiting_category)
async def adm_got_category(message: types.Message, state: FSMContext):
    category = message.text.strip()
    if len(category) < 2:
        await message.answer("⚠️ Слишком короткое название категории.")
        return
    await state.update_data(category=category)
    await state.set_state(AddProduct.waiting_price_xtr)
    await message.answer(
        f"✅ Новая категория: <b>{category}</b>\n\n"
        "Шаг 6/7: Цена в <b>Stars</b> (целое число, 0 = бесплатно)",
        reply_markup=cancel_kb(),
        parse_mode="HTML"
    )


@dp.message_handler(user_id=ADMIN_IDS, state=AddProduct.waiting_price_xtr)
async def adm_got_price_xtr(message: types.Message, state: FSMContext):
    try:
        price = int(message.text.strip())
        if price < 0:
            raise ValueError
    except ValueError:
        await message.answer("⚠️ Введи целое неотрицательное число. Пример: <code>50</code>", parse_mode="HTML")
        return
    await state.update_data(price_xtr=price)
    await state.set_state(AddProduct.waiting_price_crypto)
    await message.answer(
        f"Шаг 7/10: Цена в <b>крипте</b> (например <code>1.5</code>)\n"
        f"Валюта по умолчанию: {CRYPTO_PAY_DEFAULT_ASSET}\n"
        "Или напиши <b>нет</b>",
        reply_markup=cancel_kb(),
        parse_mode="HTML"
    )


@dp.message_handler(user_id=ADMIN_IDS, state=AddProduct.waiting_price_crypto)
async def adm_got_price_crypto(message: types.Message, state: FSMContext):
    text = message.text.strip()
    if text.lower() == "нет":
        await state.update_data(price_crypto="", crypto_asset="")
    else:
        # Нормализуем: убираем пробелы, заменяем запятую
        normalized = text.replace(" ", "").replace(",", ".")
        test_prod = {"price_crypto": normalized, "product_id": "test"}
        if parse_crypto_amount(test_prod) is None:
            await message.answer(
                "⚠️ Неверный формат. Введи число, например: <code>0.2</code> или <code>1.5</code>\n"
                "Или напиши <b>нет</b>",
                parse_mode="HTML"
            )
            return
        await state.update_data(price_crypto=normalized, crypto_asset=CRYPTO_PAY_DEFAULT_ASSET)

    await state.set_state(AddProduct.waiting_price_rub)
    await message.answer(
        "Шаг 8/10: Цена в <b>рублях</b> (для оплаты картой РФ)\n\n"
        "Введи целое число, например: <code>150</code>\n"
        "Или напиши <b>нет</b> если оплата картой недоступна для этого товара",
        reply_markup=cancel_kb(),
        parse_mode="HTML"
    )


@dp.message_handler(user_id=ADMIN_IDS, state=AddProduct.waiting_price_rub)
async def adm_got_price_rub(message: types.Message, state: FSMContext):
    text = message.text.strip()
    if text.lower() == "нет":
        await state.update_data(price_rub=0)
    else:
        try:
            price = int(text)
            if price < 0:
                raise ValueError
            await state.update_data(price_rub=price)
        except ValueError:
            await message.answer(
                "⚠️ Введи целое неотрицательное число. Например: <code>150</code>\n"
                "Или напиши <b>нет</b>",
                parse_mode="HTML"
            )
            return

    await state.set_state(AddProduct.waiting_age)
    await _send_age_choice(message.chat.id)


# ---- Вспомогательные клавиатуры для возраста и тегов ----

# Предустановленные возрастные диапазоны
_AGE_PRESETS = ["3-4", "4-5", "5-6", "6-8", "3-6", "4-8"]

# Предустановленные теги (совпадают с INTEREST_TAGS в квизе)
_TAG_PRESETS = ["творчество", "наука", "логика"]


def admin_age_kb(selected: list = None) -> InlineKeyboardMarkup:
    """Клавиатура выбора возраста с пресетами + кнопка ввода вручную."""
    selected = selected or []
    kb = InlineKeyboardMarkup(row_width=3)
    for age in _AGE_PRESETS:
        tick = "✅ " if age in selected else ""
        kb.insert(InlineKeyboardButton(
            f"{tick}{age}",
            callback_data=f"adm:age:{age}"
        ))
    kb.add(InlineKeyboardButton("✏️ Ввести вручную", callback_data="adm:age:__custom__"))
    kb.add(InlineKeyboardButton("➡️ Пропустить", callback_data="adm:age:__skip__"))
    kb.add(InlineKeyboardButton("❌ Отмена", callback_data="adm:cancel"))
    return kb


def admin_tags_kb(selected: list = None) -> InlineKeyboardMarkup:
    """Клавиатура выбора тегов — можно выбрать несколько + подтвердить."""
    selected = selected or []
    kb = InlineKeyboardMarkup(row_width=1)
    for tag in _TAG_PRESETS:
        tick = "✅ " if tag in selected else "◻️ "
        kb.add(InlineKeyboardButton(
            f"{tick}{tag}",
            callback_data=f"adm:tag:{tag}"
        ))
    kb.add(InlineKeyboardButton("✏️ Добавить свой тег", callback_data="adm:tag:__custom__"))
    if selected:
        kb.add(InlineKeyboardButton(
            f"✔️ Готово ({', '.join(selected)})",
            callback_data="adm:tag:__done__"
        ))
    else:
        kb.add(InlineKeyboardButton("➡️ Пропустить (без тегов)", callback_data="adm:tag:__done__"))
    kb.add(InlineKeyboardButton("❌ Отмена", callback_data="adm:cancel"))
    return kb


async def _send_age_choice(chat_id: int) -> None:
    await bot.send_message(
        chat_id,
        "Шаг 9/10: Для какого <b>возраста</b>?\n\n"
        "Выбери готовый диапазон или введи свой:",
        reply_markup=admin_age_kb(),
        parse_mode="HTML"
    )


async def _send_tags_choice(chat_id: int, selected: list = None) -> None:
    selected = selected or []
    await bot.send_message(
        chat_id,
        "Шаг 10/10: Выбери <b>теги</b> — по ним квиз подбирает материалы.\n\n"
        "Можно выбрать несколько:",
        reply_markup=admin_tags_kb(selected),
        parse_mode="HTML"
    )


# ---- Обработчики выбора возраста ----

@dp.callback_query_handler(lambda c: c.data.startswith("adm:age:"), user_id=ADMIN_IDS,
                            state=AddProduct.waiting_age)
async def adm_age_btn(call: types.CallbackQuery, state: FSMContext):
    value = call.data.split("adm:age:", 1)[1]
    await call.answer()

    if value == "__skip__":
        await state.update_data(age_range="")
        await state.set_state(AddProduct.waiting_tags)
        data = await state.get_data()
        await _send_tags_choice(call.message.chat.id, data.get("_selected_tags", []))
        return

    if value == "__custom__":
        await call.message.answer(
            "Введи диапазон вручную, например: <code>3-6</code> или <code>5</code>",
            reply_markup=cancel_kb(),
            parse_mode="HTML"
        )
        return

    # Выбран пресет
    await state.update_data(age_range=value)
    await state.set_state(AddProduct.waiting_tags)
    data = await state.get_data()
    await call.message.answer(
        f"✅ Возраст: <b>{value} лет</b>",
        parse_mode="HTML"
    )
    await _send_tags_choice(call.message.chat.id, data.get("_selected_tags", []))


@dp.message_handler(user_id=ADMIN_IDS, state=AddProduct.waiting_age)
async def adm_got_age(message: types.Message, state: FSMContext):
    """Ручной ввод возраста."""
    text = message.text.strip()
    if text.lower() in ("нет", "no", "-"):
        await state.update_data(age_range="")
    else:
        age_min, age_max = _parse_age_range(text)
        if age_min == 0 and age_max == 99:
            await message.answer(
                "⚠️ Не распознал. Напиши например <code>3-6</code> или нажми кнопку выше",
                parse_mode="HTML"
            )
            return
        await state.update_data(age_range=text)
        await message.answer(f"✅ Возраст: <b>{text} лет</b>", parse_mode="HTML")

    await state.set_state(AddProduct.waiting_tags)
    data = await state.get_data()
    await _send_tags_choice(message.chat.id, data.get("_selected_tags", []))


# ---- Обработчики выбора тегов (мультивыбор) ----

@dp.callback_query_handler(lambda c: c.data.startswith("adm:tag:"), user_id=ADMIN_IDS,
                            state=AddProduct.waiting_tags)
async def adm_tag_btn(call: types.CallbackQuery, state: FSMContext):
    value = call.data.split("adm:tag:", 1)[1]
    data = await state.get_data()
    selected = list(data.get("_selected_tags", []))
    await call.answer()

    if value == "__custom__":
        await call.message.answer(
            "Введи свой тег (одно слово или фраза):",
            reply_markup=cancel_kb()
        )
        return

    if value == "__done__":
        # Завершаем выбор тегов
        await state.update_data(tags=",".join(selected))
        await _show_add_confirm(call.message, state)
        return

    # Переключаем тег в выбранных
    if value in selected:
        selected.remove(value)
    else:
        selected.append(value)

    await state.update_data(_selected_tags=selected)

    # Редактируем клавиатуру на месте
    try:
        await call.message.edit_reply_markup(reply_markup=admin_tags_kb(selected))
    except Exception:
        pass


@dp.message_handler(user_id=ADMIN_IDS, state=AddProduct.waiting_tags)
async def adm_got_tags(message: types.Message, state: FSMContext):
    """Ручной ввод тега или завершение через текст."""
    text = message.text.strip().lower()
    data = await state.get_data()
    selected = list(data.get("_selected_tags", []))

    if text in ("нет", "no", "-", ""):
        # Пропустить теги
        await state.update_data(tags="")
    else:
        # Добавляем введённый тег к уже выбранным
        normalized = _normalize_tags(text)
        for tag in normalized.split(","):
            tag = tag.strip()
            if tag and tag not in selected:
                selected.append(tag)
        await state.update_data(_selected_tags=selected, tags=",".join(selected))
        await message.answer(
            f"✅ Тег добавлен. Выбрано: <b>{', '.join(selected)}</b>\n\n"
            "Нажми <b>Готово</b> или добавь ещё:",
            reply_markup=admin_tags_kb(selected),
            parse_mode="HTML"
        )
        return

    await _show_add_confirm(message, state)


async def _show_add_confirm(msg_or_call, state: FSMContext) -> None:
    """Показывает итоговую карточку товара перед добавлением."""
    data = await state.get_data()
    product_id = _gen_product_id()
    await state.update_data(product_id=product_id)

    price_line = f"⭐ {data['price_xtr']} Stars"
    if data.get("price_crypto"):
        price_line += f"  |  {data['price_crypto']} {data.get('crypto_asset', '')}"
    if int(data.get("price_rub", 0) or 0) > 0:
        price_line += f"  |  {data['price_rub']} ₽ 💳"
    if not data["price_xtr"] and not data.get("price_crypto") and not int(data.get("price_rub", 0) or 0):
        price_line = "🎁 Бесплатно"

    age_range = data.get("age_range", "")
    age_min, age_max = _parse_age_range(age_range)
    if age_min > 0 or age_max < 99:
        age_display = f"{age_min}–{age_max} лет" if age_min != age_max else f"{age_min} лет"
    else:
        age_display = "не указан"

    tags_display = data.get("tags", "") or "не указаны"

    preview_text = (
        f"📄 <b>{data['title']}</b>\n"
        f"<i>📂 {data['category']}</i>\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{data.get('description', '') or 'PDF файл'}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{price_line}\n"
        f"👶 Возраст: {age_display}\n"
        f"🏷 Теги: {tags_display}\n\n"
        f"🆔 <code>{product_id}</code>\n\n"
        f"Добавить товар?"
    )
    await state.set_state(AddProduct.confirm)

    # msg_or_call может быть Message или CallbackQuery.message
    chat_id = msg_or_call.chat.id if hasattr(msg_or_call, 'chat') else msg_or_call.message.chat.id
    preview_id = data.get("preview_file_id")
    if preview_id:
        await bot.send_photo(
            chat_id,
            preview_id,
            caption=preview_text,
            reply_markup=admin_confirm_kb(),
            parse_mode="HTML"
        )
    else:
        await bot.send_message(
            chat_id,
            preview_text,
            reply_markup=admin_confirm_kb(),
            parse_mode="HTML"
        )


@dp.callback_query_handler(lambda c: c.data == "adm:confirm", user_id=ADMIN_IDS, state=AddProduct.confirm)
async def adm_confirm_add(call: types.CallbackQuery, state: FSMContext):
    await call.answer()
    data = await state.get_data()
    await state.finish()
    loop = asyncio.get_running_loop()
    ok = await loop.run_in_executor(None, _db_insert_product, data)
    global _products_cache
    _products_cache = (0.0, [])
    if ok:
        await call.message.answer(
            f"✅ Товар <b>{data['title']}</b> добавлен!\n"
            f"🆔 <code>{data['product_id']}</code>",
            reply_markup=admin_main_kb(),
            parse_mode="HTML"
        )
    else:
        await call.message.answer(
            "❌ Не удалось добавить. ID уже существует или ошибка БД.",
            reply_markup=admin_main_kb()
        )


# ---- EDIT PRODUCT FSM ----

@dp.callback_query_handler(lambda c: c.data.startswith("adm:edit:"), user_id=ADMIN_IDS, state="*")
async def adm_edit_product(call: types.CallbackQuery, state: FSMContext):
    await call.answer()
    await state.finish()
    pid = call.data.split("adm:edit:", 1)[1]
    loop = asyncio.get_running_loop()
    prod = await loop.run_in_executor(None, _db_get_product, pid)
    if not prod:
        await call.answer("Товар не найден.", show_alert=True)
        return
    await state.update_data(editing_product_id=pid)
    await call.message.answer(
        f"✏️ <b>Редактирование:</b>\n\n{_format_admin_card(prod)}\n\nЧто изменить?",
        reply_markup=admin_edit_kb(pid),
        parse_mode="HTML"
    )


@dp.callback_query_handler(lambda c: c.data.startswith("adm:ef:"), user_id=ADMIN_IDS, state="*")
async def adm_edit_field(call: types.CallbackQuery, state: FSMContext):
    await call.answer()
    # FIX: state.finish() перед установкой нового состояния — очищаем предыдущее
    await state.finish()
    parts = call.data.split(":")
    pid, field = parts[2], parts[3]
    await state.update_data(editing_product_id=pid, editing_field=field)
    await state.set_state(EditProduct.waiting_value)
    prompts = {
        "title": "Введи новое <b>название</b>:",
        "desc": "Введи новое <b>описание</b> (или <b>нет</b> для пустого):",
        "price_xtr": "Введи новую цену в <b>Stars</b> (целое число):",
        "price_crypto": "Введи новую цену в <b>крипте</b> или <b>нет</b>:",
        "price_rub": "Введи новую цену в <b>рублях</b> (целое число, 0 = убрать):",
        "file_id": "Отправь новый <b>PDF-файл</b>:",
        "preview_file_id": "Отправь новое <b>фото-превью</b> или напиши <b>нет</b>:",
        "age_range": (
            "Введи возраст для которого подходит материал.\n\n"
            "Например: <code>3-6</code> или <code>4-5</code>\n"
            "Или <b>нет</b> если возраст не важен"
        ),
        "tags": (
            "Введи теги-интересы через запятую.\n\n"
            "<b>Доступные теги:</b>\n"
            "• <code>творчество</code> — разукрашки, задания\n"
            "• <code>наука</code> — познавательные сказки\n"
            "• <code>логика</code> — развивающие игры, вопросы\n\n"
            "Пример: <code>творчество, логика</code>\n"
            "Или <b>нет</b> чтобы сбросить"
        ),
    }
    if field == "category":
        await _send_category_choice(call.message.chat.id, "Выбери <b>новую категорию</b>")
    elif field == "age_range":
        # Показываем кнопки возраста, сохраняем текущее значение как уже выбранное
        loop = asyncio.get_running_loop()
        prod = await loop.run_in_executor(None, _db_get_product, pid)
        cur_age = ""
        if prod:
            a_min = int(prod.get("age_min", 0) or 0)
            a_max = int(prod.get("age_max", 99) or 99)
            if a_min > 0 or a_max < 99:
                cur_age = f"{a_min}-{a_max}"
        age_label = cur_age if cur_age else "не задан"
        await call.message.answer(
            "Текущий возраст: <b>" + age_label + "</b>\n\nВыбери новый:",
            reply_markup=admin_age_kb([cur_age] if cur_age else []),
            parse_mode="HTML"
        )
    elif field == "tags":
        # Показываем кнопки тегов с текущим выбором
        loop = asyncio.get_running_loop()
        prod = await loop.run_in_executor(None, _db_get_product, pid)
        cur_tags = []
        if prod and prod.get("tags"):
            cur_tags = [t.strip() for t in prod["tags"].split(",") if t.strip()]
        await state.update_data(_selected_tags=cur_tags)
        await call.message.answer(
            "Текущие теги: <b>" + (", ".join(cur_tags) or "не заданы") + "</b>\n\nВыбери теги:",
            reply_markup=admin_tags_kb(cur_tags),
            parse_mode="HTML"
        )
    else:
        await call.message.answer(prompts.get(field, "Введи новое значение:"), parse_mode="HTML")


@dp.callback_query_handler(
    lambda c: c.data.startswith("adm:cat:") and not c.data.startswith("adm:cat:__new__"),
    user_id=ADMIN_IDS, state=EditProduct.waiting_value
)
async def adm_edit_pick_category(call: types.CallbackQuery, state: FSMContext):
    data = await state.get_data()
    if data.get("editing_field") != "category":
        await call.answer()
        return
    category = call.data.split("adm:cat:", 1)[1]
    await call.answer()
    pid = data.get("editing_product_id")
    loop = asyncio.get_running_loop()
    ok = await loop.run_in_executor(None, _db_update_product, pid, {"category": category})
    global _products_cache
    _products_cache = (0.0, [])
    await state.finish()
    if ok:
        prod = await loop.run_in_executor(None, _db_get_product, pid)
        await call.message.answer(
            f"✅ Категория обновлена: <b>{category}</b>\n\n{_format_admin_card(prod)}",
            reply_markup=admin_edit_kb(pid),
            parse_mode="HTML"
        )
    else:
        await call.message.answer("❌ Не удалось обновить.", reply_markup=admin_main_kb())


@dp.callback_query_handler(
    lambda c: c.data == "adm:cat:__new__",
    user_id=ADMIN_IDS, state=EditProduct.waiting_value
)
async def adm_edit_new_category_prompt(call: types.CallbackQuery):
    await call.answer()
    await call.message.answer("Введи название <b>новой категории</b>:", parse_mode="HTML")


@dp.callback_query_handler(lambda c: c.data.startswith("adm:age:"),
                            user_id=ADMIN_IDS, state=EditProduct.waiting_value)
async def adm_edit_age_btn(call: types.CallbackQuery, state: FSMContext):
    """Выбор возраста кнопкой при редактировании."""
    value = call.data.split("adm:age:", 1)[1]
    data = await state.get_data()
    pid = data.get("editing_product_id")
    await call.answer()

    if value == "__custom__":
        await call.message.answer(
            "Введи диапазон вручную, например: <code>3-6</code>",
            reply_markup=cancel_kb(), parse_mode="HTML"
        )
        return

    if value == "__skip__":
        update = {"age_min": 0, "age_max": 99}
    else:
        age_min, age_max = _parse_age_range(value)
        update = {"age_min": age_min, "age_max": age_max}

    loop = asyncio.get_running_loop()
    ok = await loop.run_in_executor(None, _db_update_product, pid, update)
    global _products_cache
    _products_cache = (0.0, [])
    await state.finish()
    if ok:
        prod = await loop.run_in_executor(None, _db_get_product, pid)
        age_str = f"{update.get('age_min', 0)}–{update.get('age_max', 99)} лет" if value != "__skip__" else "не задан"
        await call.message.answer(
            f"✅ Возраст обновлён: <b>{age_str}</b>\n\n" + _format_admin_card(prod),
            reply_markup=admin_edit_kb(pid), parse_mode="HTML"
        )
    else:
        await call.message.answer("❌ Не удалось обновить.", reply_markup=admin_main_kb())


@dp.callback_query_handler(lambda c: c.data.startswith("adm:tag:"),
                            user_id=ADMIN_IDS, state=EditProduct.waiting_value)
async def adm_edit_tag_btn(call: types.CallbackQuery, state: FSMContext):
    """Выбор тегов кнопками при редактировании."""
    value = call.data.split("adm:tag:", 1)[1]
    data = await state.get_data()
    pid = data.get("editing_product_id")
    selected = list(data.get("_selected_tags", []))
    await call.answer()

    if value == "__custom__":
        await call.message.answer(
            "Введи свой тег:", reply_markup=cancel_kb()
        )
        return

    if value == "__done__":
        # Сохраняем
        new_tags = ",".join(selected)
        loop = asyncio.get_running_loop()
        ok = await loop.run_in_executor(None, _db_update_product, pid, {"tags": new_tags})
        global _products_cache
        _products_cache = (0.0, [])
        await state.finish()
        if ok:
            prod = await loop.run_in_executor(None, _db_get_product, pid)
            await call.message.answer(
                "✅ Теги обновлены: <b>" + (new_tags or "убраны") + "</b>\n\n" + _format_admin_card(prod),
                reply_markup=admin_edit_kb(pid), parse_mode="HTML"
            )
        else:
            await call.message.answer("❌ Не удалось обновить.", reply_markup=admin_main_kb())
        return

    # Переключаем тег
    if value in selected:
        selected.remove(value)
    else:
        selected.append(value)
    await state.update_data(_selected_tags=selected)
    try:
        await call.message.edit_reply_markup(reply_markup=admin_tags_kb(selected))
    except Exception:
        pass


@dp.message_handler(
    content_types=[types.ContentType.TEXT, types.ContentType.DOCUMENT, types.ContentType.PHOTO],
    user_id=ADMIN_IDS,
    state=EditProduct.waiting_value
)
async def adm_save_field(message: types.Message, state: FSMContext):
    data = await state.get_data()
    pid = data.get("editing_product_id")
    field = data.get("editing_field")
    text = message.text.strip() if message.text else ""
    update: Dict[str, Any] = {}

    if field == "title":
        if len(text) < 2:
            await message.answer("⚠️ Слишком короткое.")
            return
        update["title"] = text
    elif field == "desc":
        update["description"] = "" if text.lower() == "нет" else text
    elif field == "category":
        update["category"] = text
    elif field == "price_xtr":
        try:
            v = int(text)
            if v < 0:
                raise ValueError
            update["price_xtr"] = v
        except ValueError:
            await message.answer("⚠️ Введи целое неотрицательное число.")
            return
    elif field == "price_crypto":
        if text.lower() == "нет":
            update["price_crypto"] = ""
        else:
            test = {"price_crypto": text, "product_id": "test"}
            if parse_crypto_amount(test) is None:
                await message.answer("⚠️ Неверный формат. Пример: <code>1.5</code>", parse_mode="HTML")
                return
            update["price_crypto"] = text
    elif field == "price_rub":
        try:
            v = int(text)
            if v < 0:
                raise ValueError
            update["price_rub"] = v
        except ValueError:
            await message.answer("⚠️ Введи целое неотрицательное число или 0 чтобы убрать.")
            return
    elif field == "file_id":
        if message.document and message.document.mime_type == "application/pdf":
            update["file_id"] = message.document.file_id
        else:
            await message.answer("⚠️ Нужен PDF-файл.")
            return
    elif field == "preview_file_id":
        if message.photo:
            update["preview_file_id"] = message.photo[-1].file_id
        elif text.lower() == "нет":
            update["preview_file_id"] = ""
        else:
            await message.answer("⚠️ Отправь фото или напиши <b>нет</b>.", parse_mode="HTML")
            return
    elif field == "age_range":
        if text.lower() == "нет":
            update["age_min"] = 0
            update["age_max"] = 99
        else:
            age_min, age_max = _parse_age_range(text)
            if age_min == 0 and age_max == 99:
                await message.answer(
                    "⚠️ Не распознал. Напиши например <code>3-6</code> или <b>нет</b>",
                    parse_mode="HTML"
                )
                return
            update["age_min"] = age_min
            update["age_max"] = age_max
    elif field == "tags":
        if text.lower() == "нет":
            update["tags"] = ""
        else:
            update["tags"] = _normalize_tags(text)

    loop = asyncio.get_running_loop()
    ok = await loop.run_in_executor(None, _db_update_product, pid, update)
    global _products_cache
    _products_cache = (0.0, [])
    await state.finish()

    if ok:
        prod = await loop.run_in_executor(None, _db_get_product, pid)
        await message.answer(
            f"✅ Обновлено!\n\n{_format_admin_card(prod)}",
            reply_markup=admin_edit_kb(pid),
            parse_mode="HTML"
        )
    else:
        await message.answer("❌ Не удалось обновить.", reply_markup=admin_main_kb())


# =========================
# АНИМИРОВАННЫЙ СТАРТ
# =========================

@dp.message_handler(commands=["setgif"], user_id=ADMIN_IDS)
async def cmd_set_gif(message: types.Message):
    args = message.get_args().strip().lower()
    if args == "clear":
        _db_set_setting("start_gif", "")
        await message.answer("✅ Стартовая анимация удалена.")
        return
    await message.answer(
        "Отправь GIF-анимацию или стикер — он будет показываться новым пользователям при /start\n\n"
        "Чтобы удалить: /setgif clear"
    )


@dp.message_handler(
    content_types=[types.ContentType.ANIMATION, types.ContentType.STICKER],
    user_id=ADMIN_IDS
)
async def admin_got_animation(message: types.Message):
    if message.animation:
        _db_set_setting("start_gif", message.animation.file_id)
        _db_set_setting("start_gif_kind", "gif")
        await message.reply("Стартовая анимация сохранена!")
    elif message.sticker:
        _db_set_setting("start_gif", message.sticker.file_id)
        _db_set_setting("start_gif_kind", "sticker")
        await message.reply("Стартовый стикер сохранён!")


# =========================
# ИЗБРАННОЕ — toggle (из карточки товара)
# =========================

@dp.callback_query_handler(lambda c: c.data.startswith("fav:toggle:"))
async def cb_fav_toggle(call: types.CallbackQuery):
    # format: fav:toggle:{pid}:{category_key}
    parts = call.data.split(":")
    if len(parts) < 4:
        await call.answer("Некорректная кнопка.", show_alert=True)
        return
    pid = parts[2]
    category_key = parts[3]
    user = call.from_user
    loop = asyncio.get_running_loop()
    added = await loop.run_in_executor(None, _db_toggle_favourite, user.id, pid)
    await call.answer("❤️ Добавлено в избранное!" if added else "💔 Убрано из избранного")
    # Обновляем кнопки на карточке
    try:
        _all_products = await load_products()
        product = next((p for p in _all_products if p["product_id"] == pid), None)
        if product:
            kb = product_action_kb_fav(product, category_key, added)
            await call.message.edit_reply_markup(reply_markup=kb)
    except Exception:
        pass


def product_action_kb_fav(product: Dict[str, Any], category_key: str,
                           is_fav: bool) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    pid = product["product_id"]

    if is_free_product(product):
        kb.add(InlineKeyboardButton("Скачать бесплатно 🎁", callback_data=f"get:{pid}"))
    elif _has_multiple_pay_methods(product):
        kb.add(InlineKeyboardButton("Купить", callback_data=f"buy:{pid}:{category_key}"))
    else:
        price_xtr = int(product.get("price_xtr", 0) or 0)
        price_crypto_raw = _to_str(product.get("price_crypto", ""))
        crypto_asset = _to_str(product.get("crypto_asset", ""), CRYPTO_PAY_DEFAULT_ASSET).upper()
        if price_xtr > 0:
            kb.add(InlineKeyboardButton(
                f"Купить за {price_xtr} Stars ⭐",
                callback_data=f"paystars:{pid}"))
        elif can_buy_with_crypto(product):
            kb.add(InlineKeyboardButton(
                f"Купить за {price_crypto_raw} {crypto_asset}",
                callback_data=f"paycrypto:{pid}"))
        elif _has_card_payment(product):
            price_rub_fav = int(product.get("price_rub", 0) or 0)
            rub_label_fav = str(price_rub_fav) if price_rub_fav > 0 else CARD_PRICE_RUB
            kb.add(InlineKeyboardButton(
                f"Купить за {rub_label_fav} ₽ 💳",
                callback_data=f"paycard:{pid}:{category_key}"))

    fav_text = "Убрать из избранного 💔" if is_fav else "Добавить в избранное ❤️"
    kb.add(InlineKeyboardButton(fav_text, callback_data=f"fav:toggle:{pid}:{category_key}"))
    kb.add(InlineKeyboardButton("← Назад к списку", callback_data=f"back_items:{category_key}"))
    kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))
    return kb


# =========================
# КВИЗ — подбор материалов
# =========================

class QuizState(StatesGroup):
    age = State()
    interest = State()


# Возрастные группы → числовые диапазоны для фильтрации
AGE_GROUPS = ["3-4 года", "4-5 лет", "5-6 лет", "6-8 лет"]
AGE_RANGES: Dict[str, Tuple[int, int]] = {
    "3-4 года": (3, 4),
    "4-5 лет":  (4, 5),
    "5-6 лет":  (5, 6),
    "6-8 лет":  (6, 8),
}

# Интересы → теги которые ищем в поле tags товара
INTERESTS = ["Творчество", "Наука", "Логика", "Всё подряд"]
INTEREST_TAGS: Dict[str, List[str]] = {
    "Творчество": ["творчество"],
    "Наука":      ["наука"],
    "Логика":     ["логика"],
    "Всё подряд": [],   # пустой = без фильтра по тегу
}


def _quiz_filter_products(
    products: List[Dict[str, Any]],
    age_group: str,
    interest: str,
) -> List[Dict[str, Any]]:
    """
    Фильтрует товары по возрасту и интересу.

    Логика:
    1. Возраст: товар подходит если его диапазон [age_min, age_max] пересекается
       с выбранным диапазоном пользователя.
       Товары без возраста (age_min=0, age_max=99) — универсальные, всегда проходят.
    2. Теги: товар подходит если хотя бы один тег из interest_tags есть в его поле tags.
       Если interest_tags пуст (Всё подряд) — фильтр по тегам не применяется.
    3. Если после строгой фильтрации ничего нет — ослабляем:
       сначала убираем фильтр по тегам, потом и по возрасту.
    """
    q_min, q_max = AGE_RANGES.get(age_group, (0, 99))
    interest_tags = INTEREST_TAGS.get(interest, [])

    def age_matches(p: Dict) -> bool:
        p_min = int(p.get("age_min", 0) or 0)
        p_max = int(p.get("age_max", 99) or 99)
        # Универсальный товар (не заполнен) — подходит всегда
        if p_min == 0 and p_max == 99:
            return True
        # Пересечение диапазонов: [p_min, p_max] ∩ [q_min, q_max] ≠ ∅
        return p_min <= q_max and p_max >= q_min

    def tag_matches(p: Dict) -> bool:
        if not interest_tags:
            return True  # "Всё подряд" — без фильтра
        p_tags = [t.strip() for t in (p.get("tags", "") or "").split(",") if t.strip()]
        return any(it in p_tags for it in interest_tags)

    # Попытка 1: строгая фильтрация — и возраст, и теги
    strict = [p for p in products if age_matches(p) and tag_matches(p)]
    if strict:
        return strict

    # Попытка 2: только возраст (без фильтра тегов)
    age_only = [p for p in products if age_matches(p)]
    if age_only:
        return age_only

    # Попытка 3: только теги (без фильтра возраста) — редкий случай
    tags_only = [p for p in products if tag_matches(p)]
    if tags_only:
        return tags_only

    # Fallback: возвращаем всё
    return products


@dp.callback_query_handler(lambda c: c.data == "quiz:start", state="*")
async def quiz_start(call: types.CallbackQuery, state: FSMContext):
    await call.answer()
    await state.finish()
    await state.set_state(QuizState.age)
    kb = InlineKeyboardMarkup(row_width=2)
    for age in AGE_GROUPS:
        kb.add(InlineKeyboardButton(age, callback_data=f"quiz:age:{age}"))
    kb.add(InlineKeyboardButton("Пропустить", callback_data="quiz:skip"))
    try:
        await call.message.edit_text(
            "🎯 <b>Подберём материалы!</b>\n\nСколько лет ребёнку?",
            reply_markup=kb, parse_mode="HTML"
        )
    except Exception:
        await call.message.answer(
            "🎯 <b>Подберём материалы!</b>\n\nСколько лет ребёнку?",
            reply_markup=kb, parse_mode="HTML"
        )


@dp.callback_query_handler(lambda c: c.data == "quiz:skip", state="*")
async def quiz_skip(call: types.CallbackQuery, state: FSMContext):
    await call.answer()
    await state.finish()
    try:
        await call.message.edit_text(START_TEXT, reply_markup=start_inline_kb(), parse_mode="HTML")
    except Exception:
        await call.message.answer(START_TEXT, reply_markup=start_inline_kb(), parse_mode="HTML")


@dp.callback_query_handler(lambda c: c.data.startswith("quiz:age:"), state=QuizState.age)
async def quiz_got_age(call: types.CallbackQuery, state: FSMContext):
    age = call.data.split("quiz:age:", 1)[1]
    await state.update_data(age=age)
    await state.set_state(QuizState.interest)
    kb = InlineKeyboardMarkup(row_width=1)
    for interest in INTERESTS:
        kb.add(InlineKeyboardButton(interest, callback_data=f"quiz:int:{interest}"))
    await call.answer()
    await call.message.edit_text(
        f"Возраст: <b>{age}</b>\n\nЧто интересует больше всего?",
        reply_markup=kb, parse_mode="HTML"
    )


@dp.callback_query_handler(lambda c: c.data.startswith("quiz:int:"), state=QuizState.interest)
async def quiz_got_interest(call: types.CallbackQuery, state: FSMContext):
    interest = call.data.split("quiz:int:", 1)[1]
    data = await state.get_data()
    age = data.get("age", "")
    await state.finish()

    loop = asyncio.get_running_loop()
    await loop.run_in_executor(None, _db_save_quiz, call.from_user.id, age, interest)

    all_products = await load_products()

    # Фильтруем по возрасту и интересу
    matched = _quiz_filter_products(all_products, age, interest)

    # Убираем уже купленные
    result = []
    for p in matched:
        if not await user_has_purchase(call.from_user.id, p["product_id"]):
            result.append(p)
            if len(result) >= 4:
                break

    # Если всё куплено — показываем без фильтра по покупкам (редкий случай)
    if not result:
        result = matched[:4]

    # Определяем точность подборки для текста заголовка
    q_min, q_max = AGE_RANGES.get(age, (0, 99))
    interest_tags = INTEREST_TAGS.get(interest, [])
    has_age_filtered = any(
        not (int(p.get("age_min", 0) or 0) == 0 and int(p.get("age_max", 99) or 99) == 99)
        for p in result
    )
    has_tag_filtered = interest_tags and any(
        any(t in (p.get("tags", "") or "") for t in interest_tags)
        for p in result
    )

    if has_age_filtered or has_tag_filtered:
        header = f"🎯 <b>Подборка для {age}</b> — {interest}\n\n✅ Нашли {len(result)} подходящих материала:"
    else:
        header = f"🎯 <b>Подборка для {age}</b> — {interest}\n\n⚠️ Точных совпадений нет — показываем похожие ({len(result)} шт.):"

    await call.answer()
    await call.message.edit_text(header, parse_mode="HTML")

    for p in result:
        cat_key = _cat_key(_to_str(p.get("category", "")))
        _cat_key_to_name[cat_key] = _to_str(p.get("category", ""))
        price_xtr = int(p.get("price_xtr", 0) or 0)
        price_str = "🎁 Бесплатно" if is_free_product(p) else f"⭐ {price_xtr} Stars"

        # Показываем возраст товара если задан
        p_min = int(p.get("age_min", 0) or 0)
        p_max = int(p.get("age_max", 99) or 99)
        age_hint = ""
        if p_min > 0 or p_max < 99:
            age_hint = f"\n👶 {p_min}–{p_max} лет" if p_min != p_max else f"\n👶 {p_min} лет"

        age_text = f"  <i>({p_min}–{p_max} лет)</i>" if (p_min > 0 or p_max < 99) else ""
        price_xtr_q = int(p.get("price_xtr", 0) or 0)
        price_text = "бесплатно" if is_free_product(p) else f"{price_xtr_q} ⭐"
        kb = InlineKeyboardMarkup()
        kb.add(InlineKeyboardButton(
            "Посмотреть →",
            callback_data=f"item:{p['product_id']}:{cat_key}"
        ))
        await call.message.answer(
            f"<b>{p['title']}</b>{age_text}  <i>({price_text})</i>",
            reply_markup=kb, parse_mode="HTML"
        )

    back_kb = InlineKeyboardMarkup()
    back_kb.add(InlineKeyboardButton("🏠 Главная", callback_data="open:start"))
    await call.message.answer("─────────────", reply_markup=back_kb)

# =========================
# ОПЛАТА КАРТОЙ РФ (ручная проверка)
# =========================

class CardPayState(StatesGroup):
    waiting_screenshot = State()
    waiting_deny_reason = State()


def _admin_approve_kb(user_id: int, product_id: str, order_key: str) -> InlineKeyboardMarkup:
    """Кнопки для админа: одобрить или отклонить оплату картой."""
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(
        InlineKeyboardButton(
            "✅ Одобрить и выдать файл",
            callback_data=f"cardapprove:{user_id}:{product_id}:{order_key}"
        ),
        InlineKeyboardButton(
            "❌ Отклонить",
            callback_data=f"carddeny:{user_id}:{product_id}:{order_key}"
        )
    )
    return kb


@dp.callback_query_handler(lambda c: c.data.startswith("paycard:"))
async def cb_pay_card(call: types.CallbackQuery, state: FSMContext):
    """Пользователь выбрал оплату картой — показываем реквизиты и просим скрин."""
    parts = call.data.split(":", 2)
    if len(parts) < 3:
        await call.answer("Некорректная кнопка.", show_alert=True)
        return

    pid = parts[1]
    category_key = parts[2]

    if not CARD_NUMBER:
        await call.answer("Оплата картой временно недоступна.", show_alert=True)
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

    # Сохраняем снимок товара как pending order
    order_key = f"card:{user.id}:{int(time.time())}"
    rub_price_val = int(product.get("price_rub", 0) or 0)
    rub_label = str(rub_price_val) if rub_price_val > 0 else (CARD_PRICE_RUB or "—")
    loop = asyncio.get_running_loop()
    await loop.run_in_executor(
        None, _db_save_pending_order,
        user.id, product, "card", rub_label, "RUB", order_key
    )

    # Сохраняем в FSM — понадобится когда придёт скриншот
    await state.update_data(
        card_pid=pid,
        card_order_key=order_key,
        card_category_key=category_key
    )
    await state.set_state(CardPayState.waiting_screenshot)

    rub_show = rub_price_val if rub_price_val > 0 else (int(CARD_PRICE_RUB) if CARD_PRICE_RUB.isdigit() else 0)
    price_line = f"\n💰 Сумма: <b>{rub_show} ₽</b>" if rub_show else ""
    card_formatted = " ".join(
        CARD_NUMBER[i:i+4] for i in range(0, len(CARD_NUMBER), 4)
    )

    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("❌ Отменить", callback_data=f"cardcancel:{order_key}"))

    await call.answer()
    await bot.send_message(
        call.message.chat.id,
        f"💳 <b>Оплата картой</b>{price_line}\n\n"
        f"Переведите на карту Юмани:\n"
        f"<code>{card_formatted}</code>\n\n"
        f"После оплаты отправьте скриншот подтверждения в этот чат — "
        f"мы проверим и пришлём ваш материал.",
        reply_markup=kb,
        parse_mode="HTML"
    )


@dp.callback_query_handler(lambda c: c.data.startswith("cardcancel:"), state=CardPayState.waiting_screenshot)
async def cb_card_cancel(call: types.CallbackQuery, state: FSMContext):
    """Пользователь отменил оплату картой."""
    order_key = call.data.split("cardcancel:", 1)[1]
    data = await state.get_data()
    await state.finish()

    loop = asyncio.get_running_loop()
    await loop.run_in_executor(None, _db_delete_pending_order, "card", order_key, call.from_user.id)

    await call.answer("Отменено.")
    try:
        await call.message.delete()
    except Exception:
        await call.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup())


@dp.message_handler(
    content_types=[types.ContentType.PHOTO, types.ContentType.DOCUMENT],
    state=CardPayState.waiting_screenshot
)
async def cb_card_screenshot(message: types.Message, state: FSMContext):
    """Пользователь прислал скриншот — пересылаем админу с кнопками одобрения."""
    data = await state.get_data()
    pid = data.get("card_pid")
    order_key = data.get("card_order_key", "")

    if not pid or not order_key:
        await state.finish()
        await message.answer("Что-то пошло не так. Попробуйте снова через /start.")
        return

    # Получаем товар из pending_order (снимок)
    loop = asyncio.get_running_loop()
    pending = await loop.run_in_executor(
        None, _db_get_pending_order, "card", order_key, message.from_user.id
    )
    if not pending:
        # Fallback
        _all_products = await load_products()
        product = next((p for p in _all_products if p["product_id"] == pid), None)
        product_title = product["title"] if product else pid
    else:
        product_title = pending.get("product_title", pid)

    user = message.from_user
    username = f"@{user.username}" if user.username else "нет"
    price_label = pending.get("expected_amount", "—") if pending else "—"
    price_line = f" ({price_label} ₽)" if price_label and price_label != "—" else ""

    admin_caption = (
        f"💳 <b>Оплата картой — скриншот</b>\n\n"
        f"📄 Товар: <b>{product_title}</b>{price_line}\n"
        f"👤 Пользователь: {user.full_name}\n"
        f"ID: <code>{user.id}</code>  Username: {username}\n\n"
        f"Проверьте скриншот и подтвердите или отклоните оплату."
    )

    try:
        if message.photo:
            await bot.send_photo(
                ADMIN_CHAT_ID,
                message.photo[-1].file_id,
                caption=admin_caption,
                reply_markup=_admin_approve_kb(user.id, pid, order_key),
                parse_mode="HTML"
            )
        else:
            await bot.send_document(
                ADMIN_CHAT_ID,
                message.document.file_id,
                caption=admin_caption,
                reply_markup=_admin_approve_kb(user.id, pid, order_key),
                parse_mode="HTML"
            )
    except Exception as e:
        logger.exception("Не удалось переслать скриншот админу: %s", e)
        await message.answer(
            "Не удалось отправить скриншот на проверку. Напишите в поддержку через /help."
        )
        return

    await state.finish()
    await message.answer(
        "✅ Скриншот получен. Платёж проверяется — вы получите PDF как только оплата будет подтверждена.",
        reply_markup=InlineKeyboardMarkup().add(
            InlineKeyboardButton("🏠 Главная", callback_data="open:start")
        )
    )


@dp.callback_query_handler(lambda c: c.data.startswith("cardapprove:"), user_id=ADMIN_IDS)
async def cb_card_approve(call: types.CallbackQuery):
    """Админ одобрил оплату — выдаём файл пользователю."""
    parts = call.data.split(":")
    if len(parts) < 4:
        await call.answer("Некорректные данные.", show_alert=True)
        return

    target_user_id = int(parts[1])
    pid = parts[2]
    order_key = ":".join(parts[3:])  # order_key может содержать ":"

    loop = asyncio.get_running_loop()
    pending = await loop.run_in_executor(
        None, _db_get_pending_order, "card", order_key, target_user_id
    )

    if pending:
        product = {
            "product_id": pending["product_id"],
            "title": pending.get("product_title", ""),
            "file_id": pending["file_id"],
            "price_xtr": 0,
        }
    else:
        logger.warning("cardapprove: pending не найден для user=%s order=%s", target_user_id, order_key)
        _all_products = await load_products()
        product = next((p for p in _all_products if p["product_id"] == pid), None)
        if not product:
            await call.answer("Товар не найден. Проверьте вручную.", show_alert=True)
            return

    # Получаем реальные данные пользователя через Telegram API
    class _FakeUser:
        def __init__(self, uid, username=None, full_name=None):
            self.id = uid
            self.username = username
            self.full_name = full_name or f"user_{uid}"

    try:
        chat_info = await bot.get_chat(target_user_id)
        real_username = chat_info.username or None
        real_full_name = chat_info.full_name or f"user_{target_user_id}"
    except Exception:
        real_username = None
        real_full_name = f"user_{target_user_id}"

    fake_user = _FakeUser(target_user_id, username=real_username, full_name=real_full_name)

    ok = await grant_product_to_user(
        chat_id=target_user_id,
        user=fake_user,
        product=product,
        price_label="Карта РФ"
    )

    if ok:
        # Удаляем pending
        await loop.run_in_executor(
            None, _db_delete_pending_order, "card", order_key, target_user_id
        )
        # Уведомляем пользователя
        try:
            await bot.send_message(
                target_user_id,
                "✅ <b>Оплата подтверждена!</b>\n\nВаш материал отправлен выше 👆",
                parse_mode="HTML"
            )
        except Exception:
            pass

        await call.answer("✅ Одобрено, файл выдан!")
        # Редактируем сообщение со скриншотом — убираем кнопки, добавляем статус
        try:
            original_caption = call.message.caption or ""
            await call.message.edit_caption(
                caption=original_caption + "\n\n✅ <b>ОДОБРЕНО</b>",
                reply_markup=InlineKeyboardMarkup(),
                parse_mode="HTML"
            )
        except Exception:
            pass
    else:
        await call.answer("❌ Ошибка выдачи файла. Попробуйте отправить вручную.", show_alert=True)


@dp.callback_query_handler(lambda c: c.data.startswith("carddeny:"), user_id=ADMIN_IDS)
async def cb_card_deny(call: types.CallbackQuery, state: FSMContext):
    """Админ нажал Отклонить — просим ввести причину."""
    parts = call.data.split(":")
    if len(parts) < 4:
        await call.answer("Некорректные данные.", show_alert=True)
        return

    target_user_id = int(parts[1])
    pid = parts[2]
    order_key = ":".join(parts[3:])

    # Сохраняем контекст в FSM — понадобится когда придёт причина
    await state.update_data(
        deny_user_id=target_user_id,
        deny_pid=pid,
        deny_order_key=order_key,
        deny_message_id=call.message.message_id,
        deny_caption=call.message.caption or ""
    )
    await state.set_state(CardPayState.waiting_deny_reason)
    await call.answer()

    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Пропустить (без причины)", callback_data="carddeny_skip"))
    await bot.send_message(
        call.message.chat.id,
        "Напишите причину отклонения — она будет отправлена пользователю.\n"
        "Или нажмите кнопку чтобы отклонить без объяснений:",
        reply_markup=kb
    )


async def _execute_card_deny(
    admin_chat_id: int,
    target_user_id: int,
    pid: str,
    order_key: str,
    original_message_id: int,
    original_caption: str,
    reason: str = ""
) -> None:
    """Выполняет отклонение: удаляет pending, уведомляет пользователя, обновляет скриншот."""
    loop = asyncio.get_running_loop()
    await loop.run_in_executor(
        None, _db_delete_pending_order, "card", order_key, target_user_id
    )

    if reason:
        user_text = (
            "❌ <b>Оплата не подтверждена.</b>\n\n"
            f"Причина: {reason}\n\n"
            "Если остались вопросы — напишите в поддержку: @" + AUTHOR_USERNAME
        )
        deny_label = f"❌ ОТКЛОНЕНО\nПричина: {reason}"
    else:
        user_text = (
            "❌ <b>Оплата не подтверждена.</b>\n\n"
            "Скриншот не прошёл проверку. Если вы уверены что оплатили — "
            "напишите в поддержку: @" + AUTHOR_USERNAME
        )
        deny_label = "❌ ОТКЛОНЕНО"

    try:
        await bot.send_message(target_user_id, user_text, parse_mode="HTML")
    except Exception:
        pass

    try:
        await bot.edit_message_caption(
            chat_id=admin_chat_id,
            message_id=original_message_id,
            caption=original_caption + f"\n\n{deny_label}",
            reply_markup=InlineKeyboardMarkup(),
            parse_mode="HTML"
        )
    except Exception:
        pass


@dp.message_handler(user_id=ADMIN_IDS, state=CardPayState.waiting_deny_reason)
async def cb_card_deny_reason(message: types.Message, state: FSMContext):
    """Админ ввёл причину отклонения текстом."""
    data = await state.get_data()
    await state.finish()

    reason = message.text.strip()
    await _execute_card_deny(
        admin_chat_id=message.chat.id,
        target_user_id=data["deny_user_id"],
        pid=data["deny_pid"],
        order_key=data["deny_order_key"],
        original_message_id=data["deny_message_id"],
        original_caption=data["deny_caption"],
        reason=reason
    )
    await message.answer("Отклонено, пользователь уведомлён с причиной.")


@dp.callback_query_handler(lambda c: c.data == "carddeny_skip", user_id=ADMIN_IDS,
                            state=CardPayState.waiting_deny_reason)
async def cb_card_deny_skip(call: types.CallbackQuery, state: FSMContext):
    """Админ пропустил ввод причины."""
    data = await state.get_data()
    await state.finish()
    await call.answer()

    await _execute_card_deny(
        admin_chat_id=call.message.chat.id,
        target_user_id=data["deny_user_id"],
        pid=data["deny_pid"],
        order_key=data["deny_order_key"],
        original_message_id=data["deny_message_id"],
        original_caption=data["deny_caption"],
        reason=""
    )
    try:
        await call.message.delete()
    except Exception:
        pass
    await bot.send_message(call.message.chat.id, "Отклонено без причины, пользователь уведомлён.")



# =========================
# ОТЗЫВЫ
# =========================

class ReviewState(StatesGroup):
    comment = State()


async def send_review_requests():
    loop = asyncio.get_running_loop()
    requests_list = await loop.run_in_executor(None, _db_get_pending_review_requests)
    for req in requests_list:
        try:
            user_id = int(req["user_id"])
            product_id = req["product_id"]
            has = await loop.run_in_executor(None, _db_has_review, user_id, product_id)
            if has:
                await loop.run_in_executor(None, _db_mark_review_request_sent, req["id"])
                continue
            prod = await loop.run_in_executor(None, _db_get_product, product_id)
            title = prod["title"] if prod else product_id
            kb = InlineKeyboardMarkup(row_width=1)
            labels = ["⭐ 1 — плохо", "⭐⭐ 2 — так себе", "⭐⭐⭐ 3 — нормально", "⭐⭐⭐⭐ 4 — хорошо", "⭐⭐⭐⭐⭐ 5 — отлично"]
            for i in range(1, 6):
                kb.add(InlineKeyboardButton(
                    labels[i - 1],
                    callback_data=f"rev:rate:{product_id}:{req['id']}:{i}"
                ))
            kb.add(InlineKeyboardButton("Пропустить", callback_data=f"rev:skip:{req['id']}"))
            await bot.send_message(
                user_id,
                f"Как вам материал <b>{title}</b>?\n\nПоставьте оценку от 1 до 5:",
                reply_markup=kb, parse_mode="HTML"
            )
            await loop.run_in_executor(None, _db_mark_review_request_sent, req["id"])
        except Exception as e:
            logger.warning("send_review_request error: %s", e)
            try:
                await loop.run_in_executor(None, _db_mark_review_request_sent, req["id"])
            except Exception:
                pass


@dp.callback_query_handler(lambda c: c.data.startswith("rev:skip:"))
async def cb_review_skip(call: types.CallbackQuery):
    await call.answer("Хорошо!")
    try:
        await call.message.delete()
    except Exception:
        await call.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup())


@dp.callback_query_handler(lambda c: c.data.startswith("rev:rate:"), state="*")
async def cb_review_rate(call: types.CallbackQuery, state: FSMContext):
    parts = call.data.split(":")
    product_id = parts[2]
    rating = int(parts[4])
    await state.update_data(rev_product_id=product_id, rev_rating=rating)
    await state.set_state(ReviewState.comment)
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Пропустить", callback_data=f"rev:nc:{product_id}:{rating}"))
    await call.answer()
    stars_label = ["", "1 ★", "2 ★★", "3 ★★★", "4 ★★★★", "5 ★★★★★"]
    await call.message.edit_text(
        f"Оценка: <b>{stars_label[rating]}</b>\n\nНапишите комментарий (или нажмите пропустить):",
        reply_markup=kb, parse_mode="HTML"
    )


@dp.callback_query_handler(lambda c: c.data.startswith("rev:nc:"), state=ReviewState.comment)
async def cb_review_no_comment(call: types.CallbackQuery, state: FSMContext):
    parts = call.data.split(":")
    product_id, rating = parts[2], int(parts[3])
    await _finalize_review(call.from_user, product_id, rating, "")
    await state.finish()
    await call.answer("Спасибо за оценку!")
    try:
        await call.message.delete()
    except Exception:
        pass


@dp.message_handler(state=ReviewState.comment)
async def cb_review_comment(message: types.Message, state: FSMContext):
    data = await state.get_data()
    await _finalize_review(
        message.from_user,
        data.get("rev_product_id", ""),
        data.get("rev_rating", 5),
        message.text.strip()
    )
    await state.finish()
    await message.answer("Спасибо за отзыв!")


async def _finalize_review(user, product_id: str, rating: int, comment: str):
    loop = asyncio.get_running_loop()
    prod = await loop.run_in_executor(None, _db_get_product, product_id)
    title = prod["title"] if prod else product_id
    await loop.run_in_executor(None, _db_add_review, user, product_id, title, rating, comment)


@dp.callback_query_handler(lambda c: c.data.startswith("rev:del:"))
async def cb_review_delete(call: types.CallbackQuery):
    review_id = int(call.data.split(":")[2])
    user = call.from_user
    loop = asyncio.get_running_loop()
    review = await loop.run_in_executor(None, _db_get_review_by_id, review_id)
    if not review:
        await call.answer("Отзыв не найден.", show_alert=True)
        return
    if str(user.id) != review.get("user_id") and user.id not in ADMIN_IDS:
        await call.answer("Нет прав на удаление.", show_alert=True)
        return
    await loop.run_in_executor(None, _db_delete_review, review_id)
    await call.answer("Отзыв удалён.")
    try:
        await call.message.delete()
    except Exception:
        pass


async def _get_reviews_text(product_id: str) -> str:
    """FIX: Единственное определение — дублирование устранено."""
    loop = asyncio.get_running_loop()
    reviews = await loop.run_in_executor(None, _db_get_reviews, product_id)
    if not reviews:
        return ""
    avg = sum(r["rating"] for r in reviews) / len(reviews)
    lines = [f"\n{'⭐' * round(avg)} <b>{avg:.1f}</b> ({len(reviews)} отзывов)"]
    for r in reviews[:2]:
        name = (r.get("full_name") or "Покупатель").split()[0]
        comment = r.get("comment", "")
        r_stars = "⭐" * r["rating"]
        line = f"  {r_stars} {name}"
        if comment:
            line += f": {comment[:50]}"
        lines.append(line)
    return "\n".join(lines)


# =========================
# ПОХОЖИЕ ТОВАРЫ ПОСЛЕ ПОКУПКИ
# =========================

async def _safe_suggest_more(chat_id: int, user_id: int, product: Dict[str, Any]) -> None:
    """FIX: обёртка с обработкой исключений для фоновой задачи."""
    try:
        await _suggest_more(chat_id, user_id, product)
    except Exception as e:
        logger.warning("_safe_suggest_more error: %s", e)


async def _suggest_more(chat_id: int, user_id: int, product: Dict[str, Any]) -> None:
    await asyncio.sleep(1)
    all_products = await load_products()
    category = product.get("category", "")
    suggestions = []
    for p in all_products:
        if (p.get("category") == category
                and p["product_id"] != product["product_id"]
                and not await user_has_purchase(user_id, p["product_id"])):
            suggestions.append(p)
            if len(suggestions) >= 3:
                break
    if not suggestions:
        return
    kb = InlineKeyboardMarkup(row_width=1)
    for p in suggestions:
        cat_key = _cat_key(_to_str(p.get("category", "")))
        _cat_key_to_name[cat_key] = _to_str(p.get("category", ""))
        price_xtr = int(p.get("price_xtr", 0) or 0)
        kb.add(InlineKeyboardButton(
            _product_btn_label(p),
            callback_data=f"item:{p['product_id']}:{cat_key}"
        ))
    await bot.send_message(
        chat_id,
        "🎯 <b>Попробуйте ещё из этой серии:</b>",
        reply_markup=kb,
        parse_mode="HTML"
    )


# =========================
# WEBHOOK / POLLING
# =========================

WEBHOOK_HOST = os.getenv("RAILWAY_PUBLIC_DOMAIN", "").strip()
WEBHOOK_PATH = f"/webhook/{BOT_TOKEN}"
WEBHOOK_URL = f"https://{WEBHOOK_HOST}{WEBHOOK_PATH}" if WEBHOOK_HOST else ""
WEBAPP_PORT = int(os.getenv("PORT", 8080))


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
    await _setup_bot_commands()
    asyncio.create_task(_review_request_loop())
    if WEBHOOK_URL:
        await bot.set_webhook(WEBHOOK_URL)
        logger.info("Webhook set: %s", WEBHOOK_URL)
    else:
        logger.info("No RAILWAY_PUBLIC_DOMAIN — using polling")


async def _setup_bot_commands():
    from aiogram.types import BotCommand, BotCommandScopeDefault, BotCommandScopeChat

    user_commands = [
        BotCommand("start", "🏠 Главная"),
        BotCommand("help", "❓ Поддержка"),
    ]
    await bot.set_my_commands(user_commands, scope=BotCommandScopeDefault())

    admin_commands = [
        BotCommand("start", "🏠 Главная"),
        BotCommand("admin", "🛠 Панель управления"),
        BotCommand("refresh", "🔄 Сбросить кеш"),
        BotCommand("help", "❓ Поддержка"),
        BotCommand("cancel", "❌ Отменить действие"),
        BotCommand("testreview", "🧪 Тест запроса отзыва"),
        BotCommand("reviews", "💬 Просмотр и удаление отзывов"),
        BotCommand("cardtest", "🔍 Диагностика карты"),
    ]
    for admin_id in ADMIN_IDS:
        try:
            await bot.set_my_commands(
                admin_commands,
                scope=BotCommandScopeChat(chat_id=admin_id)
            )
        except Exception as e:
            logger.warning("Не удалось установить команды для админа %s: %s", admin_id, e)

    logger.info("Bot commands configured")


async def on_shutdown(dp):
    if WEBHOOK_URL:
        await bot.delete_webhook()


if __name__ == "__main__":
    if WEBHOOK_URL:
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
        _db_cleanup_pending_orders()
        executor.start_polling(dp, skip_updates=True, on_startup=on_startup)
