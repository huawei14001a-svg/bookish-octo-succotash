#!/usr/bin/env python3
"""
💹 VRF Exchange Bot — Telegram-биржа токена #VRF
Покупка · Продажа · Стейкинг (гибкий и с фиксированным сроком)
Deploy: Railway.app | Set BOT_TOKEN env var
Start command: python vrf_exchange_bot.py

Requirements (requirements.txt):
    python-telegram-bot==21.6
    aiosqlite
    matplotlib   # опционально — для /chart
    aiohttp      # публичный REST API для сторонних разработчиков

Env vars:
    BOT_TOKEN   — токен бота (обязательно)
    DB_PATH     — путь к SQLite базе (по умолчанию vrf_exchange.db)
    ADMIN_IDS   — список ID администраторов через запятую (опционально)
    PORT        — порт для REST API (Railway подставляет автоматически)
    API_CORS_ORIGIN — Access-Control-Allow-Origin для API (по умолчанию "*")

Публичный REST API (для внешних сайтов/приложений) поднимается на
0.0.0.0:$PORT и живёт независимо от long-polling бота. Документация
для разработчиков — см. API_DOCS.md.
"""

import asyncio
import base64
import hashlib
import io
import json
import logging
import math
import os
import random
import secrets
import threading
import time
import uuid
from datetime import datetime, timedelta
from typing import Optional, Tuple

import aiosqlite
from telegram import (
    ForceReply,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    ReplyParameters,
    Update,
)
from telegram.constants import ParseMode
from telegram.error import TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)


# ══════════════════════════════════════════════════════
#  STYLED BUTTON — InlineKeyboardButton + style field
# ══════════════════════════════════════════════════════
# Telegram Bot API supports: style="success" 🟢  "danger" 🔴  "primary" 🔵

class SBtn(InlineKeyboardButton):
    """InlineKeyboardButton with the official Telegram `style` field."""
    _cache: dict = {}

    def __init__(self, text: str, *, style: str = None, **kwargs):
        super().__init__(text, **kwargs)
        if style:
            SBtn._cache[id(self)] = style

    def to_dict(self, **kwargs) -> dict:
        d = super().to_dict(**kwargs)
        s = SBtn._cache.get(id(self))
        if s:
            d["style"] = s
        return d

    def __del__(self) -> None:
        SBtn._cache.pop(id(self), None)


# ══════════════════════════════════════════════════════
#                       CONFIG
# ══════════════════════════════════════════════════════

BOT_TOKEN: str = os.getenv("BOT_TOKEN", "")
DB_PATH:   str = os.getenv("DB_PATH", "vrf_exchange.db")
ADMIN_IDS: list = [int(x) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip().isdigit()]

STARTING_USD   = 1000.0
STARTING_VRF   = 0.0
STARTING_SCAM  = 100.0

PRICE_START        = 1.00     # USD за 1 VRF
PRICE_TICK_SECONDS = 45
PRICE_VOLATILITY   = 0.018    # шум за тик
FAIR_DRIFT_CHANCE  = 0.10     # шанс сдвига "справедливой" цены за тик
FAIR_DRIFT_PCT     = 0.03
MEAN_REVERSION      = 0.06
PRICE_MIN, PRICE_MAX = 0.01, 1_000_000.0

TRADE_FEE_PCT = 0.01   # 1% комиссия на сделку

BUY_PRESETS_USD  = [10, 50, 100, 500, 1000]
SELL_PRESETS_VRF = [10, 50, 100, 500, 1000]
STAKE_PRESETS_VRF = [100, 500, 1000, 5000, 10000]

STAKE_TIERS = {
    "flex": {"label": "🔓 Гибкий",  "apr": 0.08, "lock_days": 0,  "penalty": 0.0},
    "7d":   {"label": "📅 7 дней",  "apr": 0.15, "lock_days": 7,  "penalty": 0.10},
    "14d":  {"label": "📅 14 дней", "apr": 0.22, "lock_days": 14, "penalty": 0.12},
    "30d":  {"label": "📅 30 дней", "apr": 0.35, "lock_days": 30, "penalty": 0.15},
}

# ── Public REST API ────────────────────────────────────
API_PORT         = int(os.getenv("PORT", "8080"))
API_CORS_ORIGIN  = os.getenv("API_CORS_ORIGIN", "*")
API_KEY_PREFIX   = "vrf_live_"
API_RATE_LIMIT   = 120     # запросов
API_RATE_WINDOW  = 60      # секунд, скользящее окно на ключ/IP

E_UP, E_DOWN, E_FLAT = "🟢", "🔴", "⚪️"
E_COIN, E_USD, E_LOCK = "💎", "💵", "🔒"

logging.basicConfig(
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    level=logging.INFO,
)
log = logging.getLogger("vrf-exchange")

# ── In-memory market state ────────────────────────────
market = {
    "price": PRICE_START,
    "fair":  PRICE_START,
    "prev_price": PRICE_START,
}
market_lock = asyncio.Lock()

# ── Pending custom-amount input (ForceReply flow) ─────
pending_input: dict = {}   # key: (cid, uid) -> {"kind":..., "tier":..., "expires":...}


# ══════════════════════════════════════════════════════
#                    HELPERS
# ══════════════════════════════════════════════════════

def _now() -> str:
    return datetime.now().isoformat()


def mention(uid: int, name: str) -> str:
    safe = str(name).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    return f'<a href="tg://user?id={uid}">{safe}</a>'


def fmt(n: float) -> str:
    if n >= 1_000_000: return f"{n/1_000_000:.2f}M"
    if n >= 10_000:    return f"{n/1_000:.2f}K"
    if n == int(n):    return f"{int(n):,}".replace(",", " ")
    return f"{n:,.2f}".replace(",", " ")


def fmt_price(p: float) -> str:
    if p >= 100: return f"{p:,.2f}"
    if p >= 1:   return f"{p:,.4f}"
    return f"{p:.6f}"


def fmt_scam(n: float) -> str:
    """Format a SCAM amount trimmed of trailing zeros, comma as decimal separator."""
    s = f"{n:.6f}".rstrip("0").rstrip(".")
    if s in ("", "-"):
        s = "0"
    return s.replace(".", ",")


def fmt_cd(seconds: int) -> str:
    seconds = max(0, int(seconds))
    d, r = divmod(seconds, 86400)
    h, r = divmod(r, 3600)
    m, s = divmod(r, 60)
    if d: return f"{d}д {h}ч"
    if h: return f"{h}ч {m}м"
    if m: return f"{m}м {s}с"
    return f"{s}с"


async def is_admin(uid: int) -> bool:
    return uid in ADMIN_IDS


# ══════════════════════════════════════════════════════
#         RICH MESSAGE HELPER  📄  (sendRichMessage + fallback)
# ══════════════════════════════════════════════════════

async def send_rich(
    bot,
    chat_id: int,
    markdown: str = "",
    fallback_html: str = "",
    reply_to_id: int = None,
    reply_markup=None,
    html: str = "",
) -> bool:
    fb_text = fallback_html or html or markdown
    rich_msg: dict = {"html": html} if html else {"markdown": markdown or " "}
    kw: dict = {"chat_id": chat_id, "rich_message": rich_msg}
    if reply_to_id:
        kw["reply_parameters"] = {"message_id": reply_to_id}
    if reply_markup:
        try:
            kw["reply_markup"] = reply_markup.to_dict()
        except Exception:
            pass
    try:
        await bot.do_api_request("sendRichMessage", api_kwargs=kw)
        return True
    except Exception:
        pass

    msg_kw: dict = {"chat_id": chat_id, "text": fb_text, "parse_mode": ParseMode.HTML}
    if reply_to_id:
        msg_kw["reply_parameters"] = {"message_id": reply_to_id}
    if reply_markup:
        msg_kw["reply_markup"] = reply_markup
    try:
        await bot.send_message(**msg_kw)
        return False
    except Exception:
        pass

    import re as _re
    plain = _re.sub(r"<[^>]+>", "", fb_text)[:4096].strip()
    if plain:
        try:
            p_kw: dict = {"chat_id": chat_id, "text": plain}
            if reply_markup:
                p_kw["reply_markup"] = reply_markup
            await bot.send_message(**p_kw)
        except Exception:
            pass
    return False


# ══════════════════════════════════════════════════════
#                    DATABASE
# ══════════════════════════════════════════════════════

async def db_init() -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.executescript(f"""
            CREATE TABLE IF NOT EXISTS users (
                user_id     INTEGER PRIMARY KEY,
                username    TEXT DEFAULT '',
                first_name  TEXT DEFAULT '',
                usd         REAL DEFAULT {STARTING_USD},
                vrf         REAL DEFAULT {STARTING_VRF},
                scam        REAL DEFAULT {STARTING_SCAM},
                created_at  TEXT
            );

            CREATE TABLE IF NOT EXISTS scam_transfers (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                from_id     INTEGER NOT NULL,
                to_id       INTEGER NOT NULL,
                amount      REAL NOT NULL,
                ts          TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS stakes (
                id            INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id       INTEGER NOT NULL,
                tier          TEXT NOT NULL,
                amount        REAL NOT NULL,
                apr           REAL NOT NULL,
                lock_days     INTEGER NOT NULL,
                penalty       REAL NOT NULL,
                start_ts      TEXT NOT NULL,
                last_claim_ts TEXT NOT NULL,
                status        TEXT DEFAULT 'active'
            );

            CREATE TABLE IF NOT EXISTS price_log (
                id    INTEGER PRIMARY KEY AUTOINCREMENT,
                ts    TEXT NOT NULL,
                price REAL NOT NULL
            );

            CREATE TABLE IF NOT EXISTS trades (
                id      INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                side    TEXT NOT NULL,
                vrf     REAL NOT NULL,
                usd     REAL NOT NULL,
                price   REAL NOT NULL,
                ts      TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS api_keys (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id     INTEGER NOT NULL,
                key_hash    TEXT NOT NULL UNIQUE,
                key_prefix  TEXT NOT NULL,
                label       TEXT DEFAULT '',
                created_at  TEXT NOT NULL,
                last_used_at TEXT DEFAULT NULL,
                revoked     INTEGER DEFAULT 0
            );
        """)
        await db.commit()
        # ── Migration: add `scam` column to pre-existing DBs (safe no-op if present) ──
        try:
            await db.execute(f"ALTER TABLE users ADD COLUMN scam REAL DEFAULT {STARTING_SCAM}")
            await db.commit()
        except Exception:
            pass  # Column already exists
    log.info("Database initialised at %s", DB_PATH)


async def db_ensure_user(uid: int, username: str, first_name: str) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            """INSERT INTO users (user_id, username, first_name, usd, vrf, scam, created_at)
               VALUES (?,?,?,?,?,?,?)
               ON CONFLICT(user_id) DO UPDATE SET
                 username=excluded.username, first_name=excluded.first_name""",
            (uid, username or "", first_name or "", STARTING_USD, STARTING_VRF, STARTING_SCAM, _now()),
        )
        await db.commit()


async def db_get_user(uid: int) -> Optional[dict]:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        async with db.execute("SELECT * FROM users WHERE user_id=?", (uid,)) as cur:
            row = await cur.fetchone()
            return dict(row) if row else None


async def db_set_balances(uid: int, usd: float = None, vrf: float = None, scam: float = None) -> None:
    sets, args = [], []
    if usd is not None:
        sets.append("usd=?"); args.append(max(0.0, usd))
    if vrf is not None:
        sets.append("vrf=?"); args.append(max(0.0, vrf))
    if scam is not None:
        sets.append("scam=?"); args.append(max(0.0, scam))
    if not sets:
        return
    args.append(uid)
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(f"UPDATE users SET {', '.join(sets)} WHERE user_id=?", args)
        await db.commit()


async def db_add_usd(uid: int, amount: float) -> float:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("UPDATE users SET usd=usd+? WHERE user_id=?", (amount, uid))
        await db.commit()
        async with db.execute("SELECT usd FROM users WHERE user_id=?", (uid,)) as cur:
            row = await cur.fetchone()
            return row[0] if row else 0.0


async def db_add_scam(uid: int, amount: float) -> float:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("UPDATE users SET scam=scam+? WHERE user_id=?", (amount, uid))
        await db.commit()
        async with db.execute("SELECT scam FROM users WHERE user_id=?", (uid,)) as cur:
            row = await cur.fetchone()
            return row[0] if row else 0.0


async def db_log_scam_transfer(from_id: int, to_id: int, amount: float) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO scam_transfers (from_id, to_id, amount, ts) VALUES (?,?,?,?)",
            (from_id, to_id, amount, _now()),
        )
        await db.commit()


async def db_add_vrf(uid: int, amount: float) -> float:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("UPDATE users SET vrf=vrf+? WHERE user_id=?", (amount, uid))
        await db.commit()
        async with db.execute("SELECT vrf FROM users WHERE user_id=?", (uid,)) as cur:
            row = await cur.fetchone()
            return row[0] if row else 0.0


async def db_log_trade(uid: int, side: str, vrf: float, usd: float, price: float) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO trades (user_id, side, vrf, usd, price, ts) VALUES (?,?,?,?,?,?)",
            (uid, side, vrf, usd, price, _now()),
        )
        await db.commit()


async def db_log_price(price: float) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("INSERT INTO price_log (ts, price) VALUES (?,?)", (_now(), price))
        await db.commit()


async def db_price_range(hours: int) -> Tuple[Optional[float], Optional[float]]:
    since = (datetime.now() - timedelta(hours=hours)).isoformat()
    async with aiosqlite.connect(DB_PATH) as db:
        async with db.execute(
            "SELECT MIN(price), MAX(price) FROM price_log WHERE ts>=?", (since,)
        ) as cur:
            row = await cur.fetchone()
            return (row[0], row[1]) if row else (None, None)


async def db_price_at(hours_ago: float) -> Optional[float]:
    target = (datetime.now() - timedelta(hours=hours_ago)).isoformat()
    async with aiosqlite.connect(DB_PATH) as db:
        async with db.execute(
            "SELECT price FROM price_log WHERE ts<=? ORDER BY ts DESC LIMIT 1", (target,)
        ) as cur:
            row = await cur.fetchone()
            if row:
                return row[0]
        async with db.execute("SELECT price FROM price_log ORDER BY ts ASC LIMIT 1") as cur:
            row = await cur.fetchone()
            return row[0] if row else None


async def db_price_history(hours: int) -> list:
    since = (datetime.now() - timedelta(hours=hours)).isoformat()
    async with aiosqlite.connect(DB_PATH) as db:
        async with db.execute(
            "SELECT ts, price FROM price_log WHERE ts>=? ORDER BY ts ASC", (since,)
        ) as cur:
            return await cur.fetchall()


# ── Stakes ─────────────────────────────────────────────

async def db_create_stake(uid: int, tier_key: str, amount: float) -> int:
    t = STAKE_TIERS[tier_key]
    now = _now()
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute(
            """INSERT INTO stakes (user_id, tier, amount, apr, lock_days, penalty, start_ts, last_claim_ts, status)
               VALUES (?,?,?,?,?,?,?,?, 'active')""",
            (uid, tier_key, amount, t["apr"], t["lock_days"], t["penalty"], now, now),
        )
        await db.commit()
        return cur.lastrowid


async def db_get_stake(stake_id: int) -> Optional[dict]:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        async with db.execute("SELECT * FROM stakes WHERE id=?", (stake_id,)) as cur:
            row = await cur.fetchone()
            return dict(row) if row else None


async def db_get_user_stakes(uid: int) -> list:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(
            "SELECT * FROM stakes WHERE user_id=? AND status='active' ORDER BY start_ts DESC", (uid,)
        ) as cur:
            return [dict(r) for r in await cur.fetchall()]


async def db_close_stake(stake_id: int, status: str, last_claim_ts: str = None) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        if last_claim_ts:
            await db.execute(
                "UPDATE stakes SET status=?, last_claim_ts=? WHERE id=?",
                (status, last_claim_ts, stake_id),
            )
        else:
            await db.execute("UPDATE stakes SET status=? WHERE id=?", (status, stake_id))
        await db.commit()


async def db_touch_stake(stake_id: int, ts: str) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("UPDATE stakes SET last_claim_ts=? WHERE id=?", (ts, stake_id))
        await db.commit()


def stake_accrued(stake: dict, upto: datetime = None) -> float:
    """Simple interest accrued since last_claim_ts, capped at lock period for fixed tiers."""
    upto = upto or datetime.now()
    start   = datetime.fromisoformat(stake["last_claim_ts"])
    matured = datetime.fromisoformat(stake["start_ts"]) + timedelta(days=stake["lock_days"])
    end     = min(upto, matured) if stake["lock_days"] > 0 else upto
    elapsed = max(0.0, (end - start).total_seconds())
    years   = elapsed / (365 * 86400)
    return stake["amount"] * stake["apr"] * years


def stake_is_matured(stake: dict) -> bool:
    if stake["lock_days"] <= 0:
        return True
    matured = datetime.fromisoformat(stake["start_ts"]) + timedelta(days=stake["lock_days"])
    return datetime.now() >= matured


def stake_time_left(stake: dict) -> int:
    if stake["lock_days"] <= 0:
        return 0
    matured = datetime.fromisoformat(stake["start_ts"]) + timedelta(days=stake["lock_days"])
    return int((matured - datetime.now()).total_seconds())


# ══════════════════════════════════════════════════════
#              API KEYS  🔑  (для внешних разработчиков)
# ══════════════════════════════════════════════════════

def _hash_key(raw_key: str) -> str:
    return hashlib.sha256(raw_key.encode()).hexdigest()


def generate_api_key() -> Tuple[str, str]:
    """Returns (raw_key_to_show_once, key_hash_to_store)."""
    raw = API_KEY_PREFIX + secrets.token_urlsafe(32)
    return raw, _hash_key(raw)


async def db_create_api_key(uid: int, label: str = "") -> Tuple[int, str]:
    raw, key_hash = generate_api_key()
    prefix = raw[:len(API_KEY_PREFIX) + 6] + "…"
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute(
            """INSERT INTO api_keys (user_id, key_hash, key_prefix, label, created_at)
               VALUES (?,?,?,?,?)""",
            (uid, key_hash, prefix, label, _now()),
        )
        await db.commit()
        return cur.lastrowid, raw


async def db_get_user_from_key(raw_key: str) -> Optional[dict]:
    """Validate a raw API key and return the owning user's row, or None."""
    if not raw_key or not raw_key.startswith(API_KEY_PREFIX):
        return None
    key_hash = _hash_key(raw_key)
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(
            "SELECT * FROM api_keys WHERE key_hash=? AND revoked=0", (key_hash,)
        ) as cur:
            krow = await cur.fetchone()
        if not krow:
            return None
        await db.execute(
            "UPDATE api_keys SET last_used_at=? WHERE id=?", (_now(), krow["id"])
        )
        await db.commit()
        async with db.execute(
            "SELECT * FROM users WHERE user_id=?", (krow["user_id"],)
        ) as cur:
            urow = await cur.fetchone()
            return dict(urow) if urow else None


async def db_list_user_keys(uid: int) -> list:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(
            "SELECT * FROM api_keys WHERE user_id=? AND revoked=0 ORDER BY created_at DESC", (uid,)
        ) as cur:
            return [dict(r) for r in await cur.fetchall()]


async def db_revoke_key(key_id: int, uid: int) -> bool:
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute(
            "UPDATE api_keys SET revoked=1 WHERE id=? AND user_id=?", (key_id, uid)
        )
        await db.commit()
        return cur.rowcount > 0


# Simple in-memory sliding-window rate limiter (per API key or IP)
_rate_hits: dict = {}


def _rate_limited(bucket: str) -> bool:
    now = time.time()
    hits = _rate_hits.setdefault(bucket, [])
    hits[:] = [t for t in hits if now - t < API_RATE_WINDOW]
    if len(hits) >= API_RATE_LIMIT:
        return True
    hits.append(now)
    return False


# ══════════════════════════════════════════════════════
#              MARKET SIMULATION 📈
# ══════════════════════════════════════════════════════

async def _price_tick() -> None:
    async with market_lock:
        if random.random() < FAIR_DRIFT_CHANCE:
            market["fair"] *= 1 + random.uniform(-FAIR_DRIFT_PCT, FAIR_DRIFT_PCT)
            market["fair"] = max(PRICE_MIN, min(PRICE_MAX, market["fair"]))

        noise = random.gauss(0, PRICE_VOLATILITY)
        reversion = (market["fair"] - market["price"]) / market["fair"] * MEAN_REVERSION
        new_price = market["price"] * (1 + noise + reversion)
        new_price = max(PRICE_MIN, min(PRICE_MAX, new_price))

        market["prev_price"] = market["price"]
        market["price"] = round(new_price, 6)

    await db_log_price(market["price"])


async def _price_ticker_loop() -> None:
    await db_log_price(market["price"])
    while True:
        await asyncio.sleep(PRICE_TICK_SECONDS)
        try:
            await _price_tick()
        except Exception:
            log.exception("Price ticker error")


def _change_pct(old: float, new: float) -> float:
    if old <= 0:
        return 0.0
    return (new - old) / old * 100


def _trend_emoji(pct: float) -> str:
    if pct > 0.05:  return E_UP
    if pct < -0.05: return E_DOWN
    return E_FLAT


# ── Price chart (matplotlib, optional) ─────────────────

def _price_chart_sync(rows: list) -> Optional[bytes]:
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import matplotlib.dates as mdates
        from datetime import datetime as _dt
    except ImportError:
        return None
    if not rows:
        return None

    xs = [_dt.fromisoformat(r[0]) for r in rows]
    ys = [r[1] for r in rows]

    fig, ax = plt.subplots(figsize=(12, 5.5))
    fig.patch.set_facecolor("#0d1117")
    ax.set_facecolor("#0d1117")

    up = ys[-1] >= ys[0]
    color = "#3fb950" if up else "#f85149"
    ax.plot(xs, ys, color=color, linewidth=2, zorder=3)
    ax.fill_between(xs, ys, min(ys), color=color, alpha=0.12, zorder=2)

    ax.xaxis.set_major_formatter(mdates.DateFormatter("%H:%M"))
    ax.tick_params(colors="#8b949e", labelsize=9)
    for sp in ax.spines.values():
        sp.set_visible(False)
    ax.yaxis.grid(True, color="#21262d", linewidth=0.6)
    ax.set_axisbelow(True)
    ax.set_title(f"VRF / USD  —  {ys[-1]:.4f}", color="#e6edf3", fontsize=13, pad=10)

    plt.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="PNG", dpi=130, facecolor="#0d1117")
    plt.close(fig)
    buf.seek(0)
    return buf.read()


# ══════════════════════════════════════════════════════
#      SCAM TRANSFER CARD IMAGE  🎭  (Pillow + фото-шаблон)
# ══════════════════════════════════════════════════════
# Рисует сумму поверх фиксированного фона (свой арт-дирекшн + иконки уже
# вшиты в сам файл — код только позиционирует текст в размеченные под него
# зоны). Позиции измерены по референсному макету и заданы в долях от размера
# картинки, поэтому подходят для фона любого разрешения с тем же соотношением
# сторон.
#
# Источник данных — ГЛАВНЫМ ОБРАЗОМ scam_assets_data.py (фон и шрифты,
# закодированные в base64 прямо внутри обычного .py-файла). Это специально
# сделано так, чтобы НЕ зависеть от того, доехала ли отдельная папка
# assets/ до сервера деплоя — .py-файл гарантированно деплоится вместе
# с остальным кодом. Папка assets/ на диске поддерживается только как
# запасной вариант (например, для локальной разработки).

_ASSETS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "assets")
SCAM_BG_PATH = os.path.join(_ASSETS_DIR, "scam_bg.png")
FONT_BOLD_PATHS = [
    os.path.join(_ASSETS_DIR, "fonts", "DejaVuSans-Bold.ttf"),
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
]
FONT_REG_PATHS = [
    os.path.join(_ASSETS_DIR, "fonts", "DejaVuSans.ttf"),
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
]

try:
    from scam_assets_data import SCAM_BG_B64, FONT_BOLD_B64, FONT_REG_B64
    _ASSETS_MODULE_FOUND = True
except ImportError:
    SCAM_BG_B64 = FONT_BOLD_B64 = FONT_REG_B64 = None
    _ASSETS_MODULE_FOUND = False


def _b64_bytes(b64_str):
    if not b64_str:
        return None
    try:
        return base64.b64decode(b64_str)
    except Exception:
        return None


_EMBEDDED_BG_BYTES   = _b64_bytes(SCAM_BG_B64)
_EMBEDDED_BOLD_BYTES = _b64_bytes(FONT_BOLD_B64)
_EMBEDDED_REG_BYTES  = _b64_bytes(FONT_REG_B64)


# ── Диагностика assets ─────────────────────────────────
# Отдельная функция, чтобы можно было увидеть состояние данных на сервере
# и в логах Railway при старте, и по команде /checkassets прямо в Telegram —
# без необходимости заходить в Shell.

def _asset_report_lines() -> list:
    lines = [f"📂 Скрипт запущен из: {os.path.dirname(os.path.abspath(__file__))}"]

    lines.append(
        f"{'✅' if _ASSETS_MODULE_FOUND else '❌'} scam_assets_data.py: "
        + ("найден и импортирован" if _ASSETS_MODULE_FOUND else "НЕ найден рядом со скриптом")
    )
    lines.append(
        f"{'✅' if _EMBEDDED_BG_BYTES else '❌'} embedded scam_bg: "
        + (f"{len(_EMBEDDED_BG_BYTES)/1024:.0f} КБ декодировано" if _EMBEDDED_BG_BYTES else "нет данных")
    )
    lines.append(
        f"{'✅' if _EMBEDDED_BOLD_BYTES else '❌'} embedded bold-шрифт: "
        + (f"{len(_EMBEDDED_BOLD_BYTES)/1024:.0f} КБ декодировано" if _EMBEDDED_BOLD_BYTES else "нет данных")
    )

    exists = os.path.isdir(_ASSETS_DIR)
    lines.append(f"{'ℹ️' if exists else 'ℹ️'} (запасной вариант) папка assets/: "
                 f"{'найдена' if exists else 'не найдена'} — {_ASSETS_DIR}")
    bg_exists = os.path.isfile(SCAM_BG_PATH)
    if bg_exists:
        lines.append(f"   scam_bg.png на диске: {os.path.getsize(SCAM_BG_PATH)/1024:.0f} КБ")

    lines.append(
        "🖼 Итог: фон будет взят из "
        + ("scam_assets_data.py (основной источник)" if _EMBEDDED_BG_BYTES
           else ("assets/scam_bg.png (запасной путь)" if bg_exists
                 else "программной заглушки (ни один источник не найден)"))
    )
    return lines


def _log_asset_diagnostics() -> None:
    lines = _asset_report_lines()
    log.info("=== SCAM assets diagnostics ===")
    for ln in lines:
        log.info(ln)
    log.info("================================")


# Зоны (x0, y0, x1, y1) в долях ширины/высоты фона
SCAM_NUM_BBOX_FRAC   = (0.0859, 0.4111, 0.6805, 0.6958)   # крупная сумма
SCAM_LABEL_BBOX_FRAC = (0.6984, 0.6389, 0.8188, 0.6917)   # тег "SCAM"
SCAM_USD_BBOX_FRAC   = (0.0961, 0.7625, 0.2844, 0.8653)   # "$ 0,00"

SCAM_USD_DISPLAY = "0,00"   # у SCAM нет рыночной цены — токен-шутка, всегда $0

_SENTINEL_MISSING = object()
_scam_bg_cache = None   # None = ещё не пробовали · _SENTINEL_MISSING = нигде не нашли · Image = загружен


def _load_scam_bg():
    global _scam_bg_cache
    if _scam_bg_cache is None:
        from PIL import Image
        try:
            if _EMBEDDED_BG_BYTES:
                _scam_bg_cache = Image.open(io.BytesIO(_EMBEDDED_BG_BYTES)).convert("RGB")
            else:
                _scam_bg_cache = Image.open(SCAM_BG_PATH).convert("RGB")
        except Exception:
            log.warning("SCAM background unavailable (embedded and %s) — using fallback card", SCAM_BG_PATH)
            _scam_bg_cache = _SENTINEL_MISSING
    return None if _scam_bg_cache is _SENTINEL_MISSING else _scam_bg_cache


def _load_font(kind: str, size: int):
    """kind: 'bold' | 'reg'. Пробует embedded-байты, затем файловые пути."""
    from PIL import ImageFont
    data = _EMBEDDED_BOLD_BYTES if kind == "bold" else _EMBEDDED_REG_BYTES
    if data:
        try:
            return ImageFont.truetype(io.BytesIO(data), size)
        except Exception:
            pass
    for p in (FONT_BOLD_PATHS if kind == "bold" else FONT_REG_PATHS):
        try:
            return ImageFont.truetype(p, size)
        except Exception:
            continue
    return None


def _fit_text(draw, text: str, kind: str, max_w: int, max_h: int,
              max_size: int = 440, min_size: int = 10, step: int = 2):
    """Подбирает наибольший размер шрифта, при котором text помещается в max_w×max_h.
    kind: 'bold' | 'reg'. Никогда не бросает исключение — при отсутствии всех
    источников шрифта откатывается на встроенный шрифт Pillow (load_default)."""
    from PIL import ImageFont

    size = max_size
    while size >= min_size:
        font = _load_font(kind, size)
        if font is None:
            size -= step
            continue
        bbox = draw.textbbox((0, 0), text, font=font)
        w, h = bbox[2] - bbox[0], bbox[3] - bbox[1]
        if w <= max_w and h <= max_h:
            return font, bbox
        size -= step

    font = _load_font(kind, min_size)
    if font is None:
        try:
            font = ImageFont.load_default(size=min_size)
        except TypeError:
            font = ImageFont.load_default()
    return font, draw.textbbox((0, 0), text, font=font)


def _scam_card_image_sync(amount: float) -> Optional[bytes]:
    """Карточка перевода SCAM: фон-шаблон + сумма + тег SCAM + $-эквивалент."""
    try:
        from PIL import Image, ImageDraw
    except ImportError:
        return None

    bg = _load_scam_bg()
    if bg is None:
        return _scam_card_fallback_sync(amount)

    img = bg.copy()
    W, H = img.size
    d = ImageDraw.Draw(img)

    WHITE = (255, 255, 255)
    GRAY  = (150, 163, 180)

    def box_px(frac):
        x0, y0, x1, y1 = frac
        return int(x0 * W), int(y0 * H), int(x1 * W), int(y1 * H)

    def draw_fitted(frac, text, color):
        x0, y0, x1, y1 = box_px(frac)
        font, bbox = _fit_text(d, text, "bold", x1 - x0, y1 - y0)
        th = bbox[3] - bbox[1]
        tx = x0 - bbox[0]
        ty = y0 + ((y1 - y0) - th) // 2 - bbox[1]
        d.text((tx, ty), text, font=font, fill=color)

    amount_str = fmt_scam(amount)
    draw_fitted(SCAM_NUM_BBOX_FRAC, amount_str, WHITE)
    draw_fitted(SCAM_LABEL_BBOX_FRAC, "SCAM", GRAY)
    draw_fitted(SCAM_USD_BBOX_FRAC, f"$ {SCAM_USD_DISPLAY}", GRAY)

    buf = io.BytesIO()
    img.save(buf, format="PNG", optimize=True)
    buf.seek(0)
    return buf.read()


def _scam_bg_gradient(W: int, H: int):
    """Тёмно-синий фон с мягким свечением снизу-слева (похоже на референс).
    Использует numpy для гладкого радиального градиента; если numpy
    недоступен — откатывается на простой линейный градиент по строкам."""
    from PIL import Image
    BG_TOP = (6, 10, 18)
    BG_MID = (9, 15, 27)
    GLOW = (28, 95, 190)

    try:
        import numpy as np
        yy, xx = np.mgrid[0:H, 0:W]
        t = yy / H
        base = (np.array(BG_TOP)[None, None, :]
                + (np.array(BG_MID) - np.array(BG_TOP))[None, None, :] * t[:, :, None])
        dist = np.sqrt(xx.astype(float) ** 2 + (yy - H).astype(float) ** 2)
        max_d = math.hypot(W * 0.62, H * 0.62)
        glow_amt = np.clip(1 - dist / max_d, 0, 1) ** 2.2
        glow = np.array(GLOW)[None, None, :] * glow_amt[:, :, None]
        arr = np.clip(base + glow, 0, 255).astype("uint8")
        return Image.fromarray(arr, mode="RGB")
    except Exception:
        img = Image.new("RGB", (W, H), BG_TOP)
        d = ImageDraw.Draw(img)
        for y in range(H):
            t = y / H
            col = tuple(round(BG_TOP[i] + (BG_MID[i] - BG_TOP[i]) * t) for i in range(3))
            d.line([(0, y), (W, y)], fill=col)
        return img


def _draw_lightning_badge(d, cx: int, cy: int, r: int) -> None:
    d.ellipse([cx - r, cy - r, cx + r, cy + r], fill=(24, 119, 242))
    d.ellipse([cx - r, cy - r, cx + r, cy + r], outline=(70, 160, 255), width=max(2, r // 30))
    bw, bh = r * 0.62, r * 1.05
    pts = [
        (cx + bw * 0.28, cy - bh * 0.52),
        (cx - bw * 0.42, cy + bh * 0.08),
        (cx - bw * 0.02, cy + bh * 0.08),
        (cx - bw * 0.28, cy + bh * 0.52),
        (cx + bw * 0.42, cy - bh * 0.08),
        (cx + bw * 0.02, cy - bh * 0.08),
    ]
    d.polygon(pts, fill=(255, 255, 255))


def _draw_spy_icon(d, x0: int, y0: int, x1: int, y1: int) -> None:
    d.rounded_rectangle([x0, y0, x1 + (x1 - x0) * 0.5, y1 + (y1 - y0) * 0.5],
                        radius=34, outline=(52, 110, 190), width=4)
    bw, bh = x1 - x0, y1 - y0
    cx = x0 + bw * 0.5
    cy = y0 + bh * 0.58
    Wc = bw * 0.72

    head_r = Wc * 0.30
    d.ellipse([cx - head_r, cy - head_r * 0.9, cx + head_r, cy + head_r * 0.95], fill=(255, 255, 255))

    brim_y = cy - head_r * 0.55
    d.ellipse([cx - Wc * 0.52, brim_y - Wc * 0.10, cx + Wc * 0.52, brim_y + Wc * 0.10], fill=(255, 255, 255))
    dome_r = Wc * 0.30
    d.pieslice([cx - dome_r, brim_y - dome_r * 1.5, cx + dome_r, brim_y + dome_r * 0.5],
               180, 360, fill=(255, 255, 255))

    lens_w, lens_h = head_r * 0.62, head_r * 0.40
    ly = cy - head_r * 0.05
    d.rounded_rectangle([cx - lens_w * 1.05, ly - lens_h / 2, cx - lens_w * 0.15, ly + lens_h / 2],
                        radius=int(lens_h * 0.3), fill=(15, 20, 30))
    d.rounded_rectangle([cx + lens_w * 0.15, ly - lens_h / 2, cx + lens_w * 1.05, ly + lens_h / 2],
                        radius=int(lens_h * 0.3), fill=(15, 20, 30))
    d.line([(cx - lens_w * 0.15, ly), (cx + lens_w * 0.15, ly)],
           fill=(15, 20, 30), width=max(2, int(lens_h * 0.18)))

    coll_y0 = cy + head_r * 0.75
    coll_y1 = cy + head_r * 1.7
    d.polygon([(cx - head_r * 0.9, coll_y0), (cx - head_r * 0.05, coll_y0), (cx - head_r * 0.55, coll_y1)],
              fill=(255, 255, 255))
    d.polygon([(cx + head_r * 0.9, coll_y0), (cx + head_r * 0.05, coll_y0), (cx + head_r * 0.55, coll_y1)],
              fill=(255, 255, 255))


def _draw_send_arrow(d, x: int, y: int, size: int) -> None:
    w, h = size, size * 1.15
    col = (215, 238, 250)
    lw = max(3, size // 14)
    apex     = (x + w * 0.5, y)
    left_bot = (x + w * 0.30, y + h)
    left_in  = (x + w * 0.30, y + h * 0.42)
    right_in = (x + w * 0.70, y + h * 0.42)
    right_bot = (x + w * 0.70, y + h)
    d.line([left_bot, left_in, apex, right_in, right_bot], fill=col, width=lw, joint="curve")


def _scam_card_fallback_sync(amount: float) -> Optional[bytes]:
    """Запасной вариант, если assets/scam_bg.png не найден рядом со скриптом —
    рисует карточку в похожем стиле (градиент + свечение, значок +SEND,
    молния, силуэт "шпиона"), чтобы бот не падал и выглядел презентабельно
    даже без твоего фото-фона."""
    try:
        from PIL import Image, ImageDraw
    except ImportError:
        return None

    W, H = 1280, 720
    img = _scam_bg_gradient(W, H)
    d = ImageDraw.Draw(img)

    _draw_send_arrow(d, int(W * 0.078), int(H * 0.10), int(W * 0.075))
    f_send, _ = _fit_text(d, "+SEND", "bold", int(W * 0.16), int(H * 0.08), max_size=60)
    d.text((int(W * 0.198), int(H * 0.155)), "+SEND", font=f_send, fill=(215, 238, 250))

    _draw_lightning_badge(d, int(W * 0.82), int(H * 0.26), int(W * 0.065))
    _draw_spy_icon(d, int(W * 0.80), int(H * 0.70), int(W * 0.97), int(H * 0.97))

    WHITE = (255, 255, 255)
    GRAY  = (150, 163, 180)

    def box_px(frac):
        x0, y0, x1, y1 = frac
        return int(x0 * W), int(y0 * H), int(x1 * W), int(y1 * H)

    def draw_fitted(frac, text, color):
        x0, y0, x1, y1 = box_px(frac)
        font, bbox = _fit_text(d, text, "bold", x1 - x0, y1 - y0)
        th = bbox[3] - bbox[1]
        tx = x0 - bbox[0]
        ty = y0 + ((y1 - y0) - th) // 2 - bbox[1]
        d.text((tx, ty), text, font=font, fill=color)

    amount_str = fmt_scam(amount)
    draw_fitted(SCAM_NUM_BBOX_FRAC, amount_str, WHITE)
    draw_fitted(SCAM_LABEL_BBOX_FRAC, "SCAM", GRAY)
    draw_fitted(SCAM_USD_BBOX_FRAC, f"$ {SCAM_USD_DISPLAY}", GRAY)

    buf = io.BytesIO()
    img.save(buf, format="PNG", optimize=True)
    buf.seek(0)
    return buf.read()


# ══════════════════════════════════════════════════════
#          RICH CARDS  —  market / balance / stakes
# ══════════════════════════════════════════════════════

async def _market_cards() -> Tuple[str, str]:
    price = market["price"]
    prev  = market["prev_price"]
    chg_tick = _change_pct(prev, price)

    p24 = await db_price_at(24)
    chg24 = _change_pct(p24, price) if p24 else 0.0
    lo24, hi24 = await db_price_range(24)
    lo24 = lo24 if lo24 is not None else price
    hi24 = hi24 if hi24 is not None else price

    tr = _trend_emoji(chg24)
    sign = "+" if chg24 >= 0 else ""

    rich_h = (
        f"<h2>{E_COIN} VRF / USD</h2>"
        "<table bordered striped>"
        f"<tr><td>💰 Цена</td><td align=\"right\"><mark><b>{fmt_price(price)} USD</b></mark></td></tr>"
        f"<tr><td>{tr} Изм. 24ч</td><td align=\"right\"><b>{sign}{chg24:.2f}%</b></td></tr>"
        f"<tr><td>⬆️ Макс. 24ч</td><td align=\"right\">{fmt_price(hi24)} USD</td></tr>"
        f"<tr><td>⬇️ Мин. 24ч</td><td align=\"right\">{fmt_price(lo24)} USD</td></tr>"
        f"<tr><td>🔁 Тик</td><td align=\"right\">{'+' if chg_tick>=0 else ''}{chg_tick:.2f}%</td></tr>"
        "</table>"
        f"<blockquote>Комиссия сделки: {TRADE_FEE_PCT*100:.1f}%</blockquote>"
    )
    fb_h = (
        f"{E_COIN} <b>VRF / USD</b>\n\n"
        f"💰 Цена: <b>{fmt_price(price)} USD</b>\n"
        f"{tr} 24ч: <b>{sign}{chg24:.2f}%</b>\n"
        f"⬆️ Макс: {fmt_price(hi24)}  ⬇️ Мин: {fmt_price(lo24)}\n\n"
        f"Комиссия сделки: {TRADE_FEE_PCT*100:.1f}%"
    )
    return rich_h, fb_h


def _market_kb(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [
            SBtn(f"{E_UP} Купить", style="success", callback_data=f"ex:menu:{uid}:buy"),
            SBtn(f"{E_DOWN} Продать", style="danger", callback_data=f"ex:menu:{uid}:sell"),
        ],
        [
            SBtn(f"{E_LOCK} Стейкинг", style="primary", callback_data=f"st:menu:{uid}"),
            SBtn("📊 График", style="primary", callback_data=f"ex:chart:{uid}"),
        ],
        [SBtn("🔄 Обновить", style="primary", callback_data=f"ex:refresh:{uid}")],
    ])


async def _balance_cards(uid: int) -> Tuple[str, str]:
    u = await db_get_user(uid)
    price = market["price"]
    usd, vrf = (u["usd"], u["vrf"]) if u else (0.0, 0.0)
    scam = u["scam"] if u else 0.0

    stakes = await db_get_user_stakes(uid)
    staked_total = sum(s["amount"] for s in stakes)
    accrued_total = sum(stake_accrued(s) for s in stakes)

    vrf_value = vrf * price
    staked_value = staked_total * price
    net_worth = usd + vrf_value + staked_value

    rich_h = (
        "<h2>👤 Баланс</h2>"
        "<table bordered striped>"
        f"<tr><td>{E_USD} USD</td><td align=\"right\"><b>{fmt(usd)}</b></td></tr>"
        f"<tr><td>{E_COIN} VRF</td><td align=\"right\"><b>{fmt(vrf)}</b> "
        f"<i>(~{fmt(vrf_value)} USD)</i></td></tr>"
        f"<tr><td>🎭 SCAM</td><td align=\"right\"><b>{fmt_scam(scam)}</b></td></tr>"
        f"<tr><td>{E_LOCK} В стейке</td><td align=\"right\"><b>{fmt(staked_total)} VRF</b> "
        f"<i>(~{fmt(staked_value)} USD)</i></td></tr>"
        f"<tr><td>💠 Накоплено %</td><td align=\"right\"><b>{fmt(accrued_total)} VRF</b></td></tr>"
        f"<tr><th>💼 Всего активов</th><th align=\"right\"><mark><b>~{fmt(net_worth)} USD</b></mark></th></tr>"
        "</table>"
    )
    fb_h = (
        f"👤 <b>Баланс</b>\n\n"
        f"{E_USD} USD: <b>{fmt(usd)}</b>\n"
        f"{E_COIN} VRF: <b>{fmt(vrf)}</b> (~{fmt(vrf_value)} USD)\n"
        f"🎭 SCAM: <b>{fmt_scam(scam)}</b>\n"
        f"{E_LOCK} В стейке: <b>{fmt(staked_total)} VRF</b>\n"
        f"💠 Накоплено %: <b>{fmt(accrued_total)} VRF</b>\n\n"
        f"💼 Всего активов: <b>~{fmt(net_worth)} USD</b>"
    )
    return rich_h, fb_h


def _balance_kb(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        SBtn(f"{E_UP} Купить", style="success", callback_data=f"ex:menu:{uid}:buy"),
        SBtn(f"{E_DOWN} Продать", style="danger", callback_data=f"ex:menu:{uid}:sell"),
    ], [
        SBtn(f"{E_LOCK} Стейки", style="primary", callback_data=f"st:list:{uid}"),
        SBtn("🔄 Обновить", style="primary", callback_data=f"ba:refresh:{uid}"),
    ]])


# ══════════════════════════════════════════════════════
#                    COMMANDS
# ══════════════════════════════════════════════════════

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    u = update.effective_user
    await db_ensure_user(u.id, u.username or "", u.first_name)

    rich_h = (
        "<h1>💹 VRF Exchange</h1>"
        "<p>Биржа токена <b>#VRF</b> — покупай, продавай, зарабатывай на стейкинге!</p>"
        "<hr/>"
        "<ul>"
        f"<li>{E_UP} <b>/buy</b> — купить VRF за USD</li>"
        f"<li>{E_DOWN} <b>/sell</b> — продать VRF за USD</li>"
        f"<li>{E_LOCK} <b>/stake</b> — положить VRF под процент</li>"
        "<li>👤 <b>/balance</b> — баланс и активы</li>"
        "<li>💹 <b>/market</b> — текущая цена и график</li>"
        "</ul>"
        "<hr/>"
        f"<blockquote>Стартовый баланс: <b>{fmt(STARTING_USD)} USD</b></blockquote>"
    )
    fb_h = (
        "💹 <b>VRF Exchange</b>\n\n"
        f"Стартовый баланс: <b>{fmt(STARTING_USD)} USD</b>\n\n"
        "/buy · /sell · /stake · /balance · /market"
    )
    await send_rich(context.bot, update.effective_chat.id, html=rich_h, fallback_html=fb_h,
                    reply_to_id=update.message.message_id,
                    reply_markup=_market_kb(u.id))


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    rich_h = (
        "<h1>📖 Помощь — VRF Exchange</h1>"
        "<h3>💹 Торговля</h3>"
        "<ul>"
        "<li>/market — текущая цена VRF, изменение, график</li>"
        "<li>/buy [сумма USD] — купить VRF</li>"
        "<li>/sell [сумма VRF] — продать VRF</li>"
        "<li>/chart — график цены за 24ч</li>"
        "</ul>"
        "<h3>🔒 Стейкинг</h3>"
        "<ul>"
        "<li>/stake — выбрать тариф и положить VRF под процент</li>"
        "<li>/stakes — активные стейки, начисленный процент</li>"
        "</ul>"
        "<h3>🎭 Токен SCAM</h3>"
        "<ul><li><code>пер 0,048</code> — перевести SCAM (ответом на сообщение получателя), "
        "генерируется картинка-чек</li></ul>"
        "<h3>👤 Аккаунт</h3>"
        "<ul><li>/balance — баланс USD/VRF/SCAM и суммарные активы</li></ul>"
        "<hr/>"
        "<details open><summary>⚙️ Тарифы стейкинга</summary><ul>"
        + "".join(
            f"<li>{t['label']} — <b>{t['apr']*100:.0f}% годовых</b>"
            + (f", штраф за досрочный вывод {t['penalty']*100:.0f}%" if t["lock_days"] else "")
            + "</li>"
            for t in STAKE_TIERS.values()
        )
        + "</ul></details>"
    )
    fb_h = (
        "📖 <b>Помощь — VRF Exchange</b>\n\n"
        "💹 /market /buy /sell /chart\n"
        "🔒 /stake /stakes\n"
        "🎭 <code>пер 0,048</code> — перевод SCAM (ответом)\n"
        "👤 /balance\n\n"
        "Тарифы стейкинга:\n" +
        "\n".join(f"• {t['label']} — {t['apr']*100:.0f}% год." for t in STAKE_TIERS.values())
    )
    await send_rich(context.bot, update.effective_chat.id, html=rich_h, fallback_html=fb_h,
                    reply_to_id=update.message.message_id)


async def cmd_market(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    u = update.effective_user
    await db_ensure_user(u.id, u.username or "", u.first_name)
    rich_h, fb_h = await _market_cards()
    await send_rich(context.bot, update.effective_chat.id, html=rich_h, fallback_html=fb_h,
                    reply_to_id=update.message.message_id, reply_markup=_market_kb(u.id))


async def cmd_price(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    price = market["price"]
    chg = _change_pct(await db_price_at(24) or price, price)
    tr = _trend_emoji(chg)
    await update.message.reply_text(
        f"{E_COIN} <b>1 VRF = {fmt_price(price)} USD</b>  {tr} {chg:+.2f}% (24ч)",
        parse_mode=ParseMode.HTML,
    )


async def cmd_balance(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    u = update.effective_user
    await db_ensure_user(u.id, u.username or "", u.first_name)
    rich_h, fb_h = await _balance_cards(u.id)
    await send_rich(context.bot, update.effective_chat.id, html=rich_h, fallback_html=fb_h,
                    reply_to_id=update.message.message_id, reply_markup=_balance_kb(u.id))


async def cmd_chart(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    hours = 24
    if context.args:
        try:
            hours = min(168, max(1, int(context.args[0])))
        except ValueError:
            pass
    rows = await db_price_history(hours)
    if len(rows) < 2:
        await update.message.reply_text("📊 Пока недостаточно данных для графика.")
        return
    loop = asyncio.get_running_loop()
    img = await loop.run_in_executor(None, _price_chart_sync, rows)
    if img is None:
        await update.message.reply_text(
            "❌ Установи matplotlib:\n<code>pip install matplotlib</code>",
            parse_mode=ParseMode.HTML,
        )
        return
    await context.bot.send_photo(
        chat_id=update.effective_chat.id,
        photo=io.BytesIO(img),
        caption=f"📊 <b>VRF/USD — последние {hours}ч</b>",
        parse_mode=ParseMode.HTML,
    )


# ── Buy / Sell (execute trade) ─────────────────────────

async def _execute_buy(uid: int, usd_amount: float) -> Tuple[bool, str]:
    u = await db_get_user(uid)
    if not u:
        return False, "❌ Пользователь не найден"
    if usd_amount <= 0:
        return False, "❌ Сумма должна быть больше 0"
    if u["usd"] < usd_amount:
        return False, f"❌ Недостаточно USD! Есть: {fmt(u['usd'])}"

    async with market_lock:
        price = market["price"]

    fee = usd_amount * TRADE_FEE_PCT
    net_usd = usd_amount - fee
    vrf_bought = net_usd / price

    await db_set_balances(uid, usd=u["usd"] - usd_amount)
    new_vrf = await db_add_vrf(uid, vrf_bought)
    await db_log_trade(uid, "buy", vrf_bought, usd_amount, price)

    return True, (
        f"{E_UP} <b>Покупка исполнена!</b>\n\n"
        f"💵 Потрачено: <b>{fmt(usd_amount)} USD</b> <i>(комиссия {fmt(fee)})</i>\n"
        f"{E_COIN} Получено: <b>+{fmt(vrf_bought)} VRF</b>\n"
        f"💰 По цене: {fmt_price(price)} USD\n\n"
        f"{E_COIN} Баланс VRF: <b>{fmt(new_vrf)}</b>"
    )


async def _execute_sell(uid: int, vrf_amount: float) -> Tuple[bool, str]:
    u = await db_get_user(uid)
    if not u:
        return False, "❌ Пользователь не найден"
    if vrf_amount <= 0:
        return False, "❌ Сумма должна быть больше 0"
    if u["vrf"] < vrf_amount:
        return False, f"❌ Недостаточно VRF! Есть: {fmt(u['vrf'])}"

    async with market_lock:
        price = market["price"]

    gross_usd = vrf_amount * price
    fee = gross_usd * TRADE_FEE_PCT
    net_usd = gross_usd - fee

    await db_set_balances(uid, vrf=u["vrf"] - vrf_amount)
    new_usd = await db_add_usd(uid, net_usd)
    await db_log_trade(uid, "sell", vrf_amount, net_usd, price)

    return True, (
        f"{E_DOWN} <b>Продажа исполнена!</b>\n\n"
        f"{E_COIN} Продано: <b>{fmt(vrf_amount)} VRF</b>\n"
        f"💵 Получено: <b>+{fmt(net_usd)} USD</b> <i>(комиссия {fmt(fee)})</i>\n"
        f"💰 По цене: {fmt_price(price)} USD\n\n"
        f"{E_USD} Баланс USD: <b>{fmt(new_usd)}</b>"
    )


async def cmd_buy(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    u = update.effective_user
    await db_ensure_user(u.id, u.username or "", u.first_name)
    if not context.args:
        await _show_buy_menu(update.message, u.id, context)
        return
    try:
        amount = float(context.args[0].replace(",", "."))
    except ValueError:
        await update.message.reply_text("❌ Использование: /buy <сумма USD>")
        return
    ok, msg = await _execute_buy(u.id, amount)
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML)


async def cmd_sell(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    u = update.effective_user
    await db_ensure_user(u.id, u.username or "", u.first_name)
    if not context.args:
        await _show_sell_menu(update.message, u.id, context)
        return
    try:
        amount = float(context.args[0].replace(",", "."))
    except ValueError:
        await update.message.reply_text("❌ Использование: /sell <сумма VRF>")
        return
    ok, msg = await _execute_sell(u.id, amount)
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML)


def _buy_kb(uid: int) -> InlineKeyboardMarkup:
    row1 = [SBtn(f"{a} USD", style="success", callback_data=f"ex:buy:{uid}:{a}")
            for a in BUY_PRESETS_USD[:3]]
    row2 = [SBtn(f"{a} USD", style="success", callback_data=f"ex:buy:{uid}:{a}")
            for a in BUY_PRESETS_USD[3:]]
    return InlineKeyboardMarkup([
        row1, row2,
        [SBtn("✏️ Своя сумма", style="primary", callback_data=f"ex:buyc:{uid}")],
        [SBtn("◀ Назад", style="primary", callback_data=f"ex:refresh:{uid}")],
    ])


def _sell_kb(uid: int) -> InlineKeyboardMarkup:
    row1 = [SBtn(f"{a} VRF", style="danger", callback_data=f"ex:sell:{uid}:{a}")
            for a in SELL_PRESETS_VRF[:3]]
    row2 = [SBtn(f"{a} VRF", style="danger", callback_data=f"ex:sell:{uid}:{a}")
            for a in SELL_PRESETS_VRF[3:]]
    return InlineKeyboardMarkup([
        row1, row2,
        [SBtn("✏️ Своя сумма", style="primary", callback_data=f"ex:sellc:{uid}")],
        [SBtn("◀ Назад", style="primary", callback_data=f"ex:refresh:{uid}")],
    ])


async def _show_buy_menu(message, uid: int, context) -> None:
    price = market["price"]
    await message.reply_text(
        f"{E_UP} <b>Купить VRF</b>\n\n💰 Цена: <b>{fmt_price(price)} USD</b>\n\n"
        f"Выбери сумму в USD:",
        parse_mode=ParseMode.HTML, reply_markup=_buy_kb(uid),
    )


async def _show_sell_menu(message, uid: int, context) -> None:
    price = market["price"]
    await message.reply_text(
        f"{E_DOWN} <b>Продать VRF</b>\n\n💰 Цена: <b>{fmt_price(price)} USD</b>\n\n"
        f"Выбери сумму в VRF:",
        parse_mode=ParseMode.HTML, reply_markup=_sell_kb(uid),
    )


# ── Staking ─────────────────────────────────────────────

def _stake_tier_kb(uid: int) -> InlineKeyboardMarkup:
    rows = []
    for key, t in STAKE_TIERS.items():
        rows.append([SBtn(
            f"{t['label']} — {t['apr']*100:.0f}%",
            style="primary", callback_data=f"st:tier:{uid}:{key}",
        )])
    rows.append([SBtn("◀ Назад", style="primary", callback_data=f"ex:refresh:{uid}")])
    return InlineKeyboardMarkup(rows)


def _stake_amount_kb(uid: int, tier: str) -> InlineKeyboardMarkup:
    row1 = [SBtn(f"{a}", style="success", callback_data=f"st:amt:{uid}:{tier}:{a}")
            for a in STAKE_PRESETS_VRF[:3]]
    row2 = [SBtn(f"{a}", style="success", callback_data=f"st:amt:{uid}:{tier}:{a}")
            for a in STAKE_PRESETS_VRF[3:]]
    return InlineKeyboardMarkup([
        row1, row2,
        [SBtn("✏️ Своя сумма", style="primary", callback_data=f"st:amtc:{uid}:{tier}")],
        [SBtn("◀ Назад", style="primary", callback_data=f"st:menu:{uid}")],
    ])


async def cmd_stake(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    u = update.effective_user
    await db_ensure_user(u.id, u.username or "", u.first_name)
    uu = await db_get_user(u.id)
    rows = "".join(
        f"<tr><td>{t['label']}</td><td align=\"right\"><b>{t['apr']*100:.0f}%</b> год."
        + (f" · штраф {t['penalty']*100:.0f}%" if t["lock_days"] else "") + "</td></tr>"
        for t in STAKE_TIERS.values()
    )
    rich_h = (
        f"<h2>{E_LOCK} Стейкинг VRF</h2>"
        f"<p>Баланс: <b>{fmt(uu['vrf'] if uu else 0)} VRF</b></p>"
        "<table bordered striped>" + rows + "</table>"
        "<blockquote>Гибкий тариф — снятие в любой момент.<br/>"
        "Тарифы со сроком — выше доходность, штраф за досрочный вывод.</blockquote>"
    )
    fb_h = (
        f"{E_LOCK} <b>Стейкинг VRF</b>\n\nБаланс: <b>{fmt(uu['vrf'] if uu else 0)} VRF</b>\n\n"
        + "\n".join(f"• {t['label']} — {t['apr']*100:.0f}% год." for t in STAKE_TIERS.values())
    )
    await send_rich(context.bot, update.effective_chat.id, html=rich_h, fallback_html=fb_h,
                    reply_to_id=update.message.message_id, reply_markup=_stake_tier_kb(u.id))


def _stake_row_kb(stake: dict) -> InlineKeyboardMarkup:
    sid = stake["id"]
    btns = []
    if stake["lock_days"] == 0:
        btns.append(SBtn("💠 Забрать %", style="primary", callback_data=f"st:cl:{sid}"))
        btns.append(SBtn("🔓 Вывести", style="danger", callback_data=f"st:un:{sid}"))
    else:
        if stake_is_matured(stake):
            btns.append(SBtn("💰 Забрать всё", style="success", callback_data=f"st:un:{sid}"))
        else:
            btns.append(SBtn("⚠️ Досрочно", style="danger", callback_data=f"st:un:{sid}"))
    return InlineKeyboardMarkup([btns])


async def _stakes_text(uid: int) -> Tuple[str, list]:
    stakes = await db_get_user_stakes(uid)
    if not stakes:
        return f"{E_LOCK} У тебя нет активных стейков.\n\nИспользуй /stake чтобы начать!", []

    blocks = [f"{E_LOCK} <b>Активные стейки</b>\n"]
    for s in stakes:
        t = STAKE_TIERS[s["tier"]]
        acc = stake_accrued(s)
        if s["lock_days"] == 0:
            status = "🔓 гибкий, можно вывести в любой момент"
        elif stake_is_matured(s):
            status = "✅ срок истёк — можно забрать полностью"
        else:
            status = f"⏳ осталось {fmt_cd(stake_time_left(s))}"
        blocks.append(
            f"\n<b>#{s['id']}</b>  {t['label']}  ({t['apr']*100:.0f}%)\n"
            f"💎 {fmt(s['amount'])} VRF  ·  накоплено <b>{fmt(acc)} VRF</b>\n"
            f"{status}"
        )
    return "".join(blocks), stakes


async def cmd_stakes(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    u = update.effective_user
    await db_ensure_user(u.id, u.username or "", u.first_name)
    text, stakes = await _stakes_text(u.id)
    await update.message.reply_text(text, parse_mode=ParseMode.HTML)
    for s in stakes:
        t = STAKE_TIERS[s["tier"]]
        await update.message.reply_text(
            f"#{s['id']}  {t['label']}  ·  {fmt(s['amount'])} VRF",
            reply_markup=_stake_row_kb(s),
        )


# ── API keys (личный доступ для разработчиков) ─────────

async def cmd_apikey(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    u = update.effective_user
    await db_ensure_user(u.id, u.username or "", u.first_name)
    label = " ".join(context.args) if context.args else ""
    key_id, raw = await db_create_api_key(u.id, label)
    await update.message.reply_text(
        f"🔑 <b>Новый API-ключ создан!</b>\n\n"
        f"<code>{raw}</code>\n\n"
        f"⚠️ Скопируй его сейчас — второй раз он не покажется.\n"
        f"Ключ даёт доступ <b>только к твоему аккаунту</b> "
        f"(баланс, покупка/продажа, стейкинг) через REST API.\n\n"
        f"Используй заголовок:\n<code>Authorization: Bearer {raw[:len(API_KEY_PREFIX)+6]}…</code>\n\n"
        f"📖 Документация: см. API_DOCS.md\n"
        f"🗑 Управление: /apikeys",
        parse_mode=ParseMode.HTML,
    )


async def cmd_apikeys(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    u = update.effective_user
    keys = await db_list_user_keys(u.id)
    if not keys:
        await update.message.reply_text(
            "🔑 У тебя пока нет API-ключей.\n\nСоздай командой /apikey [название]"
        )
        return
    lines = ["🔑 <b>Твои API-ключи</b>\n"]
    kb_rows = []
    for k in keys:
        used = f"использован {k['last_used_at'][:16].replace('T',' ')}" if k["last_used_at"] else "не использовался"
        lines.append(
            f"\n<b>#{k['id']}</b> {('· ' + k['label']) if k['label'] else ''}\n"
            f"<code>{k['key_prefix']}</code>\n"
            f"создан {k['created_at'][:16].replace('T',' ')} · {used}"
        )
        kb_rows.append([SBtn(f"🗑 Отозвать #{k['id']}", style="danger",
                             callback_data=f"ak:rev:{k['id']}")])
    await update.message.reply_text(
        "".join(lines), parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup(kb_rows),
    )


# ── Admin ────────────────────────────────────────────────

async def cmd_setprice(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        await update.message.reply_text("❌ Только для администраторов")
        return
    if not context.args:
        await update.message.reply_text("Использование: /setprice <цена>")
        return
    try:
        p = max(PRICE_MIN, min(PRICE_MAX, float(context.args[0].replace(",", "."))))
    except ValueError:
        await update.message.reply_text("❌ Некорректная цена")
        return
    async with market_lock:
        market["prev_price"] = market["price"]
        market["price"] = p
        market["fair"] = p
    await db_log_price(p)
    await update.message.reply_text(f"✅ Цена установлена: <b>{fmt_price(p)} USD</b>", parse_mode=ParseMode.HTML)


async def cmd_addusd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        await update.message.reply_text("❌ Только для администраторов")
        return
    if not update.message.reply_to_message or not context.args:
        await update.message.reply_text("Использование: /addusd <сумма> (ответом)")
        return
    try:
        amount = float(context.args[0].replace(",", "."))
    except ValueError:
        await update.message.reply_text("❌ Некорректная сумма")
        return
    target = update.message.reply_to_message.from_user
    await db_ensure_user(target.id, target.username or "", target.first_name)
    new_bal = await db_add_usd(target.id, amount)
    await update.message.reply_text(
        f"✅ Выдано <b>{fmt(amount)} USD</b> → {mention(target.id, target.first_name)}\n"
        f"💵 Баланс: {fmt(new_bal)} USD",
        parse_mode=ParseMode.HTML,
    )


async def cmd_addvrf(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        await update.message.reply_text("❌ Только для администраторов")
        return
    if not update.message.reply_to_message or not context.args:
        await update.message.reply_text("Использование: /addvrf <сумма> (ответом)")
        return
    try:
        amount = float(context.args[0].replace(",", "."))
    except ValueError:
        await update.message.reply_text("❌ Некорректная сумма")
        return
    target = update.message.reply_to_message.from_user
    await db_ensure_user(target.id, target.username or "", target.first_name)
    new_bal = await db_add_vrf(target.id, amount)
    await update.message.reply_text(
        f"✅ Выдано <b>{fmt(amount)} VRF</b> → {mention(target.id, target.first_name)}\n"
        f"{E_COIN} Баланс: {fmt(new_bal)} VRF",
        parse_mode=ParseMode.HTML,
    )


async def cmd_addscam(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        await update.message.reply_text("❌ Только для администраторов")
        return
    if not update.message.reply_to_message or not context.args:
        await update.message.reply_text("Использование: /addscam <сумма> (ответом)")
        return
    try:
        amount = float(context.args[0].replace(",", "."))
    except ValueError:
        await update.message.reply_text("❌ Некорректная сумма")
        return
    target = update.message.reply_to_message.from_user
    await db_ensure_user(target.id, target.username or "", target.first_name)
    new_bal = await db_add_scam(target.id, amount)
    await update.message.reply_text(
        f"✅ Выдано <b>{fmt_scam(amount)} SCAM</b> → {mention(target.id, target.first_name)}\n"
        f"🎭 Баланс: {fmt_scam(new_bal)} SCAM",
        parse_mode=ParseMode.HTML,
    )


async def cmd_checkassets(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Показывает прямо в Telegram, видит ли сервер assets/scam_bg.png и шрифты —
    чтобы не нужно было лезть в Shell/логи Railway для диагностики."""
    if not await is_admin(update.effective_user.id):
        await update.message.reply_text("❌ Только для администраторов")
        return
    lines = _asset_report_lines()
    text = "🔍 <b>Диагностика assets/</b>\n\n" + "\n".join(
        f"<code>{ln}</code>" for ln in lines
    )
    await update.message.reply_text(text, parse_mode=ParseMode.HTML)


async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        await update.message.reply_text("❌ Нет доступа")
        return
    async with aiosqlite.connect(DB_PATH) as db:
        async with db.execute("SELECT COUNT(*), SUM(usd), SUM(vrf) FROM users") as cur:
            n_users, sum_usd, sum_vrf = await cur.fetchone()
        async with db.execute("SELECT COUNT(*), SUM(amount) FROM stakes WHERE status='active'") as cur:
            n_stakes, sum_staked = await cur.fetchone()
    await update.message.reply_text(
        f"🛡️ <b>VRF Exchange — Admin</b>\n\n"
        f"👥 Пользователей: <b>{n_users or 0}</b>\n"
        f"💵 USD в обороте: <b>{fmt(sum_usd or 0)}</b>\n"
        f"{E_COIN} VRF в обороте: <b>{fmt(sum_vrf or 0)}</b>\n"
        f"{E_LOCK} Активных стейков: <b>{n_stakes or 0}</b> ({fmt(sum_staked or 0)} VRF)\n\n"
        f"💰 Текущая цена: <b>{fmt_price(market['price'])} USD</b>\n\n"
        f"<code>/setprice &lt;цена&gt;</code>\n"
        f"<code>/addusd &lt;сумма&gt;</code> (ответом)\n"
        f"<code>/addvrf &lt;сумма&gt;</code> (ответом)",
        parse_mode=ParseMode.HTML,
    )


async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    key = (update.effective_chat.id, update.effective_user.id)
    if pending_input.pop(key, None):
        await update.message.reply_text("✅ Ввод отменён")
    else:
        await update.message.reply_text("❌ Нечего отменять")


# ══════════════════════════════════════════════════════
#                CALLBACK HANDLER
# ══════════════════════════════════════════════════════

async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    data  = query.data
    who   = query.from_user
    cid   = query.message.chat_id

    # ── Exchange ──────────────────────────────────────
    if data.startswith("ex:"):
        parts = data.split(":")
        action = parts[1]

        if action == "refresh":
            uid = int(parts[2])
            await query.answer("🔄")
            rich_h, fb_h = await _market_cards()
            plain = __import__("re").sub(r"<[^>]+>", "", fb_h)[:4096]
            try:
                await query.edit_message_text(plain, parse_mode=ParseMode.HTML,
                                              reply_markup=_market_kb(uid))
            except TelegramError:
                pass
            return

        if action == "menu":
            uid  = int(parts[2])
            side = parts[3]
            if who.id != uid:
                await query.answer("❌ Это не твоё меню!", show_alert=True)
                return
            await query.answer()
            price = market["price"]
            if side == "buy":
                await query.edit_message_text(
                    f"{E_UP} <b>Купить VRF</b>\n\n💰 Цена: <b>{fmt_price(price)} USD</b>\n\n"
                    f"Выбери сумму в USD:",
                    parse_mode=ParseMode.HTML, reply_markup=_buy_kb(uid),
                )
            else:
                await query.edit_message_text(
                    f"{E_DOWN} <b>Продать VRF</b>\n\n💰 Цена: <b>{fmt_price(price)} USD</b>\n\n"
                    f"Выбери сумму в VRF:",
                    parse_mode=ParseMode.HTML, reply_markup=_sell_kb(uid),
                )
            return

        if action == "buy":
            uid = int(parts[2]); amount = float(parts[3])
            if who.id != uid:
                await query.answer("❌ Не твоя кнопка!", show_alert=True)
                return
            ok, msg = await _execute_buy(uid, amount)
            await query.answer("✅ Куплено!" if ok else "❌ Ошибка", show_alert=not ok)
            if ok:
                await context.bot.send_message(cid, msg, parse_mode=ParseMode.HTML)
            return

        if action == "sell":
            uid = int(parts[2]); amount = float(parts[3])
            if who.id != uid:
                await query.answer("❌ Не твоя кнопка!", show_alert=True)
                return
            ok, msg = await _execute_sell(uid, amount)
            await query.answer("✅ Продано!" if ok else "❌ Ошибка", show_alert=not ok)
            if ok:
                await context.bot.send_message(cid, msg, parse_mode=ParseMode.HTML)
            return

        if action in ("buyc", "sellc"):
            uid = int(parts[2])
            if who.id != uid:
                await query.answer("❌ Не твоя кнопка!", show_alert=True)
                return
            kind = "buy" if action == "buyc" else "sell"
            pending_input[(cid, uid)] = {
                "kind": kind, "expires": datetime.now() + timedelta(seconds=90),
            }
            unit = "USD" if kind == "buy" else "VRF"
            await query.answer("✍️ Напиши сумму в чат")
            try:
                await context.bot.send_message(
                    cid, f"✏️ {mention(uid, who.first_name)}, напиши сумму в <b>{unit}</b> ответом:",
                    parse_mode=ParseMode.HTML,
                    reply_markup=ForceReply(selective=True, input_field_placeholder=f"Например: 100"),
                )
            except TelegramError:
                pass
            return

        if action == "chart":
            uid = int(parts[2])
            await query.answer("📊 Строю график...")
            rows = await db_price_history(24)
            if len(rows) < 2:
                await context.bot.send_message(cid, "📊 Пока недостаточно данных для графика.")
                return
            loop = asyncio.get_running_loop()
            img = await loop.run_in_executor(None, _price_chart_sync, rows)
            if img:
                await context.bot.send_photo(
                    cid, photo=io.BytesIO(img),
                    caption=f"📊 <b>VRF/USD — 24ч</b>", parse_mode=ParseMode.HTML,
                )
            return

        await query.answer()
        return

    # ── Balance refresh ────────────────────────────────
    if data.startswith("ba:"):
        _, action, uid_s = data.split(":")
        uid = int(uid_s)
        if who.id != uid:
            await query.answer("❌ Не твоя кнопка!", show_alert=True)
            return
        await query.answer("🔄")
        rich_h, fb_h = await _balance_cards(uid)
        plain = __import__("re").sub(r"<[^>]+>", "", fb_h)[:4096]
        try:
            await query.edit_message_text(plain, parse_mode=ParseMode.HTML,
                                          reply_markup=_balance_kb(uid))
        except TelegramError:
            pass
        return

    # ── Staking ─────────────────────────────────────────
    if data.startswith("st:"):
        parts = data.split(":")
        action = parts[1]

        if action == "menu":
            uid = int(parts[2])
            if who.id != uid:
                await query.answer("❌ Не твоё меню!", show_alert=True)
                return
            await query.answer()
            uu = await db_get_user(uid)
            rows = "".join(f"• {t['label']} — {t['apr']*100:.0f}% год.\n" for t in STAKE_TIERS.values())
            await query.edit_message_text(
                f"{E_LOCK} <b>Стейкинг VRF</b>\n\nБаланс: <b>{fmt(uu['vrf'] if uu else 0)} VRF</b>\n\n{rows}",
                parse_mode=ParseMode.HTML, reply_markup=_stake_tier_kb(uid),
            )
            return

        if action == "tier":
            uid, tier = int(parts[2]), parts[3]
            if who.id != uid:
                await query.answer("❌ Не твоё меню!", show_alert=True)
                return
            t = STAKE_TIERS[tier]
            await query.answer(t["label"])
            uu = await db_get_user(uid)
            await query.edit_message_text(
                f"{t['label']}  ·  <b>{t['apr']*100:.0f}% годовых</b>\n"
                + (f"Штраф за досрочный вывод: {t['penalty']*100:.0f}%\n" if t["lock_days"] else "")
                + f"\nБаланс: <b>{fmt(uu['vrf'] if uu else 0)} VRF</b>\n\nСколько VRF положить?",
                parse_mode=ParseMode.HTML, reply_markup=_stake_amount_kb(uid, tier),
            )
            return

        if action == "amt":
            uid, tier, amt = int(parts[2]), parts[3], float(parts[4])
            if who.id != uid:
                await query.answer("❌ Не твоя кнопка!", show_alert=True)
                return
            ok, msg = await _do_stake(uid, tier, amt)
            await query.answer("✅ В стейк!" if ok else "❌ Ошибка", show_alert=not ok)
            if ok:
                await context.bot.send_message(cid, msg, parse_mode=ParseMode.HTML)
            return

        if action == "amtc":
            uid, tier = int(parts[2]), parts[3]
            if who.id != uid:
                await query.answer("❌ Не твоя кнопка!", show_alert=True)
                return
            pending_input[(cid, uid)] = {
                "kind": "stake", "tier": tier,
                "expires": datetime.now() + timedelta(seconds=90),
            }
            await query.answer("✍️ Напиши сумму в чат")
            try:
                await context.bot.send_message(
                    cid, f"✏️ {mention(uid, who.first_name)}, напиши сумму VRF для стейка ответом:",
                    parse_mode=ParseMode.HTML,
                    reply_markup=ForceReply(selective=True, input_field_placeholder="Например: 250"),
                )
            except TelegramError:
                pass
            return

        if action == "list":
            uid = int(parts[2])
            if who.id != uid:
                await query.answer("❌ Не твоё меню!", show_alert=True)
                return
            await query.answer()
            text, stakes = await _stakes_text(uid)
            await context.bot.send_message(cid, text, parse_mode=ParseMode.HTML)
            for s in stakes:
                t = STAKE_TIERS[s["tier"]]
                await context.bot.send_message(
                    cid, f"#{s['id']}  {t['label']}  ·  {fmt(s['amount'])} VRF",
                    reply_markup=_stake_row_kb(s),
                )
            return

        if action == "cl":  # claim flexible interest
            sid = int(parts[2])
            stake = await db_get_stake(sid)
            if not stake or stake["status"] != "active":
                await query.answer("❌ Стейк не найден", show_alert=True)
                return
            if stake["user_id"] != who.id:
                await query.answer("❌ Это не твой стейк!", show_alert=True)
                return
            acc = stake_accrued(stake)
            if acc < 0.000001:
                await query.answer("Пока нечего забирать", show_alert=True)
                return
            await db_touch_stake(sid, _now())
            new_bal = await db_add_vrf(who.id, acc)
            await query.answer(f"💠 +{fmt(acc)} VRF!", show_alert=True)
            await context.bot.send_message(
                cid,
                f"💠 <b>Проценты начислены!</b>\n\n"
                f"Стейк #{sid}: +<b>{fmt(acc)} VRF</b>\n"
                f"{E_COIN} Баланс: <b>{fmt(new_bal)} VRF</b>",
                parse_mode=ParseMode.HTML,
            )
            return

        if action == "un":  # unstake
            sid = int(parts[2])
            stake = await db_get_stake(sid)
            if not stake or stake["status"] != "active":
                await query.answer("❌ Стейк не найден", show_alert=True)
                return
            if stake["user_id"] != who.id:
                await query.answer("❌ Это не твой стейк!", show_alert=True)
                return

            if stake["lock_days"] == 0 or stake_is_matured(stake):
                acc = stake_accrued(stake)
                payout = stake["amount"] + acc
                await db_close_stake(sid, "withdrawn")
                new_bal = await db_add_vrf(who.id, payout)
                await query.answer("✅ Выведено!", show_alert=True)
                await context.bot.send_message(
                    cid,
                    f"✅ <b>Стейк #{sid} закрыт!</b>\n\n"
                    f"💎 Тело: {fmt(stake['amount'])} VRF\n"
                    f"💠 Проценты: +{fmt(acc)} VRF\n"
                    f"🏆 Итого: <b>{fmt(payout)} VRF</b>\n\n"
                    f"{E_COIN} Баланс: <b>{fmt(new_bal)} VRF</b>",
                    parse_mode=ParseMode.HTML,
                )
            else:
                # Early withdrawal — confirm penalty
                penalty_amt = stake["amount"] * stake["penalty"]
                get_back = stake["amount"] - penalty_amt
                await query.answer()
                await context.bot.send_message(
                    cid,
                    f"⚠️ <b>Досрочный вывод стейка #{sid}</b>\n\n"
                    f"Осталось: <b>{fmt_cd(stake_time_left(stake))}</b>\n"
                    f"Штраф: <b>{stake['penalty']*100:.0f}%</b> ({fmt(penalty_amt)} VRF)\n"
                    f"Ты получишь: <b>{fmt(get_back)} VRF</b> <i>(без процентов)</i>\n\n"
                    f"Подтвердить?",
                    parse_mode=ParseMode.HTML,
                    reply_markup=InlineKeyboardMarkup([[
                        SBtn("⚠️ Подтвердить", style="danger", callback_data=f"st:unc:{sid}"),
                        SBtn("Отмена", style="primary", callback_data=f"st:uncancel:{sid}"),
                    ]]),
                )
            return

        if action == "unc":  # confirmed early unstake
            sid = int(parts[2])
            stake = await db_get_stake(sid)
            if not stake or stake["status"] != "active":
                await query.answer("❌ Стейк уже закрыт", show_alert=True)
                return
            if stake["user_id"] != who.id:
                await query.answer("❌ Это не твой стейк!", show_alert=True)
                return
            penalty_amt = stake["amount"] * stake["penalty"]
            get_back = stake["amount"] - penalty_amt
            await db_close_stake(sid, "withdrawn_early")
            new_bal = await db_add_vrf(who.id, get_back)
            await query.answer("✅ Выведено досрочно")
            await query.edit_message_text(
                f"✅ <b>Стейк #{sid} выведен досрочно</b>\n\n"
                f"Получено: <b>{fmt(get_back)} VRF</b> <i>(штраф {fmt(penalty_amt)})</i>\n"
                f"{E_COIN} Баланс: <b>{fmt(new_bal)} VRF</b>",
                parse_mode=ParseMode.HTML,
            )
            return

        if action == "uncancel":
            await query.answer("Отменено")
            try:
                await query.edit_message_text("❌ Досрочный вывод отменён.")
            except TelegramError:
                pass
            return

        await query.answer()
        return

    # ── API keys ────────────────────────────────────────
    if data.startswith("ak:"):
        _, action, kid_s = data.split(":")
        kid = int(kid_s)
        if action == "rev":
            ok = await db_revoke_key(kid, who.id)
            if ok:
                await query.answer("🗑 Ключ отозван")
                try:
                    await query.edit_message_reply_markup(None)
                except TelegramError:
                    pass
            else:
                await query.answer("❌ Не найден или уже отозван", show_alert=True)
        else:
            await query.answer()
        return

    await query.answer()


async def _do_stake(uid: int, tier: str, amount: float) -> Tuple[bool, str]:
    if tier not in STAKE_TIERS:
        return False, "❌ Неверный тариф"
    if amount <= 0:
        return False, "❌ Сумма должна быть больше 0"
    u = await db_get_user(uid)
    if not u or u["vrf"] < amount:
        return False, f"❌ Недостаточно VRF! Есть: {fmt(u['vrf']) if u else 0}"

    await db_set_balances(uid, vrf=u["vrf"] - amount)
    sid = await db_create_stake(uid, tier, amount)
    t = STAKE_TIERS[tier]

    return True, (
        f"{E_LOCK} <b>Стейк #{sid} открыт!</b>\n\n"
        f"{t['label']}  ·  <b>{t['apr']*100:.0f}% годовых</b>\n"
        f"💎 Сумма: <b>{fmt(amount)} VRF</b>\n"
        + (f"⏱ Срок: {t['lock_days']} дн.\n" if t['lock_days'] else "🔓 Снятие в любой момент\n")
        + f"\nСмотри /stakes чтобы забрать проценты или вывести."
    )


# ══════════════════════════════════════════════════════
#           MESSAGE HANDLER — custom amount replies
# ══════════════════════════════════════════════════════

async def _execute_scam_transfer(context, chat_id: int, cmd_msg_id: int,
                                  recipient_msg, sender, recipient, amount: float) -> None:
    """Deduct SCAM from sender, credit recipient, send a generated receipt image
    as a reply-with-quote pointing at the recipient's original message (native
    Telegram quote — reply_parameters.quote), not a formatting trick."""
    if recipient.id == sender.id:
        await context.bot.send_message(chat_id, "❌ Нельзя переводить SCAM самому себе!",
                                       reply_to_message_id=cmd_msg_id)
        return
    if amount <= 0:
        await context.bot.send_message(chat_id, "❌ Сумма должна быть больше 0",
                                       reply_to_message_id=cmd_msg_id)
        return

    await db_ensure_user(sender.id, sender.username or "", sender.first_name)
    await db_ensure_user(recipient.id, getattr(recipient, "username", "") or "", recipient.first_name)

    su = await db_get_user(sender.id)
    if not su or su["scam"] < amount:
        await context.bot.send_message(
            chat_id,
            f"❌ Недостаточно SCAM! Есть: <b>{fmt_scam(su['scam'] if su else 0)}</b>",
            parse_mode=ParseMode.HTML, reply_to_message_id=cmd_msg_id,
        )
        return

    await db_set_balances(sender.id, scam=su["scam"] - amount)
    await db_add_scam(recipient.id, amount)
    await db_log_scam_transfer(sender.id, recipient.id, amount)

    loop = asyncio.get_running_loop()
    img = await loop.run_in_executor(None, _scam_card_image_sync, amount)

    # "#SCAM" — кликабельная ссылка на самого бота; отправитель/получатель —
    # кликабельные ссылки на профиль (tg://user?id=...); ⭐️ перед суммой.
    bot_username = getattr(context.bot, "username", None)
    scam_tag = f'<a href="https://t.me/{bot_username}">#SCAM</a>' if bot_username else "#SCAM"

    caption = (
        f"<b>{scam_tag} {mention(sender.id, sender.first_name)} отправил(а) ⭐️ "
        f"{fmt_scam(amount)} SCAM для {mention(recipient.id, recipient.first_name)}</b>"
    )

    # Цитата — короткий фрагмент исходного сообщения получателя (ровно то,
    # на которое ответили командой "пер"). Должна быть точной подстрокой,
    # поэтому просто берём префикс, а не произвольно обрезанный текст.
    quote_src = (getattr(recipient_msg, "text", None) or getattr(recipient_msg, "caption", None) or "").strip()
    quote_text = quote_src[:250] if quote_src else None

    reply_kwargs = {"message_id": recipient_msg.message_id}
    if quote_text:
        reply_kwargs["quote"] = quote_text
    reply_params = ReplyParameters(**reply_kwargs)

    try:
        if img:
            await context.bot.send_photo(
                chat_id, photo=io.BytesIO(img), caption=caption,
                parse_mode=ParseMode.HTML, reply_parameters=reply_params,
            )
        else:
            await context.bot.send_message(chat_id, caption, parse_mode=ParseMode.HTML,
                                           reply_parameters=reply_params)
    except TelegramError:
        # Если реплай/цитата вдруг невалидны (например, исходное сообщение
        # успели удалить) — отправляем обычным сообщением, чтобы перевод
        # не "потерялся" для пользователя.
        if img:
            await context.bot.send_photo(chat_id, photo=io.BytesIO(img), caption=caption,
                                         parse_mode=ParseMode.HTML)
        else:
            await context.bot.send_message(chat_id, caption, parse_mode=ParseMode.HTML)


async def on_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.message or not update.effective_user:
        return
    u = update.effective_user
    if u.is_bot:
        return
    cid = update.effective_chat.id
    text_raw = (update.message.text or "").strip()

    # ── "пер <сумма>" — перевод токена SCAM (ответом на сообщение получателя) ──
    parts = text_raw.split()
    if parts and parts[0].lower() in ("пер", "перевод", "sendscam", "трансфер"):
        if not update.message.reply_to_message or update.message.reply_to_message.from_user.is_bot:
            await update.message.reply_text(
                "❌ Ответь на сообщение получателя, чтобы перевести SCAM.\n"
                "Использование: <code>пер 0,048</code> (ответом)",
                parse_mode=ParseMode.HTML,
            )
            return
        if len(parts) < 2:
            await update.message.reply_text(
                "❌ Укажи сумму: <code>пер 0,048</code>", parse_mode=ParseMode.HTML,
            )
            return
        amount_str = parts[1].replace(" ", "").replace(",", ".")
        try:
            amount = float(amount_str)
        except ValueError:
            await update.message.reply_text("❌ Некорректная сумма SCAM")
            return

        recipient = update.message.reply_to_message.from_user
        await _execute_scam_transfer(
            context, cid, update.message.message_id,
            update.message.reply_to_message, u, recipient, amount,
        )
        return

    key = (cid, u.id)
    pend = pending_input.get(key)
    if not pend:
        return

    if datetime.now() > pend["expires"]:
        pending_input.pop(key, None)
        return

    text = text_raw.replace(" ", "").replace(",", ".")
    try:
        amount = float(text)
    except ValueError:
        await update.message.reply_text("❌ Введи число. Попробуй ещё раз или /cancel")
        return

    pending_input.pop(key, None)
    kind = pend["kind"]

    if kind == "buy":
        ok, msg = await _execute_buy(u.id, amount)
        await update.message.reply_text(msg, parse_mode=ParseMode.HTML)
    elif kind == "sell":
        ok, msg = await _execute_sell(u.id, amount)
        await update.message.reply_text(msg, parse_mode=ParseMode.HTML)
    elif kind == "stake":
        ok, msg = await _do_stake(u.id, pend["tier"], amount)
        await update.message.reply_text(msg, parse_mode=ParseMode.HTML)


# ══════════════════════════════════════════════════════
#                       MAIN
# ══════════════════════════════════════════════════════

# ══════════════════════════════════════════════════════
#           PUBLIC REST API  🌐  (для сторонних разработчиков)
# ══════════════════════════════════════════════════════
# Работает независимо от long-polling бота (свой event loop в отдельном
# потоке), поднимается на 0.0.0.0:$PORT. Railway нужно включить
# Public Networking для этого порта, чтобы API был доступен извне.

def _json_resp(data, status: int = 200):
    from aiohttp import web as _web
    return _web.json_response(data, status=status,
                              dumps=lambda o: json.dumps(o, ensure_ascii=False))


def _err(msg: str, status: int = 400):
    return _json_resp({"ok": False, "error": msg}, status)


async def _api_auth(request) -> Optional[dict]:
    """Extract & validate Bearer token, return the owning user's row or None."""
    auth = request.headers.get("Authorization", "")
    token = auth[7:].strip() if auth.lower().startswith("bearer ") else ""
    if not token:
        token = request.headers.get("X-API-Key", "").strip()
    if not token:
        return None
    return await db_get_user_from_key(token)


async def _rl_middleware(app, handler):
    async def middleware(request):
        from aiohttp import web as _web
        bucket = f"ip:{request.remote}"
        if _rate_limited(bucket):
            return _err("Rate limit exceeded, try again later", 429)
        try:
            return await handler(request)
        except _web.HTTPException:
            raise
        except Exception:
            log.exception("API handler error: %s %s", request.method, request.path)
            return _err("Internal server error", 500)
    return middleware


def _cors_headers() -> dict:
    return {
        "Access-Control-Allow-Origin": API_CORS_ORIGIN,
        "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
        "Access-Control-Allow-Headers": "Content-Type, Authorization, X-API-Key",
    }


async def _cors_middleware(app, handler):
    async def middleware(request):
        from aiohttp import web as _web
        if request.method == "OPTIONS":
            return _web.Response(status=204, headers=_cors_headers())
        resp = await handler(request)
        resp.headers.update(_cors_headers())
        return resp
    return middleware


# ── Public endpoints ───────────────────────────────────

async def api_root(request):
    return _json_resp({
        "ok": True,
        "name": "VRF Exchange API",
        "version": "v1",
        "docs": "See API_DOCS.md in the repository",
        "endpoints": [
            "GET  /api/v1/price",
            "GET  /api/v1/price/history?hours=24",
            "GET  /api/v1/stats",
            "GET  /api/v1/tiers",
            "GET  /api/v1/me                (auth)",
            "POST /api/v1/trade/buy         (auth) {usd_amount}",
            "POST /api/v1/trade/sell        (auth) {vrf_amount}",
            "GET  /api/v1/stakes            (auth)",
            "POST /api/v1/stakes            (auth) {tier, amount}",
            "POST /api/v1/stakes/{id}/claim (auth)",
            "POST /api/v1/stakes/{id}/unstake (auth)",
        ],
    })


async def api_health(request):
    return _json_resp({"ok": True, "status": "up", "ts": _now()})


async def api_price(request):
    price = market["price"]
    p24 = await db_price_at(24)
    lo24, hi24 = await db_price_range(24)
    return _json_resp({
        "ok": True,
        "pair": "VRF/USD",
        "price": price,
        "prev_price": market["prev_price"],
        "change_24h_pct": round(_change_pct(p24 or price, price), 4),
        "high_24h": hi24 if hi24 is not None else price,
        "low_24h": lo24 if lo24 is not None else price,
        "fee_pct": TRADE_FEE_PCT,
        "ts": _now(),
    })


async def api_price_history(request):
    try:
        hours = min(720, max(1, int(request.query.get("hours", 24))))
    except ValueError:
        return _err("hours must be an integer")
    rows = await db_price_history(hours)
    return _json_resp({
        "ok": True,
        "hours": hours,
        "points": [{"ts": r[0], "price": r[1]} for r in rows],
    })


async def api_stats(request):
    async with aiosqlite.connect(DB_PATH) as db:
        async with db.execute("SELECT COUNT(*), SUM(usd), SUM(vrf) FROM users") as cur:
            n_users, sum_usd, sum_vrf = await cur.fetchone()
        async with db.execute("SELECT COUNT(*), SUM(amount) FROM stakes WHERE status='active'") as cur:
            n_stakes, sum_staked = await cur.fetchone()
        async with db.execute("SELECT COUNT(*) FROM trades") as cur:
            n_trades = (await cur.fetchone())[0]
    return _json_resp({
        "ok": True,
        "users": n_users or 0,
        "usd_in_circulation": sum_usd or 0,
        "vrf_in_circulation": sum_vrf or 0,
        "active_stakes": n_stakes or 0,
        "vrf_staked": sum_staked or 0,
        "total_trades": n_trades or 0,
        "price": market["price"],
    })


async def api_tiers(request):
    return _json_resp({
        "ok": True,
        "tiers": [
            {"key": k, "label": t["label"], "apr": t["apr"],
             "lock_days": t["lock_days"], "early_penalty": t["penalty"]}
            for k, t in STAKE_TIERS.items()
        ],
    })


# ── Authenticated endpoints (personal API key) ─────────

async def api_me(request):
    user = await _api_auth(request)
    if not user:
        return _err("Invalid or missing API key", 401)
    price = market["price"]
    stakes = await db_get_user_stakes(user["user_id"])
    return _json_resp({
        "ok": True,
        "user_id": user["user_id"],
        "usd": user["usd"],
        "vrf": user["vrf"],
        "scam": user["scam"],
        "vrf_value_usd": round(user["vrf"] * price, 6),
        "staked_vrf": sum(s["amount"] for s in stakes),
        "pending_rewards_vrf": round(sum(stake_accrued(s) for s in stakes), 6),
    })


async def api_trade_buy(request):
    user = await _api_auth(request)
    if not user:
        return _err("Invalid or missing API key", 401)
    if _rate_limited(f"trade:{user['user_id']}"):
        return _err("Rate limit exceeded", 429)
    try:
        body = await request.json()
        amount = float(body["usd_amount"])
    except Exception:
        return _err('Body must be JSON: {"usd_amount": number}')
    ok, msg = await _execute_buy(user["user_id"], amount)
    if not ok:
        return _err(msg.lstrip("❌ ").strip(), 400)
    u2 = await db_get_user(user["user_id"])
    return _json_resp({"ok": True, "usd": u2["usd"], "vrf": u2["vrf"], "price": market["price"]})


async def api_trade_sell(request):
    user = await _api_auth(request)
    if not user:
        return _err("Invalid or missing API key", 401)
    if _rate_limited(f"trade:{user['user_id']}"):
        return _err("Rate limit exceeded", 429)
    try:
        body = await request.json()
        amount = float(body["vrf_amount"])
    except Exception:
        return _err('Body must be JSON: {"vrf_amount": number}')
    ok, msg = await _execute_sell(user["user_id"], amount)
    if not ok:
        return _err(msg.lstrip("❌ ").strip(), 400)
    u2 = await db_get_user(user["user_id"])
    return _json_resp({"ok": True, "usd": u2["usd"], "vrf": u2["vrf"], "price": market["price"]})


def _stake_json(s: dict) -> dict:
    return {
        "id": s["id"], "tier": s["tier"], "amount": s["amount"], "apr": s["apr"],
        "lock_days": s["lock_days"], "start_ts": s["start_ts"],
        "accrued_vrf": round(stake_accrued(s), 6),
        "matured": stake_is_matured(s),
        "seconds_left": stake_time_left(s),
    }


async def api_stakes_list(request):
    user = await _api_auth(request)
    if not user:
        return _err("Invalid or missing API key", 401)
    stakes = await db_get_user_stakes(user["user_id"])
    return _json_resp({"ok": True, "stakes": [_stake_json(s) for s in stakes]})


async def api_stakes_create(request):
    user = await _api_auth(request)
    if not user:
        return _err("Invalid or missing API key", 401)
    try:
        body = await request.json()
        tier = str(body["tier"])
        amount = float(body["amount"])
    except Exception:
        return _err('Body must be JSON: {"tier": string, "amount": number}')
    ok, msg = await _do_stake(user["user_id"], tier, amount)
    if not ok:
        return _err(msg.lstrip("❌ ").strip(), 400)
    stakes = await db_get_user_stakes(user["user_id"])
    return _json_resp({"ok": True, "stakes": [_stake_json(s) for s in stakes]}, 201)


async def api_stake_claim(request):
    user = await _api_auth(request)
    if not user:
        return _err("Invalid or missing API key", 401)
    try:
        sid = int(request.match_info["id"])
    except ValueError:
        return _err("Invalid stake id")
    stake = await db_get_stake(sid)
    if not stake or stake["status"] != "active" or stake["user_id"] != user["user_id"]:
        return _err("Stake not found", 404)
    acc = stake_accrued(stake)
    if acc <= 0:
        return _err("Nothing to claim yet", 400)
    await db_touch_stake(sid, _now())
    new_bal = await db_add_vrf(user["user_id"], acc)
    return _json_resp({"ok": True, "claimed_vrf": round(acc, 6), "vrf_balance": new_bal})


async def api_stake_unstake(request):
    user = await _api_auth(request)
    if not user:
        return _err("Invalid or missing API key", 401)
    try:
        sid = int(request.match_info["id"])
    except ValueError:
        return _err("Invalid stake id")
    stake = await db_get_stake(sid)
    if not stake or stake["status"] != "active" or stake["user_id"] != user["user_id"]:
        return _err("Stake not found", 404)

    if stake["lock_days"] == 0 or stake_is_matured(stake):
        acc = stake_accrued(stake)
        payout = stake["amount"] + acc
        await db_close_stake(sid, "withdrawn")
        new_bal = await db_add_vrf(user["user_id"], payout)
        return _json_resp({
            "ok": True, "early": False, "principal": stake["amount"],
            "interest": round(acc, 6), "payout_vrf": round(payout, 6),
            "vrf_balance": new_bal,
        })

    body = {}
    try:
        body = await request.json()
    except Exception:
        pass
    if not body.get("confirm_early"):
        penalty_amt = stake["amount"] * stake["penalty"]
        return _err(
            f"Lock not expired ({stake_time_left(stake)}s left). "
            f"Early withdrawal forfeits interest and applies a "
            f"{stake['penalty']*100:.0f}% penalty ({penalty_amt:.4f} VRF). "
            f'Resend with {{"confirm_early": true}} to proceed.',
            409,
        )
    penalty_amt = stake["amount"] * stake["penalty"]
    get_back = stake["amount"] - penalty_amt
    await db_close_stake(sid, "withdrawn_early")
    new_bal = await db_add_vrf(user["user_id"], get_back)
    return _json_resp({
        "ok": True, "early": True, "penalty_vrf": round(penalty_amt, 6),
        "payout_vrf": round(get_back, 6), "vrf_balance": new_bal,
    })


def _build_api_app():
    from aiohttp import web as _web
    app = _web.Application(middlewares=[_cors_middleware, _rl_middleware])
    app.router.add_get("/", api_root)
    app.router.add_get("/health", api_health)
    app.router.add_get("/api/v1", api_root)
    app.router.add_get("/api/v1/price", api_price)
    app.router.add_get("/api/v1/price/history", api_price_history)
    app.router.add_get("/api/v1/stats", api_stats)
    app.router.add_get("/api/v1/tiers", api_tiers)
    app.router.add_get("/api/v1/me", api_me)
    app.router.add_post("/api/v1/trade/buy", api_trade_buy)
    app.router.add_post("/api/v1/trade/sell", api_trade_sell)
    app.router.add_get("/api/v1/stakes", api_stakes_list)
    app.router.add_post("/api/v1/stakes", api_stakes_create)
    app.router.add_post("/api/v1/stakes/{id}/claim", api_stake_claim)
    app.router.add_post("/api/v1/stakes/{id}/unstake", api_stake_unstake)
    return app


def _run_api_server() -> None:
    """Runs the aiohttp REST API in its own event loop / background thread,
    since the bot's main thread is blocked inside app.run_polling()."""
    async def _serve():
        try:
            from aiohttp import web as _web
        except ImportError:
            log.warning("aiohttp not installed — REST API disabled. pip install aiohttp")
            return
        web_app = _build_api_app()
        runner = _web.AppRunner(web_app)
        await runner.setup()
        site = _web.TCPSite(runner, "0.0.0.0", API_PORT)
        await site.start()
        log.info("REST API listening on 0.0.0.0:%s  (see API_DOCS.md)", API_PORT)
        await asyncio.Event().wait()

    asyncio.run(_serve())


async def on_startup(app: Application) -> None:
    await db_init()
    _log_asset_diagnostics()
    from telegram import BotCommand, BotCommandScopeDefault
    cmds = [
        BotCommand("start",   "🏠 Старт / Главное меню"),
        BotCommand("market",  "💹 Текущая цена VRF"),
        BotCommand("price",   "💰 Быстрая цена"),
        BotCommand("chart",   "📊 График цены [часов]"),
        BotCommand("buy",     "🟢 Купить VRF за USD"),
        BotCommand("sell",    "🔴 Продать VRF за USD"),
        BotCommand("stake",   "🔒 Стейкинг VRF"),
        BotCommand("stakes",  "📋 Мои активные стейки"),
        BotCommand("balance", "👤 Баланс и активы"),
        BotCommand("apikey",  "🔑 Создать API-ключ для разработчиков"),
        BotCommand("apikeys", "🗂 Мои API-ключи"),
        BotCommand("cancel",  "🚫 Отменить ввод суммы"),
        BotCommand("help",    "ℹ️ Помощь"),
    ]
    try:
        await app.bot.set_my_commands(cmds, scope=BotCommandScopeDefault())
    except Exception:
        pass
    app.create_task(_price_ticker_loop())

    t = threading.Thread(target=_run_api_server, daemon=True, name="vrf-api-server")
    t.start()

    log.info("VRF Exchange Bot is online!")


def main() -> None:
    if not BOT_TOKEN:
        log.critical("BOT_TOKEN environment variable is not set!")
        raise SystemExit(1)

    app = Application.builder().token(BOT_TOKEN).post_init(on_startup).build()

    app.add_handler(CommandHandler("start",   cmd_start))
    app.add_handler(CommandHandler("help",    cmd_help))
    app.add_handler(CommandHandler("market",  cmd_market))
    app.add_handler(CommandHandler("price",   cmd_price))
    app.add_handler(CommandHandler("chart",   cmd_chart))
    app.add_handler(CommandHandler("buy",     cmd_buy))
    app.add_handler(CommandHandler("sell",    cmd_sell))
    app.add_handler(CommandHandler("stake",   cmd_stake))
    app.add_handler(CommandHandler("stakes",  cmd_stakes))
    app.add_handler(CommandHandler("balance", cmd_balance))
    app.add_handler(CommandHandler("apikey",  cmd_apikey))
    app.add_handler(CommandHandler("apikeys", cmd_apikeys))
    app.add_handler(CommandHandler("cancel",  cmd_cancel))

    app.add_handler(CommandHandler("admin",       cmd_admin))
    app.add_handler(CommandHandler("checkassets", cmd_checkassets))
    app.add_handler(CommandHandler("setprice", cmd_setprice))
    app.add_handler(CommandHandler("addusd",   cmd_addusd))
    app.add_handler(CommandHandler("addvrf",   cmd_addvrf))
    app.add_handler(CommandHandler("addscam",  cmd_addscam))

    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_message))

    log.info("Starting polling...")
    app.run_polling(
        drop_pending_updates=True,
        allowed_updates=["message", "callback_query"],
    )


if __name__ == "__main__":
    main()
