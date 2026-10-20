# v2026-09-30 Arena: self-healing DB + 24h hero/trending + SA title-only + P1(security,SEO,a11y) + P1.1(headings) + P1.2(gemini-3.5-model) + P2(no-starvation) + P2.1(neon-cu-saver) + P3(v7: robots+sitemap+canonical+og+twitter+jsonld+favicon+aria+focus)
"""
Sports News Aggregator - Single-file, self-updating build.

Everything runs from THIS file:
  * Flask web portal + secret admin dashboard + internal article reader
  * RSS fetcher / per-article junk filter / sports localization / translation

Key deployment choices:
  * DATABASE_URL, when set, -> PostgreSQL stores articles persistently across
    Render restarts and redeploys. Without it, local fallback is SQLite/RAM.
    One shared connection guarded by a global RLock so the web request threads
    and the background fetcher thread share data safely.
  * The fetcher runs on a BACKGROUND THREAD (autopilot). A token-protected HTTP route
    (/osvezi-vesti-777) also forces a cycle inside the request thread, which is
    the reliable way to refill the volatile DB on Render Free.

If DATABASE_URL is not set, the local SQLite/RAM fallback is volatile and
reseeds from RSS on every process start. Configure Render PostgreSQL in production.

Env vars (all optional):
    DATABASE_URL             PostgreSQL connection URL (required for persistent production data)
    SECRET_KEY               Flask secret (set in production!)
    REFRESH_TOKEN            secret token required by the cron refresh route
    ADMIN_PASSWORD           admin password (simple setup; use a hash when possible)
    ADMIN_PASSWORD_HASH      optional Werkzeug password hash (preferred over plain password)
    PORT                     HTTP port (default 5000)
    TRANSLATION_MODE         "ai" (default, uses Gemini) or "free" (Google translate)
    GEMINI_API_KEY           Google AI Studio key -> full 2-3 paragraph articles.
                             If missing/unset, the app safely falls back to free.
    GEMINI_MODEL             Gemini model (default "gemini-2.5-flash")
    GOOGLE_API_KEY/GOOGLE_CX optional Google image search; requires
                             ALLOW_EXTERNAL_IMAGES=1 and verified image rights.
    MAX_TRANSLATIONS_PER_RUN default 1 per cycle
    FEED_TIMEOUT_SECONDS      timeout for each RSS request (default 8)
    MAX_FEEDS_PER_FETCH       RSS feeds per cron call (default 2)
    MAX_ENTRIES_PER_FEED      newest entries accepted from each feed (3)
    HOME_CATEGORY_LIMIT       newest cards per category on homepage (default 12)
    ARCHIVE_PAGE_SIZE         archive cards per page (default 24)
    ADMIN_PAGE_SIZE           admin list cards per page (default 40)
    AUTO_ARCHIVE_DAYS         age for automatic non-destructive archive (30)
    FETCH_INTERVAL_SECONDS    autopilot loop interval (default 600)
    RUN_FETCHER              "0" to disable the background fetcher
    AUTOPILOT_PUBLISH        "1" (default) auto-publishes every translated
                             article live; "0" holds everything in the admin
                             "Na čekanju" queue for manual approval.

No AI SDK is needed: Gemini is called over plain HTTPS with urllib.

Run:
    pip install -r requirements.txt
    python app.py
"""

import calendar
import html
import hmac
import json
import os
import re
import secrets
import socket
import sqlite3
import threading
import time
import urllib.parse
import urllib.request
from functools import wraps
from typing import Any

import feedparser

try:
    import psycopg
    from psycopg.rows import dict_row
except ImportError:  # local SQLite mode can still run without psycopg installed
    psycopg = None
    dict_row = None

from flask import (
    Flask, flash, redirect, render_template_string, request, session, url_for,
)
import base64
from werkzeug.security import check_password_hash

try:  # free translation mode (deep-translator)
    from deep_translator import GoogleTranslator
except ImportError:  # pragma: no cover
    GoogleTranslator = None

# Fallback socket timeout. RSS requests below also pass an explicit timeout.
socket.setdefaulttimeout(10)

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

# Production uses Render PostgreSQL through DATABASE_URL. SQLite remains as a
# local fallback so the app can still be run without a database service.
DATABASE_URL = (
    os.environ.get("DATABASE_URL")
    or os.environ.get("POSTGRES_URL")
    or ""
).strip()
DB_PATH = os.environ.get("DB_PATH", ":memory:")
DB_DIALECT = "postgres" if DATABASE_URL else "sqlite"

ADMIN_PATH = "/admin-tajna-kontrola-777"    # admin entry URL
ADMIN_LOGIN_PATH = ADMIN_PATH + "/login"
ADMIN_LOGOUT_PATH = ADMIN_PATH + "/logout"
REFRESH_PATH = "/osvezi-vesti-777"          # cron refresh trigger

TRANSLATION_MODE = (os.environ.get("TRANSLATION_MODE") or "ai").strip() or "ai"    # "ai" | "free"
TARGET_LANGUAGE = "sr"
# Google AI Studio (Gemini) free tier. No external SDK needed - plain HTTPS call.
GEMINI_MODEL = (os.environ.get("GEMINI_MODEL") or "").strip() or "gemini-3.5-flash-lite"  # prazno = default; 2.5-flash povucen -> 404
GEMINI_API_URL = (
    "https://generativelanguage.googleapis.com/v1beta/models/"
    "{model}:generateContent?key={key}"
)
# Temporary Render-safe default: one translation per refresh cycle.
# Increase only after the worker/queue architecture is in place.
MAX_TRANSLATIONS_PER_RUN = int(os.environ.get("MAX_TRANSLATIONS_PER_RUN", "1"))

# Anti-zastoj: srcevo napustanje van-delijum-prevod-carstva (queue starvation).
# Kapija posmatra samo vesti koje SADA mogu u ciklus; one u grace-periodi
# (next_retry_at u buducnosti) ne blokiraju fetch. Ako vest sakupi dovoljno
# neuspeha, parkiramo je 30 dana (retry logika je i dalje vraca kad se
# prevodi oporave) — jedna otrovana vest nikada ne sme zarobiti ceo sajt.
PARK_AFTER_ATTEMPTS = int(os.environ.get("PARK_AFTER_ATTEMPTS", "30"))
PARK_PARKING_SECONDS = int(os.environ.get("PARK_PARKING_SECONDS", str(30 * 86400)))
# AUTOMATIC publishing: every successfully translated article goes live on its
# own as a 'standard' card. Placement still follows the priority criteria
# (Zvezda p=2 -> hero, etc.) and the admin panel ALWAYS stays available so any
# live article can be edited, repositioned (hero/trending) or deleted by hand.
# Set AUTOPILOT_PUBLISH=0 to fall back to full manual approval (Na čekanju queue).
AUTOPILOT_PUBLISH = os.environ.get("AUTOPILOT_PUBLISH", "1") != "0"
FETCH_INTERVAL_SECONDS = int(os.environ.get("FETCH_INTERVAL_SECONDS", "600"))

# Editorial freshness windows: Hero and "Najcitanije" slots are released
# after this age so an old pinned story can never block the homepage.
HERO_MAX_AGE_HOURS = float(os.environ.get("HERO_MAX_AGE_HOURS", "24"))
TRENDING_MAX_AGE_HOURS = float(os.environ.get("TRENDING_MAX_AGE_HOURS", "24"))
RUN_FETCHER = os.environ.get("RUN_FETCHER", "1") != "0"
REFRESH_TOKEN = os.environ.get("REFRESH_TOKEN", "")
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "")
ADMIN_PASSWORD_HASH = os.environ.get("ADMIN_PASSWORD_HASH", "")
FEED_TIMEOUT_SECONDS = int(os.environ.get("FEED_TIMEOUT_SECONDS", "8"))
# Conservative default for a synchronous HTTP cron request: two feeds at a time.
MAX_FEEDS_PER_FETCH = int(os.environ.get("MAX_FEEDS_PER_FETCH", "2"))
# Prevent one high-volume feed from filling the entire translation queue.
MAX_ENTRIES_PER_FEED = max(1, int(os.environ.get("MAX_ENTRIES_PER_FEED", "3")))
# Homepage stays concise while the full history remains available in /arhiva.
HOME_CATEGORY_LIMIT = max(1, int(os.environ.get("HOME_CATEGORY_LIMIT", "12")))
ARCHIVE_PAGE_SIZE = max(1, int(os.environ.get("ARCHIVE_PAGE_SIZE", "24")))
ADMIN_PAGE_SIZE = max(1, int(os.environ.get("ADMIN_PAGE_SIZE", "40")))
AUTO_ARCHIVE_DAYS = max(0, int(os.environ.get("AUTO_ARCHIVE_DAYS", "30")))
# External image search is opt-in only. Google results are not assumed to be
# licensed for republication; keep the owned inline SVG fallback by default.
ALLOW_EXTERNAL_IMAGES = os.environ.get("ALLOW_EXTERNAL_IMAGES", "0") == "1"

# Full browser User-Agent so foreign CDNs/servers do not block our requests.
BROWSER_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"
)

# Feeds with "lang": "sr" are already in Serbian -> shown directly, never sent
# through the translator (avoids garbling club names). Every URL below was
# live-tested to actually return articles (homepage URLs return 0 in feedparser).
# The operator must verify each feed's reuse terms; RSS attribution is not a
# licence. Keep the stored material as a factual, attributed news brief.
SPORTS_FEEDS = [
    # DOMAĆI TEREN - profesionalne domaće redakcije (već na srpskom)
    {"name": "Sportski žurnal", "url": "http://www.zurnal.rs/rss", "lang": "sr"},
    {"name": "Telegraf Sport", "url": "https://www.telegraf.rs/rss/sport", "lang": "sr"},
    # EVROPSKI GIGANTI (La Liga, Serija A, Premijer liga, Liga šampiona, transferi)
    {"name": "Marca (Španija)", "url": "https://e00-marca.uecdn.es/rss/futbol.xml", "lang": "es", "category": "football"},
    {"name": "AS (Španija)", "url": "https://as.com/rss/futbol/portada.xml", "lang": "es", "category": "football"},
    {"name": "Gazzetta (Italija)", "url": "https://www.gazzetta.it/rss/calcio.xml", "lang": "it", "category": "football"},
    {"name": "Sky Sports (Engleska)", "url": "https://www.skysports.com/rss/12040", "lang": "en", "category": "football"},
    {"name": "Football Italia", "url": "https://football-italia.net/feed/", "lang": "en", "category": "football"},
    # KOŠARKA (NBA + Evroliga)
    {"name": "Eurohoops", "url": "https://www.eurohoops.net/feed/", "lang": "en", "category": "basketball"},
    {"name": "Sportando", "url": "https://sportando.basketball/en/feed/", "lang": "en", "category": "basketball"},
    # TENIS
    {"name": "ESPN Tennis", "url": "https://www.espn.com/espn/rss/tennis/news", "lang": "en", "category": "tennis"},
    {"name": "ATP Tour", "url": "https://www.atptour.com/en/media/rss-feed", "lang": "en", "category": "tennis"},
    # BOKS
    {"name": "BoxingScene", "url": "https://www.boxingscene.com/rss/news.xml", "lang": "en", "category": "boxing"},
    # JUŽNOAMERIČKA MAGIJA (Argentina + Brazil)
    {"name": "Olé (Argentina)", "url": "https://www.ole.com.ar/rss/", "lang": "es"},
    {"name": "Clarín (Argentina)", "url": "https://www.clarin.com/rss/deportes/", "lang": "es"},
    {"name": "Globo Esporte (Brazil)", "url": "https://ge.globo.com/dynamo/rss2.xml", "lang": "pt"},
]

# The cron route fetches only a rotating subset of feeds per call. This keeps a
# slow or unavailable feed from making every refresh request wait for all feeds.
_feed_cursor = 0
_feed_cursor_lock = threading.Lock()

# ABSOLUTE priority (priority=2): an article mentioning Crvena zvezda always
# claims the Hero ("Udarna vest") slot, ahead of any general foreign news.
STAR_KEYWORDS = [
    "Crvena zvezda", "Red Star", "Marakana", "Marakani", "Marakanu",
    "Zvezda", "Zvezdini", "Zvezdine", "Zvezdin", "Zvezdu", "Zvezde",
    "Zvezdi", "crveno-beli", "crveno-belim",
]

HIGH_PRIORITY_KEYWORDS = [
    "Messi", "Maradona", "Boca Juniors", "Boca", "River Plate", "River",
    "Transfer", "Fichaje", "Refuerzo", "Partizan",
    "Radnicki", "Radnički", "Vojvodina", "Voša", "Neymar", "Ronaldinho",
    "Jokic", "Jokić", "NBA", "champions", "Champions League",
]

BREAKING_NEWS_PATTERN = r"\bbreaking(?:\s*[:-]|\\s+news\b)"
FREE_MAX_RETRIES = 3
TRANSLATION_ERROR_MARKERS = (
    "error 500", "server error", "that’s an error", "that's an error",
    "please try again", "too many requests",
)

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "dev-insecure-secret-change-in-production")

# --- Security headers (v2026-09-30 P1+). Svi dobijaju iste vrednosti;
# CSP je baseline: inline stilovi/handleri ostaju dozvoljeni (sajt ih
# koristi), bez eksternih biblioteka, slike smeju s bilo kog HTTPS izvora.
_CSP = (
    "default-src 'self'; "
    "img-src 'self' data: https:; "
    "style-src 'self' 'unsafe-inline'; "
    "script-src 'self' 'unsafe-inline'; "
    "font-src 'self' data:; "
    "connect-src 'self'; "
    "object-src 'none'; "
    "base-uri 'self'; "
    "form-action 'self'; "
    "frame-ancestors 'self'"
)


@app.after_request
def _security_headers(resp):
    h = resp.headers
    h.setdefault("Strict-Transport-Security", "max-age=31536000; includeSubDomains")
    h.setdefault("Content-Security-Policy", _CSP)
    h.setdefault("X-Frame-Options", "SAMEORIGIN")
    h.setdefault("X-Content-Type-Options", "nosniff")
    h.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")
    h.setdefault("Permissions-Policy", "camera=(), microphone=(), geolocation=()")
    return resp

class _DatabaseAdapter:
    """Small compatibility layer for existing qmark SQL in SQLite/PostgreSQL.

    Self-healing for free-tier hosting: Neon/Render routinely drop idle
    sockets or interrupt queries. The old code kept one shared connection
    forever, so one interruption (or an aborted transaction never rolled
    back) turned EVERY page into HTTP 500 until a manual restart.
    Now a failed statement rolls the broken transaction back, reconnects
    when the socket itself is dead, and is retried exactly once.
    """

    _PG_OPTIONS = ("-c lock_timeout=5000 "
                   "-c idle_in_transaction_session_timeout=300000")

    def __init__(self, connection, dialect: str, dsn: str = ""):
        self.connection = connection
        self.dialect = dialect
        self.dsn = dsn
        self._last_used = time.monotonic()

    _IDLE_RECYCLE = float(os.environ.get("DB_IDLE_RECYCLE_SECONDS", "45"))

    def _recycle_if_idle(self) -> None:
        """Close the shared connection after a few quiet seconds.

        Free-tiers (Neon) treat an OPEN connection as activity: a 24/7 lived
        connection keeps the compute awake and burns the full 100 CU-hours
        monthly allowance in ~2 weeks. Closing it quickly when it goes quiet
        lets Neon's autosuspend finally put the database to sleep between
        cron cycles -> roughly 2x less compute spend.
        """
        if self.connection is None:
            return
        if time.monotonic() - self._last_used > self._IDLE_RECYCLE:
            try:
                self.connection.close()
            except Exception:
                pass
            self.connection = None

    def _ensure(self):
        if self.connection is None:
            self.connection = self._connect()
        self._last_used = time.monotonic()

    def _connect(self):
        import psycopg as _pg
        return _pg.connect(
            self.dsn,
            row_factory=dict_row,
            connect_timeout=10,
            options=self._PG_OPTIONS,
        )

    def _reconnect(self):
        try:
            self.connection.close()
        except Exception:
            pass
        self.connection = None
        self._ensure()

    def execute(self, sql: str, params=()):
        if self.dialect != "postgres":
            return self.connection.execute(sql, params)
        # All application queries use ? placeholders. psycopg uses %s.
        sql = sql.replace("?", "%s")
        self._recycle_if_idle()
        self._ensure()
        try:
            return self.connection.execute(sql, params)
        except (psycopg.OperationalError, psycopg.InterfaceError):
            self._reconnect()
            return self.connection.execute(sql, params)
        except psycopg.Error:
            # Aborted-transaction state (25P02) or any leftover SQL error:
            # roll back so one bad statement can never poison every later
            # request on the shared connection, then retry once.
            try:
                self.connection.rollback()
            except Exception:
                self._reconnect()
            return self.connection.execute(sql, params)

    def commit(self):
        try:
            return self.connection.commit()
        except (psycopg.OperationalError, psycopg.InterfaceError):
            if self.dialect == "postgres":
                self._reconnect()
            raise

    def rollback(self):
        try:
            return self.connection.rollback()
        except Exception:
            pass


# One shared connection + a lock for multi-thread (Flask + fetcher) access.
# PostgreSQL is the production database; SQLite/RAM is only a local fallback.
_db_lock = threading.RLock()
if DATABASE_URL:
    if psycopg is None:
        raise RuntimeError(
            "DATABASE_URL je podešen, ali psycopg nije instaliran. "
            "Dodaj psycopg[binary] u requirements.txt."
        )
    if DATABASE_URL.startswith("postgres://"):
        DATABASE_URL = "postgresql://" + DATABASE_URL[len("postgres://"):]
    _raw_db = psycopg.connect(
        DATABASE_URL,
        row_factory=dict_row,
        connect_timeout=10,
        options=_DatabaseAdapter._PG_OPTIONS,
    )
else:
    _raw_db = sqlite3.connect(DB_PATH, check_same_thread=False)
    _raw_db.row_factory = sqlite3.Row

_db = _DatabaseAdapter(_raw_db, DB_DIALECT, (DATABASE_URL if DB_DIALECT == "postgres" else ""))

# Prevent the background fetcher and the HTTP refresh route from running
# overlapping RSS/Gemini cycles and spending duplicate API calls.
_cycle_lock = threading.Lock()

# Secure session cookie defaults for the production HTTPS deployment.
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.environ.get("SESSION_COOKIE_SECURE", "1") != "0",
)


def _admin_auth_configured() -> bool:
    return bool(ADMIN_PASSWORD_HASH or ADMIN_PASSWORD)


def _verify_admin_password(candidate: str) -> bool:
    if ADMIN_PASSWORD_HASH:
        try:
            return check_password_hash(ADMIN_PASSWORD_HASH, candidate)
        except (ValueError, TypeError):
            return False
    return bool(ADMIN_PASSWORD) and hmac.compare_digest(candidate, ADMIN_PASSWORD)


def csrf_token() -> str:
    token = session.get("csrf_token")
    if not token:
        token = secrets.token_urlsafe(32)
        session["csrf_token"] = token
    return token


def valid_csrf_token() -> bool:
    expected = session.get("csrf_token", "")
    supplied = request.form.get("csrf_token", "")
    return bool(expected and supplied) and hmac.compare_digest(expected, supplied)


def admin_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not _admin_auth_configured():
            return (
                "Admin password nije podešen. Dodaj ADMIN_PASSWORD ili "
                "ADMIN_PASSWORD_HASH u Render Environment Variables.",
                503,
            )
        if not session.get("admin_authenticated"):
            return redirect(url_for("admin_login"))
        return view(*args, **kwargs)
    return wrapped


def valid_refresh_token() -> bool:
    """Accept a header; query-string fallback supports simple cron providers."""
    supplied = request.headers.get("X-Refresh-Token", "")
    if not supplied:
        supplied = request.args.get("token", "")
    return bool(REFRESH_TOKEN) and hmac.compare_digest(supplied, REFRESH_TOKEN)


# --------------------------------------------------------------------------- #
# AI prompts (used only when TRANSLATION_MODE == "ai", needs GEMINI_API_KEY)
# --------------------------------------------------------------------------- #

AI_HEADLINE_SYSTEM_PROMPT = (
    "You are a senior Serbian sports journalist and SEO copywriter. "
    "Translate the Spanish/English/Italian/Portuguese sports headline to Serbian, "
    "convert foreign football slang into localized Serbian sports terminology, and "
    "rewrite the headline to be unique and catchy for SEO. Preserve all key facts. "
    "Use these club names exactly: Crvena zvezda, Partizan, River Plejt, "
    "Boka Juniors, Njuels Old Bojs, Radnički Kragujevac. "
    "Output ONLY the Serbian headline."
)

AI_BODY_SYSTEM_PROMPT = (
    "You are a careful Serbian sports editor. Translate the supplied RSS material "
    "into natural Serbian. Use ONLY facts explicitly present in the headline and "
    "brief: never invent scores, dates, quotes, lineups, transfers, causes, context "
    "or predictions. If the material is short, return a concise one-paragraph news "
    "brief; do not pad it or pretend it is a full report. If the material is long, "
    "you may organise it into clear paragraphs without adding facts. Localize only "
    "football terminology that is actually present. Use these club names exactly: "
    "Crvena zvezda, Partizan, River Plejt, Boka Juniors, Njuels Old Bojs, "
    "Radnički Kragujevac. Output ONLY the Serbian article body."
)


# =========================================================================== #
#  IN-MEMORY DATABASE
# =========================================================================== #

SCHEMA_SQL_SQLITE = """
CREATE TABLE IF NOT EXISTS articles (
    id                 INTEGER PRIMARY KEY AUTOINCREMENT,
    source             TEXT    NOT NULL,
    original_title     TEXT    NOT NULL,
    original_summary   TEXT    DEFAULT '',
    link               TEXT    NOT NULL UNIQUE,
    published_date     TEXT,
    translated_title   TEXT    NOT NULL DEFAULT '',
    translated_summary TEXT    NOT NULL DEFAULT '',
    source_lang        TEXT    NOT NULL DEFAULT 'auto',
    priority           INTEGER NOT NULL DEFAULT 0,
    status             TEXT    NOT NULL DEFAULT 'pending'
                                        CHECK (status IN ('pending','published')),
    position           TEXT    NOT NULL DEFAULT 'standard'
                                        CHECK (position IN ('hero','trending','standard')),
    category           TEXT    NOT NULL DEFAULT 'other',
    content_type       TEXT    NOT NULL DEFAULT 'brief',
    attempt_count      INTEGER NOT NULL DEFAULT 0,
    last_error         TEXT    NOT NULL DEFAULT '',
    last_attempt_at    TEXT,
    next_retry_at      REAL,
    is_archived        INTEGER NOT NULL DEFAULT 0,
    archived_at        TEXT,
    views              INTEGER NOT NULL DEFAULT 0
)
"""

SCHEMA_SQL_POSTGRES = """
CREATE TABLE IF NOT EXISTS articles (
    id                 BIGSERIAL PRIMARY KEY,
    source             TEXT    NOT NULL,
    original_title     TEXT    NOT NULL,
    original_summary   TEXT    DEFAULT '',
    link               TEXT    NOT NULL UNIQUE,
    published_date     TEXT,
    translated_title   TEXT    NOT NULL DEFAULT '',
    translated_summary TEXT    NOT NULL DEFAULT '',
    source_lang        TEXT    NOT NULL DEFAULT 'auto',
    priority           INTEGER NOT NULL DEFAULT 0,
    status             TEXT    NOT NULL DEFAULT 'pending'
                                        CHECK (status IN ('pending','published')),
    position           TEXT    NOT NULL DEFAULT 'standard'
                                        CHECK (position IN ('hero','trending','standard')),
    category           TEXT    NOT NULL DEFAULT 'other',
    content_type       TEXT    NOT NULL DEFAULT 'brief',
    attempt_count      INTEGER NOT NULL DEFAULT 0,
    last_error         TEXT    NOT NULL DEFAULT '',
    last_attempt_at    TEXT,
    next_retry_at      REAL,
    is_archived        INTEGER NOT NULL DEFAULT 0,
    archived_at        TEXT,
    views              INTEGER NOT NULL DEFAULT 0
)
"""


def init_db() -> None:
    with _db_lock:
        if DB_DIALECT == "postgres":
            # DDL can block behind locks left by crashed old instances;
            # never let it hang or kill the boot (the table already exists).
            try:
                _db.execute(SCHEMA_SQL_POSTGRES)
            except Exception as exc:
                print(f"[DB] schema create skipped: {exc}")
                _db.rollback()
            try:
                # PostgreSQL migrations for databases created by older versions.
                for column_sql in (
                    "position TEXT NOT NULL DEFAULT 'standard'",
                    "category TEXT NOT NULL DEFAULT 'other'",
                    "content_type TEXT NOT NULL DEFAULT 'brief'",
                    "attempt_count INTEGER NOT NULL DEFAULT 0",
                    "last_error TEXT NOT NULL DEFAULT ''",
                    "last_attempt_at TEXT",
                    "next_retry_at DOUBLE PRECISION",
                    "is_archived INTEGER NOT NULL DEFAULT 0",
                    "archived_at TEXT",
                ):
                    column_name = column_sql.split()[0]
                    _db.execute(
                        f"ALTER TABLE articles ADD COLUMN IF NOT EXISTS {column_name} {column_sql[len(column_name)+1:]}"
                    )
            except Exception as exc:
                print(f"[DB] column migration skipped: {exc}")
                _db.rollback()
        else:
            _db.execute(SCHEMA_SQL_SQLITE)
            # SQLite migration for any pre-existing table without new metadata.
            cols = {row[1] for row in _db.execute("PRAGMA table_info(articles)")}
            migrations = {
                "position": "TEXT NOT NULL DEFAULT 'standard'",
                "category": "TEXT NOT NULL DEFAULT 'other'",
                "content_type": "TEXT NOT NULL DEFAULT 'brief'",
                "attempt_count": "INTEGER NOT NULL DEFAULT 0",
                "last_error": "TEXT NOT NULL DEFAULT ''",
                "last_attempt_at": "TEXT",
                "next_retry_at": "REAL",
                "is_archived": "INTEGER NOT NULL DEFAULT 0",
                "archived_at": "TEXT",
            }
            for column_name, column_type in migrations.items():
                if column_name not in cols:
                    _db.execute(
                        f"ALTER TABLE articles ADD COLUMN {column_name} {column_type}"
                    )
        _db.commit()


def get_db():
    """Return the shared database connection; _db_lock serializes access."""
    return _db


@app.teardown_appcontext
def close_db(_exception: Exception | None) -> None:
    # The in-memory connection must live for the whole process; do not close.
    pass


# =========================================================================== #
#  BUILT-IN RSS FETCHER  (ported from rss_fetcher.py)
# =========================================================================== #

def clean_text(raw: str | None) -> str:
    if not raw:
        return ""
    text = re.sub(r"<[^>]+>", " ", raw)
    text = html.unescape(text)
    return re.sub(r"\s+", " ", text).strip()


def _format_date(entry: Any) -> str:
    parsed = entry.get("published_parsed") or entry.get("updated_parsed")
    if parsed:
        return time.strftime("%Y-%m-%d %H:%M:%S UTC", parsed)
    return entry.get("published") or entry.get("updated") or "Unknown date"


def _feed_text_values(entry: Any) -> list[str]:
    """Collect text exposed by common RSS/Atom fields.

    feedparser normalises ``content:encoded`` to ``content_encoded`` for many
    feeds, while other feeds leave it under the literal key. Some feeds expose
    ``content`` as a list of dictionaries. Keep every usable candidate and let
    the caller select the longest one instead of assuming ``summary`` is best.
    """
    values: list[str] = []
    for key in ("content", "content_encoded", "content:encoded", "description", "summary"):
        raw = entry.get(key)
        if isinstance(raw, (list, tuple)):
            for item in raw:
                if isinstance(item, dict):
                    raw_value = item.get("value") or item.get("content") or item.get("text")
                else:
                    raw_value = item
                cleaned = clean_text(str(raw_value or ""))
                if cleaned:
                    values.append(cleaned)
        elif isinstance(raw, dict):
            cleaned = clean_text(str(raw.get("value") or raw.get("content") or ""))
            if cleaned:
                values.append(cleaned)
        else:
            cleaned = clean_text(str(raw or ""))
            if cleaned:
                values.append(cleaned)
    # A feed can repeat the same content under summary and description.
    return list(dict.fromkeys(values))


def _content_type_for_source(text: str) -> str:
    """Classify source material, not generated prose, as full or brief."""
    words = re.findall(r"\w+", text or "", flags=re.UNICODE)
    sentences = len(re.findall(r"[.!?](?:\s|$)", text or ""))
    return "full" if len(text or "") >= 320 and (len(words) >= 55 or sentences >= 3) else "brief"


def parse_entry(entry: Any, source: str) -> dict:
    candidates = _feed_text_values(entry)
    summary = max(candidates, key=len, default="")
    return {
        "source": source,
        "title": clean_text(entry.get("title")),
        "link": entry.get("link", ""),
        "published": _format_date(entry),
        "summary": summary,
        "content_type": _content_type_for_source(summary),
    }


def calculate_priority(title: str, summary: str) -> int:
    text = f"{title or ''} {summary or ''}".lower()
    # Absolute priority first: Zvezda news must always top the page.
    for kw in STAR_KEYWORDS:
        if re.search(rf"\b{re.escape(kw.lower())}s?\b", text):
            return 2
    for kw in HIGH_PRIORITY_KEYWORDS:
        if re.search(rf"\b{re.escape(kw.lower())}s?\b", text):
            return 1
    if re.search(BREAKING_NEWS_PATTERN, text):
        return 1
    return 0


# ---------- Sports localization (prevents funny literal translations) ------ #

# Applied to the ORIGINAL source text BEFORE translation: we drop the already
# correct Serbian name in, so the translator keeps it instead of literally
# translating ("Red Star" -> stays "Crvena zvezda").
LOCALIZE_PRE = [
    (r"newell'?s\s+old\s+boys", "Njuels Old Bojs"),
    (r"partizan\s+belgrade", "Partizan"),
    (r"red\s+star(?:\s+belgrade)?", "Crvena zvezda"),
    (r"river\s+plate", "River Plejt"),
    (r"boca\s+juniors", "Boka Juniors"),
    (r"transfer\s+window", "Prelazni rok"),
    (r"transfer\s+market", "Fudbalska pijaca"),
]

# Applied to the FINISHED Serbian text: cleans up any leftover English and the
# famous machine-translation blunders (River Plate -> "Bela kuća"/"Srebrna reka").
LOCALIZE_POST = [
    (r"red\s+star(?:\s+belgrade)?", "Crvena zvezda"),
    (r"partizan\s+belgrade", "Partizan"),
    (r"(?:reka\s+je\s+)?b(?:ij|e)l(?:a|e|u)\s+ku(?:ć|c)[aćehu]", "River Plejt"),
    (r"srebrna\s+reka", "River Plejt"),
    (r"river\s*plate?", "River Plejt"),
    (r"boca\s+juniors", "Boka Juniors"),
    (r"newell'?s\s+old\s+boys", "Njuels Old Bojs"),
]

_KRAGUJEVAC_CONTEXT = ["kragujevc", "čika dač", "cika dac", "đavol", "davol"]

# Serbian is phonetic and 1:1 between scripts. Google often returns Cyrillic;
# we normalise every Serbian output to Latin so the club-name post-filters
# (written in Latin) always match and the whole site stays a uniform script.
_CYR_TO_LAT = {
    "а": "a", "б": "b", "в": "v", "г": "g", "д": "d", "ђ": "đ", "е": "e",
    "ж": "ž", "з": "z", "и": "i", "ј": "j", "к": "k", "л": "l", "љ": "lj",
    "м": "m", "н": "n", "њ": "nj", "о": "o", "п": "p", "р": "r", "с": "s",
    "т": "t", "ћ": "ć", "у": "u", "ф": "f", "х": "h", "ц": "c", "ч": "č",
    "џ": "dž", "ш": "š",
    "А": "A", "Б": "B", "В": "V", "Г": "G", "Д": "D", "Ђ": "Đ", "Е": "E",
    "Ж": "Ž", "З": "Z", "И": "I", "Ј": "J", "К": "K", "Л": "L", "Љ": "Lj",
    "М": "M", "Н": "N", "Њ": "Nj", "О": "O", "П": "P", "Р": "R", "С": "S",
    "Т": "T", "Ћ": "Ć", "У": "U", "Ф": "F", "Х": "H", "Ц": "C", "Ч": "Č",
    "Џ": "Dž", "Ш": "Š",
}


def to_latin(text: str) -> str:
    return "".join(_CYR_TO_LAT.get(ch, ch) for ch in (text or ""))


def _apply_map(text: str, rules: list[tuple[str, str]]) -> str:
    for pattern, replacement in rules:
        text = re.sub(pattern, replacement, text, flags=re.IGNORECASE)
    return text


def localize_pre(text: str) -> str:
    return _apply_map(text or "", LOCALIZE_PRE)


def localize_post(text: str) -> str:
    """Fix Serbian output: normalise to Latin, fix club names, force 'Radnički
    Kragujevac' in context."""
    text = to_latin(text or "")
    text = _apply_map(text, LOCALIZE_POST)
    low = text.lower()
    if any(ctx in low for ctx in _KRAGUJEVAC_CONTEXT):
        # Bare nominative "Radnički" in a Kragujevac context must read
        # "Radnički Kragujevac". The trailing \b protects genitive/dative forms
        # ("Radničkog", "Radničkom") already present in domestic Serbian text;
        # the lookahead avoids re-appending when the city/year is already there.
        text = re.sub(
            r"\bRadni[čc]ki(?!\s+(?:Kragujevac|Ni[šs]|1923))\b",
            "Radnički Kragujevac", text,
        )
    return text


# ---------- Translation engine ---------- #

def translate_text(text: str, is_headline: bool = False,
                   source_headline: str | None = None) -> str:
    if not text or not text.strip():
        return ""
    # Preferred path: Gemini expands a short foreign brief into 2-3 Serbian
    # journalistic paragraphs. If GEMINI_API_KEY is missing or the call fails
    # for any reason, fall back to the free translator so the app never crashes.
    if TRANSLATION_MODE == "ai":
        try:
            if not os.environ.get("GEMINI_API_KEY"):
                raise RuntimeError("GEMINI_API_KEY nije podešen")
            return localize_post(_translate_ai(text, is_headline, source_headline))
        except Exception as exc:
            print(f"[TRANSLATE][AI] otkaz, koristim free prevod: {exc}")
    return localize_post(_translate_free(localize_pre(text)))


def _translate_free(text: str) -> str:
    if GoogleTranslator is None:
        raise RuntimeError("deep-translator is not installed: pip install deep-translator")
    translator = GoogleTranslator(source="auto", target=TARGET_LANGUAGE)
    last_error: Exception | None = None
    for attempt in range(1, FREE_MAX_RETRIES + 1):
        try:
            result = translator.translate(text)
            if result and not _looks_like_error_page(result):
                return result
            last_error = RuntimeError("translator returned an error page")
        except Exception as exc:
            last_error = exc
        if attempt < FREE_MAX_RETRIES:
            time.sleep(2.0 * attempt)
    raise RuntimeError(f"Free translation failed after {FREE_MAX_RETRIES}: {last_error}")


def _looks_like_error_page(text: str) -> bool:
    low = text.lower()
    return any(m in low for m in TRANSLATION_ERROR_MARKERS)


def _translate_ai(text: str, is_headline: bool, source_headline: str | None) -> str:
    """Call Google Gemini (AI Studio free tier) over plain HTTPS - no SDK.

    Returns Serbian text (headline = translated title; body = 2-3 paragraph
    article). Raises on any failure so translate_text() can fall back to free.
    """
    key = os.environ.get("GEMINI_API_KEY")
    if not key:
        raise RuntimeError("AI mode zahteva GEMINI_API_KEY environment varijablu")

    prompt = AI_HEADLINE_SYSTEM_PROMPT if is_headline else AI_BODY_SYSTEM_PROMPT
    if is_headline:
        user = f"Headline:\n{text}"
        tokens = 200
    else:
        user = f"Headline:\n{source_headline or ''}\n\nNews brief:\n{text}"
        tokens = 1200

    payload = {
        "system_instruction": {"parts": [{"text": prompt}]},
        "contents": [{
            "role": "user",
            "parts": [{"text": f"Target language: {TARGET_LANGUAGE}\n\n{user}"}],
        }],
        "generationConfig": {
            "temperature": 0.7,
            "maxOutputTokens": tokens,
        },
        # Don't let sports content (hard tackles, derbies) trip the safety filter.
        "safetySettings": [
            {"category": "HARM_CATEGORY_HARASSMENT", "threshold": "BLOCK_NONE"},
            {"category": "HARM_CATEGORY_HATE_SPEECH", "threshold": "BLOCK_NONE"},
            {"category": "HARM_CATEGORY_SEXUALLY_EXPLICIT", "threshold": "BLOCK_NONE"},
            {"category": "HARM_CATEGORY_DANGEROUS_CONTENT", "threshold": "BLOCK_NONE"},
        ],
    }

    url = GEMINI_API_URL.format(model=GEMINI_MODEL, key=urllib.parse.quote(key))
    req = urllib.request.Request(
        url, data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"}, method="POST",
    )
    with urllib.request.urlopen(req, timeout=45) as resp:
        data = json.loads(resp.read().decode("utf-8", "ignore"))

    candidate = (data.get("candidates") or [{}])[0]
    parts = candidate.get("content", {}).get("parts", [])
    result = "".join(p.get("text", "") for p in parts).strip()
    if not result:
        reason = (data.get("promptFeedback", {}) or {}).get("blockReason") \
            or candidate.get("finishReason") or "prazan odgovor"
        raise RuntimeError(f"Gemini nije vratio tekst ({reason})")
    return result


# ---------- Fetch / store cycle ---------- #

def _next_feed_batch() -> list[dict]:
    """Return the next rotating subset of RSS feeds for this process."""
    global _feed_cursor
    if not SPORTS_FEEDS:
        return []

    batch_size = max(1, min(MAX_FEEDS_PER_FETCH, len(SPORTS_FEEDS)))
    with _feed_cursor_lock:
        start = _feed_cursor
        indexes = [
            (start + offset) % len(SPORTS_FEEDS)
            for offset in range(batch_size)
        ]
        _feed_cursor = (start + batch_size) % len(SPORTS_FEEDS)
    return [SPORTS_FEEDS[index] for index in indexes]


def _fetch_and_parse_feed(url: str):
    """Download one feed with an explicit timeout, then parse its bytes."""
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": BROWSER_UA,
            "Accept": "application/rss+xml, application/atom+xml, application/xml, text/xml",
            "Accept-Encoding": "identity",
        },
    )
    with urllib.request.urlopen(req, timeout=FEED_TIMEOUT_SECONDS) as response:
        raw = response.read()
    return feedparser.parse(raw)


def fetch_all_feeds(feeds: list[dict] | None = None) -> tuple[int, int]:
    """Fetch a rotating feed batch, dedupe by link and skip junk per article.

    By default only MAX_FEEDS_PER_FETCH feeds are fetched. Passing ``feeds`` is
    useful for tests or an explicit full refresh.
    """
    feeds_to_fetch = feeds if feeds is not None else _next_feed_batch()
    new = skipped = 0
    print(
        f"[FETCH] Starting batch: {len(feeds_to_fetch)} feed(s), "
        f"timeout={FEED_TIMEOUT_SECONDS}s"
    )

    for feed in feeds_to_fetch:
        source, url, lang = feed["name"], feed["url"], feed.get("lang", "auto")
        try:
            parsed = _fetch_and_parse_feed(url)
            if parsed.bozo and not parsed.entries:
                raise parsed.bozo_exception or RuntimeError("Feed vratio 0 vesti")

            batch = []          # build rows WITHOUT holding the lock across the network
            entries = parsed.entries[:MAX_ENTRIES_PER_FEED]
            print(
                f"[FETCH] {source}: considering {len(entries)} newest of "
                f"{len(parsed.entries)} feed entries"
            )
            for entry in entries:
                art = parse_entry(entry, source)
                if not art["link"]:
                    continue
                # Unsupported sports are intentionally retained and routed
                # to the extensible "Ostalo" category instead of being lost.
                art["priority"] = calculate_priority(art["title"], art["summary"])
                feed_category = feed.get("category") or _SOURCE_CATEGORY_HINTS.get(source)
                art["category"] = (
                    feed_category if feed_category in CATEGORY_LABELS
                    else classify_category(art["title"], art["summary"], source)
                )
                art["lang"] = lang
                batch.append(art)

            with _db_lock:
                for art in batch:
                    exists = _db.execute(
                        "SELECT 1 FROM articles WHERE link = ? LIMIT 1", (art["link"],)
                    ).fetchone()
                    if exists:
                        skipped += 1
                        continue
                    _db.execute(
                        """INSERT INTO articles
                           (source, original_title, original_summary, link,
                            published_date, source_lang, priority, category,
                            content_type, status)
                           VALUES (?,?,?,?,?,?,?,?,?, 'pending')""",
                        (art["source"], art["title"], art["summary"], art["link"],
                         art["published"], art["lang"], art["priority"],
                         art["category"], art["content_type"]),
                    )
                    new += 1
                _db.commit()
            print(f"[FETCH] {source}: batch ok ({len(batch)} u obzir)")
        except Exception as exc:
            print(f"[FETCH][ERROR] {source}: {exc}")
    return new, skipped


def _generated_text(text: str, headline: bool = False) -> str:
    """Normalise model/translator output while keeping article paragraphs."""
    text = html.unescape((text or "").replace("\r\n", "\n")).strip()
    parts = []
    for part in re.split(r"\n\s*\n+", text):
        part = re.sub(r"\s+", " ", part).strip(" -*\t")
        if part:
            parts.append(part)
    return "\n\n".join(parts)


def _translate_short_brief(text: str) -> str:
    """Translate a short RSS brief without asking AI to invent an article."""
    return localize_post(_translate_free(localize_pre(text)))


def _validate_article_output(title: str, body: str) -> None:
    if len((title or "").strip()) < 5:
        raise RuntimeError("prevod naslova je prazan ili prekratak")
    if len((body or "").strip()) < 12:
        raise RuntimeError("prevod sadržaja je prazan ili prekratak")
    if _looks_like_error_page(body) or _looks_like_error_page(title):
        raise RuntimeError("prevod liči na stranicu greške")


def _retry_delay(attempt_count: int) -> float:
    # Cron normally runs every ten minutes: failed work is retained but does
    # not hammer a provider on every request. It eventually retries hourly.
    return min(3600.0, 30.0 * (2 ** min(max(attempt_count - 1, 0), 7)))


def process_translations(limit: int = MAX_TRANSLATIONS_PER_RUN) -> tuple[int, int]:
    """Process at most ``limit`` due rows, retaining failures for retry.

    Short RSS entries are published as explicitly brief, factual items. They
    are never fed to the expansion prompt as if they contained facts that are
    not present in the feed. Longer permitted RSS material may be expanded by
    AI, but only a quality-checked result is published.
    """
    now = time.time()
    with _db_lock:
        rows = _db.execute(
            """SELECT id, source, original_title, original_summary, priority,
                      source_lang, category, content_type, attempt_count
               FROM articles
               WHERE status='pending'
                 AND (translated_title = '' OR translated_summary = '')
                 AND (next_retry_at IS NULL OR next_retry_at <= ?)
               ORDER BY priority DESC, published_date DESC, id DESC
               LIMIT ?""",
            (now, limit),
        ).fetchall()

    if not rows:
        return 0, 0

    translated = failed = 0
    for row in rows:
        article_id = row["id"]
        attempt_count = int(row["attempt_count"] or 0) + 1
        attempt_at = time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime())
        with _db_lock:
            _db.execute(
                """UPDATE articles
                   SET attempt_count=?, last_attempt_at=?, last_error=''
                   WHERE id=?""",
                (attempt_count, attempt_at, article_id),
            )
            _db.commit()

        try:
            original_title = (row["original_title"] or "").strip()
            original_summary = (row["original_summary"] or "").strip()
            source_material = original_summary or original_title
            source_type = row["content_type"] or _content_type_for_source(source_material)

            if row["source_lang"] == "sr":
                tr_title = localize_post(original_title)
                tr_summary = localize_post(original_summary) if original_summary else tr_title
            else:
                # Short material gets ordinary translation for both title and
                # body. This is the important anti-hallucination branch for
                # 10–15 word RSS feeds: no AI headline embellishment either.
                if len(source_material) < 80:
                    tr_title = _translate_short_brief(original_title)
                    tr_summary = (
                        tr_title if source_material == original_title
                        else _translate_short_brief(source_material)
                    )
                else:
                    tr_title = translate_text(
                        original_title, is_headline=True, source_headline=original_title,
                    )
                    if TRANSLATION_MODE == "ai":
                        tr_summary = translate_text(
                            source_material, is_headline=False,
                            source_headline=original_title,
                        )
                    else:
                        tr_summary = _translate_short_brief(source_material)

            tr_title = _generated_text(localize_post(tr_title), headline=True)
            tr_summary = _generated_text(localize_post(tr_summary))
            if not tr_summary:
                # A title-only RSS item remains visible as a short item, rather
                # than being falsely presented as a detailed report.
                tr_summary = tr_title
            if source_type == "full" and len(tr_summary) < 80:
                raise RuntimeError(
                    "prevod dužeg RSS sadržaja je prekratak; vest ostaje za retry"
                )
            _validate_article_output(tr_title, tr_summary)

            category = row["category"] if row["category"] in CATEGORY_LABELS else "other"
            if category == "other":
                category = classify_category(original_title, original_summary, row["source"])
            content_type = (
                "full" if source_type == "full" and len(tr_summary) >= 280 else "brief"
            )

            # AUTOMATIC publishing stays enabled by default. Manual hero and
            # legacy 'trending' placement remain separate from view ranking.
            if AUTOPILOT_PUBLISH:
                status = "published"
                position = "hero" if row["priority"] == 2 else "standard"
            else:
                status, position = "pending", "standard"

            with _db_lock:
                if position == "hero":
                    _db.execute(
                        "UPDATE articles SET position='standard' "
                        "WHERE position='hero' AND id != ?", (article_id,))
                _db.execute(
                    """UPDATE articles
                       SET translated_title=?, translated_summary=?,
                           category=?, content_type=?, status=?, position=?,
                           last_error='', next_retry_at=NULL
                       WHERE id=?""",
                    (tr_title, tr_summary, category, content_type, status,
                     position, article_id),
                )
                _db.commit()
            translated += 1
            tag = "PUBLISHED" if status == "published" else "pending"
            print(
                f"[TRANSLATE] #{article_id} [{row['source']}] {tag}/"
                f"{content_type}: {tr_title[:60]}"
            )
            if row["source_lang"] != "sr" and TRANSLATION_MODE == "free":
                time.sleep(0.5)
        except Exception as exc:
            failed += 1
            if attempt_count >= PARK_AFTER_ATTEMPTS:
                park_at = time.time() + PARK_PARKING_SECONDS
                park_txt = f"parked after {attempt_count} attempts: " + str(exc).replace("\n", " ")[:440]
                with _db_lock:
                    _db.execute(
                        """UPDATE articles
                           SET translated_title='', translated_summary='',
                               last_error=?, next_retry_at=?, status='pending'
                           WHERE id=?""",
                        (park_txt, park_at, article_id),
                    )
                    _db.commit()
                print(
                    f"[TRANSLATE][PARK] #{article_id}: {attempt_count}. pokusaj — "
                    f"vest parkirana na {PARK_PARKING_SECONDS//86400} dana."
                )
                continue
            retry_at = time.time() + _retry_delay(attempt_count)
            error_text = str(exc).replace("\n", " ")[:500]
            with _db_lock:
                _db.execute(
                    """UPDATE articles
                       SET translated_title='', translated_summary='',
                           last_error=?, next_retry_at=?, status='pending'
                       WHERE id=?""",
                    (error_text, retry_at, article_id),
                )
                _db.commit()
            print(
                f"[TRANSLATE][ERROR] #{article_id} attempt={attempt_count}; "
                f"retry in {int(_retry_delay(attempt_count))}s: {error_text}"
            )
    print(f"[TRANSLATE] cycle done: {translated} ok, {failed} failed")
    return translated, failed

def run_fetcher_cycle() -> None:
    """Run the legacy background cycle, but never overlap another cycle."""
    if not _cycle_lock.acquire(blocking=False):
        print("[AUTOPILOT] cycle skipped: another cycle is already running")
        return

    try:
        new, skipped = fetch_all_feeds()
        process_translations()
        with _db_lock:
            total = _db.execute("SELECT COUNT(*) c FROM articles").fetchone()["c"]
            live = _db.execute(
                "SELECT COUNT(*) c FROM articles WHERE status='published'").fetchone()["c"]
        print(
            f"[AUTOPILOT] cycle: {new} new, {skipped} skipped/dupes | "
            f"DB {total} | live {live}"
        )
    finally:
        _cycle_lock.release()


def _fetcher_loop() -> None:
    """Background thread: initial seed shortly after boot, then loop forever."""
    time.sleep(3)  # let the web server come up first
    while True:
        try:
            run_fetcher_cycle()
        except Exception as exc:
            print(f"[AUTOPILOT][ERROR] cycle failed but loop continues: {exc}")
        time.sleep(FETCH_INTERVAL_SECONDS)


def start_background_fetcher() -> None:
    if not RUN_FETCHER:
        print("[AUTOPILOT] background fetcher disabled (RUN_FETCHER=0)")
        return
    t = threading.Thread(target=_fetcher_loop, name="rss-fetcher", daemon=True)
    t.start()
    print(f"[AUTOPILOT] background fetcher thread started "
          f"(mode={TRANSLATION_MODE}, interval={FETCH_INTERVAL_SECONDS}s)")


# =========================================================================== #
#  DYNAMIC IMAGERY / CATEGORIES / LOCAL-CLUB BADGES
# =========================================================================== #

# The registry is deliberately data-driven: adding a new sport means adding one
# entry here and one keyword list, not rewriting the homepage route/template.
CATEGORY_CONFIG = [
    {"key": "football", "label": "Fudbal", "emoji": "⚽", "anchor": "fudbal", "detect_order": 40},
    {"key": "basketball", "label": "Košarka", "emoji": "🏀", "anchor": "kosarka", "detect_order": 10},
    {"key": "tennis", "label": "Tenis", "emoji": "🎾", "anchor": "tenis", "detect_order": 20},
    {"key": "boxing", "label": "Boks", "emoji": "🥊", "anchor": "boks", "detect_order": 30},
    {"key": "other", "label": "Ostalo", "emoji": "🏆", "anchor": "ostalo", "detect_order": 100},
]
CATEGORY_LABELS = {item["key"]: item["label"] for item in CATEGORY_CONFIG}
CATEGORY_EMOJIS = {item["key"]: item["emoji"] for item in CATEGORY_CONFIG}

# Only dedicated feeds receive a source hint. Mixed domestic feeds are
# classified per article; otherwise their basketball/tennis/boxing items would
# all inherit a football label merely because the feed is called "Sport".
_SOURCE_CATEGORY_HINTS = {
    "Marca (Španija)": "football",
    "AS (Španija)": "football",
    "Gazzetta (Italija)": "football",
    "Sky Sports (Engleska)": "football",
    "Football Italia": "football",
    "Eurohoops": "basketball",
    "Sportando": "basketball",
    "ESPN Tennis": "tennis",
    "ATP Tour": "tennis",
    "BoxingScene": "boxing",
}

# Keep category signals specific. Generic words such as "meč", "trener",
# "napad" and "odbrana" are intentionally absent because they misclassify
# tennis, boxing and other sports as football.
_CATEGORY_KEYWORDS = {
    "basketball": [
        "nba", "wnba", "basketball", "košarka", "kosarka", "košarkašk",
        "kosarkask", "košarkaš", "kosarkas", "basket", "evroliga",
        "evrolige", "euroleague", "evrokup", "fiba", "ncaa basketball",
    ],
    "tennis": [
        "tennis", "tenis", "atp", "wta", "itf tennis", "grand slam",
        "wimbledon", "roland garros", "us open", "australian open",
        "french open", "cincinnati open", "masters 1000", "davis cup",
        "fed cup", "bekhend", "forhend", "brejk lopta",
        "break point", "setova", "teniski teren",
    ],
    "boxing": [
        "boxing", "boks", "bokser", "bokseri", "bokserski", "ring",
        "nokaut", "nokautirao", "nokautiran", "knockout", "ko pobeda",
        "wbc", "wba", "ibf", "wbo", "ufc", "mma", "teška kategorija",
        "teska kategorija", "velter", "superteška", "superteska",
    ],
    "football": [
        "football", "soccer", "fudbal", "fudbalsk", "messi", "maradona",
        "boca juniors", "boka juniors", "river plej", "river plate", "xeneize",
        "millonario", "real madrid", "liverpool", "barselona", "barcelona",
        "manchester", "chelsea", "arsenal", "psg", "premier league", "la liga",
        "serija a", "serie a", "bundesliga", "clausura", "klauzura",
        "libertadores", "sudamericana", "golman", "golova", "golovima",
        "ofšajd", "ofsajd", "corner", "korner", "penal", "jedanaesterac",
        "kapiten", "derbi", "prelazni rok", "fudbalska pijaca", "transfer",
        "fichaje", "refuerzo", "superliga", "radnički", "radnicki", "vojvodina",
        "vosa", "voša", "čika dača", "cika daca", "đavoli", "davoli",
        "radnički niš", "radnicki nis", "nišava", "čair", "novi pazar",
        "partizan", "crvena zvezda", "zvezda", "kragujevac", "kragujevcu",
        "neymar", "ronaldinho", "pelé", "pele", "endrick", "estevao",
        "estêvão", "messinho", "flamengo", "palmeiras", "santos", "sao paulo",
        "são paulo", "fluminense", "brasileirao", "brasileirão",
    ],
}

_SOUTH_AMERICA_KEYWORDS = [
    "boka", "boca", "river plej", "plejt", "xeneize", "millonario",
    "boca juniors", "boka juniors", "river plate", "lanús", "lanus",
    "vélez", "velez", "racing", "independiente", "san lorenzo",
    "estudiantes", "bombonera", "clausura", "klauzura", "libertadores",
    "sudamericana", "gaucho", "gaučo", "gaučos", "karioka", "karioke",
    "tango", "samba", "argentina", "argentinski", "brazil", "brazilu",
    "brazilski", "brazilskom", "messi", "maradona", "tevez", "riquelme",
    "gallardo", "neymar", "ronaldinho", "pelé", "pele", "endrick", "estevao",
    "estêvão", "messinho", "flamengo", "palmeiras", "santos", "sao paulo",
    "são paulo", "fluminense", "brasileirao", "brasileirão", "njujels", "ole",
    "clarin", "globo",
]


def _keyword_hit(text: str, keyword: str) -> bool:
    """Accent-tolerant-ish phrase match without broad substring accidents."""
    return keyword.lower() in text.lower()


def classify_category(title: str, summary: str, source: str = "") -> str:
    text = f"{source} {title} {summary}".lower()
    # Specific categories win first, so a tennis/boxing article containing a
    # generic football word in a quote or tag cannot fall into football. The
    # order comes from the registry, so new sports can be added without
    # changing this function.
    for config in sorted(CATEGORY_CONFIG, key=lambda item: item.get("detect_order", 100)):
        category = config["key"]
        keywords = _CATEGORY_KEYWORDS.get(category, [])
        if any(_keyword_hit(text, keyword) for keyword in keywords):
            return category
    return "other"

# Offline fallback images (inline SVG) used by default. External image search
# is never assumed to grant republication rights and is opt-in below.
_FALLBACK_EMOJI = {"football": "⚽", "basketball": "🏀", "tennis": "🎾", "boxing": "🥊", "other": "🏆", "general": "🏆"}


def _fallback_image(category: str) -> str:
    emoji = _FALLBACK_EMOJI.get(category, "🏆")
    svg = (
        "<svg xmlns='http://www.w3.org/2000/svg' width='1200' height='675' "
        "viewBox='0 0 1200 675'>"
        "<rect width='1200' height='675' fill='#1e293b'/>"
        "<rect x='18' y='18' width='1164' height='639' rx='24' fill='none' "
        "stroke='#334155' stroke-width='4'/>"
        "<text x='600' y='380' font-size='230' text-anchor='middle'>"
        f"{emoji}</text>"
        "</svg>"
    )
    return "data:image/svg+xml;charset=utf-8," + urllib.parse.quote(svg)


# Cache of Google image results keyed by article id (we never call the paid API
# twice for the same article within a process, even on repeated page loads).
_image_cache: dict[int, str] = {}
_image_cache_lock = threading.Lock()


def _google_image_url(query: str) -> str | None:
    """Query Google Custom Search (image search) and return the first hit."""
    api_key = os.environ.get("GOOGLE_API_KEY")
    cx = os.environ.get("GOOGLE_CX")
    if not api_key or not cx:
        return None
    params = {
        "key": api_key, "cx": cx, "q": query,
        "searchType": "image", "num": 1, "safe": "active",
        "imgSize": "large",
    }
    url = "https://www.googleapis.com/customsearch/v1?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"User-Agent": BROWSER_UA})
    with urllib.request.urlopen(req, timeout=8) as resp:
        data = json.loads(resp.read().decode("utf-8", "ignore"))
    items = data.get("items") or []
    if items and items[0].get("link"):
        return items[0]["link"]
    return None


def article_image(article) -> str:
    """Real Google image for the article headline; offline SVG fallback."""
    try:
        article_id = article["id"]
        title = article["translated_title"] or ""
    except (KeyError, IndexError, TypeError):
        article_id, title = None, ""
    category = article_category(article)

    with _image_cache_lock:
        if article_id in _image_cache:
            return _image_cache[article_id]

    result = _fallback_image(category)
    query = (title or category).strip()
    if ALLOW_EXTERNAL_IMAGES:
        try:
            found = _google_image_url(query)
            if found:
                result = found
        except Exception as exc:
            print(f"[IMAGE] Google image search nije dostupan ({query[:40]}...): {exc}")

    if article_id is not None:
        with _image_cache_lock:
            _image_cache[article_id] = result
    return result


LOCAL_CLUBS = [
    {"label": "Radnički KG", "css": "club-kg",
     "match": ["kragujevac", "kragujevcu", "kragujevca", "čika dača",
               "cika daca", "đavoli", "davoli", "radnički kragujevac"]},
    {"label": "Radnički Niš", "css": "club-nis",
     "match": ["radnički niš", "radnicki nis", "čair", "nišava"]},
    {"label": "Novi Pazar", "css": "club-pazar",
     "match": ["novi pazar", "novog pazara", "novom pazaru", "novim pazarom",
               "pazarci"]},
    {"label": "Vojvodina", "css": "club-vosa",
     "match": ["vojvodina", "vojvodine", "vojvodini", "vojvodinom", "voša",
               "vosa", "voše", "novosađani", "novosadjani", "novosađana"]},
]
_NIS_CONTEXT = ["niš", "čair", "nišava"]


def article_text_blob(article) -> str:
    def val(k):
        try:
            return article[k] or ""
        except (KeyError, IndexError, TypeError):
            return ""
    return " ".join(
        val(k) for k in ("translated_title", "translated_summary",
                         "original_title", "original_summary", "source")
    ).lower()


def article_category(article) -> str:
    """Read persisted category; infer safely for legacy rows.

    Older records had no category column (or used ``general``). They are
    reclassified from their text at render time, while new RSS rows persist the
    result at ingestion so later keyword edits do not move them unexpectedly.
    """
    try:
        stored = article["category"]
    except (KeyError, IndexError, TypeError):
        stored = ""
    if stored in CATEGORY_LABELS and stored != "other":
        return stored
    text = article_text_blob(article)
    return classify_category(
        article.get("original_title", "") if hasattr(article, "get") else "",
        article.get("original_summary", "") if hasattr(article, "get") else "",
        article.get("source", "") if hasattr(article, "get") else text,
    )


def is_south_america(article) -> bool:
    """South-America bucket is decided by TITLES only. Scanning full summaries
    misfiled any story whose body quoted a legend ("Pele/Maradona") into Južna
    Amerika (e.g. a Cristiano Ronaldo piece)."""
    try:
        title = f"{article['translated_title'] or ''} {article['original_title'] or ''}".lower()
    except (KeyError, IndexError, TypeError):
        return False
    return any(re.search(rf"\b{re.escape(k)}", title) for k in _SOUTH_AMERICA_KEYWORDS)


def category_label(article) -> str:
    return CATEGORY_LABELS[article_category(article)]


def club_badges(article) -> list[dict]:
    text = article_text_blob(article)
    badges, labels = [], set()
    for club in LOCAL_CLUBS:
        if any(s in text for s in club["match"]) and club["label"] not in labels:
            badges.append({"label": club["label"], "css": club["css"]})
            labels.add(club["label"])
    has_rad = re.search(r"\bradni[čc]ki\b", text) is not None
    if (has_rad and not any(b["label"] in ("Radnički KG", "Radnički Niš") for b in badges)
            and any(re.search(rf"\b{re.escape(w)}", text) for w in _NIS_CONTEXT)):
        badges.append({"label": "Radnički Niš", "css": "club-nis"})
    return badges


app.jinja_env.globals.update(
    article_image=article_image,
    article_category=article_category,
    category_label=category_label,
    club_badges=club_badges,
    csrf_token=csrf_token,
)


# =========================================================================== #
#  CSS
# =========================================================================== #

BASE_CSS = """
:root{
  --bg:#0f172a; --panel:#1e293b; --panel-2:#162033; --border:#334155;
  --text:#f8fafc; --muted:#94a3b8;
  --green:#22c55e; --green-dark:#16a34a; --red:#ef4444; --red-dark:#dc2626;
  --shadow:0 10px 30px rgba(2,6,23,.45);
}
*{box-sizing:border-box; margin:0; padding:0;}
html{-webkit-text-size-adjust:100%; scroll-behavior:smooth;}
body{background:var(--bg); color:var(--text);
  font-family:'Segoe UI', system-ui, -apple-system, Roboto, sans-serif;
  line-height:1.6; min-height:100vh;}
.container{max-width:1200px; margin:0 auto; padding:0 20px;}
a{color:inherit; text-decoration:none;} img{display:block; max-width:100%;}
.topbar{background:rgba(15,23,42,.85); backdrop-filter:blur(10px);
  border-bottom:1px solid var(--border); position:sticky; top:0; z-index:20;}
.topbar-inner{display:flex; align-items:center; justify-content:space-between;
  gap:12px; padding:16px 0; flex-wrap:wrap;}
.brand{display:flex; align-items:center; gap:10px; font-size:1.35rem; font-weight:800;}
.brand .ball{font-size:1.5rem;} .brand em{font-style:normal; color:var(--green);}

/* ---- hamburger navigation ---- */
.site-nav{display:flex; align-items:center; gap:14px;}
.hamburger{display:inline-flex; flex-direction:column; justify-content:center; gap:5px;
  width:46px; height:46px; border:1px solid var(--border); border-radius:10px;
  background:var(--panel); cursor:pointer; padding:0 11px;}
.hamburger span{display:block; height:2px; width:100%; background:var(--text);
  border-radius:2px; transition:transform .25s ease, opacity .25s ease;}
.hamburger.open span:nth-child(1){transform:translateY(7px) rotate(45deg);}
.hamburger.open span:nth-child(2){opacity:0;}
.hamburger.open span:nth-child(3){transform:translateY(-7px) rotate(-45deg);}
.nav-dropdown{position:absolute; top:70px; right:20px; min-width:230px; z-index:40;
  background:var(--panel); border:1px solid var(--border); border-radius:12px;
  box-shadow:var(--shadow); padding:8px; display:none;}
.nav-dropdown.show{display:block;}
.nav-dropdown a{display:flex; align-items:center; gap:10px; padding:13px 16px;
  border-radius:9px; font-weight:600; font-size:1rem; transition:background .15s;}
.nav-dropdown a:hover{background:var(--panel-2); color:var(--green);}
.nav-dropdown a .ico{font-size:1.2rem;}

.chip{display:inline-block; background:rgba(15,23,42,.72); color:#e2e8f0;
  border:1px solid rgba(148,163,184,.35); border-radius:999px; padding:4px 12px;
  font-size:.72rem; font-weight:700; letter-spacing:.8px; text-transform:uppercase;
  backdrop-filter:blur(4px);}
.badge-hot{display:inline-block; background:var(--green); color:#052e16;
  border-radius:999px; padding:4px 12px; font-size:.72rem; font-weight:800;
  letter-spacing:.8px; text-transform:uppercase; box-shadow:0 0 18px rgba(34,197,94,.5);}
.badge-live{display:inline-block; background:rgba(34,197,94,.15); color:#86efac;
  border:1px solid rgba(34,197,94,.4); border-radius:999px; padding:3px 11px;
  font-size:.7rem; font-weight:800; letter-spacing:.5px; text-transform:uppercase;}
.badge-star{display:inline-block; background:linear-gradient(135deg,#dc2626,#b91c1c);
  color:#fff; border-radius:999px; padding:4px 12px; font-size:.72rem; font-weight:800;
  letter-spacing:.8px; text-transform:uppercase; box-shadow:0 0 18px rgba(220,38,38,.55);}

.club-badges{display:flex; gap:8px; flex-wrap:wrap; margin-top:2px;}
.club-chip{display:inline-block; border-radius:6px; padding:3px 11px; font-size:.72rem;
  font-weight:800; letter-spacing:.5px; white-space:nowrap; text-transform:uppercase;
  border:1px solid transparent;}
.club-kg{background:#dc2626; color:#fff; border-color:#f87171;}
.club-nis{background:#f97316; color:#1f1300; border-color:#fb923c;}
.club-pazar{background:#2563eb; color:#fff; border-color:#60a5fa;}
.club-vosa{background:#e2e8f0; color:#0f172a; border-color:#cbd5e1;}

.hero{position:relative; border-radius:18px; overflow:hidden; margin:26px 0 34px;
  min-height:440px; display:flex; align-items:flex-end; border:1px solid var(--border);
  box-shadow:var(--shadow); transition:transform .25s ease;}
.hero:hover{transform:translateY(-3px);}
.hero img{position:absolute; inset:0; width:100%; height:100%; object-fit:cover;}
.hero-overlay{position:absolute; inset:0;
  background:linear-gradient(to top, rgba(2,6,23,.96) 0%, rgba(2,6,23,.72) 42%,
             rgba(2,6,23,.15) 75%, rgba(2,6,23,.05) 100%);}
.hero-content{position:relative; padding:34px 36px; max-width:860px;}
.hero-tags{display:flex; gap:10px; margin-bottom:14px; flex-wrap:wrap;}
.hero h1, .hero h2{font-size:clamp(1.6rem,3.6vw,2.6rem); font-weight:800; line-height:1.15;
  margin-bottom:12px; text-shadow:0 2px 14px rgba(0,0,0,.5);}
.hero p{font-size:clamp(1rem,1.6vw,1.18rem); color:#cbd5e1; margin-bottom:16px;}

.section-head{display:flex; align-items:center; gap:12px; margin:8px 0 20px;}
.section-head h2{font-size:1.25rem; font-weight:800; letter-spacing:.4px;
  border-left:4px solid var(--green); padding-left:12px;}
.section-head .line{flex:1; height:1px; background:var(--border);}
.section-head h2 .emoji{margin-right:8px;}
.sa-sub{font-size:.72rem; font-weight:600; color:var(--muted);
  text-transform:none; letter-spacing:.3px; white-space:nowrap;}
.grid-section{margin-bottom:44px; scroll-margin-top:88px;}
.hero-head{scroll-margin-top:88px;}

.grid{display:grid; grid-template-columns:repeat(3,1fr); gap:24px;}
.card{background:var(--panel); border:1px solid var(--border); border-radius:12px;
  overflow:hidden; display:flex; flex-direction:column; color:inherit; cursor:pointer;
  transition:transform .22s ease, box-shadow .22s ease, border-color .22s ease;}
.card:hover{transform:scale(1.02);
  box-shadow:0 14px 34px rgba(34,197,94,.16), 0 4px 14px rgba(2,6,23,.5);
  border-color:rgba(34,197,94,.5);}
.card-media{position:relative; aspect-ratio:16/9; overflow:hidden;
  background:linear-gradient(135deg,#1e293b,#0f172a);}
.card-media img{width:100%; height:100%; object-fit:cover; transition:transform .35s ease;}
.card:hover .card-media img{transform:scale(1.06);}
.card-media .chip{position:absolute; top:12px; left:12px;}
.card-body{padding:18px 20px 20px; display:flex; flex-direction:column; gap:10px; flex:1;}
.card-body h3, .card-body h2{font-size:1.06rem; font-weight:700; line-height:1.35;}
.card-excerpt{color:#cbd5e1; font-size:.92rem; display:-webkit-box;
  -webkit-line-clamp:3; -webkit-box-orient:vertical; overflow:hidden;}
.card-body .meta{margin-top:auto; padding-top:8px; border-top:1px solid var(--border);}

.card.trending{border-color:rgba(249,115,22,.45);}
.card.trending:hover{box-shadow:0 14px 34px rgba(249,115,22,.20), 0 4px 14px rgba(2,6,23,.5);
  border-color:rgba(249,115,22,.75);}
.badge-trending{position:absolute; top:12px; right:12px; display:inline-flex; align-items:center;
  gap:4px; background:linear-gradient(135deg,#f97316,#f59e0b); color:#1f1300;
  border-radius:999px; padding:4px 11px; font-size:.72rem; font-weight:800;
  text-transform:uppercase; box-shadow:0 4px 14px rgba(249,115,22,.45);}
.card-rank{position:absolute; bottom:12px; left:12px; width:30px; height:30px;
  border-radius:50%; background:var(--green); color:#052e16; font-weight:800;
  display:flex; align-items:center; justify-content:center; box-shadow:0 4px 12px rgba(2,6,23,.5);}
.hero-head h2{font-size:1.25rem; font-weight:800; border-left:4px solid var(--green);
  padding-left:12px;} .hero-head{margin:8px 0 18px;}

.meta{display:flex; gap:16px; flex-wrap:wrap; color:var(--muted); font-size:.84rem;
  align-items:center;}
.views{margin-left:auto; font-weight:600;} .views b{color:var(--green);}
.archive-tools{display:flex; align-items:end; justify-content:space-between; gap:16px; flex-wrap:wrap;
  margin:8px 0 22px; padding:14px 16px; background:var(--panel); border:1px solid var(--border);
  border-radius:12px; color:var(--muted);}
.archive-tools form{display:flex; align-items:center; gap:10px; margin:0;}
.archive-tools label{margin:0; color:var(--muted); text-transform:none; letter-spacing:normal;}
.archive-tools select{background:var(--bg); color:var(--text); border:1px solid var(--border);
  border-radius:8px; padding:8px 10px; font:inherit;}
.pagination{display:flex; align-items:center; justify-content:center; gap:8px; flex-wrap:wrap; margin:4px 0 40px;}
.pagination a,.pagination strong{min-width:36px; padding:8px 12px; text-align:center; border:1px solid var(--border); border-radius:8px;}
.pagination a:hover{border-color:var(--green); color:var(--green);}
.pagination strong{background:var(--green); color:#052e16; border-color:var(--green);}
.admin-list .pagination{margin:12px 0 6px; gap:4px;}
.admin-list .pagination a,.admin-list .pagination strong{min-width:28px; padding:5px 8px; font-size:.8rem;}
.empty{background:var(--panel); border:1px dashed var(--border); border-radius:14px;
  color:var(--muted); text-align:center; padding:64px 24px; font-size:1.08rem;}
.footer-text{color:var(--muted); font-size:.88rem; text-align:center; padding:34px 0 26px;}

/* ---- internal article reader ---- */
.article-page{max-width:840px; margin:0 auto; padding:26px 20px 10px;}
.back-link{display:inline-flex; align-items:center; gap:7px; margin-bottom:22px;
  color:var(--green); font-weight:700; font-size:.95rem;}
.back-link:hover{text-decoration:underline;}
.article-card{background:var(--panel); border:1px solid var(--border); border-radius:16px;
  overflow:hidden; box-shadow:var(--shadow);}
.article-cover{width:100%; aspect-ratio:16/9; object-fit:cover; background:var(--panel-2);}
.article-inner{padding:28px 32px 34px;}
.article-tags{display:flex; gap:10px; flex-wrap:wrap; margin-bottom:14px;}
.article-title{font-size:clamp(1.5rem,3.2vw,2.3rem); font-weight:800; line-height:1.2;
  margin-bottom:14px; text-shadow:0 2px 12px rgba(0,0,0,.4);}
.article-meta{margin-bottom:22px; padding-bottom:18px; border-bottom:1px solid var(--border);}
.article-body{font-size:1.08rem; line-height:1.9; color:#dbe4f0;}
.article-body p{margin-bottom:18px;}
.source-discreet{margin-top:34px; padding-top:18px; border-top:1px solid var(--border);
  font-size:.78rem; line-height:1.6; color:var(--muted);}
.source-discreet a{color:var(--muted); text-decoration:underline;}
.source-discreet a:hover{color:var(--text);}
.notfound{max-width:560px; margin:70px auto; text-align:center;}

.btn{display:inline-block; border:none; border-radius:9px; padding:11px 20px;
  font-size:.92rem; font-weight:600; cursor:pointer; text-align:center;
  transition:background .15s, color .15s, border-color .15s;}
.btn-green{background:var(--green); color:#052e16;} .btn-green:hover{background:var(--green-dark); color:#fff;}
.btn-red{background:transparent; color:var(--red); border:1px solid var(--red);} .btn-red:hover{background:var(--red); color:#fff;}
.btn-red.big{display:block; width:100%; padding:15px 22px; font-size:1.05rem; font-weight:800;
  letter-spacing:.5px; text-transform:uppercase; margin-top:16px;
  background:var(--red-dark); color:#fff; border-color:var(--red);}
.btn-red.big:hover{background:var(--red);}
.btn-ghost{background:transparent; color:var(--muted); border:1px solid var(--border);} .btn-ghost:hover{color:var(--text); border-color:var(--muted);}
.flash{background:rgba(34,197,94,.12); border:1px solid var(--green); color:#bbf7d0;
  border-radius:10px; padding:12px 16px; margin-bottom:18px; font-size:.92rem;}

.admin-wrap{display:flex; gap:20px; align-items:flex-start; margin-top:20px;}
.panel{background:var(--panel); border:1px solid var(--border); border-radius:12px;}
.admin-list{width:38%; max-height:calc(100vh - 160px); overflow-y:auto; padding:10px;}
.admin-group{margin-bottom:6px;}
.admin-review{width:62%; padding:22px; position:sticky; top:96px;}
.group-head{font-size:.78rem; font-weight:800; letter-spacing:1.2px; text-transform:uppercase;
  padding:10px 10px 8px; position:sticky; top:0; background:var(--panel); z-index:2;}
.group-head.pending{color:#fbbf24;}
.group-head.published{color:var(--green); border-bottom:1px solid var(--border); margin-bottom:4px;}
.panel-head{font-size:.78rem; font-weight:700; letter-spacing:1.5px; text-transform:uppercase;
  color:var(--muted); padding:8px 10px 12px; border-bottom:1px solid var(--border); margin-bottom:10px;}
.admin-review .panel-head{margin:0 0 16px; padding:0 0 12px;}
.pending-item{display:block; padding:12px 14px; border-radius:9px; margin-bottom:6px;
  border:1px solid transparent; transition:background .12s, border-color .12s;}
.pending-item:hover{background:var(--panel-2);}
.pending-item.active{background:var(--panel-2); border-color:var(--green);}
.pi-title{font-weight:600; font-size:.95rem; line-height:1.35; margin-bottom:4px;}
.pi-meta{display:flex; gap:8px; align-items:center;}
.empty-small{color:var(--muted); font-size:.9rem; padding:10px 12px 14px;}
.orig-ref{background:var(--panel-2); border:1px solid var(--border); border-radius:10px;
  padding:14px 16px; margin-bottom:18px; font-size:.9rem;}
.orig-label{color:var(--muted); font-size:.72rem; text-transform:uppercase; letter-spacing:1.5px; margin-bottom:6px;}
.orig-ref strong{display:block; margin-bottom:6px; font-weight:600;} .orig-ref p{color:var(--muted);}
form label{display:block; font-size:.8rem; font-weight:600; letter-spacing:.6px;
  text-transform:uppercase; color:var(--muted); margin:14px 0 6px;}
form input[type=text], form textarea{width:100%; background:var(--bg); color:var(--text);
  border:1px solid var(--border); border-radius:9px; padding:12px 14px; font-size:1rem;
  font-family:inherit; line-height:1.5;}
form input[type=text]:focus, form textarea:focus{outline:none; border-color:var(--green);
  box-shadow:0 0 0 3px rgba(34,197,94,.15);}
form textarea{resize:vertical; min-height:160px;}
.pos-options{display:flex; flex-direction:column; gap:10px; margin-top:8px;}
.pos-opt{display:flex; align-items:center; gap:12px; background:var(--bg);
  border:1px solid var(--border); border-radius:10px; padding:12px 14px;
  cursor:pointer; text-transform:none; letter-spacing:normal; margin:0;
  transition:border-color .15s, background .15s;}
.pos-opt:hover{border-color:var(--green);}
.pos-opt input{width:auto; margin:0; accent-color:var(--green); cursor:pointer;}
.pos-opt:has(input:checked){border-color:var(--green);
  background:rgba(34,197,94,.1); box-shadow:0 0 0 2px rgba(34,197,94,.12);}
.pos-ico{font-size:1.4rem; line-height:1;}
.pos-text{display:flex; flex-direction:column; gap:2px;}
.pos-text b{font-size:.98rem; color:var(--text);}
.pos-text small{color:var(--muted); font-size:.78rem; font-weight:500;}
.actions{display:flex; gap:12px; margin-top:18px; flex-wrap:wrap;}
.sel-status{margin-left:auto;}

@media (max-width:1024px){ .grid{grid-template-columns:repeat(2,1fr);} }
@media (max-width:768px){
  .grid{grid-template-columns:1fr; gap:18px;}
  .hero{min-height:380px;} .hero-content{padding:24px 22px;}
  .article-inner{padding:22px 20px 26px;}
  .admin-wrap{flex-direction:column;} .admin-list, .admin-review{width:100%;}
  .admin-list{max-height:46vh;} .admin-review{position:static;}
}

/* v7: vidljiv fokus za tastaturnu navigaciju (WCAG 2.4.7) */
a:focus-visible, button:focus-visible, [tabindex]:focus-visible {
  outline: 3px solid var(--green);
  outline-offset: 2px;
  border-radius: 4px;
}
"""


# =========================================================================== #
#  TEMPLATES
# =========================================================================== #

PUBLIC_TEMPLATE = """
<!doctype html>
<html lang="sr">
<head>
  <meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{{ view_title }} &#8211; Sportski Portal</title>
  <meta name="description" content="Sportski Portal — najnovije sportske vesti iz Srbije i sveta: fudbal, ko&#353;arka, tenis, boks. Udarne vesti, rezultati, transferi i analize.">
  <meta property="og:title" content="{% if view_title %}{{ view_title }} &#8211; {% endif %}Sportski Portal">
  <meta property="og:description" content="Najnovije sportske vesti iz Srbije i sveta: fudbal, ko&#353;arka, tenis, boks. Udarne vesti, rezultati i analize.">
  <meta property="og:type" content="website">
  <meta property="og:url" content="https://sportska.onrender.com{{ request.path }}">
  <link rel="canonical" href="https://sportska.onrender.com{{ request.path }}">
  <meta name="twitter:card" content="summary_large_image">
  <meta name="twitter:title" content="{% if view_title %}{{ view_title }} &#8211; {% endif %}Sportski Portal">
  <meta name="twitter:image" content="https://sportska.onrender.com/static/og-cover.jpg">
  <link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 100 100'%3E%3Ctext y='.9em' font-size='90'%3E%E2%9A%BD%3C/text%3E%3C/svg%3E">
  {% if hero %}{% set _img = article_image(hero) %}{% if _img.startswith('https') %}<meta property="og:image" content="{{ _img|e }}">{% else %}<meta property="og:image" content="https://sportska.onrender.com/static/og-cover.jpg">{% endif %}{% else %}<meta property="og:image" content="https://sportska.onrender.com/static/og-cover.jpg">{% endif %}
  <style>{{ css|safe }}</style>
</head>
<body>
  <a href="#main" class="skip-link" style="position:absolute;left:-9999px;top:0;width:1px;height:1px;overflow:hidden;" onfocus="this.style.left='0';this.style.width='auto';this.style.height='auto';this.style.zIndex='9999';this.style.background='#0f172a';this.style.color='#fff';this.style.padding='10px 16px';this.style.overflow='visible'" onblur="this.style.left='-9999px';this.style.width='1px';this.style.height='1px';this.style.overflow='hidden'">Presko&#269;i na sadr&#382;aj</a>
  {% macro card(a, eager=false, rank=none, h='h3') -%}
  <a class="card {% if rank %}trending{% endif %}"
     href="{{ url_for('article_detail', article_id=a['id']) }}">
    <div class="card-media">
      <img src="{{ article_image(a) }}" alt="{{ a.translated_title|truncate(95) }}"
           loading="{{ 'eager' if eager else 'lazy' }}" onerror="this.style.opacity='0'">
      <span class="chip">{{ category_label(a) }}</span>
      {% if a.content_type != 'full' %}<span class="chip">Kratka vest</span>{% endif %}
      {% if rank %}<span class="badge-trending">&#128293; Naj&#269;itanije</span>
      {% elif a.position == 'trending' %}<span class="badge-trending">&#128293; Ru&#269;no istaknuto</span>
      {% elif a.priority == 2 %}<span class="badge-star">&#11088; Zvezda</span>
      {% elif a.priority == 1 %}<span class="badge-hot">&#9889;</span>{% endif %}
      {% if rank %}<span class="card-rank">{{ rank }}</span>{% endif %}
    </div>
    <div class="card-body">
      {% if h == "h2" %}<h2>{{ a.translated_title }}</h2>{% else %}<h3>{{ a.translated_title }}</h3>{% endif %}
      {% set clubs = club_badges(a) %}
      {% if clubs %}
      <div class="club-badges">
        {% for club in clubs %}<span class="club-chip {{ club.css }}">&#9917; {{ club.label }}</span>{% endfor %}
      </div>
      {% endif %}
      <p class="card-excerpt">{{ a.translated_summary }}</p>
      <div class="meta">
        <span><span aria-hidden="true">&#128337;</span> {{ a.published_date }}</span>
        <span class="views"><span aria-hidden="true">&#128065;</span> <b>{{ a.views or 0 }}</b></span>
      </div>
    </div>
  </a>
  {%- endmacro %}

  <header class="topbar">
    <div class="container topbar-inner">
      <a class="brand" href="{{ url_for('index') }}"><span class="ball">&#9917;</span>Sportski<em>Portal</em></a>
      <nav class="site-nav">
        <button type="button" class="hamburger" id="hamburgerBtn"
                aria-label="Meni" aria-expanded="false" aria-controls="navDropdown"
                onclick="document.getElementById('navDropdown').classList.toggle('show');
                         this.classList.toggle('open');
                         this.setAttribute('aria-expanded', this.classList.contains('open'));">
          <span></span><span></span><span></span>
        </button>
        <div class="nav-dropdown" id="navDropdown">
          <a href="{{ url_for('most_read') }}" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#128293;</span> Naj&#269;itanije</a>
          <a href="{{ url_for('archive') }}" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#128218;</span> Arhiva</a>
          <a href="{{ url_for('index') }}#fudbal" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#9917;</span> Fudbal</a>
          <a href="{{ url_for('index') }}#kosarka" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127936;</span> Ko&#353;arka</a>
          <a href="{{ url_for('index') }}#tenis" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127934;</span> Tenis</a>
          <a href="{{ url_for('index') }}#boks" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#129354;</span> Boks</a>
          <a href="{{ url_for('index') }}#ostalo" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127942;</span> Ostalo</a>
          <a href="{{ url_for('index') }}#juzna-amerika" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#10024;</span> Ju&#382;na Amerika</a>
          <a href="{{ url_for('index') }}" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127968;</span> Po&#269;etna</a>
        </div>
      </nav>
    </div>
  </header>

  <main class="container" id="main">
    {% if hero or trending or category_sections or south_america %}

      {% if hero %}
      <div class="hero-head section-head">
        <h2><span class="emoji">&#9889;</span>UDARNA VEST</h2><span class="line"></span>
      </div>
      <a class="hero" href="{{ url_for('article_detail', article_id=hero['id']) }}">
        <img src="{{ article_image(hero) }}" alt="{{ hero.translated_title|truncate(95) }}"
             loading="eager" onerror="this.style.display='none'">
        <div class="hero-overlay"></div>
        <div class="hero-content">
          <div class="hero-tags">
            {% if hero.priority == 2 %}<span class="badge-star">&#11088; Crvena zvezda &#8211; udarna vest</span>
            {% else %}<span class="badge-hot">&#9889; Udarna vest</span>{% endif %}
            <span class="chip">{{ category_label(hero) }}</span>
            {% if hero.content_type != 'full' %}<span class="chip">Kratka vest</span>{% endif %}
            {% for club in club_badges(hero) %}<span class="club-chip {{ club.css }}">&#9917; {{ club.label }}</span>{% endfor %}
            <span class="chip"><span aria-hidden="true">&#128065;</span> {{ hero.views or 0 }}</span>
          </div>
          {% if is_most_read %}<h2>{{ hero.translated_title }}</h2>{% else %}<h1>{{ hero.translated_title }}</h1>{% endif %}
          <p>{{ hero.translated_summary }}</p>
          <div class="meta">
            <span><span aria-hidden="true">&#128337;</span> {{ hero.published_date }}</span>
            <span class="views"><span aria-hidden="true">&#128065;</span> <b>{{ hero.views or 0 }}</b></span>
          </div>
        </div>
      </a>
      {% endif %}

      {% if is_most_read or is_archive %}
      <div class="hero-head section-head" style="margin-top:26px;">
        <h1 style="font-size:1.65rem;">{{ view_title }}</h1><span class="line"></span>
      </div>
      {% if view_intro %}<p style="color:var(--muted); margin:-8px 0 22px;">{{ view_intro }}</p>{% endif %}
      {% endif %}

      {% if trending %}
      <section class="grid-section">
        {% if not is_most_read %}<div class="section-head"><h2><span class="emoji">{% if is_archive %}&#128218;{% else %}&#128293;{% endif %}</span>{{ list_heading }}</h2><span class="line"></span></div>{% endif %}
        <div class="grid">{% for a in trending %}{{ card(a, eager=(loop.index==1), rank=(loop.index if is_most_read else none), h=('h2' if is_most_read else 'h3')) }}{% endfor %}</div>
      </section>
      {% endif %}

      {% if is_archive %}
      <div class="archive-tools">
        <form method="get" action="{{ url_for('archive') }}">
          <label for="archive-category">Filtriraj arhivu</label>
          <select id="archive-category" name="category" onchange="this.form.submit()">
            <option value="">Sve kategorije</option>
            {% for option in archive_categories %}
            <option value="{{ option.key }}" {{ 'selected' if archive_category == option.key else '' }}>{{ option.label }}</option>
            {% endfor %}
          </select>
        </form>
        <span>{{ archive_total }} objavljenih vesti</span>
      </div>
      {% if archive_total_pages > 1 %}
      <nav class="pagination" aria-label="Stranice arhive">
        {% if archive_page > 1 %}<a href="{{ url_for('archive', page=archive_page-1, category=archive_category) }}">&larr; Prethodna</a>{% endif %}
        {% for number in archive_pages %}
          {% if number == archive_page %}<strong>{{ number }}</strong>
          {% else %}<a href="{{ url_for('archive', page=number, category=archive_category) }}">{{ number }}</a>{% endif %}
        {% endfor %}
        {% if archive_page < archive_total_pages %}<a href="{{ url_for('archive', page=archive_page+1, category=archive_category) }}">Sledeća &rarr;</a>{% endif %}
      </nav>
      {% endif %}
      {% endif %}

      {% for section in category_sections %}
      <section class="grid-section" id="{{ section.anchor }}">
        <div class="section-head"><h2><span class="emoji">{{ section.emoji }}</span>{{ section.label }}</h2><span class="line"></span></div>
        <div class="grid">{% for a in section.articles %}{{ card(a) }}{% endfor %}</div>
      </section>
      {% endfor %}

      {% if south_america %}
      <section class="grid-section" id="juzna-amerika">
        <div class="section-head"><h2><span class="emoji">&#10024;</span>JU&#381;NOAMERI&#268;KA MAGIJA <span class="sa-sub"> (Gau&#269;osi i Karijoke)</span></h2><span class="line"></span></div>
        <div class="grid">{% for a in south_america %}{{ card(a) }}{% endfor %}</div>
      </section>
      {% endif %}

    {% else %}
      <div class="empty" style="margin-top:30px;">
        Pokre&#263;em feedove i prevodim vesti iz RAM-a&#8230; osve&#382;i stranicu za nekoliko sekundi!
      </div>
    {% endif %}
  </main>

  <footer class="container footer-text">
    &copy; 2026 Sportski Portal. Sva prava zadr&#382;ana.
  </footer>
</body>
</html>
"""

ARTICLE_DETAIL_TEMPLATE = """
<!doctype html>
<html lang="sr">
<head>
  <meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{{ a.translated_title }} &#8211; Sportski Portal</title>
  <meta name="description" content="{{ (a.translated_summary or a.translated_title)|truncate(160)|e }}">
  <meta property="og:title" content="{{ a.translated_title|e }}">
  <meta property="og:description" content="{{ (a.translated_summary or '')|truncate(200)|e }}">
  <meta property="og:type" content="article">
  <meta property="og:url" content="https://sportska.onrender.com/vest/{{ a.id }}">
  <link rel="canonical" href="https://sportska.onrender.com/vest/{{ a.id }}">
  <meta name="twitter:card" content="summary_large_image">
  <meta name="twitter:title" content="{{ a.translated_title|e }}">
  <meta name="twitter:image" content="https://sportska.onrender.com/static/og-cover.jpg">
  <link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 100 100'%3E%3Ctext y='.9em' font-size='90'%3E%E2%9A%BD%3C/text%3E%3C/svg%3E">
  <script type="application/ld+json">
  {"@context":"https://schema.org","@type":"NewsArticle",
   "headline":{{ a.translated_title|tojson }},
   "description":{{ (a.translated_summary or '')|truncate(300)|tojson }},
   "inLanguage":"sr","datePublished":"{{ a.published_date }}",
   "url":"https://sportska.onrender.com/vest/{{ a.id }}",
   "isBasedOn":"{{ a.link|e }}",
   "author":{"@type":"Organization","name":"Sportski Portal"},
   "publisher":{"@type":"Organization","name":"Sportski Portal"}}
  </script>
  {% set _img = article_image(a) %}{% if _img.startswith('https') %}<meta property="og:image" content="{{ _img|e }}">{% else %}<meta property="og:image" content="https://sportska.onrender.com/static/og-cover.jpg">{% endif %}
  <style>{{ css|safe }}</style>
</head>
<body>
  <header class="topbar">
    <div class="container topbar-inner">
      <a class="brand" href="{{ url_for('index') }}"><span class="ball">&#9917;</span>Sportski<em>Portal</em></a>
      <nav class="site-nav">
        <button type="button" class="hamburger" id="hamburgerBtn"
                aria-label="Meni" aria-expanded="false" aria-controls="navDropdown"
                onclick="document.getElementById('navDropdown').classList.toggle('show');
                         this.classList.toggle('open');
                         this.setAttribute('aria-expanded', this.classList.contains('open'));">
          <span></span><span></span><span></span>
        </button>
        <div class="nav-dropdown" id="navDropdown">
          <a href="{{ url_for('most_read') }}" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#128293;</span> Naj&#269;itanije</a>
          <a href="{{ url_for('archive') }}" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#128218;</span> Arhiva</a>
          <a href="{{ url_for('index') }}#fudbal" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#9917;</span> Fudbal</a>
          <a href="{{ url_for('index') }}#kosarka" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127936;</span> Ko&#353;arka</a>
          <a href="{{ url_for('index') }}#tenis" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127934;</span> Tenis</a>
          <a href="{{ url_for('index') }}#boks" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#129354;</span> Boks</a>
          <a href="{{ url_for('index') }}#ostalo" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127942;</span> Ostalo</a>
          <a href="{{ url_for('index') }}#juzna-amerika" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#10024;</span> Ju&#382;na Amerika</a>
          <a href="{{ url_for('index') }}" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127968;</span> Po&#269;etna</a>
        </div>
      </nav>
    </div>
  </header>

  <main class="article-page">
    <a class="back-link" href="{{ url_for('index') }}">&larr; Nazad na po&#269;etnu</a>

    <article class="article-card">
      <img class="article-cover" src="{{ article_image(a) }}" alt="{{ a.translated_title|truncate(95) }}"
           onerror="this.style.display='none'">
      <div class="article-inner">
        <div class="article-tags">
          <span class="chip">{{ category_label(a) }}</span>
          {% if a.content_type != 'full' %}<span class="chip">Kratka vest</span>{% endif %}
          {% if a.priority == 2 %}<span class="badge-star">&#11088; Crvena zvezda</span>
          {% elif a.priority == 1 %}<span class="badge-hot">&#9889; Udarna vest</span>{% endif %}
          {% for club in club_badges(a) %}<span class="club-chip {{ club.css }}">&#9917; {{ club.label }}</span>{% endfor %}
        </div>

        <h1 class="article-title">{{ a.translated_title }}</h1>

        <div class="meta article-meta">
          <span><span aria-hidden="true">&#128337;</span> {{ a.published_date }}</span>
          <span class="views"><span aria-hidden="true">&#128065;</span> <b>{{ a.views or 0 }}</b> pregleda</span>
        </div>

        <div class="article-body">
          {% for para in paragraphs %}<p>{{ para }}</p>{% endfor %}
        </div>

        <p class="source-discreet">
          Informacije u ovom &#269;lanku preuzete su sa portala
          <a href="{{ a.link }}" target="_blank" rel="noopener noreferrer"
             style="color:var(--muted); text-decoration:underline;">{{ a.source }}</a>.
        </p>
      </div>
    </article>

    <p style="text-align:center; margin:26px 0 40px;">
      <a class="btn btn-ghost" href="{{ url_for('index') }}">&larr; Vrati se na sve vesti</a>
    </p>
  </main>
</body>
</html>
"""

ARTICLE_404_TEMPLATE = """
<!doctype html>
<html lang="sr">
<head>
  <meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Vest nije pronađena</title><style>{{ css|safe }}</style>
</head>
<body>
  <header class="topbar">
    <div class="container topbar-inner">
      <a class="brand" href="{{ url_for('index') }}"><span class="ball">&#9917;</span>Sportski<em>Portal</em></a>
    </div>
  </header>
  <main class="container">
    <div class="empty notfound">
      <h3 style="margin-bottom:12px;">&#128533; Ta vest nije dostupna</h3>
      <p style="margin-bottom:18px;">ILI je jo&#353; uvek na &#269;ekanju za odobrenje, ILI je obrisana.</p>
      <a class="btn btn-green" href="{{ url_for('index') }}">&larr; Nazad na po&#269;etnu</a>
    </div>
  </main>
</body>
</html>
"""

ADMIN_LOGIN_TEMPLATE = """
<!doctype html>
<html lang="sr">
<head>
  <meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Admin prijava</title><style>{{ css|safe }}</style>
</head>
<body>
  <header class="topbar">
    <div class="container topbar-inner">
      <div class="brand"><span class="ball">&#128274;</span>Admin<em>Prijava</em></div>
      <a class="btn btn-ghost" href="{{ url_for('index') }}">Javni sajt</a>
    </div>
  </header>
  <main class="container">
    <section class="panel" style="max-width:480px; margin:70px auto; padding:24px;">
      <div class="panel-head">Prijava u admin panel</div>
      {% if error %}<div class="flash" style="color:#fecaca; border-color:var(--red);">{{ error }}</div>{% endif %}
      <form method="post" action="{{ url_for('admin_login') }}">
        <input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
        <label for="password">Lozinka</label>
        <input type="password" id="password" name="password" required autofocus>
        <button type="submit" class="btn btn-green" style="margin-top:18px; width:100%;">&#128274; Prijavi se</button>
      </form>
    </section>
  </main>
</body>
</html>
"""


ADMIN_TEMPLATE = """
<!doctype html>
<html lang="sr">
<head>
  <meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Admin kontrola</title><style>{{ css|safe }}</style>
</head>
<body>
  <header class="topbar">
    <div class="container topbar-inner">
      <div class="brand"><span class="ball">&#128736;</span>Admin<em>Kontrola</em></div>
      <div style="display:flex; gap:10px; align-items:center;">
        <a class="btn btn-ghost" href="{{ url_for('index') }}">&larr; Javni sajt</a>
        <form method="post" action="{{ url_for('admin_logout') }}" style="display:inline;">
          <input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
          <button type="submit" class="btn btn-ghost">Odjava</button>
        </form>
      </div>
    </div>
  </header>
  <main class="container">
    {% with messages = get_flashed_messages() %}
      {% for message in messages %}<div class="flash" style="margin-top:20px;">{{ message }}</div>{% endfor %}
    {% endwith %}
    <div class="admin-wrap">
      <aside class="admin-list">
        <div class="admin-group">
          <div class="group-head pending">&#9203; Na &#269;ekanju ({{ pending_total }})</div>
          {% if pending %}
            {% for a in pending %}
            <a class="pending-item {% if selected and selected['id'] == a['id'] %}active{% endif %}"
               href="{{ url_for('admin', article_id=a['id'], pending_page=pending_page, published_page=published_page) }}">
              <div class="pi-title">{{ a.translated_title or a.original_title }}{% if a.priority == 2 %} <span class="badge-star">&#11088;</span>{% elif a.priority == 1 %} <span class="badge-hot">&#9889;</span>{% endif %}</div>
              <div class="pi-meta meta">
                <span>{{ a.source }}</span>
                {% if a.last_error %}<span style="color:#fca5a5;">&#9888; poku&#353;aj {{ a.attempt_count or 0 }}</span>{% endif %}
              </div>
            </a>
            {% endfor %}
          {% else %}
            <p class="empty-small">Nema vesti na &#269;ekanju.</p>
          {% endif %}
          {% if pending_total_pages > 1 %}
          <nav class="pagination" aria-label="Stranice vesti na čekanju">
            {% if pending_page > 1 %}<a href="{{ url_for('admin', pending_page=pending_page-1, published_page=published_page) }}">&larr;</a>{% endif %}
            {% for number in pending_pages %}
              {% if number == pending_page %}<strong>{{ number }}</strong>
              {% else %}<a href="{{ url_for('admin', pending_page=number, published_page=published_page) }}">{{ number }}</a>{% endif %}
            {% endfor %}
            {% if pending_page < pending_total_pages %}<a href="{{ url_for('admin', pending_page=pending_page+1, published_page=published_page) }}">&rarr;</a>{% endif %}
          </nav>
          {% endif %}
        </div>

        <div class="admin-group">
          <div class="group-head published">&#128994; Objavljene vesti &#8211; u&#382;ivo ({{ published_total }})</div>
          {% if published %}
            {% for a in published %}
            <a class="pending-item {% if selected and selected['id'] == a['id'] %}active{% endif %}"
               href="{{ url_for('admin', article_id=a['id'], pending_page=pending_page, published_page=published_page) }}">
              <div class="pi-title">{{ a.translated_title }}</div>
              <div class="pi-meta meta">
                <span>{{ a.source }}</span>
                <span class="views"><span aria-hidden="true">&#128065;</span> <b>{{ a.views or 0 }}</b></span>
              </div>
            </a>
            {% endfor %}
          {% else %}
            <p class="empty-small">Jo&#353; uvek nema objavljenih vesti.</p>
          {% endif %}
          {% if published_total_pages > 1 %}
          <nav class="pagination" aria-label="Stranice objavljenih vesti">
            {% if published_page > 1 %}<a href="{{ url_for('admin', pending_page=pending_page, published_page=published_page-1) }}">&larr;</a>{% endif %}
            {% for number in published_pages %}
              {% if number == published_page %}<strong>{{ number }}</strong>
              {% else %}<a href="{{ url_for('admin', pending_page=pending_page, published_page=number) }}">{{ number }}</a>{% endif %}
            {% endfor %}
            {% if published_page < published_total_pages %}<a href="{{ url_for('admin', pending_page=pending_page, published_page=published_page+1) }}">&rarr;</a>{% endif %}
          </nav>
          {% endif %}
        </div>
      </aside>

      <section class="admin-review">
        {% if selected %}
        <div class="panel-head">
          Pregled i obrada #{{ selected.id }}
          <span class="sel-status">
            {% if selected.status == 'published' %}<span class="badge-live">&#128994; U&#382;ivo na sajtu</span>
            {% else %}<span class="chip">&#9203; Na &#269;ekanju</span>{% endif %}
          </span>
        </div>
        <div class="orig-ref">
          <div class="orig-label">Original &mdash; {{ selected.source }}</div>
          <strong>{{ selected.original_title }}</strong>
          <p>{{ selected.original_summary }}</p>
          <div class="pi-meta meta" style="margin-top:10px;">
            <span>Kategorija: {{ category_label(selected) }}</span>
            <span>Tip sadržaja: {{ 'duža vest' if selected.content_type == 'full' else 'kratka vest' }}</span>
            {% if selected.attempt_count %}<span>Pokušaji: {{ selected.attempt_count }}</span>{% endif %}
          </div>
          {% if selected.last_error %}
          <p style="color:#fca5a5; margin-top:10px;">Poslednja greška: {{ selected.last_error }}. Vest ostaje sačuvana za automatski retry.</p>
          {% endif %}
        </div>
        <form method="post" action="{{ url_for('publish_article', article_id=selected.id) }}">
          <input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
          <label for="title">Naslov (srpski)</label>
          <input type="text" id="title" name="translated_title" value="{{ selected.translated_title }}" required>
          <label for="summary">Sa&#382;etak / &#269;lanak (srpski)</label>
          <textarea id="summary" name="translated_summary" rows="10" required>{{ selected.translated_summary }}</textarea>

          <label>Pozicija na naslovnoj strani</label>
          <div class="pos-options">
            <label class="pos-opt">
              <input type="radio" name="position" value="hero"
                     {{ 'checked' if selected.position == 'hero' else '' }}>
              <span class="pos-ico">&#9889;</span>
              <span class="pos-text"><b>Udarna vest / Hero</b><small>Velika gornja sekcija (samo jedna)</small></span>
            </label>
            <label class="pos-opt">
              <input type="radio" name="position" value="trending"
                     {{ 'checked' if selected.position == 'trending' else '' }}>
              <span class="pos-ico">&#128293;</span>
              <span class="pos-text"><b>Ru&#269;no istaknuta vest</b><small>Uredni&#269;ka oznaka; ne uti&#269;e na Naj&#269;itanije rangiranje</small></span>
            </label>
            <label class="pos-opt">
              <input type="radio" name="position" value="standard"
                     {{ 'checked' if selected.position not in ('hero','trending') else '' }}>
              <span class="pos-ico">&#9917;</span>
              <span class="pos-text"><b>Standardna kartica</b><small>Raspore&#273;uje se po kategoriji</small></span>
            </label>
          </div>

          <div class="actions">
            {% if selected.status == 'published' %}
              <button type="submit" class="btn btn-green">&#128190; Sa&#269;uvaj izmene (ostaje u&#382;ivo)</button>
              <a class="btn btn-ghost" href="{{ url_for('article_detail', article_id=selected.id) }}" target="_blank" rel="noopener">&#128065; Pogledaj na sajtu</a>
            {% else %}
              <button type="submit" class="btn btn-green">&#10003; Objavi vest</button>
            {% endif %}
          </div>
        </form>
        <form method="post" action="{{ url_for('delete_article', article_id=selected.id) }}"
              onsubmit="return confirm('Obrisati ovu vest zauvek? Ova radnja se ne mo&#382;e poni&#353;titi.');">
          <input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
          {% if selected.status == 'published' %}
            <button type="submit" class="btn btn-red big">&#128465; Obri&#353;i vest zauvek</button>
          {% else %}
            <div class="actions" style="margin-top:14px; border-top:1px solid var(--border); padding-top:16px;">
              <button type="submit" class="btn btn-red">&#128465; Obri&#353;i vest</button>
            </div>
          {% endif %}
        </form>
        {% else %}
        <div class="empty">&larr; Izaberite vest sa leve liste (na &#269;ekanju ili ve&#263; objavljenu) da biste je pregledali, uredili ili obrisali.</div>
        {% endif %}
      </section>
    </div>
  </main>
</body>
</html>
"""


# =========================================================================== #
#  ROUTES
# =========================================================================== #

def _backfill_categories() -> int:
    """Recompute persisted categories, fixing records from old broad rules."""
    changed = 0
    with _db_lock:
        rows = _db.execute(
            """SELECT id, source, original_title, original_summary, category
               FROM articles"""
        ).fetchall()
        for row in rows:
            source = row["source"] or ""
            category = _SOURCE_CATEGORY_HINTS.get(source) or classify_category(
                row["original_title"] or "",
                row["original_summary"] or "",
                source,
            )
            if category != (row["category"] or ""):
                _db.execute("UPDATE articles SET category=? WHERE id=?", (category, row["id"]))
                changed += 1
        if changed:
            _db.commit()
    if changed:
        print(f"[CATEGORY] corrected {changed} article categories")
    return changed


def _archive_old_published() -> int:
    """Move old non-hero/non-manual articles out of the homepage, never delete.

    RSS dates are stored as display text, so only our stable UTC format is
    eligible. Unknown or provider-specific dates stay visible until a later
    manual decision rather than being archived accidentally.
    """
    if AUTO_ARCHIVE_DAYS <= 0:
        return 0
    cutoff = time.time() - AUTO_ARCHIVE_DAYS * 86400
    archived_at = time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime())
    with _db_lock:
        rows = _db.execute(
            """SELECT id, published_date FROM articles
               WHERE status='published' AND is_archived=0
                 AND position NOT IN ('hero','trending')"""
        ).fetchall()
        ids = []
        for row in rows:
            value = (row["published_date"] or "")[:10]
            try:
                published_epoch = calendar.timegm(time.strptime(value, "%Y-%m-%d"))
            except (TypeError, ValueError, OverflowError):
                continue
            if published_epoch < cutoff:
                ids.append(row["id"])
        if ids:
            for article_id in ids:
                _db.execute(
                    "UPDATE articles SET is_archived=1, archived_at=? WHERE id=?",
                    (archived_at, article_id),
                )
            _db.commit()
    if ids:
        print(f"[ARCHIVE] {len(ids)} old articles moved to archive (no deletion)")
    return len(ids)


def _published_articles(order_by_views: bool = False, limit: int | None = None,
                         offset: int = 0, include_archived: bool = False,
                         category: str = ""):

    sql = """SELECT id, source, original_title, original_summary, link,
                     translated_title, translated_summary, published_date,
                     priority, position, category, content_type, is_archived,
                     archived_at, views
              FROM articles WHERE status='published'"""
    if not include_archived:
        sql += " AND is_archived=0"
    params = []
    if category in CATEGORY_LABELS:
        sql += " AND category=?"
        params.append(category)
    if order_by_views:
        sql += " ORDER BY views DESC, published_date DESC, id DESC"
    else:
        sql += " ORDER BY published_date DESC, id DESC"
    if limit is not None:
        sql += " LIMIT ?"
        params.append(limit)
        if offset:
            sql += " OFFSET ?"
            params.append(offset)
    with _db_lock:
        return _db.execute(sql, tuple(params)).fetchall()


def _article_age_hours(article) -> float | None:
    """Article age in hours; None when the date is unparsable.
    Unknown dates are treated as fresh so nothing is ever hidden by accident."""
    value = (article.get("published_date") or "").strip()
    for fmt, cut in (("%Y-%m-%d %H:%M:%S", 19), ("%Y-%m-%d", 10)):
        try:
            epoch = calendar.timegm(time.strptime(value[:cut], fmt))
            return max(0.0, (time.time() - epoch) / 3600.0)
        except (TypeError, ValueError, OverflowError):
            continue
    return None


def _article_is_fresh(article, max_hours: float) -> bool:
    age = _article_age_hours(article)
    return age is None or age <= max_hours


def _archive_count(category: str = "") -> int:
    sql = "SELECT COUNT(*) AS c FROM articles WHERE status='published'"
    params = []
    if category in CATEGORY_LABELS:
        sql += " AND category=?"
        params.append(category)
    with _db_lock:
        return int(_db.execute(sql, tuple(params)).fetchone()["c"] or 0)


def _category_sections(articles, excluded_ids: set[int] | None = None) -> list[dict]:
    excluded_ids = excluded_ids or set()
    sections = []
    for config in CATEGORY_CONFIG:
        section_articles = [
            article for article in articles
            if article["id"] not in excluded_ids
            and article_category(article) == config["key"]
        ][:HOME_CATEGORY_LIMIT]
        if section_articles:
            sections.append({**config, "articles": section_articles})
    return sections


@app.route("/")
def index():
    _archive_old_published()
    articles = _published_articles()

    # Hero is editorial but time-boxed: a 'hero' pin expires after
    # HERO_MAX_AGE_HOURS hours, so yesterday's derby cannot block today's news.
    # Expired pins are demoted to 'standard' in the DB (keeps admin truthful).
    hero = next(
        (a for a in articles
         if a["position"] == "hero" and _article_is_fresh(a, HERO_MAX_AGE_HOURS)),
        None)
    stale_hero_ids = [
        a["id"] for a in articles
        if a["position"] == "hero" and not _article_is_fresh(a, HERO_MAX_AGE_HOURS)]
    if stale_hero_ids:
        placeholders = ",".join("?" * len(stale_hero_ids))
        with _db_lock:
            _db.execute(
                f"UPDATE articles SET position='standard' WHERE id IN ({placeholders})",
                tuple(stale_hero_ids))
            _db.commit()
    if hero is None:
        # Winner order: fresh Star (Zvezda) story -> any high-priority story ->
        # the freshest article overall, so the slot is never empty.
        hero = next((a for a in articles if a["priority"] == 2), None) or \
            next((a for a in articles if a["priority"] == 1), None) or \
            (articles[0] if articles else None)
    hero_id = hero["id"] if hero else None

    # "Najcitanije" = most viewed among RECENT stories only
    # (TRENDING_MAX_AGE_HOURS, default 24h). Older giants can no longer squat
    # the slot forever; if fewer than 3 fresh stories exist, the newest ones
    # pad the row so the homepage never looks empty.
    ranked = sorted(
        (a for a in articles
         if a["id"] != hero_id and _article_is_fresh(a, TRENDING_MAX_AGE_HOURS)),
        key=lambda a: (a["views"] or 0, a["published_date"] or "", a["id"]),
        reverse=True,
    )
    trending = ranked[:3]
    if len(trending) < 3:
        have = {a["id"] for a in trending} | ({hero_id} if hero_id is not None else set())
        fill = sorted(
            (a for a in articles if a["id"] not in have),
            key=lambda a: (a["published_date"] or "", a["id"]),
            reverse=True,
        )
        trending = (trending + fill)[:3]
    featured_ids = ({hero_id} if hero_id is not None else set()) | {a["id"] for a in trending}
    category_sections = _category_sections(articles, featured_ids)
    south_america = [
        a for a in articles
        if a["id"] not in featured_ids and is_south_america(a)
    ][:HOME_CATEGORY_LIMIT]
    south_ids = {a["id"] for a in south_america}
    category_sections = [
        {**section, "articles": [a for a in section["articles"] if a["id"] not in south_ids]}
        for section in category_sections
    ]
    category_sections = [section for section in category_sections if section["articles"]]

    return render_template_string(
        PUBLIC_TEMPLATE, hero=hero, trending=trending,
        category_sections=category_sections, south_america=south_america,
        view_title="Sportske vesti", view_intro="", is_most_read=False,
        is_archive=False, list_heading="NAJČITANIJE", css=BASE_CSS,
    )


@app.route("/najcitanije")
def most_read():
    """Dedicated persisted view-count ranking, not a manually curated list."""
    ranked = _published_articles(
        order_by_views=True, limit=50, include_archived=True,
    )
    return render_template_string(
        PUBLIC_TEMPLATE, hero=None, trending=ranked,
        category_sections=[], south_america=[],
        view_title="Najčitanije vesti",
        view_intro="Rangirano prema stvarnom broju pregleda.",
        is_most_read=True, is_archive=False, list_heading="NAJČITANIJE",
        css=BASE_CSS,
    )


@app.route("/arhiva")
def archive():
    """Paginated catalogue of every published article; nothing is deleted."""
    _archive_old_published()
    category = (request.args.get("category") or "").strip().lower()
    if category not in CATEGORY_LABELS:
        category = ""
    total = _archive_count(category)
    total_pages = max(1, (total + ARCHIVE_PAGE_SIZE - 1) // ARCHIVE_PAGE_SIZE)
    page = max(1, request.args.get("page", 1, type=int) or 1)
    page = min(page, total_pages)
    rows = _published_articles(
        limit=ARCHIVE_PAGE_SIZE,
        offset=(page - 1) * ARCHIVE_PAGE_SIZE,
        include_archived=True,
        category=category,
    )
    page_start = max(1, page - 2)
    page_end = min(total_pages, page + 2)
    return render_template_string(
        PUBLIC_TEMPLATE, hero=None, trending=rows,
        category_sections=[], south_america=[],
        view_title="Arhiva vesti",
        view_intro="Sve objavljene vesti ostaju sačuvane; prikaz je podeljen po stranicama.",
        is_most_read=False, is_archive=True,
        list_heading="ARHIVA VESTI", archive_category=category,
        archive_categories=CATEGORY_CONFIG, archive_page=page,
        archive_total=total, archive_total_pages=total_pages,
        archive_pages=range(page_start, page_end + 1), css=BASE_CSS,
    )


@app.route("/vest/<int:article_id>")
def article_detail(article_id: int):
    """Internal Serbian article reader (no external redirect). Counts the view."""
    db = get_db()
    with _db_lock:
        db.execute("UPDATE articles SET views = views + 1 WHERE id = ?", (article_id,))
        db.commit()
        row = db.execute("SELECT * FROM articles WHERE id = ?", (article_id,)).fetchone()

    # Only published articles are publicly readable; pending/missing -> 404.
    if not row or row["status"] != "published":
        return render_template_string(ARTICLE_404_TEMPLATE, css=BASE_CSS), 404

    body = row["translated_summary"] or ""
    paragraphs = [p.strip() for p in re.split(r"\n{2,}|\r\n{2,}", body) if p.strip()]
    if not paragraphs and body:
        paragraphs = [body]

    return render_template_string(
        ARTICLE_DETAIL_TEMPLATE, a=row, paragraphs=paragraphs, css=BASE_CSS,
    )



# ---------------------------------------------------------------------------
# v7 quick-wins (audit 2026-10-16): robots.txt, sitemap.xml, staticka OG korica
# ---------------------------------------------------------------------------
SITE_URL = "https://sportska.onrender.com"

_OG_COVER_JPG_B64 = (
    "/9j/4AAQSkZJRgABAQAAAQABAAD/2wBDAAUEBAQEAwUEBAQGBQUGCA0ICAcHCBALDAkNExAUExIQ"
    "EhIUFx0ZFBYcFhISGiMaHB4fISEhFBkkJyQgJh0gISD/2wBDAQUGBggHCA8ICA8gFRIVICAgICAg"
    "ICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICD/wAARCAJ2BLADASIA"
    "AhEBAxEB/8QAHwAAAQUBAQEBAQEAAAAAAAAAAAECAwQFBgcICQoL/8QAtRAAAgEDAwIEAwUFBAQA"
    "AAF9AQIDAAQRBRIhMUEGE1FhByJxFDKBkaEII0KxwRVS0fAkM2JyggkKFhcYGRolJicoKSo0NTY3"
    "ODk6Q0RFRkdISUpTVFVWV1hZWmNkZWZnaGlqc3R1dnd4eXqDhIWGh4iJipKTlJWWl5iZmqKjpKWm"
    "p6ipqrKztLW2t7i5usLDxMXGx8jJytLT1NXW19jZ2uHi4+Tl5ufo6erx8vP09fb3+Pn6/8QAHwEA"
    "AwEBAQEBAQEBAQAAAAAAAAECAwQFBgcICQoL/8QAtREAAgECBAQDBAcFBAQAAQJ3AAECAxEEBSEx"
    "BhJBUQdhcRMiMoEIFEKRobHBCSMzUvAVYnLRChYkNOEl8RcYGRomJygpKjU2Nzg5OkNERUZHSElK"
    "U1RVVldYWVpjZGVmZ2hpanN0dXZ3eHl6goOEhYaHiImKkpOUlZaXmJmaoqOkpaanqKmqsrO0tba3"
    "uLm6wsPExcbHyMnK0tPU1dbX2Nna4uPk5ebn6Onq8vP09fb3+Pn6/9oADAMBAAIRAxEAPwC9RRRX"
    "zJ+FBRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUU"
    "UUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRR"
    "QAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFA"
    "BRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAF"
    "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"
    "Eo8S/wDQxan/AOBcn+NZFFHs4dkH1el/IvuQUUUVobBRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUV12hfDL"
    "4g+JYkn0Twdqt3A/Kzi3ZIm+jthT+ddSv7OfxmePePBbge99bA/kZM1PMl1HZnlFFelXfwH+Ltkm"
    "6bwNfOP+mDRzH8kY1yGreEfFeg7v7b8NappoXqbqzkiH5sBTTT2CxiUUUUxBRRRQAUUUUAFFFFAB"
    "RRRQAUUUUAFFFFABRWlpHh/XvEFwbfQtFvtUmHVLO3eYj6hQcV3ln8AfjBfRh4fA92gP/PeaKE/k"
    "7g0m0tx2PMaK9TuP2efjJbIXk8EzMB/zyureQ/kshNcXrvgvxd4ZyfEPhnU9LQHHmXNq6IfoxGD+"
    "BpJp7BZmBRRRVCCiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAoq7pmk6r"
    "rV4LLR9Mu9RuT0htYWlc/wDAVBNd/Y/AT4v6hGJIPA96gPa4kigP5SMDSbS3HY8zor1WX9nb4ywj"
    "L+CpT/uXls38pDWBqPwl+JulKz3vgTWlRfvPHaPKo+pQEUuZdwsziaKmubW5s52gu7eW3lXrHKhV"
    "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"
    "fEHUfDU3hDWP7SSyiuFnP2eWHYWKbf8AWKuc7T0z0r5/oqY01F3Q3JsK9S+A+r+C/DnxTt/EnjfV"
    "l0+z02F5bbNvLN5k5G1eI1bGAzNk9wK8torRq6sSj9EP+Gkfgt/0Of8A5Trv/wCNVn63+0x8Kbbw"
    "9qM+jeJ/tupx28jWtv8AYLlfNl2nYuWjAALY5Jr8/wCisvZRK52STTS3FxJcTyNJLKxd3Y5LMTkk"
    "/jUdFFbEBRRRQB9bfs//AB08GeFfhl/wjPjbXG06ewuX+yZtppg8L/PjMaNjDl+vYivWv+Gkfgt/"
    "0Of/AJTrv/41X530Vk6SbuWpM+of2jviD8LfiL4R0yfwz4lW81zTLk7IjZXEfmQuMONzxgcFUPJ7"
    "H1r5ktHWK+t5XOESRWJ9ADUNFXGPKrEt31P0Q/4aR+C3/Q5/+U67/wDjVH/DSPwW/wChz/8AKdd/"
    "/Gq/O+is/YxK52foh/w0j8Fv+hz/APKdd/8Axqj/AIaR+C3/AEOf/lOu/wD41X530UexiHOz9EP+"
    "Gkfgt/0Of/lOu/8A41R/w0j8Fv8Aoc//ACnXf/xqvzvoo9jEOdna/FfXNL8S/FvxHruiXX2rTry6"
    "8yCbYyb12gZ2sAR07iuKoorVK2hIUUUUxBRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUA"
    "FFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAU"
    "UUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRR"
    "RQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFF"
    "ABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUA"
    "FFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAU"
    "UUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRR"
    "RQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFF"
    "ABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUA"
    "FFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAU"
    "UUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRR"
    "RQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUVb03Tb3V"
    "9Tg03ToGnup22oi9/wDAAck9q9p0n4EW32ZX1zWpTMRlo7NQFU+m5gc/kKAvY8Lor6Em+BPhtlxb"
    "6vqUbeshjcfoorzjx78OX8E21rdrqovobmQxgGLy2UgZ9Tmiwro4KiiigYUUUUAFFFFABRRRQAUU"
    "UUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRVrT7C71TUYNOsIvOurhwkabgu4ntkkAfjX"
    "Sah8NvGul6dPqN9ovk2tuhkkf7TE21R1OA5J/CgDkaKKKACiiigAorU8PafDq3ijS9LuWdIbu5jh"
    "doyAwDMAcZBGefSvY/EHwb8MaT4Y1TVLe/1R5rS1knRZJYypZVJGcIDjj1osFzwiiiigAooooAKK"
    "KKACiiigAooooAKKKKACiiigAooooAKKKKACiitfQfDWt+JrmW20Oy+1ywpvdfMRMDOM/MRQBkUV"
    "0GveDPEvhm1iudb037JFM/lo3nRvlsZx8rHtXP0AFFe1eC/hN4c8R+DNP1q+vdSjuLkOXWGSMIMO"
    "yjAKE9AO9ebeNdDtPDnjTUNFsZJZLe2KBGmILnKKxyQAOpPaiwXOeooooAKKKKACiiigAooooAKK"
    "KKACiiigAor2rwX8JvDniPwZp+tX17qUdxchy6wyRhBh2UYBQnoB3rzbxrodp4c8aahotjJLJb2x"
    "QI0xBc5RWOSAB1J7UWC5z1FFFABRRRQAUUUUAFFe0eCPhR4d8S+CtP1u+vdRjuLnzN6wyRhBtkZR"
    "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"
    "uxB+qBhXIfFLx14V8R+Dk0/RtU+1XIukkKeRInyhWBOWUDuKGJHTfBSRX+HbKpyY7yRW9jhT/Iiu"
    "C+N2m3kfjO31HyHNrPaoiyhTt3hmyufXGD+NY/w48f8A/CGXs9vewvPpl0QZFj+9Gw/iUHrxwR9P"
    "Tn2GT4weBUtvOXUp5XxnyVtn3fTkAfrR0DZmZ8FtAv8ASfDd7f38D27ahKpjjkGG2KDhsdslj+We"
    "9c/8fP8AX+Hv924/nHW5oPxm0O+1DUn1uYaVaKY1s4zE8juPm3MxRTg/d4/nya4n4u+K9A8US6M2"
    "hX/2sWwmEv7p027tmPvAZ6HpR0DqeXUUUUigooooAKKKKACiiigAooooAKKKKACiiigAooooAKKK"
    "KACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAoooo"
    "AKKKKACt/wAFf8lA0D/r/h/9DFYFFAH1/wCNP+RB8Qf9g+f/ANFmvkCiihsSVgooooGFFFFABRRR"
    "QAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFA"
    "BRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFd98MvBul+MdTv7fVJrqNLaJZF+zuq5JO"
    "Ocqa4GigD66utU8M+BvDsVvPdxWlraRbIoN+6R8dgOrE/wD66+V9e1aXXfEV/rEy7Gu5mk25ztHY"
    "fgMD8KzaKGxJWCiiigYUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFF"
    "ABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUA"
    "FFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAU"
    "UUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRR"
    "RQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFF"
    "ABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUA"
    "FFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAU"
    "UUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRR"
    "RQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFF"
    "ABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUA"
    "FFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAU"
    "UUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRR"
    "RQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFF"
    "ABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUA"
    "FFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAU"
    "UUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRR"
    "RQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFF"
    "ABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUA"
    "FFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFW9O0zUNWvFs9Ns5bqdsfLGucDIGSegGSOTwM128Xwy"
    "a1hSTxJ4l07RWmUGKN2DMT/EDuZRkZHQsOfpnGpWp09JM5K+MoUHapKz7bv7lqee0V6J/ZPwl/6G"
    "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"
    "/wDjVH/CwPDX/ROdM/OP/wCNUe1q/wDPt/ev8w+tYr/oHf8A4FH/ADPO6K9E/wCFgeGv+ic6Z+cf"
    "/wAao/4WB4a/6Jzpn5x//GqPa1f+fb+9f5h9axX/AEDv/wACj/med0V6J/wsDw1/0TnTPzj/APjV"
    "H/CwPDX/AETnTPzj/wDjVHtav/Pt/ev8w+tYr/oHf/gUf8zjNJ0PVtduTb6TYS3Tr94qMKnBI3Mc"
    "Bc4OMnnFd5Y6Nonw/SHV/E0y3mtmLzbXTIxkRvnAJbkZHHzHgENt3EA1kal8UPFeoQ+VHPBYKVZW"
    "NrHhmB92LEEdiuDz9K4yWWWeZ5ppGllkYs7ucsxPJJJ6mk4Vauk/dXZb/f8A5Eyo4rFe7XahDqk7"
    "t+TlpZeiv5l7Wta1DX9Vl1LUpvMmfgKOFjXsqjsB/iTkkms6iiuqMVFWWx6kIRhFQgrJBRRRVFBR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUU"
    "AFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQA"
    "UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABR"
    "RRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFF"
    "FABRRRQB6P4F+Dfif4g+H5ta0a+0u3t4rhrZlu5ZFcsFViQFRhjDjv61wur6ZPouu6ho108b3Fhc"
    "SW0jRklSyMVJBIBxkcZAr6x/Zk/5JXf/APYWl/8ARUNfMvj7/kp3ir/sL3f/AKOapT1GdivwJ8XN"
    "4DHjIajo/wDZ507+0/L86XzfK8rzMY8vG7HbOM968qr7ii/5NeX/ALFL/wBs6+Y/hJ8NX+I3iaaC"
    "5nkttJsVWS7ljxvOSdqLngE4PPYA0JiPOa9q8R/Af/hH/hjL41/4Sr7T5drDc/ZPsOzO8qNu/wAw"
    "9N3XHau48V/Dz4B6deL4Ul1c6Fr0iqElFxLKUYj5fM3ZRc5BwdvB7da7v4rWb6d+ztqunyOrvbWV"
    "vCzL0JV4wSPyouB8RUV6X8LdG+GmoxatefEXVzZJamIW0ImKedu37/lUFmxhenTNeuaN4T/Zu8WX"
    "66JoMm7UJAdgFxdRu2Bk7fN+UnAJwAadwPliivRPi18OD8OfFENpbXUl1pl7GZbWWUDeMHDI2OCR"
    "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"
    "KKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAo"
    "oooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACii"
    "igAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKK"
    "ACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooA"
    "KKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAo"
    "oooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACii"
    "igAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKK"
    "ACiivavhd+zt4m+JGgJ4ifU7bRNIldkglljMsk204ZlQEDaCCMlhyDxUtpasaVzxWivp3Xf2PfEl"
    "nZNN4e8W2OrTqM+RcW7Wpb2UhnGfrge9eN/Df4ey+P8A4kw+C5tT/siV1mLz+T5+wxqSRt3LnpjO"
    "aSmmrodmcNRX0xd/sieI08WwaXp/iaGfS/s4mn1Ke0MQjYsR5aRh2LtgZ6gAH6ZxPiL+zD4m8E+G"
    "rjxDpWsw+IbK0QyXSJbmCWJB1cLuYMo6nnIHOMZwc8e4crPAqK6Lwb4L8Q+PfEsPh/w3ZfabuQF2"
    "ZjtSFB1d27KMj8wBkkCvoi1/Y11N7IPe+PbWG6xzHDp7SID/AL5kU/8AjtDkluCTZ8q0V6R8Tvg1"
    "4t+Fs8MmrrDe6Zctsh1C1JMZbGdjAjKtgZweDzgnBx2Pwn/Z2/4Wh4HPib/hMP7JxdSW32f+z/P+"
    "6FO7d5q9d3THanzK1xWex4NRX0jo37JfiK58OT6vr/iSDR5EjeVLVbUzybQCRv8AnUKTjoN2M+vF"
    "fRHwO+G//CtvAcll/bP9qf2pKuob/s/k+VuiQbMbmzjb14+lRKolsUos/Oaivqf4q/s1/wBl6Z4t"
    "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"
    "BRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAF"
    "FFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABX1f8Jfj"
    "R4Bf4ND4aeNtSu9AkSCa0F7Ar4kjkZiCroCUcbiORjgHJyRXyhX0P8OviD8Ebj4e6V4Q+J3hItda"
    "cJEXUxAX3q0rvjfGRKuN+McjjNZzV0VE7Pw58EtKvBcaz8FfjbcC8tiCyhw4yc7RL5ZUgHB6oQcH"
    "g1wXwC0zVNG/aoGla2mzUrX7bFcgYI8wI24jHBBPIxXrGi/F/wDZy+GOl3reAoJ5ZroBpIbW2uDJ"
    "MVztBe4xgDJ78ZPFeX/A7xHceLv2s28TXUKwS6l9suDEpyIwY2wue+BgZ9qz1s7laaHTfthazq8e"
    "t+G9ES5mi0praS5MasQssu/blvUqAMem4+tes/s26lqWv/AayXXJHvFinntI2nO8yQg8Ak9QMlfo"
    "MdqzvjV4t+GNp4x0nwn8VPDhv9LmtPtltfR799tIXZWB8sh9pCr90nkcg8Y5Lxl+0X8PfDHw7Phf"
    "4TRtLOYDb2rx2zwQ2QOcv84DM/JI4OTyT6zZuKSQ9ncs/sl6ZplrB44uLXa8yaglsr9SIVDFefQk"
    "n649q8F+NfibxHJ8ffEF1LqV3BcaZemGyKSspt0TATZj7uRhuOpJPeoPg18Wrz4U+Kp7w2rX2kX6"
    "rHe2qttYhSdroTxuXLcHggkcdR9Ban8Rf2WvF2tQ+LfEVqG1lApIubG53sV6B1jBjcgAD5s8ADpV"
    "u8ZN2uLdWO5+LIGu/srajea5Goun0q3vH3DBSf5G49Du4/HFY/7J/wDyQ9v+wpP/AOgpXjHx0/aE"
    "tvH2i/8ACI+ErW4t9FaRXurm4AV7nacqgUE7UBAbnkkDgY56v9nv4w/DnwP8K20TxT4i/s+/N/LN"
    "5X2SeX5GCAHKIw7HvU8r5B3Vz538aeMfEHiD4h6r4gu9VuhdtdSeUyysPIQMQqJg/KAMDivq39j7"
    "/kmGu/8AYXb/ANEx18X6jLHPqt3PE26OSZ3U4xkFiRXvX7Onxn8P/DmHVdB8VefDp19KtzFdQxmQ"
    "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"
    "zznPNGsZPS9w3Rv/ALV9nZ3HwTW6uFX7Ra6jC0DHrlgysB9VJOPYelbXwqv5tK/ZS0vVLbHn2ekX"
    "NxHkZG5DIw/UV8v/ABz+ODfFK5tNJ0izmsfD1jIZkWcjzbiXBAdgCQoAJAAJ6kk84Hq3g34zfDXS"
    "v2a4vCF/4k8nW10i5tTbfY7hv3jiTau4Rledw5zjmpcWopDurnNfslazql98V/EaXuoXFz9r0xrq"
    "cyyFjJKJowHOepw7c+9Z/wC1X4k1lfjHY6dBqE9vb6XZRTW6RSFQkrMzGQY/i+6M/wCyK539nDxx"
    "4X8BfETU9W8Wap/Z1lPpb28cnkSS7pDLEwGI1Y9FbnGOKzf2gPF3h7xt8WJdc8Mah9v09rOGITeU"
    "8XzLnIw6g9/Srt79yb+6fVH7SIFx+zfqU8wDSB7SQHHRjKgJ/U/nXwBX2B8aPjN8NfFvwOv/AA34"
    "f8SfbdVl+zbIPsdxHnZKjN8zxheAD3r4/p0k0tQluFFFFakBRRRQAUUUUAFFFFABRRRQAUUUUAFF"
    "FFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUU"
    "UAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQ"
    "AUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFAB"
    "XoXwb8b6V8PPifZeKNat7u4s4IZo2S0RWkJdCowGZR1PrXntFJq6sM9d+PXxO0H4o+LNL1bw/aah"
    "bQWll9mdb6NEYtvZsjY7DGCO9eRUUUJWVkDdwooopiCiiigAooooAKKKKACiiigAooooAKKKKACi"
    "iigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKK"
    "KACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAoooo"
    "AKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooA67/AIVt41/6"
    "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"
    "mL/4uvoiij+1K3Zfj/mH+suL/lj9z/zPnf8A4Vt41/6Av/kzF/8AF0f8K28a/wDQF/8AJmL/AOLr"
    "6Ioo/tSt2X4/5h/rLi/5Y/c/8z53/wCFbeNf+gL/AOTMX/xdH/CtvGv/AEBf/JmL/wCLr6Ioo/tS"
    "t2X4/wCYf6y4v+WP3P8AzPnf/hW3jX/oC/8AkzF/8XR/wrbxr/0Bf/JmL/4uvoiij+1K3Zfj/mH+"
    "suL/AJY/c/8AM+d/+FbeNf8AoC/+TMX/AMXR/wAK28a/9AX/AMmYv/i6+iKKP7Urdl+P+Yf6y4v+"
    "WP3P/M+d/wDhW3jX/oC/+TMX/wAXR/wrbxr/ANAX/wAmYv8A4uvoiij+1K3Zfj/mH+suL/lj9z/z"
    "Pnf/AIVt41/6Av8A5Mxf/F0f8K28a/8AQF/8mYv/AIuvoiij+1K3Zfj/AJh/rLi/5Y/c/wDM+d/+"
    "FbeNf+gL/wCTMX/xdH/CtvGv/QF/8mYv/i6+iKKP7Urdl+P+Yf6y4v8Alj9z/wAz53/4Vt41/wCg"
    "L/5Mxf8AxdH/AArbxr/0Bf8AyZi/+Lr6Ioo/tSt2X4/5h/rLi/5Y/c/8z53/AOFbeNf+gL/5Mxf/"
    "ABdH/CtvGv8A0Bf/ACZi/wDi6+iKKP7Urdl+P+Yf6y4v+WP3P/MKKKK8o+XCiiigAooooAKKKKAC"
    "iiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKK"
    "KKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooo"
    "oAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiig"
    "AooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKAC"
    "iiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooA//"
    "2Q=="
)


@app.route("/robots.txt")
def robots_txt():
    """Robots pravila + pokazivac na sitemap."""
    body = ("User-agent: *\nAllow: /\n"
            f"Sitemap: {SITE_URL}/sitemap.xml\n")
    return body, 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.route("/sitemap.xml")
def sitemap_xml():
    """XML mapa: naslovnica + pomocne stranice + poslednjih 1000 objavljenih vesti."""
    db = get_db()
    rows = db.execute(
        "SELECT id FROM articles WHERE status = 'published' ORDER BY id DESC LIMIT 1000"
    ).fetchall()
    urls = "".join(
        f"<url><loc>{SITE_URL}/vest/{r['id']}</loc><changefreq>hourly</changefreq><priority>0.6</priority></url>"
        for r in rows)
    xml = ('<?xml version="1.0" encoding="UTF-8"?>'
           '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">'
           f'<url><loc>{SITE_URL}/</loc><changefreq>hourly</changefreq><priority>1.0</priority></url>'
           f'<url><loc>{SITE_URL}/najcitanije</loc><changefreq>daily</changefreq><priority>0.8</priority></url>'
           f'<url><loc>{SITE_URL}/arhiva</loc><changefreq>daily</changefreq><priority>0.7</priority></url>'
           f'{urls}</urlset>')
    return xml, 200, {"Content-Type": "application/xml; charset=utf-8"}


@app.route("/static/og-cover.jpg")
def og_cover():
    """OG/Twitter korica 1200x630 (ugradjena u kod; kesira se 24h)."""
    payload = base64.b64decode(_OG_COVER_JPG_B64)
    return payload, 200, {"Content-Type": "image/jpeg",
                          "Cache-Control": "public, max-age=86400"}


@app.route(REFRESH_PATH)
def rucno_osvezi_vesti_iz_rama():
    """Cron endpoint with alternating work:

    * if untranslated articles exist, translate only one;
    * otherwise fetch the RSS feeds and return immediately after fetching.

    This keeps the expensive translation phase out of the same HTTP request as
    the RSS phase. The endpoint still needs authentication in production; the
    current first change focuses on the cycle strategy and duplicate protection.
    """
    if not REFRESH_TOKEN:
        print("[CRON][ERROR] REFRESH_TOKEN nije podešen.")
        return "Cron ruta nije konfigurisana.", 503
    if not valid_refresh_token():
        return "Forbidden", 403

    if not _cycle_lock.acquire(blocking=False):
        return (
            "<h3>Ciklus je već u toku</h3>"
            "<p>Sačekaj sledeći cron poziv.</p>"
        ), 202

    try:
        now_gate = time.time()
        with _db_lock:
            pending = _db.execute(
                """SELECT 1 FROM articles
                   WHERE status='pending'
                     AND is_archived = 0
                     AND translated_title = ''
                     AND translated_summary = ''
                     AND (next_retry_at IS NULL OR next_retry_at <= ?)
                   LIMIT 1""",
                (now_gate,),
            ).fetchone()

        if pending:
            print("[CRON] Pronađena sirova vest. Pokrećem prevod samo jedne vesti...")
            translated, failed = process_translations(limit=1)
            if translated:
                return (
                    "<h3>Uspeh!</h3>"
                    "<p>Jedna vest je uspešno obrađena.</p>"
                )
            if failed:
                # The row is durably retained with retry metadata. Return a
                # normal cron response so the scheduler does not immediately
                # replay the whole HTTP request on top of the next cycle.
                return (
                    "<h3>Prevod nije uspeo</h3>"
                    "<p>Greška je zabeležena; vest ostaje na čekanju za automatski retry.</p>"
                )
            return (
                "<h3>Nema obrađene vesti</h3>"
                "<p>Proveri Render log.</p>"
            ), 202

        print("[CRON] Nema sirovih vesti. Pokrećem skidanje RSS feedova...")
        new, skipped = fetch_all_feeds()
        return (
            "<h3>RSS osvežen</h3>"
            f"<p>Povučenih novih: {new}, preskočeno: {skipped}.</p>"
            "<p>Prevod će se pokrenuti sledećim cron pozivom.</p>"
        )
    except Exception as exc:
        print(f"[CRON][ERROR] Greška tokom pametnog ciklusa: {exc}")
        # Do not expose raw exception text in a public HTML response.
        return (
            "<h3>Greška tokom osvežavanja</h3>"
            "<p>Pogledaj Render log za detalje.</p>"
        ), 500
    finally:
        _cycle_lock.release()


@app.route(ADMIN_LOGIN_PATH, methods=["GET", "POST"])
def admin_login():
    if not _admin_auth_configured():
        return (
            "Admin login nije konfigurisan. Dodaj ADMIN_PASSWORD ili "
            "ADMIN_PASSWORD_HASH u Render Environment Variables.",
            503,
        )

    error = ""
    if request.method == "POST":
        if not valid_csrf_token():
            return "Nevažeći CSRF token.", 400
        password = request.form.get("password", "")
        if _verify_admin_password(password):
            session.clear()
            session["admin_authenticated"] = True
            session["csrf_token"] = secrets.token_urlsafe(32)
            return redirect(url_for("admin"))
        error = "Pogrešna lozinka."

    return render_template_string(
        ADMIN_LOGIN_TEMPLATE,
        css=BASE_CSS,
        error=error,
    )


@app.post(ADMIN_LOGOUT_PATH)
@admin_required
def admin_logout():
    if not valid_csrf_token():
        return "Nevažeći CSRF token.", 400
    session.clear()
    return redirect(url_for("admin_login"))


@app.route(ADMIN_PATH)
@admin_required
def admin():
    db = get_db()
    with _db_lock:
        pending_total = int(db.execute(
            "SELECT COUNT(*) AS c FROM articles WHERE status='pending'"
        ).fetchone()["c"] or 0)
        published_total = int(db.execute(
            "SELECT COUNT(*) AS c FROM articles WHERE status='published'"
        ).fetchone()["c"] or 0)

        pending_pages_total = max(1, (pending_total + ADMIN_PAGE_SIZE - 1) // ADMIN_PAGE_SIZE)
        published_pages_total = max(1, (published_total + ADMIN_PAGE_SIZE - 1) // ADMIN_PAGE_SIZE)
        pending_page = max(1, request.args.get("pending_page", 1, type=int) or 1)
        published_page = max(1, request.args.get("published_page", 1, type=int) or 1)
        pending_page = min(pending_page, pending_pages_total)
        published_page = min(published_page, published_pages_total)

        pending = db.execute(
            """SELECT id, source, original_title, translated_title, priority,
                      last_error, attempt_count
               FROM articles
               WHERE status='pending'
               ORDER BY priority DESC, published_date DESC, id DESC
               LIMIT ? OFFSET ?""",
            (ADMIN_PAGE_SIZE, (pending_page - 1) * ADMIN_PAGE_SIZE),
        ).fetchall()
        published = db.execute(
            """SELECT id, source, translated_title, priority, category, views,
                      is_archived
               FROM articles WHERE status='published'
               ORDER BY published_date DESC, id DESC
               LIMIT ? OFFSET ?""",
            (ADMIN_PAGE_SIZE, (published_page - 1) * ADMIN_PAGE_SIZE),
        ).fetchall()
        selected = None
        article_id = request.args.get("article_id", type=int)
        if article_id:
            selected = db.execute("SELECT * FROM articles WHERE id = ?", (article_id,)).fetchone()

    def page_window(current: int, total: int):
        return range(max(1, current - 2), min(total, current + 2) + 1)

    return render_template_string(
        ADMIN_TEMPLATE, pending=pending, published=published,
        pending_total=pending_total, published_total=published_total,
        pending_page=pending_page, pending_total_pages=pending_pages_total,
        pending_pages=page_window(pending_page, pending_pages_total),
        published_page=published_page, published_total_pages=published_pages_total,
        published_pages=page_window(published_page, published_pages_total),
        selected=selected, css=BASE_CSS,
    )


@app.post("/admin/publish/<int:article_id>")
@admin_required
def publish_article(article_id: int):
    if not valid_csrf_token():
        return "Nevažeći CSRF token.", 400
    title = (request.form.get("translated_title") or "").strip()
    summary = (request.form.get("translated_summary") or "").strip()
    position = (request.form.get("position") or "standard").strip()
    if position not in ("hero", "trending", "standard"):
        position = "standard"
    if not title or not summary:
        flash("Naslov i sa&#382;etak ne smeju biti prazni.")
        return redirect(url_for("admin", article_id=article_id))
    db = get_db()
    with _db_lock:
        # Only ONE hero may exist: demote the current hero when a new one is set.
        if position == "hero":
            db.execute(
                "UPDATE articles SET position='standard' "
                "WHERE position='hero' AND id != ?", (article_id,))
        content_type = "full" if len(summary) >= 280 else "brief"
        db.execute(
            """UPDATE articles
               SET translated_title=?, translated_summary=?,
                   content_type=?, status='published', position=?,
                   last_error='', next_retry_at=NULL
               WHERE id=?""",
            (title, summary, content_type, position, article_id))
        db.commit()
    flash(f"Vest #{article_id} je sa&#269;uvana, objavljena i pozicionirana ({position}).")
    return redirect(url_for("admin", article_id=article_id))


@app.post("/admin/delete/<int:article_id>")
@admin_required
def delete_article(article_id: int):
    if not valid_csrf_token():
        return "Nevažeći CSRF token.", 400
    db = get_db()
    with _db_lock:
        db.execute("DELETE FROM articles WHERE id = ?", (article_id,))
        db.commit()
    flash(f"Vest #{article_id} je obrisana zauvek.")
    return redirect(url_for("admin"))


# =========================================================================== #
#  BOOTSTRAP
# =========================================================================== #

init_db()
_backfill_categories()
print(f"[DB] connected using {DB_DIALECT}")
start_background_fetcher()

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False, threaded=True)
