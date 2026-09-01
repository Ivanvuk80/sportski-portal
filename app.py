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
    GOOGLE_API_KEY/GOOGLE_CX optional Google image search (real photos).
    MAX_TRANSLATIONS_PER_RUN default 1 per cycle
    FEED_TIMEOUT_SECONDS      timeout for each RSS request (default 8)
    MAX_FEEDS_PER_FETCH       RSS feeds per cron call (default 2)
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

TRANSLATION_MODE = os.environ.get("TRANSLATION_MODE", "ai")    # "ai" | "free"
TARGET_LANGUAGE = "sr"
# Google AI Studio (Gemini) free tier. No external SDK needed - plain HTTPS call.
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash")
GEMINI_API_URL = (
    "https://generativelanguage.googleapis.com/v1beta/models/"
    "{model}:generateContent?key={key}"
)
# Temporary Render-safe default: one translation per refresh cycle.
# Increase only after the worker/queue architecture is in place.
MAX_TRANSLATIONS_PER_RUN = int(os.environ.get("MAX_TRANSLATIONS_PER_RUN", 1))
# AUTOMATIC publishing: every successfully translated article goes live on its
# own as a 'standard' card. Placement still follows the priority criteria
# (Zvezda p=2 -> hero, etc.) and the admin panel ALWAYS stays available so any
# live article can be edited, repositioned (hero/trending) or deleted by hand.
# Set AUTOPILOT_PUBLISH=0 to fall back to full manual approval (Na čekanju queue).
AUTOPILOT_PUBLISH = os.environ.get("AUTOPILOT_PUBLISH", "1") != "0"
FETCH_INTERVAL_SECONDS = int(os.environ.get("FETCH_INTERVAL_SECONDS", 600))
RUN_FETCHER = os.environ.get("RUN_FETCHER", "1") != "0"
REFRESH_TOKEN = os.environ.get("REFRESH_TOKEN", "")
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "")
ADMIN_PASSWORD_HASH = os.environ.get("ADMIN_PASSWORD_HASH", "")
FEED_TIMEOUT_SECONDS = int(os.environ.get("FEED_TIMEOUT_SECONDS", 8))
# Conservative default for a synchronous HTTP cron request: two feeds at a time.
MAX_FEEDS_PER_FETCH = int(os.environ.get("MAX_FEEDS_PER_FETCH", 2))

# Full browser User-Agent so foreign CDNs/servers do not block our requests.
BROWSER_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"
)

# Feeds with "lang": "sr" are already in Serbian -> shown directly, never sent
# through the translator (avoids garbling club names). Every URL below was
# live-tested to actually return articles (homepage URLs return 0 in feedparser).
SPORTS_FEEDS = [
    # DOMAĆI TEREN - profesionalne domaće redakcije (već na srpskom)
    {"name": "Sportski žurnal", "url": "http://www.zurnal.rs/rss", "lang": "sr"},
    {"name": "Telegraf Sport", "url": "https://www.telegraf.rs/rss/sport", "lang": "sr"},
    # EVROPSKI GIGANTI (La Liga, Serija A, Premijer liga, Liga šampiona, transferi)
    {"name": "Marca (Španija)", "url": "https://e00-marca.uecdn.es/rss/futbol.xml", "lang": "es"},
    {"name": "AS (Španija)", "url": "https://as.com/rss/futbol/portada.xml", "lang": "es"},
    {"name": "Gazzetta (Italija)", "url": "https://www.gazzetta.it/rss/calcio.xml", "lang": "it"},
    {"name": "Sky Sports (Engleska)", "url": "https://www.skysports.com/rss/12040", "lang": "en"},
    {"name": "Football Italia", "url": "https://football-italia.net/feed/", "lang": "en"},
    # KOŠARKA (NBA + Evroliga)
    {"name": "Eurohoops", "url": "https://www.eurohoops.net/feed/", "lang": "en"},
    {"name": "Sportando", "url": "https://sportando.basketball/en/feed/", "lang": "en"},
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

# A SINGLE article carrying one of these is skipped (never the whole feed/site).
JUNK_SPORT_WORDS = [
    "triathlon", "triatlon", "cricket", "kriket", "críquet", "críquete",
    "rugby", "ragbi", "rúgbi", "golf", "snooker", "snuker",
]

BREAKING_NEWS_PATTERN = r"\bbreaking(?:\s*[:-]|\\s+news\b)"
FREE_MAX_RETRIES = 3
TRANSLATION_ERROR_MARKERS = (
    "error 500", "server error", "that’s an error", "that's an error",
    "please try again", "too many requests",
)

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "dev-insecure-secret-change-in-production")

class _DatabaseAdapter:
    """Small compatibility layer for existing qmark SQL in SQLite/PostgreSQL."""

    def __init__(self, connection, dialect: str):
        self.connection = connection
        self.dialect = dialect

    def execute(self, sql: str, params=()):
        if self.dialect == "postgres":
            # All application queries use ? placeholders. psycopg uses %s.
            sql = sql.replace("?", "%s")
        return self.connection.execute(sql, params)

    def commit(self):
        return self.connection.commit()

    def rollback(self):
        return self.connection.rollback()


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
    )
else:
    _raw_db = sqlite3.connect(DB_PATH, check_same_thread=False)
    _raw_db.row_factory = sqlite3.Row

_db = _DatabaseAdapter(_raw_db, DB_DIALECT)

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
    "You are a senior sports journalist writing for a major Serbian sports "
    "portal (Mozzart Sport / Sportal / Arena Sport style). Given a short RSS "
    "news brief plus its headline in Spanish, English, Italian or Portuguese: "
    "1) Translate to Serbian and EXPAND it into a full, engaging, professional "
    "article of 2-3 detailed paragraphs (~150 words). 2) Open with a strong "
    "journalistic lead, add context and a closing outlook. 3) Localize football "
    "slang into natural Serbian terminology. 4) Use these club names exactly: "
    "Crvena zvezda, Partizan, River Plejt, Boka Juniors, Njuels Old Bojs, "
    "Radnički Kragujevac. 5) Never invent facts. 6) Output ONLY the article body."
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
    views              INTEGER NOT NULL DEFAULT 0
)
"""


def init_db() -> None:
    with _db_lock:
        if DB_DIALECT == "postgres":
            _db.execute(SCHEMA_SQL_POSTGRES)
            # PostgreSQL migration for databases created by an older version.
            _db.execute(
                "ALTER TABLE articles ADD COLUMN IF NOT EXISTS position "
                "TEXT NOT NULL DEFAULT 'standard'"
            )
        else:
            _db.execute(SCHEMA_SQL_SQLITE)
            # SQLite migration for any pre-existing table without `position`.
            cols = {row[1] for row in _db.execute("PRAGMA table_info(articles)")}
            if "position" not in cols:
                _db.execute(
                    "ALTER TABLE articles ADD COLUMN position "
                    "TEXT NOT NULL DEFAULT 'standard'"
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


def parse_entry(entry: Any, source: str) -> dict:
    return {
        "source": source,
        "title": clean_text(entry.get("title")),
        "link": entry.get("link", ""),
        "published": _format_date(entry),
        "summary": clean_text(entry.get("summary") or entry.get("description")),
    }


def is_junk_sport(title: str, summary: str) -> bool:
    """True if THIS SINGLE article is about a sport we don't cover."""
    text = f"{title or ''} {summary or ''}".lower()
    return any(re.search(rf"\b{re.escape(w)}\b", text) for w in JUNK_SPORT_WORDS)


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
            # gemini-2.5-flash: disable internal "thinking" for fast, cheap output
            "thinkingConfig": {"thinkingBudget": 0},
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
            for entry in parsed.entries:
                art = parse_entry(entry, source)
                if not art["link"]:
                    continue
                if is_junk_sport(art["title"], art["summary"]):
                    skipped += 1                 # drop ONLY this single article
                    continue
                art["priority"] = calculate_priority(art["title"], art["summary"])
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
                            published_date, source_lang, priority, status)
                           VALUES (?,?,?,?,?,?,?, 'pending')""",
                        (art["source"], art["title"], art["summary"], art["link"],
                         art["published"], art["lang"], art["priority"]),
                    )
                    new += 1
                _db.commit()
            print(f"[FETCH] {source}: batch ok ({len(batch)} u obzir)")
        except Exception as exc:
            print(f"[FETCH][ERROR] {source}: {exc}")
    return new, skipped


def process_translations(limit: int = MAX_TRANSLATIONS_PER_RUN) -> tuple[int, int]:
    """Translate/generate up to `limit` pending articles; autopilot-publish hot ones.

    Serbian-source articles are copied through directly (no network call) so club
    names are never mangled.
    """
    with _db_lock:
        rows = _db.execute(
            """SELECT id, source, original_title, original_summary, priority, source_lang
               FROM articles
               WHERE translated_title = '' AND translated_summary = ''
               ORDER BY published_date DESC, id DESC
               LIMIT ?""",
            (limit,),
        ).fetchall()

    if not rows:
        return 0, 0

    translated = failed = 0
    for row in rows:
        article_id = row["id"]
        try:
            # In AI mode, foreign feeds (Marca/Sky/Ole) often have an empty or
            # very short summary (<30 chars). Feed Gemini the TITLE so it can
            # write a full 2-3 paragraph article from the headline alone.
            ai_body_material = row["original_summary"] or ""
            if TRANSLATION_MODE == "ai" and len(ai_body_material.strip()) < 30:
                ai_body_material = row["original_title"]

            if row["source_lang"] == "sr":
                # Ako je TRANSLATION_MODE postavljen na "ai", šaljemo i domaću
                # vest na proširivanje u 2-3 pasusa (naslov ostaje izvoran).
                if TRANSLATION_MODE == "ai" and os.environ.get("GEMINI_API_KEY"):
                    tr_title = localize_post(row["original_title"])
                    # Ugrađeni AI novinar od naslova/jedne rečenice pravi ceo članak.
                    tr_summary = translate_text(
                        ai_body_material, is_headline=False,
                        source_headline=row["original_title"])
                else:
                    # Već na srpskom -> prikaži direktno, samo lokalno srediti imena.
                    tr_title = localize_post(row["original_title"])
                    tr_summary = (
                        localize_post(row["original_summary"])
                        if row["original_summary"] else ""
                    )
            else:
                tr_title = translate_text(row["original_title"], is_headline=True,
                                          source_headline=row["original_title"])
                tr_summary = (
                    translate_text(ai_body_material, is_headline=False,
                                   source_headline=row["original_title"])
                    if ai_body_material else ""
                )
            # AUTOMATIC publishing: every translated article goes live. A
            # Zvezda (priority=2) article auto-claims the Hero slot and demotes
            # the previous hero; everything else lands as a standard card.
            # With AUTOPILOT_PUBLISH=0 everything stays 'pending' for approval.
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
                       SET translated_title = ?, translated_summary = ?,
                           status = ?, position = ?
                       WHERE id = ?""",
                    (tr_title, tr_summary, status, position, article_id),
                )
                _db.commit()
            translated += 1
            tag = "PUBLISHED" if status == "published" else "pending"
            print(f"[TRANSLATE] #{article_id} [{row['source']}] {tag}: {tr_title[:60]}")
            if row["source_lang"] != "sr" and TRANSLATION_MODE == "free":
                time.sleep(0.5)
        except Exception as exc:
            failed += 1
            print(f"[TRANSLATE][ERROR] #{article_id}: {exc}")
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

_BASKETBALL_KEYWORDS = [
    "nba", "jokic", "jokić", "basketball", "košarka", "kosarka",
    "košarkašk", "kosarkask", "košarkaš", "kosarkas", "basket",
    "evroliga", "evrolige", "euroleague", "euroleague", "evrokup",
]
_FOOTBALL_KEYWORDS = [
    "football", "soccer", "fudbal", "fudbalsk", "messi", "maradona",
    "boca juniors", "boka juniors", "boka", "river plej t", "river plej",
    "plejt", "xeneize", "river plate", "lanus", "lanús", "velez", "vélez",
    "real madrid", "liverpool", "barselona", "barcelona", "psg", "fichaje",
    "refuerzo", "transfer", "gol", "utakmica", "meč", "premier league",
    "la liga", "serija a", "clausura", "klauzura", "libertadores",
    "sudamericana", "golman", "kapiten", "trener", "derbi", "prelazni rok",
    "fudbalska pijaca", "ofšajd", "napad", "odbrana",
    "radnicki", "radnički", "radničkog", "radničkom", "radnički 1923",
    "radnicki kragujevac", "radnički kragujevac", "crvena zvezda", "zvezda",
    "partizan", "kragujevac", "kragujevcu", "vojvodina", "vojvodine",
    "vojvodini", "vojvodinom", "vosa", "voša", "voše", "cika daca",
    "čika dača", "đavoli", "davoli", "superliga", "novosađani",
    "novosadjani", "novosađana", "radnicki nis", "radnički niš",
    "radnički iz niša", "nišava", "čair", "novi pazar", "novog pazara",
    "novom pazaru", "novim pazarom", "pazarci",
    "neymar", "ronaldinho", "pelé", "pele", "endrick", "estevao", "estêvão",
    "messinho", "flamengo", "palmeiras", "santos",
    "sao paulo", "são paulo", "fluminense",
]
_SOUTH_AMERICA_KEYWORDS = [
    "boka", "boca", "river plej", "plejt", "xeneize", "millonario",
    "boca juniors", "boka juniors", "river plate", "lanús", "lanus",
    "vélez", "velez", "racing", "independiente", "san lorenzo",
    "estudiantes", "bombonera", "clausura", "klauzura", "libertadores",
    "sudamericana", "gaucho", "gaučo", "gaučos", "karioka", "karioke",
    "tango", "samba", "argentina", "argentinski", "brazil", "brazilu",
    "brazilski", "brazilskom",
    "messi", "maradona", "tevez", "riquelme", "gallardo",
    "neymar", "ronaldinho", "pelé", "pele", "endrick", "estevao",
    "estêvão", "messinho", "flamengo", "palmeiras", "santos",
    "sao paulo", "são paulo", "fluminense", "brasileirao", "brasileirão",
    "njujels", "ole", "clarin", "globo",
]

# Offline fallback images (inline SVG) used when Google Image Search is not
# configured (no GOOGLE_API_KEY / GOOGLE_CX) or when the API call fails.
_FALLBACK_EMOJI = {"football": "⚽", "basketball": "🏀", "general": "🏆"}


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


CATEGORY_LABELS = {"football": "Fudbal", "basketball": "Košarka", "general": "Sport"}

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
    text = article_text_blob(article)
    if any(k in text for k in _BASKETBALL_KEYWORDS):
        return "basketball"
    if any(k in text for k in _FOOTBALL_KEYWORDS):
        return "football"
    return "general"


def is_south_america(article) -> bool:
    text = article_text_blob(article)
    return any(re.search(rf"\b{re.escape(k)}", text) for k in _SOUTH_AMERICA_KEYWORDS)


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
.hero h2{font-size:clamp(1.6rem,3.6vw,2.6rem); font-weight:800; line-height:1.15;
  margin-bottom:12px; text-shadow:0 2px 14px rgba(0,0,0,.5);}
.hero p{font-size:clamp(1rem,1.6vw,1.18rem); color:#cbd5e1; margin-bottom:16px;}

.section-head{display:flex; align-items:center; gap:12px; margin:8px 0 20px;}
.section-head h3{font-size:1.25rem; font-weight:800; letter-spacing:.4px;
  border-left:4px solid var(--green); padding-left:12px;}
.section-head .line{flex:1; height:1px; background:var(--border);}
.section-head h3 .emoji{margin-right:8px;}
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
.card-body h4{font-size:1.06rem; font-weight:700; line-height:1.35;}
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
.hero-head h3{font-size:1.25rem; font-weight:800; border-left:4px solid var(--green);
  padding-left:12px;} .hero-head{margin:8px 0 18px;}

.meta{display:flex; gap:16px; flex-wrap:wrap; color:var(--muted); font-size:.84rem;
  align-items:center;}
.views{margin-left:auto; font-weight:600;} .views b{color:var(--green);}
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
"""


# =========================================================================== #
#  TEMPLATES
# =========================================================================== #

PUBLIC_TEMPLATE = """
<!doctype html>
<html lang="sr">
<head>
  <meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Sportske vesti &#8211; Sportski Portal</title>
  <style>{{ css|safe }}</style>
</head>
<body>
  {% macro card(a, eager=false, rank=none) -%}
  <a class="card {% if rank %}trending{% endif %}"
     href="{{ url_for('article_detail', article_id=a['id']) }}">
    <div class="card-media">
      <img src="{{ article_image(a) }}" alt="{{ a.translated_title }}"
           loading="{{ 'eager' if eager else 'lazy' }}" onerror="this.style.opacity='0'">
      <span class="chip">{{ category_label(a) }}</span>
      {% if rank %}<span class="badge-trending">&#128293; Naj&#269;itanije</span>
      {% elif a.priority == 2 %}<span class="badge-star">&#11088; Zvezda</span>
      {% elif a.priority == 1 %}<span class="badge-hot">&#9889;</span>{% endif %}
      {% if rank %}<span class="card-rank">{{ rank }}</span>{% endif %}
    </div>
    <div class="card-body">
      <h4>{{ a.translated_title }}</h4>
      {% set clubs = club_badges(a) %}
      {% if clubs %}
      <div class="club-badges">
        {% for club in clubs %}<span class="club-chip {{ club.css }}">&#9917; {{ club.label }}</span>{% endfor %}
      </div>
      {% endif %}
      <p class="card-excerpt">{{ a.translated_summary }}</p>
      <div class="meta">
        <span>&#128337; {{ a.published_date }}</span>
        <span class="views">&#128065; <b>{{ a.views or 0 }}</b></span>
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
          <a href="{{ url_for('index') }}#fudbal" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#9917;</span> Fudbal</a>
          <a href="{{ url_for('index') }}#kosarka" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127936;</span> Ko&#353;arka</a>
          <a href="{{ url_for('index') }}#juzna-amerika" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#10024;</span> Ju&#382;na Amerika</a>
          <a href="{{ url_for('index') }}" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127968;</span> Po&#269;etna</a>
        </div>
      </nav>
    </div>
  </header>

  <main class="container">
    {% if hero or trending or football or basketball or south_america %}

      {% if hero %}
      <div class="hero-head section-head">
        <h3><span class="emoji">&#9889;</span>UDARNA VEST</h3><span class="line"></span>
      </div>
      <a class="hero" href="{{ url_for('article_detail', article_id=hero['id']) }}">
        <img src="{{ article_image(hero) }}" alt="{{ hero.translated_title }}"
             loading="eager" onerror="this.style.display='none'">
        <div class="hero-overlay"></div>
        <div class="hero-content">
          <div class="hero-tags">
            {% if hero.priority == 2 %}<span class="badge-star">&#11088; Crvena zvezda &#8211; udarna vest</span>
            {% else %}<span class="badge-hot">&#9889; Udarna vest</span>{% endif %}
            <span class="chip">{{ category_label(hero) }}</span>
            {% for club in club_badges(hero) %}<span class="club-chip {{ club.css }}">&#9917; {{ club.label }}</span>{% endfor %}
            <span class="chip">&#128065; {{ hero.views or 0 }}</span>
          </div>
          <h2>{{ hero.translated_title }}</h2>
          <p>{{ hero.translated_summary }}</p>
          <div class="meta">
            <span>&#128337; {{ hero.published_date }}</span>
            <span class="views">&#128065; <b>{{ hero.views or 0 }}</b></span>
          </div>
        </div>
      </a>
      {% endif %}

      {% if trending %}
      <section class="grid-section">
        <div class="section-head"><h3><span class="emoji">&#128293;</span>NAJ&#268;ITANIJE</h3><span class="line"></span></div>
        <div class="grid">{% for a in trending %}{{ card(a, eager=(loop.index==1), rank=loop.index) }}{% endfor %}</div>
      </section>
      {% endif %}

      {% if football %}
      <section class="grid-section" id="fudbal">
        <div class="section-head"><h3><span class="emoji">&#9917;</span>DOMA&#262;I TEREN &amp; EVROPSKI GIGANTI</h3><span class="line"></span></div>
        <div class="grid">{% for a in football %}{{ card(a) }}{% endfor %}</div>
      </section>
      {% endif %}

      {% if basketball %}
      <section class="grid-section" id="kosarka">
        <div class="section-head"><h3><span class="emoji">&#127936;</span>KO&#352;ARKA</h3><span class="line"></span></div>
        <div class="grid">{% for a in basketball %}{{ card(a) }}{% endfor %}</div>
      </section>
      {% endif %}

      {% if south_america %}
      <section class="grid-section" id="juzna-amerika">
        <div class="section-head"><h3><span class="emoji">&#10024;</span>JU&#381;NOAMERI&#268;KA MAGIJA <span class="sa-sub">(Gau&#269;osi i Karijoke)</span></h3><span class="line"></span></div>
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
          <a href="{{ url_for('index') }}#fudbal" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#9917;</span> Fudbal</a>
          <a href="{{ url_for('index') }}#kosarka" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127936;</span> Ko&#353;arka</a>
          <a href="{{ url_for('index') }}#juzna-amerika" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#10024;</span> Ju&#382;na Amerika</a>
          <a href="{{ url_for('index') }}" onclick="document.getElementById('navDropdown').classList.remove('show');document.getElementById('hamburgerBtn').classList.remove('open');"><span class="ico">&#127968;</span> Po&#269;etna</a>
        </div>
      </nav>
    </div>
  </header>

  <main class="article-page">
    <a class="back-link" href="{{ url_for('index') }}">&larr; Nazad na po&#269;etnu</a>

    <article class="article-card">
      <img class="article-cover" src="{{ article_image(a) }}" alt="{{ a.translated_title }}"
           onerror="this.style.display='none'">
      <div class="article-inner">
        <div class="article-tags">
          <span class="chip">{{ category_label(a) }}</span>
          {% if a.priority == 2 %}<span class="badge-star">&#11088; Crvena zvezda</span>
          {% elif a.priority == 1 %}<span class="badge-hot">&#9889; Udarna vest</span>{% endif %}
          {% for club in club_badges(a) %}<span class="club-chip {{ club.css }}">&#9917; {{ club.label }}</span>{% endfor %}
        </div>

        <h1 class="article-title">{{ a.translated_title }}</h1>

        <div class="meta article-meta">
          <span>&#128337; {{ a.published_date }}</span>
          <span class="views">&#128065; <b>{{ a.views or 0 }}</b> pregleda</span>
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
          <div class="group-head pending">&#9203; Na &#269;ekanju ({{ pending|length }})</div>
          {% if pending %}
            {% for a in pending %}
            <a class="pending-item {% if selected and selected['id'] == a['id'] %}active{% endif %}"
               href="{{ url_for('admin', article_id=a['id']) }}">
              <div class="pi-title">{{ a.translated_title }}{% if a.priority == 2 %} <span class="badge-star">&#11088;</span>{% elif a.priority == 1 %} <span class="badge-hot">&#9889;</span>{% endif %}</div>
              <div class="pi-meta meta">{{ a.source }}</div>
            </a>
            {% endfor %}
          {% else %}
            <p class="empty-small">Nema vesti na &#269;ekanju.</p>
          {% endif %}
        </div>

        <div class="admin-group">
          <div class="group-head published">&#128994; Objavljene vesti &#8211; u&#382;ivo ({{ published|length }})</div>
          {% if published %}
            {% for a in published %}
            <a class="pending-item {% if selected and selected['id'] == a['id'] %}active{% endif %}"
               href="{{ url_for('admin', article_id=a['id']) }}">
              <div class="pi-title">{{ a.translated_title }}</div>
              <div class="pi-meta meta">
                <span>{{ a.source }}</span>
                <span class="views">&#128065; <b>{{ a.views or 0 }}</b></span>
              </div>
            </a>
            {% endfor %}
          {% else %}
            <p class="empty-small">Jo&#353; uvek nema objavljenih vesti.</p>
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
              <span class="pos-text"><b>Naj&#269;itanije / Trending</b><small>Traka sa tri istaknute vesti</small></span>
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

@app.route("/")
def index():
    db = get_db()
    with _db_lock:
        articles = db.execute(
            """SELECT id, source, original_title, original_summary, link,
                      translated_title, translated_summary, published_date,
                      priority, position, views
               FROM articles WHERE status='published'
               ORDER BY published_date DESC, id DESC"""
        ).fetchall()

        # --- Hero: ONLY the article the editor set to position='hero' ---
        hero = next((a for a in articles if a["position"] == "hero"), None)
        # Fallback (nothing placed yet): freshest Zvezda (p=2), then high (p=1).
        if hero is None:
            hero = next((a for a in articles if a["priority"] == 2), None) or \
                next((a for a in articles if a["priority"] == 1), None)
        hero_id = hero["id"] if hero else None

        # --- Trending: editor-picked position='trending' (max 3) ---
        picked_trending = [a for a in articles
                           if a["position"] == "trending" and a["id"] != hero_id][:3]
        used = {a["id"] for a in picked_trending}
        if hero_id is not None:
            used.add(hero_id)
        remaining = [a for a in articles if a["id"] not in used]
        # Fill up to 3 with most-viewed articles if fewer than 3 were picked.
        auto_trending = sorted(
            remaining,
            key=lambda a: (a["views"] or 0, a["published_date"] or "", a["id"]),
            reverse=True,
        )[:max(0, 3 - len(picked_trending))]
        trending = picked_trending + auto_trending

        featured_ids = ({hero_id} if hero_id is not None else set()) | {a["id"] for a in trending}
        rest = [a for a in articles if a["id"] not in featured_ids]
        basketball = [a for a in rest if article_category(a) == "basketball"]
        south_america = [a for a in rest if is_south_america(a)]
        sa_ids = {a["id"] for a in south_america}
        football = [a for a in rest
                    if article_category(a) == "football" and a["id"] not in sa_ids]

    return render_template_string(
        PUBLIC_TEMPLATE, hero=hero, trending=trending, football=football,
        basketball=basketball, south_america=south_america, css=BASE_CSS,
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
        with _db_lock:
            pending = _db.execute(
                """SELECT 1 FROM articles
                   WHERE status='pending'
                     AND translated_title = ''
                     AND translated_summary = ''
                   LIMIT 1"""
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
                return (
                    "<h3>Prevod nije uspeo</h3>"
                    "<p>Vest ostaje na čekanju i biće ponovo obrađena.</p>"
                ), 502
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
        pending = db.execute(
            """SELECT id, source, translated_title, priority
               FROM articles
               WHERE status='pending' AND translated_title != ''
               ORDER BY priority DESC, published_date DESC, id DESC"""
        ).fetchall()
        published = db.execute(
            """SELECT id, source, translated_title, priority, views
               FROM articles WHERE status='published'
               ORDER BY published_date DESC, id DESC"""
        ).fetchall()
        selected = None
        article_id = request.args.get("article_id", type=int)
        if article_id:
            selected = db.execute("SELECT * FROM articles WHERE id = ?", (article_id,)).fetchone()
    return render_template_string(
        ADMIN_TEMPLATE, pending=pending, published=published,
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
        db.execute(
            """UPDATE articles
               SET translated_title=?, translated_summary=?,
                   status='published', position=?
               WHERE id=?""",
            (title, summary, position, article_id))
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
print(f"[DB] connected using {DB_DIALECT}")
start_background_fetcher()

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False, threaded=True)
