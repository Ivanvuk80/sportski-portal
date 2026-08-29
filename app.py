"""
Sports News Aggregator - Single-file, diskless, self-updating build.

Everything runs from THIS file:
  * Flask web portal + secret admin dashboard (app.py)
  * RSS fetcher / priority engine / translation engine (rss_fetcher.py)

Key deployment choices:
  * DATABASE_PATH = ":memory:"  -> the SQLite database lives in RAM and never
    touches the disk. Because an in-memory SQLite DB is scoped to a single
    connection, we open ONE shared connection (check_same_thread=False) and
    guard every access with a global re-entrant lock so the web request
    threads and the background fetcher thread share the same data safely.
  * The fetcher runs on a BACKGROUND THREAD on an autopilot loop, so the app is
    completely self-contained: start it and the site fills with live articles.

  Trade-off: RAM is volatile, so the in-memory DB is seeded fresh on each
  process start (and each serverless "cold start"). Perfect for stateless /
  ephemeral deployments; use a file/Postgres when you need persistence.

Env vars (all optional):
    SECRET_KEY               Flask secret (set in production!)
    PORT                     HTTP port (default 5000)
    TRANSLATION_MODE         "free" (default) or "ai"
    MAX_TRANSLATIONS_PER_RUN default 8 per cycle
    FETCH_INTERVAL_SECONDS   autopilot loop interval (default 600)
    RUN_FETCHER              "0" to disable the background fetcher

Run:
    pip install -r requirements.txt
    python app.py
"""

import html
import os
import random
import re
import socket
import sqlite3
import threading
import time
from typing import Any

import feedparser
from flask import Flask, g, flash, redirect, render_template_string, request, url_for

try:  # free translation mode (deep-translator) is required for the autopilot
    from deep_translator import GoogleTranslator
except ImportError:  # pragma: no cover
    GoogleTranslator = None

socket.setdefaulttimeout(15)

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

DB_PATH = ":memory:"                       # RAM only - never touches the disk
ADMIN_PATH = "/admin-tajna-kontrola-777"   # secret admin URL

TRANSLATION_MODE = os.environ.get("TRANSLATION_MODE", "free")   # "free" | "ai"
TARGET_LANGUAGE = "sr"
MAX_TRANSLATIONS_PER_RUN = int(os.environ.get("MAX_TRANSLATIONS_PER_RUN", 8))
AUTOPILOT_PUBLISH_HIGH_PRIORITY = True
FETCH_INTERVAL_SECONDS = int(os.environ.get("FETCH_INTERVAL_SECONDS", 600))
RUN_FETCHER = os.environ.get("RUN_FETCHER", "1") != "0"

SPORTS_FEEDS = [
    {"name": "BBC Sport", "url": "https://feeds.bbci.co.uk/sport/rss.xml"},
    {"name": "Ole (Argentina)", "url": "https://www.ole.com.ar/rss/"},
    {"name": "Clarin Deportes (Argentina)", "url": "https://www.clarin.com/rss/deportes/"},
]

HIGH_PRIORITY_KEYWORDS = [
    "Messi", "Maradona", "Boca Juniors", "Boca", "River Plate", "River",
    "Transfer", "Fichaje", "Refuerzo",
    "Radnicki", "Radnički", "Vojvodina", "Voša", "Neymar", "Ronaldinho",
]

JUNK_SPORT_WORDS = [
    "triathlon", "cricket", "rugby", "golf", "snooker", "triatlon", "kriket",
]

BREAKING_NEWS_PATTERN = r"\bbreaking(?:\s*[:-]|\s+news\b)"
FREE_MAX_RETRIES = 3
TRANSLATION_ERROR_MARKERS = (
    "error 500", "server error", "that’s an error", "that's an error",
    "please try again", "too many requests",
)

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "dev-insecure-secret-change-in-production")

# One shared in-memory connection + a lock for multi-thread (Flask + fetcher) access.
_db_lock = threading.RLock()
_db = sqlite3.connect(DB_PATH, check_same_thread=False)
_db.row_factory = sqlite3.Row


# --------------------------------------------------------------------------- #
# AI prompts (used only when TRANSLATION_MODE == "ai", needs OPENAI_API_KEY)
# --------------------------------------------------------------------------- #

AI_HEADLINE_SYSTEM_PROMPT = (
    "You are a senior Serbian sports journalist and SEO copywriter. "
    "Translate the Spanish/English sports headline to Serbian, convert foreign "
    "football slang into localized Serbian sports terminology, and rewrite the "
    "headline to be unique and catchy for SEO. Preserve all key facts. "
    "Output ONLY the Serbian headline."
)

AI_BODY_SYSTEM_PROMPT = (
    "You are a senior sports journalist writing for a major Serbian sports "
    "portal (Mozzart Sport / Sportal / Arena Sport style). Given a short RSS "
    "news brief plus its headline in Spanish or English: 1) Translate to Serbian "
    "and EXPAND it into a full, engaging, professional article of 2-3 detailed "
    "paragraphs (~150 words). 2) Open with a strong journalistic lead, then add "
    "context (key moment, stakes, standings) and a closing outlook. 3) Localize "
    "football slang into natural Serbian terminology. 4) Never invent facts not "
    "in the brief. 5) Output ONLY the article body, no headline or preamble."
)


# =========================================================================== #
#  IN-MEMORY DATABASE
# =========================================================================== #

SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS articles (
    id                 INTEGER PRIMARY KEY AUTOINCREMENT,
    source             TEXT    NOT NULL,
    original_title     TEXT    NOT NULL,
    original_summary   TEXT    DEFAULT '',
    link               TEXT    NOT NULL UNIQUE,
    published_date     TEXT,
    translated_title   TEXT    NOT NULL DEFAULT '',
    translated_summary TEXT    NOT NULL DEFAULT '',
    priority           INTEGER NOT NULL DEFAULT 0,
    status             TEXT    NOT NULL DEFAULT 'pending'
                                        CHECK (status IN ('pending','published')),
    views              INTEGER NOT NULL DEFAULT 0
)
"""


def init_db() -> None:
    with _db_lock:
        _db.execute(SCHEMA_SQL)
        _db.commit()


def get_db() -> sqlite3.Connection:
    """
    All threads (Flask workers + background fetcher) share the SAME in-memory
    connection; the RLock serializes access. There is no per-request close().
    """
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


def calculate_priority(title: str, summary: str) -> int:
    text = f"{title or ''} {summary or ''}".lower()
    if any(re.search(rf"\b{re.escape(w)}\b", text) for w in JUNK_SPORT_WORDS):
        return 0
    for kw in HIGH_PRIORITY_KEYWORDS:
        if re.search(rf"\b{re.escape(kw.lower())}s?\b", text):
            return 1
    if re.search(BREAKING_NEWS_PATTERN, text):
        return 1
    return 0


# ---------- Translation engine ---------- #

def translate_text(text: str, is_headline: bool = False,
                   source_headline: str | None = None) -> str:
    if not text or not text.strip():
        return ""
    if TRANSLATION_MODE == "ai":
        return _translate_ai(text, is_headline, source_headline)
    return _translate_free(text)


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
    try:
        from openai import OpenAI
    except ImportError as exc:
        raise RuntimeError("AI mode needs the 'openai' package: pip install openai") from exc

    import os as _os
    key = _os.environ.get("OPENAI_API_KEY")
    if not key:
        raise RuntimeError("AI mode requires the OPENAI_API_KEY environment variable")

    client = OpenAI(api_key=key)
    prompt = AI_HEADLINE_SYSTEM_PROMPT if is_headline else AI_BODY_SYSTEM_PROMPT
    if is_headline:
        user = f"Headline:\n{text}"
        temp, tokens = 0.7, 200
    else:
        user = f"Headline:\n{source_headline or ''}\n\nNews brief:\n{text}"
        temp, tokens = 0.7, 900
    resp = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[{"role": "system", "content": prompt},
                  {"role": "user", "content": f"Target language: {TARGET_LANGUAGE}\n\n{user}"}],
        temperature=temp, max_tokens=tokens,
    )
    return resp.choices[0].message.content.strip()


# ---------- Fetch / store cycle ---------- #

def fetch_all_feeds() -> tuple[int, int]:
    """Pull every feed, dedupe by link, store new articles. Returns (new, skipped)."""
    new = skipped = 0
    for feed in SPORTS_FEEDS:
        source, url = feed["name"], feed["url"]
        try:
            parsed = feedparser.parse(url, agent="SportsAggregator/1.0")
            if parsed.bozo and not parsed.entries:
                raise parsed.bozo_exception or RuntimeError("Feed returned no entries")

            batch = []          # build rows WITHOUT holding the lock across the network
            for entry in parsed.entries:
                art = parse_entry(entry, source)
                if not art["link"]:
                    continue
                batch.append(art)

            with _db_lock:
                for art in batch:
                    exists = _db.execute(
                        "SELECT 1 FROM articles WHERE link = ? LIMIT 1", (art["link"],)
                    ).fetchone()
                    if exists:
                        skipped += 1
                        continue
                    art["priority"] = calculate_priority(art["title"], art["summary"])
                    _db.execute(
                        """INSERT INTO articles
                           (source, original_title, original_summary, link,
                            published_date, priority, status)
                           VALUES (?,?,?,?,?,?, 'pending')""",
                        (art["source"], art["title"], art["summary"], art["link"],
                         art["published"], art["priority"]),
                    )
                    new += 1
                _db.commit()
            print(f"[FETCH] {source}: batch ok")
        except Exception as exc:
            print(f"[FETCH][ERROR] {source}: {exc}")
    return new, skipped


def process_translations(limit: int = MAX_TRANSLATIONS_PER_RUN) -> tuple[int, int]:
    """Translate/generate up to `limit` pending articles; autopilot-publish hot ones."""
    with _db_lock:
        rows = _db.execute(
            """SELECT id, source, original_title, original_summary, priority
               FROM articles
               WHERE translated_title = '' AND translated_summary = ''
               ORDER BY priority DESC, published_date DESC
               LIMIT ?""",
            (limit,),
        ).fetchall()

    if not rows:
        return 0, 0

    translated = failed = 0
    for row in rows:
        article_id = row["id"]
        try:
            tr_title = translate_text(row["original_title"], is_headline=True,
                                      source_headline=row["original_title"])
            tr_summary = (
                translate_text(row["original_summary"], is_headline=False,
                               source_headline=row["original_title"])
                if row["original_summary"] else ""
            )
            status = (
                "published"
                if (AUTOPILOT_PUBLISH_HIGH_PRIORITY and row["priority"] == 1)
                else "pending"
            )
            with _db_lock:
                _db.execute(
                    """UPDATE articles
                       SET translated_title = ?, translated_summary = ?, status = ?
                       WHERE id = ?""",
                    (tr_title, tr_summary, status, article_id),
                )
                _db.commit()
            translated += 1
            tag = "PUBLISHED" if status == "published" else "pending"
            print(f"[TRANSLATE] #{article_id} [{row['source']}] {tag}: "
                  f"{tr_title[:60]}")
            if TRANSLATION_MODE == "free":
                time.sleep(0.5)
        except Exception as exc:
            failed += 1
            print(f"[TRANSLATE][ERROR] #{article_id}: {exc}")
    print(f"[TRANSLATE] cycle done: {translated} ok, {failed} failed")
    return translated, failed


def run_fetcher_cycle() -> None:
    new, skipped = fetch_all_feeds()
    process_translations()
    with _db_lock:
        total = _db.execute("SELECT COUNT(*) c FROM articles").fetchone()["c"]
        live = _db.execute(
            "SELECT COUNT(*) c FROM articles WHERE status='published'").fetchone()["c"]
    print(f"[AUTOPILOT] cycle: {new} new, {skipped} dupes | DB {total} | live {live}")


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
    "košarkašk", "kosarkask", "basket",
]
_FOOTBALL_KEYWORDS = [
    "football", "soccer", "fudbal", "fudbalsk", "messi", "maradona",
    "boca juniors", "boca", "xeneize", "river plate", "river", "lanus",
    "lanús", "velez", "vélez", "real madrid", "liverpool", "barselona",
    "barcelona", "psg", "fichaje", "refuerzo", "transfer", "gol",
    "utakmica", "meč", "premier league", "la liga", "clausura",
    "libertadores", "golman", "kapiten", "trener", "derbi", "prelazni rok",
    "ofšajd", "napad", "odbrana",
    "radnicki", "radnički", "radničkog", "radničkom", "radnički 1923",
    "radnicki kragujevac", "radnički kragujevac",
    "kragujevac", "kragujevcu", "vojvodina", "vojvodine", "vojvodini",
    "vojvodinom", "vosa", "voša", "voše", "cika daca", "čika dača",
    "đavoli", "davoli", "superliga", "novosađani", "novosadjani", "novosađana",
    "radnicki nis", "radnički niš", "radnički iz niša", "nišava", "čair",
    "novi pazar", "novog pazara", "novom pazaru", "novim pazarom", "pazarci",
    "neymar", "ronaldinho", "pelé", "pele", "endrick", "estevao", "estêvão",
    "messinho", "flamengo", "palmeiras", "santos",
    "sao paulo", "são paulo", "fluminense",
]
_SOUTH_AMERICA_KEYWORDS = [
    "boca", "river", "xeneize", "millonario", "nuñeza", "nunjeza",
    "boca juniors", "river plate", "lanús", "lanus", "vélez", "velez",
    "racing", "independiente", "san lorenzo", "estudiantes",
    "bombonera", "clausura", "libertadores", "sudamericana", "gaucho", "gaučo",
    "messi", "maradona", "tevez", "riquelme", "gallardo", "arruabarrena",
    "arrubarena", "ponzio", "belmonte",
    "neymar", "ronaldinho", "pelé", "pele", "endrick", "estevao", "estêvão",
    "messinho", "flamengo", "palmeiras", "santos",
    "sao paulo", "são paulo", "fluminense", "brasileirao", "brasileirão",
    "carioca", "carioka",
]

PLACEHOLDER_IMAGES = {
    "football": [
        "https://images.unsplash.com/photo-1574629810360-7efbbe195018?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1522778119026-d647f0596c20?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1431324155629-1a6deb1dec8d?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1508098682722-e99c43a406b2?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1489944440615-453fc2b6a9a9?auto=format&fit=crop&w=1200&q=70",
    ],
    "basketball": [
        "https://images.unsplash.com/photo-1546519638-68e109498ffc?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1519861531473-9200262188bf?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1574623452334-1e0ac2b3ccb4?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1608248543803-ba4f8c70ae0b?auto=format&fit=crop&w=1200&q=70",
    ],
    "general": [
        "https://images.unsplash.com/photo-1517649763962-0c623066013b?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1461896836934-ffe607ba8211?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1521412644187-c49fa049e84d?auto=format&fit=crop&w=1200&q=70",
        "https://images.unsplash.com/photo-1552674605-db6ffd4facb5?auto=format&fit=crop&w=1200&q=70",
    ],
}
CATEGORY_LABELS = {"football": "Fudbal", "basketball": "Košarka", "general": "Sport"}

LOCAL_CLUBS = [
    {"label": "Radnički KG", "css": "club-kg",
     "match": ["kragujevac", "kragujevcu", "kragujevca", "čika dača",
               "cika daca", "đavoli", "davoli"]},
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


def article_image(article) -> str:
    try:
        seed = article["id"] or 0
    except (KeyError, IndexError, TypeError):
        seed = 0
    return random.Random(f"img-{seed}").choice(PLACEHOLDER_IMAGES[article_category(article)])


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
html{-webkit-text-size-adjust:100%;}
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
.topbar-tag{color:var(--muted); font-size:.78rem; text-transform:uppercase; letter-spacing:2.5px;}
.live-dot{display:inline-flex; align-items:center; gap:6px; color:var(--green);
  font-size:.74rem; font-weight:700; letter-spacing:.5px; text-transform:uppercase;}
.live-dot::before{content:''; width:8px; height:8px; border-radius:50%;
  background:var(--green); box-shadow:0 0 10px var(--green);
  animation:pulse 1.6s infinite;}
@keyframes pulse{0%,100%{opacity:1;} 50%{opacity:.35;}}

.chip{display:inline-block; background:rgba(15,23,42,.72); color:#e2e8f0;
  border:1px solid rgba(148,163,184,.35); border-radius:999px; padding:4px 12px;
  font-size:.72rem; font-weight:700; letter-spacing:.8px; text-transform:uppercase;
  backdrop-filter:blur(4px);}
.badge-hot{display:inline-block; background:var(--green); color:#052e16;
  border-radius:999px; padding:4px 12px; font-size:.72rem; font-weight:800;
  letter-spacing:.8px; text-transform:uppercase; box-shadow:0 0 18px rgba(34,197,94,.5);}

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
.grid-section{margin-bottom:44px;}

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
.footer-text{color:var(--muted); font-size:.82rem; text-align:center; padding:34px 0 26px;}
.foot-note{font-size:.72rem; color:var(--muted);}

.btn{display:inline-block; border:none; border-radius:9px; padding:11px 20px;
  font-size:.92rem; font-weight:600; cursor:pointer; text-align:center;
  transition:background .15s, color .15s, border-color .15s;}
.btn-green{background:var(--green); color:#052e16;} .btn-green:hover{background:var(--green-dark); color:#fff;}
.btn-red{background:transparent; color:var(--red); border:1px solid var(--red);} .btn-red:hover{background:var(--red); color:#fff;}
.btn-ghost{background:transparent; color:var(--muted); border:1px solid var(--border);} .btn-ghost:hover{color:var(--text); border-color:var(--muted);}
.flash{background:rgba(34,197,94,.12); border:1px solid var(--green); color:#bbf7d0;
  border-radius:10px; padding:12px 16px; margin-bottom:18px; font-size:.92rem;}

.admin-wrap{display:flex; gap:20px; align-items:flex-start; margin-top:20px;}
.panel{background:var(--panel); border:1px solid var(--border); border-radius:12px;}
.admin-list{width:38%; max-height:calc(100vh - 160px); overflow-y:auto; padding:10px;}
.admin-review{width:62%; padding:22px; position:sticky; top:96px;}
.panel-head{font-size:.78rem; font-weight:700; letter-spacing:1.5px; text-transform:uppercase;
  color:var(--muted); padding:8px 10px 12px; border-bottom:1px solid var(--border); margin-bottom:10px;}
.admin-review .panel-head{margin:0 0 16px; padding:0 0 12px;}
.pending-item{display:block; padding:12px 14px; border-radius:9px; margin-bottom:6px;
  border:1px solid transparent; transition:background .12s, border-color .12s;}
.pending-item:hover{background:var(--panel-2);}
.pending-item.active{background:var(--panel-2); border-color:var(--green);}
.pi-title{font-weight:600; font-size:.95rem; line-height:1.35; margin-bottom:4px;}
.empty-small{color:var(--muted); font-size:.9rem; padding:14px;}
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
.actions{display:flex; gap:12px; margin-top:18px; flex-wrap:wrap;}
.delete-form{margin-top:14px; border-top:1px solid var(--border); padding-top:16px;}

@media (max-width:1024px){ .grid{grid-template-columns:repeat(2,1fr);} }
@media (max-width:768px){
  .grid{grid-template-columns:1fr; gap:18px;}
  .hero{min-height:380px;} .hero-content{padding:24px 22px;}
  .admin-wrap{flex-direction:column;} .admin-list, .admin-review{width:100%;}
  .admin-list{max-height:42vh;} .admin-review{position:static;}
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
     href="{{ url_for('track_click', article_id=a['id']) }}" target="_blank" rel="noopener noreferrer">
    <div class="card-media">
      <img src="{{ article_image(a) }}" alt="{{ a.translated_title }}"
           loading="{{ 'eager' if eager else 'lazy' }}" onerror="this.style.opacity='0'">
      <span class="chip">{{ category_label(a) }}</span>
      {% if rank %}<span class="badge-trending">&#128293; Naj&#269;itanije</span>
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
        <span>&#128240; {{ a.source }}</span>
        <span>&#128337; {{ a.published_date }}</span>
        <span class="views">&#128065; <b>{{ a.views or 0 }}</b></span>
      </div>
    </div>
  </a>
  {%- endmacro %}

  <header class="topbar">
    <div class="container topbar-inner">
      <div class="brand"><span class="ball">&#9917;</span>Sportski<em>Portal</em></div>
      <span class="live-dot">U&#382;ivo &#8211; RAM baza</span>
    </div>
  </header>

  <main class="container">
    {% if hero or trending or football or basketball or south_america %}

      {% if hero %}
      <div class="hero-head section-head">
        <h3><span class="emoji">&#9889;</span>UDARNA VEST</h3><span class="line"></span>
      </div>
      <a class="hero" href="{{ url_for('track_click', article_id=hero['id']) }}"
         target="_blank" rel="noopener noreferrer">
        <img src="{{ article_image(hero) }}" alt="{{ hero.translated_title }}"
             loading="eager" onerror="this.style.display='none'">
        <div class="hero-overlay"></div>
        <div class="hero-content">
          <div class="hero-tags">
            <span class="badge-hot">&#9889; Udarna vest</span>
            <span class="chip">{{ category_label(hero) }}</span>
            {% for club in club_badges(hero) %}<span class="club-chip {{ club.css }}">&#9917; {{ club.label }}</span>{% endfor %}
            <span class="chip">&#128065; {{ hero.views or 0 }}</span>
          </div>
          <h2>{{ hero.translated_title }}</h2>
          <p>{{ hero.translated_summary }}</p>
          <div class="meta">
            <span>&#128240; {{ hero.source }}</span>
            <span>&#128337; {{ hero.published_date }}</span>
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
      <section class="grid-section">
        <div class="section-head"><h3><span class="emoji">&#9917;</span>DOMA&#262;I TEREN &amp; EVROPSKI GIGANTI</h3><span class="line"></span></div>
        <div class="grid">{% for a in football %}{{ card(a) }}{% endfor %}</div>
      </section>
      {% endif %}

      {% if basketball %}
      <section class="grid-section">
        <div class="section-head"><h3><span class="emoji">&#127936;</span>KO&#352;ARKA</h3><span class="line"></span></div>
        <div class="grid">{% for a in basketball %}{{ card(a) }}{% endfor %}</div>
      </section>
      {% endif %}

      {% if south_america %}
      <section class="grid-section">
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
    Sportski Portal &#8211; diskless autopilot (SQLite :memory: + background thread)<br>
    <span class="foot-note">Podaci su u RAM-u i osve&#382;avaju se svakih {{ interval }}s;
    restart procesa ponovo puni bazu sa RSS feedova.</span>
  </footer>
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
      <a class="btn btn-ghost" href="{{ url_for('index') }}">&larr; Javni sajt</a>
    </div>
  </header>
  <main class="container">
    {% with messages = get_flashed_messages() %}
      {% for message in messages %}<div class="flash" style="margin-top:20px;">{{ message }}</div>{% endfor %}
    {% endwith %}
    <div class="admin-wrap">
      <aside class="admin-list">
        <div class="panel-head">Na &#269;ekanju ({{ pending|length }})</div>
        {% if pending %}
          {% for a in pending %}
          <a class="pending-item {% if selected and selected['id'] == a['id'] %}active{% endif %}"
             href="{{ url_for('admin', article_id=a['id']) }}">
            <div class="pi-title">{{ a.translated_title }}{% if a.priority == 1 %} <span class="badge-hot">&#9889;</span>{% endif %}</div>
            <div class="meta">{{ a.source }}</div>
          </a>
          {% endfor %}
        {% else %}
          <p class="empty-small">Sve prevedene vesti su obra&#273;ene.</p>
        {% endif %}
      </aside>
      <section class="admin-review">
        {% if selected %}
        <div class="panel-head">Pregled i obrada #{{ selected.id }}</div>
        <div class="orig-ref">
          <div class="orig-label">Original &mdash; {{ selected.source }}</div>
          <strong>{{ selected.original_title }}</strong>
          <p>{{ selected.original_summary }}</p>
        </div>
        <form method="post" action="{{ url_for('publish_article', article_id=selected.id) }}">
          <label for="title">Naslov (srpski)</label>
          <input type="text" id="title" name="translated_title" value="{{ selected.translated_title }}" required>
          <label for="summary">Sa&#382;etak / &#269;lanak (srpski)</label>
          <textarea id="summary" name="translated_summary" rows="10" required>{{ selected.translated_summary }}</textarea>
          <div class="actions"><button type="submit" class="btn btn-green">&#10003; Objavi vest</button></div>
        </form>
        <form class="delete-form" method="post" action="{{ url_for('delete_article', article_id=selected.id) }}"
              onsubmit="return confirm('Obrisati ovu vest zauvek?');">
          <button type="submit" class="btn btn-red">&#128465; Obri&#353;i vest</button>
        </form>
        {% else %}
        <div class="empty">&larr; Izaberite vest sa leve liste da biste je pregledali, uredili i objavili.</div>
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
                      translated_title, translated_summary, published_date, priority, views
               FROM articles WHERE status='published'
               ORDER BY published_date DESC, id DESC"""
        ).fetchall()

        hero = next((a for a in articles if a["priority"] == 1), None)
        hero_id = hero["id"] if hero else None

        trending = sorted(
            (a for a in articles if a["id"] != hero_id),
            key=lambda a: (a["views"] or 0, a["published_date"] or "", a["id"]),
            reverse=True,
        )[:3]

        featured_ids = ({hero_id} if hero_id is not None else set()) | {a["id"] for a in trending}
        rest = [a for a in articles if a["id"] not in featured_ids]
        basketball = [a for a in rest if article_category(a) == "basketball"]
        south_america = [a for a in rest if is_south_america(a)]
        sa_ids = {a["id"] for a in south_america}
        football = [a for a in rest
                    if article_category(a) == "football" and a["id"] not in sa_ids]

    return render_template_string(
        PUBLIC_TEMPLATE, hero=hero, trending=trending, football=football,
        basketball=basketball, south_america=south_america,
        interval=FETCH_INTERVAL_SECONDS, css=BASE_CSS,
    )


@app.route("/click/<int:article_id>")
def track_click(article_id: int):
    db = get_db()
    with _db_lock:
        db.execute("UPDATE articles SET views = views + 1 WHERE id = ?", (article_id,))
        db.commit()
        row = db.execute("SELECT link FROM articles WHERE id = ?", (article_id,)).fetchone()
    if row and row["link"]:
        return redirect(row["link"], code=302)
    return redirect(url_for("index"))


@app.route("/osvezi-vesti-777")
def rucno_osvezi_vesti_iz_rama():
    """
    Ruta za ručno forsiranje RSS fetcher-a i prevodioca na Render Free okruženju.
    Slanjem HTTP GET zahteva, Render izvršava ciklus unutar glavne niti zahteva,
    čime se sprečava gašenje procesa i puni volatile :memory: baza podataka.
    """
    try:
        print("[MANUAL FETCH] Pokretanje ručnog osvežavanja vesti kroz HTTP zahtev...")
        run_fetcher_cycle()
        with _db_lock:
            total = _db.execute("SELECT COUNT(*) c FROM articles").fetchone()["c"]
            live = _db.execute(
                "SELECT COUNT(*) c FROM articles WHERE status='published'").fetchone()["c"]
        return (
            "<h3>Uspeh!</h3>"
            "<p>Robot je ručno pokrenut i RAM baza je upravo osvežena novim sportskim vestima.</p>"
            f"<p>Ukupno u bazi: <b>{total}</b> &mdash; objavljeno (uživo): <b>{live}</b>.</p>"
            "<p><a href='/'>Vrati se na početnu stranicu</a> ili idi na <a href='"
            + ADMIN_PATH + "'>Admin Panel</a>.</p>"
        )
    except Exception as e:
        print(f"[MANUAL FETCH][ERROR] Greška prilikom ručnog osvežavanja: {e}")
        return f"<h3>Greška prilikom buđenja robota:</h3><p>{e}</p>", 500


@app.route(ADMIN_PATH)
def admin():
    db = get_db()
    with _db_lock:
        pending = db.execute(
            """SELECT id, source, translated_title, priority FROM articles
               WHERE status='pending' AND translated_title != ''
               ORDER BY priority DESC, published_date DESC, id DESC"""
        ).fetchall()
        selected = None
        article_id = request.args.get("article_id", type=int)
        if article_id:
            selected = db.execute("SELECT * FROM articles WHERE id = ?", (article_id,)).fetchone()
    return render_template_string(ADMIN_TEMPLATE, pending=pending,
                                  selected=selected, css=BASE_CSS)


@app.post("/admin/publish/<int:article_id>")
def publish_article(article_id: int):
    title = (request.form.get("translated_title") or "").strip()
    summary = (request.form.get("translated_summary") or "").strip()
    if not title or not summary:
        flash("Naslov i sa&#382;etak ne smeju biti prazni.")
        return redirect(url_for("admin", article_id=article_id))
    db = get_db()
    with _db_lock:
        db.execute(
            """UPDATE articles SET translated_title=?, translated_summary=?, status='published'
               WHERE id=?""", (title, summary, article_id))
        db.commit()
    flash(f"Vest #{article_id} je objavljena.")
    return redirect(url_for("admin"))


@app.post("/admin/delete/<int:article_id>")
def delete_article(article_id: int):
    db = get_db()
    with _db_lock:
        db.execute("DELETE FROM articles WHERE id = ?", (article_id,))
        db.commit()
    flash(f"Vest #{article_id} je obrisana.")
    return redirect(url_for("admin"))


# =========================================================================== #
#  BOOTSTRAP
# =========================================================================== #

init_db()
start_background_fetcher()

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False, threaded=True)
