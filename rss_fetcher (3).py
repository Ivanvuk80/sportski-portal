"""
Sports News Aggregator - Phase 1, Step 4 (Autopilot)
Fetches sports RSS feeds, deduplicates articles by link, assigns a
rule-based priority, stores everything in SQLite, then turns the brief
RSS summaries into Serbian content via a dual-mode engine:
  - "free": direct Google translation (deep-translator)
  - "ai"  : gpt-4o-mini rewrites the short summary into a full ~150-word
            Serbian sports article plus an SEO-optimised headline

Autopilot:
  - High-priority articles (priority = 1) are published automatically and
    go straight to the live homepage, bypassing the admin review queue.
  - Normal articles stay 'pending' for manual review in the admin panel.
  - The script runs continuously, refreshing the feeds every 10 minutes.

Usage:
    pip install feedparser deep-translator     # + `pip install openai` for AI
    python rss_fetcher.py     # CTRL+C to stop the autopilot loop

Modes:
    TRANSLATION_MODE = "free" -> Google Translate (via deep-translator)
    TRANSLATION_MODE = "ai"   -> OpenAI gpt-4o-mini (requires OPENAI_API_KEY)
"""

import html
import os
import re
import socket
import sqlite3
import time
from pathlib import Path
from typing import Any

import feedparser
from deep_translator import GoogleTranslator

# Hard timeout for network operations (feedparser uses urllib under the hood)
socket.setdefaulttimeout(15)

DB_PATH = Path(__file__).with_name("sports_news.db")

# --------------------------------------------------------------------------- #
# Configuration flags
# --------------------------------------------------------------------------- #
TRANSLATION_MODE = "free"          # "free" (Google) or "ai" (OpenAI gpt-4o-mini)
TARGET_LANGUAGE = "sr"             # Serbian (ISO-639-1, Google returns Serbian)
MAX_TRANSLATIONS_PER_RUN = 5       # cap per cycle to save API tokens/time while testing

# Autopilot: high-priority articles skip the admin queue and go live immediately
AUTOPILOT_PUBLISH_HIGH_PRIORITY = True

# Continuous background loop
RUN_CONTINUOUSLY = True            # False = single run; True = loop forever
LOOP_INTERVAL_SECONDS = 600        # wait 10 minutes between fetch+translate cycles

SPORTS_FEEDS = [
    {"name": "BBC Sport", "url": "https://feeds.bbci.co.uk/sport/rss.xml"},
    {"name": "Ole (Argentina)", "url": "https://www.ole.com.ar/rss/"},
    {"name": "Clarin Deportes (Argentina)", "url": "https://www.clarin.com/rss/deportes/"},
    # TyC Sports no longer exposes a public RSS feed; add new sources here.
]

# A whole-word hit in title OR summary marks an article as high priority (1)
HIGH_PRIORITY_KEYWORDS = [
    "Messi", "Maradona",                 # legendary players
    "Boca Juniors", "Boca",              # Argentine superclasico clubs
    "River Plate", "River",              # (short forms used in most headlines)
    "Transfer",                          # English transfer-window news
    "Fichaje", "Refuerzo",               # Spanish transfer-window equivalents
]

# Editorial breaking-news labels only ("BREAKING:", "BREAKING -", "Breaking news"),
# so generic prose like "breaking the world record" does not trigger high priority
BREAKING_NEWS_PATTERN = r"\bbreaking(?:\s*[:-]|\s+news\b)"

# Sports we never want flagged as high priority, even if they mention a keyword.
# A mention of any of these instantly forces Normal priority (0).
JUNK_SPORT_WORDS = [
    "triathlon", "cricket", "rugby", "golf", "snooker",
    "triatlon", "kriket",
]

# The free Google endpoint intermittently returns an HTTP-500 HTML error page
# instead of raising; treat such bodies as failures and retry rather than
# persisting them as translations.
FREE_MAX_RETRIES = 3
TRANSLATION_ERROR_MARKERS = (
    "error 500", "server error", "that’s an error", "that's an error",
    "please try again", "too many requests",
)

# --------------------------------------------------------------------------- #
# AI translation prompts (used only in TRANSLATION_MODE = "ai")
# --------------------------------------------------------------------------- #
AI_HEADLINE_SYSTEM_PROMPT = (
    "You are a senior Serbian sports journalist and SEO copywriter. "
    "You receive a sports news headline in Spanish or English.\n"
    "Your task:\n"
    "1. Translate to Serbian, convert foreign football slang into localized "
    "Serbian sports terminology, and rewrite the headline to be unique and "
    "catchy for SEO purposes.\n"
    "2. Preserve every key fact: club names, player names, scores, and results. "
    "Keep club/player names in their standard Serbian press form.\n"
    "3. Use natural, punchy headline-style Serbian as seen on popular Serbian "
    "sports portals (e.g. Mozzart Sport, Sportal).\n"
    "4. Output ONLY the translated headline — no quotes, no explanations."
)

AI_BODY_SYSTEM_PROMPT = (
    "You are a senior sports journalist writing for a major Serbian sports "
    "portal (in the style of Mozzart Sport, Sportal or Arena Sport). You are "
    "given a short, one-sentence RSS news brief plus its headline, in Spanish "
    "or English.\n"
    "Your task:\n"
    "1. Translate to Serbian and EXPAND the brief into a full, engaging and "
    "professional Serbian sports news article of 2-3 detailed paragraphs, "
    "roughly 150 words total. Do NOT just translate the one line — turn it "
    "into a proper article.\n"
    "2. Open with a strong journalistic lead (who, what, when, result), then "
    "add context: the key moment, the stakes, standings/tournament impact, "
    "and a closing sentence about what happens next.\n"
    "3. Convert foreign football slang and jargon into natural, localized "
    "Serbian sports terminology (e.g. 'derbi', 'prelazni rok', 'ofšajd', "
    "'kapiten', 'gostovanje'). Use club and player names in their standard "
    "Serbian press form.\n"
    "4. Stay 100% faithful to the facts given in the brief — never invent "
    "scores, quotes, injuries or statistics that were not provided. Only "
    "elaborate on the known facts and general context.\n"
    "5. Write fluent, punchy, authentic journalistic Serbian that reads like a "
    "real article on a major portal.\n"
    "6. Output ONLY the article body (the 2-3 paragraphs), with no headline, "
    "no preamble and no explanations."
)


# --------------------------------------------------------------------------- #
# Feed parsing
# --------------------------------------------------------------------------- #

def clean_text(raw: str | None) -> str:
    """Strip HTML tags/entities and collapse whitespace from feed text."""
    if not raw:
        return ""
    text = re.sub(r"<[^>]+>", " ", raw)
    text = html.unescape(text)
    return re.sub(r"\s+", " ", text).strip()


def format_date(entry: Any) -> str:
    """Normalize the publication date from a feed entry, falling back to raw string."""
    parsed = entry.get("published_parsed") or entry.get("updated_parsed")
    if parsed:
        return time.strftime("%Y-%m-%d %H:%M:%S UTC", parsed)
    return entry.get("published") or entry.get("updated") or "Unknown date"


def parse_entry(entry: Any, source: str) -> dict[str, str]:
    """Extract a single article's fields into a dictionary."""
    return {
        "source": source,
        "title": clean_text(entry.get("title")),
        "link": entry.get("link", ""),
        "published": format_date(entry),
        "summary": clean_text(entry.get("summary") or entry.get("description")),
    }


# --------------------------------------------------------------------------- #
# Priority rules engine
# --------------------------------------------------------------------------- #

def calculate_priority(title: str, summary: str) -> int:
    """
    Return 1 (high) if a high-priority keyword matches as a whole word or a
    breaking-news label appears, else 0 (normal). Word boundaries prevent
    substring false positives such as 'river' in 'driver' or 'boca' in 'mouth'.
    """
    text = f"{title or ''} {summary or ''}".lower()

    # Exclusion filter: non-core sports never become high priority.
    if any(re.search(rf"\b{re.escape(word)}\b", text) for word in JUNK_SPORT_WORDS):
        return 0

    for keyword in HIGH_PRIORITY_KEYWORDS:
        if re.search(rf"\b{re.escape(keyword.lower())}s?\b", text):
            return 1

    if re.search(BREAKING_NEWS_PATTERN, text):
        return 1

    return 0


# --------------------------------------------------------------------------- #
# Translation engine (dual mode)
# --------------------------------------------------------------------------- #

def translate_text(
    text: str,
    target_lang: str = "sr",
    mode: str = "free",
    is_headline: bool = False,
    source_headline: str | None = None,
) -> str:
    """
    Translate (free mode) or rewrite (AI mode) one text block to target_lang.

    mode="free": direct Google Translate via deep-translator (no API key).
    mode="ai"  : OpenAI gpt-4o-mini with sports-localization prompts and, for
                 bodies, full-article expansion. `source_headline` is forwarded
                 to the body call so the AI has the headline as context.
    """
    if not text or not text.strip():
        return ""

    if mode == "free":
        return _translate_free(text, target_lang)

    if mode == "ai":
        return _translate_ai(text, target_lang, is_headline, source_headline)

    raise ValueError(f"Unknown translation mode: {mode!r} (use 'free' or 'ai')")


def _translate_free(text: str, target_lang: str) -> str:
    """
    Direct Google Translate call with retry/backoff. Google occasionally answers
    with an HTML error page (HTTP 500) or rate-limit text without raising, so the
    result is validated and retried before being accepted.
    """
    translator = GoogleTranslator(source="auto", target=target_lang)
    last_error: Exception | None = None

    for attempt in range(1, FREE_MAX_RETRIES + 1):
        try:
            result = translator.translate(text)
            if result and not _looks_like_error_page(result):
                return result
            last_error = RuntimeError("translator returned an error page")
        except Exception as exc:  # network/API hiccup -> retry
            last_error = exc

        if attempt < FREE_MAX_RETRIES:
            time.sleep(2.0 * attempt)  # linear backoff: 2s, 4s

    raise RuntimeError(f"Free translation failed after {FREE_MAX_RETRIES} attempts: {last_error}")


def _looks_like_error_page(text: str) -> bool:
    """True when a supposed translation is actually an HTTP error page body."""
    lowered = text.lower()
    return any(marker in lowered for marker in TRANSLATION_ERROR_MARKERS)


def _translate_ai(
    text: str,
    target_lang: str,
    is_headline: bool,
    source_headline: str | None = None,
) -> str:
    """
    OpenAI backend. The chat model receives a detailed system prompt
    (AI_HEADLINE_SYSTEM_PROMPT for headlines / AI_BODY_SYSTEM_PROMPT for bodies)
    plus the raw source text, and returns only the Serbian result. For bodies
    the source headline is supplied as additional context for the article.
    """
    try:
        from openai import OpenAI
    except ImportError as exc:  # pragma: no cover - depends on optional dependency
        raise RuntimeError(
            "AI mode requires the 'openai' package: pip install openai"
        ) from exc

    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        raise RuntimeError("AI mode requires the OPENAI_API_KEY environment variable")

    client = OpenAI(api_key=api_key)
    system_prompt = AI_HEADLINE_SYSTEM_PROMPT if is_headline else AI_BODY_SYSTEM_PROMPT

    # Bodies are expanded into full articles, so give the model more room
    if is_headline:
        user_content = f"Target language code: {target_lang}\n\nHeadline:\n{text}"
        temperature, max_tokens = 0.7, 200
    else:
        user_content = (
            f"Target language code: {target_lang}\n\n"
            f"Headline:\n{source_headline or ''}\n\n"
            f"News brief (summary):\n{text}"
        )
        temperature, max_tokens = 0.7, 900  # ~150 Serbian words

    response = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_content},
        ],
        temperature=temperature,
        max_tokens=max_tokens,
    )
    return response.choices[0].message.content.strip()


def process_translations(
    conn: sqlite3.Connection,
    mode: str = TRANSLATION_MODE,
    target_lang: str = TARGET_LANGUAGE,
    limit: int = MAX_TRANSLATIONS_PER_RUN,
) -> tuple[int, int]:
    """
    Process up to `limit` untranslated articles (high priority first), generate
    the Serbian headline and body, and persist each result immediately. A
    failure on one article is logged and skipped; successful results are
    committed so no progress is lost. High-priority articles are set to
    'published' (autopilot -> live homepage); normal ones stay 'pending' for
    the admin queue. Returns (translated_count, failed_count).
    """
    rows = conn.execute(
        """
        SELECT id, source, original_title, original_summary, priority
        FROM articles
        WHERE translated_title = '' AND translated_summary = ''
        ORDER BY priority DESC, published_date DESC
        LIMIT ?
        """,
        (limit,),
    ).fetchall()

    if not rows:
        print("[INFO] No untranslated articles pending.")
        return 0, 0

    print(f"[TRANSLATE] mode='{mode}' target='{target_lang}' - {len(rows)} article(s) queued")

    translated = 0
    failed = 0

    for article_id, source, title, summary, priority in rows:
        try:
            translated_title = translate_text(
                title, target_lang, mode, is_headline=True, source_headline=title
            )
            # In AI mode the body is expanded into a full ~150-word article;
            # the headline is passed along as context for that generation.
            translated_summary = (
                translate_text(
                    summary, target_lang, mode,
                    is_headline=False, source_headline=title,
                )
                if summary else ""
            )

            # Autopilot: a finished high-priority article goes live the moment
            # its Serbian content exists; normal articles stay in the admin
            # review queue. This is what actually bypasses the admin panel.
            if AUTOPILOT_PUBLISH_HIGH_PRIORITY and priority == 1:
                new_status = "published"
            else:
                new_status = "pending"

            conn.execute(
                """
                UPDATE articles
                SET translated_title = ?, translated_summary = ?, status = ?
                WHERE id = ?
                """,
                (translated_title, translated_summary, new_status, article_id),
            )
            conn.commit()  # commit each success so later failures cannot lose it
            translated += 1

            flag = "AUTO-PUBLISHED" if new_status == "published" else "pending"
            print(f"\n  [OK] #{article_id} [{source}] -> {flag}")
            print(f"       EN/ES : {title[:80]}")
            print(f"       SR    : {translated_title[:80]}")

            # Be polite to the free translation endpoint
            if mode == "free":
                time.sleep(0.5)

        except Exception as exc:
            # One bad translation must never abort the whole batch
            conn.rollback()
            failed += 1
            print(f"\n  [ERROR] Translation failed for article #{article_id} ({source}): {exc}")
            continue

    print(f"\n[TRANSLATE] Done: {translated} translated, {failed} failed")
    return translated, failed


# --------------------------------------------------------------------------- #
# Database layer
# --------------------------------------------------------------------------- #

def init_db(conn: sqlite3.Connection) -> None:
    """Create the articles table if it does not exist yet."""
    conn.execute(
        """
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
                                                CHECK (status IN ('pending', 'published')),
            views              INTEGER NOT NULL DEFAULT 0
        )
        """
    )
    conn.commit()
    _migrate_views_column(conn)


def _migrate_views_column(conn: sqlite3.Connection) -> None:
    """Add the analytics 'views' column to databases created before Step 4.2."""
    columns = {row[1] for row in conn.execute("PRAGMA table_info(articles)")}
    if "views" not in columns:
        conn.execute("ALTER TABLE articles ADD COLUMN views INTEGER NOT NULL DEFAULT 0")
        conn.commit()
        print("[DB] Migrated: added 'views' column to articles table.")


def link_exists(conn: sqlite3.Connection, link: str) -> bool:
    """Deduplication check: an article with this link is already stored."""
    row = conn.execute(
        "SELECT 1 FROM articles WHERE link = ? LIMIT 1", (link,)
    ).fetchone()
    return row is not None


def insert_article(
    conn: sqlite3.Connection, article: dict[str, Any], status: str = "pending"
) -> None:
    """
    Persist one new article. `status` is 'pending' for normal items (they wait
    in the admin queue) or 'published' for autopilot high-priority items (they
    go straight to the live homepage once translated).
    """
    conn.execute(
        """
        INSERT INTO articles
            (source, original_title, original_summary, link,
             published_date, priority, status)
        VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            article["source"],
            article["title"],
            article["summary"],
            article["link"],
            article["published"],
            article["priority"],
            status,
        ),
    )


# --------------------------------------------------------------------------- #
# Fetch loop (DB updates stay localized here)
# --------------------------------------------------------------------------- #

def fetch_feed(feed: dict[str, str], conn: sqlite3.Connection) -> tuple[list[dict], int]:
    """
    Fetch one feed, deduplicate by link, score priority, and insert new
    articles inside the loop. Returns (newly_inserted_articles, skipped_count).
    """
    source, url = feed["name"], feed["url"]
    inserted: list[dict] = []
    skipped = 0

    try:
        parsed = feedparser.parse(url, agent="SportsAggregator/1.0")

        # feedparser does not raise on HTTP/parse errors; it flags them via bozo
        if parsed.bozo and not parsed.entries:
            raise parsed.bozo_exception or RuntimeError("Feed returned no entries")

        for entry in parsed.entries:
            article = parse_entry(entry, source)

            if link_exists(conn, article["link"]):
                skipped += 1
                continue

            article["priority"] = calculate_priority(article["title"], article["summary"])

            # Every new article starts 'pending'. High-priority items are marked
            # for autopilot and flipped to 'published' by process_translations()
            # the moment their Serbian content exists — publishing an
            # untranslated row now would put a blank card on the homepage.
            article["status"] = "pending"
            insert_article(conn, article, status=article["status"])
            inserted.append(article)

        conn.commit()  # one transaction per feed
        flagged = sum(1 for a in inserted if a["priority"] == 1)
        print(
            f"[OK] {source}: {len(inserted)} new "
            f"({flagged} high-priority, auto-publish on translation), "
            f"{skipped} duplicates skipped"
        )

    except Exception as exc:
        # One bad feed must never stop the whole aggregation run
        conn.rollback()
        print(f"[ERROR] {source} ({url}) is unavailable: {exc}")

    return inserted, skipped


def fetch_all_feeds(
    feeds: list[dict[str, str]], conn: sqlite3.Connection
) -> tuple[list[dict], int]:
    """Loop through every configured feed and aggregate newly stored articles."""
    articles: list[dict] = []
    total_skipped = 0
    for feed in feeds:
        inserted, skipped = fetch_feed(feed, conn)
        articles.extend(inserted)
        total_skipped += skipped
    return articles, total_skipped


# --------------------------------------------------------------------------- #
# Terminal output
# --------------------------------------------------------------------------- #

def print_articles(articles: list[dict]) -> None:
    """Print newly inserted articles with clear terminal formatting."""
    print("\n" + "=" * 80)
    print(f"NEWLY STORED ARTICLES - {len(articles)}".center(80))
    print("=" * 80)

    for i, article in enumerate(articles, start=1):
        summary = article["summary"]
        if len(summary) > 200:
            summary = summary[:197].rstrip() + "..."
        priority = "HIGH (1)" if article["priority"] == 1 else "NORMAL (0)"

        print(f"\n[{i}] {article['title']}")
        print(f"    Source  : {article['source']}")
        print(f"    Date    : {article['published']}")
        print(f"    Link    : {article['link']}")
        print(f"    Priority: {priority}   Status: {article['status']}")
        print(f"    Summary : {summary or 'No summary available.'}")
        print("-" * 80)


def print_db_summary(conn: sqlite3.Connection, new_count: int, skipped: int) -> None:
    """Report run totals and current database contents."""
    total, high, untranslated, published = conn.execute(
        """
        SELECT COUNT(*),
               COALESCE(SUM(priority), 0),
               SUM(CASE WHEN translated_title = '' AND translated_summary = ''
                        THEN 1 ELSE 0 END),
               SUM(CASE WHEN status = 'published' THEN 1 ELSE 0 END)
        FROM articles
        """
    ).fetchone()

    print("\n" + "=" * 80)
    print("RUN SUMMARY".center(80))
    print("=" * 80)
    print(f"  New articles inserted   : {new_count}")
    print(f"  Duplicates skipped      : {skipped}")
    print(f"  Articles in database    : {total}")
    print(f"    - high priority       : {high}")
    print(f"    - awaiting translation: {untranslated}")
    print(f"    - published           : {published}")
    print("=" * 80)


def run_cycle(conn: sqlite3.Connection) -> None:
    """One complete autopilot pass: fetch -> print -> translate -> summarize."""
    articles, skipped = fetch_all_feeds(SPORTS_FEEDS, conn)
    print_articles(articles)

    # Translation / article-generation pass on untranslated rows
    process_translations(conn)

    print_db_summary(conn, len(articles), skipped)


def main() -> None:
    conn = sqlite3.connect(DB_PATH)
    try:
        init_db(conn)

        if not RUN_CONTINUOUSLY:
            # Single-run mode (handy for cron/systemd or one-off testing)
            run_cycle(conn)
            return

        # Continuous background loop: stay alive, refresh every 10 minutes
        print(
            f"[AUTOPILOT] Continuous mode ON - refreshing feeds every "
            f"{LOOP_INTERVAL_SECONDS}s. Press CTRL+C to stop.\n"
        )
        cycle = 0
        while True:
            cycle += 1
            print("\n" + "#" * 80)
            print(f"# AUTOPILOT CYCLE {cycle} - {time.strftime('%Y-%m-%d %H:%M:%S')}".center(79))
            print("#" * 80)

            try:
                run_cycle(conn)
            except Exception as exc:
                # Never let a single bad cycle kill the background process
                conn.rollback()
                print(f"[AUTOPILOT] Cycle {cycle} failed but loop continues: {exc}")

            print(f"\n[AUTOPILOT] Sleeping {LOOP_INTERVAL_SECONDS}s until next cycle...")
            time.sleep(LOOP_INTERVAL_SECONDS)

    except KeyboardInterrupt:
        print("\n[AUTOPILOT] Stopped by user (CTRL+C). Bye!")
    finally:
        conn.close()


if __name__ == "__main__":
    main()
