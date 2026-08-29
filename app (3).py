"""
Sports News Aggregator - Phase 2 (Premium UI)
Flask web server: a professional sports-portal homepage (hero + responsive
article grid, dynamic placeholder imagery) and a secret split-screen admin
dashboard for reviewing, editing, publishing and deleting articles.

Templates are embedded with render_template_string so the whole app is a
single deployable file.

Environment variables (all optional):
    DATABASE_PATH  - full path to sports_news.db (defaults: next to this file)
    SECRET_KEY     - Flask session/flash secret (set this in production!)
    PORT           - port for local dev server (default 5000)

Run locally:
    pip install flask
    python app.py
"""

import os
import random
import re
import sqlite3
from pathlib import Path

from flask import Flask, g, flash, redirect, render_template_string, request, url_for

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

DB_PATH = Path(
    os.environ.get("DATABASE_PATH", Path(__file__).resolve().parent / "sports_news.db")
)
ADMIN_PATH = "/admin-tajna-kontrola-777"  # secret, unguessable admin URL

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "dev-insecure-secret-change-in-production")


# --------------------------------------------------------------------------- #
# Dynamic placeholder imagery (RSS rarely ships usable images)
# --------------------------------------------------------------------------- #

# Keyword sets drive BOTH the placeholder image and the category chip.
_BASKETBALL_KEYWORDS = [
    "nba", "jokic", "jokić", "basketball", "košarka", "kosarka",
    "košarkašk", "kosarkask", "basket",
]
_FOOTBALL_KEYWORDS = [
    # General
    "football", "soccer", "fudbal", "fudbalsk", "messi", "maradona",
    "boca juniors", "boca", "xeneize", "river plate", "river", "lanus",
    "lanús", "velez", "vélez", "real madrid", "liverpool", "barselona",
    "barcelona", "psg", "fichaje", "refuerzo", "transfer", "gol",
    "utakmica", "meč", "premier league", "la liga", "clausura",
    "libertadores", "golman", "kapiten", "trener", "derbi", "prelazni rok",
    "ofšajd", "napad", "odbrana",
    # Local Serbian clubs / slang (Superliga)
    "radnicki", "radnički", "radničkog", "radničkom", "radnički 1923",
    "kragujevac", "kragujevcu", "vojvodina", "vojvodine", "vojvodini",
    "vosa", "voša", "voše", "cika daca", "čika dača",
    "đavoli", "davoli", "superliga", "novosađani", "novosadjani",
    # Brazilian stars / clubs
    "neymar", "ronaldinho", "pelé", "pele", "endrick", "estevao", "estêvão",
    "messinho", "flamengo", "palmeiras", "santos",
    "sao paulo", "são paulo", "fluminense",
]

# South American football — powers the dedicated "Južnoamerička magija" grid.
_SOUTH_AMERICA_KEYWORDS = [
    # Argentina
    "boca", "river", "xeneize", "millonario", "nuñeza", "nunjeza",
    "boca juniors", "river plate", "lanús", "lanus", "vélez", "velez",
    "racing", "independiente", "san lorenzo", "estudiantes",
    "bombonera", "clausura", "libertadores", "sudamericana", "gaucho", "gaučo",
    "messi", "maradona", "tevez", "riquelme", "gallardo", "arruabarrena",
    "arrubarena", "ponzio", "belmonte",
    # Brazil
    "neymar", "ronaldinho", "pelé", "pele", "endrick", "estevao", "estêvão",
    "messinho", "flamengo", "palmeiras", "santos",
    "sao paulo", "são paulo", "fluminense", "brasileirao", "brasileirão",
    "carioca", "carioka",
]


# Curated, hot-linkable Unsplash photos (auto-sized via URL params).
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


def article_text_blob(article) -> str:
    """All text we use to guess the article's sport (SR + original)."""
    def val(key):
        try:
            return article[key] or ""
        except (KeyError, IndexError, TypeError):
            return ""
    return " ".join(
        val(k) for k in ("translated_title", "translated_summary",
                         "original_title", "original_summary", "source")
    ).lower()


def article_category(article) -> str:
    """Guess 'basketball' / 'football' / 'general' from the article's text."""
    text = article_text_blob(article)
    if any(kw in text for kw in _BASKETBALL_KEYWORDS):
        return "basketball"
    if any(kw in text for kw in _FOOTBALL_KEYWORDS):
        return "football"
    return "general"


def is_south_america(article) -> bool:
    """
    True when an article is about South American (Argentine/Brazilian) football.
    Word-boundary at the START of each keyword (\\b<kw>) avoids false hits such as
    'river' inside 'driver' while still matching inflected forms (Boku, Messija…).
    """
    text = article_text_blob(article)
    return any(
        re.search(rf"\b{re.escape(kw)}", text)
        for kw in _SOUTH_AMERICA_KEYWORDS
    )


def article_image(article) -> str:
    """
    Deterministically pick a professional placeholder image for the article's
    sport (seeded by id so the same article always gets the same picture).
    """
    category = article_category(article)
    try:
        seed = article["id"] or 0
    except (KeyError, IndexError, TypeError):
        seed = 0
    return random.Random(f"img-{seed}").choice(PLACEHOLDER_IMAGES[category])


def category_label(article) -> str:
    return CATEGORY_LABELS[article_category(article)]


# Expose the helpers to Jinja templates
app.jinja_env.globals.update(
    article_image=article_image,
    article_category=article_category,
    category_label=category_label,
)


# --------------------------------------------------------------------------- #
# Database helpers
# --------------------------------------------------------------------------- #

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
                                        CHECK (status IN ('pending', 'published')),
    views              INTEGER NOT NULL DEFAULT 0
)
"""


def init_db() -> None:
    """Make sure the articles table exists and has the analytics 'views' column."""
    try:
        with sqlite3.connect(DB_PATH) as db:
            db.execute(SCHEMA_SQL)
            columns = {row[1] for row in db.execute("PRAGMA table_info(articles)")}
            if "views" not in columns:
                db.execute(
                    "ALTER TABLE articles ADD COLUMN views INTEGER NOT NULL DEFAULT 0"
                )
                print("[DB] Migrated: added 'views' column to articles table.")
            db.commit()
    except sqlite3.Error as exc:  # read-only FS on some serverless hosts
        print(f"[WARN] Could not initialize database at {DB_PATH}: {exc}")


def get_db() -> sqlite3.Connection:
    """One SQLite connection per request, closed automatically on teardown."""
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
    return g.db


@app.teardown_appcontext
def close_db(_exception: Exception | None) -> None:
    db = g.pop("db", None)
    if db is not None:
        db.close()


# --------------------------------------------------------------------------- #
# Shared dark-mode CSS (no external frameworks)
# --------------------------------------------------------------------------- #

BASE_CSS = """
:root{
  --bg:#0f172a; --panel:#1e293b; --panel-2:#162033; --border:#334155;
  --text:#f8fafc; --muted:#94a3b8;
  --green:#22c55e; --green-dark:#16a34a; --red:#ef4444; --red-dark:#dc2626;
  --shadow:0 10px 30px rgba(2,6,23,.45);
}
*{box-sizing:border-box; margin:0; padding:0;}
html{-webkit-text-size-adjust:100%;}
body{
  background:var(--bg); color:var(--text);
  font-family:'Segoe UI', system-ui, -apple-system, Roboto, sans-serif;
  line-height:1.6; min-height:100vh;
}
.container{max-width:1200px; margin:0 auto; padding:0 20px;}
a{color:inherit; text-decoration:none;}
img{display:block; max-width:100%;}

/* ---------- Top bar ---------- */
.topbar{
  background:rgba(15,23,42,.85); backdrop-filter:blur(10px);
  border-bottom:1px solid var(--border); position:sticky; top:0; z-index:20;
}
.topbar-inner{display:flex; align-items:center; justify-content:space-between;
  gap:12px; padding:16px 0; flex-wrap:wrap;}
.brand{display:flex; align-items:center; gap:10px; font-size:1.35rem;
  font-weight:800; letter-spacing:.3px;}
.brand .ball{font-size:1.5rem;}
.brand em{font-style:normal; color:var(--green);}
.topbar-tag{color:var(--muted); font-size:.78rem; text-transform:uppercase;
  letter-spacing:2.5px;}

/* ---------- Category chips & badges ---------- */
.chip{
  display:inline-block; background:rgba(15,23,42,.72); color:#e2e8f0;
  border:1px solid rgba(148,163,184,.35); border-radius:999px;
  padding:4px 12px; font-size:.72rem; font-weight:700; letter-spacing:.8px;
  text-transform:uppercase; backdrop-filter:blur(4px);
}
.badge-hot{
  display:inline-block; background:var(--green); color:#052e16;
  border-radius:999px; padding:4px 12px; font-size:.72rem; font-weight:800;
  letter-spacing:.8px; text-transform:uppercase; white-space:nowrap;
  box-shadow:0 0 18px rgba(34,197,94,.5);
}

/* ---------- Hero article ---------- */
.hero{
  position:relative; border-radius:18px; overflow:hidden; margin:26px 0 34px;
  min-height:440px; display:flex; align-items:flex-end;
  border:1px solid var(--border); box-shadow:var(--shadow);
}
.hero img{position:absolute; inset:0; width:100%; height:100%;
  object-fit:cover;}
.hero-overlay{
  position:absolute; inset:0;
  background:linear-gradient(to top, rgba(2,6,23,.96) 0%, rgba(2,6,23,.72) 42%,
             rgba(2,6,23,.15) 75%, rgba(2,6,23,.05) 100%);
}
.hero-content{position:relative; padding:34px 36px; max-width:860px;}
.hero-tags{display:flex; gap:10px; margin-bottom:14px; flex-wrap:wrap;}
.hero h2{
  font-size:clamp(1.6rem, 3.6vw, 2.6rem); font-weight:800; line-height:1.15;
  margin-bottom:12px; text-shadow:0 2px 14px rgba(0,0,0,.5);
}
.hero p{
  font-size:clamp(1rem, 1.6vw, 1.18rem); color:#cbd5e1; line-height:1.6;
  margin-bottom:16px;
}
.hero .meta{font-size:.9rem;}
.hero{transition:transform .25s ease;}
.hero:hover{transform:translateY(-3px);}

/* ---------- Section heading ---------- */
.section-head{
  display:flex; align-items:center; gap:12px; margin:8px 0 20px;
}
.section-head h3{
  font-size:1.25rem; font-weight:800; letter-spacing:.4px;
  border-left:4px solid var(--green); padding-left:12px;
}
.section-head .line{flex:1; height:1px; background:var(--border);}
.section-head h3 .emoji{margin-right:8px;}
.section-head .sa-sub{font-size:.72rem; font-weight:600; color:var(--muted);
  text-transform:none; letter-spacing:.3px; white-space:nowrap;}
.grid-section{margin-bottom:44px;}

/* ---------- Article grid ---------- */
.grid{display:grid; grid-template-columns:repeat(3, 1fr); gap:24px;}
.card{
  background:var(--panel); border:1px solid var(--border);
  border-radius:12px; overflow:hidden; display:flex; flex-direction:column;
  color:inherit; cursor:pointer;
  transition:transform .22s ease, box-shadow .22s ease, border-color .22s ease;
}
.views{margin-left:auto; font-weight:600; color:var(--muted);}
.views b{color:var(--green); font-weight:700;}

/* ---------- Most-read (trending) accents ---------- */
.card.trending{border-color:rgba(249,115,22,.45);}
.card.trending:hover{
  box-shadow:0 14px 34px rgba(249,115,22,.20), 0 4px 14px rgba(2,6,23,.5);
  border-color:rgba(249,115,22,.75);
}
.badge-trending{
  position:absolute; top:12px; right:12px;
  display:inline-flex; align-items:center; gap:4px;
  background:linear-gradient(135deg,#f97316,#f59e0b); color:#1f1300;
  border-radius:999px; padding:4px 11px; font-size:.72rem; font-weight:800;
  letter-spacing:.6px; text-transform:uppercase; white-space:nowrap;
  box-shadow:0 4px 14px rgba(249,115,22,.45);
}
.card-rank{
  position:absolute; bottom:12px; left:12px;
  display:inline-flex; align-items:center; justify-content:center;
  width:30px; height:30px; border-radius:50%;
  background:var(--green); color:#052e16; font-weight:800; font-size:.95rem;
  box-shadow:0 4px 12px rgba(2,6,23,.5);
}
/* Green left-border indicator for the hero section header */
.hero-head h3{
  font-size:1.25rem; font-weight:800; letter-spacing:.4px;
  border-left:4px solid var(--green); padding-left:12px;
}
.hero-head{margin:8px 0 18px;}
.card:hover{
  transform:scale(1.02);
  box-shadow:0 14px 34px rgba(34,197,94,.16), 0 4px 14px rgba(2,6,23,.5);
  border-color:rgba(34,197,94,.5);
}
.card-media{position:relative; aspect-ratio:16/9; overflow:hidden;
  background:linear-gradient(135deg,#1e293b,#0f172a);}
.card-media img{width:100%; height:100%; object-fit:cover;
  transition:transform .35s ease;}
.card:hover .card-media img{transform:scale(1.06);}
.card-media .chip{position:absolute; top:12px; left:12px;}
.card-media .badge-hot{position:absolute; top:12px; right:12px;}
.card-body{padding:18px 20px 20px; display:flex; flex-direction:column;
  gap:10px; flex:1;}
.card-body h4{font-size:1.06rem; font-weight:700; line-height:1.35;}
.card-excerpt{color:#cbd5e1; font-size:.92rem;
  display:-webkit-box; -webkit-line-clamp:3; -webkit-box-orient:vertical;
  overflow:hidden;}
.card-body .meta{margin-top:auto; padding-top:8px; border-top:1px solid var(--border);}

/* ---------- Meta / misc ---------- */
.meta{display:flex; gap:16px; flex-wrap:wrap; color:var(--muted);
  font-size:.84rem; align-items:center;}
.empty{
  background:var(--panel); border:1px dashed var(--border); border-radius:14px;
  color:var(--muted); text-align:center; padding:64px 24px; font-size:1.08rem;
}
.footer-text{color:var(--muted); font-size:.82rem; text-align:center;
  padding:34px 0 26px;}

/* ---------- Buttons ---------- */
.btn{
  display:inline-block; border:none; border-radius:9px; padding:11px 20px;
  font-size:.92rem; font-weight:600; cursor:pointer; text-align:center;
  transition:background .15s, color .15s, border-color .15s;
}
.btn-green{background:var(--green); color:#052e16;}
.btn-green:hover{background:var(--green-dark); color:#fff;}
.btn-red{background:transparent; color:var(--red); border:1px solid var(--red);}
.btn-red:hover{background:var(--red); color:#fff;}
.btn-ghost{background:transparent; color:var(--muted); border:1px solid var(--border);}
.btn-ghost:hover{color:var(--text); border-color:var(--muted);}

/* ---------- Flash messages ---------- */
.flash{
  background:rgba(34,197,94,.12); border:1px solid var(--green);
  color:#bbf7d0; border-radius:10px; padding:12px 16px; margin-bottom:18px;
  font-size:.92rem;
}

/* ---------- Admin split-screen ---------- */
.admin-wrap{display:flex; gap:20px; align-items:flex-start; margin-top:20px;}
.panel{background:var(--panel); border:1px solid var(--border); border-radius:12px;}
.admin-list{width:38%; max-height:calc(100vh - 160px); overflow-y:auto; padding:10px;}
.admin-review{width:62%; padding:22px; position:sticky; top:96px;}
.panel-head{
  font-size:.78rem; font-weight:700; letter-spacing:1.5px; text-transform:uppercase;
  color:var(--muted); padding:8px 10px 12px; border-bottom:1px solid var(--border);
  margin-bottom:10px;
}
.admin-review .panel-head{margin:0 0 16px; padding:0 0 12px;}
.pending-item{
  display:block; padding:12px 14px; border-radius:9px; margin-bottom:6px;
  border:1px solid transparent; transition:background .12s, border-color .12s;
}
.pending-item:hover{background:var(--panel-2);}
.pending-item.active{background:var(--panel-2); border-color:var(--green);}
.pi-title{font-weight:600; font-size:.95rem; line-height:1.35; margin-bottom:4px;}
.empty-small{color:var(--muted); font-size:.9rem; padding:14px;}

.orig-ref{
  background:var(--panel-2); border:1px solid var(--border); border-radius:10px;
  padding:14px 16px; margin-bottom:18px; font-size:.9rem;
}
.orig-label{
  color:var(--muted); font-size:.72rem; text-transform:uppercase;
  letter-spacing:1.5px; margin-bottom:6px;
}
.orig-ref strong{display:block; margin-bottom:6px; font-weight:600;}
.orig-ref p{color:var(--muted);}
form label{
  display:block; font-size:.8rem; font-weight:600; letter-spacing:.6px;
  text-transform:uppercase; color:var(--muted); margin:14px 0 6px;
}
form input[type=text], form textarea{
  width:100%; background:var(--bg); color:var(--text);
  border:1px solid var(--border); border-radius:9px;
  padding:12px 14px; font-size:1rem; font-family:inherit; line-height:1.5;
}
form input[type=text]:focus, form textarea:focus{
  outline:none; border-color:var(--green);
  box-shadow:0 0 0 3px rgba(34,197,94,.15);
}
form textarea{resize:vertical; min-height:160px;}
.actions{display:flex; gap:12px; margin-top:18px; flex-wrap:wrap;}
.delete-form{margin-top:14px; border-top:1px solid var(--border); padding-top:16px;}

/* ---------- Responsive ---------- */
@media (max-width:1024px){
  .grid{grid-template-columns:repeat(2, 1fr);}
}
@media (max-width:768px){
  .grid{grid-template-columns:1fr; gap:18px;}
  .hero{min-height:380px;}
  .hero-content{padding:24px 22px;}
  .admin-wrap{flex-direction:column;}
  .admin-list, .admin-review{width:100%;}
  .admin-list{max-height:42vh;}
  .admin-review{position:static;}
}
"""


# --------------------------------------------------------------------------- #
# Templates
# --------------------------------------------------------------------------- #

PUBLIC_TEMPLATE = """
<!doctype html>
<html lang="sr">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Sportske vesti &#8211; Sportski Portal</title>
  <style>{{ css|safe }}</style>
</head>
<body>
  {# Reusable article card; every card routes clicks through /click/<id>,
     which increments the view counter before redirecting to the source.
     `rank` (1-3) marks the most-read / trending cards. #}
  {% macro card(a, eager=false, rank=none) -%}
  <a class="card {% if rank %}trending{% endif %}"
     href="{{ url_for('track_click', article_id=a['id']) }}"
     target="_blank" rel="noopener noreferrer">
    <div class="card-media">
      <img src="{{ article_image(a) }}" alt="{{ a.translated_title }}"
           loading="{{ 'eager' if eager else 'lazy' }}"
           onerror="this.style.opacity='0'">
      <span class="chip">{{ category_label(a) }}</span>
      {% if rank %}
        <span class="badge-trending">&#128293; Naj&#269;itanije</span>
      {% elif a.priority == 1 %}
        <span class="badge-hot">&#9889;</span>
      {% endif %}
      {% if rank %}<span class="card-rank">{{ rank }}</span>{% endif %}
    </div>
    <div class="card-body">
      <h4>{{ a.translated_title }}</h4>
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
      <span class="topbar-tag">Najnovije sportske vesti</span>
    </div>
  </header>

  <main class="container">
    {% if hero or trending or football or basketball or south_america %}

      {% if hero %}
      <!-- SECTION: HERO / UDARNA VEST — newest high-priority, full width -->
      <div class="hero-head section-head">
        <h3><span class="emoji">&#9889;</span>UDARNA VEST</h3>
        <span class="line"></span>
      </div>
      <a class="hero"
         href="{{ url_for('track_click', article_id=hero['id']) }}"
         target="_blank" rel="noopener noreferrer">
        <img src="{{ article_image(hero) }}" alt="{{ hero.translated_title }}"
             loading="eager" onerror="this.style.display='none'">
        <div class="hero-overlay"></div>
        <div class="hero-content">
          <div class="hero-tags">
            <span class="badge-hot">&#9889; Udarna vest</span>
            <span class="chip">{{ category_label(hero) }}</span>
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
      <!-- SECTION: 🔥 NAJČITANIJE — top 3 by views -->
      <section class="grid-section">
        <div class="section-head">
          <h3><span class="emoji">&#128293;</span>NAJ&#268;ITANIJE</h3>
          <span class="line"></span>
        </div>
        <div class="grid">
          {% for a in trending %}{{ card(a, eager=(loop.index == 1), rank=loop.index) }}{% endfor %}
        </div>
      </section>
      {% endif %}

      {% if football %}
      <!-- SECTION: ⚽ DOMAĆI TEREN & EVROPSKI GIGANTI -->
      <section class="grid-section">
        <div class="section-head">
          <h3><span class="emoji">&#9917;</span>DOMA&#262;I TEREN &amp; EVROPSKI GIGANTI</h3>
          <span class="line"></span>
        </div>
        <div class="grid">
          {% for a in football %}{{ card(a) }}{% endfor %}
        </div>
      </section>
      {% endif %}

      {% if basketball %}
      <!-- SECTION: 🏀 KOŠARKA -->
      <section class="grid-section">
        <div class="section-head">
          <h3><span class="emoji">&#127936;</span>KO&#352;ARKA</h3>
          <span class="line"></span>
        </div>
        <div class="grid">
          {% for a in basketball %}{{ card(a) }}{% endfor %}
        </div>
      </section>
      {% endif %}

      {% if south_america %}
      <!-- SECTION: ✨ JUŽNOAMERIČKA MAGIJA (Gaučosi i Karijoke) -->
      <section class="grid-section">
        <div class="section-head">
          <h3><span class="emoji">&#10024;</span>JU&#381;NOAMERI&#268;KA MAGIJA <span class="sa-sub">(Gau&#269;osi i Karijoke)</span></h3>
          <span class="line"></span>
        </div>
        <div class="grid">
          {% for a in south_america %}{{ card(a) }}{% endfor %}
        </div>
      </section>
      {% endif %}

    {% else %}
      <div class="empty" style="margin-top:30px;">
        Jo&#353; uvek nema objavljenih vesti. Navratite uskoro!
      </div>
    {% endif %}
  </main>

  <footer class="container footer-text">
    &copy; Sportski Portal &#8211; Sports News Aggregator
  </footer>
</body>
</html>
"""

ADMIN_TEMPLATE = """
<!doctype html>
<html lang="sr">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Admin kontrola</title>
  <style>{{ css|safe }}</style>
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
      {% for message in messages %}
        <div class="flash" style="margin-top:20px;">{{ message }}</div>
      {% endfor %}
    {% endwith %}

    <div class="admin-wrap">
      <!-- LEFT: scrollable pending queue -->
      <aside class="admin-list">
        <div class="panel-head">Na &#269;ekanju ({{ pending|length }})</div>
        {% if pending %}
          {% for a in pending %}
          <a class="pending-item {% if selected and selected['id'] == a['id'] %}active{% endif %}"
             href="{{ url_for('admin', article_id=a['id']) }}">
            <div class="pi-title">
              {{ a.translated_title }}
              {% if a.priority == 1 %}<span class="badge-hot">&#9889;</span>{% endif %}
            </div>
            <div class="meta">{{ a.source }}</div>
          </a>
          {% endfor %}
        {% else %}
          <p class="empty-small">Sve prevedene vesti su obra&#273;ene.</p>
        {% endif %}
      </aside>

      <!-- RIGHT: review / edit area -->
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
          <input type="text" id="title" name="translated_title"
                 value="{{ selected.translated_title }}" required>

          <label for="summary">Sa&#382;etak / &#269;lanak (srpski)</label>
          <textarea id="summary" name="translated_summary" rows="10" required>{{ selected.translated_summary }}</textarea>

          <div class="actions">
            <button type="submit" class="btn btn-green">&#10003; Objavi vest</button>
          </div>
        </form>

        <form class="delete-form" method="post"
              action="{{ url_for('delete_article', article_id=selected.id) }}"
              onsubmit="return confirm('Obrisati ovu vest zauvek?');">
          <button type="submit" class="btn btn-red">&#128465; Obri&#353;i vest</button>
        </form>

        {% else %}
        <div class="empty">
          &larr; Izaberite vest sa leve liste da biste je pregledali,
          uredili i objavili.
        </div>
        {% endif %}
      </section>
    </div>
  </main>
</body>
</html>
"""


# --------------------------------------------------------------------------- #
# Routes
# --------------------------------------------------------------------------- #

@app.route("/")
def index():
    """
    Public homepage, split into exact semantic sections:
      - UDARNA VEST        : the single newest high-priority (priority=1) article
      - NAJČITANIJE        : the top 3 most-read articles by view count
      - DOMAĆI TEREN...    : football articles (European + local Serbian)
      - KOŠARKA            : basketball articles
      - JUŽNOAMERIČKA MAGIJA : South American (Argentine/Brazilian) football
    Each article appears in exactly one place on the page.
    """
    articles = get_db().execute(
        """
        SELECT id, source, original_title, original_summary, link,
               translated_title, translated_summary, published_date,
               priority, views
        FROM articles
        WHERE status = 'published'
        ORDER BY published_date DESC, id DESC
        """
    ).fetchall()

    # HERO / UDARNA VEST: the single newest high-priority article
    hero = next((a for a in articles if a["priority"] == 1), None)
    hero_id = hero["id"] if hero else None

    # 🔥 NAJČITANIJE: top 3 by views (newest first as the tie-breaker),
    # excluding the hero so it is not shown twice.
    trending = sorted(
        (a for a in articles if a["id"] != hero_id),
        key=lambda a: (a["views"] or 0, a["published_date"] or "", a["id"]),
        reverse=True,
    )[:3]

    # Everything not already featured (hero + trending) feeds the sport grids
    featured_ids = {hero_id} if hero_id is not None else set()
    featured_ids |= {a["id"] for a in trending}

    rest = [a for a in articles if a["id"] not in featured_ids]
    basketball = [a for a in rest if article_category(a) == "basketball"]

    # South American football gets its own specialized grid ("Gaučosi i Karijoke")
    south_america = [a for a in rest if is_south_america(a)]
    sa_ids = {a["id"] for a in south_america}
    football = [
        a for a in rest
        if article_category(a) == "football" and a["id"] not in sa_ids
    ]

    return render_template_string(
        PUBLIC_TEMPLATE,
        hero=hero, trending=trending,
        football=football, basketball=basketball,
        south_america=south_america,
        css=BASE_CSS,
    )


@app.route("/click/<int:article_id>")
def track_click(article_id: int):
    """
    Analytics click tracker: every card links here. It bumps the article's
    view count by 1, then immediately 302-redirects the reader to the
    original source link.
    """
    db = get_db()
    db.execute(
        "UPDATE articles SET views = views + 1 WHERE id = ?", (article_id,)
    )
    db.commit()

    row = db.execute(
        "SELECT link FROM articles WHERE id = ?", (article_id,)
    ).fetchone()
    if row and row["link"]:
        return redirect(row["link"], code=302)

    # Fallback: article missing / no source link -> back to the homepage
    return redirect(url_for("index"))


@app.route(ADMIN_PATH)
def admin():
    """Secret split-screen dashboard. ?article_id=<id> loads a story for review."""
    db = get_db()

    pending = db.execute(
        """
        SELECT id, source, translated_title, priority
        FROM articles
        WHERE status = 'pending' AND translated_title != ''
        ORDER BY priority DESC, published_date DESC, id DESC
        """
    ).fetchall()

    selected = None
    article_id = request.args.get("article_id", type=int)
    if article_id:
        selected = db.execute(
            "SELECT * FROM articles WHERE id = ?", (article_id,)
        ).fetchone()

    return render_template_string(
        ADMIN_TEMPLATE, pending=pending, selected=selected, css=BASE_CSS
    )


@app.post("/admin/publish/<int:article_id>")
def publish_article(article_id: int):
    """Save edited Serbian title/summary and mark the article as published."""
    title = (request.form.get("translated_title") or "").strip()
    summary = (request.form.get("translated_summary") or "").strip()

    if not title or not summary:
        flash("Naslov i sa&#382;etak ne smeju biti prazni.")
        return redirect(url_for("admin", article_id=article_id))

    db = get_db()
    db.execute(
        """
        UPDATE articles
        SET translated_title = ?, translated_summary = ?, status = 'published'
        WHERE id = ?
        """,
        (title, summary, article_id),
    )
    db.commit()
    flash(f"Vest #{article_id} je objavljena i sada je vidljiva na javnom sajtu.")
    return redirect(url_for("admin"))


@app.post("/admin/delete/<int:article_id>")
def delete_article(article_id: int):
    """Permanently delete an article."""
    db = get_db()
    db.execute("DELETE FROM articles WHERE id = ?", (article_id,))
    db.commit()
    flash(f"Vest #{article_id} je obrisana.")
    return redirect(url_for("admin"))


# --------------------------------------------------------------------------- #
# Entrypoint
# --------------------------------------------------------------------------- #

init_db()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=False)
