#!/usr/bin/env python3
"""
Account-level social ingestion for the Dubai Property Signals console.

Polls named YouTube channels, subreddits and RSS/Atom feeds, keeps only
property-relevant items, and writes social.json for the morning sweep to read.

Standard library only — no pip install, so CI stays fast and nothing can rot.

Usage:
    python3 collect.py              # normal run, writes social.json + state.json
    python3 collect.py --dry-run    # fetch and report, write nothing
    python3 collect.py --validate   # check an existing social.json against the schema
"""

import argparse
import json
import os
import re
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "social.json")
STATE = os.path.join(HERE, "state.json")
SOURCES = os.path.join(HERE, "sources.json")

UA = ("DubaiPropertySignals/2.0 (+https://github.com/) "
      "media monitoring bot; respects robots and rate limits")

KEEP = 250              # items retained in social.json
MAX_AGE_DAYS = 45       # drop anything older than this
PER_SOURCE_CAP = 40     # no single account can flood a run
SEEN_TTL_DAYS = 120     # how long an id stays in the dedupe memory
HTTP_TIMEOUT = 30

ARABIC = re.compile(r"[؀-ۿ]")

# --------------------------------------------------------------- config


DEFAULT_SOURCES = {
    "youtube": [
        "@AllsoppandAllsopp",
        "@fam-properties",
        "@DrivenProperties",
        "@BetterhomesUAE",
    ],
    "subreddits": ["dubai", "UAE", "DubaiRealEstate", "expats"],
    "rss": [
        "https://masdarak.com/feed/",
        "https://news.google.com/rss/search?q=%22Dubai+Land+Department%22&hl=en-AE&gl=AE&ceid=AE:en",
        "https://news.google.com/rss/search?q=%D8%AF%D8%A7%D8%A6%D8%B1%D8%A9+%D8%A7%D9%84%D8%A3%D8%B1%D8%A7%D8%B6%D9%8A+%D9%88%D8%A7%D9%84%D8%A3%D9%85%D9%84%D8%A7%D9%83&hl=ar&gl=AE&ceid=AE:ar",
    ],
    "keywords": [
        "property", "real estate", "realestate", "rent", "rental", "landlord",
        "tenant", "mortgage", "off-plan", "offplan", "freehold", "villa",
        "apartment", "developer", "dld", "rera", "ejari", "service charge",
        "handover", "escrow", "title deed", "golden visa",
        "عقار", "عقارات", "إيجار", "ايجار", "تملك", "المطور", "رهن", "فيلا", "شقة",
    ],
}


def load_sources():
    """sources.json wins if present, so the watchlist is editable without touching code."""
    if os.path.exists(SOURCES):
        try:
            with open(SOURCES, encoding="utf-8") as fh:
                cfg = json.load(fh) or {}
            merged = dict(DEFAULT_SOURCES)
            for key in merged:
                if isinstance(cfg.get(key), list) and cfg[key]:
                    merged[key] = cfg[key]
            return merged
        except Exception as exc:
            log("  ! sources.json unreadable (%s) — using built-in list" % exc.__class__.__name__)
    return dict(DEFAULT_SOURCES)


# --------------------------------------------------------------- plumbing


def log(msg):
    print(msg, file=sys.stderr, flush=True)


def today():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def now_iso():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


class Fetcher:
    """HTTP with retries, Retry-After support and conditional GETs."""

    def __init__(self, cache):
        self.cache = cache if isinstance(cache, dict) else {}

    def get(self, url, accept=None, tries=3, conditional=False):
        headers = {
            "User-Agent": UA,
            "Accept": accept or "*/*",
            "Accept-Language": "en,ar;q=0.8",
        }
        entry = self.cache.get(url) or {}
        if conditional:
            if entry.get("etag"):
                headers["If-None-Match"] = entry["etag"]
            if entry.get("modified"):
                headers["If-Modified-Since"] = entry["modified"]

        for attempt in range(tries):
            try:
                req = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as resp:
                    body = resp.read().decode("utf-8", "replace")
                    if conditional:
                        self.cache[url] = {
                            "etag": resp.headers.get("ETag") or entry.get("etag"),
                            "modified": resp.headers.get("Last-Modified") or entry.get("modified"),
                        }
                    return body, None
            except urllib.error.HTTPError as exc:
                if exc.code == 304:
                    return "", "not-modified"
                if exc.code in (429, 500, 502, 503, 504) and attempt < tries - 1:
                    wait = 3 * (attempt + 1)
                    retry_after = exc.headers.get("Retry-After") if exc.headers else None
                    if retry_after and str(retry_after).isdigit():
                        wait = min(int(retry_after), 30)
                    time.sleep(wait)
                    continue
                return None, "HTTP %s" % exc.code
            except Exception as exc:
                if attempt < tries - 1:
                    time.sleep(2 * (attempt + 1))
                    continue
                return None, exc.__class__.__name__
        return None, "unreachable"


def build_matcher(keywords):
    """Word-boundary match for Latin terms so 'rent' stops matching 'current'.
    Arabic is matched as a substring because of clitics and prefixes."""
    latin, arabic = [], []
    for kw in keywords:
        (arabic if ARABIC.search(kw) else latin).append(kw.lower())
    pattern = None
    if latin:
        pattern = re.compile(
            r"(?<![a-z])(" + "|".join(re.escape(k) for k in latin) + r")(?![a-z])",
            re.IGNORECASE)

    def relevant(*fields):
        hay = " ".join(f for f in fields if f)
        low = hay.lower()
        if pattern and pattern.search(low):
            return True
        return any(k in hay for k in arabic)

    return relevant


def iso_day(value):
    """Normalise assorted date shapes to YYYY-MM-DD. None when unknown."""
    if isinstance(value, (int, float)):
        return datetime.fromtimestamp(value, timezone.utc).strftime("%Y-%m-%d")
    if not value:
        return None
    s = str(value).strip()
    m = re.match(r"(\d{4})-(\d{2})-(\d{2})", s)
    if m:
        return m.group(0)
    for fmt in ("%a, %d %b %Y %H:%M:%S %z", "%a, %d %b %Y %H:%M:%S %Z",
                "%d %b %Y %H:%M:%S %z", "%a, %d %b %Y %H:%M %z"):
        try:
            return datetime.strptime(s, fmt).strftime("%Y-%m-%d")
        except ValueError:
            pass
    return None


def too_old(day):
    if not day:
        return False
    try:
        d = datetime.strptime(day, "%Y-%m-%d").replace(tzinfo=timezone.utc)
    except ValueError:
        return False
    return (datetime.now(timezone.utc) - d).days > MAX_AGE_DAYS


def language_of(*fields):
    text = " ".join(f for f in fields if f)
    if not text:
        return "en"
    arabic_chars = len(ARABIC.findall(text))
    return "ar" if arabic_chars >= max(4, len(text) * 0.08) else "en"


def make_item(**kw):
    """One shape for every source, so the console never sees a surprise field."""
    day = kw.get("date")
    approx = False
    if not day:                      # unknown publication date: stamp it, flag it
        day, approx = today(), True
    return {
        "id": kw["id"],
        "platform": kw["platform"],
        "channel": kw["channel"],
        "stream": kw.get("stream", "social"),
        "account": kw.get("account", ""),
        "title": kw["title"],
        "text": (kw.get("text") or "")[:600],
        "url": kw["url"],
        "date": day,
        "dateApprox": approx,
        "language": language_of(kw.get("title"), kw.get("text")),
        "engagement": kw.get("engagement", ""),
        "firstSeenAt": now_iso(),
    }


# --------------------------------------------------------------- youtube

CHANNEL_ID_RE = re.compile(r'"(?:channelId|externalId)"\s*:\s*"(UC[\w-]{22})"')
ATOM = "{http://www.w3.org/2005/Atom}"
MEDIA = "{http://search.yahoo.com/mrss/}"
YT = "{http://www.youtube.com/xml/schemas/2015}"


def resolve_channel(entry, fetcher, cache):
    """Turn a handle or URL into a UC... channel id, caching both hits and misses."""
    entry = entry.strip()
    if re.fullmatch(r"UC[\w-]{22}", entry):
        return entry, None

    hit = cache.get(entry)
    if isinstance(hit, dict):
        if hit.get("id"):
            return hit["id"], None
        # negative cache: stop hammering a bad handle every six hours
        if hit.get("checkedAt", "") > (datetime.now(timezone.utc) - timedelta(days=7)).strftime("%Y-%m-%d"):
            return None, "unresolved (cached)"
    elif isinstance(hit, str) and hit:
        return hit, None

    handle = entry
    if handle.startswith("http"):
        m = re.search(r"/(?:@|channel/|c/|user/)([^/?#]+)", handle)
        handle = m.group(1) if m else handle
    handle = handle.lstrip("@")
    quoted = urllib.parse.quote(handle)

    for url in ("https://www.youtube.com/@%s/videos" % quoted,
                "https://www.youtube.com/@%s" % quoted,
                "https://www.youtube.com/c/%s" % quoted,
                "https://www.youtube.com/user/%s" % quoted):
        html, err = fetcher.get(url, accept="text/html")
        if not html:
            continue
        m = CHANNEL_ID_RE.search(html)
        if m:
            cache[entry] = {"id": m.group(1), "checkedAt": today()}
            log("  resolved %s -> %s" % (entry, m.group(1)))
            return m.group(1), None

    cache[entry] = {"id": None, "checkedAt": today()}
    return None, "could not resolve handle"


def poll_youtube(cfg, fetcher, relevant, cache, report):
    out = []
    for entry in cfg["youtube"]:
        cid, err = resolve_channel(entry, fetcher, cache)
        if not cid:
            report.append({"source": "YouTube %s" % entry, "ok": False, "items": 0, "error": err})
            log("  ! %s: %s" % (entry, err))
            continue
        xml, err = fetcher.get(
            "https://www.youtube.com/feeds/videos.xml?channel_id=" + cid,
            accept="application/atom+xml", conditional=True)
        if err == "not-modified":
            report.append({"source": "YouTube %s" % entry, "ok": True, "items": 0, "error": "unchanged"})
            continue
        if not xml:
            report.append({"source": "YouTube %s" % entry, "ok": False, "items": 0, "error": err})
            continue
        try:
            root = ET.fromstring(xml)
        except ET.ParseError:
            report.append({"source": "YouTube %s" % entry, "ok": False, "items": 0, "error": "unparseable feed"})
            continue

        author = (root.findtext(ATOM + "title") or entry).strip()
        kept = 0
        for e in root.findall(ATOM + "entry")[:PER_SOURCE_CAP]:
            title = (e.findtext(ATOM + "title") or "").strip()
            vid = (e.findtext(YT + "videoId") or "").strip()
            link_el = e.find(ATOM + "link")
            url = link_el.get("href") if link_el is not None else ""
            day = iso_day(e.findtext(ATOM + "published"))
            group = e.find(MEDIA + "group")
            desc = group.findtext(MEDIA + "description") if group is not None else ""
            views = ""
            if group is not None:
                comm = group.find(MEDIA + "community")
                stats = comm.find(MEDIA + "statistics") if comm is not None else None
                if stats is not None and stats.get("views"):
                    try:
                        views = "{:,} views".format(int(stats.get("views")))
                    except (TypeError, ValueError):
                        views = "%s views" % stats.get("views")
            if not title or not url or too_old(day) or not relevant(title, desc):
                continue
            out.append(make_item(id="yt:" + (vid or url), platform="YouTube", channel="YouTube",
                                 account=author, title=title, text=desc, url=url,
                                 date=day, engagement=views))
            kept += 1
        report.append({"source": "YouTube %s" % author, "ok": True, "items": kept, "error": None})
    return out


# --------------------------------------------------------------- reddit


def poll_reddit(cfg, fetcher, relevant, report):
    """Reddit blocks datacenter IPs hard. Try the RSS feed first (lighter, less
    often blocked), fall back to the JSON listing, and report the block plainly
    rather than pretending the subreddit was quiet."""
    out = []
    for sub in cfg["subreddits"]:
        quoted = urllib.parse.quote(sub)
        kept, err = 0, None

        raw, err = fetcher.get("https://www.reddit.com/r/%s/new/.rss?limit=50" % quoted,
                               accept="application/atom+xml")
        parsed = []
        if raw:
            try:
                root = ET.fromstring(raw)
                for e in root.findall(ATOM + "entry")[:PER_SOURCE_CAP]:
                    link_el = e.find(ATOM + "link")
                    parsed.append({
                        "id": (e.findtext(ATOM + "id") or "").split("/")[-1],
                        "title": (e.findtext(ATOM + "title") or "").strip(),
                        "body": re.sub(r"<[^>]+>", " ", e.findtext(ATOM + "content") or "")[:600],
                        "url": link_el.get("href") if link_el is not None else "",
                        "day": iso_day(e.findtext(ATOM + "published") or e.findtext(ATOM + "updated")),
                        "engagement": "",
                    })
            except ET.ParseError:
                parsed = []

        if not parsed:
            raw, err2 = fetcher.get("https://www.reddit.com/r/%s/new.json?limit=100" % quoted,
                                    accept="application/json")
            err = err or err2
            if raw:
                try:
                    data = json.loads(raw)
                    for c in (data.get("data") or {}).get("children") or []:
                        d = c.get("data") or {}
                        parsed.append({
                            "id": d.get("id") or "",
                            "title": (d.get("title") or "").strip(),
                            "body": (d.get("selftext") or "")[:600],
                            "url": "https://www.reddit.com" + (d.get("permalink") or ""),
                            "day": iso_day(d.get("created_utc")),
                            "engagement": "%s upvotes · %s comments" % (d.get("score", 0), d.get("num_comments", 0)),
                        })
                except json.JSONDecodeError:
                    err = err or "blocked (non-JSON response)"

        for p in parsed[:PER_SOURCE_CAP]:
            if not p["title"] or not p["url"] or too_old(p["day"]):
                continue
            if not relevant(p["title"], p["body"]):
                continue
            out.append(make_item(id="rd:" + (p["id"] or p["url"]), platform="Reddit", channel="Reddit",
                                 account="r/" + sub, title=p["title"], text=p["body"],
                                 url=p["url"], date=p["day"], engagement=p["engagement"]))
            kept += 1

        ok = bool(parsed)
        report.append({"source": "r/" + sub, "ok": ok, "items": kept,
                       "error": None if ok else (err or "no response")})
        if not ok:
            log("  ! r/%s unavailable: %s" % (sub, err or "no response"))
        time.sleep(1.5)  # be polite
    return out


# --------------------------------------------------------------- rss


def text_of(el, *names):
    for n in names:
        v = el.findtext(n)
        if v:
            return v.strip()
    return ""


def poll_rss(cfg, fetcher, relevant, report):
    out = []
    for feed in cfg["rss"]:
        xml, err = fetcher.get(feed, accept="application/rss+xml, application/xml", conditional=True)
        if err == "not-modified":
            report.append({"source": feed, "ok": True, "items": 0, "error": "unchanged"})
            continue
        if not xml:
            report.append({"source": feed, "ok": False, "items": 0, "error": err})
            log("  ! feed failed: %s (%s)" % (feed, err))
            continue
        try:
            root = ET.fromstring(xml)
        except ET.ParseError:
            report.append({"source": feed, "ok": False, "items": 0, "error": "unparseable"})
            continue

        site = (root.findtext("./channel/title") or root.findtext(ATOM + "title") or feed).strip()
        nodes = root.findall("./channel/item") or root.findall(ATOM + "entry")
        kept = 0
        for it in nodes[:PER_SOURCE_CAP]:
            title = text_of(it, "title", ATOM + "title")
            link = text_of(it, "link")
            if not link:
                le = it.find(ATOM + "link")
                link = le.get("href") if le is not None else text_of(it, "guid")
            desc = re.sub(r"<[^>]+>", " ", text_of(it, "description", ATOM + "summary", ATOM + "content"))[:600]
            day = iso_day(text_of(it, "pubDate", ATOM + "published", ATOM + "updated"))
            if not title or not link or too_old(day) or not relevant(title, desc):
                continue
            out.append(make_item(id="rs:" + link, platform="RSS", channel="News", stream="news",
                                 account=site, title=title, text=desc, url=link,
                                 date=day, engagement=""))
            kept += 1
        report.append({"source": site, "ok": True, "items": kept, "error": None})
    return out


# --------------------------------------------------------------- state


def load_json(path, default):
    if not os.path.exists(path):
        return default
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh) or default
    except Exception:
        return default


def write_json_atomic(path, payload):
    """Never leave a half-written file if the runner is killed mid-write."""
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(path), suffix=".tmp")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, indent=1)
            fh.write("\n")
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp, path)
    except Exception:
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise


def prune_seen(seen):
    """Age out the dedupe memory by date, not alphabetically.
    The old lexicographic trim silently evicted every Reddit id first."""
    cutoff = (datetime.now(timezone.utc) - timedelta(days=SEEN_TTL_DAYS)).strftime("%Y-%m-%d")
    return {k: v for k, v in seen.items() if (v or "") >= cutoff}


SCHEMA_KEYS = {"id", "platform", "channel", "stream", "account", "title", "text",
               "url", "date", "dateApprox", "language", "engagement", "firstSeenAt"}


def validate(path):
    doc = load_json(path, None)
    if not doc:
        log("validate: %s missing or unreadable" % path)
        return 1
    problems = []
    for i, item in enumerate(doc.get("items") or []):
        missing = SCHEMA_KEYS - set(item)
        if missing:
            problems.append("item %d missing %s" % (i, ", ".join(sorted(missing))))
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", item.get("date") or ""):
            problems.append("item %d bad date %r" % (i, item.get("date")))
        if item.get("stream") not in ("social", "news"):
            problems.append("item %d bad stream %r" % (i, item.get("stream")))
    if problems:
        for p in problems[:20]:
            log("  x " + p)
        log("validate: %d problem(s)" % len(problems))
        return 1
    log("validate: %d items, schema clean" % len(doc.get("items") or []))
    return 0


# --------------------------------------------------------------- main


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true", help="fetch and report, write nothing")
    ap.add_argument("--validate", action="store_true", help="check existing social.json and exit")
    args = ap.parse_args()

    if args.validate:
        return validate(OUT)

    cfg = load_sources()
    relevant = build_matcher(cfg["keywords"])

    state = load_json(STATE, {})
    channel_cache = state.get("channelIds") or {}
    http_cache = state.get("http") or {}
    seen = state.get("seen") or {}
    if isinstance(seen, list):                     # migrate the old list format
        seen = {sid: today() for sid in seen}

    fetcher = Fetcher(http_cache)
    report = []

    log("YouTube…")
    items = poll_youtube(cfg, fetcher, relevant, channel_cache, report)
    log("Reddit…")
    items += poll_reddit(cfg, fetcher, relevant, report)
    log("RSS…")
    items += poll_rss(cfg, fetcher, relevant, report)

    fresh = [i for i in items if i["id"] not in seen]
    ok_sources = sum(1 for r in report if r["ok"])
    log("collected %d items, %d new, %d/%d sources ok" % (len(items), len(fresh), ok_sources, len(report)))

    previous = (load_json(OUT, {}) or {}).get("items") or []
    merged, keys = [], set()
    for i in fresh + previous:
        if i.get("id") in keys:
            continue
        keys.add(i["id"])
        merged.append(i)
    merged.sort(key=lambda x: (x.get("date") or "", x.get("firstSeenAt") or ""), reverse=True)
    merged = merged[:KEEP]

    payload = {
        "generatedAt": now_iso(),
        "newThisRun": len(fresh),
        "sourcesOk": ok_sources,
        "sourcesTotal": len(report),
        "counts": {
            "youtube": sum(1 for i in merged if i["platform"] == "YouTube"),
            "reddit": sum(1 for i in merged if i["platform"] == "Reddit"),
            "rss": sum(1 for i in merged if i["platform"] == "RSS"),
        },
        "sources": report,
        "items": merged,
    }

    if args.dry_run:
        log(json.dumps({k: v for k, v in payload.items() if k != "items"}, ensure_ascii=False, indent=1))
        log("dry run: nothing written")
        return 0

    write_json_atomic(OUT, payload)

    stamp = today()
    for i in merged:
        seen[i["id"]] = stamp
    write_json_atomic(STATE, {
        "channelIds": channel_cache,
        "http": http_cache,
        "seen": prune_seen(seen),
    })

    log("wrote %s (%d items)" % (OUT, len(merged)))

    # Fail the job when every source failed, so GitHub emails you instead of
    # committing an empty file in silence. A partial failure is not fatal.
    if report and ok_sources == 0:
        log("ERROR: every source failed this run")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
