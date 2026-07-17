
#!/usr/bin/env python3
"""
site_cloner.py — crawl a website and save an offline-browsable mirror.

Crawls same-domain pages (BFS), downloads HTML/CSS/JS/images/fonts,
then rewrites all links to relative local paths so the archive works
entirely offline (open <out>/index.html in a browser).

Usage:
    python site_cloner.py https://example.com
    python site_cloner.py https://example.com -o mirror --max-pages 200 --delay 0.5

Deps:
    pip install -r ./requirements.txt
"""

import argparse
import hashlib
import os
import posixpath
import re
import sys
import time
from collections import deque
from urllib import robotparser
from urllib.parse import urljoin, urlsplit, urlunsplit, unquote, quote
import requests
from bs4 import BeautifulSoup


HTML_TYPES = {"text/html", "application/xhtml+xml"}
CSS_URL_RE = re.compile(r"""url\(\s*(['"]?)([^'")]+)\1\s*\)""", re.IGNORECASE)
CSS_IMPORT_RE = re.compile(r"""@import\s+(['"])([^'"]+)\1""", re.IGNORECASE)
BAD_PATH_CHARS = re.compile(r'[<>:"|?*\x00-\x1f]')

# (tag, attr) pairs to extract/rewrite. a/area hrefs are crawled as pages;
# everything else is treated as an asset.
TAG_ATTRS = [
    ("a", "href"), ("area", "href"), ("link", "href"),
    ("script", "src"), ("img", "src"), ("img", "srcset"),
    ("source", "src"), ("source", "srcset"),
    ("video", "src"), ("video", "poster"), ("audio", "src"),
    ("iframe", "src"), ("embed", "src"), ("input", "src"),
]

# <link rel=...> values that point at pages/metadata we don't need to fetch
SKIP_LINK_RELS = {"canonical", "alternate", "dns-prefetch", "preconnect", "prefetch"}

SKIP_SCHEMES = ("data:", "mailto:", "javascript:", "tel:", "blob:", "about:")


class SiteCloner:
    def __init__(self, start_url, out_dir, max_pages=300, max_depth=8,
                 max_files=10000, delay=0.3, timeout=20,
                 external_assets=True, respect_robots=True,
                 user_agent="site-cloner/1.0 (+offline mirror)"):
        if not urlsplit(start_url).scheme:
            start_url = "https://" + start_url
        self.start_url = self.normalize(start_url)
        self.out_dir = out_dir
        self.max_pages = max_pages
        self.max_depth = max_depth
        self.max_files = max_files
        self.delay = delay
        self.timeout = timeout
        self.external_assets = external_assets

        self.session = requests.Session()
        self.session.headers["User-Agent"] = user_agent
        self.session.verify = False

        self.url_to_path = {}       # normalized url -> local relpath (posix)
        self.used_paths = set()
        self.html_pages = []        # (relpath, url) for pass-2 rewriting
        self.css_files = []         # (relpath, url)
        self.failed = []

        self.robots = None
        if respect_robots:
            rp = robotparser.RobotFileParser()
            try:
                rp.set_url(urljoin(self.start_url, "/robots.txt"))
                rp.read()
                self.robots = rp
            except Exception:
                pass

    # ---------- URL helpers ----------

    @staticmethod
    def normalize(url):
        s = urlsplit(url)
        return urlunsplit((s.scheme, s.netloc, s.path, s.query, ""))

    @staticmethod
    def _host(url):
        h = urlsplit(url).netloc.lower()
        return h[4:] if h.startswith("www.") else h

    def _same_site(self, url):
        return self._host(url) == self._host(self.start_url)

    def _robots_ok(self, url):
        if self.robots is None or not self._same_site(url):
            return True
        try:
            return self.robots.can_fetch(self.session.headers["User-Agent"], url)
        except Exception:
            return True

    # ---------- URL -> local path ----------

    @staticmethod
    def _sanitize(comp):
        return (BAD_PATH_CHARS.sub("_", comp)[:150]) or "_"

    def local_path_for(self, url, content_type):
        s = urlsplit(url)
        path = unquote(s.path)
        if not path or path.endswith("/"):
            path += "index.html"
        comps = [self._sanitize(c) for c in path.split("/") if c not in ("", ".", "..")]
        if not comps:
            comps = ["index.html"]

        stem, ext = posixpath.splitext(comps[-1])
        ct = (content_type or "").split(";")[0].strip().lower()
        # Force browser-friendly extensions for file:// viewing
        if ct in HTML_TYPES and ext.lower() not in (".html", ".htm"):
            stem, ext = comps[-1], ".html"
        elif ct == "text/css" and ext.lower() != ".css":
            stem, ext = comps[-1], ".css"
        if s.query:
            stem += "_" + hashlib.md5(s.query.encode()).hexdigest()[:8]
        comps[-1] = stem + ext

        if self._same_site(url):
            rel = posixpath.join(*comps)
        else:
            rel = posixpath.join("_external", self._sanitize(s.netloc.lower()), *comps)

        if rel in self.used_paths:
            st, ex = posixpath.splitext(rel)
            rel = f"{st}_{hashlib.md5(url.encode()).hexdigest()[:8]}{ex}"
        self.used_paths.add(rel)
        return rel

    def _save(self, rel, data):
        full = os.path.join(self.out_dir, *rel.split("/"))
        try:
            os.makedirs(os.path.dirname(full), exist_ok=True)
            if os.path.isdir(full):
                raise OSError("path is a directory")
        except OSError:
            st, ex = posixpath.splitext(rel)
            rel = f"{st}_{hashlib.md5(rel.encode()).hexdigest()[:6]}{ex}"
            full = os.path.join(self.out_dir, *rel.split("/"))
            os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "wb") as f:
            f.write(data)
        return rel

    # ---------- crawl (pass 1) ----------

    @staticmethod
    def _srcset_urls(val):
        return [p.strip().split()[0] for p in val.split(",") if p.strip()]

    def _enqueue(self, q, seen, url, depth, is_page):
        url = url.strip()
        if not url or url.startswith(SKIP_SCHEMES) or url.startswith("#"):
            return
        n = self.normalize(url)
        if urlsplit(n).scheme not in ("http", "https") or n in seen:
            return
        if is_page and (not self._same_site(n) or depth > self.max_depth):
            return
        if not is_page and not self._same_site(n) and not self.external_assets:
            return
        seen.add(n)
        q.append((n, depth, is_page))

    def _extract(self, q, seen, soup, page_url, depth):
        base_tag = soup.find("base", href=True)
        base = urljoin(page_url, base_tag["href"]) if base_tag else page_url

        for tag, attr in TAG_ATTRS:
            for el in soup.find_all(tag):
                val = el.get(attr)
                if not val:
                    continue
                if tag == "link":
                    rels = {r.lower() for r in (el.get("rel") or [])}
                    if rels & SKIP_LINK_RELS:
                        continue
                if attr == "srcset":
                    for u in self._srcset_urls(val):
                        self._enqueue(q, seen, urljoin(base, u), depth + 1, False)
                else:
                    is_page = tag in ("a", "area")
                    self._enqueue(q, seen, urljoin(base, val), depth + 1, is_page)

        # url(...) inside style="" attributes and <style> blocks
        for el in soup.find_all(style=True):
            for m in CSS_URL_RE.finditer(el["style"]):
                self._enqueue(q, seen, urljoin(base, m.group(2)), depth + 1, False)
        for el in soup.find_all("style"):
            for m in CSS_URL_RE.finditer(el.get_text()):
                self._enqueue(q, seen, urljoin(base, m.group(2)), depth + 1, False)

    def _extract_css(self, q, seen, css_text, css_url, depth):
        for regex in (CSS_URL_RE, CSS_IMPORT_RE):
            for m in regex.finditer(css_text):
                self._enqueue(q, seen, urljoin(css_url, m.group(2)), depth + 1, False)

    def crawl(self):
        q = deque()
        seen = set()
        self._enqueue(q, seen, self.start_url, 0, True)
        pages = assets = 0

        while q:
            if len(self.url_to_path) >= self.max_files:
                print("[!] max-files limit reached, stopping crawl")
                break
            url, depth, is_page = q.popleft()
            if is_page and pages >= self.max_pages:
                continue
            if not self._robots_ok(url):
                continue

            try:
                resp = self.session.get(url, timeout=self.timeout)
                resp.raise_for_status()
            except Exception as e:
                self.failed.append((url, str(e)))
                continue
            finally:
                time.sleep(self.delay)

            ct = resp.headers.get("Content-Type", "")
            base_ct = ct.split(";")[0].strip().lower()
            rel = self.local_path_for(url, ct)
            rel = self._save(rel, resp.content)
            self.url_to_path[url] = rel
            self.url_to_path.setdefault(self.normalize(resp.url), rel)  # redirects

            if base_ct in HTML_TYPES:
                pages += 1
                print(f"[page {pages:>4}] {url}")
                self.html_pages.append((rel, self.normalize(resp.url)))
                if is_page:
                    soup = BeautifulSoup(resp.content, "html.parser")
                    self._extract(q, seen, soup, self.normalize(resp.url), depth)
            else:
                assets += 1
                if base_ct == "text/css" or rel.endswith(".css"):
                    self.css_files.append((rel, self.normalize(resp.url)))
                    self._extract_css(q, seen,
                                      resp.content.decode("utf-8", "replace"),
                                      self.normalize(resp.url), depth)

        print(f"\nDownloaded {pages} pages, {assets} assets "
              f"({len(self.failed)} failures)")

    # ---------- rewrite links (pass 2) ----------

    def _to_local(self, base_url, ref, from_rel):
        """Return rewritten ref, or None to leave the attribute untouched."""
        ref = (ref or "").strip()
        if not ref or ref.startswith(SKIP_SCHEMES) or ref.startswith("#"):
            return None
        abs_url = urljoin(base_url, ref)
        frag = ""
        if "#" in abs_url:
            abs_url, _, frag = abs_url.partition("#")
            frag = "#" + frag
        target = self.url_to_path.get(self.normalize(abs_url))
        if target is None:
            # Not archived: absolutize so the link still works online
            return abs_url + frag if urlsplit(abs_url).scheme in ("http", "https") else None
        relpath = posixpath.relpath(target, posixpath.dirname(from_rel) or ".")
        return quote(relpath) + frag

    def _rewrite_css_text(self, text, base_url, from_rel):
        def sub_url(m):
            new = self._to_local(base_url, m.group(2), from_rel)
            return f"url({m.group(1)}{new}{m.group(1)})" if new else m.group(0)

        def sub_import(m):
            new = self._to_local(base_url, m.group(2), from_rel)
            return f"@import {m.group(1)}{new}{m.group(1)}" if new else m.group(0)

        return CSS_IMPORT_RE.sub(sub_import, CSS_URL_RE.sub(sub_url, text))

    def _rewrite_srcset(self, val, base_url, from_rel):
        parts = []
        for part in val.split(","):
            bits = part.strip().split()
            if bits:
                new = self._to_local(base_url, bits[0], from_rel)
                if new:
                    bits[0] = new
                parts.append(" ".join(bits))
        return ", ".join(parts)

    def rewrite(self):
        for rel, url in self.html_pages:
            full = os.path.join(self.out_dir, *rel.split("/"))
            with open(full, "rb") as f:
                soup = BeautifulSoup(f.read(), "html.parser")

            base_tag = soup.find("base", href=True)
            base_url = urljoin(url, base_tag["href"]) if base_tag else url
            if base_tag:
                base_tag.decompose()  # <base> breaks relative offline links

            for tag, attr in TAG_ATTRS:
                for el in soup.find_all(tag):
                    val = el.get(attr)
                    if not val:
                        continue
                    if attr == "srcset":
                        el[attr] = self._rewrite_srcset(val, base_url, rel)
                    else:
                        new = self._to_local(base_url, val, rel)
                        if new:
                            el[attr] = new

            # SRI/CORS attributes can block file:// loads
            for el in soup.find_all(("link", "script")):
                el.attrs.pop("integrity", None)
                el.attrs.pop("crossorigin", None)

            for el in soup.find_all(style=True):
                el["style"] = self._rewrite_css_text(el["style"], base_url, rel)
            for el in soup.find_all("style"):
                if el.string is not None:
                    el.string = self._rewrite_css_text(el.string, base_url, rel)

            with open(full, "wb") as f:
                f.write(soup.encode("utf-8"))

        for rel, url in self.css_files:
            full = os.path.join(self.out_dir, *rel.split("/"))
            with open(full, "rb") as f:
                text = f.read().decode("utf-8", "replace")
            with open(full, "wb") as f:
                f.write(self._rewrite_css_text(text, url, rel).encode("utf-8"))

        print(f"Rewrote links in {len(self.html_pages)} HTML "
              f"and {len(self.css_files)} CSS files")

    def run(self):
        self.crawl()
        self.rewrite()
        entry = self.url_to_path.get(self.start_url)
        if entry:
            print(f"\nDone. Open: {os.path.join(self.out_dir, *entry.split('/'))}")
        if self.failed:
            print("Failures:")
            for u, err in self.failed[:20]:
                print(f"  {u}  ({err})")


def main():
    ap = argparse.ArgumentParser(description="Clone a website for offline browsing")
    ap.add_argument("url", help="start URL, e.g. https://example.com")
    ap.add_argument("-o", "--output", help="output directory (default: <host>_mirror)")
    ap.add_argument("--max-pages", type=int, default=300)
    ap.add_argument("--max-depth", type=int, default=8)
    ap.add_argument("--max-files", type=int, default=10000)
    ap.add_argument("--delay", type=float, default=0.3, help="seconds between requests")
    ap.add_argument("--timeout", type=float, default=20)
    ap.add_argument("--no-external-assets", action="store_true",
                    help="skip CDN/third-party images, CSS, JS")
    ap.add_argument("--ignore-robots", action="store_true")
    ap.add_argument("--user-agent", default="site-cloner/1.0 (+offline mirror)")
    args = ap.parse_args()

    out = args.output or (SiteCloner._host(args.url if "://" in args.url
                                           else "https://" + args.url) + "_mirror")
    cloner = SiteCloner(
        args.url, out,
        max_pages=args.max_pages, max_depth=args.max_depth,
        max_files=args.max_files, delay=args.delay, timeout=args.timeout,
        external_assets=not args.no_external_assets,
        respect_robots=not args.ignore_robots,
        user_agent=args.user_agent,
    )
    try:
        cloner.run()
    except KeyboardInterrupt:
        print("\nInterrupted — rewriting links for what was downloaded...")
        cloner.rewrite()
        sys.exit(1)


if __name__ == "__main__":
    main()
