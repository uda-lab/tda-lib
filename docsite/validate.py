"""Offline checks of the complete rendered site, including raw HTML links."""
from __future__ import annotations

from html.parser import HTMLParser
from pathlib import Path
import re
from urllib.parse import unquote, urljoin, urlsplit

PREFIX = "/tda-lib/"
ORIGIN = "http://preview.invalid"
# Must match docsite/mkdocs.yml's site_url. The readthedocs theme emits exactly
# one absolute external href per page, <link rel="canonical">, derived from it;
# every other href/src must resolve under PREFIX, so that one tag is checked
# against this expected self-reference instead of being treated as a resource.
SITE_URL = "https://uda-lab.github.io/tda-lib/"


class Page(HTMLParser):
    def __init__(self, text: str):
        super().__init__()
        self.ids = set()
        self.links = []
        self.canonical = None
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        if tag == "a" and "name" in attrs:
            self.ids.add(attrs["name"])
        if tag == "link" and attrs.get("rel") == "canonical":
            self.canonical = attrs.get("href")
            return
        for key in ("href", "src"):
            if key in attrs:
                self.links.append((tag, attrs[key]))


def destination(source: str, link: str) -> tuple[str, str] | None:
    url = urlsplit(urljoin(ORIGIN + PREFIX + source, link))
    if url.scheme == "data":
        return None
    if url.scheme not in ("http", "https") or url.netloc != "preview.invalid":
        return None
    path = unquote(url.path)
    if not path.startswith(PREFIX):
        raise ValueError(f"Link escapes repository prefix in {source}: {link}")
    relative = path[len(PREFIX):]
    if not relative or relative.endswith("/"):
        relative += "index.html"
    return relative, unquote(url.fragment)


def validate(output: Path, names: list[str]) -> dict[str, int]:
    pages = {p.relative_to(output).as_posix(): Page(p.read_text())
             for p in output.rglob("*.html")}
    expected = {
        (str(Path(name).parent / "index.html") if Path(name).name == "README.md"
         else str(Path(name).with_suffix("") / "index.html")) for name in names
    }
    if set(pages) != expected | {"404.html"}:
        raise ValueError("Rendered pages differ from the explicit source allowlist")

    def expected_canonical(source: str) -> str:
        return SITE_URL if source == "index.html" else SITE_URL + source[:-len("index.html")]

    for source in expected:
        if pages[source].canonical != expected_canonical(source):
            raise ValueError(
                f"Wrong or missing canonical link in {source}: {pages[source].canonical!r}"
            )

    edges = {name: set() for name in pages}
    count = 0

    def check(source, link):
        nonlocal count
        target = destination(source, link)
        if target is None:
            return None
        name, anchor = target
        if not (output / name).is_file():
            raise ValueError(f"Missing output in {source}: {link}")
        if anchor and name in pages and anchor not in pages[name].ids:
            raise ValueError(f"Missing anchor in {source}: {link}")
        count += 1
        return name

    for source, page in pages.items():
        for tag, link in page.links:
            target = check(source, link)
            if target in pages:
                edges[source].add(target)
            if target is None and tag != "a" and not link.startswith("data:"):
                raise ValueError(f"External page resource in {source}: {link}")
    for css in output.rglob("*.css"):
        for link in re.findall(r"url\(['\"]?([^)'\"]+)", css.read_text()):
            check(css.relative_to(output).as_posix(), link)
    reached, pending = set(), ["index.html"]
    while pending:
        page = pending.pop()
        if page not in reached:
            reached.add(page)
            pending.extend(edges[page] - reached)
    if not expected <= reached:
        raise ValueError(f"Unreachable curated pages: {sorted(expected - reached)}")
    return {"pages": len(expected), "local_links_and_assets": count}
