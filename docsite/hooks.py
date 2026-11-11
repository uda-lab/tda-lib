"""MkDocs integration: checkout links, Unicode anchors, note index, provenance."""
from __future__ import annotations

from html import escape
from pathlib import Path
import posixpath
import re
from urllib.parse import quote, unquote, urlsplit, urlunsplit

from markdown.extensions import Extension
from markdown.blockprocessors import BlockProcessor
from markdown.extensions.toc import slugify_unicode
from markdown.treeprocessors import Treeprocessor
from mkdocs.utils import get_relative_url

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "https://github.com/uda-lab/tda-lib"


class RepositoryLinks(Treeprocessor):
    """Keep curated links local; bind other existing repo files to the source SHA."""

    def __init__(self, extension):
        super().__init__()
        self.extension = extension

    def run(self, root):
        ext = self.extension
        for element in root.iter():
            key = {"a": "href", "img": "src"}.get(element.tag)
            if not key or not element.get(key):
                continue
            url = urlsplit(element.get(key))
            if url.scheme or url.netloc or not url.path:
                continue
            if url.path.startswith(("/", "\\")):
                raise ValueError(f"Root-relative link in {ext.page}: {url.geturl()}")
            target = posixpath.normpath(posixpath.join(posixpath.dirname(ext.page), unquote(url.path)))
            if target in ext.config.extra["sources"]:
                continue
            path = ROOT / target
            if (target.startswith("../") or not path.exists()
                    or not path.resolve().is_relative_to(ROOT)):
                raise ValueError(f"Missing/outside repository link in {ext.page}: {url.geturl()}")
            if element.tag == "img":
                raise ValueError(f"Image must be explicitly staged as an asset: {target}")
            committed = ext.config.extra["committed_files"]
            exists_at_revision = target in committed or any(p.startswith(target + "/") for p in committed)
            if not exists_at_revision:
                element.tag = "span"
                element.attrib.pop(key)
                element.set("title", "Local-only file; absent from the recorded commit")
                continue
            kind = "tree" if path.is_dir() else "blob"
            location = f"{REPOSITORY}/{kind}/{ext.config.extra['source_revision']}/{quote(target)}"
            element.set(key, urlunsplit((*urlsplit(location)[:3], url.query, url.fragment)))
        return root


class RepositoryExtension(Extension):
    def __init__(self, config):
        super().__init__()
        self.config = config
        self.page = ""

    def extendMarkdown(self, md):
        # After inline parsing but before MkDocs' relative-link validation (priority 0).
        md.treeprocessors.register(RepositoryLinks(self), "repository_links", 5)
        # Lists, blockquotes and indented code must parse before we split prose.
        # SuperFences has already protected fenced literals in preprocessing.
        md.parser.blockprocessors.register(DisplayMathBlocks(md.parser), "display_math_boundaries", 11)


_extension = None


class DisplayMathBlocks(BlockProcessor):
    """Split prose around a display, leaving literal parsing to Markdown itself."""

    displays = re.compile(r"^[ \t]*(?:\\\[.*?\\\]|\$\$.*?\$\$)[ \t]*(?=\n|$)", re.M | re.S)

    def test(self, parent, block):
        # Reuse the pinned renderer's code-span rules, including multiline and
        # variable-length backticks, rather than inventing a second parser.
        backticks = self.parser.md.inlinePatterns["backtick"]
        protected, end = [], 0
        for candidate in backticks.getCompiledRegExp().finditer(block):
            if candidate.start() < end:
                continue
            element, start, end = backticks.handleMatch(candidate, block)
            if getattr(element, "tag", None) == "code":
                protected.append((start, end))
        for match in self.displays.finditer(block):
            if any(start < match.end() and end > match.start() for start, end in protected):
                continue
            if block[:match.start()].strip() or block[match.end():].strip():
                self.match = match
                return True
        return False

    def run(self, parent, blocks):
        block = blocks.pop(0)
        start, end = self.match.span()
        blocks[:0] = [part for part in (block[:start], block[start:end], block[end:]) if part.strip()]


def on_config(config):
    global _extension
    _extension = RepositoryExtension(config)
    config.markdown_extensions.append(_extension)
    config.mdx_configs.setdefault("toc", {})["slugify"] = slugify_unicode
    return config


def on_page_markdown(markdown, page, config, files):
    _extension.page = page.file.src_uri
    if page.file.src_uri == "docs/math/README.md":
        entries = []
        for name in config.extra["sources"]:
            if name.startswith("docs/math/") and name != "docs/math/README.md":
                text = Path(files.get_file_from_path(name).abs_src_path).read_text()
                title = next(line[2:] for line in text.splitlines() if line.startswith("# "))
                # Keep arbitrary Markdown punctuation out of generated link labels.
                title = title.replace("[", "\\[").replace("]", "\\]")
                entries.append((title.casefold(), f"- [{title}]({Path(name).name})"))
        markdown += "\n\n## All mathematical notes\n\n" + "\n".join(link for _, link in sorted(entries)) + "\n"
    return markdown


def on_page_content(html, page, config, files):
    revision = config.extra["source_revision"]
    label = "Modified local preview based on" if config.extra["modified_preview"] else "Source revision"
    source = f"{REPOSITORY}/blob/{revision}/{quote(page.file.src_uri)}"
    api = files.get_file_from_path("docs/generated-api.md")
    api_url = get_relative_url(api.url, page.url)
    source_link = (f'<a href="{escape(source)}">Committed source</a>. '
                   if page.file.src_uri in config.extra["committed_files"]
                   else "New page, absent from the recorded commit. ")
    return (
        '<aside class="admonition note" aria-label="Documentation provenance">'
        f'<p>{label} <code>{escape(revision)}</code>. '
        f'{source_link}'
        f'<a href="{escape(api_url)}">Generated API unavailable</a>.'
        '</p></aside>\n' + html
    )
