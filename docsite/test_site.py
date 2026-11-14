#!/usr/bin/env python3
"""Focused Lean-independent regression checks; run with the pinned site Python."""
from functools import partial
from html import unescape
from html.parser import HTMLParser
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import textwrap
from types import SimpleNamespace
import unittest
from unittest.mock import patch
from urllib.request import urlopen

import markdown

import build
import hooks
from validate import Page, destination, validate


def source_fences(source):
    """Read the corpus's fenced literal blocks independently of the renderer."""
    result, opening, body = [], None, []
    for line in source.splitlines():
        match = re.match(r"^( *)(`{3,}|~{3,})([\w+-]*)\s*$", line)
        if opening is None and match:
            opening = match.groups()
        elif opening is not None:
            indent, fence, language = opening
            if (match and not match[3] and match[1] == indent
                    and match[2] == fence):
                result.append((language, "\n".join(body), bool(indent)))
                opening, body = None, []
            else:
                body.append(line[len(indent):] if line.startswith(indent) else line)
    if opening is not None:
        raise AssertionError("Unclosed source fence")
    return result


class ArticleContent(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.depth = 0
        self.pre = False
        self.code = None
        self.items = []
        self.nested_items = []
        self.blocks = []
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "div" and (self.depth or attrs.get("itemprop") == "articleBody"):
            self.depth += 1
        if not self.depth:
            return
        if tag == "li":
            self.items.append([])
        elif tag == "pre":
            self.pre = True
        elif tag == "code" and self.pre:
            language = attrs.get("class", "").removeprefix("language-")
            self.code = (language, [], bool(self.items))

    def handle_data(self, text):
        if self.depth:
            if self.items:
                self.items[-1].append(text)
            if self.code is not None:
                self.code[1].append(text)

    def handle_endtag(self, tag):
        if not self.depth:
            return
        if tag == "code" and self.code is not None:
            language, text, nested = self.code
            self.blocks.append((language, "".join(text).rstrip("\n"), nested))
            self.code = None
        elif tag == "pre":
            self.pre = False
        elif tag == "li":
            text = " ".join("".join(self.items.pop()).split())
            if self.items:
                self.nested_items.append(text)
        elif tag == "div":
            self.depth -= 1


class SourcePolicyTests(unittest.TestCase):
    def test_failed_validation_keeps_previous_preview(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp) / "work"
            output = work / "preview/tda-lib"
            output.mkdir(parents=True)
            (output / "index.html").write_text("KNOWN GOOD")
            with patch.multiple(build, WORK=work, OUTPUT=output), patch.object(sys, "argv", ["build.py"]):
                with patch("validate.validate", side_effect=ValueError("Invalid candidate")):
                    with self.assertRaisesRegex(ValueError, "Invalid candidate"):
                        build.main()
            self.assertEqual(list(output.iterdir()), [output / "index.html"])
            self.assertEqual((output / "index.html").read_text(), "KNOWN GOOD")
            self.assertFalse(list(work.glob("previous-preview-*")))
            self.assertFalse(list(work.glob("render-*")))

    def test_failed_install_rolls_back_previous_preview(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp) / "work"
            output = work / "preview/tda-lib"
            output.mkdir(parents=True)
            (output / "index.html").write_text("KNOWN GOOD")
            rendered = work / "candidate"
            rendered.mkdir()
            original_rename = Path.rename

            def failing_rename(source, destination):
                if source == rendered:
                    raise OSError("Simulated rename failure")
                return original_rename(source, destination)

            with patch.multiple(build, WORK=work, OUTPUT=output), patch.object(Path, "rename", failing_rename):
                with self.assertRaisesRegex(OSError, "Simulated rename failure"):
                    build.install_preview(rendered)
            self.assertEqual((output / "index.html").read_text(), "KNOWN GOOD")
            self.assertFalse(list(work.glob("previous-preview-*")))

    def test_vendor_paths_reject_traversal_and_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copytree(build.ROOT / "docsite/assets", root / "docsite/assets")
            shutil.copy(build.ROOT / "docsite/vendor.json", root / "docsite/vendor.json")
            self.assertEqual(set(build.vendor_assets(root)), {"mathjax-config.js", "tex-svg.js", "MathJax-LICENSE"})
            manifest = root / "docsite/vendor.json"
            vendor = json.loads(manifest.read_text())
            vendor["files"]["../private"] = "0" * 64
            manifest.write_text(json.dumps(vendor))
            with self.assertRaisesRegex(ValueError, "inventory"):
                build.vendor_assets(root)
            shutil.copy(build.ROOT / "docsite/vendor.json", manifest)
            asset = root / "docsite/assets/tex-svg.js"
            asset.unlink()
            asset.symlink_to(build.ROOT / "docsite/assets/tex-svg.js")
            with self.assertRaisesRegex(ValueError, "regular repository file"):
                build.vendor_assets(root)

    def test_fresh_output_preserves_unknown_old_data_without_following_links(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp) / "work"
            output = work / "preview/tda-lib"
            output.mkdir(parents=True)
            (output / ".secret").write_text("PRIVATE FILE")
            (output / "unreviewed.txt").write_text("NOT A SITE INPUT")
            (output / ".private").mkdir()
            (output / ".private/record").write_text("PRIVATE RECORD")
            outside = Path(tmp) / "outside"
            outside.mkdir()
            (outside / "sentinel").write_text("DO NOT CHANGE")
            (output / "docs").symlink_to(outside, target_is_directory=True)
            with patch.multiple(build, WORK=work, OUTPUT=output), patch.object(sys, "argv", ["build.py"]):
                build.main()
            self.assertEqual(list(outside.iterdir()), [outside / "sentinel"])
            self.assertEqual((outside / "sentinel").read_text(), "DO NOT CHANGE")
            self.assertFalse((output / "docs").is_symlink())
            self.assertFalse((output / "unreviewed.txt").exists())
            self.assertTrue((output / "docs/index.html").is_file())
            self.assertFalse(any(p.is_symlink() or p.name.startswith(".") for p in output.rglob("*")))
            backups = list(work.glob("previous-preview-*"))
            self.assertEqual(len(backups), 1)
            old = backups[0] / "tda-lib"
            self.assertEqual((old / ".secret").read_text(), "PRIVATE FILE")
            self.assertEqual((old / "unreviewed.txt").read_text(), "NOT A SITE INPUT")
            self.assertEqual((old / ".private/record").read_text(), "PRIVATE RECORD")
            self.assertTrue((old / "docs").is_symlink())
            self.assertFalse(backups[0].is_relative_to(output.parent))

    def test_output_symlink_is_rejected_without_touching_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp) / "work"
            (work / "preview").mkdir(parents=True)
            outside = Path(tmp) / "outside"
            outside.mkdir()
            (outside / "sentinel").write_text("KEEP")
            output = work / "preview/tda-lib"
            output.symlink_to(outside, target_is_directory=True)
            with patch.multiple(build, WORK=work, OUTPUT=output), self.assertRaises(ValueError):
                build.output_paths()
            self.assertEqual((outside / "sentinel").read_text(), "KEEP")

    def test_display_boundaries_preserve_markdown_literals_exactly(self):
        cases = {
            "fake backtick closer": "```text\n```not-a-closing-fence\n\\[literal\\]\n```\n",
            "fake tilde closer": "~~~text\n~~~not-a-closing-fence\n\\[literal\\]\n~~~\t\n",
            "shorter and opposite fences": "````text\n```\n~~~\n\\[literal\\]\n````\n",
            "longer inner fence": "~~~text\n~~~~\n\\[literal\\]\n~~~\n",
            "indented list fence": "- Item\n\n  ```text\n    ```\n  ```not-a-closer\n  \\[literal\\]\n  ```\t\n",
            "indented literal code": "Code:\n\n    prior\n    \\[literal\\]\n    after\n",
            "inline triple backticks": "```literal```\n",
            "inline math delimiters": "`\\[literal\\]` and ``$$literal$$``\n",
            "multiline inline code": "`first\n\\[literal\\]\nlast`\n",
        }
        extensions = ["pymdownx.highlight", "pymdownx.superfences", "mdx_truly_sane_lists", "pymdownx.arithmatex"]
        configs = {
            "pymdownx.highlight": {"use_pygments": False},
            "mdx_truly_sane_lists": {"nested_indent": 2, "truly_sane": False},
            "pymdownx.arithmatex": {"generic": True},
        }
        for label, literal in cases.items():
            with self.subTest(label=label):
                source = literal + "\nAfter literal\n\\[x_1^2 + \\alpha\\]\nMore prose\n"
                baseline = markdown.markdown(source, extensions=extensions, extension_configs=configs)
                ext = hooks.RepositoryExtension(SimpleNamespace(extra={"sources": {}}))
                rendered = markdown.markdown(source, extensions=[*extensions, ext], extension_configs=configs)
                code = lambda text: [unescape(t) for t in re.findall(r"<code(?: [^>]*)?>(.*?)</code>", text, re.S)]
                self.assertTrue(code(baseline), "Fixture must really contain a Markdown literal")
                self.assertEqual(code(rendered), code(baseline))
                self.assertEqual(rendered.count('class="arithmatex"'), 1)
                self.assertIn(r'<div class="arithmatex">\[x_1^2 + \alpha\]</div>', rendered)

    def test_allowlist_rejects_unsafe_or_unreviewed_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "docsite").mkdir()
            (root / "README.md").write_text("# Home")
            manifest = root / "docsite/sources.txt"
            for text in ["../secret.md", "docs/orchestration.md", "docs/math/*.md",
                         "README.md\nREADME.md", "docs/math/missing.md", ""]:
                with self.subTest(text=text):
                    manifest.write_text(text)
                    with self.assertRaises(ValueError):
                        build.sources(root)
            manifest.write_text("README.md\n")
            self.assertEqual(build.sources(root), ["README.md"])
            (root / "README.md").unlink()
            (root / "README.md").symlink_to(build.ROOT / "README.md")
            with self.assertRaises(ValueError):
                build.sources(root)

    def test_source_links_use_exact_revision(self):
        ext = hooks.RepositoryExtension(SimpleNamespace(extra={
            "sources": {"README.md": ""}, "source_revision": "a" * 40,
            "committed_files": ["LICENSE"],
        }))
        ext.page = "README.md"
        result = markdown.markdown("[License](LICENSE) [Home](README.md#citation)", extensions=[ext])
        self.assertIn("/blob/" + "a" * 40 + "/LICENSE", result)
        self.assertIn('href="README.md#citation"', result)
        for link in ["missing.md", "../outside.md", "/root-only", "docs/not-real.md"]:
            with self.subTest(link=link), self.assertRaises(ValueError):
                markdown.markdown(f"[Bad]({link})", extensions=[ext])
        result = markdown.markdown("[Local](docsite/mkdocs.yml)", extensions=[ext])
        self.assertNotIn("href=", result)
        self.assertIn("Local-only file", result)

    def test_math_delimiters_survive_markdown(self):
        source = r"Inline \(x_1 < y^2\), $a+b$ and `\(code\)`." + "\n\n" + r"\[x^2+y^2\]" + "\n\n$$z_1^2$$"
        result = markdown.markdown(source, extensions=["pymdownx.arithmatex"],
                                   extension_configs={"pymdownx.arithmatex": {"generic": True}})
        self.assertEqual(result.count('class="arithmatex"'), 4)
        self.assertIn(r"\(x_1 &lt; y^2\)", result)
        self.assertIn(r"\[z_1^2\]", result)
        self.assertIn(r"<code>\(code\)</code>", result)

    def test_vendor_integrity(self):
        vendor = json.loads((build.ROOT / "docsite/vendor.json").read_text())
        self.assertEqual(vendor["version"], "3.2.2")
        for name, expected in vendor["files"].items():
            self.assertEqual(hashlib.sha256((build.ROOT / "docsite/assets" / name).read_bytes()).hexdigest(), expected)

    def test_link_auditor_rejects_bad_prefix(self):
        with self.assertRaises(ValueError):
            destination("docs/index.html", "/css/theme.css")

    def test_link_auditor_rejects_missing_anchor(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            canonical = '<link rel="canonical" href="https://uda-lab.github.io/tda-lib/" />'
            (root / "index.html").write_text(canonical + '<a href="#missing">Bad</a>')
            (root / "404.html").write_text("")
            with self.assertRaisesRegex(ValueError, "Missing anchor"):
                validate(root, ["README.md"])

    def test_link_auditor_rejects_wrong_or_missing_canonical(self):
        for canonical in ["", '<link rel="canonical" href="https://example.invalid/" />']:
            with tempfile.TemporaryDirectory() as tmp, self.subTest(canonical=canonical):
                root = Path(tmp)
                (root / "index.html").write_text(canonical)
                (root / "404.html").write_text("")
                with self.assertRaisesRegex(ValueError, "canonical"):
                    validate(root, ["README.md"])


class BuiltSiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # All these commands would fail if the site attempted to invoke Lean or fetch.
        cls.traps = tempfile.TemporaryDirectory()
        for name in ["lean", "lake", "elan", "curl", "wget", "npm"]:
            trap = Path(cls.traps.name) / name
            trap.write_text("#!/bin/sh\necho Forbidden tool invocation >&2\nexit 99\n")
            trap.chmod(0o755)
        env = dict(os.environ, PATH=cls.traps.name + os.pathsep + os.environ["PATH"])
        subprocess.run([sys.executable, str(build.ROOT / "docsite/build.py")], check=True, env=env)
        cls.names = build.sources()
        cls.info = json.loads((build.OUTPUT / "build-info.json").read_text())

    @classmethod
    def tearDownClass(cls):
        cls.traps.cleanup()

    def test_inventory_and_navigation(self):
        result = validate(build.OUTPUT, self.names)
        self.assertEqual(result["pages"], len(self.names))
        self.assertEqual(set(self.info["sources"]), set(self.names))
        self.assertIsNone(self.info["api_snapshot"])
        self.assertEqual(self.info["source_revision"], build.git("rev-parse", "HEAD"))
        for name in self.names:
            self.assertEqual(self.info["sources"][name], hashlib.sha256((build.ROOT / name).read_bytes()).hexdigest())
        for prohibited in [".git", ".agents", ".lake", "docbuild", "docs/orchestration", "sources"]:
            self.assertFalse((build.OUTPUT / prohibited).exists())
        self.assertFalse(list(build.OUTPUT.rglob("*.md")))
        self.assertFalse(list(build.OUTPUT.rglob("*.lean")))

    def test_responsive_stylesheet_is_local_and_loaded_after_theme(self):
        css = build.OUTPUT / "css/curated.css"
        self.assertEqual(css.read_bytes(),
                         (build.ROOT / "docsite/theme/css/curated.css").read_bytes())
        for name in self.names:
            target = (str(Path(name).parent / "index.html") if Path(name).name == "README.md"
                      else str(Path(name).with_suffix("") / "index.html"))
            html = (build.OUTPUT / target).read_text()
            with self.subTest(name=name):
                styles = re.findall(r'<link[^>]*href="([^"]+)"[^>]*rel="stylesheet"[^>]*>|'
                                    r'<link[^>]*rel="stylesheet"[^>]*href="([^"]+)"[^>]*>', html)
                paths = [a or b for a, b in styles]
                self.assertTrue(paths[-1].endswith("css/curated.css"))
                self.assertEqual(destination(target, paths[-1])[0], "css/curated.css")
        # The browser-only probe is a test input, never a published page/asset.
        self.assertFalse((build.OUTPUT / "test_layout.js").exists())

    def test_explicit_and_unicode_anchors(self):
        home = Page((build.OUTPUT / "index.html").read_text())
        self.assertIn("results-in-v010", home.ids)
        api = Page((build.OUTPUT / "docs/api/index.html").read_text())
        self.assertIn("ambient-čech-complexes", api.ids)

    def test_provenance_and_math(self):
        text = (build.OUTPUT / "docs/math/rank-resolution-simplicial-coordinate-translation/index.html").read_text()
        self.assertIn(self.info["source_revision"], text)
        self.assertIn("Generated API unavailable", text)
        self.assertIn('class="arithmatex"', text)
        self.assertIn(r"\(C\)", text)
        self.assertNotIn("cdnjs.cloudflare.com", text)
        if self.info["modified_preview"]:
            self.assertIn("Modified local preview", text)

    def test_corpus_code_lists_and_exact_display_tex(self):
        totals = {"code_blocks": 0, "nested_items": 0, "display_math": 0}
        for name in self.names:
            source = (build.ROOT / name).read_text()
            target = (str(Path(name).parent / "index.html") if Path(name).name == "README.md"
                      else str(Path(name).with_suffix("") / "index.html"))
            html = (build.OUTPUT / target).read_text()
            article = ArticleContent(html)
            fences = source_fences(source)
            if name in {"docs/math/finite-p-boundary-transport.md", "docs/math/multiparameter-closure.md"}:
                # These three displays are deliberate four-space indented code,
                # rather than fences. Preserve their complete source text too.
                fences.extend(("", text, False) for text in re.findall(r"^    ([^ ].*)$", source, re.M))
            with self.subTest(name=name, content="fences"):
                # Exact language, line breaks, relative indentation and list ownership.
                self.assertEqual(article.blocks, fences)
            totals["code_blocks"] += len(fences)
            # The full corpus uses 12 two-space nested bullets. Deeper '+' lines
            # elsewhere are math or multiline code spans, not Markdown lists.
            nested = re.findall(r"^  - (.*)$", source, re.M)
            with self.subTest(name=name, content="nested lists"):
                self.assertEqual(len(article.nested_items), len(nested))
                for original, rendered in zip(nested, article.nested_items):
                    self.assertTrue(rendered.startswith(original.split("`")[0][:25]))
            totals["nested_items"] += len(nested)
            original = re.findall(r"\\\[(.*?)\\\]|\$\$(.*?)\$\$", source, re.S)
            rendered = re.findall(r'<div class="arithmatex">\\\[(.*?)\\\]</div>', html, re.S)
            # Normalize only outer block whitespace/list indentation and the
            # two equivalent display delimiter styles; compare all TeX exactly.
            expected = [textwrap.dedent(a or b).strip() for a, b in original]
            actual = [textwrap.dedent(unescape(text)).strip() for text in rendered]
            with self.subTest(name=name, content="display TeX"):
                self.assertEqual(actual, expected)
            totals["display_math"] += len(original)
        print(f"Corpus structure checked: {totals}")

    def test_subpath_http_preview(self):
        class QuietHandler(SimpleHTTPRequestHandler):
            def log_message(self, *args):
                pass
        handler = partial(QuietHandler, directory=str(build.OUTPUT.parent))
        with ThreadingHTTPServer(("127.0.0.1", 0), handler) as server:
            worker = threading.Thread(target=server.serve_forever, daemon=True)
            worker.start()
            try:
                # Fetch every page and every asset as served below the repository prefix.
                for path in build.OUTPUT.rglob("*"):
                    if not path.is_file():
                        continue
                    from urllib.parse import quote
                    url = f"http://127.0.0.1:{server.server_port}/tda-lib/" + quote(path.relative_to(build.OUTPUT).as_posix())
                    with urlopen(url, timeout=5) as response:
                        self.assertEqual(response.status, 200, url)
                        self.assertEqual(response.read(), path.read_bytes(), url)
            finally:
                server.shutdown()
                worker.join()

    def test_clean_requirement_when_modified(self):
        if not self.info["modified_preview"]:
            self.skipTest("This checkout is clean")
        result = subprocess.run([sys.executable, str(build.ROOT / "docsite/build.py"), "--require-clean"],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("A clean checkout is required", result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
