#!/usr/bin/env python3
"""Exercise documentation invalidation without building Lean or doc-gen4."""

import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import tempfile
import unittest


SOURCE = Path(__file__).resolve().parents[2]


class DocumentationCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tda-docs-cache-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for name in (
            "lean-toolchain", "lakefile.toml", "lake-manifest.json",
            "docbuild/lean-toolchain", "docbuild/lakefile.toml", "docbuild/lake-manifest.json",
            "scripts/build-docs.sh", "scripts/check-doc-lock.sh", "scripts/lib/docs-cache.py",
        ):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(SOURCE / name, target)
        self.lake = self.root / "docbuild/.lake"
        self.build = self.lake / "build"
        self.run_helper("prepare", "old-revision")
        self.write("doc-data/Mathlib.Keep.doc", "")
        self.write("doc-data/Mathlib.Keep.doc.trace", "dependency trace")
        self.write("doc-data/TDA.Removed.doc", "")
        self.write("doc-data/TDA.Removed.doc.trace", "old trace")
        self.write("doc-data/TDA.Library--module.docs_built", "")
        self.write("doc/TDA/Removed.html", "stale page")
        self.write("doc/declarations/declaration-data-TDA.Removed.bmp", "stale search")
        self.write("doc/navbar.html", "stale navigation")
        self.write("doc/index.html", "index")
        self.write("doc-manifest.json", "stale manifest")
        with sqlite3.connect(self.build / "api-docs.db") as db:
            db.executescript("""
                CREATE TABLE modules (name TEXT PRIMARY KEY);
                CREATE TABLE declarations (module TEXT REFERENCES modules(name) ON DELETE CASCADE);
                INSERT INTO modules VALUES ('TDA.Removed'), ('Mathlib.Keep');
                INSERT INTO declarations VALUES ('TDA.Removed'), ('Mathlib.Keep');
            """)
        (self.lake / "docs-source-rev").write_text("old-revision\n")

    def run_helper(self, *args, env=None):
        return subprocess.check_output(
            ["python3", str(self.root / "scripts/lib/docs-cache.py"), *args],
            env=env, text=True,
        ).strip()

    def write(self, name, contents):
        path = self.build / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents)

    def test_same_revision_preserves_complete_cache(self):
        before = {p.relative_to(self.lake): p.read_bytes() for p in self.lake.rglob("*") if p.is_file()}
        self.run_helper("prepare", "old-revision")
        after = {p.relative_to(self.lake): p.read_bytes() for p in self.lake.rglob("*") if p.is_file()}
        self.assertEqual(before, after)

    def test_new_revision_keeps_dependency_database_and_traces(self):
        self.run_helper("prepare", "new-revision")
        self.assertTrue((self.build / "doc-data/Mathlib.Keep.doc.trace").is_file())
        self.assertFalse(list((self.build / "doc-data").glob("TDA*")))
        self.assertFalse((self.build / "doc").exists())
        self.assertFalse((self.build / "doc-manifest.json").exists())
        with sqlite3.connect(self.build / "api-docs.db") as db:
            self.assertEqual(db.execute("SELECT * FROM modules").fetchall(), [("Mathlib.Keep",)])
            self.assertEqual(db.execute("SELECT * FROM declarations").fetchall(), [("Mathlib.Keep",)])
        self.assertEqual((self.lake / "docs-source-rev").read_text(), "old-revision\n")

    def test_missing_database_cannot_reuse_markers(self):
        (self.build / "api-docs.db").unlink()
        self.run_helper("prepare", "old-revision")
        self.assertFalse(self.build.exists())

    def test_configuration_change_discards_database_and_markers(self):
        with (self.root / "docbuild/lake-manifest.json").open("a") as f:
            f.write("\n")
        self.run_helper("prepare", "old-revision")
        self.assertFalse(self.build.exists())

    def test_missing_html_regenerates_html_only(self):
        shutil.rmtree(self.build / "doc")
        self.run_helper("prepare", "old-revision")
        self.assertFalse((self.build / "doc-data/TDA.Library--module.docs_built").exists())
        self.assertTrue((self.build / "doc-data/Mathlib.Keep.doc.trace").is_file())

    def test_source_mode_and_bibliography_participate_in_key(self):
        original = self.run_helper("key")
        self.assertNotEqual(original, self.run_helper("key", env={**os.environ, "DOCGEN_SRC": "vscode"}))
        refs = self.root / "docbuild/docs/references.json"
        refs.parent.mkdir()
        refs.write_text("[]")
        self.assertNotEqual(original, self.run_helper("key"))

    def test_workflow_discards_silent_partial_restore(self):
        # actions/cache can swallow extraction errors, return no matched key and
        # leave step outcome=success. Guard the workflow wiring for this case.
        workflow = (SOURCE / ".github/workflows/ci.yml").read_text()
        cleanup = workflow.split("      - name: Discard incomplete documentation cache restore\n", 1)[1]
        cleanup = cleanup.split("\n      - name:", 1)[0]
        condition, body = cleanup.split("        run: |\n", 1)
        self.assertIn("steps.docs-cache.outputs.cache-matched-key == ''", condition)
        command = "\n".join(line[10:] for line in body.splitlines())
        paths = [".lake/build", "docbuild/.lake"] + [
            f".lake/packages/{pkg}/.lake/build"
            for pkg in ("doc-gen4", "leansqlite", "UnicodeBasic", "BibtexQuery", "MD4Lean", "Cli")
        ]
        for name in paths + [".lake/packages/mathlib/.lake/build"]:
            path = self.root / name
            path.mkdir(parents=True, exist_ok=True)
            (path / "partial").touch()
        subprocess.run(["bash", "-euc", command], cwd=self.root, check=True)
        for name in paths:
            self.assertFalse((self.root / name).exists(), name)
        self.assertTrue((self.root / ".lake/packages/mathlib/.lake/build/partial").is_file())


if __name__ == "__main__":
    unittest.main()
