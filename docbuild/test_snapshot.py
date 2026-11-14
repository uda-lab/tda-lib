#!/usr/bin/env python3
"""Synthetic inventory tests; no Lean, doc-gen4, network or real API artifact."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import inspect_snapshot as snapshot


class SnapshotTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="tda-snapshot-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.site = self.root / "site"
        self.site.mkdir()
        (self.site / "index.html").write_bytes(b"synthetic index")
        (self.site / "TDA").mkdir()
        (self.site / "TDA/space and \u03b1.html").write_bytes(b"synthetic page")
        (self.site / ".asset").write_bytes(b"\x00\xff")

    def test_exact_inventory_and_hash(self):
        result = snapshot.inspect(self.site)
        records = result["site"]["files"]
        self.assertEqual([r["path"] for r in records],
                         [".asset", "TDA/space and \u03b1.html", "index.html"])
        for record in records:
            data = (self.site / record["path"]).read_bytes()
            self.assertEqual(record["bytes"], len(data))
            self.assertEqual(record["sha256"], hashlib.sha256(data).hexdigest())
        encoded = json.dumps(records, sort_keys=True, ensure_ascii=True,
                             separators=(",", ":")).encode("utf-8")
        self.assertEqual(result["site"]["inventory_sha256"], hashlib.sha256(encoded).hexdigest())
        self.assertEqual(result["site"]["total_file_bytes"], 31)
        self.assertEqual(result["site"]["file_count"], 3)
        self.assertIsNone(result["archive"])

    def test_digest_ignores_mtime_but_detects_names_and_content(self):
        def digest():
            return snapshot.inspect(self.site)["site"]["inventory_sha256"]
        before = digest()
        os.utime(self.site / "index.html", (100, 100))
        self.assertEqual(digest(), before)
        (self.site / ".asset").rename(self.site / "renamed")
        renamed = digest()
        self.assertNotEqual(renamed, before)
        (self.site / "renamed").write_bytes(b"changed")
        self.assertNotEqual(digest(), renamed)

    def test_archive_is_only_measured_not_certified(self):
        archive = self.root / "arbitrary.tar.gz"
        archive.write_bytes(b"not a real archive")
        result = snapshot.inspect(self.site, archive)
        self.assertEqual(result["archive"]["bytes"], 18)
        self.assertEqual(result["archive"]["sha256"], hashlib.sha256(archive.read_bytes()).hexdigest())
        self.assertIn("Archive contents are not compared with the site.", result["limitations"])
        with self.assertRaisesRegex(ValueError, "outside"):
            snapshot.inspect(self.site, self.site / "index.html")
        alias = self.root / "archive-link"
        alias.symlink_to(archive)
        with self.assertRaisesRegex(ValueError, "symlink"):
            snapshot.inspect(self.site, alias)
        with self.assertRaisesRegex(ValueError, "regular file"):
            snapshot.inspect(self.site, self.root)

    def test_absent_site_or_index_is_not_a_snapshot(self):
        with self.assertRaises(FileNotFoundError):
            snapshot.inspect(self.root / "absent")
        (self.site / "index.html").unlink()
        with self.assertRaisesRegex(ValueError, "index.html"):
            snapshot.inspect(self.site)

    def test_rejects_symlink_files_directories_and_root(self):
        for target in (self.root / "missing", self.site / "index.html", self.site / "TDA"):
            link = self.site / "link"
            link.symlink_to(target)
            with self.assertRaisesRegex(ValueError, "regular file or directory"):
                snapshot.inspect(self.site)
            link.unlink()
        alias = self.root / "alias"
        alias.symlink_to(self.site)
        with self.assertRaisesRegex(ValueError, "symlink"):
            snapshot.inspect(alias)

    def test_rejects_special_file_without_blocking(self):
        os.mkfifo(self.site / "pipe")
        with self.assertRaisesRegex(ValueError, "regular file or directory"):
            snapshot.inspect(self.site)

    def test_changed_file_fails(self):
        path = self.site / "index.html"
        old = snapshot.signature(path.lstat())
        path.write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "changed"):
            snapshot.measure_file(path, old)

    def test_added_file_during_inspection_fails(self):
        original = snapshot.measure_file
        def changing(path, expected):
            result = original(path, expected)
            (self.site / "new").write_bytes(b"new")
            return result
        with patch.object(snapshot, "measure_file", side_effect=changing):
            with self.assertRaisesRegex(ValueError, "Site changed"):
                snapshot.inspect(self.site)

    def test_cli_does_not_write_inputs_and_missing_site_fails_closed(self):
        script = Path(snapshot.__file__)
        before = snapshot.inventory(self.site)
        env = {**os.environ, "CODEX_STOP_FILE": str(self.root / "stop")}
        result = subprocess.run([sys.executable, str(script), str(self.site)],
                                capture_output=True, text=True, env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["schema_version"], 1)
        self.assertEqual(snapshot.inventory(self.site), before)
        result = subprocess.run([sys.executable, str(script), str(self.root / "absent")],
                                capture_output=True, text=True, env=env)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        (self.root / "stop").touch()
        result = subprocess.run([sys.executable, str(script), str(self.site)],
                                capture_output=True, text=True, env=env)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Stopped", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_documented_archive_example_round_trips_a_synthetic_site(self):
        source = Path(snapshot.__file__).parent
        (self.root / "docbuild").mkdir()
        (self.root / "docbuild/inspect_snapshot.py").write_bytes(
            (source / "inspect_snapshot.py").read_bytes())
        target = self.root / "docbuild/.lake/build/doc"
        target.parent.mkdir(parents=True)
        self.site.rename(target)
        readme = (source / "README.md").read_text()
        command = readme.split("```sh\n(\n", 1)[1].split("\n```", 1)[0]
        env = {**os.environ, "TMPDIR": str(self.root),
               "CODEX_STOP_FILE": str(self.root / "stop")}
        result = subprocess.run(["bash", "-c", "(\n" + command], cwd=self.root,
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        work = Path(result.stdout.strip().removeprefix("Private staging directory: "))
        before = json.loads((work / "before.json").read_text())
        after = json.loads((work / "measurement.json").read_text())
        self.assertEqual(before["site"]["inventory_sha256"], after["site"]["inventory_sha256"])
        restored = self.root / "restored"
        restored.mkdir()
        with tarfile.open(work / "site.tar.gz") as archive:
            archive.extractall(restored, filter="data")
        self.assertEqual(snapshot.inspect(restored)["site"]["inventory_sha256"],
                         after["site"]["inventory_sha256"])


if __name__ == "__main__":
    unittest.main()
