#!/usr/bin/env python3
"""Test the TDA cache key and its workflow consumer without running Lean."""

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest


SOURCE = Path(__file__).resolve().parents[2]
HELPER = SOURCE / "scripts/lib/tda-cache.py"
WORKFLOW = SOURCE / ".github/workflows/ci.yml"
LEGACY_PREFIX = (
    "tda-build-${{ runner.os }}-${{ runner.arch }}-"
    "${{ hashFiles('lean-toolchain') }}-"
    "${{ hashFiles('lake-manifest.json', 'lakefile.toml') }}-"
)
V2_KEY = (
    "tda-build-v2-${{ runner.os }}-${{ runner.arch }}-"
    "${{ steps.tda-key.outputs.key }}-${{ github.sha }}"
)


BASE_CONFIG = '''name = "CacheFixture"
version = "0.3.0"
description = "fixture package"
license = "Apache-2.0"
keywords = ["math", "cache", "fixture"]
defaultTargets = ["CacheFixture"]
moreLeanArgs = ["-DcacheFixture=1"]
future_flag = "preserve"

[leanOptions]
autoImplicit = true
maxRecDepth = 1024

[[require]]
name = "mathlib"
git = "https://example.invalid/mathlib.git"
rev = "v4.33.1"
version = "nested-v1"

[[lean_lib]]
name = "CacheFixture"
roots = ["CacheFixture"]
globs = ["CacheFixture.*"]

[lean_lib.leanOptions]
warningAsError = false

[extra]
sequence = [1, 2]
record = { kind = "example", count = 1 }
'''


def step_block(workflow, name):
    marker = f"      - name: {name}\n"
    start = workflow.index(marker)
    end = workflow.find("\n      - name:", start + len(marker))
    return workflow[start:] if end < 0 else workflow[start:end]


def run_body(block):
    marker = "        run: |\n"
    start = block.index(marker) + len(marker)
    lines = block[start:].splitlines()
    body = []
    for line in lines:
        if line and not line.startswith("          "):
            break
        body.append(line[10:] if line else "")
    return "\n".join(body) + "\n"


class TdaCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tda-cache-key-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "fixture"
        self.root.mkdir()
        self.other_cwd = Path(self.tmp.name) / "outside"
        self.other_cwd.mkdir()
        self.write("lean-toolchain", b"leanprover/lean4:v4.33.1\n")
        self.write_manifest()
        self.write("lakefile.toml", BASE_CONFIG)
        (self.root / "scripts/lib").mkdir(parents=True)
        shutil.copyfile(HELPER, self.helper)

    @property
    def helper(self):
        return self.root / "scripts/lib/tda-cache.py"

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(value, bytes):
            path.write_bytes(value)
        else:
            path.write_text(value, encoding="utf-8")
        return path

    def write_manifest(self, value=None):
        if value is None:
            value = {
                "version": "1.2.0",
                "packagesDir": ".lake/packages",
                "packages": [{"name": "mathlib", "rev": "abc123"}],
                "lakeDir": ".lake",
                "name": "CacheFixture",
            }
        self.write("lake-manifest.json", json.dumps(value, ensure_ascii=False))

    def run_key(self, *args, cwd=None):
        return subprocess.run(
            ["python3", str(self.helper), *args],
            cwd=cwd or self.root,
            capture_output=True,
            text=True,
            check=False,
        )

    def key(self):
        result = self.run_key("key")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stdout, r"\A[0-9a-f]{64}\n\Z")
        self.assertEqual(result.stderr, "")
        return result.stdout.strip()

    def assert_no_key(self, result, message=None):
        self.assertNotEqual(result.returncode, 0, message or result.stdout)
        self.assertEqual(result.stdout, "")
        self.assertTrue(result.stderr.strip(), "expected a useful stderr diagnostic")

    def config(self):
        return (self.root / "lakefile.toml").read_text(encoding="utf-8")

    def set_config(self, contents):
        self.write("lakefile.toml", contents)

    def test_only_top_level_package_version_is_ignored(self):
        original = self.key()
        config = self.config()
        for version in ("0.4.0", "1.0.0-rc.1+build.7"):
            with self.subTest(version=version):
                self.set_config(config.replace('version = "0.3.0"', f'version = "{version}"'))
                self.assertEqual(self.key(), original)
        self.set_config(config.replace('version = "0.3.0"\n', ""))
        self.assertEqual(self.key(), original)

    def test_toml_formatting_comments_and_table_key_order_normalize(self):
        original = self.key()
        config = self.config()
        changed = config.replace(
            'description = "fixture package"\nlicense = "Apache-2.0"',
            'license = "Apache-2.0"  # a comment\n  description = "fixture package"',
        ).replace(
            'name = "mathlib"\ngit = "https://example.invalid/mathlib.git"\nrev = "v4.33.1"\nversion = "nested-v1"',
            'version = "nested-v1"\nrev = "v4.33.1"\ngit = "https://example.invalid/mathlib.git"\nname = "mathlib"',
        )
        self.set_config(changed)
        self.assertEqual(self.key(), original)

    def test_raw_manifest_toolchain_and_build_configuration_invalidate(self):
        original_config = self.config()
        original_manifest = (self.root / "lake-manifest.json").read_bytes()
        original_toolchain = (self.root / "lean-toolchain").read_bytes()
        base_key = self.key()

        (self.root / "lean-toolchain").write_bytes(original_toolchain + b"# changed\n")
        self.assertNotEqual(self.key(), base_key)
        (self.root / "lean-toolchain").write_bytes(original_toolchain)

        manifest = json.loads(original_manifest)
        manifest["packages"][0]["rev"] = "def456"
        self.write_manifest(manifest)
        self.assertNotEqual(self.key(), base_key)
        (self.root / "lake-manifest.json").write_bytes(original_manifest)

        variants = (
            ("rev", 'rev = "v4.33.1"', 'rev = "v4.33.2"'),
            ("package Lean option", "autoImplicit = true", "autoImplicit = false"),
            ("library Lean option", "warningAsError = false", "warningAsError = true"),
            ("moreLeanArgs", 'moreLeanArgs = ["-DcacheFixture=1"]', 'moreLeanArgs = ["-DcacheFixture=2"]'),
            ("defaultTargets", 'defaultTargets = ["CacheFixture"]', 'defaultTargets = ["Other"]'),
            ("library target name", 'name = "CacheFixture"\nroots = ["CacheFixture"]', 'name = "Other"\nroots = ["CacheFixture"]'),
            ("library roots", 'roots = ["CacheFixture"]', 'roots = ["Other"]'),
            ("library globs", 'globs = ["CacheFixture.*"]', 'globs = ["Other.*"]'),
            ("nested version", 'version = "nested-v1"', 'version = "nested-v2"'),
            ("description", 'description = "fixture package"', 'description = "changed"'),
            ("license", 'license = "Apache-2.0"', 'license = "MIT"'),
            ("keywords", 'keywords = ["math", "cache", "fixture"]', 'keywords = ["math", "cache"]'),
            ("unfamiliar field", 'future_flag = "preserve"', 'future_flag = "changed"'),
            ("array order", "sequence = [1, 2]", "sequence = [2, 1]"),
            ("nested table value", 'kind = "example", count = 1', 'kind = "example", count = 2'),
        )
        for label, old, new in variants:
            with self.subTest(change=label):
                self.set_config(original_config.replace(old, new, 1))
                self.assertNotEqual(self.key(), base_key)

        renamed_unknown = original_config.replace(
            'future_flag = "preserve"', 'future_option = "preserve"'
        )
        self.set_config(renamed_unknown)
        self.assertNotEqual(self.key(), base_key)

    def test_tagged_types_nested_values_and_arrays_are_distinct(self):
        config = self.config()
        keys = set()
        for value in ("true", "1", "true", "1"):
            self.set_config(config + f"\n[typed]\nvalue = {json.dumps(value)}\n")
            keys.add(self.key())
        self.set_config(config + "\n[typed]\nvalue = true\n")
        boolean_key = self.key()
        self.set_config(config + "\n[typed]\nvalue = 1\n")
        integer_key = self.key()
        self.assertEqual(len(keys), 2)
        self.assertNotIn(boolean_key, keys)
        self.assertNotIn(integer_key, keys)
        self.assertNotEqual(boolean_key, integer_key)

        nested = config + '\n[typed]\nvalue = { enabled = true, labels = ["a", "b"] }\n'
        self.set_config(nested)
        ordered = self.key()
        self.set_config(nested.replace('["a", "b"]', '["b", "a"]'))
        self.assertNotEqual(self.key(), ordered)

    def test_unsupported_values_fail_without_stdout(self):
        original_config = self.config()
        for label, value in (
            ("float", "1.25"),
            ("date", "1979-05-27"),
            ("time", "07:32:00"),
            ("datetime", "1979-05-27T07:32:00Z"),
        ):
            with self.subTest(value_type=label):
                self.set_config(original_config + f"\n[unsupported]\nvalue = {value}\n")
                result = self.run_key("key")
                self.assert_no_key(result)
                self.assertIn("unsupported TOML value type", result.stderr)

        self.set_config(original_config + '\n[unsupported]\nvalue = "1979-05-27"\n')
        string_key = self.key()
        self.set_config(self.config().replace('value = "1979-05-27"', 'value = "1979-05-28"'))
        self.assertNotEqual(self.key(), string_key)

    def test_missing_malformed_and_unsupported_inputs_fail_closed(self):
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            path = self.root / name
            original = path.read_bytes()
            with self.subTest(missing=name):
                path.unlink()
                self.assert_no_key(self.run_key("key"))
                path.write_bytes(original)
            with self.subTest(empty=name):
                path.write_bytes(b"")
                self.assert_no_key(self.run_key("key"))
                path.write_bytes(original)

        original_config = self.config()
        for label, invalid in (
            ("duplicate key", original_config.replace(
                'description = "fixture package"',
                'name = "duplicate"\ndescription = "fixture package"',
            )),
            ("invalid UTF-8", b"\xff"),
            ("malformed TOML", original_config + "\n[broken\n"),
        ):
            with self.subTest(config_error=label):
                self.write("lakefile.toml", invalid)
                self.assert_no_key(self.run_key("key"))
                self.write("lakefile.toml", original_config)

        alternative = self.write("lakefile.lean", "package CacheFixture\n")
        self.assert_no_key(self.run_key("key"))
        alternative.unlink()
        alternative.symlink_to("missing-lakefile.lean")
        self.assertFalse(alternative.exists())
        self.assertTrue(alternative.is_symlink())
        self.assert_no_key(self.run_key("key"))
        alternative.unlink()

        for label, value in (
            ("boolean", "true"),
            ("integer", "1"),
            ("float", "1.0"),
            ("array", "[]"),
            ("table", "{}"),
            ("date", "1979-05-27"),
            ("empty string", '""'),
        ):
            with self.subTest(version_type=label):
                self.set_config(original_config.replace('version = "0.3.0"', f"version = {value}"))
                result = self.run_key("key")
                self.assert_no_key(result)
                self.assertIn("version must be a nonempty string", result.stderr)
                self.set_config(original_config)

        for raw in (b"not json", b"NaN", b"Infinity", b"-Infinity", b"[]", b"\xff"):
            with self.subTest(manifest=raw):
                self.write("lake-manifest.json", raw)
                self.assert_no_key(self.run_key("key"))
        self.write_manifest()
        self.assert_no_key(self.run_key("wrong-command"))

    def test_helper_bytes_cwd_and_source_edits(self):
        original = self.key()
        self.assertEqual(self.run_key("key", cwd=self.other_cwd).stdout.strip(), original)
        self.assertEqual(self.key(), original)

        self.write("TDA/Example.lean", "def before := 1\n")
        self.assertEqual(self.key(), original)
        self.write("TDA/Example.lean", "def after := 2\n")
        self.assertEqual(self.key(), original)

        with self.helper.open("ab") as helper:
            helper.write(b"\n# changed helper bytes\n")
        self.assertNotEqual(self.key(), original)

    def test_shell_sensitive_strings_remain_data(self):
        marker = self.root / "should-not-exist"
        value = f'''description = "quote \\"inside\\" and ${{HOME}}"
shell_payload = """first line
second line ${{HOME}} $ (not shell syntax) ${{MARKER}}
$(touch {marker})"""
'''
        config = self.config() + "\n" + value
        self.set_config(config)
        result = self.run_key("key")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stdout, r"\A[0-9a-f]{64}\n\Z")
        self.assertFalse(marker.exists())


class WorkflowWiringTests(unittest.TestCase):
    def setUp(self):
        self.workflow = WORKFLOW.read_text(encoding="utf-8")
        self.compatibility = step_block(self.workflow, "TDA build cache compatibility")
        self.restore = step_block(self.workflow, "Restore TDA build cache")
        self.cleanup = step_block(self.workflow, "Discard failed TDA cache restore")
        self.full_gate = step_block(self.workflow, "Full gate (scripts/check.sh)")
        self.save = step_block(self.workflow, "Save TDA build cache")

    def test_actual_workflow_keys_conditions_scope_and_migration(self):
        self.assertLess(
            self.workflow.index("      - name: TDA build cache compatibility\n"),
            self.workflow.index("      - name: Restore TDA build cache\n"),
        )
        self.assertEqual(self.compatibility.count("name: TDA build cache compatibility"), 1)
        self.assertIn("if: steps.changes.outputs.build == 'true'", self.compatibility)
        self.assertIn("id: tda-key", self.compatibility)
        self.assertIn("shell: bash", self.compatibility)
        self.assertIn("set -euo pipefail", self.compatibility)
        self.assertIn('key="$(python3 scripts/lib/tda-cache.py key)"', self.compatibility)
        self.assertIn('[[ ! "$key" =~ ^[0-9a-f]{64}$ ]]', self.compatibility)
        self.assertIn("printf 'key=%s\\n' \"$key\" >> \"$GITHUB_OUTPUT\"", self.compatibility)
        self.assertNotRegex(self.compatibility, r"echo\s+['\"]?key=\$\(")

        for block in (self.restore, self.save):
            self.assertIn(f"key: {V2_KEY}", block)
            self.assertIn("path: .lake/build", block)
            self.assertIn("continue-on-error: true", block)
        self.assertIn("uses: actions/cache/restore@caa296126883cff596d87d8935842f9db880ef25", self.restore)
        self.assertIn("uses: actions/cache/save@caa296126883cff596d87d8935842f9db880ef25", self.save)
        restore_keys = re.search(r"        restore-keys: \|\n((?:          .*\n)+)", self.restore)
        self.assertIsNotNone(restore_keys)
        prefixes = [line.strip() for line in restore_keys.group(1).splitlines()]
        self.assertEqual(prefixes, [
            "tda-build-v2-${{ runner.os }}-${{ runner.arch }}-${{ steps.tda-key.outputs.key }}-",
            LEGACY_PREFIX,
        ])
        self.assertEqual(self.workflow.count(LEGACY_PREFIX), 1)
        self.assertIn("if: steps.changes.outputs.build == 'true'", self.restore)
        self.assertIn("if: steps.tda-cache.outcome == 'failure'", self.cleanup)
        self.assertIn("rm -rf .lake/build", self.cleanup)
        self.assertIn("if: steps.changes.outputs.build == 'true'", self.full_gate)
        self.assertIn("bash scripts/check.sh", self.full_gate)
        self.assertIn("success()", self.save)
        self.assertIn("github.event_name == 'push'", self.save)
        self.assertIn("github.ref == 'refs/heads/develop'", self.save)
        self.assertIn("steps.changes.outputs.build == 'true'", self.save)
        self.assertIn("steps.tda-cache.outputs.cache-hit != 'true'", self.save)

        guards = (SOURCE / "scripts/test-guards.sh").read_text(encoding="utf-8")
        self.assertIn("python3 scripts/agent/test-tda-cache.py", guards)
        self.assertLess(
            guards.index("python3 scripts/agent/test-tda-cache.py"),
            guards.index("scripts/agent/test-docs-cache.py"),
        )

    def run_actual_step(self, root, output_file):
        environment = os.environ.copy()
        environment["GITHUB_OUTPUT"] = str(output_file)
        return subprocess.run(
            ["bash", "-euo", "pipefail", "-c", run_body(self.compatibility)],
            cwd=root,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )

    def make_shell_fixture(self, root):
        (root / "scripts/lib").mkdir(parents=True)
        shutil.copyfile(HELPER, root / "scripts/lib/tda-cache.py")
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n", encoding="utf-8")
        (root / "lake-manifest.json").write_text('{"name":"CacheFixture","packages":[]}\n', encoding="utf-8")
        (root / "lakefile.toml").write_text('name = "CacheFixture"\nversion = "0.1.0"\n', encoding="utf-8")

    def test_actual_step_writes_only_a_validated_key(self):
        with tempfile.TemporaryDirectory(prefix="tda-cache-step-") as tmp:
            root = Path(tmp)
            self.make_shell_fixture(root)
            output_file = root / "output"
            success = self.run_actual_step(root, output_file)
            self.assertEqual(success.returncode, 0, success.stderr)
            self.assertEqual(success.stdout, "")
            self.assertRegex(output_file.read_text(), r"\Akey=[0-9a-f]{64}\n\Z")

            output_file.unlink()
            (root / "lakefile.toml").write_text("bad = [\n", encoding="utf-8")
            invalid = self.run_actual_step(root, output_file)
            self.assertNotEqual(invalid.returncode, 0)
            self.assertIn("ERROR:", invalid.stderr)
            self.assertFalse(output_file.exists())

    def test_actual_step_rejects_helper_failures_and_invalid_output(self):
        stubs = (
            ("exit 42", "import sys\nsys.exit(42)\n"),
            ("empty output", "pass\n"),
            ("malformed output", "import sys\nsys.stdout.write('bad\\nsecond\\n')\n"),
        )
        with tempfile.TemporaryDirectory(prefix="tda-cache-step-stub-") as tmp:
            root = Path(tmp)
            self.make_shell_fixture(root)
            helper = root / "scripts/lib/tda-cache.py"
            output_file = root / "output"
            for label, body in stubs:
                with self.subTest(stub=label):
                    helper.write_text("#!/usr/bin/env python3\n" + body, encoding="utf-8")
                    output_file.unlink(missing_ok=True)
                    result = self.run_actual_step(root, output_file)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertFalse(output_file.exists())


if __name__ == "__main__":
    unittest.main()
