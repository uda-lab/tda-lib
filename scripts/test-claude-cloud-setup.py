#!/usr/bin/env python3
"""Offline smoke tests for the standalone Claude cloud setup path."""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SETUP = ROOT / "scripts/claude-cloud-setup.sh"
ACTIVATE = ROOT / "scripts/claude-cloud-activate.sh"
PIN_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")


def embedded_pin(script: str, filename: str, marker: str) -> str:
    pattern = re.compile(
        rf'cat > "\$PROJECT_DIR/{re.escape(filename)}" <<\'{re.escape(marker)}\'\n'
        rf'(.*?)\n{re.escape(marker)}\n',
        re.DOTALL,
    )
    match = pattern.search(script)
    if not match:
        raise AssertionError(f"could not find embedded {filename} pin")
    return match.group(1) + "\n"


def write_mock_bin(directory: Path) -> None:
    directory.mkdir(parents=True)
    commands = {
        "timeout": r'''#!/usr/bin/env bash
set -e
while [[ "$1" == --* ]]; do shift; done
[[ "$1" =~ ^[0-9]+s$ ]] && shift
exec "$@"
''',
        "curl": r'''#!/usr/bin/env bash
set -e
[[ "${MOCK_CURL_FAIL:-0}" == 1 ]] && exit 22
out=
while (($#)); do
  if [[ "$1" == --output ]]; then out=$2; shift 2; else shift; fi
done
[[ -n "$out" ]]
mkdir -p "$(dirname "$out")"
printf mock-elan-archive > "$out"
''',
        "sha256sum": r'''#!/usr/bin/env bash
if [[ "${MOCK_BAD_CHECKSUM:-0}" == 1 ]]; then exit 1; fi
for arg in "$@"; do
  if [[ "$arg" == - ]]; then exit 0; fi
done
exec /usr/bin/sha256sum "$@"
''',
        "tar": r'''#!/usr/bin/env bash
set -e
[[ "${MOCK_TAR_FAIL:-0}" == 1 ]] && exit 2
dest=
while (($#)); do
  if [[ "$1" == -C ]]; then dest=$2; shift 2; else shift; fi
done
[[ -n "$dest" ]]
cat > "$dest/elan-init" <<'MOCK_ELAN_INIT'
#!/usr/bin/env bash
set -e
mkdir -p "$HOME/.elan/bin"
cat > "$HOME/.elan/bin/elan" <<'MOCK_ELAN'
#!/usr/bin/env bash
set -e
if [[ "$1" == --version ]]; then echo 'elan 4.2.4 (mock)'; exit 0; fi
if [[ "$1" == toolchain && "$2" == list ]]; then
  [[ -f "$HOME/.elan/fake-toolchain" ]] && echo 'leanprover/lean4:v4.33.1'
  exit 0
fi
if [[ "$1" == toolchain && "$2" == install ]]; then
  mkdir -p "$HOME/.elan/toolchains"
  touch "$HOME/.elan/fake-toolchain"
  exit 0
fi
if [[ "$1" == run && "$3" == lean && "$4" == --version ]]; then
  [[ "${MOCK_LEAN_VERSION_FAIL:-0}" == 1 ]] && echo 'Lean (version 4.33.0, mock)' && exit 0
  echo 'Lean (version 4.33.1, mock)'
  exit 0
fi
if [[ "$1" == run && "$3" == lake && "$4" == --version ]]; then
  [[ "${MOCK_LEAN_VERSION_FAIL:-0}" == 1 ]] && echo 'Lake version 5 (Lean version 4.33.0)' && exit 0
  echo 'Lake version 5 (Lean version 4.33.1)'
  exit 0
fi
exit 64
MOCK_ELAN
cat > "$HOME/.elan/bin/lake" <<'MOCK_LAKE'
#!/usr/bin/env bash
set -e
printf '%s\n' "$*" >> "${MOCK_LAKE_CALLS:?}"
[[ "${MOCK_LAKE_FAIL:-0}" == 1 ]] && exit 42
[[ "$*" == 'exe cache get' ]]
python3 - <<'PY'
import json, os
from pathlib import Path
project = Path.cwd()
manifest = json.loads((project / 'lake-manifest.json').read_text())
for package in manifest['packages']:
    path = project / '.lake' / 'packages' / package['name']
    (path / '.git').mkdir(parents=True, exist_ok=True)
cache = Path(os.environ['MATHLIB_CACHE_DIR'])
cache.mkdir(parents=True, exist_ok=True)
(cache / 'mock.ltar').write_bytes(b'mock cache artifact')
(project / '.lake' / 'build' / 'lib' / 'lean').mkdir(parents=True, exist_ok=True)
(project / '.lake' / 'build' / 'lib' / 'lean' / 'Mock.olean').write_bytes(b'mock')
PY
echo 'Downloaded all files successfully!'
MOCK_LAKE
chmod +x "$HOME/.elan/bin/elan" "$HOME/.elan/bin/lake"
MOCK_ELAN_INIT
chmod +x "$dest/elan-init"
''',
        "git": r'''#!/usr/bin/env bash
set -e
if [[ "$1" == -C && "$3" == rev-parse && "$4" == HEAD ]]; then
  [[ -d "$2" ]] || exit 128
  python3 - "$MOCK_PROJECT/lake-manifest.json" "$(basename "$2")" <<'PY'
import json, sys
from pathlib import Path
manifest = json.loads(Path(sys.argv[1]).read_text())
for package in manifest['packages']:
    if package['name'] == sys.argv[2]:
        print(package['rev'])
        break
else:
    raise SystemExit(1)
PY
  exit
fi
if [[ "$1" == -C && "$3" == diff ]]; then exit 0; fi
if [[ "$1" == -C && "$3" == status ]]; then
  [[ -f "$2/Extra.lean" ]] && echo '?? Extra.lean'
  exit 0
fi
exec /usr/bin/git "$@"
''',
    }
    for name, body in commands.items():
        path = directory / name
        path.write_text(body)
        path.chmod(0o755)


def environment(mock_bin: Path, home: Path, setup_root: Path, calls: Path, **extra: str) -> dict[str, str]:
    env = os.environ.copy()
    env.update(
        HOME=str(home),
        PATH=f"{mock_bin}:/usr/bin:/bin",
        TDA_CLAUDE_SETUP_ROOT=str(setup_root),
        MOCK_PROJECT=str(setup_root / "project"),
        MOCK_LAKE_CALLS=str(calls),
    )
    env.update(extra)
    return env


def run(command: list[str], env: dict[str, str], *, expect: int = 0) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
    if result.returncode != expect:
        raise AssertionError(
            f"command returned {result.returncode}, expected {expect}: {command}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def make_checkout(directory: Path) -> None:
    (directory / "scripts").mkdir(parents=True)
    for filename in PIN_FILES:
        shutil.copy2(ROOT / filename, directory / filename)
    shutil.copy2(ACTIVATE, directory / "scripts/claude-cloud-activate.sh")


def status_map(path: Path) -> dict[str, str]:
    return dict(line.split("=", 1) for line in path.read_text().splitlines() if "=" in line)


def main() -> None:
    script_text = SETUP.read_text()
    expected_markers = {
        "lean-toolchain": "TDA_LEAN_TOOLCHAIN",
        "lakefile.toml": "TDA_LAKEFILE",
        "lake-manifest.json": "TDA_LAKE_MANIFEST",
    }
    for filename, marker in expected_markers.items():
        embedded = embedded_pin(script_text, filename, marker)
        if embedded != (ROOT / filename).read_text():
            raise AssertionError(f"embedded {filename} is not byte-for-byte current")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    if manifest["packages"][0]["rev"] not in script_text:
        raise AssertionError("setup script does not identify the current mathlib commit")

    run(["bash", "-n", str(SETUP)], os.environ.copy())
    run(["bash", "-n", str(ACTIVATE)], os.environ.copy())

    with tempfile.TemporaryDirectory(prefix="tda claude cloud ") as temp:
        base = Path(temp)
        mock_bin = base / "mock-bin"
        write_mock_bin(mock_bin)

        # An unavailable cache path does not fail the cloud session setup hook.
        blocked_parent = base / "not-a-directory"
        blocked_parent.write_text("file")
        blocked_home = base / "home blocked"
        blocked_home.mkdir()
        blocked_setup = blocked_parent / "cache"
        blocked_result = run(
            ["bash", str(SETUP)],
            environment(mock_bin, blocked_home, blocked_setup, base / "calls-blocked"),
        )
        if "could not create its cache paths" not in blocked_result.stderr:
            raise AssertionError("unwritable setup path was not reported clearly")
        if (blocked_setup / "STATUS.txt").exists():
            raise AssertionError("setup reported a status despite not creating its cache root")

        # Successful mocked download/install/cache path and fresh-checkout activation.
        home = base / "home ready"
        setup_root = base / "setup ready"
        calls = base / "lake-calls.txt"
        home.mkdir()
        env = environment(mock_bin, home, setup_root, calls)
        result = run(["bash", str(SETUP)], env)
        status = status_map(setup_root / "STATUS.txt")
        if status["state"] != "warm" or status["mathlib_cache_status"] != "complete":
            raise AssertionError(f"mocked complete setup did not become warm:\n{result.stdout}\n{status}")
        if calls.read_text().splitlines() != ["exe cache get"]:
            raise AssertionError("setup ran a command beyond the pinned cache fetch")
        if not (setup_root / "downloads/elan-x86_64-unknown-linux-gnu.tar.gz").exists():
            raise AssertionError("verified Elan download was not retained in the setup cache")

        checkout = base / "checkout"
        make_checkout(checkout)
        helper_env = env | {"CLAUDE_CODE_REMOTE": "true"}
        activated = run(["bash", str(checkout / "scripts/claude-cloud-activate.sh")], helper_env)
        expected_packages = (setup_root / "project/.lake/packages").resolve()
        actual_packages = (checkout / ".lake/packages").resolve()
        if actual_packages != expected_packages or "Pinned setup artifacts match" not in activated.stdout:
            raise AssertionError("activation did not link the exact prepared package cache")

        # Reruns reuse the pinned Elan/toolchain and keep the exact status warm.
        rerun = run(["bash", str(SETUP)], env)
        rerun_status = status_map(setup_root / "STATUS.txt")
        if rerun_status["state"] != "warm" or len(calls.read_text().splitlines()) != 2:
            raise AssertionError(f"setup rerun was not idempotent:\n{rerun.stdout}\n{rerun_status}")

        # A pin mismatch is rejected without creating .lake or touching files.
        mismatch = base / "checkout-mismatch"
        make_checkout(mismatch)
        (mismatch / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
        run(["bash", str(mismatch / "scripts/claude-cloud-activate.sh")], helper_env, expect=2)
        if (mismatch / ".lake").exists():
            raise AssertionError("activation created a cache link despite a pin mismatch")

        # Existing package paths are kept intact.
        existing = base / "checkout-existing"
        make_checkout(existing)
        marker = existing / ".lake/packages/keep-me"
        marker.parent.mkdir(parents=True)
        marker.write_text("preserve")
        run(["bash", str(existing / "scripts/claude-cloud-activate.sh")], helper_env)
        if marker.read_text() != "preserve" or marker.parent.is_symlink():
            raise AssertionError("activation replaced an existing dependency path")

        # Source cleanliness includes untracked files, not only Git's tracked diff.
        untracked_source = setup_root / "project/.lake/packages/mathlib/Extra.lean"
        untracked_source.write_text("def extra := True\n")
        untracked_checkout = base / "checkout-untracked-source"
        make_checkout(untracked_checkout)
        run(
            ["bash", str(untracked_checkout / "scripts/claude-cloud-activate.sh")],
            helper_env,
            expect=3,
        )
        if (untracked_checkout / ".lake").exists():
            raise AssertionError("activation linked prepared packages with an untracked source")
        untracked_source.unlink()

        # Same-count artifact corruption is caught by the setup checksum manifest.
        corrupt_archive = home / ".cache/mathlib/mock.ltar"
        corrupt_archive.write_bytes(b"corrupt archive")
        corrupt_checkout = base / "checkout-corrupt-cache"
        make_checkout(corrupt_checkout)
        run(
            ["bash", str(corrupt_checkout / "scripts/claude-cloud-activate.sh")],
            helper_env,
            expect=3,
        )

        # An already-listed but broken Lean/Lake toolchain is not labelled ready.
        home_broken_toolchain = base / "home broken toolchain"
        setup_broken_toolchain = base / "setup broken toolchain"
        shutil.copytree(home, home_broken_toolchain)
        shutil.copytree(setup_root, setup_broken_toolchain)
        broken_calls = base / "lake-calls-broken-toolchain.txt"
        broken_env = environment(
            mock_bin, home_broken_toolchain, setup_broken_toolchain, broken_calls,
            MOCK_LEAN_VERSION_FAIL="1",
        )
        result = run(["bash", str(SETUP)], broken_env)
        broken_status = status_map(setup_broken_toolchain / "STATUS.txt")
        if broken_status["state"] != "partial" or broken_status["lean_toolchain_status"] != "incomplete":
            raise AssertionError(f"broken registered toolchain was mislabeled ready:\n{result.stdout}\n{broken_status}")
        if broken_calls.exists():
            raise AssertionError("cache fetch ran with an unverified Lean/Lake toolchain")

        # A failed cache request remains explicitly partial and cannot be activated.
        home_partial = base / "home partial"
        home_partial.mkdir()
        partial_root = base / "setup partial"
        partial_calls = base / "lake-calls-partial.txt"
        partial_env = environment(
            mock_bin, home_partial, partial_root, partial_calls, MOCK_LAKE_FAIL="1"
        )
        result = run(["bash", str(SETUP)], partial_env)
        partial = status_map(partial_root / "STATUS.txt")
        if partial["state"] != "partial" or partial["mathlib_cache_status"] != "incomplete":
            raise AssertionError(f"failed cache was mislabeled as warm:\n{result.stdout}\n{partial}")
        partial_checkout = base / "checkout-partial"
        make_checkout(partial_checkout)
        partial_helper_env = partial_env | {"CLAUDE_CODE_REMOTE": "true"}
        run(
            ["bash", str(partial_checkout / "scripts/claude-cloud-activate.sh")],
            partial_helper_env,
            expect=3,
        )
        if (partial_checkout / ".lake").exists():
            raise AssertionError("partial setup unexpectedly linked dependency sources")

        # A bad downloaded checksum stays partial and never installs Elan.
        home_bad = base / "home bad checksum"
        home_bad.mkdir()
        bad_root = base / "setup bad checksum"
        bad_calls = base / "lake-calls-bad.txt"
        bad_env = environment(
            mock_bin, home_bad, bad_root, bad_calls, MOCK_BAD_CHECKSUM="1"
        )
        result = run(["bash", str(SETUP)], bad_env)
        bad = status_map(bad_root / "STATUS.txt")
        if bad["state"] != "partial" or bad["elan_status"] == "ready":
            raise AssertionError(f"bad checksum was not treated as incomplete:\n{result.stdout}\n{bad}")

    print("Claude cloud setup smoke tests passed (all network, install, Lake, and Git calls mocked).")


if __name__ == "__main__":
    main()
