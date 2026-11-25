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
SKILL_NAMES = ("github-driven-workflow", "github-loop-engineering", "lean-formalization-discipline")
# Filled in by main() with the offline fixture repository standing in for t-uda/skills.
SKILLS_ENV: dict[str, str] = {}


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
  [[ -f "$HOME/.elan/fake-toolchain" ]] && echo 'leanprover/lean4:v4.35.0'
  exit 0
fi
if [[ "$1" == toolchain && "$2" == install ]]; then
  mkdir -p "$HOME/.elan/toolchains"
  touch "$HOME/.elan/fake-toolchain"
  exit 0
fi
if [[ "$1" == run && "$3" == lean && "$4" == --version ]]; then
  [[ "${MOCK_LEAN_VERSION_FAIL:-0}" == 1 ]] && echo 'Lean (version 4.33.0, mock)' && exit 0
  echo 'Lean (version 4.35.0, mock)'
  exit 0
fi
if [[ "$1" == run && "$3" == lake && "$4" == --version ]]; then
  [[ "${MOCK_LEAN_VERSION_FAIL:-0}" == 1 ]] && echo 'Lake version 5 (Lean version 4.33.0)' && exit 0
  echo 'Lake version 5 (Lean version 4.35.0)'
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
if [[ "$1" == -C && "$3" == rev-parse && "$4" == HEAD && "$2" == */skills-src && -n "${MOCK_SKILLS_HEAD:-}" ]]; then
  echo "$MOCK_SKILLS_HEAD"
  exit 0
fi
if [[ "$1" == -C && "$3" == rev-parse && "$4" == HEAD && "$2" == */.lake/packages/* ]]; then
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


def write_sandbox_bin(directory: Path, *, bwrap: bool = False, apt: str | None = None) -> Path:
    """Tools visible to the sandbox stage: an optional bwrap and an optional mocked apt-get.

    `apt="install"` creates bwrap beside itself on `install`; `apt="fail"` exits nonzero.
    """
    directory.mkdir(parents=True)
    if bwrap:
        path = directory / "bwrap"
        path.write_text("#!/usr/bin/env bash\nexit 0\n")
        path.chmod(0o755)
    if apt is not None:
        path = directory / "apt-get"
        path.write_text(r'''#!/usr/bin/env bash
set -e
here="$(cd "$(dirname "$0")" && pwd)"
printf '%s|%s\n' "${DEBIAN_FRONTEND:-unset}" "$*" >> "$here/apt-calls.txt"
[[ "${MOCK_APT_FAIL:-0}" == 1 ]] && exit 100
if [[ "$1" == install ]]; then
  printf '#!/usr/bin/env bash\nexit 0\n' > "$here/bwrap"
  chmod +x "$here/bwrap"
fi
''')
        path.chmod(0o755)
    return directory


def environment(mock_bin: Path, home: Path, setup_root: Path, calls: Path, **extra: str) -> dict[str, str]:
    env = os.environ.copy()
    env.update(
        HOME=str(home),
        PATH=f"{mock_bin}:/usr/bin:/bin",
        # Never let the sandbox stage see the host's bwrap or run its real apt-get.
        TDA_CLAUDE_SETUP_SANDBOX_PATH=str(mock_bin.parent / "sandbox-present"),
        TDA_CLAUDE_SETUP_ROOT=str(setup_root),
        MOCK_PROJECT=str(setup_root / "project"),
        MOCK_LAKE_CALLS=str(calls),
    )
    env.update(SKILLS_ENV)
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


def make_skills_fixture(directory: Path) -> str:
    """A local stand-in for t-uda/skills with the three skills and an install-skill.sh.

    The fixture installer follows the real interface (`<skill> claude <root> --copy`,
    exit 2 on an existing target); no test reaches the network. Returns the commit id.
    """
    (directory / "scripts").mkdir(parents=True)
    for name in SKILL_NAMES:
        (directory / "skills" / name / "references").mkdir(parents=True)
        (directory / "skills" / name / "SKILL.md").write_text(f"---\nname: {name}\n---\nfixture\n")
        (directory / "skills" / name / "references/notes.md").write_text("notes\n")
    installer = directory / "scripts/install-skill.sh"
    installer.write_text(r'''#!/usr/bin/env sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
skill=$1; target=$2; root=$3; mode=$4
[ "$target" = claude ] && [ "$mode" = --copy ]
dest="$root/.claude/skills/$skill"
if [ -e "$dest" ] || [ -L "$dest" ]; then echo "warning: refusing to replace $dest" >&2; exit 2; fi
mkdir -p "$root/.claude/skills"
cp -R "$here/../skills/$skill" "$dest"
echo "Copied $skill -> $dest"
''')
    installer.chmod(0o755)
    git_env = os.environ | {
        "GIT_AUTHOR_NAME": "fixture", "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
        "GIT_COMMITTER_NAME": "fixture", "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
    }
    for args in (["init", "--quiet"], ["add", "."], ["commit", "--quiet", "-m", "fixture"]):
        subprocess.run(["/usr/bin/git", "-C", str(directory), *args], env=git_env, check=True,
                       capture_output=True)
    return subprocess.run(
        ["/usr/bin/git", "-C", str(directory), "rev-parse", "HEAD"],
        env=git_env, check=True, capture_output=True, text=True,
    ).stdout.strip()


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
        write_sandbox_bin(base / "sandbox-present", bwrap=True)
        skills_repo = base / "skills-fixture"
        skills_commit = make_skills_fixture(skills_repo)
        SKILLS_ENV.update(
            TDA_CLAUDE_SETUP_SKILLS_URL=str(skills_repo),
            TDA_CLAUDE_SETUP_SKILLS_COMMIT=skills_commit,
        )

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
        if status["sandbox_status"] != "ready" or "sandbox=ready" not in result.stdout:
            raise AssertionError(f"an installed bwrap was not reported ready:\n{result.stdout}\n{status}")
        if (setup_root / "logs/bubblewrap-install.log").exists():
            raise AssertionError("setup ran an install although bwrap was already present")
        if "sandbox_status" not in (setup_root / "INSTRUCTIONS.txt").read_text():
            raise AssertionError("instructions do not say where the sandbox status is recorded")
        instructions = (setup_root / "INSTRUCTIONS.txt").read_text()
        if "skills_status" not in instructions or "GIT_OPTIONAL_LOCKS=0" not in instructions:
            raise AssertionError("instructions do not cover the skills status and GIT_OPTIONAL_LOCKS=0")

        # The companion skills are copied at the pinned commit, recorded separately and bounded.
        if (status["skills_status"], status["skills_commit_requested"], status["skills_commit_found"]) != (
                "ready", skills_commit, skills_commit) or "skills=ready" not in result.stdout:
            raise AssertionError(f"skills stage was not recorded as ready at the pin:\n{result.stdout}\n{status}")
        if not status["skills_seconds"].isdigit() or not status["skills_detail"]:
            raise AssertionError(f"skills stage has no elapsed-time or detail record: {status}")
        installed_skills = home / ".claude/skills"
        for name in SKILL_NAMES:
            skill_dir = installed_skills / name
            if status[f"skill_{name}"] != "installed" or skill_dir.is_symlink() or \
                    not (skill_dir / "SKILL.md").is_file() or not (skill_dir / "references/notes.md").is_file():
                raise AssertionError(f"skill {name} was not copied as a real directory: {status}")
        if (setup_root / "tmp/skills-src").exists():
            raise AssertionError("the temporary skills clone was left behind")

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
        if rerun_status["skills_status"] != "ready" or any(
                rerun_status[f"skill_{name}"] != "present" for name in SKILL_NAMES):
            raise AssertionError(f"skills rerun did not recognise its own copies:\n{rerun_status}")

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
        if partial["sandbox_status"] != "ready":
            raise AssertionError(f"sandbox stage did not run after a failed cache:\n{result.stdout}\n{partial}")
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

        # The sandbox stage never changes the cache state. A missing bwrap is installed through
        # apt-get when that works, and is otherwise reported without failing the setup.
        sandbox_cases = [
            ("install", write_sandbox_bin(base / "sandbox-install", apt="install"), {}, "ready"),
            ("apt failure", write_sandbox_bin(base / "sandbox-apt-fail", apt="fail"),
             {"MOCK_APT_FAIL": "1"}, "incomplete"),
            ("no apt", write_sandbox_bin(base / "sandbox-empty"), {}, "unavailable"),
        ]
        for label, sandbox_bin, extra, expected in sandbox_cases:
            case_home = base / f"home sandbox {label}"
            case_home.mkdir()
            case_root = base / f"setup sandbox {label}"
            case_env = environment(
                mock_bin, case_home, case_root, base / f"lake-calls-sandbox-{label}.txt",
                TDA_CLAUDE_SETUP_SANDBOX_PATH=str(sandbox_bin), **extra,
            )
            result = run(["bash", str(SETUP)], case_env)
            case_status = status_map(case_root / "STATUS.txt")
            if case_status["state"] != "warm" or case_status["sandbox_status"] != expected:
                raise AssertionError(
                    f"sandbox case {label!r}: expected warm/{expected}:\n{result.stdout}\n{case_status}"
                )
            apt_calls = sandbox_bin / "apt-calls.txt"
            if label == "install":
                if apt_calls.read_text().splitlines() != [
                    "noninteractive|update",
                    "noninteractive|install -y --no-install-recommends bubblewrap",
                ]:
                    raise AssertionError(f"unexpected apt-get calls:\n{apt_calls.read_text()}")
            elif label == "apt failure":
                if apt_calls.read_text().splitlines() != ["noninteractive|update"]:
                    raise AssertionError(f"install continued after a failed update:\n{apt_calls.read_text()}")
                if "exit 100" not in case_status["sandbox_detail"]:
                    raise AssertionError(f"apt-get failure was not recorded: {case_status}")
            elif apt_calls.exists():
                raise AssertionError("apt-get ran although none was available")

        # Skills cases. Each starts from an empty home; the skills result never changes the
        # cache state, in either direction.
        def skills_case(label: str, *, expect_state: str, extra: dict[str, str] | None = None,
                        prepare=None) -> tuple[dict[str, str], Path]:
            case_home = base / f"home skills {label}"
            case_home.mkdir()
            if prepare is not None:
                prepare(case_home)
            case_root = base / f"setup skills {label}"
            case_env = environment(
                mock_bin, case_home, case_root, base / f"lake-calls-skills-{label}.txt", **(extra or {})
            )
            run(["bash", str(SETUP)], case_env)
            case_status = status_map(case_root / "STATUS.txt")
            if case_status["state"] != expect_state:
                raise AssertionError(f"skills case {label!r}: state {case_status['state']}: {case_status}")
            return case_status, case_home

        # A checked-out commit that differs from the pin copies nothing.
        mismatch_status, mismatch_home = skills_case(
            "pin mismatch", expect_state="warm", extra={"MOCK_SKILLS_HEAD": "0" * 40}
        )
        if mismatch_status["skills_status"] != "incomplete" or "does not match the pin" not in mismatch_status["skills_detail"]:
            raise AssertionError(f"pin mismatch was not recorded: {mismatch_status}")
        if mismatch_status["skills_commit_found"] != "0" * 40 or (mismatch_home / ".claude").exists():
            raise AssertionError(f"pin mismatch still copied skills: {mismatch_status}")

        # An unreachable source (offline) and an absent pinned commit are recorded, not fatal.
        offline_status, offline_home = skills_case(
            "offline", expect_state="warm",
            extra={"TDA_CLAUDE_SETUP_SKILLS_URL": str(base / "no-such-skills-repo")},
        )
        if offline_status["skills_status"] != "incomplete" or "clone or checkout" not in offline_status["skills_detail"]:
            raise AssertionError(f"offline skills clone was not recorded: {offline_status}")
        if (offline_home / ".claude").exists() or offline_status["skill_github-driven-workflow"] != "not-attempted":
            raise AssertionError(f"offline skills stage left residue: {offline_status}")
        absent_status, _ = skills_case(
            "absent pin", expect_state="warm", extra={"TDA_CLAUDE_SETUP_SKILLS_COMMIT": "1" * 40}
        )
        if absent_status["skills_status"] != "incomplete":
            raise AssertionError(f"absent pinned commit was not recorded: {absent_status}")
        branch_status, _ = skills_case(
            "branch pin", expect_state="warm", extra={"TDA_CLAUDE_SETUP_SKILLS_COMMIT": "main"}
        )
        if branch_status["skills_status"] != "blocked":
            raise AssertionError(f"a non-commit pin was accepted: {branch_status}")

        # A different existing skill directory is never replaced; the others are still copied.
        def prepare_conflict(case_home: Path) -> None:
            existing = case_home / ".claude/skills/github-loop-engineering"
            existing.mkdir(parents=True)
            (existing / "SKILL.md").write_text("local edit\n")

        conflict_status, conflict_home = skills_case(
            "conflict", expect_state="warm", prepare=prepare_conflict
        )
        kept = conflict_home / ".claude/skills/github-loop-engineering/SKILL.md"
        if conflict_status["skills_status"] != "conflict" or conflict_status["skill_github-loop-engineering"] != "conflict":
            raise AssertionError(f"skill conflict was not recorded: {conflict_status}")
        if kept.read_text() != "local edit\n" or conflict_status["skill_github-driven-workflow"] != "installed":
            raise AssertionError(f"conflict handling replaced or skipped the wrong skill: {conflict_status}")

        # A failed cache with healthy skills is partial while the skills stay ready.
        cold_status, _ = skills_case("cold cache", expect_state="partial", extra={"MOCK_LAKE_FAIL": "1"})
        if cold_status["skills_status"] != "ready":
            raise AssertionError(f"a failed cache changed the skills result: {cold_status}")

    print("Claude cloud setup smoke tests passed (all network, install, Lake, and Git calls mocked).")


if __name__ == "__main__":
    main()
