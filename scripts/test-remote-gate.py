#!/usr/bin/env python3
"""Real-Git loopback/adversarial fixtures for Issue #982 (never a Lean gate result)."""
from __future__ import annotations

import ast
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
HELPER = ROOT / "scripts/lib/remote-gate.py"
passed = 0
failed = 0


def report(ok: bool, name: str, detail: str = "") -> None:
    global passed, failed
    if ok:
        passed += 1
        print(f"PASS [remote-gate:{name}]")
    else:
        failed += 1
        print(f"FAIL [remote-gate:{name}] {detail}", file=sys.stderr)


def run(command: list[str], *, cwd: Path | None = None, env: dict[str, str] | None = None,
        input_data: bytes | None = None, check: bool = True) -> subprocess.CompletedProcess[bytes]:
    result = subprocess.run(command, cwd=cwd, env=env, input=input_data,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if check and result.returncode != 0:
        raise RuntimeError(f"{command!r} exited {result.returncode}: {result.stderr.decode(errors='replace')}")
    return result


def git(root: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[bytes]:
    return run(["git", "-C", str(root), *args], check=check)


def write_executable(path: Path, text: str) -> None:
    path.write_text(text)
    path.chmod(0o755)


def make_fixture(parent: Path, name: str) -> tuple[Path, str, str]:
    repo = parent / name
    (repo / "scripts/hooks").mkdir(parents=True)
    (repo / "scripts/lib").mkdir(parents=True)
    (repo / "TDA").mkdir()
    (repo / ".agents/scratch").mkdir(parents=True)
    git(repo, "init", "-q") if repo.exists() else None
    # init above needs a directory; create it first and then initialize.
    if not (repo / ".git").exists():
        git(repo, "init", "-q")
    git(repo, "config", "user.name", "remote gate fixture")
    git(repo, "config", "user.email", "remote-gate@example.invalid")
    git(repo, "config", "core.filemode", "true")
    (repo / ".gitignore").write_text(".agents/scratch/\n.lake/\n")
    for source in ("pre-push",):
        (repo / "scripts/hooks" / source).write_bytes((ROOT / "scripts/hooks" / source).read_bytes())
    for source in ("build-change-classifier.py", "build-resources.py", "build-lock.sh",
                   "lake-artifact-cache.sh", "remote-gate.py"):
        target = repo / "scripts/lib" / source
        target.write_bytes((ROOT / "scripts/lib" / source).read_bytes())
        if source == "remote-gate.py":
            target.chmod(0o755)
    for name in ("check-transient-artifacts.sh", "check-conflict-markers.sh", "check-no-sorry.sh",
                 "check-no-custom-axiom.sh", "check-root-aggregator.sh", "check-no-bare-mathlib-import.sh"):
        write_executable(repo / "scripts" / name, "#!/usr/bin/env bash\nexit 0\n")
    gate = """#!/usr/bin/env bash
set -euo pipefail
printf '%s\\n' \"$*\" >> \"$GATE_CALLS\"
case \"${GATE_ACTION:-}\" in
  mutate-source) printf '\\nmutation\\n' >> README.md ;;
  switch-branch) git symbolic-ref HEAD refs/heads/alternate ;;
  verify-lock-fds)
    ROOT="$PWD"
    . "$ROOT/scripts/lib/build-lock.sh"
    count=$(python3 -I scripts/lib/build-resources.py --inherited | wc -l)
    [ "$count" -gt 0 ] || exit 20
    echo "$count" > "$GATE_LOCK_COUNT" ;;
  timeout-term-zero)
    python3 -I -c 'import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(30)' &
    echo $! > \"$GATE_CHILD_PID\"
    trap 'exit 0' TERM
    while :; do sleep 0.1; done ;;
esac
exit \"${GATE_EXIT:-0}\"
"""
    write_executable(repo / "scripts/check.sh", gate)
    (repo / "TDA/Main.lean").write_text("def fixtureLean : True := by trivial\n")
    (repo / "TDA.lean").write_text("import TDA.Main\n")
    (repo / "lakefile.toml").write_text('name = "fixture"\n')
    (repo / "lake-manifest.json").write_text("{}\n")
    (repo / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (repo / "ComparatorChallenge").mkdir()
    (repo / "ComparatorChallenge.lean").write_text("import ComparatorChallenge.Main\n")
    (repo / "ComparatorChallenge/Main.lean").write_text("def comparatorFixture : True := by trivial\n")
    (repo / "comparator.json").write_text("{}\n")
    (repo / "README.md").write_text("fixture\n")
    git(repo, "add", "-A")
    git(repo, "commit", "-qm", "fixture base")
    git(repo, "branch", "-M", "issue-982")
    base = git(repo, "rev-parse", "HEAD").stdout.decode().strip()
    git(repo, "update-ref", "refs/remotes/origin/develop", base)
    (repo / "TDA/Added.lean").write_text("def addedFixture : True := by trivial\n")
    git(repo, "add", "TDA/Added.lean")
    git(repo, "commit", "-qm", "fixture implementation")
    target = git(repo, "rev-parse", "HEAD").stdout.decode().strip()
    tree = git(repo, "rev-parse", "HEAD^{tree}").stdout.decode().strip()
    git(repo, "branch", "alternate", target)
    return repo, base, target


def write_adapter(path: Path) -> None:
    write_executable(path, r'''#!/usr/bin/env python3
import fcntl, json, os, signal, subprocess, sys, time
from pathlib import Path
request, bundle, result, log = sys.argv[1:]
helper = os.environ["TEST_RECEIVER_HELPER"]
checkout = os.environ.get("TEST_EXECUTOR", os.getcwd())
action = os.environ.get("TEST_ADAPTER_ACTION", "")
if action == "adapter-timeout":
    child = subprocess.Popen([sys.executable, "-c", "import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(30)"])
    Path(os.environ["TEST_CHILD_PID"]).write_text(str(child.pid))
    while True: time.sleep(1)
if action == "receiver-lock-timeout":
    lock = subprocess.check_output([sys.executable, "-I", str(Path(checkout) / "scripts/lib/build-resources.py"), "--root-lock", checkout], text=True).strip()
    fd = os.open(lock, os.O_RDWR | os.O_CREAT, 0o600)
    fcntl.flock(fd, fcntl.LOCK_EX)
if action == "cancel-receiver":
    os.chmod(request, 0o600)
    request_obj = json.loads(Path(request).read_text())
    request_obj["timeout_seconds"] = 30
    Path(request).write_text(json.dumps(request_obj, sort_keys=True, separators=(",", ":")) + "\n")
if action == "transport-fail":
    sys.exit(8)
receiver = [sys.executable, "-I", helper, "receive", "--checkout", checkout,
            "--request", request, "--bundle", bundle, "--result", result, "--log", log]
if action == "mutate-request":
    os.chmod(request, 0o600)
    Path(request).write_bytes(Path(request).read_bytes()[:-2] + b',"extra":1}\n')
if action == "duplicate-request":
    os.chmod(request, 0o600)
    raw = Path(request).read_text().rstrip("\n")
    Path(request).write_text(raw[:-1] + ',"gate_mode":"full"}\n')
if action == "dirty-executor":
    with open(Path(checkout) / "README.md", "a") as stream: stream.write("dirty\n")
result_run = subprocess.run(receiver, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
if action == "timeout-allow-result":
    Path(os.environ["TEST_TIMEOUT_RECEIVER_STATUS"]).write_text(str(result_run.returncode))
diag = os.environ.get("TEST_RECEIVER_DIAG")
if diag:
    Path(diag).write_bytes(result_run.stderr)
status = result_run.returncode
if status != 0:
    if action == "receiver-lock-timeout" or (action == "timeout-allow-result" and Path(result).is_file()):
        sys.exit(0)
    sys.exit(status)
if action == "replay":
    second_args = receiver.copy()
    second_args[-3] = result + ".second"
    second_args[-1] = log + ".second"
    second = subprocess.run(second_args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    Path(os.environ["TEST_REPLAY_REJECTED"]).write_text(str(second.returncode) + ":" + second.stderr.decode())
    sys.exit(0 if second.returncode != 0 and b"request ID replay rejected" in second.stderr else 9)
if action == "duplicate-result":
    raw = Path(result).read_text().rstrip("\n")
    Path(result).write_text(raw[:-1] + ',"request_sha256":"' + "0" * 64 + '"}\n')
elif action == "truncate-result":
    Path(result).write_bytes(Path(result).read_bytes()[:20])
elif action == "missing-result":
    Path(result).unlink()
elif action == "missing-field":
    value = json.loads(Path(result).read_text())
    value.pop("gate_log_sha256")
    Path(result).write_text(json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n")
elif action == "extra-field":
    value = json.loads(Path(result).read_text())
    value["unexpected"] = True
    Path(result).write_text(json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n")
elif action == "tamper-bundle":
    os.chmod(bundle, 0o600)
    with open(bundle, "ab") as stream: stream.write(b"tamper")
elif action == "symlink-log":
    Path(log).unlink(); Path(log).symlink_to(Path(os.environ["TEST_SYMLINK_TARGET"]))
elif action == "tamper-log":
    with open(log, "ab") as stream: stream.write(b"tamper\n")
elif action.startswith("wrong-") or action == "bool-exit":
    value = json.loads(Path(result).read_text())
    field = action[6:] if action.startswith("wrong-") else "gate_exit_code"
    if field == "request":
        Path(request).write_text(json.dumps({**json.loads(Path(request).read_text()), "gate_mode":"full"}, separators=(",", ":")) + "\n")
    else:
        replacements = {
          "request_id": "0" * 64, "commit": "0" * len(value["commit"]),
          "tree": "0" * len(value["tree"]), "gate_mode": "full",
          "source_bundle_sha256": "0" * 64, "gate_code_sha256": "0" * 64,
          "argv": ["bash", "-c", "exit 0"], "request_sha256": "0" * 64,
          "timeout_seconds": 2,
        }
        if action == "bool-exit": value["gate_exit_code"] = True
        elif field == "argv": value["gate_argv"] = replacements[field]
        elif field.startswith("ref-"):
            ref_value = {"ref-null": None, "ref-list": [], "ref-bool": True,
                         "ref-main": "refs/heads/main"}[field]
            value["executor_ref_before"] = ref_value
            value["executor_ref_after"] = ref_value
        elif field == "request":
            Path(request).write_text(json.dumps({**json.loads(Path(request).read_text()), "gate_mode":"full"}, separators=(",", ":")) + "\n")
        else: value[field] = replacements.get(field, value.get(field))
        value.pop("result_sha256", None)
        canonical = json.dumps(value, sort_keys=True, separators=(",", ":"))
        import hashlib
        value["result_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
        Path(result).write_text(json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n")
sys.exit(0)
''')


def hook(repo: Path, base: str, target: str, env_extra: dict[str, str] | None = None,
         *, remote_ref: str = "refs/heads/topic", remote_oid: str | None = None) -> subprocess.CompletedProcess[bytes]:
    env = dict(os.environ)
    env.update({"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1", "TDA_STABLE_RELEASE": "0",
                "GATE_CALLS": str(repo / ".gate-calls"), "XDG_CACHE_HOME": str(repo.parent / "cache"),
                "LAKE_CACHE_DIR": str(repo.parent / "lake-artifact-cache"),
                "TEST_RECEIVER_HELPER": str(repo / "scripts/lib/remote-gate.py"),
                "TEST_RECEIVER_DIAG": str(repo.parent / "receiver-diag.txt")})
    if env_extra:
        env.update(env_extra)
    zero = "0" * len(target)
    payload = f"refs/heads/topic {target} {remote_ref} {remote_oid or base}\n".encode()
    return run(["bash", "scripts/hooks/pre-push"], cwd=repo, env=env, input_data=payload, check=False)


def configured_repo(parent: Path, name: str, adapter: Path) -> tuple[Path, str, str]:
    repo, base, target = make_fixture(parent, name)
    git(repo, "config", "--local", "tda.remoteGate.adapter", str(adapter))
    return repo, base, target


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="remote-gate-tests-") as temp_name:
        temp = Path(temp_name)
        adapter = temp / "adapter.py"
        write_adapter(adapter)

        helper_tree = ast.parse(HELPER.read_text())
        owned_gate = next(node for node in helper_tree.body if isinstance(node, ast.FunctionDef) and node.name == "run_owned_gate")
        gate_calls = [node for node in ast.walk(owned_gate) if isinstance(node, ast.Call)]
        block_line = min(node.lineno for node in gate_calls if isinstance(node.func, ast.Attribute) and
                         node.func.attr == "pthread_sigmask" and node.args and
                         isinstance(node.args[0], ast.Attribute) and node.args[0].attr == "SIG_BLOCK")
        spawn_line = min(node.lineno for node in gate_calls if isinstance(node.func, ast.Attribute) and node.func.attr == "Popen")
        gate_popen = next(node for node in gate_calls if isinstance(node.func, ast.Attribute) and node.func.attr == "Popen")
        restores_child_mask = any(keyword.arg == "preexec_fn" for keyword in gate_popen.keywords)
        owned_line = min(node.lineno for node in ast.walk(owned_gate) if isinstance(node, ast.Assign) and
                         any(isinstance(target, ast.Name) and target.id == "active_gate" for target in node.targets))
        unmask_line = min(node.lineno for node in gate_calls if isinstance(node.func, ast.Attribute) and
                          node.func.attr == "pthread_sigmask" and node.args and
                          isinstance(node.args[0], ast.Attribute) and node.args[0].attr == "SIG_SETMASK")
        unmask_line = min(node.lineno for node in gate_calls if node.lineno > owned_line and
                          isinstance(node.func, ast.Attribute) and node.func.attr == "pthread_sigmask" and node.args and
                          isinstance(node.args[0], ast.Attribute) and node.args[0].attr == "SIG_SETMASK")
        report(block_line < spawn_line < owned_line < unmask_line and restores_child_mask,
               "receiver_blocks_cancellation_until_gate_is_owned_then_restores_child_mask",
               f"block={block_line}, spawn={spawn_line}, own={owned_line}, unmask={unmask_line}, child_mask={restores_child_mask}")

        repo, base, target = configured_repo(temp, "happy", adapter)
        result = hook(repo, base, target)
        report(result.returncode == 0, "real_git_loopback_runs_canonical_incremental", result.stderr.decode(errors="replace"))
        calls = (repo / ".gate-calls").read_text() if (repo / ".gate-calls").exists() else ""
        report(calls.strip() == "--incremental", "loopback_uses_only_canonical_gate_argv", calls)
        report(b"remote incremental gate passed" in result.stdout, "client_accepts_bound_result", result.stdout.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "lock-inheritance", adapter)
        lock_count = temp / "inherited-lock-count"
        result = hook(repo, base, target, {"GATE_ACTION": "verify-lock-fds", "GATE_LOCK_COUNT": str(lock_count)})
        report(result.returncode == 0 and lock_count.exists() and int(lock_count.read_text()) > 0,
               "canonical_gate_inherits_verified_resource_locks", result.stderr.decode(errors="replace"))

        # Stale/hostile executor states are tested on real Git trees and never run the stub gate.
        repo, base, target = configured_repo(temp, "wrong-head-source", adapter)
        tree = git(repo, "rev-parse", f"{target}^{{tree}}").stdout.decode().strip()
        alt = git(repo, "commit-tree", tree, "-p", base, "-m", "different commit same tree").stdout.decode().strip()
        wrong = temp / "wrong-head-checkout"
        git(repo, "update-ref", "refs/heads/alternate-same-tree", alt)
        run(["git", "clone", "-q", str(repo), str(wrong)])
        git(wrong, "checkout", "-q", "alternate-same-tree")
        wrong_diag = temp / "wrong-head-diagnostic.txt"
        result = hook(repo, base, target, {"TEST_EXECUTOR": str(wrong),
                          "TEST_RECEIVER_HELPER": str(wrong / "scripts/lib/remote-gate.py"),
                          "GATE_CALLS": str(wrong / ".gate-calls"),
                          "TEST_RECEIVER_DIAG": str(wrong_diag)})
        report(result.returncode != 0 and wrong_diag.exists() and
               b"executor HEAD commit does not match requested commit" in wrong_diag.read_bytes() and
               not (wrong / ".gate-calls").exists(), "same_tree_different_head_rejected", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "mutated", adapter)
        result = hook(repo, base, target, {"GATE_ACTION": "mutate-source"})
        diag = (repo.parent / "receiver-diag.txt").read_bytes()
        calls = (repo / ".gate-calls").read_text().splitlines() if (repo / ".gate-calls").exists() else []
        report(result.returncode != 0 and b"raw tracked bytes changed" in diag and calls == ["--incremental"],
               "executor_source_mutation_during_gate_rejected", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "branch-change", adapter)
        result = hook(repo, base, target, {"GATE_ACTION": "switch-branch"})
        diag = (repo.parent / "receiver-diag.txt").read_bytes()
        calls = (repo / ".gate-calls").read_text().splitlines() if (repo / ".gate-calls").exists() else []
        report(result.returncode != 0 and b"branch identity changed during gate" in diag and calls == ["--incremental"],
               "same_commit_branch_identity_change_rejected", result.stderr.decode(errors="replace"))

        bad_modes = ["wrong-request_id", "wrong-commit", "wrong-tree", "wrong-gate_mode",
                     "wrong-source_bundle_sha256", "wrong-gate_code_sha256", "wrong-argv",
                     "wrong-ref-null", "wrong-ref-list", "wrong-ref-bool", "wrong-ref-main",
                     "wrong-request_sha256", "wrong-timeout_seconds", "bool-exit",
                     "duplicate-result", "truncate-result", "missing-result", "missing-field", "extra-field",
                     "tamper-log", "symlink-log", "tamper-bundle"]
        expected_failure = {
            "wrong-request_id": "result does not match request field request_id",
            "wrong-commit": "result does not match request field commit",
            "wrong-tree": "result does not match request field tree",
            "wrong-gate_mode": "result does not match request field gate_mode",
            "wrong-source_bundle_sha256": "result does not match request field source_bundle_sha256",
            "wrong-gate_code_sha256": "result does not match request field gate_code_sha256",
            "wrong-argv": "noncanonical gate invocation",
            "wrong-request_sha256": "result request digest mismatch",
            "wrong-timeout_seconds": "result does not match request field timeout_seconds",
            "wrong-ref-null": "executor ref must be a string",
            "wrong-ref-list": "executor ref must be a string",
            "wrong-ref-bool": "executor ref must be a string",
            "wrong-ref-main": "executor ref cannot be refs/heads/main",
            "bool-exit": "gate exit code is not an integer",
            "duplicate-result": "duplicate JSON field",
            "truncate-result": "cannot read protocol JSON",
            "missing-result": "cannot read protocol JSON",
            "missing-field": "result fields do not match",
            "extra-field": "result fields do not match",
            "tamper-log": "returned gate log digest mismatch",
            "symlink-log": "bounded regular gate log",
            "tamper-bundle": "adapter changed the source bundle",
        }
        for action in bad_modes:
            repo, base, target = configured_repo(temp, "bad-" + action.replace("_", "-"), adapter)
            result = hook(repo, base, target, {"TEST_ADAPTER_ACTION": action,
                          "TEST_SYMLINK_TARGET": str(temp / "nonexistent-log-target")})
            calls = (repo / ".gate-calls").read_text().splitlines() if (repo / ".gate-calls").exists() else []
            expected_calls = ["--incremental"]
            report(result.returncode != 0 and calls == expected_calls and expected_failure[action].encode() in result.stderr,
                   action.replace("_", "-") + "-rejected-after-expected-stage", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "transport-failure", adapter)
        result = hook(repo, base, target, {"TEST_ADAPTER_ACTION": "transport-fail"})
        report(result.returncode != 0 and not (repo / ".gate-calls").exists(),
               "nonzero_transport_exit_rejected", result.stderr.decode(errors="replace"))

        for action in ("mutate-request", "duplicate-request", "dirty-executor"):
            repo, base, target = configured_repo(temp, "request-" + action, adapter)
            result = hook(repo, base, target, {"TEST_ADAPTER_ACTION": action})
            diag = (repo.parent / "receiver-diag.txt").read_bytes()
            expected = {"mutate-request": b"request fields do not match",
                        "duplicate-request": b"duplicate JSON field",
                        "dirty-executor": b"raw tracked bytes changed"}[action]
            report(result.returncode != 0 and expected in diag and not (repo / ".gate-calls").exists(),
                   action.replace("_", "-") + "-rejected-before-gate", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "gate-failure", adapter)
        result = hook(repo, base, target, {"GATE_EXIT": "9"})
        report(result.returncode != 0, "nonzero_gate_exit_rejected", result.stderr.decode(errors="replace"))
        calls = (repo / ".gate-calls").read_text().splitlines() if (repo / ".gate-calls").exists() else []
        report(calls == ["--incremental"], "configured_gate_failure_never_falls_back", repr(calls))

        repo, base, target = configured_repo(temp, "replay", adapter)
        marker = temp / "replay-rejected"
        result = hook(repo, base, target, {"TEST_ADAPTER_ACTION": "replay", "TEST_REPLAY_REJECTED": str(marker)})
        report(result.returncode == 0 and marker.exists() and "request ID replay rejected" in marker.read_text(),
               "receiver_rejects_request_replay", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "full-mode", adapter)
        git(repo, "update-ref", "-d", "refs/remotes/origin/develop")
        result = hook(repo, base, target, {"TEST_ADAPTER_ACTION": ""}, remote_oid="0" * len(target))
        calls = (repo / ".gate-calls").read_text() if (repo / ".gate-calls").exists() else ""
        report(result.returncode == 0 and calls == "\n" and b"remote full gate passed" in result.stdout,
               "hook_without_base_runs_canonical_full_mode", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "timeout-trap", adapter)
        gate_child = temp / "gate-child.pid"
        timeout_receiver_status = temp / "timeout-receiver-status"
        result = hook(repo, base, target, {"TDA_REMOTE_GATE_TIMEOUT_SECONDS": "1", "GATE_ACTION": "timeout-term-zero",
                                           "TEST_ADAPTER_ACTION": "timeout-allow-result",
                                           "GATE_CHILD_PID": str(gate_child),
                                           "TEST_TIMEOUT_RECEIVER_STATUS": str(timeout_receiver_status)})
        cleaned = False
        if gate_child.exists():
            pid = int(gate_child.read_text())
            for _ in range(30):
                try:
                    state = Path(f"/proc/{pid}/stat").read_text().split()[2]
                    if state == "Z":
                        cleaned = True
                        break
                except FileNotFoundError:
                    cleaned = True
                    break
                time.sleep(0.1)
        report(result.returncode != 0 and cleaned and timeout_receiver_status.read_text() != "0" and
               b"canonical remote gate timed out" in result.stderr,
               "term_trap_zero_exit_cannot_pass_and_gate_descendant_is_cleaned",
               result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "lock-timeout", adapter)
        result = hook(repo, base, target, {"TDA_REMOTE_GATE_TIMEOUT_SECONDS": "1", "TEST_ADAPTER_ACTION": "receiver-lock-timeout"})
        diag = (repo.parent / "receiver-diag.txt").read_bytes()
        report(result.returncode != 0 and b"deadline expired while waiting for resource locks" in diag and
               not (repo / ".gate-calls").exists(), "receiver_deadline_includes_lock_wait", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "adapter-timeout", adapter)
        pidfile = temp / "timeout-child.pid"
        result = hook(repo, base, target, {"TDA_REMOTE_GATE_TIMEOUT_SECONDS": "1", "TEST_ADAPTER_ACTION": "adapter-timeout",
                                           "TEST_CHILD_PID": str(pidfile)})
        cleaned = False
        if pidfile.exists():
            pid = int(pidfile.read_text())
            for _ in range(30):
                try:
                    state = Path(f"/proc/{pid}/stat").read_text().split()[2]
                    if state == "Z":
                        cleaned = True
                        break
                except FileNotFoundError:
                    cleaned = True
                    break
                time.sleep(0.1)
        report(result.returncode != 0 and cleaned, "timeout_kills_only_owned_process_group", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "client-sigterm", adapter)
        pidfile = temp / "client-cancel-gate-child.pid"
        env = dict(os.environ)
        env.update({"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
                    "TEST_RECEIVER_HELPER": str(repo / "scripts/lib/remote-gate.py"),
                    "TEST_ADAPTER_ACTION": "cancel-receiver", "GATE_ACTION": "timeout-term-zero",
                    "GATE_CHILD_PID": str(pidfile), "TDA_REMOTE_GATE_TIMEOUT_SECONDS": "30",
                    "GATE_CALLS": str(repo / ".gate-calls"), "XDG_CACHE_HOME": str(temp / "cache"),
                    "LAKE_CACHE_DIR": str(temp / "lake-artifact-cache")})
        client_process = subprocess.Popen([sys.executable, "-I", str(HELPER), "client", "--mode", "incremental",
                                           "--commit", target], cwd=repo, env=env,
                                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        for _ in range(100):
            if pidfile.exists():
                break
            if client_process.poll() is not None:
                break
            time.sleep(0.05)
        if pidfile.exists() and client_process.poll() is None:
            client_process.send_signal(signal.SIGTERM)
        client_stdout, client_stderr = client_process.communicate(timeout=15)
        child_cleaned = False
        child_state_value = "gate child PID file missing"
        if pidfile.exists():
            child_pid = int(pidfile.read_text())
            child_state_value = f"pid={child_pid}, state=unknown"
            for _ in range(40):
                try:
                    child_state = Path(f"/proc/{child_pid}/stat").read_text().split()[2]
                    child_state_value = f"pid={child_pid}, state={child_state}"
                    if child_state == "Z":
                        child_cleaned = True
                        break
                except FileNotFoundError:
                    child_cleaned = True
                    break
                time.sleep(0.1)
        report(client_process.returncode != 0 and child_cleaned and
               b"client interrupted by signal" in client_stderr,
               "client_sigterm_cleans_adapter_receiver_and_gate_groups",
               f"returncode={client_process.returncode}, cleaned={child_cleaned}, {child_state_value}; " +
               client_stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "broken-config", adapter)
        git(repo, "config", "--local", "--unset-all", "tda.remoteGate.adapter")
        git(repo, "config", "--local", "tda.remoteGate.adapter", str(repo / "tracked-but-not-adapter"))
        result = hook(repo, base, target)
        report(result.returncode != 0 and not (repo / ".gate-calls").exists(), "broken_config_fails_closed_without_local_gate", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "stop-file", adapter)
        stop = temp / "codex-stop"
        stop.write_text("stop fixture\n")
        result = hook(repo, base, target, {"CODEX_STOP_FILE": str(stop)})
        diag = (repo.parent / "receiver-diag.txt").read_bytes()
        report(result.returncode != 0 and b"executor stopped by" in diag and not (repo / ".gate-calls").exists(),
               "configured_stop_file_blocks_receiver_before_gate", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "adapter-in-source", adapter)
        git(repo, "config", "--local", "--unset-all", "tda.remoteGate.adapter")
        git(repo, "config", "--local", "tda.remoteGate.adapter", str(repo / "scripts/check.sh"))
        result = hook(repo, base, target)
        report(result.returncode != 0 and not (repo / ".gate-calls").exists(),
               "adapter_inside_worktree_rejected", result.stderr.decode(errors="replace"))

        repo, base, target = configured_repo(temp, "adapter-in-other-worktree", adapter)
        other = temp / "adapter-other-worktree"
        git(repo, "worktree", "add", "-q", "-b", "adapter-worktree", str(other), target)
        other_adapter = other / "external-adapter"
        write_executable(other_adapter, adapter.read_text())
        git(repo, "config", "--local", "--unset-all", "tda.remoteGate.adapter")
        git(repo, "config", "--local", "tda.remoteGate.adapter", str(other_adapter))
        result = hook(repo, base, target)
        report(result.returncode != 0 and not (repo / ".gate-calls").exists(),
               "adapter_inside_another_worktree_rejected", result.stderr.decode(errors="replace"))

        repo, base, target = make_fixture(temp, "stable-no-adapter-lookup")
        git(repo, "config", "--local", "tda.remoteGate.adapter", str(repo / "missing"))
        git(repo, "tag", "-a", "v-test", "-m", "stable fixture", target)
        tag = git(repo, "rev-parse", "refs/tags/v-test").stdout.decode().strip()
        result = hook(repo, base, target, {"TDA_STABLE_RELEASE": "0"}, remote_ref="refs/tags/v-test")
        report(result.returncode == 0 and "--stable" in (repo / ".gate-calls").read_text(),
               "stable_path_keeps_local_gate_without_adapter_lookup", result.stderr.decode(errors="replace"))

        repo, base, target = make_fixture(temp, "delete-no-adapter-lookup")
        git(repo, "config", "--local", "tda.remoteGate.adapter", str(repo / "missing"))
        deleted = "0" * len(target)
        result = hook(repo, base, deleted)
        report(result.returncode == 0 and not (repo / ".gate-calls").exists(),
               "deletion_path_never_looks_up_adapter", result.stderr.decode(errors="replace"))

        repo, base, target = make_fixture(temp, "prose-no-adapter-lookup")
        git(repo, "config", "--local", "tda.remoteGate.adapter", str(repo / "missing"))
        (repo / "README.md").write_text("prose only\n")
        git(repo, "add", "README.md")
        git(repo, "commit", "-qm", "prose")
        prose = git(repo, "rev-parse", "HEAD").stdout.decode().strip()
        result = hook(repo, target, prose, remote_oid=target)
        report(result.returncode == 0 and not (repo / ".gate-calls").exists(),
               "prose_path_never_looks_up_adapter", result.stderr.decode(errors="replace"))

    print(f"remote-gate real-Git fixtures: {passed} passed, {failed} failed (stub gates only; no Lean/sandbox result)")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
