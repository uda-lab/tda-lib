#!/usr/bin/env python3
"""Versioned, argv-only pre-push gate transport contract (Issue #982).

The explicitly configured adapter is trusted transport. This protocol binds one request and
one canonical gate execution; it is not cryptographic executor attestation.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import secrets
import signal
import stat
import subprocess
import sys
import tempfile
import time
from typing import Any

PROTOCOL = "tda.remote-gate/v1"
CONFIG_KEY = "tda.remoteGate.adapter"
REQUEST_FIELDS = {
    "protocol_version", "request_id", "gate_mode", "commit", "tree",
    "source_bundle_sha256", "gate_code_sha256", "timeout_seconds",
}
RESULT_FIELDS = REQUEST_FIELDS | {
    "request_sha256", "executor_head_before", "executor_tree_before", "executor_ref_before",
    "executor_head_after", "executor_tree_after", "executor_ref_after", "gate_argv", "gate_exit_code",
    "gate_timed_out",
    "gate_log_sha256", "result_sha256",
}
OID_LENGTHS = {40, 64}
DEFAULT_TIMEOUT = 7200
MAX_TIMEOUT = 7200
MAX_RESULT_BYTES = 256 * 1024
MAX_LOG_BYTES = 128 * 1024 * 1024


class ProtocolError(Exception):
    pass


class Unconfigured(Exception):
    pass


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode("ascii")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ProtocolError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def read_json(path: Path, maximum: int) -> tuple[dict[str, Any], bytes]:
    try:
        info = path.lstat()
        if not stat.S_ISREG(info.st_mode) or info.st_size > maximum:
            raise ProtocolError("protocol file is not a bounded regular file")
        raw = path.read_bytes()
        value = json.loads(raw.decode("utf-8"), object_pairs_hook=reject_duplicate_pairs)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ProtocolError(f"cannot read protocol JSON: {error}") from error
    if not isinstance(value, dict):
        raise ProtocolError("protocol JSON must be an object")
    return value, raw


def validate_hex(value: Any, lengths: set[int], label: str) -> str:
    if not isinstance(value, str) or len(value) not in lengths or any(c not in "0123456789abcdef" for c in value):
        raise ProtocolError(f"invalid {label}")
    return value


def validate_request(value: Any) -> dict[str, Any]:
    if set(value) != REQUEST_FIELDS:
        raise ProtocolError("request fields do not match the v1 schema")
    if value["protocol_version"] != PROTOCOL:
        raise ProtocolError("unsupported request protocol")
    validate_hex(value["request_id"], {64}, "request ID")
    validate_hex(value["commit"], OID_LENGTHS, "commit ID")
    validate_hex(value["tree"], OID_LENGTHS, "tree ID")
    validate_hex(value["source_bundle_sha256"], {64}, "source bundle digest")
    validate_hex(value["gate_code_sha256"], {64}, "gate code digest")
    if not isinstance(value["gate_mode"], str) or value["gate_mode"] not in {"incremental", "full"}:
        raise ProtocolError("ordinary remote gate mode must be incremental or full")
    if type(value["timeout_seconds"]) is not int or not 1 <= value["timeout_seconds"] <= MAX_TIMEOUT:
        raise ProtocolError("invalid request timeout")
    return value


def git_env(source: dict[str, str] | None = None) -> dict[str, str]:
    env = dict(os.environ if source is None else source)
    for key in list(env):
        if key.startswith("GIT_"):
            env.pop(key, None)
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env["GIT_CONFIG_NOSYSTEM"] = "1"
    env["GIT_CONFIG_GLOBAL"] = os.devnull
    return env


def shell_env(source: dict[str, str]) -> dict[str, str]:
    env = dict(source)
    for key in ("BASH_ENV", "ENV", "CDPATH", "BASHOPTS", "SHELLOPTS",
                "PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP"):
        env.pop(key, None)
    for key in list(env):
        if key.startswith("BASH_FUNC_"):
            env.pop(key, None)
    return env


def run_git(root: Path, *args: str, env: dict[str, str] | None = None, input_data: bytes | None = None) -> bytes:
    command = ["git", "-C", str(root), *args]
    result = subprocess.run(command, input=input_data, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            env=git_env() if env is None else env, check=False)
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", "replace").strip()
        raise ProtocolError(f"git {' '.join(args[:3])} failed ({result.returncode}){': ' + detail if detail else ''}")
    return result.stdout


def repo_root(start: Path) -> Path:
    output = run_git(start, "rev-parse", "--show-toplevel").decode().strip()
    root = Path(output).resolve(strict=True)
    if not (root / ".git").exists() and not Path(run_git(root, "rev-parse", "--absolute-git-dir").decode().strip()).exists():
        raise ProtocolError("not a Git worktree")
    return root


def worktree_paths(root: Path) -> list[Path]:
    raw = run_git(root, "worktree", "list", "--porcelain", "-z")
    paths: list[Path] = []
    for item in raw.split(b"\0"):
        if item.startswith(b"worktree "):
            paths.append(Path(os.fsdecode(item[len(b"worktree "):])).resolve())
    if not paths:
        raise ProtocolError("cannot enumerate repository worktrees")
    return paths


def is_within(path: Path, parent: Path) -> bool:
    return path == parent or parent in path.parents


def configured_adapter(root: Path) -> Path:
    result = subprocess.run(["git", "-C", str(root), "config", "--local", "--null", "--get-all", CONFIG_KEY],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=git_env(), check=False)
    if result.returncode == 1:
        raise Unconfigured
    if result.returncode != 0:
        raise ProtocolError("cannot read repository-local adapter configuration")
    values = result.stdout.split(b"\0")
    if values and values[-1] == b"":
        values.pop()
    if len(values) != 1 or not values[0]:
        raise ProtocolError("adapter config must contain exactly one nonempty value")
    configured = Path(os.fsdecode(values[0]))
    if not configured.is_absolute():
        raise ProtocolError("adapter config must be an absolute path")
    lexical_path = Path(os.path.abspath(configured))
    common = Path(run_git(root, "rev-parse", "--path-format=absolute", "--git-common-dir").decode().strip()).resolve()
    repo_worktrees = worktree_paths(root)
    if any(is_within(lexical_path, worktree) for worktree in repo_worktrees) or is_within(lexical_path, common):
        raise ProtocolError("configured adapter path must not be replaceable through repository source")
    try:
        adapter = configured.resolve(strict=True)
    except OSError as error:
        raise ProtocolError(f"configured adapter path is unavailable: {error}") from error
    info = adapter.stat()
    if not stat.S_ISREG(info.st_mode) or not os.access(adapter, os.X_OK):
        raise ProtocolError("configured adapter must resolve to an executable regular file")
    if any(is_within(adapter, worktree) for worktree in repo_worktrees) or is_within(adapter, common):
        raise ProtocolError("configured adapter must be outside every repository worktree and common Git directory")
    return adapter


def tree_oid(root: Path, commit: str) -> str:
    return run_git(root, "rev-parse", "--verify", f"{commit}^{{tree}}").decode().strip()


def gate_code_digest(root: Path, commit: str) -> str:
    raw = run_git(root, "ls-tree", "-r", "-z", "--full-tree", commit)
    selected: list[tuple[bytes, bytes, bytes]] = []
    fixed = {
        b"TDA.lean", b"ComparatorChallenge.lean", b"lakefile.toml", b"lakefile.lean",
        b"lake-manifest.json", b"lean-toolchain", b"comparator.json",
        b"docs/adr/0003-comparator-pilot-contract.md",
    }
    for entry in raw.split(b"\0"):
        if not entry:
            continue
        metadata, path = entry.split(b"\t", 1)
        mode, kind, oid = metadata.split(b" ", 2)
        if path in fixed or path.startswith((b"scripts/", b"TDA/", b"ComparatorChallenge/")):
            selected.append((path, mode, oid))
    if not selected:
        raise ProtocolError("cannot compute gate code identity")
    selected.sort()
    data = bytearray(b"tda-lib gate sources v1\0")
    for path, mode, oid in selected:
        data.extend(path + b"\0" + mode + b"\0" + oid + b"\0")
    return sha256(bytes(data))


def validate_commit(root: Path, commit: str, tree: str) -> tuple[str, str]:
    actual = run_git(root, "rev-parse", "--verify", f"{commit}^{{commit}}").decode().strip()
    if actual != commit:
        raise ProtocolError("executor commit resolution changed the requested object")
    actual_tree = tree_oid(root, actual)
    if actual_tree != tree:
        raise ProtocolError("executor commit has a different tree")
    return actual, actual_tree


def branch_identity(root: Path) -> str:
    result = subprocess.run(["git", "-C", str(root), "symbolic-ref", "--quiet", "HEAD"],
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=git_env(), check=False)
    if result.returncode == 1:
        return ""
    if result.returncode != 0:
        raise ProtocolError("cannot inspect executor branch identity")
    return result.stdout.decode("ascii", "strict").strip()


def validate_executor_ref(value: Any) -> str:
    if not isinstance(value, str):
        raise ProtocolError("executor ref must be a string")
    if value == "":
        return value  # Detached HEAD is represented only by the empty string.
    if value == "refs/heads/main":
        raise ProtocolError("executor ref cannot be refs/heads/main for an ordinary gate")
    result = subprocess.run(["git", "check-ref-format", value], stdout=subprocess.DEVNULL,
                            stderr=subprocess.DEVNULL, env=git_env(), check=False)
    if result.returncode != 0:
        raise ProtocolError("executor ref is not a valid fully-qualified Git ref")
    return value


def object_hash(data: bytes, algo: str) -> str:
    h = hashlib.new(algo)
    h.update(b"blob " + str(len(data)).encode("ascii") + b"\0" + data)
    return h.hexdigest()


def parse_tree_entries(root: Path, commit: str) -> dict[bytes, tuple[bytes, bytes]]:
    raw = run_git(root, "ls-tree", "-r", "-z", "--full-tree", commit)
    entries: dict[bytes, tuple[bytes, bytes]] = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        header, path = item.split(b"\t", 1)
        mode, kind, oid = header.split(b" ", 2)
        if kind != b"blob" or mode not in {b"100644", b"100755", b"120000"}:
            raise ProtocolError(f"unsupported tracked object or mode at {os.fsdecode(path)!r}")
        if not path or path.startswith(b"/") or b".." in path.split(b"/") or b"." in path.split(b"/"):
            raise ProtocolError("unsafe tracked path in executor tree")
        if path in entries:
            raise ProtocolError("duplicate tracked path in executor tree")
        entries[path] = (mode, oid)
    return entries


def parse_index(root: Path) -> dict[bytes, tuple[bytes, bytes]]:
    raw = run_git(root, "ls-files", "--stage", "-z")
    entries: dict[bytes, tuple[bytes, bytes]] = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        header, path = item.split(b"\t", 1)
        fields = header.split()
        if len(fields) != 3 or fields[2] != b"0":
            raise ProtocolError("executor index has unmerged or malformed entries")
        mode, oid, _stage = fields
        if path in entries:
            raise ProtocolError("duplicate path in executor index")
        entries[path] = (mode, oid)
    return entries


def check_raw_worktree(root: Path, commit: str, tree: str) -> tuple[str, str]:
    actual_head = run_git(root, "rev-parse", "--verify", "HEAD^{commit}").decode().strip()
    if actual_head != commit:
        raise ProtocolError("executor HEAD commit does not match requested commit")
    head, actual_tree = validate_commit(root, commit, tree)
    if run_git(root, "write-tree").decode().strip() != tree:
        raise ProtocolError("executor index differs from requested tree")
    if parse_index(root) != parse_tree_entries(root, commit):
        raise ProtocolError("executor index entries differ from requested tree")
    flags = run_git(root, "ls-files", "-v", "-z")
    for item in flags.split(b"\0"):
        if not item:
            continue
        if item[:1] in b"abcdefghijklmnopqrstuvwxyzS":
            raise ProtocolError("executor index has assume-unchanged or skip-worktree flags")
    algo = run_git(root, "rev-parse", "--show-object-format").decode().strip()
    if algo not in {"sha1", "sha256"}:
        raise ProtocolError("unsupported Git object format")
    entries = parse_tree_entries(root, commit)
    for path_bytes, (mode, oid) in entries.items():
        parts = path_bytes.split(b"/")
        cursor = root
        for component in parts[:-1]:
            cursor = cursor / os.fsdecode(component)
            try:
                current = cursor.lstat()
            except OSError as error:
                raise ProtocolError(f"missing source directory: {os.fsdecode(path_bytes)!r}") from error
            if not stat.S_ISDIR(current.st_mode):
                raise ProtocolError(f"unsafe source path component: {os.fsdecode(path_bytes)!r}")
        path = cursor / os.fsdecode(parts[-1])
        try:
            info = path.lstat()
        except OSError as error:
            raise ProtocolError(f"missing tracked source: {os.fsdecode(path_bytes)!r}") from error
        if mode == b"120000":
            if not stat.S_ISLNK(info.st_mode):
                raise ProtocolError(f"tracked symlink was replaced: {os.fsdecode(path_bytes)!r}")
            content = os.fsencode(os.readlink(path))
        else:
            if not stat.S_ISREG(info.st_mode):
                raise ProtocolError(f"tracked regular file was replaced: {os.fsdecode(path_bytes)!r}")
            executable = bool(info.st_mode & 0o111)
            if executable != (mode == b"100755"):
                raise ProtocolError(f"tracked executable mode changed: {os.fsdecode(path_bytes)!r}")
            content = path.read_bytes()
        if object_hash(content, algo).encode("ascii") != oid:
            raise ProtocolError(f"raw tracked bytes changed: {os.fsdecode(path_bytes)!r}")
    check_untracked_sources(root)
    # Replace objects and grafts can redefine Git's view of an otherwise matching commit.
    if run_git(root, "for-each-ref", "--format=%(refname)", "refs/replace").strip():
        raise ProtocolError("executor has replacement refs")
    common = Path(run_git(root, "rev-parse", "--path-format=absolute", "--git-common-dir").decode().strip())
    grafts = common / "info" / "grafts"
    if grafts.exists() and grafts.stat().st_size:
        raise ProtocolError("executor has grafted commit history")
    branch = branch_identity(root)
    if branch == "refs/heads/main" or os.environ.get("TDA_STABLE_RELEASE") == "1":
        raise ProtocolError("ordinary remote gate cannot run in stable/main mode")
    return head, actual_tree


def check_untracked_sources(root: Path) -> None:
    normal = run_git(root, "ls-files", "--others", "--exclude-standard", "-z")
    ignored = run_git(root, "ls-files", "--others", "--ignored", "--exclude-standard", "-z")
    paths = set(normal.split(b"\0")) | set(ignored.split(b"\0"))
    paths.discard(b"")
    classifier = root / "scripts/lib/build-change-classifier.py"
    if not classifier.is_file():
        raise ProtocolError("build-change classifier is missing")
    env = git_env()
    result = subprocess.run([sys.executable, "-I", str(classifier), "--untracked"], input=b"".join(p + b"\0" for p in sorted(paths)),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, check=False)
    if result.returncode == 0:
        raise ProtocolError("executor has build-relevant untracked source")
    if result.returncode != 1:
        raise ProtocolError("executor untracked-source classifier failed")


def validate_bundle(root: Path, bundle: Path, request: dict[str, Any]) -> None:
    try:
        info = bundle.lstat()
        if not stat.S_ISREG(info.st_mode) or info.st_size == 0:
            raise ProtocolError("source bundle is not a nonempty regular file")
        digest = file_sha256(bundle)
    except OSError as error:
        raise ProtocolError(f"cannot read source bundle: {error}") from error
    if digest != request["source_bundle_sha256"]:
        raise ProtocolError("source bundle digest mismatch")
    run_git(root, "bundle", "verify", str(bundle))
    heads = run_git(root, "bundle", "list-heads", str(bundle))
    advertised: set[str] = set()
    for line in heads.decode("ascii", "strict").splitlines():
        parts = line.split(" ", 1)
        if len(parts) != 2:
            raise ProtocolError("malformed Git bundle head list")
        advertised.add(parts[0])
    if request["commit"] not in advertised:
        raise ProtocolError("source bundle does not advertise the requested commit")


def request_digest(request: dict[str, Any]) -> str:
    return sha256(canonical_bytes(request))


def replay_marker(request: dict[str, Any], cache_root: Path) -> None:
    directory = cache_root / "tda-lib" / "remote-gate" / "used"
    directory.mkdir(mode=0o700, parents=True, exist_ok=True)
    if directory.is_symlink() or not directory.is_dir():
        raise ProtocolError("unsafe replay-marker directory")
    marker = directory / (request["request_id"] + ".json")
    payload = canonical_bytes({"request_sha256": request_digest(request), "protocol_version": PROTOCOL}) + b"\n"
    try:
        fd = os.open(marker, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError as error:
        raise ProtocolError("request ID replay rejected") from error
    with os.fdopen(fd, "wb") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())


def build_lock_records(root: Path, env: dict[str, str]) -> list[tuple[str, str]]:
    helper = root / "scripts/lib/build-resources.py"
    result = subprocess.run([sys.executable, "-I", str(helper), str(root)], stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, env=env, cwd=root, check=False)
    if result.returncode != 0:
        raise ProtocolError("cannot determine canonical build-resource locks")
    records: list[tuple[str, str]] = []
    for line in result.stdout.decode("utf-8", "strict").splitlines():
        mode, path = line.split(":", 1)
        if mode not in {"S", "X"} or not path.startswith("/"):
            raise ProtocolError("malformed canonical build-resource lock plan")
        records.append((mode, path))
    if not records:
        raise ProtocolError("empty canonical build-resource lock plan")
    return records


def acquire_build_locks(root: Path, env: dict[str, str], deadline: float) -> tuple[list[int], str, list[tuple[str, str]]]:
    records = build_lock_records(root, env)
    fds: list[int] = []
    inherited: list[str] = []
    directory = Path("/tmp") / f"lean-resource-locks-{os.getuid()}"
    directory.mkdir(mode=0o700, exist_ok=True)
    try:
        for mode, lock_path in records:
            path = Path(lock_path)
            if path.parent != directory:
                raise ProtocolError("canonical lock escaped its per-user lock directory")
            fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
            operation = fcntl.LOCK_EX if mode == "X" else fcntl.LOCK_SH
            while True:
                check_stop_file(env)
                try:
                    fcntl.flock(fd, operation | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise ProtocolError("executor gate deadline expired while waiting for resource locks")
                    time.sleep(min(0.2, remaining))
            fds.append(fd)
            inherited.append(f"{fd}:{mode}:{lock_path}")
    except Exception:
        for fd in reversed(fds):
            os.close(fd)
        raise
    if build_lock_records(root, env) != records:
        for fd in reversed(fds):
            os.close(fd)
        raise ProtocolError("build-resource topology changed while acquiring locks")
    child_env = dict(env)
    child_env["LEAN_RESOURCE_LOCK_FDS"] = " ".join(inherited)
    return fds, child_env["LEAN_RESOURCE_LOCK_FDS"], records


def check_stop_file(env: dict[str, str]) -> None:
    candidates = {Path("/tmp/codex-stop")}
    configured = env.get("CODEX_STOP_FILE")
    if configured:
        candidates.add(Path(configured))
    for path in candidates:
        if path.exists():
            raise ProtocolError(f"executor stopped by {path}")


def receiver_env() -> dict[str, str]:
    env = shell_env(git_env())
    # These are the known gate bypass/stable selectors. Preserve cache, resource, thread,
    # headroom and stop-file settings from the trusted executor environment.
    env.pop("TDA_COMPARATOR_SKIP_SANDBOXED_RUN", None)
    env.pop("TDA_STABLE_RELEASE", None)
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    return env


def atomic_result(path: Path, value: dict[str, Any]) -> None:
    payload = canonical_bytes(value) + b"\n"
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())


def receiver(args: argparse.Namespace) -> int:
    global active_gate
    checkout = repo_root(Path(args.checkout))
    request_path = Path(args.request).resolve(strict=True)
    bundle_path = Path(args.bundle).resolve(strict=True)
    result_path = Path(args.result).absolute()
    log_path = Path(args.log).absolute()
    request, request_raw = read_json(request_path, MAX_RESULT_BYTES)
    request = validate_request(request)
    req_digest = request_digest(request)
    deadline = time.monotonic() + request["timeout_seconds"]
    cache_root = Path(os.environ.get("XDG_CACHE_HOME", str(Path.home() / ".cache"))).expanduser()
    replay_marker(request, cache_root)
    validate_bundle(checkout, bundle_path, request)
    check_stop_file(os.environ)
    # Preflight the repository-owned lock planner before executing it; repeat under the
    # acquired locks before the canonical gate and afterward.
    preflight_head, _preflight_tree = check_raw_worktree(checkout, request["commit"], request["tree"])
    expected_helper = checkout / "scripts/lib/remote-gate.py"
    if Path(__file__).resolve(strict=True) != expected_helper.resolve(strict=True):
        raise ProtocolError("receiver must run from the requested checkout's exact helper")
    if gate_code_digest(checkout, preflight_head) != request["gate_code_sha256"]:
        raise ProtocolError("executor gate implementation identity mismatch")

    gate_argv = ["scripts/check.sh"] + (["--incremental"] if request["gate_mode"] == "incremental" else [])
    env = receiver_env()
    fds, lock_fds, records = acquire_build_locks(checkout, env, deadline)
    try:
        check_stop_file(env)
        # Bind the exact checkout under the same locks retained through gate completion.
        head_before, tree_before = check_raw_worktree(checkout, request["commit"], request["tree"])
        ref_before = branch_identity(checkout)
        expected_helper = checkout / "scripts/lib/remote-gate.py"
        if Path(__file__).resolve(strict=True) != expected_helper.resolve(strict=True):
            raise ProtocolError("receiver must run from the requested checkout's exact helper")
        if gate_code_digest(checkout, head_before) != request["gate_code_sha256"]:
            raise ProtocolError("executor gate implementation identity mismatch")
        if ref_before == "refs/heads/main" or os.environ.get("TDA_STABLE_RELEASE") == "1":
            raise ProtocolError("ordinary remote gate cannot run in stable/main mode")
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise ProtocolError("executor gate deadline expired before canonical gate start")
        log_fd = os.open(log_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(log_fd, "wb") as log:
            child_env = dict(env)
            child_env["LEAN_RESOURCE_LOCK_FDS"] = lock_fds
            child_env["TDA_STABLE_RELEASE"] = "0"
            gate_exit, timed_out = run_owned_gate(
                ["bash", *gate_argv], cwd=checkout, env=child_env, stdout=log,
                stderr=subprocess.STDOUT, pass_fds=tuple(fds), timeout=remaining)
            log.flush()
            os.fsync(log.fileno())
        if gate_exit != 0:
            print(f"[remote-gate] canonical gate returned {gate_exit} (including deadline termination)", file=sys.stderr)
        check_stop_file(os.environ)
        head_after, tree_after = check_raw_worktree(checkout, request["commit"], request["tree"])
        ref_after = branch_identity(checkout)
        if head_after != head_before or tree_after != tree_before:
            raise ProtocolError("executor checkout identity changed during gate")
        if ref_after != ref_before:
            raise ProtocolError("executor branch identity changed during gate")
        if gate_code_digest(checkout, head_after) != request["gate_code_sha256"]:
            raise ProtocolError("executor gate source changed during gate")
        if request_path.read_bytes() != request_raw:
            raise ProtocolError("request file changed during executor run")
        if file_sha256(bundle_path) != request["source_bundle_sha256"]:
            raise ProtocolError("source bundle changed during executor run")
        log_info = log_path.lstat()
        if not stat.S_ISREG(log_info.st_mode) or log_info.st_size > MAX_LOG_BYTES:
            raise ProtocolError("gate log is not a bounded regular file")
        result = {
            **request,
            "request_sha256": req_digest,
            "executor_head_before": head_before,
            "executor_tree_before": tree_before,
            "executor_ref_before": ref_before,
            "executor_head_after": head_after,
            "executor_tree_after": tree_after,
            "executor_ref_after": ref_after,
            "gate_argv": gate_argv,
            "gate_exit_code": gate_exit,
            "gate_timed_out": timed_out,
            "gate_log_sha256": sha256(log_path.read_bytes()),
        }
        result["result_sha256"] = sha256(canonical_bytes(result))
        atomic_result(result_path, result)
    finally:
        for fd in reversed(fds):
            os.close(fd)
    return 0 if gate_exit == 0 and not timed_out else 1


def timeout_seconds() -> int:
    value = os.environ.get("TDA_REMOTE_GATE_TIMEOUT_SECONDS", str(DEFAULT_TIMEOUT))
    if not value.isdecimal():
        raise ProtocolError("remote-gate timeout must be a positive integer")
    seconds = int(value)
    if seconds < 1 or seconds > MAX_TIMEOUT:
        raise ProtocolError(f"remote-gate timeout must be between 1 and {MAX_TIMEOUT} seconds")
    return seconds


active_gate: subprocess.Popen[bytes] | None = None
active_adapter: subprocess.Popen[bytes] | None = None


def run_owned_gate(command: list[str], *, timeout: float, **kwargs: Any) -> tuple[int, bool]:
    """Install cancellation handling before spawning, with signals blocked through ownership."""
    global active_gate
    handled = {signal.SIGTERM, signal.SIGINT}
    old_mask = signal.pthread_sigmask(signal.SIG_BLOCK, handled)
    old_handlers: dict[int, Any] = {}
    child: subprocess.Popen[bytes] | None = None
    try:
        for sig in handled:
            old_handlers[sig] = signal.signal(sig, receiver_signal)
        child = subprocess.Popen(command, start_new_session=True, close_fds=True,
                                 preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK, old_mask), **kwargs)
        active_gate = child
    except BaseException:
        active_gate = None
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)
        signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)
        raise
    signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)
    timed_out = False
    try:
        try:
            return child.wait(timeout=timeout), timed_out
        except subprocess.TimeoutExpired:
            timed_out = True
            terminate_owned_group(child)
            return child.returncode if child.returncode is not None else 124, timed_out
    finally:
        old_mask = signal.pthread_sigmask(signal.SIG_BLOCK, handled)
        active_gate = None
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)
        signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)


def receiver_signal(signum: int, _frame: Any) -> None:
    global active_gate
    signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGTERM, signal.SIGINT})
    child = active_gate
    active_gate = None
    if child is not None:
        terminate_owned_group(child)
    raise ProtocolError(f"receiver interrupted by signal {signum}; owned gate process group stopped")


def client_signal(signum: int, _frame: Any) -> None:
    global active_adapter
    signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGTERM, signal.SIGINT})
    child = active_adapter
    active_adapter = None
    if child is not None:
        terminate_owned_group(child, grace_seconds=8)
    raise ProtocolError(f"client interrupted by signal {signum}; owned adapter process group stopped")


def terminate_owned_group(child: subprocess.Popen[bytes], grace_seconds: int = 5) -> None:
    # Both adapters and gates start fresh sessions. Their PGIDs are owned by this invocation;
    # detached descendants remain the trusted adapter's responsibility.
    try:
        os.killpg(child.pid, signal.SIGTERM)
    except ProcessLookupError:
        child.wait()
        return
    end = time.monotonic() + grace_seconds
    while time.monotonic() < end:
        child.poll()
        try:
            os.killpg(child.pid, 0)
        except ProcessLookupError:
            child.wait()
            return
        time.sleep(0.05)
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    child.wait()


def tail_log(path: Path, lines: int = 40) -> str:
    try:
        data = path.read_bytes()
    except OSError:
        return ""
    return "\n".join(data.decode("utf-8", "replace").splitlines()[-lines:])


def run_owned_adapter(command: list[str], *, timeout: float, **kwargs: Any) -> int:
    """Mask cancellation until the new adapter process group is recorded as ours."""
    global active_adapter
    handled = {signal.SIGTERM, signal.SIGINT}
    old_mask = signal.pthread_sigmask(signal.SIG_BLOCK, handled)
    old_handlers: dict[int, Any] = {}
    child: subprocess.Popen[bytes] | None = None
    try:
        for sig in handled:
            old_handlers[sig] = signal.signal(sig, client_signal)
        child = subprocess.Popen(command, start_new_session=True, close_fds=True,
                                 preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK, old_mask), **kwargs)
        active_adapter = child
    except BaseException:
        active_adapter = None
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)
        signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)
        raise
    signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)
    try:
        try:
            return child.wait(timeout=timeout)
        except subprocess.TimeoutExpired as error:
            terminate_owned_group(child, grace_seconds=8)
            raise ProtocolError(f"configured adapter timed out after {int(timeout)}s") from error
    finally:
        old_mask = signal.pthread_sigmask(signal.SIG_BLOCK, handled)
        active_adapter = None
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)
        signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)


def client(args: argparse.Namespace) -> int:
    root = repo_root(Path.cwd())
    adapter = configured_adapter(root)
    commit = run_git(root, "rev-parse", "--verify", "HEAD^{commit}").decode().strip()
    if args.commit and args.commit != commit:
        raise ProtocolError("hook commit differs from current HEAD")
    tree = tree_oid(root, commit)
    if args.mode not in {"incremental", "full"}:
        raise ProtocolError("invalid ordinary gate mode")
    bundle = None
    scratch = root / ".agents/scratch"
    scratch.mkdir(mode=0o700, parents=True, exist_ok=True)
    temp_path = Path(tempfile.mkdtemp(prefix="remote-gate-", dir=scratch))
    os.chmod(temp_path, 0o700)
    try:
        bundle = temp_path / "source.bundle"
        run_git(root, "bundle", "create", str(bundle), "HEAD")
        bundle_digest = file_sha256(bundle)
        timeout = timeout_seconds()
        request = {
            "protocol_version": PROTOCOL,
            "request_id": secrets.token_hex(32),
            "gate_mode": args.mode,
            "commit": commit,
            "tree": tree,
            "source_bundle_sha256": bundle_digest,
            "gate_code_sha256": gate_code_digest(root, commit),
            "timeout_seconds": timeout,
        }
        request_raw = canonical_bytes(request) + b"\n"
        request_path = temp_path / "request.json"
        result_path = temp_path / "result.json"
        log_path = temp_path / "gate.log"
        request_path.write_bytes(request_raw)
        os.chmod(request_path, 0o400)
        os.chmod(bundle, 0o400)
        request_identity = request_path.stat()
        bundle_identity = bundle.stat()
        adapter_stderr = temp_path / "adapter.stderr"
        with adapter_stderr.open("xb") as adapter_error_log:
            adapter_status = run_owned_adapter(
                [str(adapter), str(request_path), str(bundle), str(result_path), str(log_path)],
                cwd=root, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                stderr=adapter_error_log, env=shell_env(git_env()),
                timeout=timeout + min(30, timeout) + 8)
        if request_path.read_bytes() != request_raw:
            raise ProtocolError("adapter changed the in-memory-bound request file")
        current_request = request_path.lstat()
        current_bundle = bundle.lstat()
        if (not stat.S_ISREG(current_request.st_mode) or
                (current_request.st_dev, current_request.st_ino) != (request_identity.st_dev, request_identity.st_ino)):
            raise ProtocolError("adapter replaced the request file")
        if (not stat.S_ISREG(current_bundle.st_mode) or
                (current_bundle.st_dev, current_bundle.st_ino) != (bundle_identity.st_dev, bundle_identity.st_ino)):
            raise ProtocolError("adapter replaced the source bundle")
        if file_sha256(bundle) != request["source_bundle_sha256"]:
            raise ProtocolError("adapter changed the source bundle")
        result, result_raw = read_json(result_path, MAX_RESULT_BYTES)
        if set(result) != RESULT_FIELDS:
            raise ProtocolError("result fields do not match the v1 schema")
        result_digest = result.get("result_sha256")
        unsigned = dict(result)
        unsigned.pop("result_sha256", None)
        if validate_hex(result_digest, {64}, "result digest") != sha256(canonical_bytes(unsigned)):
            raise ProtocolError("result digest mismatch")
        validate_request({key: result[key] for key in REQUEST_FIELDS})
        if result["request_sha256"] != request_digest(request):
            raise ProtocolError("result request digest mismatch")
        for key, expected in request.items():
            if result.get(key) != expected:
                raise ProtocolError(f"result does not match request field {key}")
        if result["executor_head_before"] != commit or result["executor_head_after"] != commit:
            raise ProtocolError("executor commit does not match requested commit")
        ref_before = validate_executor_ref(result["executor_ref_before"])
        ref_after = validate_executor_ref(result["executor_ref_after"])
        if ref_before != ref_after:
            raise ProtocolError("executor branch identity changed during gate")
        if result["executor_tree_before"] != tree or result["executor_tree_after"] != tree:
            raise ProtocolError("executor tree does not match requested tree")
        expected_argv = ["scripts/check.sh"] + (["--incremental"] if args.mode == "incremental" else [])
        if result["gate_argv"] != expected_argv:
            raise ProtocolError("result reports a noncanonical gate invocation")
        if type(result["gate_exit_code"]) is not int:
            raise ProtocolError("result gate exit code is not an integer")
        if type(result["gate_timed_out"]) is not bool:
            raise ProtocolError("result gate timeout marker is not boolean")
        validate_hex(result["gate_log_sha256"], {64}, "gate log digest")
        log_info = log_path.lstat()
        if not stat.S_ISREG(log_info.st_mode) or log_info.st_size > MAX_LOG_BYTES:
            raise ProtocolError("adapter did not return a bounded regular gate log")
        if sha256(log_path.read_bytes()) != result["gate_log_sha256"]:
            raise ProtocolError("returned gate log digest mismatch")
        if adapter_status != 0:
            raise ProtocolError(f"configured adapter exited {adapter_status}; stderr digest {file_sha256(adapter_stderr)}")
        if result["gate_timed_out"]:
            details = tail_log(log_path)
            raise ProtocolError("canonical remote gate timed out" + (f"\n{details}" if details else ""))
        if result["gate_exit_code"] != 0:
            details = tail_log(log_path)
            raise ProtocolError(f"canonical remote gate exited {result['gate_exit_code']}" + (f"\n{details}" if details else ""))
        print(f"[pre-push] remote {args.mode} gate passed for exact commit {commit}")
        return 0
    finally:
        # Temporary request/bundle/result/log are local scratch, never repository inputs.
        import shutil
        shutil.rmtree(temp_path, ignore_errors=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    client_parser = sub.add_parser("client")
    client_parser.add_argument("--mode", required=True, choices=("incremental", "full"))
    client_parser.add_argument("--commit", required=True)
    receive_parser = sub.add_parser("receive")
    receive_parser.add_argument("--checkout", required=True)
    receive_parser.add_argument("--request", required=True)
    receive_parser.add_argument("--bundle", required=True)
    receive_parser.add_argument("--result", required=True)
    receive_parser.add_argument("--log", required=True)
    args = parser.parse_args()
    try:
        if not sys.flags.isolated:
            raise ProtocolError("invoke this helper with python3 -I")
        if args.command == "client":
            try:
                return client(args)
            except Unconfigured:
                return 3
        return receiver(args)
    except (ProtocolError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"[remote-gate] BLOCK: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
