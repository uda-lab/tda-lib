#!/usr/bin/env python3
"""Content-hashed keys and record store for the incremental local gate (`scripts/check.sh
--incremental`, Issue #951). Used only by `scripts/check-incremental.sh`; plain
`scripts/check.sh`/`--stable` never imports or runs this file.

Soundness argument (recorded here, not only in the PR, because the key formula is the
part of this feature that must never regress silently): in Lean v4.35.0,
`Lean.collectAxioms` (`Lean/Util/CollectAxioms.lean`) resolves a declaration's transitive
axiom set either by (a) an O(1) lookup into the `exportedAxiomsExt` entries that an imported
module serialized into its own `.olean` at export time, or (b) — when no such entry exists
(the declaration is in the current scope, or was not exported) — a direct walk of
`env.checked`. For a process that only ever *imports* modules (never elaborates new
declarations of its own, which is exactly what the generated incremental-audit file and the
combined `check-axioms.sh` file both are), `env.checked` is itself reconstructed entirely by
deserializing the `.olean` bytes of every module in the import closure; nothing is
re-elaborated. So the result of `collectAxioms d` for a declaration `d` defined in module `M`
is a pure, deterministic function of: the fixed toolchain algorithm, plus the `.olean` bytes
of every module in `{M} ∪ forward-import-closure(M)` (mathlib's own content is pinned by
`lean-toolchain` + `lake-manifest.json`, already part of every key below, so mathlib modules
are not hashed individually). Hashing `M`'s own olean alone would be unsound: a private
declaration in `M` can be walked (case (b) above) straight into a constant that `M` imports
from elsewhere, so an unchanged `M` can still get a different audit result when something
`M` imports changes. Hashing the whole forward closure's oleans closes that gap, and it also
makes reverse-dependency invalidation automatic: if `M` changes, every module that transitively
imports `M` has `M` in its own forward closure, so its own key changes too, with no separate
reverse-dependency computation needed.
"""

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:
    tomllib = None

ROOT = Path(__file__).resolve().parents[2]
SCAN_AWK = ROOT / "scripts" / "lean-code-scan.awk"
DOMAIN_AUDIT = b"tda-incremental-audit-v1\0"
DOMAIN_COMPARATOR = b"tda-incremental-comparator-v1\0"

# Every source that defines *how* the incremental audit computes a result. Changing any of
# these must change every key, so a behavioural change to the gate itself is never masked by
# a stale cache hit. Does not include check-axioms.sh / check_axiom_coverage.lean: those are
# the FULL gate's unchanged files and are never consulted by the selective incremental path.
AUDIT_TOOL_SOURCES = (
    "scripts/lib/incremental-cache.py",
    "scripts/lib/incremental-audit-body.lean",
    "scripts/check-incremental.sh",
    "scripts/lean-code-scan.awk",
)

ALLOWLIST = ("propext", "Classical.choice", "Quot.sound")


class KeyError_(Exception):
    """An input cannot be hashed, or is missing/unreadable; caller must fall back to full."""


def read_nonempty(path: Path, label: str) -> bytes:
    try:
        data = path.read_bytes()
    except OSError as error:
        raise KeyError_(f"cannot read {label}: {error.strerror or error}") from None
    if not data:
        raise KeyError_(f"{label} must not be empty")
    return data


def framed(digest, name: str, payload: bytes) -> None:
    name_bytes = name.encode("ascii")
    digest.update(name_bytes + b"\0")
    digest.update(str(len(payload)).encode("ascii") + b"\0")
    digest.update(payload)


def module_name_of_path(rel_path: str) -> str:
    """`TDA/Persistence/Basic.lean` -> `TDA.Persistence.Basic`, Lean's own module-name rule
    for a file at this path (matches `moduleStringOfPath` in check_axiom_coverage.lean)."""
    assert rel_path.endswith(".lean")
    return rel_path[: -len(".lean")].replace("/", ".")


def olean_path_for_module(module: str) -> Path:
    return ROOT / ".lake" / "build" / "lib" / "lean" / (module.replace(".", "/") + ".olean")


def direct_tda_imports(lean_file: Path) -> list[str]:
    try:
        output = subprocess.run(
            ["awk", "-v", "mode=imports", "-f", str(SCAN_AWK), str(lean_file)],
            cwd=ROOT, capture_output=True, text=True, check=True, env={**os.environ, "LC_ALL": "C"},
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise KeyError_(f"could not parse imports of {lean_file}: {error}") from None
    imports = []
    for line in output.stdout.splitlines():
        line = line.strip()
        if line == "TDA" or line.startswith("TDA."):
            imports.append(line)
    return imports


def discover_tda_modules() -> dict[str, list[str]]:
    """Every `TDA/**/*.lean` file on disk, mapped to its direct TDA-local imports. Raises on
    any file whose import list cannot be parsed; the caller must fall back to the full gate."""
    tda_root = ROOT / "TDA"
    graph: dict[str, list[str]] = {}
    for path in sorted(tda_root.rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        module = module_name_of_path(rel)
        graph[module] = direct_tda_imports(path)
    # TDA.lean itself (the root aggregator) is also a module in the closure graph.
    root_file = ROOT / "TDA.lean"
    if root_file.is_file():
        graph["TDA"] = direct_tda_imports(root_file)
    return graph


def forward_closure(graph: dict[str, list[str]], module: str) -> list[str]:
    """{module} union every TDA module reachable by following direct imports, transitively."""
    seen: set[str] = set()
    pending = [module]
    while pending:
        n = pending.pop()
        if n in seen:
            continue
        seen.add(n)
        for dep in graph.get(n, []):
            if dep not in seen:
                pending.append(dep)
    return sorted(seen)


def build_reverse_graph(graph: dict[str, list[str]]) -> dict[str, list[str]]:
    """`graph` with every edge reversed: `reverse[N]` lists every module whose direct
    imports include `N` (every module `graph`'s own keys can appear as a dependency of)."""
    reverse: dict[str, list[str]] = {m: [] for m in graph}
    for m, deps in graph.items():
        for dep in deps:
            reverse.setdefault(dep, []).append(m)
    return reverse


def reverse_closure(reverse: dict[str, list[str]], module: str) -> list[str]:
    """{module} union every TDA module that (transitively) imports it — the Issue
    acceptance test's "that module and its reverse dependencies": changing `module`'s
    content can only change the incremental-audit key of a module in this set, because
    `forward_closure` of anything outside it never includes `module`. `reverse` must be
    `build_reverse_graph(graph)` for the same `graph` `module` was discovered in."""
    seen: set[str] = set()
    pending = [module]
    while pending:
        n = pending.pop()
        if n in seen:
            continue
        seen.add(n)
        for parent in reverse.get(n, []):
            if parent not in seen:
                pending.append(parent)
    return sorted(seen)


def read_common_inputs():
    toolchain = read_nonempty(ROOT / "lean-toolchain", "lean-toolchain")
    manifest = read_nonempty(ROOT / "lake-manifest.json", "lake-manifest.json")
    tool_sources = b"".join(
        name.encode("ascii") + b"\0" + read_nonempty(ROOT / name, name)
        for name in AUDIT_TOOL_SOURCES
    )
    allowlist = " ".join(ALLOWLIST).encode("ascii")
    return toolchain, manifest, tool_sources, allowlist


def module_key(module: str, closure: list[str], common) -> str:
    toolchain, manifest, tool_sources, allowlist = common
    digest = hashlib.sha256()
    digest.update(DOMAIN_AUDIT)
    framed(digest, "lean-toolchain", toolchain)
    framed(digest, "lake-manifest.json", manifest)
    framed(digest, "audit-tool-sources", tool_sources)
    framed(digest, "allowlist", allowlist)
    for n in closure:  # already sorted by forward_closure
        olean = olean_path_for_module(n)
        olean_bytes = read_nonempty(olean, f"olean for {n}")
        framed(digest, n, hashlib.sha256(olean_bytes).digest())
    return digest.hexdigest()


def cmd_graph(_args: list[str]) -> int:
    """Print `<module>\\t<reverse-dep-count>` for every TDA module, one per line, sorted —
    diagnostic/test support only; not used by scripts/check-incremental.sh itself. Every
    module actually reachable from `TDA.lean` (the only kind that passes the `keys`
    command's reachability check) has a DIRECT reverse-dep count of at least 1 by
    construction — something in its own import chain reaches it — so "0" never identifies
    a genuine content leaf here; `smallest-leaf` below is what scripts/test-incremental.sh
    uses instead."""
    try:
        graph = discover_tda_modules()
    except KeyError_ as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    reverse_count: dict[str, int] = {m: 0 for m in graph}
    for module, deps in graph.items():
        for dep in deps:
            if dep in reverse_count:
                reverse_count[dep] += 1
    lines = [f"{m}\t{reverse_count[m]}" for m in sorted(graph)]
    sys.stdout.write("\n".join(lines) + ("\n" if lines else ""))
    return 0


def cmd_reverse_closure(args: list[str]) -> int:
    """`reverse-closure <module>`: print, one per line, {module} union every TDA module
    that transitively imports it. Diagnostic/test support only (scripts/test-incremental.sh
    uses it to predict exactly how many modules a real incremental run must re-audit after
    editing <module>); not used by scripts/check-incremental.sh itself."""
    if len(args) != 1:
        print("usage: incremental-cache.py reverse-closure <module>", file=sys.stderr)
        return 64
    try:
        graph = discover_tda_modules()
    except KeyError_ as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    if args[0] not in graph:
        print(f"ERROR: unknown TDA module {args[0]!r}", file=sys.stderr)
        return 1
    for m in reverse_closure(build_reverse_graph(graph), args[0]):
        print(m)
    return 0


def has_real_content(module: str) -> bool:
    """`module`'s own `.lean` file has at least one non-import/non-comment/non-blank line
    — i.e. it is NOT itself a pure aggregator (`scripts/lean-code-scan.awk -v mode=root`,
    the same lexer `scripts/check-root-aggregator.sh` uses: empty output there means
    import-only). A path-only check (not itself a directory) is not enough: some `*.lean`
    files collect a group of sibling `*Examples` files into one import-only name without
    being a directory `scripts/check-root-aggregator.sh` would ever flag — a nested
    "Examples" collector, for instance — and editing one of those to add a declaration
    would (rightly) trip the unrelated root/area-aggregator guard instead of testing this
    gate."""
    path = ROOT / (module.replace(".", "/") + ".lean")
    try:
        result = subprocess.run(
            ["awk", "-v", "mode=root", "-f", str(SCAN_AWK), str(path)],
            cwd=ROOT, capture_output=True, text=True, check=True, env={**os.environ, "LC_ALL": "C"},
        )
    except (OSError, subprocess.CalledProcessError):
        return False
    return result.stdout.strip() != ""


def cmd_smallest_leaf(args: list[str]) -> int:
    """`smallest-leaf`: print `<module>\\t<reverse-closure-size>` for the TDA content
    module — at least 3 dotted name components, not itself a directory, and with real
    content of its own (`has_real_content`) — with the globally smallest reverse closure.
    Diagnostic/test support only: scripts/test-incremental.sh's real end-to-end cases edit
    this module specifically, because (a) "zero reverse dependencies" (this project's
    area/root aggregators always import every real content module, so no non-root module
    has a direct reverse-dep count of 0 — see `graph`'s own docstring) is unsatisfiable,
    but a content module reached directly from a top-level `Examples` aggregator, bypassing
    the deeper area/library chain, can still have a SMALL reverse closure; and (b) a small,
    deterministic closure keeps these cases fast and keeps their audited-count assertion
    exact rather than merely "more than zero"."""
    if args:
        print("usage: incremental-cache.py smallest-leaf", file=sys.stderr)
        return 64
    try:
        graph = discover_tda_modules()
    except KeyError_ as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    reverse = build_reverse_graph(graph)
    best_module: str | None = None
    best_size: int | None = None
    for module in sorted(graph):
        if len(module.split(".")) < 3:
            continue
        if (ROOT / module.replace(".", "/")).is_dir():
            continue
        if not has_real_content(module):
            continue
        size = len(reverse_closure(reverse, module))
        if best_size is None or size < best_size:
            best_module, best_size = module, size
    if best_module is None:
        print(
            "ERROR: no TDA content module (>= 3 dotted components, not an aggregator "
            "directory, with real content of its own) was found",
            file=sys.stderr,
        )
        return 1
    print(f"{best_module}\t{best_size}")
    return 0


def cmd_keys(_args: list[str]) -> int:
    """Print `<module>\\t<key>` for every TDA module found on disk, one per line, sorted.
    Cross-checks the statically discovered module set against the set Lake actually built
    (every module must have an olean; an extra or missing olean is an error either way), and
    against static reachability from `TDA.lean` (Issue #951 step 6, "Unloaded files"): Lake's
    default `lean_lib` glob builds every `.lean` file under `TDA/` regardless of whether
    anything imports it, so the declared/built comparison alone does NOT catch a module that
    compiles on its own but is never reached by `import TDA` — exactly the bug the full gate's
    `check_axiom_coverage.lean` (`findUnloadedFiles`) already catches with a live environment.
    This is the cheap static counterpart required to keep that guarantee in selective mode,
    where the full gate's environment-based check never runs. It does not reproduce that
    check's failure text; it only has to make the ambiguity visible so the caller's existing
    "module key computation failed" fallback routes the run to the full gate, whose
    environment-based check then fails it for real — fail-closed, never a silent pass."""
    try:
        graph = discover_tda_modules()
        common = read_common_inputs()
        if "TDA" not in graph:
            raise KeyError_("TDA.lean (root aggregator) is missing or has no parseable imports")
        reachable = set(forward_closure(graph, "TDA"))
        declared = set(graph)
        unreachable = sorted(declared - reachable)
        if unreachable:
            raise KeyError_(
                "TDA module(s) on disk are not reachable from TDA.lean by a static header "
                f"parse (unloaded-file check): {unreachable[:5]}"
            )
        lean_root = ROOT / ".lake" / "build" / "lib" / "lean"
        built = {
            p.relative_to(lean_root).with_suffix("").as_posix().replace("/", ".")
            for p in (lean_root / "TDA").rglob("*.olean")
        } | ({"TDA"} if (lean_root / "TDA.olean").is_file() else set())
        if declared != built:
            only_declared = sorted(declared - built)
            only_built = sorted(built - declared)
            raise KeyError_(
                "module set from TDA/**/*.lean headers does not match Lake's build output "
                f"(declared-not-built={only_declared[:5]}, built-not-declared={only_built[:5]})"
            )
        lines = []
        for module in sorted(graph):
            closure = forward_closure(graph, module)
            lines.append(f"{module}\t{module_key(module, closure, common)}")
        sys.stdout.write("\n".join(lines) + ("\n" if lines else ""))
        return 0
    except KeyError_ as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


def cmd_comparator_key(args: list[str]) -> int:
    """`comparator-key <solution-module-key>`: the solution module's own already-computed
    key (from `keys`) is one ingredient, so a change anywhere in ITS closure also changes
    the comparator key, with no separate closure walk here."""
    if len(args) != 1:
        print("usage: incremental-cache.py comparator-key <solution-module-key>", file=sys.stderr)
        return 64
    solution_key = args[0]
    try:
        digest = hashlib.sha256()
        digest.update(DOMAIN_COMPARATOR)
        for name in ("comparator.json", "lakefile.toml", "scripts/check-comparator.sh"):
            framed(digest, name, read_nonempty(ROOT / name, name))
        framed(digest, "solution-module-key", solution_key.encode("ascii"))
        challenge_root = ROOT / "ComparatorChallenge"
        challenge_files = sorted(
            [ROOT / "ComparatorChallenge.lean"] + list(challenge_root.rglob("*.lean"))
        )
        for path in challenge_files:
            rel = path.relative_to(ROOT).as_posix()
            framed(digest, rel, read_nonempty(path, rel))
        sys.stdout.write(digest.hexdigest() + "\n")
        return 0
    except KeyError_ as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


def store_dir() -> Path:
    override = os.environ.get("TDA_AUDIT_RECORDS")
    if override:
        return Path(override)
    xdg = os.environ.get("XDG_CACHE_HOME") or str(Path.home() / ".cache")
    return Path(xdg) / "tda-lib" / "audit-records"


AUDIT_SCHEMA_FIELDS = {"schema": int, "kind": str, "module": str, "public": list, "declared": list}
COMPARATOR_SCHEMA_FIELDS = {"schema": int, "kind": str}


def validate_record(data, expected_kind: str) -> None:
    fields = AUDIT_SCHEMA_FIELDS if expected_kind == "audit" else COMPARATOR_SCHEMA_FIELDS
    if not isinstance(data, dict):
        raise KeyError_("record is not a JSON object")
    for field, expected_type in fields.items():
        if field not in data:
            raise KeyError_(f"record missing field {field!r}")
        if not isinstance(data[field], expected_type):
            raise KeyError_(f"record field {field!r} has the wrong type")
    if data["schema"] != 1:
        raise KeyError_(f"record schema {data['schema']!r} is not supported")
    if data["kind"] != expected_kind:
        raise KeyError_(f"record kind {data['kind']!r} != expected {expected_kind!r}")
    if expected_kind == "audit":
        if not all(isinstance(x, str) for x in data["public"]):
            raise KeyError_("record field 'public' must be an array of strings")
        if not all(isinstance(x, str) for x in data["declared"]):
            raise KeyError_("record field 'declared' must be an array of strings")
        if not set(data["public"]) <= set(data["declared"]):
            raise KeyError_("record field 'public' must be a subset of 'declared'")


def cmd_store_dir(args: list[str]) -> int:
    """`store-dir`: print the resolved record-store directory path. Pure env-var resolution,
    no filesystem access; the caller uses this to detect "the record store does not exist
    yet" (first run on a fresh clone/worktree) as its own, explicit full-gate trigger,
    distinct from an ordinary per-record cache miss."""
    if args:
        print("usage: incremental-cache.py store-dir", file=sys.stderr)
        return 64
    sys.stdout.write(str(store_dir()) + "\n")
    return 0


def cmd_read_record(args: list[str]) -> int:
    """`read-record <key> <kind>`. Exit 0 and print JSON on a valid PASS record; exit 2 if
    simply absent (an ordinary cache miss); exit 1 on any read/parse/schema error (corruption
    — the caller must fall back to the full gate, never treat this as a miss)."""
    if len(args) != 2:
        print("usage: incremental-cache.py read-record <key> <kind>", file=sys.stderr)
        return 64
    key, kind = args
    path = store_dir() / f"{key}.json"
    if not path.exists():
        return 2
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        validate_record(data, kind)
    except (OSError, UnicodeError, ValueError, KeyError_) as error:
        print(f"ERROR: corrupt record {path}: {error}", file=sys.stderr)
        return 1
    sys.stdout.write(json.dumps(data))
    return 0


def cmd_write_record(args: list[str]) -> int:
    """`write-record <key> <kind>`: reads the record JSON from stdin, validates it, and
    writes it via a temp file + rename (POSIX-atomic within the same directory). Only ever
    called with a record that already represents a PASS; this tool does not itself decide
    pass/fail."""
    if len(args) != 2:
        print("usage: incremental-cache.py write-record <key> <kind>", file=sys.stderr)
        return 64
    key, kind = args
    try:
        data = json.loads(sys.stdin.read())
        validate_record(data, kind)
    except (UnicodeError, ValueError, KeyError_) as error:
        print(f"ERROR: refusing to write an invalid record: {error}", file=sys.stderr)
        return 1
    directory = store_dir()
    try:
        directory.mkdir(parents=True, exist_ok=True)
        fd_path = directory / f".tmp-{os.getpid()}-{key}.json"
        fd_path.write_text(json.dumps(data), encoding="utf-8")
        os.replace(fd_path, directory / f"{key}.json")
    except OSError as error:
        print(f"ERROR: could not write record: {error}", file=sys.stderr)
        return 1
    return 0


def main(argv: list[str]) -> int:
    if not argv:
        print(
            "usage: incremental-cache.py "
            "{keys|graph|reverse-closure|smallest-leaf|comparator-key|store-dir|read-record|write-record} ...",
            file=sys.stderr,
        )
        return 64
    command, rest = argv[0], argv[1:]
    if tomllib is None:
        print("ERROR: Python 3.11+ with tomllib is required", file=sys.stderr)
        return 1
    if command == "keys":
        return cmd_keys(rest)
    if command == "graph":
        return cmd_graph(rest)
    if command == "reverse-closure":
        return cmd_reverse_closure(rest)
    if command == "smallest-leaf":
        return cmd_smallest_leaf(rest)
    if command == "comparator-key":
        return cmd_comparator_key(rest)
    if command == "store-dir":
        return cmd_store_dir(rest)
    if command == "read-record":
        return cmd_read_record(rest)
    if command == "write-record":
        return cmd_write_record(rest)
    print(f"ERROR: unknown command {command!r}", file=sys.stderr)
    return 64


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
