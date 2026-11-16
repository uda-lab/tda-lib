#!/usr/bin/env python3
"""Classify NUL-delimited changed paths using the hosted CI build rules.

Exit 0 means at least one build-relevant path was found, exit 1 means none, and
exit 2 means the input could not be classified. Paths are bytes so whitespace,
newlines, and non-UTF-8 names are never split or normalized.
"""

import sys


IGNORED_GENERATED_PREFIXES = (
    b".lake/",
    b"docbuild/.lake/",
    b"build/",
    b"docs/note/build/",
    b".agents/scratch/",
    b".agents/worktrees/",
    b".claude/scratch/",
    b".claude/worktrees/",
)


def is_build_relevant(path: bytes) -> bool:
    if path.endswith(b".lean"):
        return True
    if path.startswith(b"lakefile"):
        return True
    if path in (b"lean-toolchain", b"lake-manifest.json", b"comparator.json"):
        return True
    return path.startswith(b"scripts/") or path.startswith(b".github/workflows/")


def main() -> int:
    mode = sys.argv[1:]
    if mode not in ([], ["--untracked"]):
        print("usage: build-change-classifier.py [--untracked]", file=sys.stderr)
        return 2
    raw = sys.stdin.buffer.read()
    if raw and not raw.endswith(b"\0"):
        print("build-change-classifier: input is not NUL terminated", file=sys.stderr)
        return 2
    paths = raw.split(b"\0")[:-1] if raw else []
    if any(not path for path in paths):
        print("build-change-classifier: empty path in input", file=sys.stderr)
        return 2
    if mode == ["--untracked"]:
        paths = [
            path
            for path in paths
            if not path.startswith(IGNORED_GENERATED_PREFIXES)
        ]

    matches = [path for path in paths if is_build_relevant(path)]
    for path in matches:
        print("  " + repr(path))
    return 0 if matches else 1


if __name__ == "__main__":
    raise SystemExit(main())
