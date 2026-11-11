#!/usr/bin/env python3
"""Measure an existing API site, without building, publishing or certifying it."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import stat


def signature(info: os.stat_result) -> tuple[int, ...]:
    return (info.st_dev, info.st_ino, info.st_mode, info.st_size,
            info.st_mtime_ns, info.st_ctime_ns)


def inventory(root: Path) -> dict[str, tuple[int, ...]]:
    """Include directories so additions/removals during measurement are detected."""
    found = {}
    pending = [root]
    while pending:
        path = pending.pop()
        info = path.lstat()
        name = path.relative_to(root).as_posix()
        if not (stat.S_ISDIR(info.st_mode) or stat.S_ISREG(info.st_mode)):
            raise ValueError(f"Not a regular file or directory: {path}")
        found[name] = signature(info)
        if stat.S_ISDIR(info.st_mode):
            pending.extend(path.iterdir())
    return found


def measure_file(path: Path, expected: tuple[int, ...]) -> dict[str, int | str]:
    if not stat.S_ISREG(expected[2]):
        raise ValueError(f"Not a regular file: {path}")
    # O_NONBLOCK avoids hanging if a file is replaced by a FIFO before open.
    # O_NOFOLLOW refuses a final-component symlink even during such a race.
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as stream:
        if signature(os.fstat(stream.fileno())) != expected:
            raise ValueError(f"File changed before measurement: {path}")
        digest = hashlib.sha256()
        size = 0
        while chunk := stream.read(1024 * 1024):
            size += len(chunk)
            digest.update(chunk)
        if signature(os.fstat(stream.fileno())) != expected or size != expected[3]:
            raise ValueError(f"File changed during measurement: {path}")
    if signature(path.lstat()) != expected:
        raise ValueError(f"File changed after measurement: {path}")
    return {"bytes": size, "sha256": digest.hexdigest()}


def inspect(site: Path, archive: Path | None = None) -> dict:
    # Resolve parent aliases, but do not silently accept a symlink as the site.
    if site.is_symlink():
        raise ValueError(f"Site must not be a symlink: {site}")
    site = site.resolve(strict=True)
    if not site.is_dir():
        raise ValueError(f"Site is not a directory: {site}")
    before = inventory(site)
    if "index.html" not in before or not stat.S_ISREG(before["index.html"][2]):
        raise ValueError("Site must contain a regular index.html; do not pass a build cache")
    records = [
        {"path": name, **measure_file(site / name, info)}
        for name, info in sorted(before.items()) if stat.S_ISREG(info[2])
    ]
    if inventory(site) != before:
        raise ValueError("Site changed during measurement; stop writers and retry")
    encoded = json.dumps(records, sort_keys=True, ensure_ascii=True,
                         separators=(",", ":")).encode("utf-8")
    result = {
        "schema_version": 1,
        "inspected_at_utc": datetime.now(timezone.utc).isoformat(),
        "site": {
            "local_path": str(site),
            "file_count": len(records),
            "total_file_bytes": sum(record["bytes"] for record in records),
            "inventory_sha256": hashlib.sha256(encoded).hexdigest(),
            "files": records,
        },
        "archive": None,
        "limitations": [
            "Inspection time is not generation time.",
            "File hashes do not verify source revision, build target, completeness or links.",
            "Archive contents are not compared with the site.",
            "Local readability does not establish hosted access or retention.",
        ],
    }
    if archive is not None:
        if archive.is_symlink():
            raise ValueError(f"Archive must not be a symlink: {archive}")
        archive = archive.resolve(strict=True)
        if archive == site or site in archive.parents:
            raise ValueError("Keep the archive outside the measured site")
        result["archive"] = {
            "local_path": str(archive),
            **measure_file(archive, signature(archive.lstat())),
        }
        if inventory(site) != before:
            raise ValueError("Site changed during archive measurement; stop writers and retry")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path, help="Existing rendered site with index.html")
    parser.add_argument("--archive", type=Path, help="Optional existing archive to hash, not extract")
    args = parser.parse_args()
    stop = Path(os.environ.get("CODEX_STOP_FILE", "/tmp/codex-stop"))
    if stop.exists():
        parser.error(f"Stopped by {stop}")
    try:
        result = inspect(args.site, args.archive)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    print(json.dumps(result, indent=2, ensure_ascii=True))


if __name__ == "__main__":
    main()
