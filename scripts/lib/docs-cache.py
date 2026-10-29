#!/usr/bin/env python3
"""Compatibility key and transactional invalidation for the pinned doc-gen4 build."""

import hashlib
import os
from pathlib import Path
import shutil
import sqlite3
import sys


TARGET = "+TDA.Library:docs"
ROOT = Path(__file__).resolve().parents[2]
LAKE = ROOT / "docbuild/.lake"
BUILD = LAKE / "build"


def cache_key():
    digest = hashlib.sha256()
    digest.update(f"docs-v1\0{TARGET}\0{os.getenv('DOCGEN_SRC', 'github')}\0".encode())
    for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "docbuild/lean-toolchain", "docbuild/lakefile.toml", "docbuild/lake-manifest.json",
        "scripts/build-docs.sh", "scripts/check-doc-lock.sh", "scripts/lib/docs-cache.py",
    ):
        digest.update(name.encode() + b"\0" + (ROOT / name).read_bytes() + b"\0")
    # doc-gen4's bibliography prepass is rooted in docbuild.
    for name in ("docs/references.json", "docs/references.bib"):
        path = ROOT / "docbuild" / name
        digest.update(name.encode() + b"\0" + (path.read_bytes() if path.exists() else b"absent") + b"\0")
    return digest.hexdigest()


def read_stamp(name):
    path = LAKE / name
    return path.read_text().strip() if path.exists() else ""


def prepare(revision):
    key = cache_key()
    database = BUILD / "api-docs.db"
    markers = BUILD / "doc-data"
    # A marker is only evidence of rows in this exact database. Never retain one
    # after a missing database, partial restore, or compatibility change.
    if read_stamp("docs-cache-key") != key or (markers.exists() and not database.is_file()):
        print("Refreshing incompatible or incomplete documentation cache.")
        if BUILD.exists():
            shutil.rmtree(BUILD)
        LAKE.mkdir(parents=True, exist_ok=True)
        (LAKE / "docs-cache-key").write_text(key + "\n")
        (LAKE / "docs-source-rev").unlink(missing_ok=True)

    if read_stamp("docs-source-rev") != revision:
        print(f"Refreshing TDA documentation source links for {revision}.")
        if database.exists():
            # Removed modules/declarations must also leave the global linking and
            # tactics context. Keep dependency data and its matching Lake traces.
            with sqlite3.connect(database) as db:
                db.execute("PRAGMA foreign_keys = ON")
                db.execute("DELETE FROM modules WHERE name = 'TDA' OR name LIKE 'TDA.%'")
        if markers.exists():
            for path in markers.glob("TDA*.doc*"):
                path.unlink()
        # fromDb scans existing pages for navigation and backreferences. Delete
        # the entire rendered site so a smaller import closure cannot leak pages.
        if (BUILD / "doc").exists():
            shutil.rmtree(BUILD / "doc")
        (BUILD / "doc-manifest.json").unlink(missing_ok=True)

    # HTML may have been removed independently of the database/markers.
    if not (BUILD / "doc/index.html").is_file() and markers.exists():
        for path in markers.glob("*.docs_built*"):
            path.unlink()


if __name__ == "__main__":
    if sys.argv[1:] == ["key"]:
        print(cache_key())
    elif len(sys.argv) == 3 and sys.argv[1] == "prepare":
        prepare(sys.argv[2])
    else:
        sys.exit("usage: docs-cache.py key | prepare REVISION")
