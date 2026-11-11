#!/usr/bin/env python3
"""Build only explicitly curated Markdown. Does not fetch or invoke Lean tools."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "curated-docs"
OUTPUT = WORK / "preview" / "tda-lib"


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-C", str(ROOT), *args], text=True).strip()


def sources(root: Path = ROOT) -> list[str]:
    """Fail closed on duplicate, missing, symlinked or non-curated entries."""
    result = []
    for line in (root / "docsite/sources.txt").read_text().splitlines():
        name = line.strip()
        if not name or name.startswith("#"):
            continue
        path = PurePosixPath(name)
        approved = name in {
            "README.md", "CHANGELOG.md", "docs/README.md", "docs/api.md",
            "docs/citation.md", "docs/generated-api.md",
        } or (path.parent == PurePosixPath("docs/math") and path.suffix == ".md")
        target = root / name
        if (not approved or str(path) != name or name in result
                or any((root / parent).is_symlink() for parent in [path, *path.parents])
                or not target.is_file()):
            raise ValueError(f"Invalid curated source: {name}")
        result.append(name)
    if not result:
        raise ValueError("The curated source allowlist is empty")
    return result


def output_paths() -> None:
    """Reject redirected paths; never inspect or traverse an old preview's children."""
    for path in [ROOT / "build", WORK, WORK / "preview", OUTPUT]:
        if path.is_symlink() or (path.exists() and not path.is_dir()):
            raise ValueError(f"Output path must be a real directory: {path}")


def vendor_assets(root: Path = ROOT) -> dict[str, bytes]:
    """Read only fixed local asset paths, rejecting redirected files/directories."""
    names = ("mathjax-config.js", "tex-svg.js", "MathJax-LICENSE")
    paths = ["docsite/vendor.json", *(f"docsite/assets/{name}" for name in names)]
    for name in paths:
        path = PurePosixPath(name)
        if (not (root / path).is_file()
                or any((root / p).is_symlink() for p in [path, *path.parents])):
            raise ValueError(f"Asset must be a regular repository file: {name}")
    vendor = json.loads((root / "docsite/vendor.json").read_text())
    if set(vendor["files"]) != {"tex-svg.js", "MathJax-LICENSE"}:
        raise ValueError("Unexpected vendored asset inventory")
    data = {name: (root / "docsite/assets" / name).read_bytes() for name in names}
    for name, expected in vendor["files"].items():
        if hashlib.sha256(data[name]).hexdigest() != expected:
            raise ValueError(f"Vendored MathJax checksum mismatch: {name}")
    return data


def install_preview(rendered: Path) -> Path | None:
    """Replace by rename, retaining unknown old data outside the served directory."""
    output_paths()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    previous = None
    if OUTPUT.exists():
        previous = Path(tempfile.mkdtemp(prefix="previous-preview-", dir=WORK))
        OUTPUT.rename(previous / "tda-lib")
    try:
        rendered.rename(OUTPUT)
    except OSError:
        if previous is not None:
            (previous / "tda-lib").rename(OUTPUT)
            previous.rmdir()
        raise
    return previous


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-clean", action="store_true",
                        help="Reject modified/untracked files before preparing an immutable snapshot")
    args = parser.parse_args()
    if Path("/tmp/codex-stop").exists():
        parser.error("/tmp/codex-stop is present")
    names = sources()
    assets = vendor_assets()
    revision = git("rev-parse", "HEAD")
    dirty = bool(git("status", "--porcelain", "--untracked-files=all"))
    if args.require_clean and dirty:
        parser.error("A clean checkout is required; no site was built")
    output_paths()
    WORK.mkdir(parents=True, exist_ok=True)
    committed = set(git("ls-tree", "-r", "--name-only", revision).splitlines())
    info = {
        "source_revision": revision,
        "modified_preview": dirty,
        "api_snapshot": None,
        "preview_prefix": "/tda-lib/",
        "sources": {},
        "committed_files": sorted(committed),
    }
    # MkDocs preserves hidden files and may follow old directory symlinks.
    # Give it a fresh, private tree, never the existing preview directory.
    with tempfile.TemporaryDirectory(prefix="render-", dir=WORK) as temporary:
        staged = Path(temporary) / "sources"
        rendered = Path(temporary) / "site"
        for name in names:
            data = (ROOT / name).read_bytes()
            dest = staged / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            info["sources"][name] = hashlib.sha256(data).hexdigest()
        for name, data in assets.items():
            dest = staged / "assets" / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
        from mkdocs.commands.build import build
        from mkdocs.config import load_config

        config = load_config(
            str(ROOT / "docsite/mkdocs.yml"), docs_dir=str(staged),
            site_dir=str(rendered), strict=True, extra=info,
        )
        build(config)
        info.pop("committed_files")
        from validate import validate
        checked = validate(rendered, names)
        (rendered / "build-info.json").write_text(json.dumps(info, indent=2) + "\n")
        previous = install_preview(rendered)
    if previous is not None:
        print(f"Previous preview retained outside the served tree: {previous}")
    print(f"Validated {checked['local_links_and_assets']} local links, anchors and assets")
    print(f"Built {len(names)} curated pages at {OUTPUT}")
    print(f"Source: {revision}" + (" (modified local preview)" if dirty else " (clean)"))


if __name__ == "__main__":
    main()
