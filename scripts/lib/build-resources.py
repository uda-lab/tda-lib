#!/usr/bin/env python3
"""Canonical mutable Lake paths; no package downloads or hardware assumptions."""
import hashlib
import json
import os
from pathlib import Path
import sys


def resources(root):
    paths, seen, scanned = set(), set(), set()

    def build_links(directory):
        directory = directory.resolve()
        if directory in scanned or not directory.is_dir():
            return
        scanned.add(directory)
        # Nested output-directory symlinks can share files even when .lake/build differs.
        for entry in directory.iterdir():
            if entry.is_symlink():
                # A missing output target is still shared when the build creates it.
                paths.add(entry.resolve())
            if entry.is_dir():
                build_links(entry)

    def visit(package):
        package = package.resolve()
        if package in seen:
            return
        seen.add(package)
        # Lock both the checkout and its outputs: either can be a shared symlink.
        paths.add(package)
        lake = package / '.lake'
        paths.update((lake.resolve(), (lake / 'build').resolve()))
        build_links(lake / 'build')
        manifest = package / 'lake-manifest.json'
        data = json.loads(manifest.read_text()) if manifest.exists() else {}
        packages = package / data.get('packagesDir', '.lake/packages')
        paths.add(packages.resolve())
        for entry in data.get('packages', []):
            dependency = (package / entry['dir'] if entry.get('type') == 'path'
                          else packages / entry['name'])
            if entry.get('subDir'):
                dependency /= entry['subDir']
            visit(dependency)
        # Also cover materialized dependencies before/without a manifest.
        if packages.is_dir():
            for dependency in packages.iterdir():
                if dependency.is_dir():
                    visit(dependency)

    visit(Path(root))
    if (Path(root) / 'docbuild/lakefile.toml').exists():
        visit(Path(root) / 'docbuild')
    return sorted(str(path) for path in paths)


def lock_path(path):
    # Stable across checkouts, processes and TMPDIR overrides for this account.
    directory = Path('/tmp') / f'lean-resource-locks-{os.getuid()}'
    directory.mkdir(mode=0o700, exist_ok=True)
    return str(directory / (hashlib.sha256(path.encode()).hexdigest() + '.lock'))


def lock_plan(root):
    paths = resources(root)
    modes = {path: 'X' for path in paths}
    # Shared ancestors detect asymmetric overlap: /shared and /shared/lib conflict,
    # while separate /shared/a and /shared/b can both hold the /shared lock shared.
    for path in paths:
        for parent in Path(path).parents:
            modes.setdefault(str(parent), 'S')
    return sorted((lock_path(path), mode) for path, mode in modes.items())


if __name__ == '__main__':
    try:
        if sys.argv[1] == '--inherited':
            for pair in os.environ.get('LEAN_RESOURCE_LOCK_FDS', '').split():
                descriptor, mode, path = pair.split(':', 2)
                if mode not in ('S', 'X'):
                    continue
                try:
                    held, target = os.fstat(int(descriptor)), os.stat(path)
                except (OSError, ValueError):
                    continue
                if (held.st_dev, held.st_ino) == (target.st_dev, target.st_ino):
                    print(pair)
        elif sys.argv[1] == '--root-lock':
            print(lock_path(str(Path(sys.argv[2]).resolve())))
        else:
            for path, mode in lock_plan(sys.argv[1]):
                print(f'{mode}:{path}')
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        sys.exit(f'ERROR: cannot determine Lake resources: {error}')
