#!/usr/bin/env python3
"""Canonical mutable Lake paths; no package downloads or hardware assumptions."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def repository_root(root):
    """Resolve the shared checkout root for linked worktrees, or use a fixture root."""
    root = Path(root).resolve()
    try:
        result = subprocess.run(
            ['git', '-C', str(root), 'rev-parse', '--path-format=absolute', '--git-common-dir'],
            check=False, capture_output=True, text=True)
    except OSError:
        return root
    if result.returncode == 0:
        common_dir = Path(result.stdout.strip()).resolve()
        if common_dir.name == '.git':
            return common_dir.parent
    return root


def artifact_cache_dir(root):
    """Return the shared Lake artifact cache, outside the checkout and its worktrees."""
    root = Path(root).resolve()
    repo_root = repository_root(root)
    configured = os.environ.get('LAKE_CACHE_DIR')
    if configured is not None:
        if not configured:  # Lake treats an explicitly empty value as disabled system cache.
            return None
        path = Path(configured)
        if not path.is_absolute():
            path = Path.cwd() / path
    else:
        path = repo_root.parent / '.cache' / repo_root.name / 'lake-artifacts'
    path = path.resolve()
    for checkout in {root, repo_root}:
        if path == checkout or checkout in path.parents:
            raise ValueError(f'LAKE_CACHE_DIR must be outside the checkout and worktrees: {path}')
    return path


def resources(root):
    paths, seen, scanned = set(), set(), set()
    cache = artifact_cache_dir(root)
    if cache is not None:
        paths.add(str(cache))

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
        manifest = package / 'lake-manifest.json'
        data = json.loads(manifest.read_text()) if manifest.exists() else {}
        lake = package / data.get('lakeDir', '.lake')
        paths.update((lake.resolve(), (lake / 'build').resolve()))
        build_links(lake / 'build')
        packages = package / data.get('packagesDir', str(lake / 'packages'))
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


def check_outputs(root, tool, args):
    if tool == 'lake':
        if len(args) < 2 or args[0] != 'env' or Path(args[1]).name != 'lean':
            return
        args = args[2:]
    outputs = []
    index = 0
    while index < len(args):
        arg = args[index]
        # --run is a compiler flag, not an option-parsing boundary. Conservatively
        # validate output-shaped arguments throughout the invocation.
        if arg in ('-o', '-i', '-c', '-b', '--o', '--i', '--c', '--bc',
                   '--incr-save', '--incr-header-save'):
            index += 1
            outputs.append(args[index])
        elif arg.startswith(('--o=', '--i=', '--c=', '--bc=',
                             '--incr-save=', '--incr-header-save=')):
            outputs.append(arg.split('=', 1)[1])
        elif arg.startswith(('-o', '-i', '-c', '-b')) and not arg.startswith('--'):
            outputs.append(arg[2:])
        index += 1
    if outputs:
        protected = {Path(path) for path in resources(root)}
        for output in outputs:
            path = Path(output).resolve()
            if not any(parent in protected for parent in (path, *path.parents)):
                raise ValueError(f'Lean output outside guarded resources: {output}; '
                                 'use a directory inside this checkout')


if __name__ == '__main__':
    try:
        if sys.argv[1] == '--check-outputs':
            check_outputs(sys.argv[2], sys.argv[3], sys.argv[4:])
        elif sys.argv[1] == '--inherited':
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
        elif sys.argv[1] == '--artifact-cache-dir':
            path = artifact_cache_dir(sys.argv[2])
            print(path or '')
        else:
            for path, mode in lock_plan(sys.argv[1]):
                print(f'{mode}:{path}')
    except (OSError, ValueError, KeyError, RuntimeError, IndexError) as error:
        sys.exit(f'ERROR: cannot determine Lake resources: {error}')
