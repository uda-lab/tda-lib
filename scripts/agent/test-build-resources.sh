#!/usr/bin/env bash
# Real lock descriptors, fake workloads; no Lean execution or shared caches.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
python3 - "$ROOT" <<'PY'
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

source = Path(sys.argv[1])
with tempfile.TemporaryDirectory(prefix='lean-resources-') as temporary:
    base = Path(temporary)
    def workspace(name):
        root = base / name
        (root / 'scripts/lib').mkdir(parents=True)
        for filename in ('build-lock.sh', 'build-resources.py'):
            (root / 'scripts/lib' / filename).write_bytes((source / 'scripts/lib' / filename).read_bytes())
        return root
    a, b = workspace('a space'), workspace('b')
    def run(root, code, **kwargs):
        env = dict(os.environ, ROOT=str(root))
        env.pop('LEAN_RESOURCE_LOCK_FDS', None)
        return subprocess.Popen(['bash', '-c', '. "$ROOT/scripts/lib/build-lock.sh"; ' + code], env=env, **kwargs)
    def wait_file(path, process):
        end = time.monotonic() + 5
        while not path.exists():
            assert process.poll() is None, 'holder failed before ready'
            assert time.monotonic() < end, 'holder did not become ready'
            time.sleep(.01)
    def pair(shared):
        ready, done, release = [base / name for name in ('ready', 'done', 'release')]
        for p in (ready, done, release):
            p.unlink(missing_ok=True)
        first = run(a, f'touch "{ready}"; while [ ! -e "{release}" ]; do sleep .02; done')
        second = None
        try:
            wait_file(ready, first)
            second = run(b, f'touch "{done}"')
            if shared:
                time.sleep(.2)
                assert not done.exists(), 'shared resource overlapped'
            else:
                assert second.wait(timeout=5) == 0
                assert done.exists(), 'independent workspaces blocked each other'
        finally:
            release.touch()
            assert first.wait(timeout=5) == 0
            if second is not None:
                assert second.wait(timeout=5) == 0
    pair(False)
    # Shared build target via two distinct .lake directories.
    shared = base / 'shared-build'
    shared.mkdir()
    for root in (a, b):
        (root / '.lake').mkdir()
        (root / '.lake/build').symlink_to(shared, target_is_directory=True)
    pair(True)
    for root in (a, b):
        (root / '.lake/build').unlink()
        (root / '.lake/build').mkdir()
        (root / '.lake/build/lib').symlink_to(shared, target_is_directory=True)
    pair(True)
    for root in (a, b):
        (root / '.lake/build/lib').unlink()
    # Asymmetric ancestor/descendant output targets must conflict too.
    shared_lib = shared / 'lib'
    shared_lib.mkdir()
    (a / '.lake/build/lib').symlink_to(shared_lib, target_is_directory=True)
    (b / '.lake/build').rmdir()
    (b / '.lake/build').symlink_to(shared, target_is_directory=True)
    pair(True)
    (a / '.lake/build/lib').unlink()
    (b / '.lake/build').unlink()
    (b / '.lake/build').mkdir()
    # Dangling directory symlinks still identify the future shared output path.
    missing = base / 'not-created' / 'lib'
    for root in (a, b):
        (root / '.lake/build/lib').symlink_to(missing, target_is_directory=True)
    pair(True)
    for root in (a, b):
        (root / '.lake/build/lib').unlink()
    # Shared dependency checkout, including aliased package names.
    dependency = base / 'dependency'
    dependency.mkdir()
    for root, name in ((a, 'dep-a'), (b, 'dep-b')):
        packages = root / '.lake/packages'
        packages.mkdir()
        (packages / name).symlink_to(dependency, target_is_directory=True)
    pair(True)
    # Manifest path dependencies share a target without a packages-directory symlink.
    for root, name in ((a, 'dep-a'), (b, 'dep-b')):
        (root / '.lake/packages' / name).unlink()
        (root / 'lake-manifest.json').write_text(json.dumps({
            'packages': [{'type': 'path', 'name': name, 'dir': '../dependency'}]}))
    pair(True)
    # Same workspace lock reentry; an env marker without descriptors must fail closed.
    assert run(a, 'bash -c \'. "$ROOT/scripts/lib/build-lock.sh"\'').wait(timeout=5) == 0
    forged = dict(os.environ, ROOT=str(a), LEAN_RESOURCE_LOCK_FDS='9:X:/tmp/forged.lock')
    assert subprocess.run(['bash', '-c', '. "$ROOT/scripts/lib/build-lock.sh"'], env=forged,
                          stderr=subprocess.DEVNULL).returncode != 0
    # Failure and interruption release descriptors; independent process can acquire again.
    assert run(a, 'exit 42').wait(timeout=5) == 42
    ready = base / 'kill-ready'
    process = run(a, f'touch "{ready}"; exec sleep 30')
    wait_file(ready, process)
    process.terminate()
    process.wait(timeout=5)
    assert run(a, 'true').wait(timeout=5) == 0
print('resource lock self-tests OK (independent, shared build/dependency symlinks, nested, spoof, failure, termination)')
PY
