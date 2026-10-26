# Claude Code cloud setup

`scripts/claude-cloud-setup.sh` is a standalone Bash script for the Setup Script field in an Anthropic-hosted Claude Code environment. Paste the file contents into that field. It does not require a checked-out repository or GitHub credentials: it creates an isolated project from the checked-in Lean and Lake pins, installs the pinned Elan/Lean toolchain when possible, and runs only `lake exe cache get`. It never runs `lake update` or a library build.

The script stores the prepared project, logs, status, checksum manifest, and next-step instructions under `/root/.cache/tda-lib-claude-setup`; mathlib `.ltar` artifacts go to `/root/.cache/mathlib` so the repository's normal `scripts/bootstrap.sh` can reuse them. Its status is `warm` only when Elan, Lean 4.33.1, all manifest-pinned and clean package sources, and a complete mathlib cache with per-archive checksums are verified. A timeout, missing cache artifact, network failure, or pin mismatch is recorded as partial; partial state is never reported as a warm cache. Each download/install/cache stage has a time limit and an elapsed-time record, with a 250-second overall work budget to leave time for status writing. This budget is an implementation target, not a measurement of Anthropic-hosted runtime.

In each fresh repository checkout, ask Claude to read `/root/.cache/tda-lib-claude-setup/STATUS.txt` and `INSTRUCTIONS.txt`, then run the activation helper. If it reports a pin or existing-path conflict (exit 2 or 4), stop and report it. If it exits 3, inspect the status: run `scripts/bootstrap.sh` only when the current pins match and Lean 4.33.1 is ready; otherwise stop and report. On exit 0, run `scripts/bootstrap.sh` to materialize and revalidate the cache:

```sh
bash scripts/claude-cloud-activate.sh
bash scripts/bootstrap.sh
```

The activation helper compares `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` byte-for-byte before linking cached dependency sources. It also checks every package revision, tracked and untracked source cleanliness, and the saved `.ltar` checksums. It leaves an existing `.lake/packages` path untouched. `scripts/bootstrap.sh` uses the repository's guarded Lean wrapper and mathlib's hash-checked cache to materialize oleans at this checkout's path. If the helper reports a pin/path mismatch, or bootstrap fails, stop before a full build and report the status and relevant log. Do not attempt a cold mathlib source build as a fallback.

Suggested first prompt:

> Read `/root/.cache/tda-lib-claude-setup/STATUS.txt` and `INSTRUCTIONS.txt`, then run `bash scripts/claude-cloud-activate.sh`. If it exits 2 or 4, stop and report. If it exits 3, run `bash scripts/bootstrap.sh` only if Lean 4.33.1 is ready and the repository pins match. On exit 0, run `bash scripts/bootstrap.sh`. Stop before any full build if bootstrap fails.

The current setup project pins `leanprover/lean4:v4.33.1`, mathlib tag `v4.33.1` resolved to commit `0df444a360eaa60ab8c11dca51a86af692955474`, and all transitive revisions from the current `lake-manifest.json`. Keep the embedded files in `scripts/claude-cloud-setup.sh` synchronized with the repository pins; `scripts/test-claude-cloud-setup.py` checks this.

Anthropic's [current cloud-environment documentation](https://code.claude.com/docs/en/cloud-environments#environment-caching) says setup scripts run as root on Ubuntu 24.04 before Claude launches, while the repository is available as a fresh clone to the session. It does not document the clone path or guarantee the checkout is available to the setup script, so this script does not depend on either. Setup-time environment variables are not available. A filesystem snapshot is reused only when setup finishes in roughly five minutes; it expires after roughly seven days and is rebuilt when the script or allowed hosts change. SessionStart hooks run on every session start and resume, so the cache materialization step remains an explicit agent action instead of a heavy hook. A download that itself exceeds the setup window cannot be made reusable by splitting extraction into a session step.

The setup uses GitHub release assets and Mathlib's Azure cache endpoint `lakecache.blob.core.windows.net`. Trusted network access must permit those hosts and package-source downloads. This work does not change environment network rules, Claude account settings, secrets, or permissions. Do not add secrets to the setup script.
