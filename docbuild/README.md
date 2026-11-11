# API snapshot maintenance

The [generated API availability page](../docs/generated-api.md) is the reader's
entry point. This runbook is for preserving an **existing, verified** doc-gen4
site and planning a separately authorized refresh. It does not generate or host
API pages. Keep operational observations and validation evidence on the work
Issue/PR, not as a tracked inventory of machines, artifacts or build runs.

## Find the artifact before planning a build

Start with the prior build's Issue/PR and actual machine or Actions run. Record
what was inspected, when, whether files can be read, and any access restriction.
The normal local paths are `docbuild/.lake/build/doc/` and
`docbuild/.lake/docs-source-rev`. These relative paths do not establish that a
particular machine still has a site. No artifact found in a bounded search means
**unavailable in the inspected locations**, not nonexistent everywhere.

The existing [CI workflow](../.github/workflows/ci.yml) runs the docs job on main
pushes or manual runs with `release_check=false`, not ordinary develop pushes or
PRs. It requests seven-day retention for `tda-api-docs`. Inspect the actual run's
artifact ID, creation/expiry timestamps and expired flag, then verify download
access; a successful job or a familiar artifact name alone is insufficient.
The uploaded artifact contains only `docbuild/.lake/build/doc/`: the source
stamp, database, build manifest and cache are **not** included. Preserve run/head
metadata separately and check the embedded source links. Never reconstruct a
missing stamp from the current checkout's HEAD or the download filename.

PR [#767](https://github.com/uda-lab/tda-lib/pull/767) is historical evidence of
generation and validation at its evaluated head, not evidence that its files are
still accessible. Its 6.20 GiB measurement covers the **combined build cache**,
not the rendered site or a compressed site archive. Reuse its generation/cache
implementation, not its measurements as facts about a new artifact.

If bytes, provenance or access are missing, report that precise gap and leave
the API link unavailable. Do not start a heavy rebuild merely to complete this
inventory. Site size, archive size, checksums and present-day validation remain
unmeasured until an actual artifact can be inspected.

## Measure existing bytes

`inspect_snapshot.py` uses only Python's standard library on Linux/macOS; Python
3.12 is the supported setup, as for the lightweight site. It
reads an existing site and optionally an existing archive, and emits JSON to
stdout. It never calls Lean, Lake, GitHub or the network; it neither copies nor
extracts an archive, and it does not update the generator, cache or source stamp.

```sh
python3 docbuild/inspect_snapshot.py docbuild/.lake/build/doc
python3 docbuild/test_snapshot.py -v
```

The site must have a regular `index.html`. All files, including hidden assets,
are included. Symlinks and special files inside the site, and a symlink used as
the site/archive itself, are rejected. Parent path aliases are resolved and the
canonical local paths are recorded. A missing artifact exits nonzero without a
JSON result. `CODEX_STOP_FILE` defaults to `/tmp/codex-stop`.

Measurements have these meanings:

- `site.total_file_bytes` is the sum of regular-file content lengths in bytes,
  **not** disk allocation, cache size or compressed transfer size.
- `site.files` is a path-sorted list of `{path, bytes, sha256}` records, with
  paths relative to the site root. `site.inventory_sha256` hashes that list as
  UTF-8 JSON with sorted keys, ASCII escaping and separators `(',', ':')`.
  This binds file names and contents, not timestamps, permissions or empty
  directories. Identical sites in different directories have the same digest.
- `archive.bytes` and `archive.sha256` describe the supplied archive file, not
  its decoded contents. The helper deliberately does not claim that the archive
  contains the measured site. Omit `--archive` if none exists; its value is null.
- `inspected_at_utc` is inspection time, never a guessed generation time.

Coordinate with the build owner before copying or measuring: no generator or
other writer may change the tree during these operations. Preserve the existing
shared-resource guards; do not run a second builder or bypass its locks. The
helper detects observed file/directory changes and fails, but is not a lock or
a defense against hostile concurrent writers. A hash establishes content
identity, not authenticity, provenance, completeness or working navigation.

For an already quiescent, trusted local site, this optional example creates a
new private staging directory, archives only the site, and measures both. It
does not upload anything. Keep the directory until retention is decided; do not
reuse or overwrite another snapshot's destination.

```sh
(
  set -eu
  site="$(pwd -P)/docbuild/.lake/build/doc"
  work="$(mktemp -d "${TMPDIR:-/tmp}/tda-api-snapshot.XXXXXX")"
  python3 docbuild/inspect_snapshot.py "$site" > "$work/before.json"
  tar -czf "$work/site.tar.gz" -C "$site" .
  python3 docbuild/inspect_snapshot.py "$site" --archive "$work/site.tar.gz" \
    > "$work/measurement.json.tmp"
  mv "$work/measurement.json.tmp" "$work/measurement.json"
  printf 'Private staging directory: %s\n' "$work"
)
```

Compare the before/after inventory digests. Then extract **this self-created
archive** into a new empty directory, inspect that tree, and compare its digest
with `measurement.json`. A matching archive checksum alone does not perform
this comparison. For a downloaded archive, review entry paths and types before
safe extraction; do not blindly apply this step to untrusted archive contents.
Retain a passed round-trip comparison as validation evidence. Never archive the
parent `.lake`, database, dependency packages or credentials for distribution.

## Minimal provenance record

Keep `provenance.json`, `measurement.json` and the site archive together in the
private staging area, outside the measured site. Put their checksums and the
verified storage receipt on the Issue/PR. These are generated artifact metadata,
not tracked repository status files. The format below is a **draft template**,
not a record of an existing snapshot; null means unknown, never zero or passed.

```json
{
  "schema_version": 1,
  "state": "unverified",
  "source_revision": null,
  "generation": {
    "target": null,
    "source_link_mode": null,
    "completed_at_utc": null,
    "evidence_url": null,
    "toolchain": null,
    "pins": {"files": [], "dependencies": []},
    "dependency_check": "not-run"
  },
  "measurement": {
    "file": "measurement.json",
    "sha256": null
  },
  "validation": [],
  "storage": {
    "kind": null,
    "location": null,
    "artifact_id": null,
    "audience": null,
    "access_checked_at_utc": null,
    "expires_at_utc": null,
    "retention_policy": null
  }
}
```

Fill this from evidence, not defaults:

1. `source_revision`: full Git SHA supported by the original successful build
   record, any preserved stamp, and the rendered TDA source links. Resolve a tag
   to its SHA; do not use `latest`, `develop` or current HEAD as a substitute.
   An old stamp can survive a failed build, so a stamp alone does not certify
   the current directory. An exact revision mismatch makes the candidate
   unverified until resolved, not merely an old but verified snapshot.
2. `generation`: record the actual command/target (normally
   `+TDA.Library:docs`), source-link mode (normally `github`), successful completion
   time and build/run evidence. Record the exact toolchain string and each
   dependency's URL and revision from **that source revision's** parent and
   docbuild locks in `pins.dependencies` (`url` and `revision`). Preserve the two
   toolchain files, two lakefiles and two lock files, with their relative `path`
   and `sha256` values in `pins.files`. Include the
   generator pin and the successful `scripts/check-doc-lock.sh` result. File
   mtimes, cache keys and current lock files are not substitutes for this evidence.
3. `measurement`: hash the completed `measurement.json` (for example with
   `shasum -a 256`). This connects the provenance record to the complete site
   inventory and optional archive hash. Keep metadata outside the site to avoid
   a self-referential digest; separately checksum the completed provenance file.
4. `validation`: use entries with `check`, `result` (`passed`, `failed` or
   `not-run`), `scope`, `checked_at_utc` and `evidence_url` or a private evidence
   file plus checksum. State which pages, declarations and links were tested,
   how, and all limitations. A fixture test of the helper does not validate
   a generated API site. Preserve historical evidence as historical, not a new
   direct check. If generation time or other required evidence is unavailable,
   keep it null and the record unverified.
5. `storage`: for local preservation identify the machine and absolute path,
   owner and backup/retention policy; `/tmp` staging is not durable storage. For
   Actions identify the exact run/artifact and observed expiry. For a host use
   the assigned, tested URL and authorized audience, not a guessed URL. Record a
   fresh access check from the intended reader's context. Unknown expiry is not
   indefinite retention; a null expiry is acceptable for a verified record only
   if `retention_policy` explicitly records evidence of no configured expiry.
   Keep private machine paths out of reader-facing pages.

Before `state` can be `verified`, the required provenance must be complete and
the following site checks must pass against the measured bytes:

- Inventory the generated TDA pages and compare with the original build's
  module manifest/target import closure. `TDA.Library` excludes standalone
  examples outside its imports; no fixed historical page count proves this.
- Inspect **all TDA source links** for the exact SHA and expected repository;
  exercise representative line links. Dependency links have their own pins.
- Serve the extracted site over loopback HTTP. Check navigation to each library
  area, a representative declaration and its rendered type/docstring, search
  results for named declarations, and both a TDA cross-link and a Mathlib link.
  Check local link targets/assets and record the actual coverage, including
  whether fragments and JavaScript search behavior were checked.
- Compare the extracted archive's inventory digest with the site digest and
  verify recipient access to the stored bytes. No Lean proof or axiom audit is
  implied by these presentation checks; cite existing checks only for the
  revision and scope they cover.

## Storage and low-frequency refresh

Use the existing seven-day Actions artifact for **temporary authenticated
transfer**, when a successful run actually has one. Download and verify it
before its recorded expiry if longer preservation is needed; expired artifacts
are unavailable, not durable links. An Actions cache is a reusable build input,
subject to eviction, not an archive or a distribution URL.

Until real site/archive sizes and reader requirements are measured, no durable
host is selected. Compare an approved private artifact store (download/archive
access) with an approved static host (browser access). Assess current size/file
limits, authentication, retention/backup, cost and private-repository disclosure
for that measured candidate. Do not assume Pages fits or is private. Enabling
Pages, changing retention/access or publishing requires separate authorization;
this runbook changes none of them.

Plan refreshes for a selected release revision, an explicit request, or a
material API change that makes the retained snapshot unhelpful. These are
planning triggers, not automatic builds or a new merge/release gate. Routine
Markdown edits and PRs do not need full API generation. Before a heavy run,
record the exact target SHA, purpose, execution environment, available compatible
TDA/doc-data caches, thread/resource budget and one necessary validation pass.
Start only when that run is authorized; use `scripts/build-docs.sh` unchanged
from a clean checkout, with the normal resource and stop guards. Do not cold-build
mathlib, remove revision invalidation, or raise the timeout as the sole remedy.

The existing cache key binds toolchain, locks, generator configuration, target
and source-link mode. A different source revision invalidates TDA doc-data and
rendered output before regeneration; never transplant a newer stamp onto older
HTML. Preserve the previous verified archive separately before a refresh, then
measure and validate the new one. Retiring old copies or extending storage
retention is an explicit storage decision, not an automatic cleanup step here.

Only connect a verified, accessible, unexpired candidate through the reader's
availability page. Show its exact revision, validation limits, access method
and expiry. If it differs from the curated site's commit, label it
**older/different-revision API snapshot** and link to the corresponding source
guide as well as the current guide. Recheck access/expiry when changing that
link or planning a refresh; remove or mark an unavailable link instead of
silently substituting another revision. The lightweight site remains usable
without any API artifact.
