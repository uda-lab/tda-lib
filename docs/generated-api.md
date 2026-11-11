# Generated API availability

**Generated declaration pages are not published by this repository.** This
lightweight site contains curated Markdown guides, not doc-gen4 output. No
verified hosted API snapshot is linked here, and the site does not imply that an
API snapshot exists for its source revision.

The [API and import guide](api.md) describes the checkout used for this site.
For a release, use the versioned guides in the [changelog](../CHANGELOG.md).
The site banner records the exact checkout commit and identifies modified local
previews; those previews are not immutable revision snapshots.

## Local declaration pages

From a clean checkout, `scripts/build-docs.sh` produces
`docbuild/.lake/build/doc`. It uses Lean, mathlib and doc-gen4 and is independent
of the lightweight site build. See the
[build instructions](../README.md#build-and-documentation) and
[generated-page scope](README.md#generated-api-pages).

An existing local directory is not automatically a verified snapshot. Its
source revision must agree with the successful build record and the embedded
TDA source links; a build cache or historical success report is not a hosted
artifact. The [snapshot maintenance runbook](../docbuild/README.md) describes
how to find and measure existing files, preserve provenance, verify the site,
and plan a separate low-frequency refresh without generating API pages here.

## Connecting a verified snapshot

A future API link must identify the snapshot's full source commit, accessible
storage location, generation and validation scope, and retention or expiry.
Verify the artifact and access before adding the link. If its commit differs from
this site's commit, label it **older/different-revision API snapshot**, never
"current API". A missing, expired or unverified artifact remains unavailable.
Do not construct a public API URL from an assumed hosting convention.
The existing CI artifact, when present and accessible, is temporary: the
workflow requests seven-day retention, and the actual artifact's expiry must
be checked. It is not a permanent API address. No site size, compressed archive
size or fresh validation result is claimed until the corresponding files have
been inspected.
