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

## Connecting a verified snapshot

A future API link must identify the snapshot's full source commit, accessible
storage location, generation and validation scope, and retention or expiry.
Verify the artifact and access before adding the link. If its commit differs from
this site's commit, label it **older/different-revision API snapshot**, never
"current API". A missing, expired or unverified artifact remains unavailable.
Do not construct a public API URL from an assumed hosting convention.
