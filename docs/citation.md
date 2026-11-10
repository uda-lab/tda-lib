# Citing tda-lib

Cite the software version used in your work. The latest published release is
[tda-lib v0.3.0](https://github.com/uda-lab/tda-lib/releases/tag/v0.3.0), published
on 2026-10-29 and distributed under [Apache-2.0](../LICENSE).
The [changelog](../CHANGELOG.md) links to earlier releases and distinguishes their
contents from unreleased development.

If you use `develop`, include the exact commit SHA and a link to that commit.
A release citation alone does not identify later development changes. For a local
checkout, `git rev-parse HEAD` gives its full commit SHA; a GitHub commit link has
the form `https://github.com/uda-lab/tda-lib/commit/<full-SHA>`.

Mathematical papers used by the library are listed in the
[source register](math/references.md). Cite the relevant mathematical sources
separately from the software.

## Updating release citation metadata

When preparing a release, synchronize the root `CITATION.cff` fields `version`,
`date-released` and the release `url` with the actual tag and GitHub Release.
Keep README's release link and dependency example, this guide's release summary,
and the corresponding changelog entry consistent. Release dates refer to the
release's publication date, not the current development commit's date.

Keep author attribution unchanged unless its new form is confirmed. Add a DOI or
ORCID only when its assignment to this software or author has been verified.
Unreleased commits must not acquire a new published version or publication date
merely because development continues.
