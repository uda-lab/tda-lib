# Lightweight documentation site

This is a local/private preview of the curated Markdown guides. It does not build,
fetch or initialize Lean, mathlib or doc-gen4. MkDocs 1.6.1 with its bundled Read
The Docs theme supplies navigation and HTML rendering; no third-party MkDocs
plugins or search service are used. Python-Markdown and PyMdown preserve the
existing tables, fenced code, explicit anchors, Unicode heading anchors and TeX.
PyMdown SuperFences retains indented/list-nested code with language labels.
[mdx-truly-sane-lists 1.3](https://github.com/radude/mdx_truly_sane_lists)
(a small MIT-licensed Python-Markdown extension, pinned from PyPI) preserves the
corpus's two-space nested lists; loose lists remain one list. Display-math
blocks are separated after Markdown handles lists, quotes and literal code;
inline code spans use the pinned renderer's own backtick rules. Adjacent prose
or list text therefore cannot consume TeX delimiters. Corpus tests compare every fenced block and
display formula with its source and check nested-list ownership.
All direct and transitive Python dependencies are pinned in `requirements.txt`.
The supported setup is Python 3.12 on Linux or macOS.

## Build and preview

From the repository root:

```sh
python3 -m venv build/curated-docs/venv
build/curated-docs/venv/bin/python -m pip install -r docsite/requirements.txt
build/curated-docs/venv/bin/python docsite/build.py
build/curated-docs/venv/bin/python docsite/test_site.py
python3 -m http.server 8000 --bind 127.0.0.1 --directory build/curated-docs/preview
```

Open <http://127.0.0.1:8000/tda-lib/>. Stop the server with Ctrl-C. Only the
one-time Python dependency installation needs a package registry. Subsequent
builds and browsing use local files, including the equation renderer and theme
assets. There is no CDN, analytics or external font request. Links to papers,
GitHub and other sources are ordinary outbound links, not embedded resources.
Without JavaScript, protected TeX remains readable as source rather than being
typeset. The HTML/link tests do not substitute for a browser equation/layout check.

For responsive-layout regression checks, open `/tda-lib/docs/api/` at 320, 390
and 1280 CSS-pixel viewport widths, wait for local fonts and MathJax to render,
and evaluate the read-only `docsite/test_layout.js` expression in the browser.
It asserts that the page fits, table identifiers wrap in bounded columns, and
wide tables and typeset display equations retain their full width in local
scrollers.
Also inspect the API table and `#sampled-rips-laws` visually, scroll a wide
formula to both ends, and check the mobile menu. The local `css/curated.css`
override preserves full-size equations rather than shrinking their text.
The probe is not a site asset and adds no browser dependency to the Python build.

Output is generated and ignored under `build/curated-docs/preview/tda-lib/`.
Each build renders and validates in a fresh directory, then replaces the preview
by renaming directories. A prior preview (including hidden files and child
symlinks) is retained unchanged under `build/curated-docs/previous-preview-*/`,
outside the served tree. Inspect those backups before removing any you no longer
need. The builder never follows old child symlinks or cleans unknown user data.
A failed render or validation leaves the prior preview in place. If installation
fails after moving the old tree, the builder attempts to restore that tree and
reports the failure. Retained previews are not automatically deleted, so repeated
builds consume disk space; only the newest `preview/tda-lib/` is served.
Do not run concurrent builders for the same preview.
The build stages only named source files in a temporary directory; do not point
MkDocs at the repository root or copy `docs/` recursively. Use this wrapper,
not a standalone `mkdocs build`, to preserve the allowlist and revision metadata.
Rebuild after editing source Markdown. Tests build once, reject invalid source
entries, check every local link/fragment and asset, ensure all curated pages are
reachable, and fetch the complete output through HTTP under `/tda-lib/`.
They do not contact GitHub, validate external paper URLs, or run Lean/API checks.

## Content and provenance

`sources.txt` is the complete, explicit candidate-publication inventory:

- Root README and changelog.
- Subject guide, API/import guide, software citation guide and generated-API
  availability page.
- Individually named mathematical notes and their source register under
  `docs/math/`. The mathematical-notes landing page gets an alphabetical index
  of exactly these entries at build time.

No glob expands this list. New notes require a reviewed allowlist entry. The
builder rejects duplicates, missing files, traversal and symlinks. Agents'
records, orchestration/ADR/setup documents, contribution policy, scripts,
credentials, paper archives, `.git`, `.lake`, caches and doc-gen output are not
copied. A link to an excluded repository file stays a source link on GitHub,
bound to the full recorded commit, rather than publishing that file. Access to
private source links still requires repository permission. Links to new files
absent from that commit are plain text in modified previews.

Each page displays the source commit and whether this is a modified local
preview. `build-info.json` records that full commit, the dirty flag, the source
inventory and SHA-256 of each input. A modified preview is not an immutable
snapshot of its base commit: its committed-source links can differ from the
preview text. `--require-clean` rejects modified or untracked files before
building an immutable candidate. Final publication evidence must identify a
reviewed, reachable commit; neither `develop` nor a guessed version is an
adequate revision identifier. Build metadata is generated output, never a
tracked status log.

The generated-API availability page deliberately links no hosted API. API
snapshots are a separate, lower-frequency process. Add one only after verifying
its commit, artifact, accessible location, validation scope and retention.
Label a differing revision explicitly; never invent a hosted URL or call an old
snapshot current. The lightweight site does not depend on API generation.
The [API snapshot runbook](../docbuild/README.md) defines the separate provenance,
measurement and storage process. Its operational metadata and measured archives
are not included in this site's curated source inventory.

## Equations and dependency updates

The local `assets/tex-svg.js` is the official **MathJax 3.2.2** combined TeX/SVG
bundle (about 2.1 MiB), distributed under Apache-2.0 with `MathJax-LICENSE`.
`vendor.json` records its exact npm tarball URL, registry integrity and selected
file SHA-256 checksums. The builder verifies those file checksums. SVG output
needs no downloaded fonts; the configuration enables only bundled TeX packages,
disables the menu and does not enable autoload or remote extensions.

For an intentional update, fetch the pinned official `mathjax` package from npm
outside the repository, verify its published integrity, copy only
`es5/tex-svg.js` and `LICENSE`, then update `vendor.json` and review the diff.
Keep the license, rerun the site tests, and inspect representative inline and
block formulas in a browser with no external resource requests. Python upgrades
likewise need a fresh isolated environment, exact direct/transitive pins, tests
and a layout check. Do not vendor the whole package or add a CDN fallback.

## Publication

The curated site is published through
[`.github/workflows/pages.yml`](../.github/workflows/pages.yml). Its `build`
job renders and validates the site — `docsite/build.py --require-clean` and
`docsite/test_site.py` — on every push to `main`, every manual dispatch and
every pull request that touches `docsite/**` or a curated source, without
deploying. Its `deploy` job runs only for a push to `main` or a manual
dispatch on `main`, and publishes to <https://uda-lab.github.io/tda-lib/>
through the `github-pages` deployment environment. The workflow carries no
permission beyond top-level `contents: read`; `pages: write` and
`id-token: write` are scoped to the `deploy` job alone, and no secret is used.

The published revision is always the `main` commit recorded in the built
`build-info.json`'s `source_revision` field and in each page's source banner;
a deployment never carries `modified_preview: true`. Generated API pages are
not part of the published site — see
[Generated API availability](../docs/generated-api.md).

An authenticated private preview or shared artifact outside this workflow
still needs explicit approval of its recipients and hosting location. The
default loopback preview in "Build and preview" above shares nothing
externally.
