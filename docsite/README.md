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

## Separate publication stage

**Preparation is not publication.** This implementation neither enables Pages
nor changes workflows, permissions, repository visibility, credentials, runners,
branch protection or release branches. Existing required CI and review gates
remain unchanged; this is not a new merge/release gate.

Before a separately authorized deployment:

1. Review every `sources.txt` entry and the generated inventory for disclosure,
   third-party rights and mathematical scope. The source register's rights
   evidence is not blanket permission to publish copied papers. Review ordinary
   outbound links too. Do not expose the entire private repository or API cache.
2. Select the exact reviewed source commit from the authorized branch and run
   the build with `--require-clean`. Retain its generated metadata with the
   artifact and record that revision and test evidence in the publication PR.
3. Confirm the actual permitted audience and host. The proposed repository-site
   path is `/tda-lib/`; if GitHub Pages is selected, verify the assigned origin
   before setting `site_url`. No public URL is claimed here. Page/asset URLs are
   relative and the 404 recovery link uses `/tda-lib/`. A different mount path
   requires updating the preview layout, validator and 404 template together.
4. Obtain separate approval for Pages enablement, its audience/source settings
   and the exact deploy workflow. For a GitHub Actions Pages deployment, the
   expected minimum split is a read-only build (`contents: read`) plus a deploy
   job with `pages: write` and `id-token: write` using the `github-pages`
   environment. Verify current GitHub requirements, repository plan/private-site
   support and environment protections; do not assume a private repo gives a
   private website. Do not grant broad write access or create a credential.
5. Publish only the contents of the approved `preview/tda-lib/` artifact. Check
   the actual URL, subpath links/assets, navigation, representative equations,
   revision banner, API-unavailable/older-snapshot label and access controls.
   Report publication only after the deployed artifact and URL are verified.

An authenticated private preview or shared artifact also needs explicit approval
of its recipients and hosting location. The default loopback preview shares
nothing externally.
