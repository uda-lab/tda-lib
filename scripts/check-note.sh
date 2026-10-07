#!/usr/bin/env bash
# Build and mechanically check the exposition note, if the repository has one.
#
# Inactive until configured: the note lane is opt-in (loop-orchestration-scaffold § Exposition
# lane), and `docs/note/note.conf` is what enables it. Every run ends in exactly one of
#   NOT CONFIGURED  no docs/note/note.conf — nothing was built or validated (exit 0)
#   NOT RUN         configured, but the TeX toolchain is absent — NOT a pass (exit 3)
#   FAILED          configuration error, build error or a mechanical check failed (exit 1)
#   PASSED          the configured note built and the mechanical checks passed (exit 0)
# Only PASSED validates a note; callers that need a validated note check for it.
#
# Mechanical checks only: the build succeeds and the final log reports no undefined or
# multiply-defined references, labels or citations. Vocabulary, register and exposition are
# reviewed by people and review skills, never by a forbidden-word list here.
#
# docs/note/note.conf is read as data (KEY=VALUE lines, never sourced):
#   MAIN=main.tex                 entry file under docs/note/
#   ENGINE=lualatex               pdflatex | lualatex | xelatex
#   TEXLIVE_PACKAGES="…"          Debian packages CI installs (read by .github/workflows/ci.yml)
#
#   scripts/check-note.sh [--text]   --text also writes build/<stem>.txt (pdftotext) for a
#                                    language pass over the rendered text
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

NOTE_DIR="docs/note"
CONF="$NOTE_DIR/note.conf"
LATEXMK="${NOTE_LATEXMK:-latexmk}"
want_text=0
[ "${1:-}" = "--text" ] && want_text=1

if [ ! -f "$CONF" ]; then
  echo "note: NOT CONFIGURED — $CONF absent; no note built or validated (skipped)."
  exit 0
fi

conf_get() {  # conf_get KEY → value with surrounding quotes removed ('' if unset)
  sed -n "s/^[[:space:]]*$1[[:space:]]*=[[:space:]]*//p" "$CONF" | tail -n 1 \
    | sed 's/[[:space:]]*#.*$//; s/^"\(.*\)"$/\1/; s/^'"'"'\(.*\)'"'"'$/\1/'
}
fail() { echo "note: FAILED — $*" >&2; exit 1; }

main="$(conf_get MAIN)"; main="${main:-main.tex}"
engine="$(conf_get ENGINE)"; engine="${engine:-pdflatex}"
case "$main" in
  *..*|/*) fail "MAIN='$main' must be a relative path inside $NOTE_DIR/." ;;
esac
printf '%s' "$main" | grep -qE '^[A-Za-z0-9_./-]+\.tex$' || fail "MAIN='$main' is not a .tex path of [A-Za-z0-9_./-]."
case "$engine" in
  pdflatex) flag=-pdf ;; lualatex) flag=-lualatex ;; xelatex) flag=-xelatex ;;
  *) fail "ENGINE='$engine' must be pdflatex, lualatex or xelatex." ;;
esac
[ -f "$NOTE_DIR/$main" ] || fail "$NOTE_DIR/$main (MAIN) does not exist."
p="$NOTE_DIR"                                  # no symlinked component may lead outside docs/note/
IFS=/ read -r -a comps <<< "$main"
for c in "${comps[@]}"; do
  p="$p/$c"
  [ -L "$p" ] && fail "MAIN component $p is a symlink; the entry file must live inside $NOTE_DIR/."
done

if ! command -v "$LATEXMK" >/dev/null 2>&1; then
  echo "note: NOT RUN — '$LATEXMK' not found; the configured note was NOT validated." >&2
  exit 3
fi

stem="$(basename "$main" .tex)"
out="build"                                   # docs/note/build/, gitignored
buildlog="$(mktemp)"; trap 'rm -f "$buildlog"' EXIT
if ! (cd "$NOTE_DIR" && "$LATEXMK" "$flag" -interaction=nonstopmode -halt-on-error \
        -file-line-error -outdir="$out" "$main") >"$buildlog" 2>&1; then
  tail -n 40 "$buildlog" >&2
  fail "build of $NOTE_DIR/$main with $engine failed (tail above)."
fi

pdf="$NOTE_DIR/$out/$stem.pdf"; texlog="$NOTE_DIR/$out/$stem.log"
[ -s "$pdf" ] || fail "build reported success but $pdf is missing or empty."
[ -f "$texlog" ] || fail "build log $texlog is missing."
# Opening quote is ` (LaTeX kernel) or ' (biblatex); biblatex also reports missing entries.
q="[\`']"
problems="$(grep -E "There were undefined references|There were multiply-defined labels|Reference ${q}[^']*' on page [0-9]+ undefined|Citation ${q}[^']*' (on page [0-9]+ )?undefined|Label ${q}[^']*' multiply defined|The following entry could not be found" "$texlog" || true)"
if [ -n "$problems" ]; then
  printf '%s\n' "$problems" >&2
  fail "unresolved references, citations or duplicate labels in $texlog (above)."
fi

if [ "$want_text" -eq 1 ]; then
  if command -v pdftotext >/dev/null 2>&1; then
    pdftotext -layout "$pdf" "$NOTE_DIR/$out/$stem.txt"
    echo "note: rendered text at $NOTE_DIR/$out/$stem.txt"
  else
    echo "note: pdftotext not found; rendered text NOT produced." >&2
  fi
fi
echo "note: PASSED — $pdf ($engine)."
