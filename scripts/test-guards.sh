#!/usr/bin/env bash
# Self-test for the textual guards' shared lexer (scripts/lean-code-scan.awk), the
# root-aggregator guard, the exposition note check, the live axiom audit's record parsing and
# the build lock.
# Each case is a Lean snippet plus the expected number of violating lines per mode.
# Run after every edit of the lexer:  bash scripts/test-guards.sh
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
fail=0; n=0

# case <name> <expected-sorry-hits> <expected-axiom-hits> <<'EOF' ... EOF
case_() {
  local name="$1" want_s="$2" want_a="$3" f="$tmp/$1.lean" got_s got_a
  cat > "$f"
  n=$((n + 1))
  got_s="$(awk -v mode=sorry -f scripts/lean-code-scan.awk "$f" | wc -l)"
  got_a="$(awk -v mode=axiom -f scripts/lean-code-scan.awk "$f" | wc -l)"
  if [ "$got_s" -ne "$want_s" ] || [ "$got_a" -ne "$want_a" ]; then
    echo "FAIL [$name]: sorry want $want_s got $got_s; axiom want $want_a got $got_a"; fail=1
  fi
}

case_ plain_sorry 1 0 <<'EOF'
theorem t : True := by sorry
EOF
case_ marked_sorry 0 0 <<'EOF'
theorem t : True := by sorry -- ALLOW_SORRY: #12 statement contract
EOF
case_ sorry_in_comments 0 0 <<'EOF'
-- sorry in a line comment
/- sorry in a block comment
   /- nested sorry -/ still comment -/
/-- docstring: this lemma is sorry-free -/
theorem t : True := trivial
EOF
case_ sorry_in_string 0 0 <<'EOF'
def msg : String := "sorry, admit nothing"
EOF
case_ string_with_comment_opener 1 1 <<'EOF'
def marker : String := "/-"
theorem hidden : False := sorry
axiom bad : False
EOF
case_ escaped_quote_in_string 1 0 <<'EOF'
def s : String := "say \"/-\" here"
theorem t : True := by sorry
EOF
case_ multiline_string 1 0 <<'EOF'
def s : String := "line one /-
line two -- sorry inside string
end"
theorem t : True := by admit
EOF
case_ char_literal_quote 1 0 <<'EOF'
def c : Char := '"'
theorem t : True := by sorry
EOF
case_ char_literal_escaped 1 0 <<'EOF'
def c : Char := '\''
def d : Char := '\n'
theorem t : True := by sorry
EOF
case_ primed_identifiers 1 0 <<'EOF'
theorem h' (h'' : True) : True := by sorry
EOF
case_ axiom_forms 0 4 <<'EOF'
axiom a : True
@[simp] private axiom b : True
noncomputable opaque c : Nat
unsafe def d : Nat := 0
EOF
case_ axiom_marked_and_prose 0 0 <<'EOF'
axiom a : True -- ALLOW_AXIOM: #3 owner-authorised
/-- axiom of choice is used via Classical -/
def axiomatic : Nat := 0
def s := "axiom in a string"
EOF
case_ raw_string_with_hash 1 1 <<'EOF'
def raw : String := r#"text" /- still raw"#
theorem hidden : False := sorry
axiom bad : False
EOF
case_ raw_string_plain_and_double_hash 1 0 <<'EOF'
def a : String := r"no escapes \ here /-"
def b : String := r##"one "# inside"##
theorem t : True := by sorry
EOF
case_ raw_string_multiline 1 0 <<'EOF'
def a : String := r#"first
second /- line
third"#
theorem t : True := by sorry
EOF
case_ r_identifier_not_raw 0 0 <<'EOF'
theorem r (hr : True) : True := hr
def arr : Array Nat := #[]
EOF
case_ marker_inside_string_does_not_count 1 1 <<'EOF'
theorem t : True := by let s := "ALLOW_SORRY: #12"; sorry
axiom bad : "ALLOW_AXIOM: #1" = "ALLOW_AXIOM: #1"
EOF
case_ marker_in_block_comment_does_not_count 1 0 <<'EOF'
theorem t : True := by sorry /- ALLOW_SORRY: #12 -/
EOF
case_ marker_in_trailing_comment_counts 0 0 <<'EOF'
theorem t : True := by sorry -- ALLOW_SORRY: #12 landed incomplete on purpose
EOF
case_ interpolated_string 0 0 <<'EOF'
def m (x : Nat) : String := s!"sorry {x} /- not a comment"
theorem t : True := trivial
EOF
case_ interpolation_hole_is_code 1 0 <<'EOF'
def hidden : String := s!"{(by sorry : Nat)}"
EOF
case_ interpolation_hole_nested 1 0 <<'EOF'
def a (x : Nat) : String := s!"{x} and {toString (f "text /-" x)} and {(by admit : Nat)}"
EOF
case_ interpolation_hole_comment_brace 1 0 <<'EOF'
def hidden := s!"{/- } -/ (by sorry : Nat)}"
EOF
case_ interpolation_hole_line_comment 1 0 <<'EOF'
def hidden := s!"{ -- } comment
  (by sorry : Nat)}"
EOF
case_ keyword_ends_line 0 2 <<'EOF'
axiom
  bad : False
unsafe
  def bad2 : Nat := 0
EOF
case_ keyword_ends_line_marked 0 0 <<'EOF'
axiom -- ALLOW_AXIOM: #7 owner-authorised
  ok : True
EOF
case_ interpolation_escaped_brace 0 0 <<'EOF'
def a : String := s!"\{ sorry \} literal braces"
def b : String := m!"sorry in message text"
EOF
case_ escaped_identifier_with_delimiters 2 1 <<'EOF'
def «a--b» : Nat := sorry
theorem «x/-y» : True := by admit
def «sorry» : Nat := 0
def «say "hi"» : Nat := 0
axiom «c--» : False
EOF

# Stable releases reject Issue-authorized holes too; comments remain harmless.
for fixture in marked_sorry plain_sorry; do
  hits="$(awk -v mode=stable -f scripts/lean-code-scan.awk "$tmp/$fixture.lean" | wc -l)"
  if [ "$hits" -ne 1 ]; then echo "FAIL [stable:$fixture]: expected one hole"; fail=1; fi
done
for fixture in sorry_in_comments sorry_in_string; do
  hits="$(awk -v mode=stable -f scripts/lean-code-scan.awk "$tmp/$fixture.lean" | wc -l)"
  if [ "$hits" -ne 0 ]; then echo "FAIL [stable:$fixture]: comment/string counted"; fail=1; fi
done

printf 'private axiom staging : True -- ALLOW_AXIOM: #1 staging\n' > "$tmp/stable-axiom.lean"
hits="$(awk -v mode=stable_axiom -f scripts/lean-code-scan.awk "$tmp/stable-axiom.lean" | wc -l)"
if [ "$hits" -ne 1 ]; then echo "FAIL [stable:marked_axiom]: expected one declaration"; fail=1; fi

if [ "$fail" -eq 0 ]; then echo "guard lexer self-test OK ($n cases)"; else exit 1; fi

# --- root-aggregator guard (scripts/check-root-aggregator.sh) ------------------------------
# Each case runs the real guard inside a fixture repository: a copy of lakefile.toml, the guard,
# the lexer and scripts/rename-project.sh, plus the root module under test.
root_lib="$(sed -n 's/^name = "\(.*\)"$/\1/p' lakefile.toml | head -1)"
rfail=0; rn=0
fixture() {  # fixture <dir>: a minimal repository with the current library layout
  mkdir -p "$1/scripts" "$1/$root_lib"
  cp lakefile.toml "$1/"
  cp scripts/check-root-aggregator.sh scripts/lean-code-scan.awk scripts/rename-project.sh "$1/scripts/"
  printf 'namespace %s\ntheorem basic_ok : True := trivial\nend %s\n' "$root_lib" "$root_lib" > "$1/$root_lib/Basic.lean"
}
root_case() {  # root_case <name> <want: 0 pass | 1 fail> [<lib>] <<'EOF' root module EOF
  local name="$1" want="$2" lib="${3:-$root_lib}" d="$tmp/root-$1" got=0
  rn=$((rn + 1)); fixture "$d"; cat > "$d/$lib.lean"
  bash "$d/scripts/check-root-aggregator.sh" >/dev/null 2>&1 || got=1
  if [ "$got" -ne "$want" ]; then echo "FAIL [root:$name]: want exit $want got $got"; rfail=1; fi
}
root_case valid_aggregator 0 <<'EOF'
-- Library root: imports only.
/-! # Root
Module docs may mention `theorem foo : True := trivial` and
/- a nested -/ block comment. -/
import Mathlib.Data.Real.Basic
import TDA.Basic  -- trailing comment

EOF
root_case module_header_public_import 0 <<'EOF'
module
public import TDA.Basic
EOF
root_case unicode_and_escaped_module_names 0 <<'EOF'
import Foo.Δ
import Foo.«match».Bar
import h'.x?
EOF
root_case command_after_import_same_line 1 <<'EOF'
import TDA.Basic open Nat
EOF
root_case unlisted_command_after_import 1 <<'EOF'
import Lean declare_syntax_cat sneaky
EOF
root_case block_comment_as_separator 1 <<'EOF'
import Lean/-sep-/open/-sep-/Nat
EOF
root_case block_comment_separator_across_lines 1 <<'EOF'
import Lean /- starts here
-/open Nat
EOF
root_case escaped_name_with_comment_delimiter 0 <<'EOF'
import Foo.«A--».«B/-»
EOF
root_case escaped_name_hides_definition 1 <<'EOF'
import Foo.«A--» def leaked : Nat := 0
EOF
root_case two_modules_one_import 1 <<'EOF'
import A.B C.D
EOF
root_case introduced_proof 1 <<'EOF'
import TDA.Basic
theorem extra : True := trivial
EOF
root_case introduced_definition 1 <<'EOF'
import TDA.Basic
/-- a docstring does not excuse the definition -/
def helper : Nat := 0
EOF
root_case introduced_namespace_or_option 1 <<'EOF'
import TDA.Basic
set_option autoImplicit true
EOF
root_case code_after_block_comment_close 1 <<'EOF'
import TDA.Basic
/- looks like a comment
-/ lemma hidden : True := trivial
EOF
root_case continuation_line_proof 1 <<'EOF'
import TDA.Basic
example : True :=
  trivial
EOF
# An area sibling must exist and obey the same imports-only rule.
d="$tmp/root-area"; rn=$((rn + 1)); fixture "$d"
printf 'import %s.Basic\nimport %s.Zone\n' "$root_lib" "$root_lib" > "$d/$root_lib.lean"
mkdir -p "$d/$root_lib/Zone"
printf 'import %s.Basic\n' "$root_lib" > "$d/$root_lib/Zone.lean"
if ! bash "$d/scripts/check-root-aggregator.sh" >/dev/null 2>&1; then
  echo 'FAIL [root:valid-area]: rejected imports-only area'; rfail=1; fi
rn=$((rn + 1))
printf 'theorem hidden : True := trivial\n' >> "$d/$root_lib/Zone.lean"
if bash "$d/scripts/check-root-aggregator.sh" >/dev/null 2>&1; then
  echo 'FAIL [root:area-content]: proof in area aggregator not rejected'; rfail=1; fi
rn=$((rn + 1))
rm "$d/$root_lib/Zone.lean"
if bash "$d/scripts/check-root-aggregator.sh" >/dev/null 2>&1; then
  echo 'FAIL [root:missing-area]: missing area aggregator not rejected'; rfail=1; fi
# Renamed project: rename the fixture with the real script; the guard must check the renamed
# root and catch content in it, with no trace of the template name left to check.
d="$tmp/root-renamed"; rn=$((rn + 1)); fixture "$d"
printf 'import %s.Basic\n' "$root_lib" > "$d/$root_lib.lean"
if ! (cd "$d" && bash scripts/rename-project.sh RenamedLib >/dev/null 2>&1); then
  echo "FAIL [root:renamed]: rename-project.sh failed in the fixture"; rfail=1
elif [ -e "$d/$root_lib.lean" ] || ! bash "$d/scripts/check-root-aggregator.sh" 2>/dev/null | grep -q 'RenamedLib.lean'; then
  echo "FAIL [root:renamed]: guard did not check and pass RenamedLib.lean"; rfail=1
else
  rn=$((rn + 1))
  printf 'def leaked : Nat := 0\n' >> "$d/RenamedLib.lean"
  if bash "$d/scripts/check-root-aggregator.sh" >/dev/null 2>&1; then
    echo "FAIL [root:renamed-content]: definition in RenamedLib.lean not rejected"; rfail=1
  fi
fi
# A `roots` override (bare, quoted or escaped key) and `srcDir` move the root: the guard must
# scan the actual root, not the default <lib>.lean. The default root stays clean in each fixture.
for key in 'roots' '"roots"' "'roots'" '"roots"'; do
  d="$tmp/root-roots-$rn"; rn=$((rn + 1)); fixture "$d"; printf 'import %s.Basic\n' "$root_lib" > "$d/$root_lib.lean"
  printf '%s = ["Other.Top"]\n' "$key" >> "$d/lakefile.toml"
  mkdir -p "$d/Other"; printf 'import A\ntheorem hidden : True := trivial\n' > "$d/Other/Top.lean"
  out="$(bash "$d/scripts/check-root-aggregator.sh" 2>&1 || true)"
  if [[ "$out" != *'Other/Top.lean is the root aggregator'* ]]; then
    echo "FAIL [root:roots $key]: declared root Other/Top.lean not scanned"; rfail=1; fi
done
d="$tmp/root-srcdir"; rn=$((rn + 1)); fixture "$d"; printf 'import %s.Basic\n' "$root_lib" > "$d/$root_lib.lean"
python3 - "$d/lakefile.toml" <<'PY_FIXTURE'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
p.write_text('srcDir = "src"\n' + p.read_text())
PY_FIXTURE
mkdir -p "$d/src"; printf 'import A\ndef x := 0\n' > "$d/src/$root_lib.lean"
out="$(bash "$d/scripts/check-root-aggregator.sh" 2>&1 || true)"
if [[ "$out" != *"src/$root_lib.lean is the root aggregator"* ]]; then
  echo "FAIL [root:srcDir]: src/$root_lib.lean not scanned"; rfail=1; fi
d="$tmp/root-bad-toml"; rn=$((rn + 1)); fixture "$d"; printf 'import %s.Basic\n' "$root_lib" > "$d/$root_lib.lean"
printf 'roots = [`Other]\n' >> "$d/lakefile.toml"
if bash "$d/scripts/check-root-aggregator.sh" >/dev/null 2>&1; then echo "FAIL [root:bad-toml]: not rejected"; rfail=1; fi
# TOML-permitted header spellings still locate the library (and so still scan its root).
for hdr in '[[lean_lib]] # primary library' '[[ lean_lib ]]' '[["lean_lib"]]'; do
  d="$tmp/root-header-$rn"; rn=$((rn + 1)); fixture "$d"; printf 'import %s.Basic\ndef x := 0\n' "$root_lib" > "$d/$root_lib.lean"
  python3 - "$d/lakefile.toml" "$hdr" <<'PY_FIXTURE'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
p.write_text(p.read_text().replace('[[lean_lib]]', sys.argv[2]))
PY_FIXTURE
  out="$(bash "$d/scripts/check-root-aggregator.sh" 2>&1 || true)"
  if ! grep -qF "$hdr" "$d/lakefile.toml" || [[ "$out" != *'is the root aggregator'* ]]; then
    echo "FAIL [root:header '$hdr']: library not found or root content not rejected"; rfail=1
  fi
done
# A root file that does not exist fails closed.
d="$tmp/root-missing"; rn=$((rn + 1)); fixture "$d"
if bash "$d/scripts/check-root-aggregator.sh" >/dev/null 2>&1; then echo "FAIL [root:missing]: not rejected"; rfail=1; fi
# Portability: every awk found must parse the shared lexer and agree, in a UTF-8 locale.
printf 'import Foo.Δ\nimport Foo.«match»\n' > "$tmp/uni.lean"; printf 'import A open B\n' > "$tmp/bad.lean"
for a in gawk mawk nawk; do
  command -v "$a" >/dev/null 2>&1 || continue
  rn=$((rn + 1))
  if ! out="$(LC_ALL=C.UTF-8 "$a" -v mode=root -f scripts/lean-code-scan.awk "$tmp/uni.lean" 2>&1)" || [ -n "$out" ] \
     || [ "$(LC_ALL=C.UTF-8 "$a" -v mode=root -f scripts/lean-code-scan.awk "$tmp/bad.lean" | wc -l)" -ne 1 ]; then
    echo "FAIL [root:awk-$a]: lexer rejected or misjudged under $a: $out"; rfail=1
  fi
done
if [ "$rfail" -eq 0 ]; then echo "root-aggregator guard self-test OK ($rn cases)"; else exit 1; fi

# --- exposition note check (scripts/check-note.sh) ----------------------------------------
# Fixture repositories with a fake latexmk (deterministic) and, when TeX is installed, one real
# build. Asserts the four outcomes stay distinct: NOT CONFIGURED / NOT RUN / FAILED / PASSED.
nfail=0; nn=0
mkdir -p "$tmp/fakebin"
cat > "$tmp/fakebin/latexmk" <<'EOF'
#!/bin/sh
# fake latexmk: -outdir=DIR ... FILE.tex → DIR/FILE.pdf and DIR/FILE.log (content $FAKE_LOG)
out=.; for a in "$@"; do case "$a" in -outdir=*) out="${a#-outdir=}" ;; esac; f="$a"; done
stem="$(basename "$f" .tex)"; mkdir -p "$out"
[ "${FAKE_EXIT:-0}" -eq 0 ] || { echo "! LaTeX Error: fake"; exit "$FAKE_EXIT"; }
printf '%%PDF-1.5 fake\n' > "$out/$stem.pdf"; printf '%s\n' "${FAKE_LOG:-Output written}" > "$out/$stem.log"
EOF
chmod +x "$tmp/fakebin/latexmk"
note_fixture() {  # note_fixture <dir> [<conf-body>] — no conf body means not configured
  mkdir -p "$1/scripts" "$1/docs/note"; cp scripts/check-note.sh "$1/scripts/"
  printf '\\documentclass{article}\\begin{document}x\\end{document}\n' > "$1/docs/note/main.tex"
  [ $# -ge 2 ] && printf '%s\n' "$2" > "$1/docs/note/note.conf"
  return 0
}
note_case() {  # note_case <name> <want-exit> <want-word> <dir> [env…]
  local name="$1" want="$2" word="$3" d="$4" got=0 out; shift 4
  nn=$((nn + 1))
  out="$(env "$@" bash "$d/scripts/check-note.sh" 2>&1)" || got=$?
  if [ "$got" -ne "$want" ] || [[ "$out" != *"$word"* ]]; then
    echo "FAIL [note:$name]: want exit $want with '$word', got $got: $out"; nfail=1; fi
}
FAKE="NOTE_LATEXMK=$tmp/fakebin/latexmk"
note_fixture "$tmp/n1";                              note_case not_configured 0 'NOT CONFIGURED' "$tmp/n1"
note_fixture "$tmp/n2" 'MAIN=main.tex';              note_case configured_no_toolchain 3 'NOT RUN' "$tmp/n2" NOTE_LATEXMK=/nonexistent/latexmk
note_fixture "$tmp/n3" 'MAIN=main.tex';              note_case configured_passes 0 'PASSED' "$tmp/n3" "$FAKE"
note_fixture "$tmp/n4" 'MAIN=main.tex';              note_case build_error 1 'FAILED' "$tmp/n4" "$FAKE" FAKE_EXIT=1
note_fixture "$tmp/n5" 'MAIN=main.tex';              note_case undefined_reference 1 'FAILED' "$tmp/n5" "$FAKE" "FAKE_LOG=LaTeX Warning: Reference \`x' on page 1 undefined on input line 3."
note_fixture "$tmp/n6" 'MAIN=main.tex';              note_case undefined_citation 1 'FAILED' "$tmp/n6" "$FAKE" "FAKE_LOG=LaTeX Warning: Citation \`k' on page 2 undefined on input line 9."
note_fixture "$tmp/n14" 'MAIN=main.tex';             note_case biblatex_undefined_citation 1 'FAILED' "$tmp/n14" "$FAKE" "FAKE_LOG=LaTeX Warning: Citation 'missing' on page 1 undefined on input line 5."
note_fixture "$tmp/n15" 'MAIN=main.tex';             note_case biblatex_missing_entry 1 'FAILED' "$tmp/n15" "$FAKE" "FAKE_LOG=Package biblatex Warning: The following entry could not be found"
note_fixture "$tmp/n7" 'ENGINE=pdflatex; rm -rf /';  note_case engine_injection_rejected 1 'FAILED' "$tmp/n7" "$FAKE"
note_fixture "$tmp/n8" 'MAIN=../../etc/passwd.tex';  note_case main_outside_note_dir 1 'FAILED' "$tmp/n8" "$FAKE"
note_fixture "$tmp/n9" 'MAIN=missing.tex';           note_case missing_main 1 'FAILED' "$tmp/n9" "$FAKE"
note_fixture "$tmp/n13" 'MAIN=escape.tex'; ln -s ../../outside.tex "$tmp/n13/docs/note/escape.tex"
cp "$tmp/n13/docs/note/main.tex" "$tmp/n13/outside.tex"
note_case main_symlink_escape 1 'FAILED' "$tmp/n13" "$FAKE"
note_fixture "$tmp/n10" 'MAIN=main.tex'
printf '\\documentclass{article}\\begin{document}trivially obvious clearly delve\\end{document}\n' > "$tmp/n10/docs/note/main.tex"
note_case no_vocabulary_gate 0 'PASSED' "$tmp/n10" "$FAKE"
if command -v latexmk >/dev/null 2>&1 && command -v pdflatex >/dev/null 2>&1; then
  note_fixture "$tmp/n11" 'ENGINE=pdflatex'
  printf '\\documentclass{article}\\begin{document}\\section{A}\\label{s}See \\ref{s}.\\end{document}\n' > "$tmp/n11/docs/note/main.tex"
  note_case real_build_passes 0 'PASSED' "$tmp/n11"
  note_fixture "$tmp/n12" 'ENGINE=pdflatex'
  printf '\\documentclass{article}\\begin{document}See \\ref{missing}.\\end{document}\n' > "$tmp/n12/docs/note/main.tex"
  note_case real_build_undefined_ref 1 'FAILED' "$tmp/n12"
fi
if [ "$nfail" -eq 0 ]; then echo "note-check self-test OK ($nn cases)"; else exit 1; fi

# --- live axiom audit record parsing (scripts/check-axioms.sh) ----------------------------
# Each case runs the real audit in a fixture repository whose scripts/lean.sh is a stub that
# prints canned `#print axioms` output. Input: the pins, a `---` line, then the Lean output.
# Each check is ='a whole output line that must occur exactly once', +'text the output must
# contain' or -'text it must not contain'.
afail=0; an=0
mkdir -p "$tmp/auditbin"; printf '#!/bin/sh\nexit 0\n' > "$tmp/auditbin/lake"; chmod +x "$tmp/auditbin/lake"
audit_case() {  # audit_case <name> <want-exit> [=line|+text|-text]... <<'EOF' pins --- output EOF
  local name="$1" want="$2" d="$tmp/audit-$1" got=0 out check input; shift 2
  an=$((an + 1)); mkdir -p "$d/scripts/print_axioms"
  cp lakefile.toml "$d/"; cp scripts/check-axioms.sh "$d/scripts/"
  input="$(cat)"
  { printf 'import TDA\n'; printf '%s\n' "$input" | sed '/^---$/,$d' | sed 's/^/#print axioms /'; } > "$d/scripts/print_axioms/Basic.lean"
  printf '%s\n' "$input" | sed '1,/^---$/d' > "$d/lean-output.txt"
  printf '#!/bin/sh\ncat "%s/lean-output.txt"\n' "$d" > "$d/scripts/lean.sh"; chmod +x "$d/scripts/lean.sh"
  out="$(PATH="$tmp/auditbin:$PATH" bash "$d/scripts/check-axioms.sh" 2>&1)" || got=$?
  if [ "$got" -ne "$want" ]; then echo "FAIL [audit:$name]: want exit $want got $got: $out"; afail=1; fi
  for check in "$@"; do
    case "$check" in
      =*) [ "$(grep -cxF -- "${check#=}" <<<"$out" || true)" -eq 1 ] \
            || { echo "FAIL [audit:$name]: want exactly one line '${check#=}': $out"; afail=1; } ;;
      +*) [[ "$out" == *"${check#+}"* ]] || { echo "FAIL [audit:$name]: missing '${check#+}': $out"; afail=1; } ;;
      -*) [[ "$out" != *"${check#-}"* ]] || { echo "FAIL [audit:$name]: unexpected '${check#-}': $out"; afail=1; } ;;
    esac
  done
}
ALLOWED='axioms ⊆ {propext Classical.choice Quot.sound}'
# A bad X must not be excused by an axiom-free X'.
audit_case bad_x_free_xprime 1 '=ERROR: TDA.X is incomplete (depends on sorryAx).' '=OK: TDA.X'"'"' — no axioms.' \
  '-OK: TDA.X — no axioms.' "-ERROR: TDA.X'" <<'EOF'
TDA.X
TDA.X'
---
'TDA.X' depends on axioms: [sorryAx]
'TDA.X'' does not depend on any axioms
EOF
# A bad X' is reported against X' only.
audit_case free_x_bad_xprime 1 "=ERROR: TDA.X' depends on unexpected trust Lean.ofReduceBool." \
  '=OK: TDA.X — no axioms.' '-ERROR: TDA.X ' <<'EOF'
TDA.X
TDA.X'
---
'TDA.X' does not depend on any axioms
'TDA.X'' depends on axioms: [propext, Lean.ofReduceBool]
EOF
# X depends only on allowed axioms, so the bad axiom of X' must not be blamed on X.
audit_case allowed_x_bad_xprime 1 "=ERROR: TDA.X' depends on unexpected trust Lean.ofReduceBool." \
  "=OK: TDA.X — $ALLOWED: [propext]" '-ERROR: TDA.X ' <<'EOF'
TDA.X
TDA.X'
---
'TDA.X' depends on axioms: [propext]
'TDA.X'' depends on axioms: [Lean.ofReduceBool]
EOF
# Each primed pin reports its own list exactly once, unmixed with its siblings.
audit_case primed_family_allowed 0 "=OK: TDA.X — $ALLOWED: [propext Quot.sound]" \
  "=OK: TDA.X' — $ALLOWED: [Classical.choice]" "=OK: TDA.X'' — no axioms." "=AXIOM AUDIT OK — 3 declaration(s) within the allowlist {propext Classical.choice Quot.sound}." <<'EOF'
TDA.X
TDA.X'
TDA.X''
---
'TDA.X' depends on axioms: [propext, Quot.sound]
'TDA.X'' depends on axioms: [Classical.choice]
'TDA.X''' does not depend on any axioms
EOF
audit_case exact_x_absent 1 "=ERROR: no '#print axioms' output for TDA.X (declaration missing or renamed?)." '-OK: TDA.X ' <<'EOF'
TDA.X
TDA.X'
---
'TDA.X'' does not depend on any axioms
EOF
# The name token must start the record: a quoted name later in a line selects nothing.
audit_case match_anchored_at_line_start 1 "=ERROR: no '#print axioms' output for TDA.X (declaration missing or renamed?)." '-OK: TDA.X ' <<'EOF'
TDA.X
TDA.Y
---
'TDA.Y' does not depend on any axioms
note: 'TDA.X' does not depend on any axioms
EOF
audit_case duplicate_pin 1 "+ERROR: TDA.X is pinned 2 times in scripts/print_axioms; pin it once." <<'EOF'
TDA.X
TDA.X
---
'TDA.X' does not depend on any axioms
'TDA.X' does not depend on any axioms
EOF
audit_case duplicate_exact_x 1 "=ERROR: 2 '#print axioms' records for TDA.X; expected exactly one." '-OK: TDA.X ' <<'EOF'
TDA.X
---
'TDA.X' does not depend on any axioms
'TDA.X' depends on axioms: [sorryAx]
EOF
# Lean wraps long lists over several lines; the no-axioms body stands alone.
audit_case wrapped_and_no_axioms 0 "=OK: TDA.W — $ALLOWED: [propext Classical.choice Quot.sound]" \
  '=OK: TDA.N — no axioms.' '-ERROR' <<'EOF'
TDA.W
TDA.N
---
'TDA.W' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TDA.N' does not depend on any axioms
EOF
# Names are compared literally: `.`, `+`, `[...]`, `*` and `\` are neither pattern syntax nor
# escapes, and the decoys that a regex, an unanchored search or escape processing would select
# carry a disallowed axiom.
audit_case punctuation_literal 0 '=OK: TDA.a.b — no axioms.' "=OK: TDA.c+d' — $ALLOWED: [propext]" \
  '=OK: TDA.«e[f]*» — no axioms.' '=OK: TDA.«g\h» — no axioms.' '=OK: TDA.«i\\j» — no axioms.' \
  '=OK: TDA.«k\n» — no axioms.' '-ERROR' <<'EOF'
TDA.a.b
TDA.c+d'
TDA.«e[f]*»
TDA.«g\h»
TDA.«i\\j»
TDA.«k\n»
---
'TDA.aXb' depends on axioms: [sorryAx]
'TDA.a.b'' depends on axioms: [sorryAx]
'Foo.TDA.a.b' depends on axioms: [sorryAx]
'TDA.a.b' does not depend on any axioms
'TDA.c+d'' depends on axioms: [propext]
'TDA.ccd'' depends on axioms: [sorryAx]
'TDA.«ef»' depends on axioms: [sorryAx]
'TDA.«e[f]*»' does not depend on any axioms
'TDA.«g\h»' does not depend on any axioms
'TDA.«gh»' depends on axioms: [sorryAx]
'TDA.«i\j»' depends on axioms: [sorryAx]
'TDA.«i\\j»' does not depend on any axioms
'TDA.«k\n»' does not depend on any axioms
EOF
# A matched record whose body is neither form is rejected, never half-parsed.
for body in 'depends on axioms: propext' 'depends on axioms: []' 'depends on axioms: [propext,]' \
  'depends on axioms: [, propext]' 'depends on axioms: [propext,, Quot.sound]' \
  'depends on axioms: [propext] trailing' 'depends on axioms: [propext] [sorryAx]' \
  'depends on axioms: [propext Quot.sound]' 'depends on axioms: [propext' \
  'does not depend on any axioms, except sorryAx' 'depends on no axioms' ''; do
  audit_case "malformed_$an" 1 "+ERROR: malformed '#print axioms' record for TDA.X:" '-OK: TDA.X ' <<EOF
TDA.X
---
'TDA.X' $body
EOF
done
# Duplicate pins in different areas must fail the same live audit.
d="$tmp/audit-cross-area"; an=$((an + 1)); mkdir -p "$d/scripts/print_axioms"
cp lakefile.toml "$d/"; cp scripts/check-axioms.sh "$d/scripts/"
printf 'import TDA\n#print axioms TDA.X\n' > "$d/scripts/print_axioms/Persistence.lean"
printf 'import TDA\n#print axioms TDA.X\n' > "$d/scripts/print_axioms/Reeb.lean"
printf '%s\n' "'TDA.X' does not depend on any axioms" > "$d/lean-output.txt"
printf '#!/bin/sh\ncat "%s/lean-output.txt"\n' "$d" > "$d/scripts/lean.sh"
chmod +x "$d/scripts/lean.sh"
out="$(PATH="$tmp/auditbin:$PATH" bash "$d/scripts/check-axioms.sh" 2>&1)" && {
  echo 'FAIL [audit:cross-area-duplicate]: duplicate pin accepted'; afail=1;
}
if [[ "$out" != *'TDA.X is pinned 2 times in scripts/print_axioms'* ]]; then
  echo 'FAIL [audit:cross-area-duplicate]: missing duplicate diagnostic'; afail=1; fi
if [ "$afail" -eq 0 ]; then echo "axiom-audit parser self-test OK ($an cases)"; else exit 1; fi

# --- build-lock semantics (scripts/lib/build-lock.sh) ---------------------------------
# Uses the real lock file; skipped when another process holds it for more than 5 s.
LOCK=/tmp/lean-build.lock
if ! flock -w 5 "$LOCK" true; then echo "build-lock self-test SKIPPED (lock busy)"; exit 0; fi
lfail=0
# 1. sourcing acquires the lock: an outside probe cannot take it while the holder lives
if ! bash -c '. scripts/lib/build-lock.sh; ! flock -n /tmp/lean-build.lock true'; then
  echo "FAIL [lock-acquire]: lock not held after sourcing"; lfail=1; fi
# 2. re-entrancy: a child that inherits fd 9 sources the file again without blocking
if ! timeout 5 bash -c '. scripts/lib/build-lock.sh; bash -c ". scripts/lib/build-lock.sh; echo reentered"' | grep -q reentered; then
  echo "FAIL [lock-reentrant]: nested source blocked or failed"; lfail=1; fi
# 3. an environment marker is not a lock: the spoofed caller still has to wait for the holder
if ! timeout 5 bash -c 'exec 9>>/tmp/lean-build.lock; flock 9; LEAN_SCAFFOLD_LOCKED=1 timeout 2 bash -c "exec 9>&-; . scripts/lib/build-lock.sh; echo bypassed" | grep -q bypassed && exit 1; exit 0'; then
  echo "FAIL [lock-spoof]: a caller without the descriptor got past the held lock"; lfail=1; fi
# 4. release: after the holder exits the lock is free again
if ! flock -w 5 -n "$LOCK" true; then echo "FAIL [lock-release]: lock still held after holder exited"; lfail=1; fi
if [ "$lfail" -eq 0 ]; then echo "build-lock self-test OK (4 cases)"; else exit 1; fi

bash scripts/agent/test-build-docs-lock.sh
