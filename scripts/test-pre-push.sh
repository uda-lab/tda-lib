#!/usr/bin/env bash
# Fast real-Git fixtures for pre-push source binding and CI path classification.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SCRATCH="$ROOT/.agents/scratch"
mkdir -p "$SCRATCH"
TMP="$(mktemp -d "$SCRATCH/pre-push-tests.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

passed=0
failed=0
repo=""
base=""
calls=""
hook_status=0
hook_output=""

pass() {
  passed=$((passed + 1))
  echo "PASS [pre-push:$1]"
}

fail() {
  failed=$((failed + 1))
  echo "FAIL [pre-push:$1] $2" >&2
}

make_repo() {
  name="$1"
  repo="$TMP/$name"
  calls="$TMP/$name.calls"
  mkdir -p "$repo/scripts/hooks" "$repo/scripts/lib" "$repo/TDA" "$repo/.github/workflows"
  cp "$ROOT/.gitignore" "$repo/.gitignore"
  cp "$ROOT/scripts/hooks/pre-push" "$repo/scripts/hooks/pre-push"
  cp "$ROOT/scripts/lib/build-change-classifier.py" "$repo/scripts/lib/build-change-classifier.py"
  cp "$ROOT/scripts/lib/build-resources.py" "$repo/scripts/lib/build-resources.py"
  cp "$ROOT/scripts/lib/remote-gate.py" "$repo/scripts/lib/remote-gate.py"
  for name in check-transient-artifacts.sh check-conflict-markers.sh check-no-sorry.sh check-no-custom-axiom.sh check-root-aggregator.sh check-no-bare-mathlib-import.sh; do
    cat > "$repo/scripts/$name" <<'STUB'
#!/usr/bin/env bash
printf '%s %s\n' "$(basename "$0")" "$*" >> "$CALL_LOG"
STUB
  done
  cat > "$repo/scripts/check.sh" <<'STUB'
#!/usr/bin/env bash
printf 'check.sh %s\n' "$*" >> "$CALL_LOG"
if [ "$MUTATE_DURING_GATE" = 1 ]; then
  printf '\n-- changed during validation\n' >> "$MUTATE_PATH"
fi
if [ -n "${PIN_ADVISORY_FIXTURE:-}" ]; then echo "$PIN_ADVISORY_FIXTURE"; fi
if [ "$GATE_FAIL" = 1 ]; then exit 9; fi
STUB
  git -C "$repo" init -q
  git -C "$repo" config user.name "Pre-push fixture"
  git -C "$repo" config user.email "pre-push@example.invalid"
  printf 'fixture prose\n' > "$repo/README.md"
  printf 'def fixtureLean : True := by trivial\n' > "$repo/TDA/Main.lean"
  git -C "$repo" add -A
  git -C "$repo" commit -qm base
  git -C "$repo" branch -M topic
  base="$(git -C "$repo" rev-parse HEAD)"
  git -C "$repo" update-ref refs/remotes/origin/develop "$base"
  : > "$calls"
}

commit_path() {
  path="$1"
  content="$2"
  mkdir -p "$repo/$(dirname "$path")"
  printf '%s\n' "$content" > "$repo/$path"
  git -C "$repo" add -A
  git -C "$repo" commit -qm "change $path"
}

run_line() {
  hook_input="$1"
  shift || :
  : > "$calls"
  if hook_output="$(cd "$repo" && env CALL_LOG="$calls" MUTATE_PATH="$repo/TDA/Main.lean" TDA_STABLE_RELEASE=0 "$@" bash scripts/hooks/pre-push <<< "$hook_input" 2>&1)"; then
    hook_status=0
  else
    hook_status=$?
  fi
}

run_manual() {
  : > "$calls"
  if hook_output="$(cd "$repo" && env CALL_LOG="$calls" MUTATE_PATH="$repo/TDA/Main.lean" TDA_STABLE_RELEASE=0 "$@" bash scripts/hooks/pre-push </dev/null 2>&1)"; then
    hook_status=0
  else
    hook_status=$?
  fi
}

assert_status() {
  expected="$1"
  label="$2"
  if [ "$hook_status" -eq "$expected" ]; then
    pass "$label"
  else
    fail "$label" "expected exit $expected, got $hook_status: $hook_output"
  fi
}

assert_call() {
  needle="$1"
  label="$2"
  if grep -F "$needle" "$calls" >/dev/null; then
    pass "$label"
  else
    fail "$label" "missing call '$needle'; output: $hook_output"
  fi
}

assert_call_exact() {
  expected="$1"
  label="$2"
  if grep -Fx "$expected" "$calls" >/dev/null; then
    pass "$label"
  else
    fail "$label" "missing exact call '$expected'; output: $hook_output"
  fi
}

assert_index_flag() {
  expected="$1"
  label="$2"
  actual="$(git -C "$repo" ls-files -v -- TDA/Main.lean | cut -c1)"
  if [ "$actual" = "$expected" ]; then
    pass "$label"
  else
    fail "$label" "expected index flag '$expected', got '$actual'"
  fi
}

assert_no_check() {
  label="$1"
  if grep -F 'check.sh ' "$calls" >/dev/null; then
    fail "$label" "unexpected build gate call; output: $hook_output"
  else
    pass "$label"
  fi
}

assert_output_contains() {
  needle="$1"
  label="$2"
  case "$hook_output" in
    *"$needle"*) pass "$label" ;;
    *) fail "$label" "missing '$needle' in output: $hook_output" ;;
  esac
}

zero_oid() {
  length="$(printf '%s' "$1" | wc -c | tr -d ' ')"
  printf '%*s' "$length" '' | tr ' ' 0
}

classifier="$ROOT/scripts/lib/build-change-classifier.py"
paths="$TMP/classifier.paths"
matches="$TMP/classifier.matches"
printf '%s\0' 'TDA/Basic.lean' 'TDA/with space.lean' 'scripts/check-note.txt' '.github/workflows/ci.yml' 'lakefile.toml' 'lake-manifest.json' 'lean-toolchain' 'comparator.json' > "$paths"
printf '%s\0' $'TDA/tab\tname.lean' $'TDA/line\nname.lean' 'TDA/数学.lean' >> "$paths"
if python3 "$classifier" < "$paths" > "$matches"; then
  pass classifier_build_categories_and_quoted_paths
else
  fail classifier_build_categories_and_quoted_paths "build-relevant paths were missed"
fi
printf '%s\0' 'README.md' 'docs/guide.md' 'docbuild/lakefile.toml' 'src/comparator.json' > "$paths"
if python3 "$classifier" < "$paths" > "$matches"; then
  fail classifier_prose_and_nested_config "non-build paths classified as build-relevant"
else
  status=$?
  if [ "$status" -eq 1 ]; then pass classifier_prose_and_nested_config; else fail classifier_prose_and_nested_config "unexpected classifier status $status"; fi
fi
printf 'TDA/Main.lean' > "$paths"
if python3 "$classifier" < "$paths" > "$matches"; then
  fail classifier_malformed_input "malformed input accepted"
else
  status=$?
  if [ "$status" -eq 2 ]; then pass classifier_malformed_input; else fail classifier_malformed_input "expected error 2, got $status"; fi
fi
python3 - "$paths" <<'PY'
import sys
with open(sys.argv[1], "wb") as output:
    for index in range(18000):
        output.write(("docs/" + str(index).zfill(6) + "x" * 120 + ".txt").encode() + b"\0")
    output.write(b"TDA/last-in-large-list.lean\0")
PY
if python3 "$classifier" < "$paths" > "$matches"; then
  pass classifier_large_list_no_sigpipe
else
  fail classifier_large_list_no_sigpipe "large NUL list failed classification"
fi
if grep -F 'scripts/lib/build-change-classifier.py' "$ROOT/.github/workflows/ci.yml" >/dev/null; then
  pass ci_uses_shared_classifier
else
  fail ci_uses_shared_classifier "workflow no longer calls the shared classifier"
fi

make_repo prose_only
commit_path README.md changed
target="$(git -C "$repo" rev-parse HEAD)"
run_line "refs/heads/topic $target refs/heads/topic $base"
assert_status 0 prose_only_push_passes
assert_no_check prose_only_push_skips_build

make_repo script_only
commit_path scripts/tool.txt changed
target="$(git -C "$repo" rev-parse HEAD)"
pin_advisory="PIN TYPE ADVISORY: fixture mentions private helper"
run_line "refs/heads/topic $target refs/heads/topic $base" PIN_ADVISORY_FIXTURE="$pin_advisory"
if grep -Fxq "$pin_advisory" <<< "$hook_output"; then
  pass visible_pin_advisory
else
  fail visible_pin_advisory "$hook_output"
fi
assert_status 0 script_only_push_passes
assert_call 'check.sh --incremental' script_only_uses_incremental_gate

make_repo workflow_only
commit_path .github/workflows/ci.yml changed
target="$(git -C "$repo" rev-parse HEAD)"
run_line "refs/heads/topic $target refs/heads/topic $base"
assert_status 0 workflow_only_push_passes
assert_call 'check.sh --incremental' workflow_only_uses_incremental_gate

make_repo unusual_names
mkdir -p "$repo/TDA"
printf 'def a : True := by trivial\n' > "$repo/TDA/space name.lean"
printf 'def b : True := by trivial\n' > "$repo/TDA/tab	name.lean"
printf 'def c : True := by trivial\n' > "$repo/TDA/line
name.lean"
printf 'def d : True := by trivial\n' > "$repo/TDA/数学.lean"
git -C "$repo" add -A
git -C "$repo" commit -qm unusual
target="$(git -C "$repo" rev-parse HEAD)"
run_line "refs/heads/topic $target refs/heads/topic $base"
assert_status 0 unusual_lean_names_push_passes
assert_call 'check.sh --incremental' unusual_lean_names_use_incremental_gate

make_repo rename_away
git -C "$repo" mv TDA/Main.lean TDA/Main.txt
git -C "$repo" commit -qm rename-away
target="$(git -C "$repo" rev-parse HEAD)"
run_line "refs/heads/topic $target refs/heads/topic $base"
assert_status 0 rename_away_push_passes
assert_call 'check.sh --incremental' rename_away_lean_deletion_uses_gate

make_repo pushed_non_head
commit_path scripts/tool.txt child
child="$(git -C "$repo" rev-parse HEAD)"
git -C "$repo" reset --hard -q "$base"
run_line "refs/heads/topic $child refs/heads/topic $base"
assert_status 1 pushed_non_head_rejected
assert_no_check pushed_non_head_never_validated_unrelated_tree

make_repo dirty_index
printf 'staged change\n' >> "$repo/README.md"
git -C "$repo" add README.md
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 1 dirty_index_rejected

make_repo dirty_worktree
printf 'unstaged change\n' >> "$repo/README.md"
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 1 dirty_worktree_rejected

make_repo clean_filter_conceal
# Reproduce the source mismatch that clean filters can hide from Git's worktree diff.
cp "$ROOT/scripts/check-no-sorry.sh" "$repo/scripts/check-no-sorry.sh"
cp "$ROOT/scripts/lean-code-scan.awk" "$repo/scripts/lean-code-scan.awk"
git -C "$repo" add scripts/check-no-sorry.sh scripts/lean-code-scan.awk
git -C "$repo" commit -qm real_no_sorry_guard
printf 'def fixtureLean : False := by sorry\n' > "$repo/TDA/Main.lean"
git -C "$repo" add TDA/Main.lean
git -C "$repo" commit -qm sorry_blob
cp "$repo/TDA/Main.lean" "$repo/.git/fixture-lean.blob"
printf 'def fixtureLean : True := by trivial\n' > "$repo/TDA/Main.lean"
cat > "$repo/.git/clean-filter" <<'FILTER'
#!/usr/bin/env bash
set -euo pipefail
printf 'called\n' >> "$FILTER_LOG"
cat "$FILTER_BLOB"
FILTER
chmod +x "$repo/.git/clean-filter"
printf 'TDA/Main.lean filter=conceal\n' > "$repo/.git/info/attributes"
git -C "$repo" config filter.conceal.clean "$repo/.git/clean-filter"
filter_log="$TMP/clean-filter.log"
: > "$filter_log"
if (cd "$repo" && bash scripts/check-no-sorry.sh); then
  pass clean_filter_fixture_raw_proof_passes_real_no_sorry_guard
else
  fail clean_filter_fixture_raw_proof_passes_real_no_sorry_guard "real no-sorry guard rejected the proved worktree source"
fi
if grep -F 'sorry' "$repo/.git/fixture-lean.blob" >/dev/null; then
  pass clean_filter_fixture_committed_blob_contains_sorry
else
  fail clean_filter_fixture_committed_blob_contains_sorry "fixture's committed blob lacks the concealed sorry"
fi
: > "$filter_log"
if (cd "$repo" && FILTER_LOG="$filter_log" FILTER_BLOB="$repo/.git/fixture-lean.blob" git diff --quiet --no-ext-diff --no-textconv HEAD --); then
  pass clean_filter_fixture_diff_conceals_raw_worktree_change
else
  status=$?
  fail clean_filter_fixture_diff_conceals_raw_worktree_change "expected clean-filtered diff equality, got exit $status"
fi
if grep -F 'called' "$filter_log" >/dev/null; then
  pass clean_filter_fixture_concealment_executes_clean_filter
else
  fail clean_filter_fixture_concealment_executes_clean_filter "Git diff did not execute the configured clean filter"
fi
: > "$filter_log"
cp "$repo/TDA/Main.lean" "$TMP/clean-filter-source"
target="$(git -C "$repo" rev-parse HEAD)"
run_line "refs/heads/topic $target refs/heads/topic $base" FILTER_LOG="$filter_log" FILTER_BLOB="$repo/.git/fixture-lean.blob"
assert_status 1 clean_filter_hidden_source_rejected
case "$hook_output" in
  *"tracked file has a clean filter attribute configured before"*) pass clean_filter_attribute_rejected_before_identity_diff ;;
  *) fail clean_filter_attribute_rejected_before_identity_diff "hook did not fail closed on filter attributes: $hook_output" ;;
esac
if [ ! -s "$filter_log" ]; then
  pass clean_filter_not_executed_by_hardened_hook
else
  fail clean_filter_not_executed_by_hardened_hook "hook executed the configured clean filter"
fi
if cmp -s "$TMP/clean-filter-source" "$repo/TDA/Main.lean"; then
  pass clean_filter_hardened_hook_preserves_raw_source
else
  fail clean_filter_hardened_hook_preserves_raw_source "hook changed the proved worktree source"
fi
if [ ! -s "$calls" ]; then
  pass clean_filter_rejected_before_any_gate
else
  fail clean_filter_rejected_before_any_gate "gate calls occurred before filter rejection: $(cat "$calls")"
fi

make_repo disabled_filter_attribute
printf 'TDA/Main.lean -filter\n' > "$repo/.git/info/attributes"
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 0 unset_filter_attribute_allows_clean_source
assert_no_check unset_filter_attribute_skips_unneeded_build

for reserved_driver in unset unspecified; do
  make_repo "reserved_filter_$reserved_driver"
  cp "$repo/TDA/Main.lean" "$repo/.git/reserved-filter-blob"
  printf 'def fixtureLean : True := by decide\n' > "$repo/TDA/Main.lean"
  cat > "$repo/.git/reserved-clean-filter" <<'FILTER'
#!/usr/bin/env bash
set -euo pipefail
printf 'called\n' >> "$FILTER_LOG"
cat "$FILTER_BLOB"
FILTER
  chmod +x "$repo/.git/reserved-clean-filter"
  printf 'TDA/Main.lean filter=%s\n' "$reserved_driver" > "$repo/.git/info/attributes"
  git -C "$repo" config "filter.$reserved_driver.clean" "$repo/.git/reserved-clean-filter"
  attr_output="$(git -C "$repo" check-attr filter -- TDA/Main.lean)"
  case "$attr_output" in
    *": filter: $reserved_driver") pass "reserved_filter_${reserved_driver}_attribute_reports_sentinel" ;;
    *) fail "reserved_filter_${reserved_driver}_attribute_reports_sentinel" "unexpected check-attr output: $attr_output" ;;
  esac
  filter_log="$TMP/reserved-filter-$reserved_driver.log"
  : > "$filter_log"
  if (cd "$repo" && FILTER_LOG="$filter_log" FILTER_BLOB="$repo/.git/reserved-filter-blob" git diff --quiet --no-ext-diff --no-textconv HEAD --); then
    pass "reserved_filter_${reserved_driver}_diff_conceals_raw_change"
  else
    status=$?
    fail "reserved_filter_${reserved_driver}_diff_conceals_raw_change" "expected concealed diff equality, got exit $status"
  fi
  if grep -F 'called' "$filter_log" >/dev/null; then
    pass "reserved_filter_${reserved_driver}_driver_is_active"
  else
    fail "reserved_filter_${reserved_driver}_driver_is_active" "configured clean filter did not run"
  fi
  : > "$filter_log"
  run_line "refs/heads/topic $base refs/heads/topic $base" FILTER_LOG="$filter_log" FILTER_BLOB="$repo/.git/reserved-filter-blob"
  assert_status 1 "reserved_filter_${reserved_driver}_rejected"
  assert_output_contains "reserved clean-filter driver name is configured before" "reserved_filter_${reserved_driver}_fails_closed"
  if [ ! -s "$filter_log" ]; then
    pass "reserved_filter_${reserved_driver}_not_executed_by_hook"
  else
    fail "reserved_filter_${reserved_driver}_not_executed_by_hook" "hook executed the configured clean filter"
  fi
done

make_repo failed_filter_query
target="$base"
git_bin="$(command -v git)"
mkdir -p "$TMP/filter-test-bin"
cat > "$TMP/filter-test-bin/git" <<'WRAPPER'
#!/usr/bin/env bash
if [ "$1" = check-attr ]; then exit 42; fi
exec "$REAL_GIT" "$@"
WRAPPER
chmod +x "$TMP/filter-test-bin/git"
run_line "refs/heads/topic $target refs/heads/topic $base" REAL_GIT="$git_bin" PATH="$TMP/filter-test-bin:$PATH"
assert_status 1 failed_filter_query_rejected
case "$hook_output" in
  *"could not inspect tracked clean-filter attributes before"*) pass failed_filter_query_fails_closed ;;
  *) fail failed_filter_query_fails_closed "filter query error was not reported: $hook_output" ;;
esac
assert_no_check failed_filter_query_never_runs_build_gate

make_repo failed_reserved_filter_config_query
target="$base"
cat > "$TMP/filter-test-bin/git" <<'WRAPPER'
#!/usr/bin/env bash
if [ "$1" = config ]; then
  for arg in "$@"; do
    if [ "$arg" = --get-regexp ]; then exit 42; fi
  done
fi
exec "$REAL_GIT" "$@"
WRAPPER
chmod +x "$TMP/filter-test-bin/git"
run_line "refs/heads/topic $target refs/heads/topic $base" REAL_GIT="$git_bin" PATH="$TMP/filter-test-bin:$PATH"
assert_status 1 failed_reserved_filter_config_query_rejected
assert_output_contains "could not inspect reserved clean-filter driver configuration before" failed_reserved_filter_config_query_fails_closed
assert_no_check failed_reserved_filter_config_query_never_runs_build_gate

make_repo external_diff_conceal
printf 'TDA/Main.lean diff=conceal\n' > "$repo/.git/info/attributes"
git -C "$repo" config diff.conceal.command true
git -C "$repo" config diff.conceal.trustExitCode true
printf 'def concealed : True := by trivial\n' > "$repo/TDA/Main.lean"
if env -u GIT_NO_REPLACE_OBJECTS git -C "$repo" diff --quiet HEAD --; then
  pass external_diff_fixture_hides_unstaged_change
else
  status=$?
  if [ "$status" -eq 1 ]; then
    echo "SKIP [pre-push:external_diff_fixture_hides_unstaged_change] $(git --version) does not reproduce trusted external-diff concealment"
  else
    fail external_diff_fixture_hides_unstaged_change "Git diff failed with exit $status"
  fi
fi
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 1 external_diff_concealed_worktree_rejected
case "$hook_output" in
  *"tracked worktree differs from pushed commit"*) pass external_diff_disabled_for_worktree_check ;;
  *) fail external_diff_disabled_for_worktree_check "hook did not detect unstaged source bytes: $hook_output" ;;
esac

make_repo textconv_conceal
printf 'TDA/Main.lean diff=conceal\n' > "$repo/.git/info/attributes"
git -C "$repo" config diff.conceal.textconv "sh -c 'printf constant'"
printf 'def textconvHidden : True := by trivial\n' > "$repo/TDA/Main.lean"
git -C "$repo" add TDA/Main.lean
if git -C "$repo" diff --quiet --cached "$base" --; then
  pass textconv_fixture_hides_staged_change
else
  status=$?
  if [ "$status" -eq 1 ]; then
    echo "SKIP [pre-push:textconv_fixture_hides_staged_change] $(git --version) does not reproduce textconv concealment"
  else
    fail textconv_fixture_hides_staged_change "Git diff failed with exit $status"
  fi
fi
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 1 textconv_concealed_index_rejected
case "$hook_output" in
  *"index differs from pushed commit"*) pass textconv_disabled_for_index_check ;;
  *) fail textconv_disabled_for_index_check "hook did not detect staged source bytes: $hook_output" ;;
esac

make_repo assume_unchanged_source
git -C "$repo" update-index --assume-unchanged TDA/Main.lean
printf 'def hidden : True := by trivial\n' > "$repo/TDA/Main.lean"
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 1 assume_unchanged_source_rejected
assert_index_flag h assume_unchanged_flag_preserved

make_repo skip_worktree_source
git -C "$repo" update-index --skip-worktree TDA/Main.lean
printf 'def hidden : True := by trivial\n' > "$repo/TDA/Main.lean"
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 1 skip_worktree_source_rejected
assert_index_flag S skip_worktree_flag_preserved

make_repo untracked_source
printf 'def untracked : True := by trivial\n' > "$repo/Untracked.lean"
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 1 relevant_untracked_source_rejected

make_repo ignored_untracked_source
printf 'TDA/Hidden.lean\n' > "$TMP/global-excludes"
git -C "$repo" config core.excludesFile "$TMP/global-excludes"
printf 'def hidden : True := by trivial\n' > "$repo/TDA/Hidden.lean"
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 1 relevant_ignored_untracked_source_rejected

make_repo ignored_generated_artifacts
mkdir -p "$repo/.lake/build" "$repo/.agents/scratch"
printf 'generated Lean artifact\n' > "$repo/.lake/build/Generated.lean"
printf 'local scratch\n' > "$repo/.agents/scratch/experiment.lean"
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 0 ignored_generated_artifacts_allowed
assert_no_check ignored_generated_artifacts_skip_build

make_repo same_commit_multi_ref
commit_path scripts/tool.txt shared
target="$(git -C "$repo" rev-parse HEAD)"
zero="$(zero_oid "$target")"
run_line "refs/heads/one $target refs/heads/one $base
refs/heads/two $target refs/heads/two $zero"
assert_status 0 same_commit_multi_ref_passes
count="$(grep -c '^check-transient-artifacts.sh ' "$calls" || true)"
if [ "$count" -eq 1 ]; then pass same_commit_refs_deduplicate_artifact_guards; else fail same_commit_refs_deduplicate_artifact_guards "guard ran $count times"; fi
count="$(grep -c '^check.sh ' "$calls" || true)"
if [ "$count" -eq 1 ]; then pass same_commit_refs_run_one_build_gate; else fail same_commit_refs_run_one_build_gate "gate ran $count times"; fi

make_repo different_commit_multi_ref
commit_path scripts/one.txt first
first="$(git -C "$repo" rev-parse HEAD)"
commit_path README.md second
second="$(git -C "$repo" rev-parse HEAD)"
run_line "refs/heads/one $first refs/heads/one $base
refs/heads/two $second refs/heads/two $base"
assert_status 1 different_commit_multi_ref_rejected
assert_no_check different_commit_multi_ref_never_borrows_gate

make_repo lightweight_tag
git -C "$repo" tag light
target="$(git -C "$repo" rev-parse refs/tags/light)"
zero="$(zero_oid "$target")"
run_line "refs/tags/light $target refs/tags/light $zero"
assert_status 0 lightweight_tag_passes
assert_call 'check.sh --stable' lightweight_tag_uses_stable_gate

make_repo annotated_tag
git -C "$repo" tag -a annotated -m annotated "$base"
tag_oid="$(git -C "$repo" rev-parse refs/tags/annotated)"
zero="$(zero_oid "$tag_oid")"
run_line "refs/tags/annotated $tag_oid refs/tags/annotated $zero"
assert_status 0 annotated_tag_peels_to_head
assert_call 'check.sh --stable' annotated_tag_uses_stable_gate

make_repo noncommit_tag
tree="$(git -C "$repo" rev-parse 'HEAD^{tree}')"
git -C "$repo" update-ref refs/tags/tree "$tree"
zero="$(zero_oid "$tree")"
run_line "refs/tags/tree $tree refs/tags/tree $zero"
assert_status 1 noncommit_tag_rejected

make_repo replacement_ref
commit_path README.md target_commit
target="$(git -C "$repo" rev-parse HEAD)"
commit_path TDA/Main.lean replacement_tree
replacement="$(git -C "$repo" rev-parse HEAD)"
git -C "$repo" reset --hard -q "$target"
git -C "$repo" replace "$target" "$replacement"
printf 'replacement_tree\n' > "$repo/TDA/Main.lean"
if env -u GIT_NO_REPLACE_OBJECTS git -C "$repo" diff --quiet HEAD --; then
  pass replacement_ref_fixture_hides_tree_mismatch
else
  fail replacement_ref_fixture_hides_tree_mismatch "fixture did not reproduce replacement-aware clean diff"
fi
run_line "refs/heads/topic $target refs/heads/topic $base"
assert_status 1 replacement_ref_worktree_mismatch_rejected
case "$hook_output" in
  *"tracked worktree differs from pushed commit"*) pass replacement_refs_disabled_for_source_check ;;
  *) fail replacement_refs_disabled_for_source_check "hook did not report actual target-tree mismatch: $hook_output" ;;
esac

make_repo deletion_only
printf 'dirty\n' >> "$repo/README.md"
printf 'def dirty : True := by trivial\n' > "$repo/Dirty.lean"
zero="$(zero_oid "$base")"
run_line "refs/heads/topic $zero refs/heads/topic $base"
assert_status 0 deletion_only_ignores_dirty_checkout
if [ ! -s "$calls" ]; then pass deletion_only_skips_all_validation; else fail deletion_only_skips_all_validation "validation ran for deletion-only push"; fi

make_repo deletion_unborn_head
git -C "$repo" checkout --orphan unborn >/dev/null 2>&1
zero="$(zero_oid "$base")"
run_line "refs/heads/topic $zero refs/heads/topic $base"
assert_status 0 deletion_only_allows_unborn_head
if [ ! -s "$calls" ]; then pass unborn_deletion_skips_all_validation; else fail unborn_deletion_skips_all_validation "validation ran for deletion-only push"; fi

make_repo mixed_delete_update
commit_path scripts/tool.txt update
target="$(git -C "$repo" rev-parse HEAD)"
zero="$(zero_oid "$base")"
run_line "refs/heads/deleted $zero refs/heads/deleted $base
refs/heads/topic $target refs/heads/topic $base"
assert_status 0 mixed_delete_update_passes
assert_call 'check.sh --incremental' mixed_delete_update_validates_update

make_repo manual_invocation
commit_path scripts/tool.txt manual
run_manual
assert_status 0 manual_invocation_uses_head
assert_call 'check.sh --incremental' manual_invocation_runs_incremental_gate

make_repo missing_base
git -C "$repo" update-ref -d refs/remotes/origin/develop
commit_path TDA/Added.lean changed
target="$(git -C "$repo" rev-parse HEAD)"
zero="$(zero_oid "$base")"
run_line "refs/heads/new $target refs/heads/new $zero"
assert_status 0 missing_base_runs_full_gate
assert_call_exact 'check.sh ' missing_base_selects_full_gate

make_repo failed_diff
commit_path TDA/Added.lean changed
target="$(git -C "$repo" rev-parse HEAD)"
zero="$(zero_oid "$base")"
git_bin="$(command -v git)"
mkdir -p "$TMP/test-bin"
cat > "$TMP/test-bin/git" <<'WRAPPER'
#!/usr/bin/env bash
if [ "$1" = diff ] && [ ! -e "$FAIL_DIFF_MARKER" ]; then
  for arg in "$@"; do
    if [ "$arg" = --name-only ]; then
      : > "$FAIL_DIFF_MARKER"
      exit 42
    fi
  done
fi
exec "$REAL_GIT" "$@"
WRAPPER
chmod +x "$TMP/test-bin/git"
run_line "refs/heads/new $target refs/heads/new $zero" REAL_GIT="$git_bin" FAIL_DIFF_MARKER="$TMP/fail-diff" PATH="$TMP/test-bin:$PATH"
assert_status 0 failed_diff_runs_full_gate
assert_call_exact 'check.sh ' failed_diff_selects_full_gate

make_repo changed_during_gate
commit_path TDA/Changed.lean changed
target="$(git -C "$repo" rev-parse HEAD)"
run_line "refs/heads/topic $target refs/heads/topic $base" MUTATE_DURING_GATE=1
assert_status 1 source_change_during_gate_rejected

make_repo destination_main
target="$base"
zero="$(zero_oid "$target")"
run_line "refs/heads/topic $target refs/heads/main $zero"
assert_status 0 destination_main_passes
assert_call 'check.sh --stable' destination_main_uses_stable_gate

make_repo checkout_main
git -C "$repo" branch -M main
run_line "refs/heads/topic $base refs/heads/topic $base"
assert_status 0 checkout_main_passes
assert_call 'check.sh --stable' checkout_main_uses_stable_gate

make_repo explicit_stable
run_line "refs/heads/topic $base refs/heads/topic $base" TDA_STABLE_RELEASE=1
assert_status 0 explicit_stable_passes
assert_call 'check.sh --stable' explicit_stable_uses_stable_gate

if python3 -I "$ROOT/scripts/test-remote-gate.py"; then
  pass remote_gate_real_git_protocol_suite
else
  fail remote_gate_real_git_protocol_suite "real-Git remote-gate protocol fixtures failed"
fi

if [ "$failed" -ne 0 ]; then
  echo "pre-push fixture suite failed: $failed failure(s), $passed pass(es)" >&2
  exit 1
fi
echo "pre-push fixture suite OK ($passed cases)"
