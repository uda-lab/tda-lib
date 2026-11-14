#!/usr/bin/env bash
# Stub regression tests for the Comparator wrapper's fail-closed behavior and exit handling.
# These tests do not exercise Comparator's Lean statement/axiom semantics (see
# scripts/test-comparator-semantics.sh for that, against the real sandboxed `lake comparator`).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

repo="$tmp/repo"
mkdir -p "$repo/scripts/lib" "$repo/scripts/print_axioms" "$tmp/home/.elan/bin"
cp scripts/check-comparator.sh scripts/lean.sh "$repo/scripts/"
cp scripts/lib/build-lock.sh scripts/lib/build-resources.py scripts/lib/resources.sh "$repo/scripts/lib/"
cp scripts/lean-code-scan.awk "$repo/scripts/"
cp scripts/print_axioms/*.lean "$repo/scripts/print_axioms/"
cp comparator.json lake-manifest.json lakefile.toml lean-toolchain "$repo/"
cp TDA.lean "$repo/"
cp -R TDA "$repo/"
cp ComparatorChallenge.lean "$repo/"
cp -R ComparatorChallenge "$repo/"

make_bin() {
  local dir="$1" have_lake="$2" have_bwrap="$3" tool source
  mkdir -p "$dir"
  for tool in jq awk find xargs sed dirname readlink flock python3 mktemp cat rm grep perl bash; do
    source="$(command -v "$tool" 2>/dev/null || true)"
    [ -n "$source" ] || { echo "ERROR: test prerequisite '$tool' is unavailable." >&2; exit 1; }
    ln -s "$source" "$dir/$tool"
  done
  if [ "$have_bwrap" = yes ]; then
    printf '#!/bin/bash\nexit 0\n' > "$dir/bwrap"
    chmod +x "$dir/bwrap"
  fi
  if [ "$have_lake" = yes ]; then
    cat > "$dir/lake" <<'EOF'
#!/bin/bash
printf '%s\n' "$@" > "${COMPARATOR_TEST_LOG:?}"
printf '%s\n' "${COMPARATOR_TEST_MESSAGE:-stub Comparator result}" >&2
exit "${COMPARATOR_TEST_STATUS:-0}"
EOF
    chmod +x "$dir/lake"
  fi
}

all_bin="$tmp/bin-all"
no_bwrap_bin="$tmp/bin-no-bwrap"
no_lake_bin="$tmp/bin-no-lake"
no_jq_bin="$tmp/bin-no-jq"
no_awk_bin="$tmp/bin-no-awk"
no_find_bin="$tmp/bin-no-find"
no_xargs_bin="$tmp/bin-no-xargs"
no_python_bin="$tmp/bin-no-python"
make_bin "$all_bin" yes yes
make_bin "$no_bwrap_bin" yes no
make_bin "$no_lake_bin" no yes
make_bin "$no_jq_bin" yes yes
make_bin "$no_awk_bin" yes yes
make_bin "$no_find_bin" yes yes
make_bin "$no_xargs_bin" yes yes
make_bin "$no_python_bin" yes yes
rm "$no_jq_bin/jq"
rm "$no_awk_bin/awk"
rm "$no_find_bin/find"
rm "$no_xargs_bin/xargs"
rm "$no_python_bin/python3"

failures=0
cases=0
run_case() {
  local name="$1" want_status="$2" want_text="$3" want_call="$4" path="$5"
  local lake_status="${6:-0}" lake_message="${7:-stub Comparator result}" override="${8:-}"
  local argument="${9:-}"
  local output status
  local log="$tmp/lake-args"
  local args=()
  [ -n "$argument" ] && args=("$argument")
  rm -f "$log"
  if [ -n "$override" ]; then
    set +e
    output="$(env HOME="$tmp/home" PATH="$path" \
      COMPARATOR_TEST_LOG="$log" COMPARATOR_TEST_STATUS="$lake_status" \
      COMPARATOR_TEST_MESSAGE="$lake_message" COMPARATOR_BWRAP="$override" \
      /bin/bash "$repo/scripts/check-comparator.sh" "${args[@]}" 2>&1)"
    status=$?
    set -e
  else
    set +e
    output="$(env -u COMPARATOR_BWRAP HOME="$tmp/home" PATH="$path" \
      COMPARATOR_TEST_LOG="$log" COMPARATOR_TEST_STATUS="$lake_status" \
      COMPARATOR_TEST_MESSAGE="$lake_message" \
      /bin/bash "$repo/scripts/check-comparator.sh" "${args[@]}" 2>&1)"
    status=$?
    set -e
  fi
  cases=$((cases + 1))
  if [ "$status" -ne "$want_status" ] || [[ "$output" != *"$want_text"* ]]; then
    printf 'FAIL [%s]: expected exit %s and text %q; got exit %s: %s\n' \
      "$name" "$want_status" "$want_text" "$status" "$output" >&2
    failures=$((failures + 1))
  fi
  if [ "$want_call" = yes ]; then
    if [ ! -s "$log" ] || ! grep -Fxq 'comparator' "$log" \
      || ! grep -Fxq -- '--config' "$log" \
      || ! grep -Fxq "$repo/comparator.json" "$log" \
      || grep -Fq -- '--inadvisably-no-sandbox' "$log"; then
      printf 'FAIL [%s]: expected only the sandboxed lake comparator --config invocation; args: ' "$name" >&2
      cat "$log" >&2 2>/dev/null || true
      failures=$((failures + 1))
    fi
  elif [ -e "$log" ]; then
    printf 'FAIL [%s]: lake was invoked before the prerequisite/config check failed.\n' "$name" >&2
    failures=$((failures + 1))
  fi
}

run_case accepted 0 'stub Comparator result' yes "$all_bin" 0
run_case rejected 1 'stub Comparator rejection' yes "$all_bin" 1 'stub Comparator rejection'
run_case cannot_start 2 'stub Comparator cannot start' yes "$all_bin" 2 'stub Comparator cannot start'
run_case unexpected_status 2 'unexpected exit status 23' yes "$all_bin" 23 'stub unexpected status'
run_case missing_bwrap 2 'bubblewrap (bwrap) is unavailable' no "$no_bwrap_bin"
run_case missing_lake 2 'lake is unavailable' no "$no_lake_bin"
run_case missing_jq 2 'jq is required' no "$no_jq_bin"
run_case missing_awk 2 'awk is required' no "$no_awk_bin"
run_case missing_find 2 'find is required' no "$no_find_bin"
run_case missing_xargs 2 'xargs is required' no "$no_xargs_bin"
run_case missing_python 2 'python3 (with the standard tomllib module) is required' no "$no_python_bin"
cp "$all_bin/bwrap" "$tmp/bwrap.success"
cat > "$all_bin/bwrap" <<'EOF'
#!/bin/bash
echo 'user namespace is unavailable' >&2
exit 1
EOF
chmod +x "$all_bin/bwrap"
run_case unsupported_bwrap_namespace 2 'bubblewrap sandbox startup probe failed' no "$all_bin"
cp "$tmp/bwrap.success" "$all_bin/bwrap"
run_case wrong_bwrap_override 2 'refusing a sandbox override' no "$all_bin" 0 'must not run' "$tmp/other-bwrap"
run_case sandbox_bypass_argument_rejected 2 'refusing sandbox bypass' no "$all_bin" 0 'must not run' '' '--inadvisably-no-sandbox'
run_case stale_export_argument_rejected 2 'externally supplied exports' no "$all_bin" 0 'must not run' '' '--solution-from-export'
run_case challenge_export_argument_rejected 2 'externally supplied exports' no "$all_bin" 0 'must not run' '' '--challenge-from-export'

cp "$repo/TDA.lean" "$tmp/TDA.lean.saved"
printf '\nimport ComparatorChallenge.Reference\n' >> "$repo/TDA.lean"
run_case production_root_import_rejected 2 'must not import ComparatorChallenge' no "$all_bin"
cp "$tmp/TDA.lean.saved" "$repo/TDA.lean"
printf '\npublic import ComparatorChallenge.Reference\n' >> "$repo/TDA.lean"
run_case production_root_public_import_rejected 2 'must not import ComparatorChallenge' no "$all_bin"
cp "$tmp/TDA.lean.saved" "$repo/TDA.lean"
printf '\nmodule\npublic import ComparatorChallenge.Reference\n' >> "$repo/TDA.lean"
run_case production_module_header_public_import_rejected 2 'must not import ComparatorChallenge' no "$all_bin"
cp "$tmp/TDA.lean.saved" "$repo/TDA.lean"
printf '\npublic meta import all ComparatorChallenge.Reference\n' >> "$repo/TDA.lean"
run_case production_root_full_import_modifiers_rejected 2 'must not import ComparatorChallenge' no "$all_bin"
cp "$tmp/TDA.lean.saved" "$repo/TDA.lean"
cp "$repo/TDA/Probability/SamplingCoverage.lean" "$tmp/SamplingCoverage.lean.saved"
printf '\nimport ComparatorChallenge.Reference\n' >> "$repo/TDA/Probability/SamplingCoverage.lean"
run_case production_module_import_rejected 2 'must not import ComparatorChallenge' no "$all_bin"
cp "$tmp/SamplingCoverage.lean.saved" "$repo/TDA/Probability/SamplingCoverage.lean"
printf '\npublic import ComparatorChallenge.Reference\n' >> "$repo/TDA/Probability/SamplingCoverage.lean"
run_case production_module_public_import_rejected 2 'must not import ComparatorChallenge' no "$all_bin"
cp "$tmp/SamplingCoverage.lean.saved" "$repo/TDA/Probability/SamplingCoverage.lean"
printf '\nimport all ComparatorChallenge.Reference\n' >> "$repo/TDA/Probability/SamplingCoverage.lean"
run_case production_module_import_all_rejected 2 'must not import ComparatorChallenge' no "$all_bin"
cp "$tmp/SamplingCoverage.lean.saved" "$repo/TDA/Probability/SamplingCoverage.lean"

cp "$repo/ComparatorChallenge/Reference.lean" "$tmp/Reference.lean.saved"
printf '\nimport TDA.Probability.SamplingCoverage\n' >> "$repo/ComparatorChallenge/Reference.lean"
run_case challenge_reference_production_import_rejected 2 'ComparatorChallenge modules must not import TDA' no "$all_bin"
cp "$tmp/Reference.lean.saved" "$repo/ComparatorChallenge/Reference.lean"
printf '\npublic meta import all TDA.Probability.SamplingCoverage\n' >> "$repo/ComparatorChallenge/Reference.lean"
run_case challenge_reference_full_production_import_rejected 2 'ComparatorChallenge modules must not import TDA' no "$all_bin"
cp "$tmp/Reference.lean.saved" "$repo/ComparatorChallenge/Reference.lean"
cp "$repo/ComparatorChallenge.lean" "$tmp/ComparatorChallenge.lean.saved"
printf '\nimport TDA\n' >> "$repo/ComparatorChallenge.lean"
run_case challenge_root_production_import_rejected 2 'ComparatorChallenge modules must not import TDA' no "$all_bin"
cp "$tmp/ComparatorChallenge.lean.saved" "$repo/ComparatorChallenge.lean"

printf 'public meta import all ComparatorChallenge.Reference\n' > "$repo/Auxiliary.lean"
run_case auxiliary_module_challenge_import_rejected 2 'project production and auxiliary modules must not import ComparatorChallenge' no "$all_bin"
rm "$repo/Auxiliary.lean"

cp "$repo/ComparatorChallenge/Reference.lean" "$tmp/Reference.lean.saved"
printf 'import TDA.Probability.SamplingCoverage\n' > "$repo/ComparatorBridge.lean"
printf '\nimport ComparatorBridge\n' >> "$repo/ComparatorChallenge/Reference.lean"
run_case transitive_local_bridge_rejected 2 'must not import project-local modules outside ComparatorChallenge' no "$all_bin"
cp "$tmp/Reference.lean.saved" "$repo/ComparatorChallenge/Reference.lean"
printf '\nimport «ComparatorBridge»\n' >> "$repo/ComparatorChallenge/Reference.lean"
run_case transitive_escaped_local_bridge_rejected 2 'must not import project-local modules outside ComparatorChallenge' no "$all_bin"
cp "$tmp/Reference.lean.saved" "$repo/ComparatorChallenge/Reference.lean"
rm "$repo/ComparatorBridge.lean"

cp lakefile.toml "$repo/lakefile.toml"
sed -i '1i srcDir = "/tmp"' "$repo/lakefile.toml"
run_case external_source_dir_rejected 2 'configures a srcDir' no "$all_bin"
cp lakefile.toml "$repo/lakefile.toml"
sed -i '1i srcDir = "src"' "$repo/lakefile.toml"
mkdir -p "$repo/src"
printf 'import TDA.Probability.SamplingCoverage\n' > "$repo/src/ComparatorBridge.lean"
run_case configured_srcdir_rejected 2 'configures a srcDir' no "$all_bin"
cp lakefile.toml "$repo/lakefile.toml"
rm -rf "$repo/src"
cat >> "$repo/lakefile.toml" <<'EOF'

[[lean_lib]]
name = "ComparatorBridge"
srcDir = "bridge"
EOF
run_case target_source_dir_rejected 2 'configures a srcDir' no "$all_bin"
cp lakefile.toml "$repo/lakefile.toml"

printf 'public meta import all ComparatorChallenge.Reference\n' > "$tmp/symlink-source.lean"
ln -s "$tmp/symlink-source.lean" "$repo/TDA/Linked.lean"
run_case production_module_symlink_rejected 2 'hidden behind symlinks' no "$all_bin"
rm "$repo/TDA/Linked.lean"
mv "$repo/TDA.lean" "$tmp/TDA.lean.saved"
ln -s "$tmp/symlink-source.lean" "$repo/TDA.lean"
run_case production_root_symlink_rejected 2 'roots must not be symlinks' no "$all_bin"
rm "$repo/TDA.lean"
mv "$tmp/TDA.lean.saved" "$repo/TDA.lean"
mv "$repo/ComparatorChallenge.lean" "$tmp/ComparatorChallenge.lean.saved"
ln -s "$tmp/ComparatorChallenge.lean.saved" "$repo/ComparatorChallenge.lean"
run_case challenge_root_symlink_rejected 2 'roots must not be symlinks' no "$all_bin"
rm "$repo/ComparatorChallenge.lean"
mv "$tmp/ComparatorChallenge.lean.saved" "$repo/ComparatorChallenge.lean"

cp "$repo/comparator.json" "$tmp/comparator.json.saved"
: > "$repo/comparator.json"
run_case empty_config 2 'comparator.json is missing or empty' no "$all_bin"
printf '{\n' > "$repo/comparator.json"
run_case malformed_config 2 'differs from the reviewed bounded-pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"

mv "$repo/lake-manifest.json" "$tmp/lake-manifest.json.saved"
run_case missing_manifest 2 'lake-manifest.json is missing or empty' no "$all_bin"
mv "$tmp/lake-manifest.json.saved" "$repo/lake-manifest.json"
mv "$repo/lean-toolchain" "$tmp/lean-toolchain.saved"
run_case missing_toolchain_pin 2 'lean-toolchain is missing or empty' no "$all_bin"
mv "$tmp/lean-toolchain.saved" "$repo/lean-toolchain"
mv "$repo/scripts/lean.sh" "$tmp/lean.sh.saved"
run_case missing_lean_sh 2 'scripts/lean.sh is missing or not executable' no "$all_bin"
mv "$tmp/lean.sh.saved" "$repo/scripts/lean.sh"
mv "$repo/scripts/print_axioms" "$tmp/print_axioms.saved"
run_case missing_print_axioms_dir 2 'scripts/print_axioms/ is missing or unreadable' no "$all_bin"
mv "$tmp/print_axioms.saved" "$repo/scripts/print_axioms"

jq '.definition_names = ["TDA.Probability.someDefinition"]' "$repo/comparator.json" > "$tmp/config.json"
mv "$tmp/config.json" "$repo/comparator.json"
run_case definition_hole_rejected 2 'differs from the reviewed bounded-pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"
jq '.permitted_axioms += ["Fake.CustomAxiom"]' "$repo/comparator.json" > "$tmp/config.json"
mv "$tmp/config.json" "$repo/comparator.json"
run_case axiom_allowlist_expansion_rejected 2 'differs from the reviewed bounded-pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"

# A grown pinned inventory (another area file, or another pin in an existing one) is accepted
# as long as the frozen config's theorem_names stays a (not necessarily proper) subset of the
# union of scripts/print_axioms/*.lean: this pilot freezes a reference for its own one target
# theorem, not for every public lemma the repository has ever pinned.
printf '\n#print axioms TDA.Probability.unlisted\n' >> "$repo/scripts/print_axioms/Probability.lean"
run_case pinned_subset_accepted 0 'stub Comparator result' yes "$all_bin"
cp scripts/print_axioms/Probability.lean "$repo/scripts/print_axioms/Probability.lean"

jq '.theorem_names += ["TDA.Probability.not_pinned"]' "$repo/comparator.json" > "$tmp/config.json"
mv "$tmp/config.json" "$repo/comparator.json"
run_case theorem_name_not_pinned_rejected 2 'differs from the reviewed bounded-pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"

jq '.theorem_names += .theorem_names' "$repo/comparator.json" > "$tmp/config.json"
mv "$tmp/config.json" "$repo/comparator.json"
run_case duplicate_theorem_name_rejected 2 'differs from the reviewed bounded-pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"

jq '.theorem_names = []' "$repo/comparator.json" > "$tmp/config.json"
mv "$tmp/config.json" "$repo/comparator.json"
run_case empty_theorem_names_rejected 2 'differs from the reviewed bounded-pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"

if [ "$failures" -eq 0 ]; then
  printf 'Comparator wrapper stub self-test OK (%s cases; semantic Comparator checks not run).\n' "$cases"
else
  exit 1
fi
