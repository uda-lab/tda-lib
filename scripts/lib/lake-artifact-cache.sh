# shellcheck shell=bash
# Defaults shared by the guarded Lake entry points. Explicit values, including false, win.
lake_artifact_cache_init() {
  local lake_cache_root="$1"
  export LAKE_ARTIFACT_CACHE="${LAKE_ARTIFACT_CACHE-true}"
  export LAKE_RESTORE_ARTIFACTS="${LAKE_RESTORE_ARTIFACTS-true}"
  if [ -z "${LAKE_CACHE_DIR+x}" ] || [ -n "$LAKE_CACHE_DIR" ]; then
    LAKE_CACHE_DIR=$(python3 "$lake_cache_root/scripts/lib/build-resources.py" \
      --artifact-cache-dir "$lake_cache_root") || return
  fi
  # Normalize an explicit relative path before nested wrappers can change cwd.
  # An explicit empty value remains empty to select Lake's system cache default.
  export LAKE_CACHE_DIR
}
