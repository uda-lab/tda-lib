# shellcheck shell=bash
# Defaults shared by the guarded Lake entry points. Explicit values, including false, win.
lake_artifact_cache_init() {
  local lake_cache_root="$1"
  export LAKE_ARTIFACT_CACHE="${LAKE_ARTIFACT_CACHE-true}"
  export LAKE_RESTORE_ARTIFACTS="${LAKE_RESTORE_ARTIFACTS-true}"
  if [ -z "${LAKE_CACHE_DIR+x}" ]; then
    LAKE_CACHE_DIR=$(python3 "$lake_cache_root/scripts/lib/build-resources.py" \
      --artifact-cache-dir "$lake_cache_root") || return
    export LAKE_CACHE_DIR
  fi
}
