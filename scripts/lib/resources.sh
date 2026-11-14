# shellcheck shell=bash
# Read-only probes; unavailable platform metrics remain unknown.
lean_available_kib() {
  local avail max cur file shmem cg cg_path cg_dir
  avail=$(awk '/^MemAvailable:/{print $2}' /proc/meminfo 2>/dev/null) || avail=
  # v2 unified cgroup: inspect the process cgroup and each exposed ancestor.
  # A container namespace may expose its own cgroup as the filesystem root.
  cg_path=$(awk -F: '$1=="0"{print $3}' /proc/self/cgroup 2>/dev/null) || cg_path=
  cg_dir="/sys/fs/cgroup${cg_path:-}"
  [ -d "$cg_dir" ] || cg_dir=/sys/fs/cgroup
  while [ -d "$cg_dir" ]; do
    if [ -r "$cg_dir/memory.max" ] && [ -r "$cg_dir/memory.current" ]; then
      max=$(cat "$cg_dir/memory.max"); cur=$(cat "$cg_dir/memory.current")
      if [[ "$max" =~ ^[0-9]+$ ]] && [[ "$cur" =~ ^[0-9]+$ ]]; then
        file=$(awk '$1=="file"{print $2}' "$cg_dir/memory.stat" 2>/dev/null) || file=
        shmem=$(awk '$1=="shmem"{print $2}' "$cg_dir/memory.stat" 2>/dev/null) || shmem=
        cg=$(( (max - cur + ${file:-0} - ${shmem:-0}) / 1024 ))
        [ "$cg" -lt 0 ] && cg=0
        if [ -z "$avail" ] || [ "$cg" -lt "$avail" ]; then avail=$cg; fi
      fi
    fi
    [ "$cg_dir" = /sys/fs/cgroup ] && break
    cg_dir=${cg_dir%/*}
    case "$cg_dir" in /sys/fs/cgroup|/sys/fs/cgroup/*) ;; *) break ;; esac
  done
  printf '%s\n' "$avail"
}
lean_check_headroom() {
  local min=${LEAN_GUARD_MIN_AVAIL_MIB:-1536} avail
  [[ "$min" =~ ^[0-9]+$ ]] || { echo 'ERROR: LEAN_GUARD_MIN_AVAIL_MIB must be a nonnegative integer' >&2; return 2; }
  avail=$(lean_available_kib)
  if [ -z "$avail" ]; then
    echo 'Lean resource guard: memory headroom unknown on this platform.' >&2
  elif [ "$avail" -lt "$((min * 1024))" ]; then
    echo "ERROR: only $((avail / 1024)) MiB headroom; need $min MiB. Reclaim only your finished jobs." >&2
    return 2
  fi
}
# Detected thread count for an unset/empty LEAN_NUM_THREADS: the CPUs actually available to
# this process (affinity/cpuset, as `nproc` reports it) capped by a cgroup v2 CPU quota when
# one is set, at least 1. Never a hard-coded hardware number. LEAN_NPROC_CMD, LEAN_CGROUP_ROOT
# and LEAN_CGROUP_SELF_PATH exist only so self-tests can stub detection; no ordinary invocation
# needs to set any of them.
lean_detect_num_threads() {
  local nproc_cmd=${LEAN_NPROC_CMD:-nproc} affinity
  local cg_root=${LEAN_CGROUP_ROOT:-/sys/fs/cgroup} cg_path cg_dir
  local quota period step_threads quota_threads detected
  affinity=$("$nproc_cmd" 2>/dev/null) || affinity=
  [[ "$affinity" =~ ^[0-9]+$ ]] && [ "$affinity" -ge 1 ] || affinity=1

  if [ -n "${LEAN_CGROUP_SELF_PATH+set}" ]; then
    cg_path=$LEAN_CGROUP_SELF_PATH
  else
    cg_path=$(awk -F: '$1=="0"{print $3}' /proc/self/cgroup 2>/dev/null) || cg_path=
  fi
  cg_dir="$cg_root${cg_path:-}"
  [ -d "$cg_dir" ] || cg_dir=$cg_root

  # Same ancestor walk as lean_available_kib, for cpu.max instead of memory.max: inspect the
  # process's own cgroup and every exposed ancestor up to the root, taking the MINIMUM
  # quota-derived thread count seen. Stopping at the first readable cpu.max would let a looser
  # or unlimited ("max") child quota hide a stricter ancestor quota.
  quota_threads=
  while [ -d "$cg_dir" ]; do
    if [ -r "$cg_dir/cpu.max" ]; then
      read -r quota period < "$cg_dir/cpu.max" 2>/dev/null || quota=
      if [[ "${quota:-}" =~ ^[0-9]+$ ]] && [[ "${period:-}" =~ ^[0-9]+$ ]] && [ "$period" -gt 0 ]; then
        step_threads=$(( (quota + period - 1) / period ))
        [ "$step_threads" -ge 1 ] || step_threads=1
        if [ -z "$quota_threads" ] || [ "$step_threads" -lt "$quota_threads" ]; then quota_threads=$step_threads; fi
      fi
      # quota="max" (no limit) at this level contributes nothing; an ancestor's quota still can.
    fi
    [ "$cg_dir" = "$cg_root" ] && break
    cg_dir=${cg_dir%/*}
    case "$cg_dir" in "$cg_root"|"$cg_root"/*) ;; *) break ;; esac
  done

  detected=$affinity
  if [ -n "$quota_threads" ] && [ "$quota_threads" -lt "$detected" ]; then detected=$quota_threads; fi
  printf '%s\n' "$detected"
}
# Resolves LEAN_NUM_THREADS and LEAN_NUM_THREADS_SOURCE ("explicit" or "detected") into the
# caller's shell and exports both. An explicit positive value is kept exactly as given; an
# invalid explicit value is rejected (return 64, as before this helper existed). Unset/empty
# detects the available CPU count instead of falling back to a fixed 1.
lean_resolve_num_threads() {
  if [ -n "${LEAN_NUM_THREADS:-}" ]; then
    [[ "$LEAN_NUM_THREADS" =~ ^[1-9][0-9]*$ ]] || { echo 'ERROR: LEAN_NUM_THREADS must be positive' >&2; return 64; }
    LEAN_NUM_THREADS_SOURCE=explicit
  else
    LEAN_NUM_THREADS=$(lean_detect_num_threads)
    LEAN_NUM_THREADS_SOURCE=detected
  fi
  export LEAN_NUM_THREADS LEAN_NUM_THREADS_SOURCE
}
