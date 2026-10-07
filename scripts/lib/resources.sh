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
