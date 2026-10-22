# shellcheck shell=bash
# Exclude writes to canonical checkout/build/dependency paths, including symlink targets.
# Sorted locks avoid deadlock; inherited descriptors support nested gates and wrappers.
# No environment marker alone skips acquisition. Do not wrap these scripts in outer locks.
lean_lock_root=${ROOT:?ROOT must name the repository}
lean_lock_helper="$lean_lock_root/scripts/lib/build-resources.py"
lean_lock_files=$(python3 "$lean_lock_helper" "$lean_lock_root") || exit 1
lean_had_inherited_locks=${LEAN_RESOURCE_LOCK_FDS:-}
lean_inherited_locks=$(python3 "$lean_lock_helper" --inherited) || exit 1
LEAN_RESOURCE_LOCK_FDS=
lean_next_fd=9
for lean_lock_record in $lean_lock_files; do
  lean_lock_mode=${lean_lock_record%%:*}
  lean_lock_path=${lean_lock_record#*:}
  lean_lock_fd=
  for lean_pair in $lean_inherited_locks; do
    lean_candidate=${lean_pair%%:*}
    [[ "$lean_candidate" =~ ^[0-9]+$ ]] || continue
    lean_inherited_rest=${lean_pair#*:}
    lean_inherited_mode=${lean_inherited_rest%%:*}
    [ "${lean_inherited_rest#*:}" = "$lean_lock_path" ] || continue
    if [ "$lean_lock_mode" = X ] && [ "$lean_inherited_mode" = S ]; then
      echo 'ERROR: nested operation needs stronger resource locks; restart the outer gate.' >&2
      exit 1
    fi
    # Never downgrade an outer exclusive lock during a nested shared acquisition.
    lean_lock_mode=$lean_inherited_mode
    lean_lock_fd=$lean_candidate
    break
  done
  if [ -z "$lean_lock_fd" ]; then
    # A nested operation must not expand its lock set while holding a partial set:
    # that could invert global acquisition order. The outer gate covers docbuild too.
    if [ -n "$lean_had_inherited_locks" ]; then
      echo 'ERROR: Lake resource topology changed inside a guarded operation; restart the outer gate.' >&2
      exit 1
    fi
    while [ -e "/dev/fd/$lean_next_fd" ]; do lean_next_fd=$((lean_next_fd + 1)); done
    lean_lock_fd=$lean_next_fd
    lean_next_fd=$((lean_next_fd + 1))
    # Only a locally generated integer enters eval; the path remains a quoted variable.
    eval "exec ${lean_lock_fd}>>\"\$lean_lock_path\"" || exit 1
  fi
  if command -v flock >/dev/null 2>&1; then
    if [ "$lean_lock_mode" = S ]; then
      flock -s "$lean_lock_fd" || exit 1
    else
      flock "$lean_lock_fd" || exit 1
    fi
  else
    perl -e 'use Fcntl qw(:flock); open(my $fh, ">>&=", $ARGV[0]) or die "lock fd: $!"; flock($fh, $ARGV[1] eq "S" ? LOCK_SH : LOCK_EX) or die "flock: $!"' "$lean_lock_fd" "$lean_lock_mode" || exit 1
  fi
  LEAN_RESOURCE_LOCK_FDS="$LEAN_RESOURCE_LOCK_FDS $lean_lock_fd:$lean_lock_mode:$lean_lock_path"
done
export LEAN_RESOURCE_LOCK_FDS
# Refuse to run if symlink/dependency topology changed while waiting for the locks.
[ "$(python3 "$lean_lock_helper" "$lean_lock_root")" = "$lean_lock_files" ] || {
  echo 'ERROR: Lake resource topology changed while waiting; restart the guarded operation.' >&2
  exit 1
}
unset lean_lock_record lean_lock_mode lean_inherited_rest lean_inherited_mode lean_lock_files lean_had_inherited_locks lean_inherited_locks lean_next_fd lean_lock_path lean_lock_fd lean_pair lean_candidate
