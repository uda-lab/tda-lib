# shellcheck shell=bash
# Acquire the container-wide Lean build lock on file descriptor 9 for the lifetime of the
# sourcing script (and of every child it starts, since the descriptor is inherited).
#
#   . "$ROOT/scripts/lib/build-lock.sh"
#
# Serialisation is the gate's safety contract in small shared containers: two concurrent
# mathlib builds OOM each other. This file therefore
#   - fails closed when no lock implementation exists (neither flock(1) nor perl);
#   - carries no re-entry marker in the environment — a caller cannot spoof its way past the
#     lock. Re-entrancy (a script that already holds the lock calling another that sources
#     this file) is detected from the inherited descriptor: if fd 9 is open on the lock file,
#     `flock` on that same open file description is a no-op when an ancestor holds it, and
#     acquires or waits otherwise. A descriptor that merely *points* at the lock file without
#     holding the lock buys nothing.
#   - portable hosts verify descriptor identity using Perl stat.
LEAN_BUILD_LOCK=/tmp/lean-build.lock

# Verify inherited descriptor identity on Linux and portable Perl hosts.
lock_inherited=0
if [ -e /dev/fd/9 ]; then
  if [ -d /proc/self/fd ]; then
    [ "$(readlink /proc/self/fd/9 2>/dev/null)" = "$LEAN_BUILD_LOCK" ] && lock_inherited=1
  elif command -v perl >/dev/null 2>&1; then
    if perl -e 'open(my $fh, ">>&=", 9) or exit 1; my @a=stat($fh); my @b=stat($ARGV[0]); exit(!(@a && @b && $a[0]==$b[0] && $a[1]==$b[1]));' "$LEAN_BUILD_LOCK"; then lock_inherited=1; fi
  fi
fi
if [ "$lock_inherited" = 0 ]; then
  exec 9>>"$LEAN_BUILD_LOCK" || { echo "ERROR: cannot open $LEAN_BUILD_LOCK" >&2; exit 1; }
fi

if command -v flock >/dev/null 2>&1; then
  flock 9 || { echo "ERROR: flock on $LEAN_BUILD_LOCK failed" >&2; exit 1; }
elif command -v perl >/dev/null 2>&1; then
  # flock(2) locks belong to the open file description, shared with this shell through
  # fd 9; the lock survives the perl child's exit because this shell still holds the fd.
  perl -e 'use Fcntl qw(:flock); open(my $fh, ">>&=", 9) or die "fd 9: $!\n"; flock($fh, LOCK_EX) or die "flock: $!\n"' \
    || { echo "ERROR: perl flock on $LEAN_BUILD_LOCK failed" >&2; exit 1; }
else
  echo "ERROR: neither flock(1) nor perl is available; the gate cannot serialise Lean builds." >&2
  echo "       Install util-linux (flock) or perl. Refusing to build unserialised." >&2
  exit 1
fi
