#!/usr/bin/env bash
# Optional Claude-only adapter: replicate untracked, machine-local settings into a checkout.
# Shared wrappers and native Codex hooks do not require this installer.
# Typically a
# driver worktree), so a session opened there inherits the same guard tunables. The tracked
# parts (.claude/settings.json, .claude/hooks/*.sh, .claude/skills/) come with the checkout.
set -euo pipefail
SRC="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"          # .../<checkout>/.claude
DEST_ROOT="${1:?usage: install.sh <target-checkout>}"
DEST="$DEST_ROOT/.claude"

mkdir -p "$DEST"
[ -f "$SRC/settings.local.json" ] && cp "$SRC/settings.local.json" "$DEST/settings.local.json"
[ -f "$SRC/ENVIRONMENT.md" ] && ln -sfn "$SRC/ENVIRONMENT.md" "$DEST/ENVIRONMENT.md"

# Keep core dumps and local notes out of the worktree's git view without touching .gitignore.
excl="$DEST_ROOT/.git/info/exclude"
[ -f "$DEST_ROOT/.git" ] && excl="$(git -C "$DEST_ROOT" rev-parse --git-dir)/info/exclude"
mkdir -p "$(dirname "$excl")"
grep -qx 'core' "$excl" 2>/dev/null || printf '\ncore\ncore.*\n' >> "$excl"

echo "installed machine-local harness settings into $DEST"
