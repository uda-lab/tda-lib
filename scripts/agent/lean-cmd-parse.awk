# Shell-command parser for lean-guard.sh. Reads one Bash tool command (heredoc bodies
# already removed) on stdin and prints one line per finding:
#     LEAN <held> <segment text>      a Lean invocation; held=1 if it runs under the lock
#     SELFLOCK <outer>                 scripts/check.sh or scripts/hooks/pre-push; outer=1 if
#                                      an enclosing flock wrapper would deadlock it
# Nothing else is printed. Invoke:  awk -v LOCK=/tmp/lean-build.lock -f lean-cmd-parse.awk
#
# Model. The command is cut into *segments* at `;`, `&&`, `||`, `|`, `&` and newlines.
# *Groups* nest: `( … )` subshells, `$( … )` / `<( … )` / backtick substitutions (also
# inside double quotes — they execute), and the argument of `sh -c "…"` (a nested shell).
# Double-quoted text otherwise is data and is dropped; single-quoted text is always data.
# Each segment records the group it lives in; each group records its first and last segment.
#
# A Lean segment is *held* when
#   (a) its own text carries the canonical wrapper `flock [-opts] LOCK …`, or an enclosing
#       `sh -c` group was opened by a segment carrying that wrapper; or
#   (b) fd form: some fd N is bound to LOCK for this segment — by `) N>LOCK` on a group that
#       contains the segment, or by an `exec … N>LOCK` segment earlier in a group that
#       contains the segment — AND a `flock N` segment ran earlier in a group that contains
#       the segment. A redirect on an ordinary command (`true 9>LOCK`) binds nothing beyond
#       that command; a group that has closed releases its fds.
# Self-locking scripts are reported with outer=1 when their segment text puts a `flock`
# before them, or when an enclosing `sh -c` group was opened by a flock wrapper.

function esc(s) { gsub(/[.]/, "\\.", s); return s }
function wrapper_re() { return "(^|[[:space:];&|(])flock([[:space:]]+-[A-Za-z-]+([[:space:]]+[0-9]+)?)*[[:space:]]+" esc(LOCK) "([[:space:]]|$)" }
function strip_prefixes(t,   changed) {
  sub(/^[[:space:]]+/, "", t)
  do {
    changed = 0
    if (match(t, /^([A-Za-z_][A-Za-z0-9_]*=[^[:space:]]*|timeout[[:space:]]+[0-9smh]+|nice([[:space:]]+-n[[:space:]]+-?[0-9]+)?|flock([[:space:]]+-[A-Za-z-]+([[:space:]]+[0-9]+)?)*[[:space:]]+[^[:space:]]+|env|command|exec|eval|(ba|z|da)?sh[[:space:]]+-l?c)[[:space:]]+/)) {
      t = substr(t, RLENGTH + 1); changed = 1
    }
  } while (changed)
  return t
}
function is_lean(t,   w, rest) {
  t = strip_prefixes(t)
  # normalise the executable word: drop surrounding quotes and any directory prefix, so
  # `"lake" build`, `'lake' build` and `$HOME/.elan/bin/lake build` read as `lake build`
  if (match(t, /^[^[:space:]]+/)) {
    w = substr(t, 1, RLENGTH); rest = substr(t, RLENGTH + 1)
    gsub(/^["']|["']$/, "", w); sub(/^.*\//, "", w)
    t = w rest
  }
  return (t ~ /^lake[[:space:]]+build([[:space:]]|$)/ || t ~ /^lake[[:space:]]+exe[[:space:]]+cache([[:space:]]|$)/ \
       || t ~ /^lake[[:space:]]+env[[:space:]]+lean([[:space:]]|$)/ || t ~ /^lean([[:space:]]|$)/)
}
# A self-locking gate script *invoked*: as the command itself, or via `bash`/`sh` with at
# most non-`-n` flags (`bash -n scripts/check.sh` and `shellcheck scripts/check.sh` are
# not runs). Its text is matched after the usual prefix stripping.
function is_selflock(t) {
  t = strip_prefixes(t)
  return (t ~ /^((ba|z|da)?sh([[:space:]]+-[a-mo-z]+)*[[:space:]]+)?(\.\/)?scripts\/(check\.sh|bootstrap\.sh|lean\.sh|check-axioms\.sh|check-axiom-coverage\.sh|hooks\/pre-push)([[:space:]]|$)/)
}
# fd-form lock analysis for segment s in group g: some fd bound to LOCK for s (group
# redirect on a group containing s, or an earlier `exec … N>LOCK` in a group containing s)
# AND an earlier `flock N` in a group containing s.
function fd_held(s, g,   fd, h, bound) {
  for (fd in fl_seg) {
    if (fl_seg[fd] >= s) continue
    if (!in_group(fl_group[fd], s)) continue
    bound = 0
    for (h = 1; h <= ngroup; h++) if ((h in g_fd) && g_fd[h] == fd && in_group(h, s)) bound = 1
    if ((fd in ex_seg) && ex_seg[fd] < s && in_group(ex_group[fd], s)) bound = 1
    if (bound) return 1
  }
  return 0
}
function strip_env(t) { sub(/^[[:space:]]+/, "", t); while (match(t, /^([A-Za-z_][A-Za-z0-9_]*=[^[:space:]]*|env)[[:space:]]+/)) t = substr(t, RLENGTH + 1); return t }
function flock_fd(t,   s) {
  t = strip_env(t); sub(/^exec[[:space:]]+/, "", t)
  if (match(t, /^flock([[:space:]]+-[A-Za-z-]+([[:space:]]+[0-9]+)?)*[[:space:]]+[0-9]+([[:space:]]|$)/)) {
    s = substr(t, 1, RLENGTH); sub(/[[:space:]]*$/, "", s); sub(/^.*[[:space:]]/, "", s); return s
  }
  return ""
}
function exec_fd(t,   s, re) {
  t = strip_env(t)
  if (t !~ /^exec([[:space:]]|$)/) return ""
  re = "[0-9]+>[[:space:]]*" esc(LOCK) "([[:space:]]|$)"
  if (match(t, re)) { s = substr(t, RSTART, RLENGTH); sub(/>.*/, "", s); return s }
  return ""
}
function in_group(g, s) { return (g_open[g] <= s && s <= g_close[g]) }

function new_seg() { nseg++; seg_group[nseg] = cur_group; seg_text[nseg] = ""; cur_seg = nseg }
function open_group(kind, wrapped) {
  ngroup++; g_kind[ngroup] = kind; g_parent[ngroup] = cur_group; g_wrap[ngroup] = wrapped
  g_outer_seg[ngroup] = cur_seg; gstack[++gsp] = ngroup; dq_return[gsp] = 0
  g_open[ngroup] = nseg + 1; g_close[ngroup] = 1e9
  cur_group = ngroup; new_seg()
}
function close_group(   g) {
  g = gstack[gsp--]; g_close[g] = nseg    # every segment created while open lies inside
  cur_group = g_parent[g]; cur_seg = g_outer_seg[g]
  return g
}

BEGIN {
  RS = "\001"
  nseg = 0; ngroup = 0; gsp = 0; cur_group = 0; g_open[0] = 1; g_close[0] = 1e9; g_wrap[0] = 0; g_parent[0] = 0
  new_seg()
}
{
  text = $0; n = length(text); i = 1
  mode = "cmd"   # cmd | dq (double-quoted data) | sq (single-quoted data)
  while (i <= n) {
    c = substr(text, i, 1); two = substr(text, i, 2)
    if (mode == "sq") { if (c == "'") mode = "cmd"; i++; continue }
    if (mode == "dq") {
      if (c == "\\") { i += 2; continue }
      if (c == "\"") { mode = "cmd"; seg_text[cur_seg] = seg_text[cur_seg] "\"\""; i++; continue }
      if (two == "$(") { open_group("subst", 0); dq_return[gsp] = 1; mode = "cmd"; i += 2; continue }
      if (c == "`")   { open_group("btick", 0); dq_return[gsp] = 1; mode = "cmd"; i++; continue }
      i++; continue
    }
    # mode == cmd
    if (c == "\\") { seg_text[cur_seg] = seg_text[cur_seg] substr(text, i, 2); i += 2; continue }
    if (c == "'" || c == "\"") {
      if (gsp > 0 && g_kind[gstack[gsp]] == "cstr" && g_q[gstack[gsp]] == c) {
        close_group(); seg_text[cur_seg] = seg_text[cur_seg] c c; i++; continue
      }
      # `sh -c "…"` and `eval "…"` execute their argument as shell code: nested shell group
      if (seg_text[cur_seg] ~ /(^|[[:space:]])((ba|z|da)?sh[[:space:]]+-l?c|eval)[[:space:]]+$/) {
        w = (seg_text[cur_seg] ~ wrapper_re()) ? 1 : 0
        open_group("cstr", w); g_q[ngroup] = c; i++; continue
      }
      # a quoted word in command position IS the command (`"lake" build`): keep it verbatim
      if (strip_prefixes(seg_text[cur_seg]) ~ /^[[:space:]]*$/) {
        j = i + 1
        while (j <= n && substr(text, j, 1) != c) { if (c == "\"" && substr(text, j, 1) == "\\") j++; j++ }
        seg_text[cur_seg] = seg_text[cur_seg] substr(text, i, j - i + 1); i = j + 1; continue
      }
      mode = (c == "'") ? "sq" : "dq"; i++; continue
    }
    if (two == "$(" || two == "<(" || two == ">(") { open_group("subst", 0); i += 2; continue }
    if (c == "`") {
      if (gsp > 0 && g_kind[gstack[gsp]] == "btick") {
        close_group(); if (dq_return[gsp + 1]) { dq_return[gsp + 1] = 0; mode = "dq" }
        seg_text[cur_seg] = seg_text[cur_seg] "()"; i++; continue
      }
      open_group("btick", 0); i++; continue
    }
    if (c == "(") { open_group("sub", 0); i++; continue }
    if (c == ")" && gsp > 0 && (g_kind[gstack[gsp]] == "sub" || g_kind[gstack[gsp]] == "subst")) {
      g = close_group()
      seg_text[cur_seg] = seg_text[cur_seg] "()"
      i++
      re = "^[[:space:]]*[0-9]+>" esc(LOCK) "([[:space:]]|$)"
      if (match(substr(text, i), re)) {
        r = substr(text, i, RLENGTH); sub(/>.*/, "", r); sub(/^[[:space:]]*/, "", r)
        g_fd[g] = r; i += RLENGTH
      }
      if (dq_return[gsp + 1]) { dq_return[gsp + 1] = 0; mode = "dq" }
      continue
    }
    if (two == "&&" || two == "||") { new_seg(); i += 2; continue }
    if (c == ";" || c == "|" || c == "&" || c == "\n") { new_seg(); i++; continue }
    seg_text[cur_seg] = seg_text[cur_seg] c; i++
  }
  while (gsp > 0) close_group()
  for (g = 1; g <= ngroup; g++) if (g_close[g] == 1e9) g_close[g] = nseg

  for (s = 1; s <= nseg; s++) {
    t = seg_text[s]; sub(/^[[:space:]]+/, "", t); sub(/[[:space:]]+$/, "", t)
    if (t == "") continue
    g = seg_group[s]
    fd = flock_fd(t); if (fd != "") { fl_seg[fd] = s; fl_group[fd] = g }
    xfd = exec_fd(t); if (xfd != "") { ex_seg[xfd] = s; ex_group[xfd] = g }
    if (is_selflock(t)) {
      # any lock already held around the script — inline wrapper, wrapper on an enclosing
      # `sh -c`, or the fd form — deadlocks it, since the script takes the same lock itself
      outer = (t ~ "(^|[[:space:];&|(])flock[[:space:]][^;&|]*(scripts/(check|bootstrap|lean|check-axioms|check-axiom-coverage)\\.sh|scripts/hooks/pre-push)") ? 1 : 0
      for (h = g; h > 0; h = g_parent[h]) if (g_wrap[h]) outer = 1
      if (!outer && fd_held(s, g)) outer = 1
      print "SELFLOCK " outer
      continue
    }
    if (!is_lean(t)) continue
    held = 0
    if (t ~ wrapper_re()) held = 1
    for (h = g; h > 0 && !held; h = g_parent[h]) if (g_wrap[h]) held = 1
    if (!held && fd_held(s, g)) held = 1
    print "LEAN " held " " t
  }
}
