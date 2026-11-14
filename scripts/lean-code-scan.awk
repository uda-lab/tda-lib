# Comment- and string-aware scanner over Lean sources, shared by scripts/check-no-sorry.sh
# (mode=sorry), scripts/check-no-custom-axiom.sh (mode=axiom),
# scripts/check-root-aggregator.sh (mode=root) and the Comparator import boundary
# (mode=import, mode=imports; scripts/check-comparator.sh). Invoke as
#     awk -v mode=sorry -f scripts/lean-code-scan.awk FILE...
# and it prints `file:line:content` for every violating line; no output means clean.
#
# mode=import (needs `-v import_target=<Name>`) prints one `file: forbidden import of
# <Name>` line per file whose import list names a module equal to `<Name>` or dotted under
# it (`<Name>.Sub`), honouring `module`/`public`/`meta`/`all` import modifiers. mode=imports
# instead prints every direct imported module name, one per line, for project-local
# dependency checks (transitive bridge detection). Both may be invoked on multiple files;
# state resets per file, and the accumulated per-file import list is only resolved once the
# whole file has been scanned (at the next file's FNR==1, or at END for the last file), so a
# block comment that falls between `import` and the module name on separate tokens is
# rejoined the same way the rest of this scanner already treats comments: as a token
# separator, not as hidden text. Unlike every other mode, mode=import/mode=imports keep each
# `«…»` escape's literal text in the code stream instead of collapsing it to the opaque `«x»`
# token the other modes use (below), and then unescape it per dotted component
# (`normalizeEscapedModule`) before comparing against a plain module name: `import
# «ComparatorChallenge»` and `import TDA.«Probability».SamplingCoverage` are recognised the
# same as their unescaped spelling, matching Lean's own treatment of `«…»` as mere syntax for
# writing an identifier, not a different name.
#
# Lexing rules (state is reset per file):
#   * block comments `/- … -/` nest and may span lines, and leave a space in the code stream (they
#     separate tokens: `import A/- -/open B` is two commands); line comments `-- …` run to end of line;
#   * string literals `"…"` (with `\"` escapes, spanning lines — Lean allows raw newlines in
#     strings) are opaque: their content is replaced by `""` in the code stream, so a `/-`,
#     `--`, `sorry` or `axiom` inside a string neither opens a comment nor trips a rule;
#   * interpolated strings (`s!"…"`, `m!"…"`, any `<ident>!"…"`) are opaque EXCEPT their
#     `{…}` holes, which are Lean terms and are lexed as code — including nested comments
#     (a `}` inside `/- … -/` does not close the hole), nested strings and nested holes;
#     `\{` is a literal brace;
#   * raw string literals `r"…"`, `r#"…"#`, `r##"…"##` … are opaque: no escapes, closed only
#     by `"` followed by the same number of `#`; recognised where the `r` cannot be part of
#     an identifier;
#   * escaped identifiers `«…»` are opaque (a `--`, `/-`, `"` or `sorry` inside is part of the
#     name) and appear in the code stream as `«x»`; length() and substr() agree on `«` whether
#     the awk counts bytes or characters;
#   * character literals `'x'` / `'\n'` are opaque, recognised only where a `'` cannot be part
#     of an identifier (`h'` stays an identifier).
# A declaration keyword may end its line (`axiom` ⏎ `bad : False`); the axiom rule therefore
# also fires on a code line that ends with the keyword.
# mode=root flags every line whose code is neither blank, the `module` header nor an `import` of
# exactly ONE module name (optionally `public`/`private`/`meta`-prefixed): the root aggregator
# carries imports and comments only. It honours no marker. One name per line means no command can
# follow an import on the same line (`import A open B`, `import A declare_syntax_cat s`) without a
# keyword list. A module name is dotted components; `«…»` escapes and non-ASCII characters are
# accepted, ASCII punctuation other than `_ ' ! ?` is not (matched by an explicit character list,
# never a byte range, so mawk, nawk and gawk in any locale agree).
# The ALLOW_ markers are honoured ONLY in the trailing line comment of the violating line
# (`… := sorry -- ALLOW_SORRY: #12 reason`), never inside a string or a block comment.
BEGIN { q = "\047"; G = "«"; GC = "»"; LG = length(G); LGC = length(GC)
  # Byte mode (LG > 1): seqlen maps UTF-8 lead bytes to sequence lengths; character mode leaves it empty (substr() reads a whole character).
  if (LG > 1) {
    for (b = 192; b < 224; b++) seqlen[sprintf("%c", b)] = 2
    for (b = 224; b < 240; b++) seqlen[sprintf("%c", b)] = 3
    for (b = 240; b < 248; b++) seqlen[sprintf("%c", b)] = 4
  }
  if (mode == "import" && import_target == "") {
    print "lean-code-scan.awk: mode=import requires import_target" > "/dev/stderr"; exit 2
  }
}
FNR == 1 {
  if ((mode == "import" || mode == "imports") && import_file != "") {
    if (mode == "import") {
      if (moduleHasImport(import_code, import_target))
        printf "%s: forbidden import of %s\n", import_file, import_target
    } else {
      emitImports(import_code)
    }
  }
  if (mode == "import" || mode == "imports") { import_file = FILENAME; import_code = "" }
  depth = 0; inStr = 0; rawHashes = -1; interp = 0; hole = 0; holeStr = 0; holeCmt = 0
}
{
  line = $0; code = ""; inLine = 0; trailing = ""
  n = length(line); i = 1
  while (i <= n) {
    c = substr(line, i, 1); two = substr(line, i, 2)
    if (inStr && hole > 0) {                       # inside an interpolation hole: Lean code
      if (holeCmt > 0) {                            # block comment inside the hole
        if (two == "-/") { holeCmt--; i += 2; continue }
        if (two == "/-") { holeCmt++; i += 2; continue }
        i++; continue
      }
      if (inLine) { i++; continue }                # `--` inside a hole: rest of line is comment
      if (holeStr) { if (c == "\\") { i += 2; continue } if (c == "\"") holeStr = 0; i++; continue }
      if (substr(line, i, LG) == G) { i = skipGuillemets(line, i); code = code "«x»"; continue }
      if (two == "/-") { holeCmt = 1; i += 2; continue }
      if (two == "--") { inLine = 1; trailing = substr(line, i); i += 2; continue }
      if (c == "\"") { holeStr = 1; code = code "\"\""; i++; continue }
      if (c == "{") { hole++ } else if (c == "}") { hole--; if (hole == 0) { code = code " "; i++; continue } }
      code = code c; i++; continue
    }
    if (inStr) {
      if (rawHashes >= 0) {                        # raw string: `"` + rawHashes × `#` closes it
        if (c == "\"" && substr(line, i + 1, rawHashes) == hashes(rawHashes)) {
          i += 1 + rawHashes; inStr = 0; rawHashes = -1; code = code "\"\""; continue
        }
        i++; continue
      }
      if (c == "\\") { i += 2; continue }
      if (interp && c == "{") { hole = 1; code = code " "; i++; continue }
      if (c == "\"") { inStr = 0; interp = 0; code = code "\"\"" }
      i++; continue
    }
    if (depth > 0) {
      if (two == "-/") { depth--; i += 2; continue }
      if (two == "/-") { depth++; i += 2; continue }
      i++; continue
    }
    if (inLine) { i++; continue }
    if (substr(line, i, LG) == G) {
      j = skipGuillemets(line, i)
      code = code (((mode == "import" || mode == "imports") ? substr(line, i, j - i) : "«x»"))
      i = j; continue
    }
    if (two == "--") { inLine = 1; trailing = substr(line, i); i += 2; continue }
    if (two == "/-") { depth++; code = code " "; i += 2; continue }   # a comment separates tokens
    if (c == "\"") { inStr = 1; rawHashes = -1; interp = (code ~ /[A-Za-z0-9_]![[:space:]]*$/) ? 1 : 0; i++; continue }
    if (c == "r" && (code == "" || substr(code, length(code), 1) !~ /[A-Za-z0-9_.!?]/)) {
      j = i + 1; h = 0
      while (substr(line, j, 1) == "#") { h++; j++ }
      if (substr(line, j, 1) == "\"") { inStr = 1; rawHashes = h; interp = 0; i = j + 1; continue }
    }
    if (c == q) {
      prev = (code == "") ? "" : substr(code, length(code), 1)
      if (prev == "" || (prev !~ /[A-Za-z0-9_.!?]/ && prev != q)) {
        c1 = substr(line, i + 1, 1)
        if ((c1 in seqlen) && substr(line, i + 1 + seqlen[c1], 1) == q) { code = code "''"; i += 2 + seqlen[c1]; continue }
        if (substr(line, i + 1, 1) == "\\" && substr(line, i + 3, 1) == q) { code = code "''"; i += 4; continue }
        if (substr(line, i + 1, 1) != q && substr(line, i + 2, 1) == q) { code = code "''"; i += 3; continue }
      }
    }
    code = code c; i++
  }
  if ((mode == "sorry" || mode == "stable")) {
    if (code ~ /(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)/ && (mode == "stable" || trailing !~ /ALLOW_SORRY: .*#[0-9]+/))
      printf "%s:%d:%s\n", FILENAME, FNR, line
  } else if ((mode == "axiom" || mode == "stable_axiom")) {
    if (code ~ /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(axiom|constant|opaque|unsafe)([[:space:]]|$)/ && (mode == "stable_axiom" || trailing !~ /ALLOW_AXIOM: .*#[0-9]+/))
      printf "%s:%d:%s\n", FILENAME, FNR, line
  } else if (mode == "root") {
    if (!rootLineOk(code)) printf "%s:%d:%s\n", FILENAME, FNR, line
  } else if (mode == "import" || mode == "imports") {
    import_code = import_code " " code
  } else {
    print "lean-code-scan.awk: unknown mode '" mode "'" > "/dev/stderr"; exit 2
  }
}
END {
  if (mode == "import" && import_file != "" && moduleHasImport(import_code, import_target))
    printf "%s: forbidden import of %s\n", import_file, import_target
  if (mode == "imports" && import_file != "") emitImports(import_code)
}
function hashes(k,   s) { s = ""; while (k-- > 0) s = s "#"; return s }
# Index just past the `»` closing the `«` at position i (end of line if unterminated).
function skipGuillemets(s, i,   k) {
  k = index(substr(s, i + LG), GC)
  return (k == 0) ? length(s) + 1 : i + LG + k - 1 + LGC
}
function rootLineOk(s,   toks, nt, k, t) {
  nt = split(s, toks, /[[:space:]]+/); k = 1
  if (nt > 0 && toks[1] == "") k = 2                 # leading whitespace
  if (nt > 0 && toks[nt] == "") nt--                 # trailing whitespace
  if (k > nt) return 1                               # blank
  if (k == nt && toks[k] == "module") return 1
  while (k <= nt && (toks[k] == "public" || toks[k] == "private" || toks[k] == "meta")) k++
  if (k + 1 != nt || toks[k] != "import") return 0   # `import` and exactly one module name
  t = toks[nt]
  gsub(/«[^»]*»/, "X", t)
  if (t ~ /^[.0-9]/ || t ~ /\.$/ || t ~ /\.\./) return 0
  if (t ~ /[][(){}<>:;,=+*\/\\|&^%$#@~`"-]/) return 0
  return 1
}
# True if `s` (an accumulated code stream) imports `target` or a module dotted under it,
# honouring `module`/`public`/`meta`/`all` import modifiers and a whole-name `«target»` escape.
# A partially escaped dotted name (`TDA.«Probability».SamplingCoverage`) still matches via the
# substr prefix check once normalizeEscapedModule below would unescape it — but this function
# compares raw tokens, so it only recognises `target` escaped as a whole; callers that need the
# general case use emitImports, whose output is already normalized.
function moduleHasImport(s, target,   toks, nt, i, k, module, escaped_target) {
  nt = split(s, toks, /[[:space:]]+/)
  escaped_target = G target GC
  for (i = 1; i <= nt; i++) {
    k = i
    if (toks[k] == "module") k++
    if (toks[k] == "public") k++
    if (toks[k] == "meta") k++
    if (toks[k] != "import") continue
    k++
    if (toks[k] == "all") k++
    if (k > nt) continue
    module = toks[k]
    if (module == target || substr(module, 1, length(target) + 1) == target "." ||
        module == escaped_target || substr(module, 1, length(escaped_target) + 1) == escaped_target ".")
      return 1
  }
  return 0
}
# Prints each direct imported module name in `s` (an accumulated code stream), one per line,
# with every `«…»` escape unescaped (normalizeEscapedModule) so a caller comparing against
# plain dotted module names recognises `import «Foo».Bar` and `import Foo.«Bar»` the same as
# `import Foo.Bar`.
function emitImports(s,   protected, sentinel, i, n, j, escaped, toks, nt, k, module) {
  # A `«…»` escape may itself contain whitespace (a legal Lean identifier character); protect
  # it with a sentinel byte before splitting on whitespace, exactly as Lean's own lexer would
  # still see one token, then restore the spaces once each import's module token is isolated.
  sentinel = sprintf("%c", 1); protected = ""; n = length(s); i = 1
  while (i <= n) {
    if (substr(s, i, LG) == G) {
      j = skipGuillemets(s, i)
      escaped = substr(s, i, j - i); gsub(/[[:space:]]/, sentinel, escaped)
      protected = protected escaped; i = j
    } else {
      protected = protected substr(s, i, 1); i++
    }
  }
  nt = split(protected, toks, /[[:space:]]+/)
  for (i = 1; i <= nt; i++) {
    if (toks[i] != "import") continue
    k = i + 1
    if (toks[k] == "all") k++
    if (k > nt || toks[k] == "") continue
    module = toks[k]
    # A line comment can separate the components of a dotted module name on consecutive
    # non-comment tokens; rejoin spaces around a leading/trailing dot.
    while (k < nt && (module ~ /\.$/ || toks[k + 1] ~ /^\./)) { k++; module = module toks[k] }
    gsub(sentinel, " ", module)
    print normalizeEscapedModule(module)
  }
}
# Strips every `«…»` escape in a dotted module name down to its body (`«Foo».«Bar»` ->
# `Foo.Bar`), matching Lean's own treatment of `«…»` as syntax for writing an identifier that
# may contain characters an unescaped identifier cannot, not a different identifier.
function normalizeEscapedModule(s,   start, after_open, close_rel, close_start, close_next, body) {
  while ((start = index(s, G)) > 0) {
    after_open = start + LG
    close_rel = index(substr(s, after_open), GC)
    if (close_rel == 0) break
    close_start = after_open + close_rel - 1
    body = substr(s, after_open, close_start - after_open)
    close_next = close_start + LGC
    s = substr(s, 1, start - 1) body substr(s, close_next)
  }
  return s
}
