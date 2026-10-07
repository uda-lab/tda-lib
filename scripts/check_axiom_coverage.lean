/-
Live coverage guard for the axiom-pinning contract in `scripts/print_axioms.lean`.
Walks the fully elaborated environment produced by `lake build` and fails unless every
public `theorem` declared inside a `TDA…` module has a `#print axioms` line in
`scripts/print_axioms.lean` (the input consumed at run time by `scripts/check-axioms.sh`,
the live trust-footprint audit).

Run via `lake env lean scripts/check_axiom_coverage.lean` from the repository root
(`scripts/check-axiom-coverage.sh` wraps this; `scripts/check.sh` runs it immediately
after the live axiom audit, under the same `/tmp/lean-build.lock` as the rest of the
gate — this walk costs roughly the same memory as that audit run).

No Lean statement in `TDA/` is read or altered here; only `ConstantInfo`
metadata already produced by `lake build` is inspected.

"Public theorem" excludes exactly the following kinds — each a legitimate, non-claimed
`.thmInfo` declaration that Lean/Mathlib elaboration produces, not a mathematical result
a PR is claiming:

  * anything Lean's own kernel/elaborator considers automatically generated or private —
    `Lean.isAutoDeclOrPrivate_Internal`, the canonical Lean-core provenance check. It
    consults the `Environment`'s reserved-name registry rather than matching name
    suffixes, so it covers `.injEq`, `.mk.inj`, `.mk.sizeOf_spec`, `.noConfusion`,
    `recOn`/`casesOn`/`brecOn` auxiliaries, `.congr_simp`, `match_`/`proof_`/`eq_`
    equation-compiler auxiliaries and `private` declarations without ever catching a
    hand-written theorem that happens to be named `.ext` or nested under a namespace
    component called `mk`. Name-suffix heuristics were tried on the source project and
    hid hand-proved `@[ext]` lemmas; do not reintroduce them.
  * `structure`/`class` field projections — a `Prop`-valued field elaborates as a
    `theorem`-kind projection function; these are mechanical accessors, not claimed
    results, and Lean does not classify them as auto-generated — `Environment.isProjectionFn`.

That is the whole list. `instance` declarations are deliberately NOT excluded: a
hand-proved `instance : SomePropClass … := proof` in a project module is a claimed result
and must be pinned; typeclass resolution at call sites never creates a new named
declaration in this project's own modules, so there is no auto-derived category to skip.
Iterate this list, not the caller, if a false positive or negative shows up.

A prerequisite the whole walk depends on: `import TDA` must load every
`TDA/**/*.lean` file, directly or transitively, or that file's declarations never
reach `(← getEnv).constants` and every check passes vacuously for its content. So this file
also discovers every `.lean` file on disk under `TDA/` and fails if any of them is
not among `env.header.moduleNames` — the set this run's `import TDA` actually
loaded, not a static read of the root aggregator's import list (so a file reachable only
from a forgotten nested aggregator is caught too).

`scripts/rename-project.sh` rewrites every `TDA` occurrence in this file.
-/
import TDA

open Lean System

/-- `n` was declared in a module named `TDA`, or a submodule of it
(`TDA.Foo.Bar`, the root aggregator `TDA`, etc). -/
private def isProjectModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some modName => (`TDA).isPrefixOf modName
    | none => false
  | none => false

/-- `n`/`info` is a public theorem this repository must pin in
`scripts/print_axioms.lean`. -/
private def isPublicProjectTheorem (env : Environment) (n : Name) (info : ConstantInfo) :
    CoreM Bool := do
  match info with
  | .thmInfo _ =>
    if (← isAutoDeclOrPrivate_Internal n) then return false
    if env.isProjectionFn n then return false
    if !isProjectModule env n then return false
    return true
  | _ => return false

/-- Every `.lean` file under `dir`, recursively. -/
private partial def collectLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  for entry in (← dir.readDir) do
    let p := entry.path
    if (← p.isDir) then
      result := result ++ (← collectLeanFiles p)
    else if p.extension == some "lean" then
      result := result.push p
  return result

/-- `TDA/Foo/Bar.lean` -> `"TDA.Foo.Bar"`, the same string
`Name.toString` produces for the module Lean loads from that file. -/
private def moduleStringOfPath (path : System.FilePath) : String :=
  match path.components.reverse with
  | [] => ""
  | last :: rest => String.intercalate "." (rest.reverse ++ [(last.dropSuffix ".lean").toString])

/-- Every `.lean` file under `TDA/` whose module is not among `loadedModules` — i.e. a
file `import TDA` never reached, directly or transitively, so its declarations are
invisible to every check above. -/
private def findUnloadedFiles (loadedModules : Std.HashSet String) :
    IO (Array System.FilePath) := do
  let files ← collectLeanFiles "TDA"
  return files.filter fun f => !loadedModules.contains (moduleStringOfPath f)

/-- The declaration names pinned by `#print axioms <name>` lines in `path`, under the exact
same extraction rule `scripts/check-axioms.sh` uses (`awk '/^#print axioms /{print $3}'`):
the line must start with the literal, unindented text `#print axioms ` — not merely contain it
after trimming. A line inside a block comment, or indented, is never a real `#print axioms`
command as far as Lean or that audit are concerned, so this walk must not treat it as pinned
either; doing so would let the coverage guard pass while the live audit never actually checks
the name. -/
private def readPinnedNames (path : System.FilePath) : IO (Std.HashSet String) := do
  let contents ← IO.FS.readFile path
  let prefix' := "#print axioms "
  let names := (contents.splitOn "\n").filterMap fun line =>
    if line.startsWith prefix' then
      match (line.drop prefix'.length).toString.splitOn " " |>.filter (· ≠ "") with
      | name :: _ => some name
      | [] => none
    else
      none
  return Std.HashSet.ofList names

#eval show CoreM Unit from do
  let env ← getEnv
  let loadedModules : Std.HashSet String := Std.HashSet.ofList (env.header.moduleNames.toList.map (·.toString))
  let unloaded ← findUnloadedFiles loadedModules
  let pinned ← readPinnedNames "scripts/print_axioms.lean"
  let mut total : Nat := 0
  let mut missing : Array String := #[]
  for (n, info) in env.constants.toList do
    if (← isPublicProjectTheorem env n info) then
      total := total + 1
      let name := n.toString
      unless pinned.contains name do
        missing := missing.push name
  for f in unloaded do
    IO.println s!"UNLOADED: {f} (module {moduleStringOfPath f} is not reachable from 'import TDA' — its declarations were never checked)"
  for name in missing.qsort (· < ·) do
    IO.println s!"MISSING: {name}"
  if unloaded.isEmpty && missing.isEmpty then
    IO.println s!"COVERAGE OK — {total} public theorems, all pinned"
  else
    -- `throwError`, not `IO.Process.exit`: the latter terminates the process immediately and
    -- discards the `MISSING:`/`UNLOADED:` lines printed above when stdout is not a terminal.
    -- `throwError` reports through Lean's own elaboration-error channel, which both prints
    -- reliably and gives the wrapper a nonzero exit code.
    throwError s!"{unloaded.size} TDA file(s) not reachable from 'import TDA' and {missing.size} public theorem(s) not pinned in scripts/print_axioms.lean (see lines above)"
