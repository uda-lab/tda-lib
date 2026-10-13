/-
Live coverage guard for the axiom-pinning contract in `scripts/print_axioms/*.lean`.
Walks the fully elaborated environment produced by `lake build` and fails unless every
public `theorem` declared inside a `TDA…` module has a `#print axioms` line in
`scripts/print_axioms/*.lean` (the inputs consumed at run time by `scripts/check-axioms.sh`,
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
    consults the `Environment`'s reserved-name registry and Lean's internal/auxiliary-name
    conventions, so it covers `.injEq`, `.mk.inj`, `.mk.sizeOf_spec`, `.noConfusion`,
    `recOn`/`casesOn`/`brecOn` auxiliaries, `.congr_simp`, `match_`/`proof_`/`eq_`
    equation-compiler auxiliaries and `private` declarations without ever catching a
    hand-written theorem that happens to be named `.ext` or nested under a namespace
    component called `mk`. Name-suffix heuristics were tried on the source project and
    hid hand-proved `@[ext]` lemmas; do not reintroduce them.
  * `structure`/`class` field projections — a `Prop`-valued field elaborates as a
    `theorem`-kind projection function; these are mechanical accessors, not claimed
    results, and Lean does not classify them as auto-generated — `Environment.isProjectionFn`.

The additional private audit selects non-reserved private theorem roots, excluding field
projections. It conservatively includes non-reserved generated proof helpers, because Lean's
public classifier also uses lexical heuristics that can match hand-written private names. These roots need no explicit pins:
their transitive axioms are checked here against `propext`, `Classical.choice`, and `Quot.sound`
only when they are outside the union of pinned dependency closures. Already reached private
helpers remain covered by the live audit. Computational `#eval` results are not theorem
claims and do not become additional audit roots. Generated declarations can still be traversed
as dependencies; they do not need blanket pins. This checks elaborated theorem trust, not
computational test correctness or every arbitrary definition/axiom outside theorem closures.

That is the whole list for public pinning. `instance` declarations are deliberately NOT excluded: a
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
import Lean.Util.CollectAxioms

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
`scripts/print_axioms/*.lean`. -/
private def isPublicProjectTheorem (env : Environment) (n : Name) (info : ConstantInfo) :
    CoreM Bool := do
  match info with
  | .thmInfo _ =>
    if !isProjectModule env n then return false
    if (← isAutoDeclOrPrivate_Internal n) then return false
    if env.isProjectionFn n then return false
    return true
  | _ => return false

/-- A non-reserved private theorem root, including private Prop instances.
Do not apply `isAutoDeclOrPrivate_Internal` to the unmangled name: its lexical
`proof_`/`match_` heuristics can also match hand-written claims. We conservatively
retain non-reserved generated helpers; they need no pins, but cannot hide forbidden
axioms. Reserved theorem names and field projections are mechanical declarations. -/
private def isPrivateProjectTheorem (env : Environment) (n : Name) (info : ConstantInfo) :
    CoreM Bool := do
  match info with
  | .thmInfo _ =>
    if !isProjectModule env n then return false
    let some _ := privateToUserName? n | return false
    if isReservedName env n then return false
    if env.isProjectionFn n then return false
    return true
  | _ => return false

/-- The exact expression/constructor edges of Lean 4.33.1's axiom collector.
A generic declaration-usage helper also adds recursor-family edges; those extra edges
must not cause a private proof to be treated as already axiom-audited. Quotient primitives
have no outgoing collector edges. Theorems and opaque declarations include their bodies. -/
private def axiomCollectorDependencies (info : ConstantInfo) : Array Name := Id.run do
  if let .quotInfo _ := info then return #[]
  let mut deps := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    deps := deps ++ value.getUsedConstants
  if let .inductInfo value := info then
    deps := deps ++ value.ctors.toArray
  return deps

/-- Every declaration in the transitive dependency closure of the explicit pins.
Walk imported dependencies too: no namespace shortcut or assumption about dependency
ownership is needed. Each declaration's expression is inspected at most once. -/
private partial def pinnedDependencyClosure (env : Environment) (roots : Array Name) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut pending := roots
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some info := env.checked.get.find? n then
        pending := pending ++ axiomCollectorDependencies info
  return seen

/-- Keep the existing live audit's exact trust policy. `#eval` computations are not
claims: only theorem declarations selected above are additional audit roots. -/
private def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

/-- Audit private claims outside the pinned closure with Lean's own axiom collector.
Private claims inside it are already checked transitively by `check-axioms.sh`. -/
private def auditPrivateTheorems (claims : Array Name) (covered : Std.HashSet Name) :
    CoreM (Nat × Nat) := do
  let mut additional := 0
  let mut failures := 0
  for n in claims.qsort (fun a b => a.toString < b.toString) do
    unless covered.contains n do
      additional := additional + 1
      let forbidden := (← collectAxioms n).filter (!allowedAxiom ·)
      unless forbidden.isEmpty do
        failures := failures + 1
        IO.println s!"PRIVATE AXIOM FAILURE: {privateToUserName n} ({n}) depends on {forbidden}"
  return (additional, failures)

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

/-- Union the pin names in every area file, including future areas. -/
private def readAllPinnedNames (dir : System.FilePath) : IO (Std.HashSet String) := do
  let mut names : Std.HashSet String := {}
  let mut count := 0
  for entry in (← dir.readDir) do
    if entry.path.extension == some "lean" && !(← entry.path.isDir) then
      count := count + 1
      for name in (← readPinnedNames entry.path).toList do
        names := names.insert name
  if count == 0 then
    throw <| IO.userError s!"no Lean pin files in {dir}"
  return names

#eval show CoreM Unit from do
  let env := (← getEnv).setExporting false
  let loadedModules : Std.HashSet String := Std.HashSet.ofList (env.header.moduleNames.toList.map (·.toString))
  let unloaded ← findUnloadedFiles loadedModules
  let pinned ← readAllPinnedNames "scripts/print_axioms"
  let mut total : Nat := 0
  let mut missing : Array String := #[]
  let mut roots : Array Name := #[]
  let mut privateClaims : Array Name := #[]
  for (n, info) in env.constants.toList do
    if pinned.contains n.toString then
      roots := roots.push n
    if (← isPrivateProjectTheorem env n info) then
      privateClaims := privateClaims.push n
    if (← isPublicProjectTheorem env n info) then
      total := total + 1
      let name := n.toString
      unless pinned.contains name do
        missing := missing.push name
  let covered := pinnedDependencyClosure env roots
  let (additional, privateFailures) ← auditPrivateTheorems privateClaims covered
  IO.println s!"PRIVATE AUDIT — {privateClaims.size} roots, {privateClaims.size - additional} already in pinned closures, {additional} additionally checked"
  for f in unloaded do
    IO.println s!"UNLOADED: {f} (module {moduleStringOfPath f} is not reachable from 'import TDA' — its declarations were never checked)"
  for name in missing.qsort (· < ·) do
    IO.println s!"MISSING: {name}"
  if unloaded.isEmpty && missing.isEmpty && privateFailures == 0 then
    IO.println s!"COVERAGE OK — {total} public theorems, all pinned"
  else
    -- `throwError`, not `IO.Process.exit`: the latter terminates the process immediately and
    -- discards the `MISSING:`/`UNLOADED:` lines printed above when stdout is not a terminal.
    -- `throwError` reports through Lean's own elaboration-error channel, which both prints
    -- reliably and gives the wrapper a nonzero exit code.
    throwError s!"{unloaded.size} TDA file(s) not reachable from 'import TDA' and {missing.size} public theorem(s) not pinned in scripts/print_axioms/, {privateFailures} private theorem(s) with forbidden axioms (see lines above)"
