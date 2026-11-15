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
public classifier also uses lexical heuristics that can match hand-written private names. These
roots need no explicit pins: every one of them has its own transitive axioms checked here,
directly, against `propext`, `Classical.choice`, and `Quot.sound` with Lean's own axiom
collector (`#949`: no pinned-dependency-closure walk is computed first to exclude roots a
public pin already reaches transitively — auditing every root directly is a strict superset of
that older check and removes the closure walk's cost). Computational `#eval` results are not
theorem claims and do not become additional audit roots. Generated declarations can still be
traversed as dependencies by the live audit on a public pin that reaches them; they do not need
blanket pins themselves. This checks elaborated theorem trust, not computational test
correctness or every arbitrary definition/axiom outside theorem closures.

That is the whole list for public pinning. `instance` declarations are deliberately NOT excluded: a
hand-proved `instance : SomePropClass … := proof` in a project module is a claimed result
and must be pinned; typeclass resolution at call sites never creates a new named
declaration in this project's own modules, so there is no auto-derived category to skip.
Iterate this list, not the caller, if a false positive or negative shows up.

The scan walks only the constants declared in `TDA`-prefixed modules, found via each
loaded module's own `ModuleData.constNames`/`.constants` (parallel arrays, already
populated by `import TDA`), not every constant in the environment: that environment also
holds Mathlib's own ~9000 modules, and the old per-constant `env.getModuleIdxFor?` check
to filter them out was itself the scan's dominant cost (measured on #949's follow-up).
Module membership is therefore established once per module, not once per declaration.

A prerequisite the whole walk depends on: `import TDA` must load every
`TDA/**/*.lean` file, directly or transitively, or that file's declarations never
reach a `TDA`-prefixed module's `ModuleData` and every check passes vacuously for its
content. So this file also discovers every `.lean` file on disk under `TDA/` and fails
if any of them is not among `env.header.moduleNames` — the set this run's `import TDA`
actually loaded, not a static read of the root aggregator's import list (so a file
reachable only from a forgotten nested aggregator is caught too).

Additive for Issue #951 (the incremental local gate): this file also writes
`.agents/scratch/full-gate-module-audit.json`, a per-module breakdown (`public` and
`declared` theorem-name arrays) of exactly the same classification this file already
computes — no new environment load, no new check, no change to any existing printed line
or to the pass/fail decision. Only `scripts/check-incremental.sh` reads it, and only after
this file and `scripts/check-axioms.sh` have both already exited zero in the same run (i.e.
only once the whole-library guarantee this file and that script already establish is known
to hold), to refresh per-module incremental-audit records without a second environment
load. Plain `scripts/check.sh` (no flag) and `--stable` never read it.

`scripts/rename-project.sh` rewrites every `TDA` occurrence in this file.
-/
import TDA
import Lean.Util.CollectAxioms
import Lean.Data.Json

open Lean System

/-- `n`/`info` is a public theorem this repository must pin in
`scripts/print_axioms/*.lean`. Callers already restrict to names declared in a `TDA`
module — by iterating that module's own `ModuleData` (see the scan below) rather than
every constant in the environment — so no module-membership check is repeated here. -/
private def isPublicProjectTheorem (env : Environment) (n : Name) (info : ConstantInfo) :
    CoreM Bool := do
  match info with
  | .thmInfo _ =>
    if (← isAutoDeclOrPrivate_Internal n) then return false
    if env.isProjectionFn n then return false
    return true
  | _ => return false

/-- A non-reserved private theorem root, including private Prop instances.
Do not apply `isAutoDeclOrPrivate_Internal` to the unmangled name: its lexical
`proof_`/`match_` heuristics can also match hand-written claims. We conservatively
retain non-reserved generated helpers; they need no pins, but cannot hide forbidden
axioms. Reserved theorem names and field projections are mechanical declarations.
Module membership is the caller's responsibility, as above. -/
private def isPrivateProjectTheorem (env : Environment) (n : Name) (info : ConstantInfo) :
    CoreM Bool := do
  match info with
  | .thmInfo _ =>
    let some _ := privateToUserName? n | return false
    if isReservedName env n then return false
    if env.isProjectionFn n then return false
    return true
  | _ => return false

/-- Keep the existing live audit's exact trust policy. `#eval` computations are not
claims: only theorem declarations selected above are additional audit roots. -/
private def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

/-- Audit every private claim directly with Lean's own axiom collector (`collectAxioms`,
the same primitive `#print axioms` uses). No pinned-dependency-closure walk precedes this:
a root already reachable from a public pin is checked both here and, transitively, by the
live audit on that pin — redundant but never unsound, and this is what removes the closure
walk's cost (#949). -/
private def auditPrivateTheorems (claims : Array Name) : CoreM Nat := do
  let mut failures := 0
  for n in claims.qsort (fun a b => a.toString < b.toString) do
    let forbidden := (← collectAxioms n).filter (!allowedAxiom ·)
    unless forbidden.isEmpty do
      failures := failures + 1
      IO.println s!"PRIVATE AXIOM FAILURE: {privateToUserName n} ({n}) depends on {forbidden}"
  return failures

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
  let t0 ← IO.monoMsNow
  let env := (← getEnv).setExporting false
  let loadedModules : Std.HashSet String := Std.HashSet.ofList (env.header.moduleNames.toList.map (·.toString))
  let unloaded ← findUnloadedFiles loadedModules
  let pinned ← readAllPinnedNames "scripts/print_axioms"
  let t1 ← IO.monoMsNow
  let mut total : Nat := 0
  let mut missing : Array String := #[]
  let mut privateClaims : Array Name := #[]
  -- §#951 side-car accumulators: populated inline below using each module's own `modIdx`-
  -- derived name. Never a second `getModuleIdxFor?` lookup per constant — that per-constant
  -- lookup is exactly what the `ModuleData` restructuring below removed (see its comment);
  -- reintroducing it here to resolve a module name would silently undo that fix.
  let mut perModulePublic : Std.HashMap String (Array String) := {}
  let mut perModuleDeclared : Std.HashMap String (Array String) := {}
  -- Iterate only the constants declared in TDA's own modules, via each module's own
  -- `ModuleData`, instead of every constant in the environment (Mathlib's ~9000
  -- modules dominate `env.constants`, which made the old per-constant
  -- `env.getModuleIdxFor?` check the scan's real cost). `moduleData[i].constNames`
  -- and `.constants` are parallel arrays already populated by `import TDA`; no
  -- separate environment lookup is needed per declaration.
  for modIdx in [0:env.header.moduleData.size] do
    if (`TDA).isPrefixOf env.header.moduleNames[modIdx]! then
      let modStr := env.header.moduleNames[modIdx]!.toString  -- §#951: already known, no lookup
      let data := env.header.moduleData[modIdx]!
      for i in [0:data.constNames.size] do
        let n := data.constNames[i]!
        let info := data.constants[i]!
        if let .thmInfo _ := info then
          if (← isPrivateProjectTheorem env n info) then
            privateClaims := privateClaims.push n
            perModuleDeclared := perModuleDeclared.insert modStr
              ((perModuleDeclared.getD modStr #[]).push n.toString)
          if (← isPublicProjectTheorem env n info) then
            total := total + 1
            let name := n.toString
            unless pinned.contains name do
              missing := missing.push name
            perModuleDeclared := perModuleDeclared.insert modStr
              ((perModuleDeclared.getD modStr #[]).push n.toString)
            perModulePublic := perModulePublic.insert modStr
              ((perModulePublic.getD modStr #[]).push n.toString)
  let t2 ← IO.monoMsNow
  let privateFailures ← auditPrivateTheorems privateClaims
  let t3 ← IO.monoMsNow
  -- §#951 side-car: a per-module breakdown of the same names already classified above.
  -- Written unconditionally (before the pass/fail decision below) so a caller can refresh
  -- incremental-audit records for exactly the modules this run covered, whether or not this
  -- run's own pass/fail decision ultimately succeeds — a caller only ever reads this file
  -- after confirming (from this process's own exit code) that the run passed.
  let moduleNames := (perModuleDeclared.toList.map Prod.fst ++ perModulePublic.toList.map Prod.fst)
    |>.foldl (fun (s : Std.HashSet String) n => s.insert n) {} |>.toList
  let modulesJson := Json.mkObj (moduleNames.map fun modStr =>
    (modStr, Json.mkObj [
      ("public", Json.arr ((perModulePublic.getD modStr #[]).map Json.str)),
      ("declared", Json.arr ((perModuleDeclared.getD modStr #[]).map Json.str))
    ]))
  IO.FS.createDirAll ".agents/scratch"
  IO.FS.writeFile ".agents/scratch/full-gate-module-audit.json" (Json.mkObj [("modules", modulesJson)]).compress
  IO.println s!"COVERAGE TIMING — setup (unloaded files + pins): {t1 - t0} ms, scan constants: {t2 - t1} ms, private audit: {t3 - t2} ms, total: {t3 - t0} ms"
  IO.println s!"PRIVATE AUDIT — {privateClaims.size} private theorem root(s), each audited directly with collectAxioms"
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
