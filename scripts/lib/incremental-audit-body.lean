/-
Static body for the selective incremental-audit Lean file (Issue #951). NEVER run this file
standalone — it has no `import` of its own on purpose. `scripts/check-incremental.sh`
generates a header (an exact `import TDA.…` line per module this run must freshly audit,
because that module's content-hashed key has no recorded PASS) and concatenates that header
in front of a copy of this file into one temporary `.lean`, then runs the combined file once
with `lake env lean`. Changing this file changes every module's incremental-audit key
(`scripts/lib/incremental-cache.py`'s `AUDIT_TOOL_SOURCES`), so a behavioural change here can
never be masked by a stale cache hit.

Walks each scope module's own `ModuleData.constNames`/`.constants` directly (mirroring
`scripts/check_axiom_coverage.lean`'s #976 restructuring), rather than iterating every
constant in the environment and filtering by a per-constant module lookup — the same
per-constant `getModuleIdxFor?` cost #976 removed from the full gate's coverage scan would
otherwise dominate THIS file too, defeating the entire purpose of an incremental gate.

Produces three per-module name lists, not two:
  - `public`/`declared`: the same public/private THEOREM classification
    `scripts/check_axiom_coverage.lean` uses (same predicates, same reasons for excluding
    auto-generated/projection declarations — see that file's header comment), used only for
    the "every public theorem is pinned" direction.
  - `clean`: every name `scripts/print_axioms/*.lean` PINS that belongs to a scope module,
    of ANY declaration kind (ordinary `def`, `structure`, a hand-written `theorem`, or one of
    Lean's own auto-generated `._proof_N` auxiliaries — this project pins all of these, not
    only theorems, e.g. `TDA.Topology.Refinement` is a structure and
    `TDA.Persistence.dgm._proof_1` is auto-generated), each audited here directly with
    `collectAxioms`, mirroring `scripts/check-axioms.sh`'s own unrestricted `#print axioms`
    audit of whatever is pinned. `clean` is what `scripts/check-incremental.sh`'s pin
    cross-check verifies against; `declared` is NOT a sound proxy for it (a review of this
    PR found the earlier, declared-only cross-check failed on every genuinely fresh run,
    because most of this project's pins are not theorems).

Calls `Lean.collectAxioms` directly on every selected declaration (the full gate's
`check-axioms.sh` instead parses `#print axioms` text output; this file calls the same
underlying Lean API directly, which is simpler to scope per module and avoids a second text
round trip — this is sound for the same reason `#print axioms` is: both ultimately call
`Lean.collectAxioms`, see `scripts/lib/incremental-cache.py`'s module docstring). Writes a
JSON side-car per module instead of printing `#print axioms`/`MISSING:` lines, so
`scripts/check-incremental.sh` can turn each module's result directly into a content-keyed
PASS record.

A forbidden axiom anywhere, or any scope/import mismatch, still fails the whole process
(`throwError`, nonzero exit), exactly as the full gate's audit and coverage guards do; this
file's exit code is never treated as success unless it is actually zero.
-/
import Lean.Util.CollectAxioms
import Lean.Data.Json

open Lean System

/-- A public theorem of a module in `scope`, by the same rule as
`scripts/check_axiom_coverage.lean`'s `isPublicProjectTheorem`. Callers already restrict to a
scope module's own constants (via `ModuleData`), so no module-membership check is repeated
here. -/
private def isPublicScopedTheorem (env : Environment) (n : Name) (info : ConstantInfo) :
    CoreM Bool := do
  match info with
  | .thmInfo _ =>
    if (← isAutoDeclOrPrivate_Internal n) then return false
    if env.isProjectionFn n then return false
    return true
  | _ => return false

/-- A non-reserved private theorem root of a module in `scope`, by the same rule as
`scripts/check_axiom_coverage.lean`'s `isPrivateProjectTheorem`. -/
private def isPrivateScopedTheorem (env : Environment) (n : Name) (info : ConstantInfo) :
    CoreM Bool := do
  match info with
  | .thmInfo _ =>
    let some _ := privateToUserName? n | return false
    if isReservedName env n then return false
    if env.isProjectionFn n then return false
    return true
  | _ => return false

private def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

private def readScope (path : System.FilePath) : IO (Std.HashSet String) := do
  let text ← IO.FS.readFile path
  return Std.HashSet.ofList ((text.splitOn "\n").filter (· ≠ ""))

/-- The declaration names pinned by `#print axioms <name>` lines in `path` — the exact same
extraction rule `scripts/check_axiom_coverage.lean`'s `readPinnedNames` and
`scripts/check-axioms.sh`'s `awk '/^#print axioms /{print $3}'` use. -/
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
  let scope ← readScope ".agents/scratch/incremental-audit-scope.txt"
  let pinned ← readAllPinnedNames "scripts/print_axioms"
  let loadedModules : Std.HashSet String :=
    Std.HashSet.ofList (env.header.moduleNames.toList.map (·.toString))
  let mut perModulePublic : Std.HashMap String (Array String) := {}
  let mut perModuleDeclared : Std.HashMap String (Array String) := {}
  let mut perModuleClean : Std.HashMap String (Array String) := {}
  let mut failures : Array String := #[]
  let mut auditedCount : Nat := 0
  for modIdx in [0:env.header.moduleData.size] do
    let modStr := env.header.moduleNames[modIdx]!.toString
    if scope.contains modStr then
      let data := env.header.moduleData[modIdx]!
      for i in [0:data.constNames.size] do
        let n := data.constNames[i]!
        let info := data.constants[i]!
        let name := n.toString
        -- Every PINNED name belonging to this module is audited directly, whatever its
        -- declaration kind — mirrors scripts/check-axioms.sh's own unrestricted audit of
        -- every pin, not only theorems.
        if pinned.contains name then
          auditedCount := auditedCount + 1
          let forbidden := (← collectAxioms n).filter (!allowedAxiom ·)
          unless forbidden.isEmpty do
            let message := s!"{n} depends on forbidden axioms {forbidden}"
            IO.println s!"INCREMENTAL AXIOM FAILURE: {message}"
            failures := failures.push message
          perModuleClean := perModuleClean.insert modStr
            ((perModuleClean.getD modStr #[]).push name)
        if let .thmInfo _ := info then
          let isPub ← isPublicScopedTheorem env n info
          let isPriv ← isPrivateScopedTheorem env n info
          if isPub || isPriv then
            -- A pinned theorem was already audited above (and is in `clean`); an unpinned
            -- theorem still needs its own axiom check here — soundness cannot wait for the
            -- separate coverage requirement that it eventually gets pinned.
            unless pinned.contains name do
              auditedCount := auditedCount + 1
              let forbidden := (← collectAxioms n).filter (!allowedAxiom ·)
              unless forbidden.isEmpty do
                let message := s!"{n} depends on forbidden axioms {forbidden}"
                IO.println s!"INCREMENTAL AXIOM FAILURE: {message}"
                failures := failures.push message
            perModuleDeclared := perModuleDeclared.insert modStr
              ((perModuleDeclared.getD modStr #[]).push name)
            if isPub then
              perModulePublic := perModulePublic.insert modStr
                ((perModulePublic.getD modStr #[]).push name)
  -- Every scope entry must actually have been reached by the generated import header, or the
  -- scope file and that header disagree with each other — a module with genuinely zero
  -- theorems (e.g. a pure imports-only aggregator) is fine and just gets an empty record;
  -- a module Lean never loaded at all is a tooling bug and must fail loudly, not pass
  -- vacuously with an empty record indistinguishable from the legitimate case.
  for modStr in scope.toList do
    unless loadedModules.contains modStr do
      let message := s!"module {modStr} is in scope but was never loaded (generated import header / scope file mismatch)"
      IO.println s!"INCREMENTAL AUDIT FAILURE: {message}"
      failures := failures.push message
  let modulesJson := Json.mkObj (scope.toList.map fun modStr =>
    (modStr, Json.mkObj [
      ("public", Json.arr ((perModulePublic.getD modStr #[]).map Json.str)),
      ("declared", Json.arr ((perModuleDeclared.getD modStr #[]).map Json.str)),
      ("clean", Json.arr ((perModuleClean.getD modStr #[]).map Json.str))
    ]))
  let outcome := Json.mkObj [
    ("modules", modulesJson),
    ("failures", Json.arr (failures.map Json.str))
  ]
  IO.FS.createDirAll ".agents/scratch"
  IO.FS.writeFile ".agents/scratch/incremental-audit-output.json" outcome.compress
  IO.println s!"INCREMENTAL AUDIT — {scope.size} module(s), {auditedCount} declaration(s), {failures.size} failure(s)"
  unless failures.isEmpty do
    throwError s!"{failures.size} declaration(s)/module(s) failed the incremental audit (see .agents/scratch/incremental-audit-output.json and the lines above)"
