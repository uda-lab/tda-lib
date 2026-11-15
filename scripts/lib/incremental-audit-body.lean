/-
Static body for the selective incremental-audit Lean file (Issue #951). NEVER run this file
standalone — it has no `import` of its own on purpose. `scripts/check-incremental.sh`
generates a header (an exact `import TDA.…` line per module this run must freshly audit,
because that module's content-hashed key has no recorded PASS) and concatenates that header
in front of a copy of this file into one temporary `.lean`, then runs the combined file once
with `lake env lean`. Changing this file changes every module's incremental-audit key
(`scripts/lib/incremental-cache.py`'s `AUDIT_TOOL_SOURCES`), so a behavioural change here can
never be masked by a stale cache hit.

Mirrors `scripts/check_axiom_coverage.lean`'s public/private theorem classification exactly
(same predicates, same reasons for excluding auto-generated/projection declarations — see
that file's header comment for the rationale), but:
  - restricts every classification to a caller-supplied SET of module names (the modules this
    run was asked to audit), read at run time from a sidecar text file, instead of "any module
    prefixed `TDA`" — a module reachable only as a TRANSITIVE dependency of an audited module,
    but itself not in that set, already has its own recorded PASS and must not be re-recorded
    or re-counted here;
  - calls `Lean.collectAxioms` directly on every selected declaration, public and private
    alike (the full gate's `check-axioms.sh` instead parses `#print axioms` text output; this
    file calls the same underlying Lean API directly, which is simpler to scope per module and
    avoids a second text round trip — this is sound for the same reason `#print axioms` is:
    both ultimately call `Lean.collectAxioms`, see `scripts/lib/incremental-cache.py`'s module
    docstring);
  - writes a JSON side-car per module (`public` and `declared` name arrays) instead of
    printing `#print axioms`/`MISSING:` lines, so `scripts/check-incremental.sh` can turn each
    module's result directly into a content-keyed PASS record.

A forbidden axiom anywhere, or any scope/import mismatch, still fails the whole process
(`throwError`, nonzero exit), exactly as the full gate's audit and coverage guards do; this
file's exit code is never treated as success unless it is actually zero.
-/
import Lean.Util.CollectAxioms
import Lean.Data.Json

open Lean System

/-- The module name `n` was declared in, if `n` belongs to a module Lean actually loaded. -/
private def moduleNameOf (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

private def isInScope (env : Environment) (scope : Std.HashSet String) (n : Name) : Bool :=
  match moduleNameOf env n with
  | some m => scope.contains m.toString
  | none => false

/-- A public theorem of a module in `scope`, by the same rule as
`scripts/check_axiom_coverage.lean`'s `isPublicProjectTheorem`. -/
private def isPublicScopedTheorem (env : Environment) (scope : Std.HashSet String) (n : Name)
    (info : ConstantInfo) : CoreM Bool := do
  match info with
  | .thmInfo _ =>
    if !isInScope env scope n then return false
    if (← isAutoDeclOrPrivate_Internal n) then return false
    if env.isProjectionFn n then return false
    return true
  | _ => return false

/-- A non-reserved private theorem root of a module in `scope`, by the same rule as
`scripts/check_axiom_coverage.lean`'s `isPrivateProjectTheorem`. -/
private def isPrivateScopedTheorem (env : Environment) (scope : Std.HashSet String) (n : Name)
    (info : ConstantInfo) : CoreM Bool := do
  match info with
  | .thmInfo _ =>
    if !isInScope env scope n then return false
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

#eval show CoreM Unit from do
  let env := (← getEnv).setExporting false
  let scope ← readScope ".agents/scratch/incremental-audit-scope.txt"
  let loadedModules : Std.HashSet String :=
    Std.HashSet.ofList (env.header.moduleNames.toList.map (·.toString))
  let mut perModulePublic : Std.HashMap String (Array String) := {}
  let mut perModuleDeclared : Std.HashMap String (Array String) := {}
  let mut failures : Array String := #[]
  let mut auditedCount : Nat := 0
  for (n, info) in env.constants.toList do
    if let .thmInfo _ := info then
      let isPub ← isPublicScopedTheorem env scope n info
      let isPriv ← isPrivateScopedTheorem env scope n info
      if isPub || isPriv then
        let some modName := moduleNameOf env n | continue
        let modStr := modName.toString
        auditedCount := auditedCount + 1
        let forbidden := (← collectAxioms n).filter (!allowedAxiom ·)
        unless forbidden.isEmpty do
          let message := s!"{n} depends on forbidden axioms {forbidden}"
          IO.println s!"INCREMENTAL AXIOM FAILURE: {message}"
          failures := failures.push message
        perModuleDeclared := perModuleDeclared.insert modStr
          ((perModuleDeclared.getD modStr #[]).push n.toString)
        if isPub then
          perModulePublic := perModulePublic.insert modStr
            ((perModulePublic.getD modStr #[]).push n.toString)
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
      ("declared", Json.arr ((perModuleDeclared.getD modStr #[]).map Json.str))
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
