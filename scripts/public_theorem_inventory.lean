/-
Advisory inventory for the public-theorem downstream-use audit (#1207, stage 2). Prints a TSV
with one row per public declaration of the `TDA` modules loaded by `import TDA`, read from the
elaborated environment produced by `lake build`. Nothing here is a gate, is run by
`scripts/check.sh`, or reads or alters a statement.

Run from the root of the tree to inventory, after `lake build`:

    scripts/lean.sh lake env lean scripts/public_theorem_inventory.lean > inventory.tsv

(an `#eval`, like `scripts/check_axiom_coverage.lean`, not a `main`, so no `--run`). Pass this
file's path from another tree's root to inventory that tree, as
`scripts/check-released-signatures.sh` does for the signature dump. Output is sorted by
name and deterministic for a given build. The header row is the first line. Progress and counts
are not printed; a summary is easy to compute from the columns with `awk`.

"Public" follows `scripts/check_axiom_coverage.lean`: a constant stored in the `ModuleData` of a
`TDA`-prefixed module (so no Mathlib constant), that Lean does not consider automatically
generated or private (`isAutoDeclOrPrivate_Internal`) and that is not a structure field
projection (`Environment.isProjectionFn`). The coverage audit applies this to `theorem`
declarations only. This tool applies the same filter to every kind and keeps: theorem,
instance (a `def` or a Prop-valued `theorem` registered as an instance), def, opaque, axiom,
inductive, structure, class and the constructors of non-structure inductives. Structure
constructors, recursors and quotient constants are left out as mechanical.

Columns
  name         full declaration name
  module       declaring module
  area         first component after `TDA.` (the module itself for a top-level `TDA.X`)
  kind         theorem | instance | def | opaque | axiom | inductive | structure | class | ctor
  is_theorem   1 when the constant is a `theorem` declaration, which is exactly the set
               `scripts/check_axiom_coverage.lean` counts, otherwise 0
  pinned       1 when named by an unindented `#print axioms` line of `scripts/print_axioms/*.lean`
  examples     1 when the last component of the module is `Examples` or ends in `Examples`
  alias        empty | deprecated | wrapper | wrapper-loose
                 deprecated    carries `@[deprecated]`
                 wrapper       the value, under its lambda binders, is one application of another
                               public declaration whose explicit arguments are all bound variables
                 wrapper-loose same shape, but some explicit argument is a compound term
               For a theorem the wrapped declaration must also be a theorem.
  alias_target the other declaration (for `deprecated`, the replacement named in the attribute,
               when it is a public declaration of this inventory), otherwise empty
  group        first-pass family key, deterministic: the target's group for `deprecated` and
               `wrapper` rows, otherwise the declaring module with a trailing `Examples` removed
               when the remainder is a loaded module (an `*Examples` module joins its headline
               module); `wrapper-loose` rows are grouped by module and only flagged
  disposition  seed disposition: fixture (`examples` = 1), internal wrapper (`deprecated` or
               `wrapper`), non-theorem (not a theorem, carried for grouping and counting),
               otherwise pending. These are starting values for the audit; they prove no use.
  ref_other    number of constants of other `TDA` modules, outside `*Examples` modules, whose
               type or value mentions this declaration (private and generated constants count)
  ref_same     the same count over the declaring module, the declaration itself excluded
  ref_examples the same count over `*Examples` modules
  doc          first line of the docstring, tabs and newlines removed

`scripts/rename-project.sh` rewrites every `TDA` occurrence in this file.
-/
import TDA
import Lean.Linter.Deprecated

open Lean Meta System

/-- Names pinned by unindented `#print axioms <name>` lines, as in `scripts/check-axioms.sh`. -/
private def pinNames (dir : FilePath) : IO (Std.HashSet String) := do
  let mut names : Std.HashSet String := {}
  for entry in (← dir.readDir) do
    if entry.path.extension == some "lean" then
      for line in (← IO.FS.readFile entry.path).splitOn "\n" do
        if line.startsWith "#print axioms " then
          let rest := (line.drop "#print axioms ".length).toString.replace "\t" " "
          if let some n := (rest.splitOn " ").find? (· ≠ "") then names := names.insert n
  return names

private structure Row where
  name : Name
  modName : Name
  kind : String
  isThm : Bool
  pinned : Bool
  deprecated : Bool
  depTarget : Option Name
  /-- `(target, strict)` of the single application the value consists of. -/
  wrap : Option (Name × Bool)
  doc : String

private def endsWithExamples (m : Name) : Bool :=
  match m with
  | .str _ s => s.endsWith "Examples"
  | _ => false

/-- Public kind of a constant, or `none` for mechanical constants this inventory leaves out. -/
private def publicKind? (env : Environment) (n : Name) (info : ConstantInfo) :
    CoreM (Option String) := do
  if (← isAutoDeclOrPrivate_Internal n) then return none
  if env.isProjectionFn n then return none
  match info with
  | .thmInfo _ => return some (if Meta.isInstanceCore env n then "instance" else "theorem")
  | .defnInfo _ => return some (if Meta.isInstanceCore env n then "instance" else "def")
  | .opaqueInfo _ => return some "opaque"
  | .axiomInfo _ => return some "axiom"
  | .inductInfo _ =>
    return some (if isClass env n then "class" else if isStructure env n then "structure"
      else "inductive")
  | .ctorInfo c => return if isStructure env c.induct then none else some "ctor"
  | _ => return none

private def valueOf? : ConstantInfo → Option Expr
  | .thmInfo i => some i.value
  | .defnInfo i => some i.value
  | _ => none

/-- The public declaration `n`'s value applies, if the value is one application of it. -/
private def wrapperOf (env : Environment) (isPublic : Name → Bool) (n : Name) (v : Expr) :
    MetaM (Option (Name × Bool)) :=
  lambdaTelescope v fun _ body => do
    let body := body.consumeMData
    let .const c _ := body.getAppFn | return none
    if c == n || !isPublic c then return none
    let some cinfo := env.find? c | return none
    let args := body.getAppArgs
    let mut ty := cinfo.type
    let mut strict := true
    for a in args do
      match ty with
      | .forallE _ _ b bi =>
        if bi.isExplicit && !a.consumeMData.isFVar then strict := false
        ty := b
      | _ => strict := false
    return some (c, strict)

private def firstLine (s : String) : String :=
  match (s.splitOn "\n").find? (·.trimAscii.toString ≠ "") with
  | some l => (l.trimAscii.toString.replace "\t" " ").replace "\r" ""
  | none => ""

#eval show MetaM Unit from do
  let env := (← getEnv).setExporting false
  let pins ← pinNames "scripts/print_axioms"
  let mut rows : Array Row := #[]
  let mut modules : Std.HashSet Name := {}
  for modIdx in [0:env.header.moduleData.size] do
    let modName := env.header.moduleNames[modIdx]!
    if (`TDA).isPrefixOf modName then
      modules := modules.insert modName
      let data := env.header.moduleData[modIdx]!
      for i in [0:data.constNames.size] do
        let n := data.constNames[i]!
        let info := data.constants[i]!
        if let some kind ← publicKind? env n info then
          let depTarget := Linter.getDeprecatedNewName env n
          rows := rows.push
            { name := n, modName, kind, isThm := info.isTheorem, pinned := pins.contains n.toString
              deprecated := Linter.isDeprecated env n, depTarget, wrap := none
              doc := firstLine ((← findDocString? env n).getD "") }
  let isPublicName : Std.HashMap Name Row := rows.foldl (fun m r => m.insert r.name r) {}
  -- Second pass: wrappers. A theorem may only wrap a theorem.
  let mut withWrap : Array Row := #[]
  for r in rows do
    let some info := env.find? r.name | withWrap := withWrap.push r; continue
    let some v := valueOf? info | withWrap := withWrap.push r; continue
    let isPub (c : Name) : Bool :=
      match isPublicName[c]? with
      | some t => !r.isThm || t.isThm
      | none => false
    withWrap := withWrap.push { r with wrap := ← wrapperOf env isPub r.name v }
  let sorted := withWrap.qsort (fun a b => a.name.toString < b.name.toString)
  let byName : Std.HashMap Name Row := sorted.foldl (fun m r => m.insert r.name r) {}
  -- Alias target and kind: deprecated first, else the single application.
  let aliasOf (r : Row) : String × Option Name :=
    if r.deprecated then
      ("deprecated", r.depTarget.filter (byName.contains ·))
    else match r.wrap with
      | some (c, true) => ("wrapper", some c)
      | some (c, false) => ("wrapper-loose", some c)
      | none => ("", none)
  let stem (m : Name) : Name :=
    match m with
    | .str p s =>
      if s.endsWith "Examples" && s != "Examples" then
        let c := Name.str p (s.dropEnd "Examples".length).toString
        if modules.contains c then c else m
      else if s == "Examples" && modules.contains p && p != `TDA then p else m
    | _ => m
  let rec groupOf (fuel : Nat) (r : Row) : String :=
    let (a, tgt) := aliasOf r
    match fuel, (if a == "deprecated" || a == "wrapper" then tgt else none) with
    | fuel + 1, some t =>
      match byName[t]? with
      | some tr => groupOf fuel tr
      | none => (stem r.modName).toString
    | _, _ => (stem r.modName).toString
  -- Reference counts over every constant of the `TDA` modules.
  let mut refOther : Std.HashMap Name Nat := {}
  let mut refSame : Std.HashMap Name Nat := {}
  let mut refExamples : Std.HashMap Name Nat := {}
  for modIdx in [0:env.header.moduleData.size] do
    let userMod := env.header.moduleNames[modIdx]!
    if (`TDA).isPrefixOf userMod then
      let data := env.header.moduleData[modIdx]!
      for i in [0:data.constNames.size] do
        let user := data.constNames[i]!
        let info := data.constants[i]!
        let mut used := info.type.getUsedConstantsAsSet
        if let some v := valueOf? info then used := used.union v.getUsedConstantsAsSet
        for c in used do
          if c != user then
            if let some r := byName[c]? then
              if endsWithExamples userMod then
                refExamples := refExamples.insert c (refExamples.getD c 0 + 1)
              else if r.modName == userMod then refSame := refSame.insert c (refSame.getD c 0 + 1)
              else refOther := refOther.insert c (refOther.getD c 0 + 1)
  IO.println "name\tmodule\tarea\tkind\tis_theorem\tpinned\texamples\talias\talias_target\tgroup\tdisposition\tref_other\tref_same\tref_examples\tdoc"
  let b2s (b : Bool) : String := if b then "1" else "0"
  for r in sorted do
    let (a, tgt) := aliasOf r
    let comps := r.modName.components
    let area := match comps with
      | _ :: x :: _ => x.toString
      | [x] => x.toString
      | [] => ""
    let ex := endsWithExamples r.modName
    let disp :=
      if !r.isThm then "non-theorem"
      else if ex then "fixture"
      else if a == "deprecated" || a == "wrapper" then "internal wrapper"
      else "pending"
    let cell (s : String) : String := (s.replace "\t" " ").replace "\n" " "
    IO.println s!"{r.name}\t{r.modName}\t{area}\t{r.kind}\t{b2s r.isThm}\t{b2s r.pinned}\t{b2s ex}\t{a}\t{(tgt.map (·.toString)).getD ""}\t{groupOf 64 r}\t{disp}\t{refOther.getD r.name 0}\t{refSame.getD r.name 0}\t{refExamples.getD r.name 0}\t{cell r.doc}"
