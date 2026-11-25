import TDA.Persistence.F2GridHomologyErosion
import TDA.Persistence.F2GridHomologyInputExamples
import Std.Data.HashSet

/-!
# Native end-to-end erosion fixture (Issue #1063)

Executable measurement and regression for `RatGradedInput.runErosion` on the worked fixture
`triangle` against `shiftedTriangle` in degree one. It is a non-default Lake target and is
not part of the library, the ordinary build or the hosted `check`.

```
erosion-fixture MODE NUM DEN [EXPECT]
```

* `MODE = lib`: run the library `RatGradedInput.runErosion` end to end at the radius
  `NUM/DEN` and print the outcome and its wall time.
* `MODE = phases`: replay the scan of `F2GridRep.erosionFailure?` in the same enumeration
  order with a timer around every `rankAt` call, and report the time and the counts of each
  phase. After `both`, the replayed outcome must equal the library outcome.
* `MODE = split`: like `phases`, but split each `rankAt` into its floor, matrix-construction,
  fiber-dimension and rank parts, with two extra diagnostic queries per matrix.
* `MODE = both`: `lib` followed by `phases`.
* `MODE = noop`: exit at once, to time the process start and module initialisation.

`EXPECT` is `pass`, `fail` or `witness0`, the pinned outcome of `triangle_runErosion_zero`; a
different outcome of the library run exits with status 1. No runtime bound is claimed.

The inputs, degree and radius are decided at run time so that the compiler cannot evaluate them
while initialising the modules.
-/

open TDA.Persistence TDA.Persistence.RatGradedInput TDA.Persistence.RatGrid
  TDA.Persistence.F2GridRep TDA.Persistence.F2GridHomologyInputExamples

namespace TDA.Persistence.ErosionFixture

/-- The outcome type of the end-to-end run. -/
abbrev Res := RatGradedInput.ErosionResult 2

/-- The first input; `b` is true at run time. -/
@[noinline] def firstInput (b : Bool) : RatGradedInput 3 2 := if b then triangle else []

/-- The second input; `b` is true at run time. -/
@[noinline] def secondInput (b : Bool) : RatGradedInput 3 2 := if b then shiftedTriangle else []

def ratStr (q : ℚ) : String := toString q

def gradeStr (p : Fin 2 → ℚ) : String := s!"({ratStr (p 0)}, {ratStr (p 1)})"

def failureStr (w : ErosionFailure 2) : String :=
  s!"fail firstWide={w.firstWide} source={gradeStr w.source} target={gradeStr w.target} " ++
    s!"wideRank={w.wideRank} narrowRank={w.narrowRank}"

def resultStr : Res → String
  | .invalidFirst => "invalidFirst"
  | .invalidSecond => "invalidSecond"
  | .negativeRadius => "negativeRadius"
  | .pass => "pass"
  | .fail w => failureStr w

def witness0 : Res := .fail ⟨true, fun _ => 0, fun _ => 0, 1, 0⟩

def ms (ns : Nat) : String :=
  let t := ns / 1000
  s!"{t / 1000}.{(t % 1000) / 100}{(t % 100) / 10}{t % 10} ms"

/-- Run `act` and return its value and the elapsed nanoseconds. -/
def timed {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- Evaluate `f ()` between two clock readings. `force` is a cheap total function of the value;
branching on it makes the clock reading depend on the evaluation. The thunk takes a unit
argument so that the pure computation is not floated out before the first reading. -/
@[noinline] def timedPure {α : Type} (f : Unit → α) (force : α → Bool) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r := f ()
  if force r then pure ()
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- Mutable counters of the replayed scan. Times are nanoseconds. -/
structure Stats where
  pairs : Nat := 0
  comparable : Nat := 0
  rankCalls : Nat := 0
  matrixCalls : Nat := 0
  tRank : Nat := 0
  tFloor : Nat := 0
  tMap : Nat := 0
  tMatrixRank : Nat := 0
  maxDim : Nat := 0
  tDimSrc : Nat := 0
  tDimTgt : Nat := 0
  tEntry : Nat := 0
  entries : Nat := 0
  keys : Std.HashSet String := {}

/-- One `rankAt` call, timed. The result is forced before the second clock reading. -/
def timedRank (st : IO.Ref Stats) (id : Nat) (R : F2GridRep 2) (x y : Fin 2 → ℚ) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let r := R.rankAt x y
  if r > 1000000000 then throw (IO.userError "impossible rank")
  let t1 ← IO.monoNanosNow
  let low := R.values.hasLower x
  let key := if low then s!"{id}|{gradeStr (R.values.floor x)}|{gradeStr (R.values.floor y)}" else ""
  st.modify fun s =>
    { s with rankCalls := s.rankCalls + 1, tRank := s.tRank + (t1 - t0),
             matrixCalls := s.matrixCalls + (if low then 1 else 0),
             keys := if low then s.keys.insert key else s.keys }
  return r

/-- One `rankAt` call split into floor, matrix construction and rank. Same value as
`R.rankAt x y`. -/
def splitRank (st : IO.Ref Stats) (id : Nat) (R : F2GridRep 2) (x y : Fin 2 → ℚ) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let low := R.values.hasLower x
  let fx := R.values.floor x
  let fy := R.values.floor y
  if fx 0 > 1000000000 then throw (IO.userError "impossible floor")
  let t1 ← IO.monoNanosNow
  if low then
    let M := R.map fx fy
    let tm ← IO.monoNanosNow
    let d := R.dim fx
    if d > 1000000000 then throw (IO.userError "impossible dimension")
    let t2 ← IO.monoNanosNow
    let r := TDA.Persistence.Reduction.F2Matrix.rank M
    if r > 1000000000 then throw (IO.userError "impossible rank")
    let t3 ← IO.monoNanosNow
    -- diagnostics, outside the sum above: one source and one target dimension query, and one
    -- evaluation of one matrix entry
    let d' := R.dim fy
    if d' > 1000000000 then throw (IO.userError "impossible dimension")
    let t4 ← IO.monoNanosNow
    let mut entryNs := 0
    let mut entryCount := 0
    if h : 0 < d' then
      if h' : 0 < d then
        let v := M ⟨0, h⟩ ⟨0, h'⟩
        if v.val > 1000000000 then throw (IO.userError "impossible entry")
        entryNs := (← IO.monoNanosNow) - t4
        entryCount := 1
    let t5 ← IO.monoNanosNow
    let key := s!"{id}|{gradeStr fx}|{gradeStr fy}"
    st.modify fun s =>
      { s with rankCalls := s.rankCalls + 1, matrixCalls := s.matrixCalls + 1,
               tRank := s.tRank + (t3 - t0), tFloor := s.tFloor + (t1 - t0),
               tMap := s.tMap + (tm - t1), tMatrixRank := s.tMatrixRank + (t3 - t2),
               maxDim := max s.maxDim d,
               tDimSrc := s.tDimSrc + (t2 - tm), tDimTgt := s.tDimTgt + (t4 - t3),
               tEntry := s.tEntry + entryNs, entries := s.entries + entryCount,
               keys := s.keys.insert key }
    let _ := t5
    return r
  else
    st.modify fun s =>
      { s with rankCalls := s.rankCalls + 1, tRank := s.tRank + (t1 - t0),
               tFloor := s.tFloor + (t1 - t0) }
    return 0

/-- The failure at one pair, the same four rank uses in the same order as `erosionFailureAt`. -/
def failureAtIO (rk : Nat → F2GridRep 2 → (Fin 2 → ℚ) → (Fin 2 → ℚ) → IO Nat)
    (R S : F2GridRep 2) (e : ℚ) (p q : Fin 2 → ℚ) : IO (Option (ErosionFailure 2)) := do
  let sNarrow ← rk 1 S p q
  let rWide ← rk 0 R (lower e p) (upper e q)
  if sNarrow < rWide then return some ⟨true, p, q, rWide, sNarrow⟩
  let rNarrow ← rk 0 R p q
  let sWide ← rk 1 S (lower e p) (upper e q)
  if rNarrow < sWide then return some ⟨false, p, q, sWide, rNarrow⟩
  return none

/-- The replayed scan of `erosionFailure?`, in the same enumeration order, with a progress line
on stderr at most every five seconds. -/
def scanIO (st : IO.Ref Stats) (rk : Nat → F2GridRep 2 → (Fin 2 → ℚ) → (Fin 2 → ℚ) → IO Nat)
    (R S : F2GridRep 2) (e : ℚ) (T : List (Fin 2 → ℚ)) : IO (Option (ErosionFailure 2)) := do
  let tStart ← IO.monoNanosNow
  let last ← IO.mkRef tStart
  for p in T do
    for q in T do
      st.modify fun s => { s with pairs := s.pairs + 1 }
      if p ≤ q then
        st.modify fun s => { s with comparable := s.comparable + 1 }
        match ← failureAtIO rk R S e p q with
        | some w => return some w
        | none => pure ()
        let now ← IO.monoNanosNow
        if now - (← last.get) > 5000000000 then
          last.set now
          let s ← st.get
          IO.eprintln s!"progress t={ms (now - tStart)} pairs={s.pairs} comparable={s.comparable} rankCalls={s.rankCalls} rankTime={ms s.tRank}"
          (← IO.getStderr).flush
  return none

def report (name : String) (ns : Nat) : IO Unit := IO.println s!"{name} {ms ns}"

def outcome (r : Option (ErosionFailure 2)) : Res :=
  match r with | none => .pass | some w => .fail w

def runLib (xs ys : RatGradedInput 3 2) (p : ℕ) (e : ℚ) : IO (Res) := do
  let (r, t) ← timedPure (fun _ => RatGradedInput.runErosion xs ys p e)
    fun r => r == .invalidFirst
  report "lib.runErosion" t
  IO.println s!"lib.result {resultStr r}"
  return r

def runPhases (split : Bool) (xs ys : RatGradedInput 3 2) (p : ℕ) (e : ℚ)
    (libResult : Option (Res)) : IO Bool := do
  let (v1, tv1) ← timedPure (fun _ => decide (Valid xs)) fun b => !b
  let (v2, tv2) ← timedPure (fun _ => decide (Valid ys)) fun b => !b
  report "phase.validate_first" tv1
  report "phase.validate_second" tv2
  if !(v1 && v2) then
    IO.println "phase.validate: invalid input"
    return false
  let (R, tR) ← timedPure (fun _ => toF2GridRep xs p) fun r => (r.values 0).length > 1000000000
  let (S, tS) ← timedPure (fun _ => toF2GridRep ys p) fun r => (r.values 0).length > 1000000000
  report "phase.toF2GridRep_first" tR
  report "phase.toF2GridRep_second" tS
  let (T, tT) ← timedPure (fun _ => (erosionBreakpoints R.values S.values e).pointList)
    fun T => T.length > 1000000000
  report "phase.breakpoint_grid" tT
  IO.println s!"count.breakpointPoints {T.length}"
  let st ← IO.mkRef ({} : Stats)
  let rk := if split then splitRank st else timedRank st
  let (res, tScan) ← timed (scanIO st rk R S e T)
  let s ← st.get
  report "phase.scan_total" tScan
  report "phase.rankAt_total" s.tRank
  report "phase.scan_excluding_rankAt" (tScan - s.tRank)
  if split then
    report "phase.rankAt.floor" s.tFloor
    report "phase.rankAt.map_construct" s.tMap
    report "phase.rankAt.matrix_rank" s.tMatrixRank
    IO.println s!"count.maxSourceDim {s.maxDim}"
    report "phase.rankAt.dim_source_query" s.tDimSrc
    report "diag.dim_target_query_extra" s.tDimTgt
    report "diag.one_entry_evaluation_sum" s.tEntry
    IO.println s!"diag.entry_samples {s.entries}"
  IO.println s!"count.orderedPairsVisited {s.pairs}"
  IO.println s!"count.comparablePairsVisited {s.comparable}"
  IO.println s!"count.rankAtUses {s.rankCalls}"
  IO.println s!"count.enteringMatrixBranch {s.matrixCalls}"
  IO.println s!"count.distinctKeys {s.keys.size}"
  let r := outcome res
  IO.println s!"phases.result {resultStr r}"
  match libResult with
  | some l =>
    if l == r then IO.println "phases.agrees_with_lib true"; return true
    else IO.println "phases.agrees_with_lib false"; return false
  | none => return true

def parseRat (n d : String) : Option ℚ := do
  let n ← n.toInt?
  let d ← d.toInt?
  if d == 0 then none else some (Rat.divInt n d)

def usage : IO UInt32 := do
  IO.eprintln "usage: erosion-fixture (lib|phases|split|both) NUM DEN [pass|fail|witness0] | noop"
  return 64

def check (expect : String) (r : Res) : IO UInt32 := do
  let ok := match expect, r with
    | "pass", .pass => true
    | "fail", .fail _ => true
    | "witness0", r => r == witness0
    | _, _ => false
  if ok then
    IO.println s!"expect {expect}: ok"
    return 0
  else
    IO.println s!"expect {expect}: MISMATCH (got {resultStr r})"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["noop"] => return 0
  | mode :: n :: d :: rest =>
    let some e := parseRat n d | usage
    let flag := args.length < 1000
    let xs := firstInput flag
    let ys := secondInput flag
    let p : ℕ := (rest.drop 1).head?.bind String.toNat? |>.getD 1
    let expect := rest.head?.getD ""
    IO.println s!"radius {ratStr e} degree {p}"
    let mut code : UInt32 := 0
    let mut libRes : Option (Res) := none
    if mode == "lib" || mode == "both" then
      let r ← runLib xs ys p e
      libRes := some r
      if expect != "" then code ← check expect r
    if mode == "phases" || mode == "both" || mode == "split" then
      let ok ← runPhases (mode == "split") xs ys p e libRes
      if !ok then code := 1
    if !(mode == "lib" || mode == "both" || mode == "phases" || mode == "split") then
      return (← usage)
    return code
  | _ => usage

end TDA.Persistence.ErosionFixture

def main (args : List String) : IO UInt32 := TDA.Persistence.ErosionFixture.main args
