import TDA.Mapper.GraphPLReebData

/-!
# Closed level sets of graph-PL height

For a graph realization with piecewise-linear height, this module defines closed levels and
classifies their path components by the level vertices already used by the finite Reeb data.
The classification is first established over an arbitrary open interval containing exactly one
vertex height, followed by the crossing-point and horizontal-edge lemmas needed for the closed
level description.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

universe u

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-! ## Levels and level windows -/

/-- The subspace of the realization at the height `c`. -/
abbrev ClosedLevel (c : ℝ) : Type u :=
  {p : Realization G // plHeight G h p ∈ ({c} : Set ℝ)}

/-- An open interval containing `c` and no other vertex height. -/
abbrev IsLevelWindow (c : ℝ) (I : OpenInterval) : Prop :=
  c ∈ I ∧ ∀ v, h v ∈ I → h v = c

private theorem IsLevelWindow.preimage_eq {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I) :
    h ⁻¹' (I : Set ℝ) = {v | h v = c} := by
  ext v
  constructor
  · exact hI.2 v
  · intro hv
    show h v ∈ I
    rw [show h v = c from hv]
    exact hI.1

/-! The finite height set is closed, so its complement supplies a level window. -/

/-- There is a positive open interval around every real number containing no other height in a
finite vertex-height family. -/
theorem exists_isLevelWindow [Finite V] (c : ℝ) :
    ∃ η : ℝ, 0 < η ∧ IsLevelWindow h c (ioo (c - η) (c + η)) := by
  let A : Set ℝ := {x | ∃ v, h v = x ∧ h v ≠ c}
  have hA : A.Finite := (Set.finite_range h).subset (by
    intro x hx
    rcases hx with ⟨v, hv, _⟩
    exact ⟨v, hv⟩)
  have hcA : c ∉ A := by
    intro hc
    rcases hc with ⟨v, hv, hne⟩
    exact hne hv
  have hopen : IsOpen Aᶜ := hA.isClosed.isOpen_compl
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen c hcA
  refine ⟨η, hη, ?_⟩
  unfold IsLevelWindow
  constructor
  · rw [mem_ioo]
    constructor <;> linarith
  · intro v hv
    by_contra hne
    have hb : h v ∈ Metric.ball c η := by
      rw [Real.ball_eq_Ioo]
      exact hv
    exact (hball hb) ⟨v, rfl, hne⟩

/-! ## Inclusion and window classification -/

/-- The inclusion of the closed level into the inverse image of a containing interval. -/
def levelInclusion {c : ℝ} {I : OpenInterval} (hc : c ∈ I) :
    C(ClosedLevel G h c, {p : Realization G // plHeight G h p ∈ I}) :=
  TDA.Topology.preimageSetInclusion (plHeight G h) (Set.singleton_subset_iff.2 hc)

/-- The path-component classification over a level window. -/
def levelWindowEquiv {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I) :
    (intervalComponents (plHeight G h)).obj I ≃ LevelVertex G h c :=
  (preimageComponentsEquiv G h I).trans ((cellComponentsEquivSum G h I).trans
    (Equiv.sumCongr (induceComponentsEquivOfEq G (IsLevelWindow.preimage_eq h hI))
      (uncoveredEdgeEquivCrossesOfLevel G h hI.1 fun _ hv => hI.2 _ hv)))

private theorem levelWindowEquiv_apply {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I)
    (x : (intervalComponents (plHeight G h)).obj I) :
    levelWindowEquiv G h hI x =
      Equiv.sumCongr (induceComponentsEquivOfEq G (IsLevelWindow.preimage_eq h hI))
        (uncoveredEdgeEquivCrossesOfLevel G h hI.1 fun _ hv => hI.2 _ hv)
        (cellComponentsEquivSum G h I (preimageComponentsEquiv G h I x)) := rfl

private theorem levelWindowEquiv_componentMap_mk {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I) (x : ClosedLevel G h c) :
    levelWindowEquiv G h hI
        (TDA.Topology.componentMap (levelInclusion G h hI.1) (ZerothHomotopy.mk x)) =
      levelWindowEquiv G h hI
        (ZerothHomotopy.mk (⟨x.1, (levelInclusion G h hI.1 x).2⟩ :
          {p : Realization G // plHeight G h p ∈ I})) := rfl

/-- The star classification is the level-window classification for the star interval. -/
theorem graphPLStarEquiv_eq_levelWindowEquiv {n : ℕ} (S : CriticalValues n)
    (hS : CoversVertexHeights S h) (i : Fin (n + 1)) :
    graphPLStarEquiv G h S hS i =
      levelWindowEquiv G h
        (c := S.value i) (I := S.J i)
        ⟨S.value_mem_J i, fun _ hv => hS.eq_of_mem_J hv⟩ := by
  rfl

/-- A level vertex maps to the induced component of its representative vertex. -/
theorem levelWindowEquiv_mk_vertex {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I) (v : V) (hv : h v = c) :
    levelWindowEquiv G h hI
        (ZerothHomotopy.mk (⟨vertex G v, by rw [plHeight_vertex, hv]; exact hI.1⟩ :
          {p : Realization G // plHeight G h p ∈ I})) =
      Sum.inl ((G.induce {v | h v = c}).connectedComponentMk ⟨v, hv⟩) := by
  refine (levelWindowEquiv_apply G h hI _).trans ?_
  exact congrArg (fun c => Equiv.sumCongr
    (induceComponentsEquivOfEq G (IsLevelWindow.preimage_eq h hI))
    (uncoveredEdgeEquivCrossesOfLevel G h hI.1 fun _ hv => hI.2 _ hv)
    (cellComponentsEquivSum G h I c))
    (preimageComponentsEquiv_mk_vertex G h I v (by rw [hv]; exact hI.1))

private theorem levelWindowEquiv_cell_inr {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I)
    (e : {e : G.edgeSet // EdgeActive G h I e})
    (hx : (∀ v ∈ (e.1 : Sym2 V), h v ≠ c) → EdgeCrosses G h c e.1) :
    levelWindowEquiv G h hI ((preimageComponentsEquiv G h I).symm
        ((cellGraph G h I).connectedComponentMk (Sum.inr e))) =
      levelEnd G h c e.1 hx := by
  refine (levelWindowEquiv_apply G h hI _).trans ?_
  rw [Equiv.apply_symm_apply]
  by_cases hw : ∃ w ∈ (e.1 : Sym2 V), h w = c
  · obtain ⟨w, hw, hwc⟩ := hw
    have hwI : h w ∈ I := by
      rw [hwc]
      exact hI.1
    rw [cellComponentsEquivSum_inr_of_mem G h I e (w := ⟨w, hwI⟩) hw,
      levelEnd_of_mem G h hx hw hwc]
    rfl
  · replace hw : ∀ w ∈ (e.1 : Sym2 V), h w ≠ c := fun w hw' hwc => hw ⟨w, hw', hwc⟩
    have hunc : ∀ v ∈ (e.1 : Sym2 V), h v ∉ I := fun v hv hvI =>
      hw v hv (hI.2 v hvI)
    rw [cellComponentsEquivSum_inr_uncovered G h I ⟨e.1, e.2, hunc⟩,
      levelEnd_of_forall_ne G h hx hw]
    rfl

/-- An edge point in a level window maps to the endpoint or crossing label of its edge. -/
theorem levelWindowEquiv_mk_edgePoint {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I) (d : G.Dart) (t : unitInterval)
    (ht : dartHeight h d t ∈ I)
    (hx : (∀ v ∈ (dartEdge d : Sym2 V), h v ≠ c) →
      EdgeCrosses G h c (dartEdge d)) :
    levelWindowEquiv G h hI
        (ZerothHomotopy.mk (⟨edgePoint G d t, ht⟩ :
          {p : Realization G // plHeight G h p ∈ I})) =
      levelEnd G h c (dartEdge d) hx := by
  have key := levelWindowEquiv_cell_inr G h hI
    ⟨dartEdge d, edgeActive_dartEdge_of_mem ht⟩ hx
  rw [← preimageComponentsEquiv_mk_edgePoint G h I d t ht, Equiv.symm_apply_apply] at key
  exact key

/-! ## Crossing points -/

/-- The parameter at which an upward-oriented dart reaches the level `c`. -/
def crossingParam {c : ℝ} {d : G.Dart} (h₁ : h d.fst < c) (h₂ : c < h d.snd) :
    unitInterval :=
  ⟨(c - h d.fst) / (h d.snd - h d.fst), by
    have hden : 0 < h d.snd - h d.fst := by linarith
    exact div_nonneg (by linarith) hden.le, by
    have hden : 0 < h d.snd - h d.fst := by linarith
    exact (div_le_one hden).2 (by linarith)⟩

/-- The crossing parameter has height exactly `c`. -/
theorem dartHeight_crossingParam {c : ℝ} {d : G.Dart}
    (h₁ : h d.fst < c) (h₂ : c < h d.snd) :
    dartHeight h d (crossingParam G h h₁ h₂) = c := by
  have hden : 0 < h d.snd - h d.fst := by linarith
  have hmul : (c - h d.fst) / (h d.snd - h d.fst) *
      (h d.snd - h d.fst) = c - h d.fst :=
    div_mul_cancel₀ _ hden.ne'
  show (1 - ((c - h d.fst) / (h d.snd - h d.fst))) * h d.fst +
      ((c - h d.fst) / (h d.snd - h d.fst)) * h d.snd = c
  linear_combination hmul

private theorem exists_dart_crossing {c : ℝ}
    (e : {e : G.edgeSet // EdgeCrosses G h c e}) :
    ∃ d : G.Dart, dartEdge d = e.1 ∧ h d.fst < c ∧ c < h d.snd := by
  obtain ⟨d, hd⟩ := exists_dartEdge_eq e.1
  have hcross : EdgeCrosses G h c (dartEdge d) := by
    rw [hd]
    exact e.2
  obtain ⟨hmin, hmax⟩ := (edgeCrosses_dartEdge_iff d).1 hcross
  rcases le_total (h d.fst) (h d.snd) with hab | hab
  · refine ⟨d, hd, ?_, ?_⟩
    · rw [min_eq_left hab] at hmin
      exact hmin
    · rw [max_eq_right hab] at hmax
      exact hmax
  · refine ⟨d.symm, ?_, ?_, ?_⟩
    · rw [dartEdge_symm]
      exact hd
    · rw [min_eq_right hab] at hmin
      exact hmin
    · rw [max_eq_left hab] at hmax
      exact hmax

/-- The unique interior point where a crossing edge meets the closed level. -/
def crossingPoint {c : ℝ} (e : {e // EdgeCrosses G h c e}) : ClosedLevel G h c :=
  let hex := exists_dart_crossing G h e
  let d := Classical.choose hex
  have hd := Classical.choose_spec hex
  ⟨edgePoint G d (crossingParam G h hd.2.1 hd.2.2), by
    change plHeight G h (edgePoint G d (crossingParam G h hd.2.1 hd.2.2)) = c
    rw [plHeight_edgePoint, dartHeight_crossingParam]⟩

private theorem crossingPoint_spec {c : ℝ} (e : {e // EdgeCrosses G h c e}) :
    ∃ d : G.Dart, ∃ h₁ : h d.fst < c, ∃ h₂ : c < h d.snd,
      dartEdge d = e.1 ∧
        (crossingPoint G h e).1 = edgePoint G d (crossingParam G h h₁ h₂) := by
  let hex := exists_dart_crossing G h e
  let d := Classical.choose hex
  have hd := Classical.choose_spec hex
  refine ⟨d, hd.2.1, hd.2.2, hd.1, ?_⟩
  rfl

private theorem eq_of_dartHeight_eq {d : G.Dart} {s t : unitInterval}
    (hne : h d.fst ≠ h d.snd) (hst : dartHeight h d s = dartHeight h d t) : s = t := by
  apply Subtype.ext
  apply mul_right_cancel₀ (sub_ne_zero.mpr hne.symm)
  unfold dartHeight at hst
  linear_combination hst

/-- Every point of a crossing edge in the closed level is its crossing point. -/
theorem eq_crossingPoint {c : ℝ} (e : {e // EdgeCrosses G h c e}) (d : G.Dart)
    (hd : dartEdge d = e.1) (t : unitInterval) (ht : dartHeight h d t = c) :
    edgePoint G d t = (crossingPoint G h e).1 := by
  obtain ⟨d', h₁, h₂, hd', hcp⟩ := crossingPoint_spec G h e
  have hne : h d'.fst ≠ h d'.snd := by linarith
  have hdd : dartEdge d = dartEdge d' := hd.trans hd'.symm
  rcases dartEdge_eq_iff.1 hdd with hdd' | hdd'
  · have ht' : dartHeight h d' t = c := by
      simpa [hdd'] using ht
    have hts := eq_of_dartHeight_eq G h hne
      (ht'.trans (dartHeight_crossingParam G h h₁ h₂).symm)
    calc
      edgePoint G d t = edgePoint G d' t := by rw [hdd']
      _ = edgePoint G d' (crossingParam G h h₁ h₂) :=
        congrArg (edgePoint G d') hts
      _ = (crossingPoint G h e).1 := hcp.symm
  · have ht'' : dartHeight h d'.symm t = c := by
      simpa [hdd'] using ht
    have ht' : dartHeight h d' (unitInterval.symm t) = c := by
      have hsymm := dartHeight_symm h d' (unitInterval.symm t)
      rw [unitInterval.symm_symm] at hsymm
      exact hsymm.symm.trans ht''
    have hts := eq_of_dartHeight_eq G h hne
      (ht'.trans (dartHeight_crossingParam G h h₁ h₂).symm)
    calc
      edgePoint G d t = edgePoint G d'.symm t := by rw [hdd']
      _ = edgePoint G d' (unitInterval.symm t) := by
        have hsymm := edgePoint_symm G d' (unitInterval.symm t)
        simpa using hsymm
      _ = edgePoint G d' (crossingParam G h h₁ h₂) := congrArg (edgePoint G d') hts
      _ = (crossingPoint G h e).1 := hcp.symm

/-! ## Horizontal edges -/

/-- A horizontal dart joins every point of its level edge to its first endpoint inside the level. -/
theorem joinedIn_level_of_eq {c : ℝ} {d : G.Dart}
    (hd₁ : h d.fst = c) (hd₂ : h d.snd = c) (t : unitInterval) :
    JoinedIn (plHeight G h ⁻¹' {c}) (vertex G d.fst) (edgePoint G d t) := by
  refine ⟨{
      toFun := fun s => edgePoint G d (s * t)
      continuous_toFun := (continuous_edgePoint G d).comp
        (Continuous.subtype_mk (continuous_subtype_val.mul continuous_const)
          (fun s => unitInterval.mul_mem s.2 t.2))
      source' := by simp [edgePoint_zero]
      target' := by simp
    }, ?_⟩
  intro s
  change plHeight G h (edgePoint G d (s * t)) = c
  rw [plHeight_edgePoint, dartHeight_of_eq h (hd₁.trans hd₂.symm), hd₁]

/-! ## Closed-level components -/

/- The adjacency argument below is deliberately expressed through `eq_of_walk`: the
   hypothesis of `ConnectedComponent.lift` is path-based in the pinned mathlib. -/

private def closedLevelVertexPoint {c : ℝ} :
    (G.induce {v | h v = c}).ConnectedComponent →
      ZerothHomotopy (ClosedLevel G h c) :=
  ConnectedComponent.lift
    (fun v : {v : V // h v = c} =>
      ZerothHomotopy.mk
        (⟨vertex G v.1, by
          change h v.1 = c
          exact v.2⟩ : ClosedLevel G h c))
    (fun (v w : {v : V // h v = c})
        (p : (G.induce {v | h v = c}).Walk v w) _ =>
      eq_of_walk
        (f := fun v : {v : V // h v = c} =>
          ZerothHomotopy.mk
            (⟨vertex G v.1, by
              change h v.1 = c
              exact v.2⟩ : ClosedLevel G h c))
        (fun (v w : {v : V // h v = c})
            (hvw : (G.induce {v | h v = c}).Adj v w) => by
          let d : G.Dart := ⟨(v.1, w.1), induce_adj.mp hvw⟩
          have hd₁ : h d.fst = c := v.2
          have hd₂ : h d.snd = c := w.2
          have hj := TDA.Topology.mk_eq_of_joinedIn (plHeight G h) ({c} : Set ℝ)
            (joinedIn_level_of_eq G h hd₁ hd₂ (1 : unitInterval))
            (by rw [plHeight_vertex]; exact hd₁)
            (by rw [plHeight_edgePoint, dartHeight_one]; exact hd₂)
          have hend : edgePoint G d 1 = vertex G w.1 := by
            rw [edgePoint_one]
          have hend' :
              (⟨edgePoint G d 1, by
                rw [plHeight_edgePoint, dartHeight_one]
                exact hd₂⟩ : ClosedLevel G h c) =
              (⟨vertex G w.1, by
                rw [plHeight_vertex]
                exact hd₂⟩ : ClosedLevel G h c) := by
            apply Subtype.ext
            exact hend
          exact hj.trans (congrArg
            (fun z : ClosedLevel G h c => ZerothHomotopy.mk z) hend')) p)

/-- The point of a level vertex represented as a path component of the closed level. -/
def closedLevelPoint (c : ℝ) : LevelVertex G h c → ZerothHomotopy (ClosedLevel G h c) :=
  Sum.elim (closedLevelVertexPoint G h)
    (fun e =>
      (ZerothHomotopy.mk (crossingPoint G h e) : ZerothHomotopy (ClosedLevel G h c)))

private theorem closedLevelPoint_inr {c : ℝ}
    (e : {e : G.edgeSet // EdgeCrosses G h c e}) :
    closedLevelPoint G h c (Sum.inr e) =
      (ZerothHomotopy.mk (crossingPoint G h e) : ZerothHomotopy (ClosedLevel G h c)) := rfl

private theorem closedLevelPoint_inl_mk {c : ℝ} (v : {v : V | h v = c}) :
    closedLevelPoint G h c (Sum.inl ((G.induce {v | h v = c}).connectedComponentMk v)) =
      ZerothHomotopy.mk (⟨vertex G v.1, by
        change h v.1 = c
        exact v.2⟩ : ClosedLevel G h c) := rfl

private theorem levelWindow_closedLevelPoint {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I) (y : LevelVertex G h c) :
    levelWindowEquiv G h hI
        (TDA.Topology.componentMap (levelInclusion G h hI.1)
          (closedLevelPoint G h c y)) = y := by
  rcases y with y | y
  · induction y using ConnectedComponent.ind with
    | h v =>
      rw [closedLevelPoint_inl_mk G h v, levelWindowEquiv_componentMap_mk G h hI,
        levelWindowEquiv_mk_vertex G h hI v.1 v.2]
  · obtain ⟨d, h₁, h₂, hd, hpoint⟩ := crossingPoint_spec G h y
    have hne : ∀ v ∈ (dartEdge d : Sym2 V), h v ≠ c := by
      intro v hv
      rcases mem_dartEdge.1 hv with rfl | rfl
      · exact h₁.ne
      · exact h₂.ne'
    let hx : (∀ v ∈ (dartEdge d : Sym2 V), h v ≠ c) →
        EdgeCrosses G h c (dartEdge d) := fun _ => by
      rw [hd]
      exact y.2
    have ht : dartHeight h d (crossingParam G h h₁ h₂) ∈ I := by
      rw [dartHeight_crossingParam G h h₁ h₂]
      exact hI.1
    rw [closedLevelPoint_inr G h y, levelWindowEquiv_componentMap_mk G h hI]
    have hmk : (⟨(crossingPoint G h y).1,
          (levelInclusion G h hI.1 (crossingPoint G h y)).2⟩ :
          {p : Realization G // plHeight G h p ∈ I}) =
        ⟨edgePoint G d (crossingParam G h h₁ h₂), ht⟩ := Subtype.ext hpoint
    rw [hmk, levelWindowEquiv_mk_edgePoint G h hI d (crossingParam G h h₁ h₂) ht hx,
      levelEnd_of_forall_ne G h hx hne]
    exact congrArg Sum.inr (Subtype.ext hd)

private theorem closedLevelPoint_levelWindow {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I) (x : ZerothHomotopy (ClosedLevel G h c)) :
    closedLevelPoint G h c
        (levelWindowEquiv G h hI
          (TDA.Topology.componentMap (levelInclusion G h hI.1) x)) = x := by
  induction x using ZerothHomotopy.rec with
  | mk x =>
    obtain ⟨p, hp⟩ := x
    change plHeight G h p = c at hp
    induction p using ind G with
    | vertex v =>
      have hv : h v = c := by simpa [plHeight_vertex] using hp
      rw [levelWindowEquiv_componentMap_mk G h hI,
        levelWindowEquiv_mk_vertex G h hI v hv]
      change ZerothHomotopy.mk (⟨vertex G v, _⟩ : ClosedLevel G h c) =
        ZerothHomotopy.mk (⟨vertex G v, hp⟩ : ClosedLevel G h c)
      congr 1
    | edgePoint d t =>
      have ht : dartHeight h d t = c := by
        simpa [plHeight_edgePoint] using hp
      by_cases hfst : h d.fst = c
      · by_cases hsnd : h d.snd = c
        · have hx : (∀ v ∈ (dartEdge d : Sym2 V), h v ≠ c) →
              EdgeCrosses G h c (dartEdge d) := by
            intro hne
            exact (hne d.fst (fst_mem_dartEdge d) hfst).elim
          have htI : dartHeight h d t ∈ I := by
            rw [ht]
            exact hI.1
          rw [levelWindowEquiv_componentMap_mk G h hI,
            levelWindowEquiv_mk_edgePoint G h hI d t htI hx,
            levelEnd_of_mem G h hx (fst_mem_dartEdge d) hfst]
          change ZerothHomotopy.mk (⟨vertex G d.fst, _⟩ : ClosedLevel G h c) =
            ZerothHomotopy.mk (⟨edgePoint G d t, hp⟩ : ClosedLevel G h c)
          exact TDA.Topology.mk_eq_of_joinedIn (plHeight G h) ({c} : Set ℝ)
            (joinedIn_level_of_eq G h hfst hsnd t)
            (by rw [plHeight_vertex]; exact hfst) hp
        · have hne : h d.fst ≠ h d.snd := by
            intro heq
            exact hsnd (heq.symm.trans hfst)
          have ht0 : t = 0 := eq_of_dartHeight_eq G h hne (by
            rw [dartHeight_zero]
            exact ht.trans hfst.symm)
          have hxval : (⟨edgePoint G d t, hp⟩ : ClosedLevel G h c) =
              (⟨vertex G d.fst, by rw [plHeight_vertex]; exact hfst⟩ : ClosedLevel G h c) := by
            apply Subtype.ext
            calc
              edgePoint G d t = edgePoint G d 0 := congrArg (edgePoint G d) ht0
              _ = vertex G d.fst := edgePoint_zero G d
          rw [hxval, levelWindowEquiv_componentMap_mk G h hI,
            levelWindowEquiv_mk_vertex G h hI d.fst hfst]
          rfl
      · by_cases hsnd : h d.snd = c
        · have hne : h d.fst ≠ h d.snd := by
            intro heq
            exact hfst (heq.trans hsnd)
          have ht1 : t = 1 := eq_of_dartHeight_eq G h hne (by
            rw [dartHeight_one]
            exact ht.trans hsnd.symm)
          have hxval : (⟨edgePoint G d t, hp⟩ : ClosedLevel G h c) =
              (⟨vertex G d.snd, by rw [plHeight_vertex]; exact hsnd⟩ : ClosedLevel G h c) := by
            apply Subtype.ext
            calc
              edgePoint G d t = edgePoint G d 1 := congrArg (edgePoint G d) ht1
              _ = vertex G d.snd := edgePoint_one G d
          rw [hxval, levelWindowEquiv_componentMap_mk G h hI,
            levelWindowEquiv_mk_vertex G h hI d.snd hsnd]
          rfl
        · have hne : ∀ v ∈ (dartEdge d : Sym2 V), h v ≠ c := by
            intro v hv
            rcases mem_dartEdge.1 hv with rfl | rfl
            · exact hfst
            · exact hsnd
          have hcross : EdgeCrosses G h c (dartEdge d) := by
            rw [edgeCrosses_dartEdge_iff]
            rcases le_total (h d.fst) (h d.snd) with hab | hab
            · rw [min_eq_left hab, max_eq_right hab]
              have hleft : h d.fst ≤ c := by
                rw [← ht]
                unfold dartHeight
                nlinarith [t.2.1, t.2.2,
                  mul_nonneg t.2.1 (sub_nonneg.2 hab),
                  mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hab)]
              have hright : c ≤ h d.snd := by
                rw [← ht]
                unfold dartHeight
                nlinarith [t.2.1, t.2.2,
                  mul_nonneg t.2.1 (sub_nonneg.2 hab),
                  mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hab)]
              exact ⟨lt_of_le_of_ne hleft hfst, lt_of_le_of_ne hright (Ne.symm hsnd)⟩
            · rw [min_eq_right hab, max_eq_left hab]
              have hleft : h d.snd ≤ c := by
                rw [← ht]
                unfold dartHeight
                nlinarith [t.2.1, t.2.2,
                  mul_nonneg t.2.1 (sub_nonneg.2 hab),
                  mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hab)]
              have hright : c ≤ h d.fst := by
                rw [← ht]
                unfold dartHeight
                nlinarith [t.2.1, t.2.2,
                  mul_nonneg t.2.1 (sub_nonneg.2 hab),
                  mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hab)]
              exact ⟨lt_of_le_of_ne hleft hsnd, lt_of_le_of_ne hright (Ne.symm hfst)⟩
          let hx : (∀ v ∈ (dartEdge d : Sym2 V), h v ≠ c) →
              EdgeCrosses G h c (dartEdge d) := fun _ => hcross
          have htI : dartHeight h d t ∈ I := by
            rw [ht]
            exact hI.1
          rw [levelWindowEquiv_componentMap_mk G h hI,
            levelWindowEquiv_mk_edgePoint G h hI d t htI hx,
            levelEnd_of_forall_ne G h hx hne]
          change ZerothHomotopy.mk
              (crossingPoint G h ⟨dartEdge d, hcross⟩) =
                ZerothHomotopy.mk (⟨edgePoint G d t, hp⟩ : ClosedLevel G h c)
          exact congrArg ZerothHomotopy.mk (Subtype.ext
            ((eq_crossingPoint G h ⟨dartEdge d, hcross⟩ d rfl t ht).symm))

/-- The path components of a finite closed level are classified by `LevelVertex`. -/
def closedLevelComponentsEquiv [Finite V] (c : ℝ) :
    ZerothHomotopy (ClosedLevel G h c) ≃ LevelVertex G h c :=
  let hI := (exists_isLevelWindow h c).choose_spec.2
  { toFun := levelWindowEquiv G h hI ∘
      TDA.Topology.componentMap (levelInclusion G h hI.1)
    invFun := closedLevelPoint G h c
    left_inv := closedLevelPoint_levelWindow G h hI
    right_inv := levelWindow_closedLevelPoint G h hI }

private theorem closedLevelComponentsEquiv_symm_apply [Finite V] (c : ℝ)
    (y : LevelVertex G h c) :
    (closedLevelComponentsEquiv G h c).symm y = closedLevelPoint G h c y := rfl

/-- Any level window gives the same closed-level component classification map. -/
theorem closedLevelComponentsEquiv_eq [Finite V] {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I) (x : ZerothHomotopy (ClosedLevel G h c)) :
    closedLevelComponentsEquiv G h c x =
      levelWindowEquiv G h hI
        (TDA.Topology.componentMap (levelInclusion G h hI.1) x) := by
  let hI₀ : IsLevelWindow h c
      (ioo (c - (exists_isLevelWindow h c).choose)
        (c + (exists_isLevelWindow h c).choose)) :=
    (exists_isLevelWindow h c).choose_spec.2
  have hsurj : Function.Surjective (closedLevelPoint G h c) := by
    intro z
    refine ⟨closedLevelComponentsEquiv G h c z, ?_⟩
    change closedLevelPoint G h c
      (levelWindowEquiv G h hI₀
        (TDA.Topology.componentMap (levelInclusion G h hI₀.1) z)) = z
    exact closedLevelPoint_levelWindow G h hI₀ z
  obtain ⟨y, rfl⟩ := hsurj x
  calc
    closedLevelComponentsEquiv G h c (closedLevelPoint G h c y) = y :=
      by
        rw [← closedLevelComponentsEquiv_symm_apply G h c y]
        exact (closedLevelComponentsEquiv G h c).apply_symm_apply y
    _ = levelWindowEquiv G h hI
        (TDA.Topology.componentMap (levelInclusion G h hI.1)
          (closedLevelPoint G h c y)) :=
      (levelWindow_closedLevelPoint G h hI y).symm

/-- The closed-level class of a vertex is its induced level-graph component. -/
theorem closedLevelComponentsEquiv_mk_vertex [Finite V] {c : ℝ} (v : V) (hv : h v = c) :
    closedLevelComponentsEquiv G h c
      (ZerothHomotopy.mk
          (⟨vertex G v, by
            rw [plHeight_vertex, hv]
            exact Set.mem_singleton c⟩ : ClosedLevel G h c)) =
      Sum.inl ((G.induce {v | h v = c}).connectedComponentMk ⟨v, hv⟩) := by
  let hI := (exists_isLevelWindow h c).choose_spec.2
  rw [closedLevelComponentsEquiv_eq G h hI,
    levelWindowEquiv_componentMap_mk G h hI,
    levelWindowEquiv_mk_vertex G h hI v hv]

/-- The closed-level class of a crossing point is its crossing-edge component. -/
theorem closedLevelComponentsEquiv_crossingPoint [Finite V] {c : ℝ}
    (e : {e : G.edgeSet // EdgeCrosses G h c e}) :
    closedLevelComponentsEquiv G h c
        (ZerothHomotopy.mk (crossingPoint G h e)) = Sum.inr e := by
  rw [← closedLevelPoint_inr G h e]
  exact (closedLevelComponentsEquiv G h c).apply_symm_apply (Sum.inr e)

/-- The level-window classification triangle commutes with the canonical classification. -/
theorem levelWindowEquiv_comp_componentMap_levelInclusion [Finite V] {c : ℝ}
    {I : OpenInterval} (hI : IsLevelWindow h c I) :
    levelWindowEquiv G h hI ∘
        TDA.Topology.componentMap (levelInclusion G h hI.1) =
      closedLevelComponentsEquiv G h c := by
  funext x
  exact (closedLevelComponentsEquiv_eq G h hI x).symm

/-- Inclusion into any level window is bijective on path components. -/
theorem componentMap_levelInclusion_bijective [Finite V] {c : ℝ} {I : OpenInterval}
    (hI : IsLevelWindow h c I) :
    Function.Bijective
      (TDA.Topology.componentMap (levelInclusion G h hI.1)) := by
  have heq :
      TDA.Topology.componentMap (levelInclusion G h hI.1) =
        (levelWindowEquiv G h hI).symm ∘ closedLevelComponentsEquiv G h c := by
    funext x
    apply (levelWindowEquiv G h hI).injective
    rw [Function.comp_apply, Equiv.apply_symm_apply]
    exact congrFun (levelWindowEquiv_comp_componentMap_levelInclusion G h hI) x
  rw [heq]
  exact (levelWindowEquiv G h hI).symm.bijective.comp
    (closedLevelComponentsEquiv G h c).bijective

/-- The finite Reeb-data vertex type is equivalent to the corresponding closed-level components. -/
def graphPLReebDataVEquivClosedLevel [Finite V] {n : ℕ} (S : CriticalValues n)
    (i : Fin (n + 1)) :
    (graphPLReebData G h S).V i ≃
      ZerothHomotopy (ClosedLevel G h (S.value i)) :=
  (closedLevelComponentsEquiv G h (S.value i)).symm

/-- Under vertex-height covering, the star classification factors through the closed-level
components classification. -/
theorem graphPLStarEquiv_comp_componentMap_levelInclusion [Finite V] {n : ℕ}
    (S : CriticalValues n) (hS : CoversVertexHeights S h) (i : Fin (n + 1)) :
    graphPLStarEquiv G h S hS i ∘
        TDA.Topology.componentMap
          (levelInclusion G h (S.value_mem_J i)) =
      closedLevelComponentsEquiv G h (S.value i) := by
  rw [graphPLStarEquiv_eq_levelWindowEquiv G h S hS i]
  exact levelWindowEquiv_comp_componentMap_levelInclusion G h
    ⟨S.value_mem_J i, fun _ hv => hS.eq_of_mem_J hv⟩

end
end TDA.Mapper.GraphPL
