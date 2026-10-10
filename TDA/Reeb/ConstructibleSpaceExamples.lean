import TDA.Reeb.ConstructibleSpace
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Realization fixtures

Fixtures for `TDA.Reeb.CylinderPresentation`. Every statement is about the actual quotient
`Realization`, mostly at the two levels `S01 = {0, 1}` with the regular height `1/2`.

* `n = 0`: every presentation realizes `V 0` at the single height (`homeomorphZero`,
  `height_zero`).
* All pieces empty: the realization is empty (`emptyData_isEmpty`).
* Missing edges: with a point at each level and no edge, the realization is not preconnected,
  by the intermediate value theorem for the height (`gapData_not_preconnected`).
* Empty vertex piece: it forces the adjacent edge piece empty (`isEmpty_E_zero`), and no point
  lies over `[a e, a (e+1))` (`height_preimage_Ico_eq_empty`); for concrete data with `V 0`
  empty, the critical fiber at `0` is empty (`leftEmpty_criticalFiber_isEmpty`).
* Noninjective attachment: a two-point edge piece with a constant left endpoint map. The two
  bottom ends are identified, so the closed cylinder does not embed
  (`pinch_ofCylinder_not_injective`), while the top ends and the regular points stay apart.
* Parallel edges: two edges between the same pair of vertices give a regular fiber with two
  points (`parallel_regularFiber_card`).
* Disconnected realization: two disjoint segments, separated by a continuous label obtained from
  the universal property (`twoSeg_not_preconnected`).
* Exterior heights: the fibers below `0` and above `1` are empty (`pinch_fiber_lowerTail`,
  `pinch_fiber_upperTail`).
-/

open Set Topology

universe u

namespace TDA.Reeb.Examples.Cylinder

noncomputable section

open TDA.Reeb CylinderPresentation

/-- Levels `0 < 1`. -/
def S01 : CriticalValues 1 where
  value i := ((i : ℕ) : ℝ)
  strictMono _ _ h := Nat.cast_lt.2 h

@[simp] theorem S01_value_zero : S01.value 0 = 0 := by simp [S01]
@[simp] theorem S01_value_one : S01.value 1 = 1 := by simp [S01]

/-- The regular height `1/2` of the single gap. -/
def half : (S01.K 0 : Set ℝ) := ⟨1 / 2, by
  show S01.value (Fin.castSucc 0) < 1 / 2 ∧ 1 / 2 < S01.value (Fin.succ 0)
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
  norm_num⟩

/-! ### `n = 0`: the realization is `V 0` at the single height -/

theorem ofVertex_surjective_zero (S : CriticalValues 0) (P : CylinderPresentation.{u} 0) :
    Function.Surjective (P.ofVertex S 0) := by
  intro q
  rcases P.exists_rep S q with ⟨i, v, rfl⟩ | ⟨e, -, -⟩
  · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact ⟨v, rfl⟩
  · exact e.elim0

/-- For `n = 0` the realization is homeomorphic to the single vertex piece. -/
def homeomorphZero (S : CriticalValues 0) (P : CylinderPresentation.{u} 0) :
    P.V 0 ≃ₜ P.Realization S :=
  (P.isEmbedding_ofVertex S 0).toHomeomorphOfSurjective (ofVertex_surjective_zero S P)

theorem height_zero (S : CriticalValues 0) (P : CylinderPresentation.{u} 0)
    (q : P.Realization S) : P.height S q = S.value 0 := by
  obtain ⟨v, rfl⟩ := ofVertex_surjective_zero S P q
  rfl

/-! ### All pieces empty -/

/-- Finite data with all pieces empty. -/
def emptyData (n : ℕ) : FiniteReebData.{0} n :=
  ⟨fun _ => Empty, fun _ => Empty, fun _ => inferInstance, fun _ => inferInstance,
    fun _ x => x.elim, fun _ x => x.elim⟩

instance emptyData_isEmpty_V (n : ℕ) (i : Fin (n + 1)) :
    IsEmpty ((ofFiniteData (emptyData n)).V i) :=
  inferInstanceAs (IsEmpty Empty)

theorem emptyData_isEmpty (n : ℕ) (S : CriticalValues n) :
    IsEmpty ((ofFiniteData (emptyData n)).Realization S) :=
  (ofFiniteData (emptyData n)).isEmpty_realization S

/-! ### Missing edges separate adjacent levels -/

/-- A point at each of two levels and no edge. -/
def gapData : FiniteReebData.{0} 1 :=
  ⟨fun _ => Unit, fun _ => Empty, fun _ => inferInstance, fun _ => inferInstance,
    fun _ x => x.elim, fun _ x => x.elim⟩

theorem gapData_not_preconnected :
    ¬ PreconnectedSpace ((ofFiniteData gapData).Realization S01) := by
  intro h
  have hpc := isPreconnected_range ((ofFiniteData gapData).height S01).continuous
  have h0 : (0 : ℝ) ∈ range ((ofFiniteData gapData).height S01) :=
    ⟨(ofFiniteData gapData).ofVertex S01 0 (show (ofFiniteData gapData).V 0 from ()),
      ((ofFiniteData gapData).height_ofVertex S01 0 _).trans S01_value_zero⟩
  have h1 : (1 : ℝ) ∈ range ((ofFiniteData gapData).height S01) :=
    ⟨(ofFiniteData gapData).ofVertex S01 1 (show (ofFiniteData gapData).V 1 from ()),
      ((ofFiniteData gapData).height_ofVertex S01 1 _).trans S01_value_one⟩
  obtain ⟨q, hq⟩ := hpc.Icc_subset h0 h1 (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num)
  rcases (ofFiniteData gapData).exists_rep S01 q with ⟨i, v, rfl⟩ | ⟨e, p, -⟩
  · rw [height_ofVertex] at hq
    fin_cases i <;> simp at hq
  · exact isEmptyElim (α := Empty) p.1

/-! ### An empty vertex piece -/

/-- An empty vertex piece forces the adjacent edge piece empty. -/
theorem isEmpty_E_zero (P : CylinderPresentation.{u} 1) (h : IsEmpty (P.V 0)) :
    IsEmpty (P.E 0) :=
  P.isEmpty_E_of_left (e := 0) h

/-- Quotient-level companion: if `V e.castSucc` is empty, the realization has no point with
height in `[a e, a (e+1))`. -/
theorem height_preimage_Ico_eq_empty {n : ℕ} (S : CriticalValues n)
    (P : CylinderPresentation.{u} n) (e : Fin n) (h : IsEmpty (P.V e.castSucc)) :
    P.height S ⁻¹' Ico (S.value e.castSucc) (S.value e.succ) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun q hq => ?_
  rcases P.exists_rep S q with ⟨i, v, rfl⟩ | ⟨e', p, rfl⟩
  · have hq : S.value i ∈ Ico (S.value e.castSucc) (S.value e.succ) := hq
    have h₁ : e.castSucc ≤ i := S.strictMono.le_iff_le.1 hq.1
    have h₂ : i < e.succ := S.strictMono.lt_iff_lt.1 hq.2
    obtain rfl : i = e.castSucc := le_antisymm (Fin.le_castSucc_iff.2 h₂) h₁
    exact h.false v
  · have hq : (p.2 : ℝ) ∈ Ico (S.value e.castSucc) (S.value e.succ) := hq
    obtain rfl : e' = e := S.eq_of_mem_K_of_mem_Icc p.2.2 ⟨hq.1, hq.2.le⟩
    exact (P.isEmpty_E_of_left h).false p.1

/-- Concrete data: `V 0` empty, `V 1` a point, no edges. -/
def leftEmptyData : FiniteReebData.{0} 1 :=
  ⟨fun i => Fin i.val, fun _ => Empty, fun _ => inferInstance, fun _ => inferInstance,
    fun _ x => x.elim, fun _ x => x.elim⟩

theorem leftEmpty_preimage_Ico :
    (ofFiniteData leftEmptyData).height S01 ⁻¹'
      Ico (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) = ∅ :=
  height_preimage_Ico_eq_empty S01 (ofFiniteData leftEmptyData) 0
    (inferInstanceAs (IsEmpty (Fin 0)))

theorem leftEmpty_criticalFiber_isEmpty :
    IsEmpty ((ofFiniteData leftEmptyData).height S01 ⁻¹' {S01.value 0}) :=
  ⟨fun q => (show IsEmpty ((ofFiniteData leftEmptyData).V 0) from
    inferInstanceAs (IsEmpty (Fin 0))).false
    (((ofFiniteData leftEmptyData).criticalFiberHomeomorph S01 0).symm q)⟩

/-! ### Noninjective attachment of a two-point edge piece to one vertex -/

/-- `V = Bool` at both levels and `E 0 = Bool`: both edges attach on the left to the single
vertex `false` (noninjective; the vertex `true` at level 0 is isolated), injectively on the
right. -/
def pinchData : FiniteReebData.{0} 1 :=
  ⟨fun _ => Bool, fun _ => Bool, fun _ => inferInstance, fun _ => inferInstance,
    fun _ _ => false, fun _ y => y⟩

/-- The presentation of `pinchData`. -/
abbrev pinch := ofFiniteData pinchData

theorem pinch_left_not_injective : ¬ Function.Injective (pinch.left 0) := fun h =>
  Bool.false_ne_true (h (a₁ := (false : pinchData.E 0)) (a₂ := true) rfl)

theorem pinch_bot_glued :
    pinch.ofCylinder S01 0 (false, segBot S01 0) = pinch.ofCylinder S01 0 (true, segBot S01 0) :=
  (pinch.ofCylinder_segBot S01 0 false).trans (pinch.ofCylinder_segBot S01 0 true).symm

/-- The closed cylinder does not embed: its two bottom ends are identified. -/
theorem pinch_ofCylinder_not_injective : ¬ Function.Injective (pinch.ofCylinder S01 0) :=
  fun h => Bool.false_ne_true (congrArg Prod.fst (h pinch_bot_glued))

theorem pinch_top_separate :
    pinch.ofCylinder S01 0 (false, segTop S01 0) ≠ pinch.ofCylinder S01 0 (true, segTop S01 0) :=
  fun h => Bool.false_ne_true (pinch.ofVertex_injective S01 _
    (((pinch.ofCylinder_segTop S01 0 false).symm.trans h).trans
      (pinch.ofCylinder_segTop S01 0 true)))

theorem pinch_regular_separate :
    pinch.ofStrip S01 0 (false, half) ≠ pinch.ofStrip S01 0 (true, half) := fun h =>
  Bool.false_ne_true (congrArg Prod.fst (pinch.ofStrip_injective S01 0 h))

/-! ### Exterior heights -/

theorem pinch_fiber_lowerTail : pinch.height S01 ⁻¹' {-1} = ∅ :=
  pinch.height_preimage_eq_empty_of_mem_lowerTail S01
    (S01.mem_lowerTail.2 (by rw [S01_value_zero]; norm_num))

theorem pinch_fiber_upperTail : pinch.height S01 ⁻¹' {2} = ∅ :=
  pinch.height_preimage_eq_empty_of_mem_upperTail S01
    (S01.mem_upperTail.2 (by rw [show Fin.last 1 = 1 from rfl, S01_value_one]; norm_num))

/-! ### Parallel edges are retained -/

/-- Two parallel edges between single vertices. -/
def parallelData : FiniteReebData.{0} 1 :=
  ⟨fun _ => Unit, fun _ => Bool, fun _ => inferInstance, fun _ => inferInstance,
    fun _ _ => (), fun _ _ => ()⟩

theorem parallel_regularFiber_card :
    Nat.card ((ofFiniteData parallelData).height S01 ⁻¹' {(half : ℝ)}) = 2 := by
  rw [← Nat.card_congr ((ofFiniteData parallelData).regularFiberHomeomorph S01 0 half).toEquiv]
  exact Nat.card_eq_two_iff' false |>.2 ⟨true, Bool.false_ne_true.symm, fun b hb => by
    cases b <;> simp_all⟩

theorem parallel_criticalFiber_subsingleton (i : Fin 2) :
    Subsingleton ((ofFiniteData parallelData).height S01 ⁻¹' {S01.value i}) :=
  have : Subsingleton ((ofFiniteData parallelData).V i) := inferInstanceAs (Subsingleton Unit)
  ((ofFiniteData parallelData).criticalFiberHomeomorph S01 i).symm.injective.subsingleton

/-! ### A disconnected realization: two disjoint segments -/

/-- Two disjoint segments. -/
def twoSegData : FiniteReebData.{0} 1 :=
  ⟨fun _ => Bool, fun _ => Bool, fun _ => inferInstance, fun _ => inferInstance,
    fun _ y => y, fun _ y => y⟩

/-- The component label, obtained from the universal property. -/
def twoSegLabel : C((ofFiniteData twoSegData).Realization S01, Bool) :=
  lift
    { vertex := fun i => ⟨fun v : (ofFiniteData twoSegData).V i => (v : Bool),
        continuous_of_discreteTopology⟩
      cylinder := fun e => ⟨fun p => (p.1 : Bool),
        (continuous_of_discreteTopology
          (f := fun y : (ofFiniteData twoSegData).E e => (y : Bool))).comp continuous_fst⟩
      segBot_eq := fun _ _ => rfl
      segTop_eq := fun _ _ => rfl }

theorem twoSeg_not_preconnected :
    ¬ PreconnectedSpace ((ofFiniteData twoSegData).Realization S01) := fun h =>
  Bool.false_ne_true (PreconnectedSpace.constant h twoSegLabel.continuous
    (x := (ofFiniteData twoSegData).ofVertex S01 0 false)
    (y := (ofFiniteData twoSegData).ofVertex S01 0 true))

end

end TDA.Reeb.Examples.Cylinder
