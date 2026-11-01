import TDA.Reeb.ThickeningConstructible
import TDA.Reeb.ConstructibleSpaceExamples
import TDA.Reeb.ThickeningWindowExamples

/-!
# Fixtures for constructibility of thickenings

Acceptance fixtures for `TDA.Reeb.ThickeningConstructible`.

* **Constant height.** For every compact locally path-connected `X` and every `c`, the space `X`
  at constant height `c` is constructible (`isConstructibleSpace_constOver`), and so is its
  thickening (`isConstructibleSpace_thickening_constOver`), whose shifted witness has the levels
  `c - ε` and `c + ε` (`range_shifted_single`).
* **A non-Hausdorff input.** The indiscrete two-point space `IndiscreteBool` is compact, locally
  path-connected and not Hausdorff. At constant height it is constructible, its thickening is
  constructible, the thickened space is not Hausdorff (`not_t2Space_thickening_indiscreteBool`),
  and no vertex piece of the thickening presentation is Hausdorff
  (`not_t2Space_shiftedThick_V_indiscreteBool`).
* **`ε = 0`.** The general theorem at `ε = 0`, and the same conclusion through `zeroIso`
  (`isConstructibleSpace_thickening_zero`, `isConstructibleSpace_thickening_zero_of_zeroIso`);
  the shifted witness at `ε = 0` has the levels of the input (`shiftedCount_single_zero`).
* **Empty input.** The empty space at a constant height is constructible, its thickening is
  constructible and empty (`isEmpty_thickening_empty`).
* **Duplicate shifted values.** For `S = {0, 2}` and `ε = 1`, the four values `-1, 1, 1, 3` merge
  to three levels (`shiftedCount_S02_one`), and the theorem applies to the segment over `S`
  (`isConstructibleSpace_thickening_seg_S02`).
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb.Examples.ThickeningConstructible

noncomputable section

open TDA.Reeb CylinderPresentation CriticalValues Thickening

/-! ### Constant height -/

/-- One level `c`. -/
def single (c : ℝ) : CriticalValues 0 where
  value _ := c
  strictMono a b h :=
    absurd h (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; exact lt_irrefl _)

/-- The presentation with one vertex piece `X` and no edges. -/
def constPresentation (X : Type) [TopologicalSpace X] : CylinderPresentation.{0} 0 where
  V _ := X
  E e := e.elim0
  topV _ := inferInstance
  topE e := e.elim0
  left e := e.elim0
  right e := e.elim0

/-- The space `X` at constant height `c`. -/
def constOver (X : Type) [TopologicalSpace X] (c : ℝ) : Over (TopCat.of ℝ) :=
  Over.mk (TopCat.ofHom (ContinuousMap.const X c))

/-- `X` at constant height `c` is the realization of `constPresentation X` over `single c`. -/
def constOverIso (X : Type) [TopologicalSpace X] (c : ℝ) :
    constOver X c ≅ Over.mk (TopCat.ofHom ((constPresentation X).height (single c))) :=
  Over.isoMk (TopCat.isoOfHomeo (X := (constOver X c).left)
      (Y := TopCat.of ((constPresentation X).Realization (single c)))
      (Examples.Cylinder.homeomorphZero (single c) (constPresentation X))) (by
    ext x
    rfl)

/-- **Constant height.** A compact locally path-connected space at constant height is
constructible. -/
theorem isConstructibleSpace_constOver (X : Type) [TopologicalSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (c : ℝ) : IsConstructibleSpace (constOver X c) :=
  ⟨0, single c, constPresentation X, fun _ => inferInstanceAs (CompactSpace X),
    fun _ => inferInstanceAs (LocallyPathConnectedSpace X), fun e => e.elim0, fun e => e.elim0,
    ⟨constOverIso X c⟩⟩

/-- **Constant height.** Its thickening is constructible. -/
theorem isConstructibleSpace_thickening_constOver (X : Type) [TopologicalSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (c : ℝ) (ε : ℝ≥0) :
    IsConstructibleSpace ((GeometricThickening.functor ε).obj (constOver X c)) :=
  isConstructibleSpace_thickening_of_isConstructibleSpace (isConstructibleSpace_constOver X c) ε

/-- The shifted witness of one level `c` has the levels `c - ε` and `c + ε`. -/
theorem range_shifted_single (c : ℝ) (ε : ℝ≥0) :
    Set.range ((single c).shifted ε).value = {c - ε, c + ε} := by
  ext x
  rw [mem_range_shifted_iff]
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨0, h⟩

/-! ### A non-Hausdorff input -/

/-- The indiscrete two-point space. -/
def IndiscreteBool : Type := Bool

instance : TopologicalSpace IndiscreteBool := ⊤

instance : IndiscreteTopology IndiscreteBool := ⟨rfl⟩

instance : Finite IndiscreteBool := inferInstanceAs (Finite Bool)

instance : CompactSpace IndiscreteBool := Finite.compactSpace

instance : LocallyPathConnectedSpace IndiscreteBool :=
  AlexandrovDiscrete.locallyPathConnectedSpace

/-- Two distinct points of a space joined by a continuous image of the indiscrete two-point space
rule out the Hausdorff property: they are inseparable. -/
theorem not_t2Space_of_indiscreteBool {Y : Type*} [TopologicalSpace Y] (g : IndiscreteBool → Y)
    (hg : Continuous g) (hne : g (true : Bool) ≠ g (false : Bool)) : ¬ T2Space Y := fun _ =>
  hne ((Inseparable.all (α := IndiscreteBool) true false).map hg).eq

/-- **Not Hausdorff.** The indiscrete two-point space is not Hausdorff. -/
theorem not_t2Space_indiscreteBool : ¬ T2Space IndiscreteBool :=
  not_t2Space_of_indiscreteBool id continuous_id fun h =>
    Bool.noConfusion (h : (true : Bool) = false)

/-- The indiscrete two-point space at constant height is constructible. -/
theorem isConstructibleSpace_constOver_indiscreteBool (c : ℝ) :
    IsConstructibleSpace (constOver IndiscreteBool c) :=
  isConstructibleSpace_constOver IndiscreteBool c

/-- **A non-Hausdorff input.** Its thickening is constructible. -/
theorem isConstructibleSpace_thickening_indiscreteBool (c : ℝ) (ε : ℝ≥0) :
    IsConstructibleSpace ((GeometricThickening.functor ε).obj (constOver IndiscreteBool c)) :=
  isConstructibleSpace_thickening_constOver IndiscreteBool c ε

/-- **Not Hausdorff.** The thickened space `IndiscreteBool × [-ε, ε]` is not Hausdorff. -/
theorem not_t2Space_thickening_indiscreteBool (c : ℝ) (ε : ℝ≥0) :
    ¬ T2Space ((GeometricThickening.functor ε).obj (constOver IndiscreteBool c)).left := by
  show ¬ T2Space (IndiscreteBool × GeometricThickening.Band ε)
  exact not_t2Space_of_indiscreteBool
    (fun b => ((b, ⟨0, GeometricThickening.zero_mem_band ε⟩) :
      IndiscreteBool × GeometricThickening.Band ε))
    (continuous_id.prodMk continuous_const) fun h =>
      Bool.noConfusion (congrArg Prod.fst h : (true : Bool) = false)

/-- **Not Hausdorff.** No vertex piece of the thickening presentation of the indiscrete two-point
space is Hausdorff: through `windowFiberHomeomorph` it is the fiber of the thickened height, which
contains the inseparable points over `true` and over `false` at band coordinate `b j - c`. -/
theorem not_t2Space_shiftedThick_V_indiscreteBool (c : ℝ) (ε : ℝ≥0)
    (j : Fin ((single c).shiftedCount ε + 1)) :
    ¬ T2Space (((constPresentation IndiscreteBool).shiftedThick (single c) ε).V j) := by
  intro hT
  have hb : ((single c).shifted ε).value j - c ∈ GeometricThickening.Band ε := by
    obtain ⟨_, h | h⟩ := (mem_range_shifted_iff (single c) ε).1 ⟨j, rfl⟩
    · rw [h]
      show (c - ε) - c ∈ Icc (-(ε : ℝ)) ε
      constructor <;> linarith [ε.coe_nonneg]
    · rw [h]
      show (c + ε) - c ∈ Icc (-(ε : ℝ)) ε
      constructor <;> linarith [ε.coe_nonneg]
  have : T2Space ((constPresentation IndiscreteBool).Window (single c) ε
      (((single c).shifted ε).value j)) := hT
  have : T2Space (GeometricThickening.height ((constPresentation IndiscreteBool).height (single c))
      ε ⁻¹' {((single c).shifted ε).value j}) :=
    ((constPresentation IndiscreteBool).windowFiberHomeomorph (single c) ε j).symm.isEmbedding
      |>.t2Space
  let q : IndiscreteBool → (constPresentation IndiscreteBool).Realization (single c) :=
    (constPresentation IndiscreteBool).ofVertex (single c) 0
  have hmem : ∀ b, ((q b, ⟨_, hb⟩) : (constPresentation IndiscreteBool).Realization (single c) ×
      GeometricThickening.Band ε) ∈ GeometricThickening.height
        ((constPresentation IndiscreteBool).height (single c)) ε ⁻¹'
          {((single c).shifted ε).value j} := fun b => by
    show c + (((single c).shifted ε).value j - c) = ((single c).shifted ε).value j
    ring
  let g : IndiscreteBool → GeometricThickening.height
      ((constPresentation IndiscreteBool).height (single c)) ε ⁻¹'
        {((single c).shifted ε).value j} := fun b => ⟨(q b, ⟨_, hb⟩), hmem b⟩
  refine not_t2Space_of_indiscreteBool g
    ((((constPresentation IndiscreteBool).continuous_ofVertex (single c) 0).prodMk
      continuous_const).subtype_mk hmem) (fun h => ?_) this
  exact Bool.noConfusion ((constPresentation IndiscreteBool).ofVertex_injective (single c) 0
    (congrArg (fun z => z.1.1) h) : (true : Bool) = false)

/-! ### `ε = 0` -/

/-- **`ε = 0`.** The general theorem at `ε = 0`. -/
theorem isConstructibleSpace_thickening_zero {A : Over (TopCat.of ℝ)}
    (hA : IsConstructibleSpace A) :
    IsConstructibleSpace ((GeometricThickening.functor 0).obj A) :=
  isConstructibleSpace_thickening_of_isConstructibleSpace hA 0

/-- **`ε = 0`.** The same conclusion through `T_0 ≅ 𝟭`. -/
theorem isConstructibleSpace_thickening_zero_of_zeroIso {A : Over (TopCat.of ℝ)}
    (hA : IsConstructibleSpace A) :
    IsConstructibleSpace ((GeometricThickening.functor 0).obj A) := by
  obtain ⟨m, T, P, h1, h2, h3, h4, ⟨i⟩⟩ := hA
  exact ⟨m, T, P, h1, h2, h3, h4, ⟨GeometricThickening.zeroIso.app A ≪≫ i⟩⟩

/-- **`ε = 0`.** The shifted witness of one level at `ε = 0` has one level, and the indiscrete
two-point space has a constructible thickening at `ε = 0`. -/
theorem shiftedCount_single_zero (c : ℝ) :
    (single c).shiftedCount 0 = 0 ∧
      IsConstructibleSpace ((GeometricThickening.functor 0).obj (constOver IndiscreteBool c)) :=
  ⟨(single c).shiftedCount_zero,
    isConstructibleSpace_thickening_zero (isConstructibleSpace_constOver_indiscreteBool c)⟩

/-! ### Empty input -/

/-- The empty space at constant height is constructible. -/
theorem isConstructibleSpace_constOver_empty (c : ℝ) : IsConstructibleSpace (constOver Empty c) :=
  isConstructibleSpace_constOver Empty c

/-- **Empty input.** The thickening of the empty space is constructible and empty. -/
theorem isEmpty_thickening_empty (c : ℝ) (ε : ℝ≥0) :
    IsConstructibleSpace ((GeometricThickening.functor ε).obj (constOver Empty c)) ∧
      IsEmpty ((GeometricThickening.functor ε).obj (constOver Empty c)).left :=
  ⟨isConstructibleSpace_thickening_constOver Empty c ε,
    inferInstanceAs (IsEmpty (Empty × GeometricThickening.Band ε))⟩

/-! ### Duplicate shifted values -/

/-- The two levels `0 < 2`. -/
abbrev S02 : CriticalValues 1 := CriticalValues.pair 0 2 two_pos

/-- The four values `{-1, 1} ∪ {1, 3}` merge to three levels. -/
theorem range_shifted_S02_one : Set.range (S02.shifted 1).value = {-1, 1, 3} := by
  rw [range_shifted_pair]
  ext x
  simp only [mem_insert_iff, mem_singleton_iff, NNReal.coe_one]
  constructor
  · rintro (h | h | h | h) <;> rw [h] <;> norm_num
  · rintro (h | h | h) <;> rw [h] <;> norm_num

/-- **Duplicate shifted values.** The shifted witness of `{0, 2}` at `ε = 1` has two slabs, not
three. -/
theorem shiftedCount_S02_one : S02.shiftedCount 1 = 2 := by
  have h : S02.shiftedSet 1 = {-1, 1, 3} := by
    rw [← Finset.coe_inj, ← range_shifted, range_shifted_S02_one]
    simp
  unfold shiftedCount
  rw [h, Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
    Finset.card_singleton]

/-- **Duplicate shifted values.** The thickening of the segment over `{0, 2}` at `ε = 1` is
constructible, presented over the merged three-level witness. -/
theorem isConstructibleSpace_thickening_seg_S02 :
    IsConstructibleSpace ((GeometricThickening.functor 1).obj
      (Over.mk (TopCat.ofHom (Examples.ThickeningWindow.seg.height S02)))) := by
  have : ∀ i, CompactSpace (Examples.ThickeningWindow.seg.V i) := fun _ =>
    inferInstanceAs (CompactSpace Unit)
  have : ∀ i, LocallyPathConnectedSpace (Examples.ThickeningWindow.seg.V i) := fun _ =>
    inferInstanceAs (LocallyPathConnectedSpace Unit)
  have : ∀ e, CompactSpace (Examples.ThickeningWindow.seg.E e) := fun _ =>
    inferInstanceAs (CompactSpace Unit)
  have : ∀ e, LocallyPathConnectedSpace (Examples.ThickeningWindow.seg.E e) := fun _ =>
    inferInstanceAs (LocallyPathConnectedSpace Unit)
  exact Examples.ThickeningWindow.seg.isConstructibleSpace_thickening_realization S02 1

end

end TDA.Reeb.Examples.ThickeningConstructible
