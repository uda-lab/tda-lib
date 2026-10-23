import TDA.Persistence.RectangleFamily
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Prod.Lex

/-!
# The Hall neighbor inequality for finite rectangle sums

A rectangle is significant at δ when some grade survives its δ transition.
For an actual ε-interleaving of finite rectangle sums, every selected family
of `(4n−2)ε`-significant occurrences has at least as many neighbors at radius
`(2n−1)ε`. Occurrence indices preserve repeated rectangles.

The proof follows the finite bounded part of Bjerkevik's Lemma 4.9. Component
maps have a scalar constant on their overlap. Common-grade geometry proves
the scalar composition law for ordered significant endpoints. The actual
interleaving equations and path pruning then give a scalar matrix product
that is triangular with unit diagonal, so Mathlib's rank bounds imply Hall's
inequality. A two-sided matching and the barcode distance bounds require
further arguments.
-/

set_option autoImplicit false

namespace TDA.Persistence.RectangleHall

open CategoryTheory CoordinateShift
open scoped TDA.Persistence NNReal

/-- A rectangle is δ-significant when a grade survives the δ transition. -/
def Significant {n : ℕ} (δ : ℝ≥0) (R : Rectangle n) : Prop :=
  ∃ p, p ∈ R.support ∧ translation δ p ∈ R.support

/-- Significance persists when the transition length is decreased. -/
theorem Significant.of_le {n : ℕ} {δ ρ : ℝ≥0} (hδρ : δ ≤ ρ)
    {R : Rectangle n} (h : Significant ρ R) : Significant δ R := by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p, hp, R.ordConnected.out hp hp' ?_⟩
  constructor
  · intro j
    change p j ≤ p j + (δ : ℝ)
    exact le_add_of_nonneg_right δ.coe_nonneg
  · intro j
    change p j + (δ : ℝ) ≤ p j + (ρ : ℝ)
    exact add_le_add le_rfl (show (δ : ℝ) ≤ (ρ : ℝ) from hδρ)

/-- Scalar of a shifted rectangle map at a supported source grade. -/
noncomputable def shiftedCoefficientAt {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    (p : Fin n → ℝ) (hpR : p ∈ R.support) : k :=
  ((show SupportInterval.fiber (k := k) S.support (translation ε p) from
    (f.app p).hom (SupportInterval.one (k := k) R.support hpR)) : k)

/-- Naturality makes the scalar coefficient of a shifted rectangle map
constant along comparable points of its overlap. -/
theorem shifted_coefficient_eq_of_le {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    {p q : Fin n → ℝ} (hpq : p ≤ q)
    (hpR : p ∈ R.support) (hqR : q ∈ R.support)
    (hqS : translation ε q ∈ S.support) :
    shiftedCoefficientAt R S ε f p hpR =
      shiftedCoefficientAt R S ε f q hqR := by
  classical
  have hn := congrArg
    (fun v => ((show SupportInterval.fiber (k := k) S.support (translation ε q)
      from v.hom (SupportInterval.one (k := k) R.support hpR)) : k))
    (f.naturality (homOfLE hpq))
  have hm : structureMapLinear R.module hpq
      (SupportInterval.one (k := k) R.support hpR) =
      SupportInterval.one (k := k) R.support hqR := by
    apply Subtype.ext
    rw [SupportInterval.structureMap_val]
    simp [hqR, SupportInterval.one]
  change ((show SupportInterval.fiber (k := k) S.support (translation ε q) from
      (f.app q).hom (structureMapLinear R.module hpq
        (SupportInterval.one R.support hpR))) : k) =
    (structureMapLinear S.module ((translation ε).monotone' hpq)
      ((f.app p).hom (SupportInterval.one R.support hpR)) : k) at hn
  rw [hm] at hn
  change _ = ((structureMapLinear (SupportInterval.module (k := k) S.support S.ordConnected)
    ((translation ε).monotone' hpq)
    ((f.app p).hom (SupportInterval.one R.support hpR))) : k) at hn
  have hv : ((structureMapLinear (SupportInterval.module (k := k) S.support
      S.ordConnected) ((translation ε).monotone' hpq)
      ((f.app p).hom (SupportInterval.one R.support hpR))) : k) =
      shiftedCoefficientAt R S ε f p hpR := by
    have hs := SupportInterval.structureMap_val S.support S.ordConnected
      ((translation ε).monotone' hpq)
      ((f.app p).hom (SupportInterval.one R.support hpR))
    change _ = if translation ε q ∈ S.support then
      shiftedCoefficientAt R S ε f p hpR else 0 at hs
    rw [if_pos hqS] at hs
    exact hs
  rw [hv] at hn
  simpa only [shiftedCoefficientAt] using hn.symm

/-- Every nonzero shifted rectangle map has one scalar coefficient across its
entire overlap, including open and closed endpoint cases. -/
theorem shifted_coefficient_eq {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    {p q : Fin n → ℝ} (hpR : p ∈ R.support)
    (hpS : translation ε p ∈ S.support)
    (hqR : q ∈ R.support) (hqS : translation ε q ∈ S.support) :
    shiftedCoefficientAt R S ε f p hpR =
      shiftedCoefficientAt R S ε f q hqR := by
  have hmR := R.inf_mem hpR hqR
  have hmS : translation ε (p ⊓ q) ∈ S.support := by
    intro i
    by_cases h : p i ≤ q i
    · simpa [translation_apply, Pi.inf_apply, min_eq_left h] using hpS i
    · have h' : q i ≤ p i := le_of_not_ge h
      simpa [translation_apply, Pi.inf_apply, min_eq_right h'] using hqS i
  have hmp := shifted_coefficient_eq_of_le R S ε f inf_le_left hmR hpR hpS
  have hmq := shifted_coefficient_eq_of_le R S ε f inf_le_right hmR hqR hqS
  exact hmp.symm.trans hmq

/-- The scalar of a shifted rectangle map, zero when the overlap is empty.
The chosen point depends only on the supports, so this is additive in the map. -/
noncomputable def shiftedCoefficient {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module) : k := by
  classical
  exact if h : ∃ p, p ∈ R.support ∧ translation ε p ∈ S.support then
    shiftedCoefficientAt R S ε f (Classical.choose h) (Classical.choose_spec h).1
  else 0

/-- Any grade of the overlap computes the support-independent scalar. -/
theorem shiftedCoefficient_eq_at {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    {p : Fin n → ℝ} (hpR : p ∈ R.support)
    (hpS : translation ε p ∈ S.support) :
    shiftedCoefficient R S ε f = shiftedCoefficientAt R S ε f p hpR := by
  classical
  have h : ∃ p, p ∈ R.support ∧ translation ε p ∈ S.support := ⟨p, hpR, hpS⟩
  simp only [shiftedCoefficient, dif_pos h]
  exact shifted_coefficient_eq R S ε f
    (Classical.choose_spec h).1 (Classical.choose_spec h).2 hpR hpS

@[simp] theorem shiftedCoefficient_zero {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0) :
    shiftedCoefficient (k := k) R S ε 0 = 0 := by
  classical
  unfold shiftedCoefficient
  split_ifs with h
  · rfl
  · rfl

theorem shiftedCoefficient_add {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f g : R.module (k := k) ⟶ (shift ε).obj S.module) :
    shiftedCoefficient R S ε (f + g) =
      shiftedCoefficient R S ε f + shiftedCoefficient R S ε g := by
  classical
  unfold shiftedCoefficient
  split_ifs with h
  · rfl
  · exact (add_zero (0 : k)).symm

theorem shiftedCoefficient_sum {n : ℕ} {k : Type*} [Field k]
    {ι : Type*} (R S : Rectangle n) (ε : ℝ≥0) (A : Finset ι)
    (f : ι → (R.module (k := k) ⟶ (shift ε).obj S.module)) :
    shiftedCoefficient R S ε (∑ i ∈ A, f i) =
      ∑ i ∈ A, shiftedCoefficient R S ε (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih => simp [hi, shiftedCoefficient_add, ih]

/-- A shifted rectangle map acts by its coefficient on every active overlap. -/
theorem shifted_app_val {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    {p : Fin n → ℝ} (hpR : p ∈ R.support)
    (hpS : translation ε p ∈ S.support)
    (x : SupportInterval.fiber (k := k) R.support p) :
    ((show SupportInterval.fiber (k := k) S.support (translation ε p) from
      (f.app p).hom x) : k) = (x : k) * shiftedCoefficient R S ε f := by
  rw [shiftedCoefficient_eq_at R S ε f hpR hpS]
  have hx : x = (x : k) • SupportInterval.one (k := k) R.support hpR := by
    apply Subtype.ext
    simp [SupportInterval.one]
  calc
    _ = ((show SupportInterval.fiber (k := k) S.support (translation ε p) from
        (f.app p).hom ((x : k) • SupportInterval.one R.support hpR)) : k) :=
      congrArg (fun z => ((show SupportInterval.fiber (k := k) S.support
        (translation ε p) from (f.app p).hom z) : k)) hx
    _ = _ := by rw [map_smul]; rfl

/-- A normalized endpoint comparison has scalar one whenever its overlap
is nonempty, including a singleton overlap at closed endpoints. -/
theorem shiftedCoefficient_comparison {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (h : ∀ j, RectangleStabilityGeometry.decoratedLE
      (RectangleStabilityGeometry.endpoint S j)
      (RectangleStabilityGeometry.endpoint R j + (ε : ℝ))
      (RectangleStabilityGeometry.plus S j) (RectangleStabilityGeometry.plus R j))
    {p : Fin n → ℝ} (hpR : p ∈ R.support)
    (hpS : translation ε p ∈ S.support) :
    shiftedCoefficient (k := k) R S ε
      (RectangleStabilityGeometry.comparison R S ε h) = 1 := by
  classical
  rw [shiftedCoefficient_eq_at R S ε _ hpR hpS]
  have hv := RectangleStabilityGeometry.comparison_app_val R S ε h p
    (SupportInterval.one (k := k) R.support hpR)
  change shiftedCoefficientAt R S ε _ p hpR =
    if translation ε p ∈ S.support then 1 else 0 at hv
  simpa only [if_pos hpS] using hv

/-- Nonzero morphisms have nonzero scalars, and conversely. -/
theorem shiftedCoefficient_ne_zero_iff {n : ℕ} {k : Type*} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module) :
    shiftedCoefficient R S ε f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · intro h hf
    exact h (hf ▸ shiftedCoefficient_zero R S ε)
  · intro hf
    obtain ⟨p, hpR, hpS, hne⟩ :=
      RectangleStabilityGeometry.exists_nonzero_shifted_component R S ε f hf
    rw [shiftedCoefficient_eq_at R S ε f hpR hpS]
    intro hz
    apply hne
    exact Subtype.ext hz

private theorem shiftedCoefficient_composite_at {n : ℕ} {k : Type*} [Field k]
    (R S T : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    (g : S.module (k := k) ⟶ (shift ε).obj T.module)
    {p : Fin n → ℝ} (hpR : p ∈ R.support)
    (hpS : translation ε p ∈ S.support)
    (hpT : translation (ε + ε) p ∈ T.support) :
    shiftedCoefficient R T (ε + ε)
      (f ≫ (shift ε).map g ≫ (compIso ε ε T.module).hom) =
      shiftedCoefficient R S ε f * shiftedCoefficient S T ε g := by
  classical
  have he : translation ε (translation ε p) = translation (ε + ε) p := by
    funext i
    simp [translation_apply, NNReal.coe_add, add_assoc]
  have hpT' : translation ε (translation ε p) ∈ T.support := he ▸ hpT
  rw [shiftedCoefficient_eq_at R T (ε + ε) _ hpR hpT]
  let x : SupportInterval.fiber (k := k) S.support (translation ε p) :=
    (f.app p).hom (SupportInterval.one (k := k) R.support hpR)
  let y : SupportInterval.fiber (k := k) T.support (translation ε (translation ε p)) :=
    (g.app (translation ε p)).hom x
  have hgval := shifted_app_val S T ε g hpS hpT' x
  have hyval : (y : k) = (x : k) * shiftedCoefficient S T ε g := hgval
  have hfval := shifted_app_val R S ε f hpR hpS
    (SupportInterval.one (k := k) R.support hpR)
  have hcomp : translation ε (translation ε p) ≤ translation (ε + ε) p :=
    le_of_eq he
  change ((structureMapLinear (SupportInterval.module (k := k) T.support T.ordConnected)
    hcomp y) : k) = _
  rw [SupportInterval.structureMap_val]
  change (if translation (ε + ε) p ∈ T.support then (y : k) else 0) = _
  rw [if_pos hpT, hyval]
  have hxval : ((show SupportInterval.fiber (k := k) S.support
      (translation ε p) from x) : k) = shiftedCoefficient R S ε f := by
    change (x : k) = (1 : k) * shiftedCoefficient R S ε f at hfval
    simpa only [one_mul] using hfval
  rw [hxval]

/-- Scalar products really compute composition for α-ordered significant
endpoints. Nonvanishing of the composite is proved by the common-grade
geometry, rather than assumed as a compatibility axiom. -/
theorem shiftedCoefficient_composite {n : ℕ} (hn : 0 < n)
    {k : Type*} [Field k] (R S T : Rectangle n) (ε : ℝ≥0)
    (hRT : RectangleStabilityGeometry.alphaLE R T)
    (hR : ∃ p, p ∈ R.support ∧
      translation (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) p ∈ R.support)
    (hT : ∃ p, p ∈ T.support ∧
      translation (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) p ∈ T.support)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    (g : S.module (k := k) ⟶ (shift ε).obj T.module) :
    shiftedCoefficient R T (ε + ε)
      (f ≫ (shift ε).map g ≫ (compIso ε ε T.module).hom) =
      shiftedCoefficient R S ε f * shiftedCoefficient S T ε g := by
  by_cases hf : f = 0
  · subst f
    simp
  by_cases hg : g = 0
  · subst g
    simp
  obtain ⟨p, hpR, hpS, hpT⟩ :=
    RectangleStabilityGeometry.nonzero_path_support hn R S T ε hRT hR hT f hf g hg
  exact shiftedCoefficient_composite_at R S T ε f g hpR hpS hpT

/-- Ordered significant endpoints prevent cancellation of a path consisting
of two nonzero shifted rectangle maps. -/
theorem composite_ne_zero_of_significant {n : ℕ} (hn : 0 < n)
    {k : Type*} [Field k] (R S T : Rectangle n) (ε : ℝ≥0)
    (hRT : RectangleStabilityGeometry.alphaLE R T)
    (hR : Significant (RectangleStabilityGeometry.stabilityRadius n ε +
      RectangleStabilityGeometry.stabilityRadius n ε) R)
    (hT : Significant (RectangleStabilityGeometry.stabilityRadius n ε +
      RectangleStabilityGeometry.stabilityRadius n ε) T)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module) (hf : f ≠ 0)
    (g : S.module (k := k) ⟶ (shift ε).obj T.module) (hg : g ≠ 0) :
    f ≫ (shift ε).map g ≠ 0 := by
  intro hz
  have hc := shiftedCoefficient_composite hn R S T ε hRT hR hT f g
  have hne := mul_ne_zero ((shiftedCoefficient_ne_zero_iff R S ε f).2 hf)
    ((shiftedCoefficient_ne_zero_iff S T ε g).2 hg)
  have hc₀ : shiftedCoefficient R T (ε + ε)
      (f ≫ (shift ε).map g ≫ (compIso ε ε T.module).hom) = 0 := by
    simp only [← Category.assoc, hz]
    simp
  exact hne (hc.symm.trans hc₀)

/-- A rectangle transition that survives somewhere has coefficient one. -/
theorem shiftedCoefficient_transition {n : ℕ} {k : Type*} [Field k]
    (R : Rectangle n) (δ : ℝ≥0)
    (h : ∃ p, p ∈ R.support ∧ translation δ p ∈ R.support) :
    shiftedCoefficient (k := k) R R δ (transition δ R.module) = 1 := by
  classical
  obtain ⟨p, hp, hp'⟩ := h
  rw [shiftedCoefficient_eq_at R R δ _ hp hp']
  change ((structureMapLinear (SupportInterval.module (k := k) R.support R.ordConnected)
    (show p ≤ translation δ p from fun j => le_add_of_nonneg_right δ.coe_nonneg)
    (SupportInterval.one R.support hp)) : k) = 1
  rw [SupportInterval.structureMap_val]
  change (if translation δ p ∈ R.support then (1 : k) else 0) = 1
  rw [if_pos hp']

/-- The support criterion is exactly nonvanishing of the actual transition. -/
theorem significant_iff_transition_ne_zero {n : ℕ} {k : Type*} [Field k]
    (R : Rectangle n) (δ : ℝ≥0) :
    Significant δ R ↔ transition δ (R.module (k := k)) ≠ 0 := by
  classical
  rw [← shiftedCoefficient_ne_zero_iff R R δ]
  constructor
  · intro h
    rw [shiftedCoefficient_transition R δ h]
    exact one_ne_zero
  · intro h
    by_contra hn
    change ¬ (∃ p, p ∈ R.support ∧ translation δ p ∈ R.support) at hn
    exact h (by simp [shiftedCoefficient, hn])

/-- A neighboring pair is connected by an actual interleaving at the stability
radius, including the zero-parameter case. -/
def Neighbor {n : ℕ} {k : Type*} [Field k] (ρ : ℝ≥0)
    (R S : Rectangle n) : Prop :=
  Nonempty (CoordinateInterleaving ρ (R.module (k := k)) S.module)

/-- An intermediate rectangle outside both endpoint neighborhoods cannot
contribute to a forward α-ordered path. This is Lemma 4.7 applied to actual
component maps of a finite-family interleaving. -/
theorem path_eq_zero_of_not_neighbor {n : ℕ} (hn : 0 < n)
    {k : Type*} [Field k] (R S T : Rectangle n) (ε : ℝ≥0)
    (hRT : RectangleStabilityGeometry.alphaLE R T)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    (g : S.module (k := k) ⟶ (shift ε).obj T.module)
    (hRS : ¬ Neighbor (k := k) (RectangleStabilityGeometry.stabilityRadius n ε) R S)
    (hST : ¬ Neighbor (k := k) (RectangleStabilityGeometry.stabilityRadius n ε) S T) :
    f ≫ (shift ε).map g = 0 := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · subst g
    change f ≫ 0 = 0
    simp
  rcases RectangleStabilityGeometry.nonzero_path_interleaving hn R S T ε hRT f hf g hg
    with h | h
  · exact False.elim (hRS h)
  · exact False.elim (hST h)

/-- Neighbors in the finite second family of at least one selected occurrence
of the first family. -/
noncomputable def neighbors {n : ℕ} {k : Type*} [Field k]
    {ι κ : Type} [Fintype κ] (R : ι → Rectangle n) (S : κ → Rectangle n)
    (A : Finset ι) (ρ : ℝ≥0) : Finset κ := by
  classical
  exact Finset.univ.filter (fun j => ∃ i ∈ A, Neighbor (k := k) ρ (R i) (S j))

/-- A path through an occurrence outside the selected neighborhood vanishes
whenever its source and target are selected and ordered by α. -/
theorem component_path_zero_outside {n : ℕ} (hn : 0 < n)
    {k : Type*} [Field k] {ι κ : Type} [Finite ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (f : RectangleFamily.module (k := k) R ⟶
      (shift ε).obj (RectangleFamily.module S))
    (g : RectangleFamily.module (k := k) S ⟶
      (shift ε).obj (RectangleFamily.module R))
    (A : Finset ι) {i i' : ι} (hi : i ∈ A) (hi' : i' ∈ A)
    (hα : RectangleStabilityGeometry.alphaLE (R i) (R i'))
    {j : κ} (hj : j ∉ neighbors (k := k) R S A
      (RectangleStabilityGeometry.stabilityRadius n ε)) :
    RectangleFamily.component R S ε f i j ≫
      (shift ε).map (RectangleFamily.component S R ε g j i') = 0 := by
  have hnot (l : ι) (hl : l ∈ A) :
      ¬ Neighbor (k := k) (RectangleStabilityGeometry.stabilityRadius n ε)
        (R l) (S j) := by
    intro h
    apply hj
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, hl, h⟩
  have hnot' : ¬ Neighbor (k := k)
      (RectangleStabilityGeometry.stabilityRadius n ε) (S j) (R i') := by
    intro h
    exact hnot i' hi' ⟨(Classical.choice h).symm⟩
  exact path_eq_zero_of_not_neighbor hn (R i) (S j) (R i') ε hα
    (RectangleFamily.component R S ε f i j)
    (RectangleFamily.component S R ε g j i') (hnot i hi) hnot'

/-- In the lower triangular and diagonal positions of Lemma 4.9, the
interleaving sum can be restricted to actual neighbors of the selected finite
family. -/
theorem component_sum_neighbors {n : ℕ} (hn : 0 < n)
    {k : Type*} [Field k] {ι κ : Type} [Finite ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (f : RectangleFamily.module (k := k) R ⟶
      (shift ε).obj (RectangleFamily.module S))
    (g : RectangleFamily.module (k := k) S ⟶
      (shift ε).obj (RectangleFamily.module R))
    (A : Finset ι) {i i' : ι} (hi : i ∈ A) (hi' : i' ∈ A)
    (hα : RectangleStabilityGeometry.alphaLE (R i) (R i')) :
    ∑ j ∈ neighbors (k := k) R S A (RectangleStabilityGeometry.stabilityRadius n ε),
      RectangleFamily.component R S ε f i j ≫
        (shift ε).map (RectangleFamily.component S R ε g j i') =
      ∑ j : κ, RectangleFamily.component R S ε f i j ≫
        (shift ε).map (RectangleFamily.component S R ε g j i') := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  exact component_path_zero_outside hn R S ε f g A hi hi' hα hj

/-- An upper triangular scalar product with unit diagonal must have at least
as many intermediate coordinates as source rectangles. The occurrence index
can be empty. -/
theorem card_le_of_triangular_product
    {k : Type*} [Field k] {ι κ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype κ]
    (G : Matrix ι κ k) (F : Matrix κ ι k)
    (hbelow : ∀ ⦃i i' : ι⦄, i' < i → (G * F) i i' = 0)
    (hdiag : ∀ i : ι, (G * F) i i = 1) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  have htri : (G * F).IsUpperTriangular := by
    intro i i' h
    exact hbelow h
  have hdet : (G * F).det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    simp only [hdiag, Finset.prod_const_one]
    exact one_ne_zero
  calc
    Fintype.card ι = (G * F).rank :=
      (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ G.rank := Matrix.rank_mul_le_left G F
    _ ≤ Fintype.card κ := Matrix.rank_le_card_width G

/-- The actual interleaving of finite rectangle sums implies the Hall
neighbor inequality for every selected family of significant occurrences.
No Hall inequality, matrix compatibility or matching is assumed. -/
theorem card_le_neighbors {n : ℕ} (hn : 0 < n)
    {k : Type*} [Field k] {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (RectangleFamily.module (k := k) R)
      (RectangleFamily.module S)) (A : Finset ι)
    (hA : ∀ i ∈ A, Significant
      (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) (R i)) :
    A.card ≤ (neighbors (k := k) R S A
      (RectangleStabilityGeometry.stabilityRadius n ε)).card := by
  classical
  let B := neighbors (k := k) R S A (RectangleStabilityGeometry.stabilityRadius n ε)
  let key (i : A) : (ℝ ×ₗ ℕ) ×ₗ Fin (Fintype.card A) :=
    toLex (toLex (RectangleStabilityGeometry.alphaValue (R i),
      RectangleStabilityGeometry.alphaPlus (R i)), (Fintype.equivFin A) i)
  let : LinearOrder A := LinearOrder.lift' key (by
    intro i j hij
    apply (Fintype.equivFin A).injective
    exact congrArg (fun z => (ofLex z).2) hij)
  have hα {i i' : A} (h : i ≤ i') :
      RectangleStabilityGeometry.alphaLE (R i) (R i') := by
    change key i ≤ key i' at h
    have hh := Prod.Lex.monotone_fst _ _ h
    exact Prod.Lex.toLex_le_toLex.mp hh
  let F : Matrix B A k := fun j i => shiftedCoefficient (R i) (S j) ε
    (RectangleFamily.component R S ε I.φ i j)
  let G : Matrix A B k := fun i j => shiftedCoefficient (S j) (R i) ε
    (RectangleFamily.component S R ε I.ψ j i)
  have entry (i i' : A) (h : RectangleStabilityGeometry.alphaLE (R i) (R i')) :
      (G * F) i' i = shiftedCoefficient (R i) (R i') (ε + ε)
        ((∑ j : κ, RectangleFamily.component R S ε I.φ i j ≫
          (shift ε).map (RectangleFamily.component S R ε I.ψ j i')) ≫
            (compIso ε ε ((R i').module (k := k))).hom) := by
    calc
      (G * F) i' i = ∑ j ∈ B,
          shiftedCoefficient (R i) (S j) ε (RectangleFamily.component R S ε I.φ i j) *
          shiftedCoefficient (S j) (R i') ε (RectangleFamily.component S R ε I.ψ j i') := by
        change (∑ j : B,
          shiftedCoefficient (S j) (R i') ε (RectangleFamily.component S R ε I.ψ j i') *
          shiftedCoefficient (R i) (S j) ε (RectangleFamily.component R S ε I.φ i j)) = _
        calc
          _ = ∑ j ∈ B,
              shiftedCoefficient (S j) (R i') ε
                (RectangleFamily.component S R ε I.ψ j i') *
              shiftedCoefficient (R i) (S j) ε
                (RectangleFamily.component R S ε I.φ i j) :=
            Finset.sum_coe_sort B _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            exact mul_comm _ _
      _ = ∑ j ∈ B, shiftedCoefficient (R i) (R i') (ε + ε)
          (RectangleFamily.component R S ε I.φ i j ≫
            (shift ε).map (RectangleFamily.component S R ε I.ψ j i') ≫
              (compIso ε ε ((R i').module (k := k))).hom) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (shiftedCoefficient_composite hn (R i) (S j) (R i') ε h
          (hA i i.property) (hA i' i'.property) _ _).symm
      _ = shiftedCoefficient (R i) (R i') (ε + ε)
          ((∑ j ∈ B, RectangleFamily.component R S ε I.φ i j ≫
            (shift ε).map (RectangleFamily.component S R ε I.ψ j i')) ≫
              (compIso ε ε ((R i').module (k := k))).hom) := by
        rw [Preadditive.sum_comp, shiftedCoefficient_sum]
        simp only [Category.assoc]
      _ = _ := by
        rw [component_sum_neighbors hn R S ε I.φ I.ψ A i.property i'.property h]
  have hbelow : ∀ ⦃i i' : A⦄, i' < i → (G * F) i i' = 0 := by
    intro i i' h
    rw [entry i' i (hα (le_of_lt h)),
      RectangleFamily.component_interleaving_sum_ne R S ε I
        (show (i' : ι) ≠ (i : ι) from fun he => (ne_of_lt h) (Subtype.ext he)),
      shiftedCoefficient_zero]
  have hε : ε ≤ RectangleStabilityGeometry.stabilityRadius n ε := by
    have hnat : 1 ≤ 2 * n - 1 := by omega
    have hc : (1 : ℝ≥0) ≤ ((2 * n - 1 : ℕ) : ℝ≥0) := by exact_mod_cast hnat
    simpa only [one_mul, RectangleStabilityGeometry.stabilityRadius] using
      mul_le_mul_of_nonneg_right hc (show 0 ≤ ε from zero_le)
  have hdiag (i : A) : (G * F) i i = 1 := by
    rw [entry i i (hα le_rfl), RectangleFamily.component_interleaving_sum_self R S ε I]
    exact shiftedCoefficient_transition (R i) (ε + ε)
      (Significant.of_le (add_le_add hε hε) (hA i i.property))
  have hc := card_le_of_triangular_product G F hbelow hdiag
  simpa only [Fintype.card_coe] using hc

end TDA.Persistence.RectangleHall
