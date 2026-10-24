import TDA.Persistence.RectangleMatchingDistance
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A sharp two-dimensional rectangle example

Bjerkevik's Example 5.2 consists of two triples of open rectangles. Its
integral coefficient matrices define an actual 1-interleaving over every
field. Below radius 3, two significant source occurrences would both have
to match the first target occurrence. This obstruction gives bottleneck
distance 3 and, using rectangle stability, interleaving distance 1.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RectangleSharpExample

open CategoryTheory CategoryTheory.Limits CoordinateShift
open RectangleStabilityGeometry RectangleHall RectangleFamily RectangleMatching
open scoped TDA.Persistence NNReal ENNReal Classical ZeroObject

private def openInterval (a b : ℝ) (h : a < b) : BoundedInterval :=
  ⟨a, b, false, false, Or.inl h⟩

/-- The source occurrences `(0,10)×(1,11)`, `(0,12)×(-1,11)`,
and `(2,10)×(1,9)`, all with open endpoints. -/
def source : Fin 3 → Rectangle 2 := ![
  ![openInterval 0 10 (by norm_num), openInterval 1 11 (by norm_num)],
  ![openInterval 0 12 (by norm_num), openInterval (-1) 11 (by norm_num)],
  ![openInterval 2 10 (by norm_num), openInterval 1 9 (by norm_num)]]

/-- The target occurrences `(1,11)×(0,10)`, `(1,9)×(0,12)`,
and `(-1,11)×(2,10)`, all with open endpoints. -/
def target : Fin 3 → Rectangle 2 := ![
  ![openInterval 1 11 (by norm_num), openInterval 0 10 (by norm_num)],
  ![openInterval 1 9 (by norm_num), openInterval 0 12 (by norm_num)],
  ![openInterval (-1) 11 (by norm_num), openInterval 2 10 (by norm_num)]]

private def family (b : Bool) : Fin 3 → Rectangle 2 := if b then target else source

private def matrix (b : Bool) : Fin 3 → Fin 3 → ℤ :=
  if b then ![![-1, 1, 1], ![1, 0, -1], ![1, -1, 0]]
  else ![![1, 1, 1], ![1, 1, 0], ![1, 0, 1]]

private theorem mem_family (b : Bool) (i : Fin 3) {a : ℝ}
    (ha : 2 < a) (ha' : a < 9) : (fun _ => a) ∈ (family b i).support := by
  intro j
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp [family, source, target, openInterval, BoundedInterval.support] <;>
    constructor <;> linarith

private theorem significant_family (b : Bool) (i : Fin 3) {δ : ℝ≥0}
    (hδ : δ ≤ 6) : Significant δ (family b i) := by
  refine ⟨fun _ => (5 / 2 : ℝ), mem_family b i (by norm_num) (by norm_num), ?_⟩
  change (fun _ => 5 / 2 + (δ : ℝ)) ∈ (family b i).support
  apply mem_family
  · have := δ.coe_nonneg; linarith
  · have : (δ : ℝ) ≤ 6 := hδ; linarith

private theorem alpha_family (b : Bool) (i l : Fin 3) :
    alphaLE (family b i) (family b l) := by
  cases b <;> fin_cases i <;> fin_cases l <;>
    norm_num [alphaLE, alphaValue, alphaPlus, endpoint, plus, family, source,
      target, openInterval, Fintype.sum_prod_type, Fin.sum_univ_succ]

private def admissible (b : Bool) (i j : Fin 3) : Prop :=
  ∀ e, decoratedLE (endpoint (family (!b) j) e)
    (endpoint (family b i) e + (1 : ℝ))
    (plus (family (!b) j) e) (plus (family b i) e)

private theorem admissible_of_matrix_ne_zero (b : Bool) (i j : Fin 3)
    (h : matrix b i j ≠ 0) : admissible b i j := by
  intro ⟨c, e⟩
  cases b <;> fin_cases i <;> fin_cases j <;> fin_cases c <;> cases e <;>
    norm_num [matrix] at h <;>
    norm_num [family, source, target, openInterval, decoratedLE, endpoint, plus]

variable {k : Type u} [Field k]

private instance (ε : ℝ≥0) : (shift (R := k) (n := 2) ε).Additive where
  map_add := by intros; rfl

private noncomputable def coefficientHom (R S : Rectangle 2) (ε : ℝ≥0) :
    (R.module (k := k) ⟶ (shift ε).obj S.module) →+ k where
  toFun := shiftedCoefficient R S ε
  map_zero' := shiftedCoefficient_zero R S ε
  map_add' := shiftedCoefficient_add R S ε

private theorem coefficient_injective (R S : Rectangle 2) (ε : ℝ≥0) :
    Function.Injective (coefficientHom (k := k) R S ε) := by
  intro f g h
  apply sub_eq_zero.mp
  by_contra hne
  apply (shiftedCoefficient_ne_zero_iff R S ε (f - g)).mpr hne
  change coefficientHom R S ε (f - g) = 0
  rw [map_sub, h, sub_self]

private noncomputable def entry (b : Bool) (i j : Fin 3) :
    (family b i).module (k := k) ⟶ (shift 1).obj (family (!b) j).module :=
  if h : admissible b i j then matrix b i j • comparison _ _ 1 h else 0

private theorem coefficient_entry (b : Bool) (i j : Fin 3) :
    shiftedCoefficient (family b i) (family (!b) j) 1 (entry (k := k) b i j) =
      (matrix b i j : k) := by
  classical
  by_cases h : admissible b i j
  · change coefficientHom _ _ 1 (entry b i j) = _
    rw [entry, dif_pos h, map_zsmul]
    have hc : coefficientHom (k := k) _ _ 1 (comparison _ _ 1 h) = 1 :=
      shiftedCoefficient_comparison _ _ 1 h
        (mem_family b i (a := 3) (by norm_num) (by norm_num))
        (by
          have he : translation 1 (fun _ : Fin 2 => (3 : ℝ)) = (fun _ => 4) := by
            funext c; norm_num [translation_apply]
          rw [he]
          exact mem_family (!b) j (a := 4) (by norm_num) (by norm_num))
    rw [hc]; simp
  · have hz : matrix b i j = 0 := by
      by_contra hn; exact h (admissible_of_matrix_ne_zero b i j hn)
    simp [entry, h, shiftedCoefficient_zero, hz]

private noncomputable def familyMap (b : Bool) :
    module (k := k) (family b) ⟶ (shift 1).obj (module (family (!b))) :=
  mapOfComponents _ _ 1 (entry b)

private theorem matrix_inverse (b : Bool) (i l : Fin 3) :
    (∑ j : Fin 3, (matrix b i j : k) * (matrix (!b) j l : k)) =
      if i = l then 1 else 0 := by
  cases b <;> fin_cases i <;> fin_cases l <;>
    norm_num [matrix, Fin.sum_univ_succ]

private theorem matrix_law (A B : Fin 3 → Rectangle 2)
    (f : ∀ i j, (A i).module (k := k) ⟶ (shift 1).obj (B j).module)
    (g : ∀ j l, (B j).module (k := k) ⟶ (shift 1).obj (A l).module)
    (hα : ∀ i l, alphaLE (A i) (A l))
    (hs : ∀ i, Significant 6 (A i))
    (hinv : ∀ i l, (∑ j, shiftedCoefficient (A i) (B j) 1 (f i j) *
      shiftedCoefficient (B j) (A l) 1 (g j l)) = if i = l then 1 else 0) :
    mapOfComponents A B 1 f ≫ (shift 1).map (mapOfComponents B A 1 g) ≫
      (compIso 1 1 (module A)).hom = transition (1 + 1) (module A) := by
  classical
  apply component_ext A A (1 + 1)
  intro i l
  apply coefficient_injective
  rw [← component_composite_shift]
  simp only [component_mapOfComponents, Preadditive.sum_comp]
  change coefficientHom _ _ (1 + 1) (∑ j : Fin 3, _) = _
  rw [map_sum]
  have hpath (j : Fin 3) :
      coefficientHom (k := k) _ _ (1 + 1)
        (f i j ≫ (shift 1).map (g j l) ≫
          (compIso 1 1 ((A l).module)).hom) =
        shiftedCoefficient (A i) (B j) 1 (f i j) *
          shiftedCoefficient (B j) (A l) 1 (g j l) := by
    change shiftedCoefficient _ _ _ _ = _
    exact shiftedCoefficient_composite (by norm_num) _ _ _ 1 (hα i l)
      (by change Significant _ (A i); convert hs i using 1; norm_num [stabilityRadius])
      (by change Significant _ (A l); convert hs l using 1; norm_num [stabilityRadius]) _ _
  calc
    _ = ∑ j : Fin 3, shiftedCoefficient (A i) (B j) 1 (f i j) *
        shiftedCoefficient (B j) (A l) 1 (g j l) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hpath j
    _ = if i = l then 1 else 0 := hinv i l
    _ = _ := ?_
  by_cases h : i = l
  · subst l
    rw [if_pos rfl, component_transition_self]
    exact (shiftedCoefficient_transition _ _
      ((hs i).of_le (by norm_num))).symm
  · rw [if_neg h, component_transition_ne _ _ h]
    exact (shiftedCoefficient_zero _ _ _).symm

/-- The actual 1-interleaving given by the two integral matrices of Example 5.2.
The inverse identities hold in every field, including characteristic two. -/
noncomputable def interleaving :
    CoordinateInterleaving 1 (module (k := k) source) (module target) where
  φ := familyMap false
  ψ := familyMap true
  φ_ψ := matrix_law source target (entry false) (entry true)
    (alpha_family false) (fun i => significant_family false i le_rfl)
    (by
      intro i l
      calc
        _ = ∑ j : Fin 3, (matrix false i j : k) * (matrix true j l : k) := by
          apply Finset.sum_congr rfl
          intro j _
          exact congrArg₂ (· * ·) (coefficient_entry false i j) (coefficient_entry true j l)
        _ = _ := matrix_inverse false i l)
  ψ_φ := matrix_law target source (entry true) (entry false)
    (alpha_family true) (fun i => significant_family true i le_rfl)
    (by
      intro i l
      calc
        _ = ∑ j : Fin 3, (matrix true i j : k) * (matrix false j l : k) := by
          apply Finset.sum_congr rfl
          intro j _
          exact congrArg₂ (· * ·) (coefficient_entry true i j) (coefficient_entry false j l)
        _ = _ := matrix_inverse true i l)

/-- Reading the forward maps recovers the source's coefficient matrix. -/
theorem forward_component_coefficient (i j : Fin 3) :
    shiftedCoefficient (source i) (target j) 1
      (component source target 1 (interleaving (k := k)).φ i j) =
      (![![1, 1, 1], ![1, 1, 0], ![1, 0, 1]] : Fin 3 → Fin 3 → k) i j := by
  change shiftedCoefficient _ _ 1 (component _ _ 1 (mapOfComponents _ _ 1 _) i j) = _
  have h := coefficient_entry (k := k) false i j
  calc
    _ = shiftedCoefficient (source i) (target j) 1 (entry false i j) :=
      congrArg (shiftedCoefficient (k := k) (source i) (target j) 1)
        (component_mapOfComponents source target 1 (entry false) i j)
    _ = (matrix false i j : k) := h
    _ = _ := by fin_cases i <;> fin_cases j <;> norm_num [matrix]

/-- Reading the reverse maps recovers the integral inverse matrix. -/
theorem reverse_component_coefficient (i j : Fin 3) :
    shiftedCoefficient (target i) (source j) 1
      (component target source 1 (interleaving (k := k)).ψ i j) =
      (![![-1, 1, 1], ![1, 0, -1], ![1, -1, 0]] : Fin 3 → Fin 3 → k) i j := by
  change shiftedCoefficient _ _ 1 (component _ _ 1 (mapOfComponents _ _ 1 _) i j) = _
  have h := coefficient_entry (k := k) true i j
  calc
    _ = shiftedCoefficient (target i) (source j) 1 (entry true i j) :=
      congrArg (shiftedCoefficient (k := k) (target i) (source j) 1)
        (component_mapOfComponents target source 1 (entry true) i j)
    _ = (matrix true i j : k) := h
    _ = _ := by fin_cases i <;> fin_cases j <;> norm_num [matrix]

/-- A full occurrence matching, pairing the three equal indices. -/
def matching : OccurrenceMatching (Fin 3) (Fin 3) PEmpty.{1} PEmpty.{1} where
  finite i := some i
  finite_injective := by intro i i' j h h'; exact Option.some.inj (h.trans h'.symm)
  essential := Equiv.refl _

private theorem endpointClose_three (i j : Fin 3) : endpointClose 3 (source i) (target j) := by
  intro ⟨c, e⟩
  fin_cases i <;> fin_cases j <;> fin_cases c <;> cases e <;>
    norm_num [endpointClose, decoratedLE, endpoint, plus, source, target, openInterval]

/-- Every paired module really is 3-interleaved; the matching has no deletions. -/
theorem isMatching_three : IsMatching (k := k) 3 source target matching where
  paired := by
    intro i j h
    have he : i = j := Option.some.inj h
    subst j
    exact ⟨interleavingOfEndpointClose _ _ 3 (endpointClose_three i i)⟩
  source_zero := by intro i h; cases h
  target_zero := by intro j h; exact False.elim (h j rfl)

private theorem forced_partner {ρ : ℝ≥0} (hρ : ρ < 3)
    {i j : Fin 3} (hi : i ≠ 0)
    (I : CoordinateInterleaving ρ ((source i).module (k := k)) (target j).module) : j = 0 := by
  have hs : Significant (ρ + ρ) (source i) :=
    significant_family false i (by have : (ρ : ℝ) < 3 := hρ; exact_mod_cast (by linarith :
      (ρ : ℝ) + (ρ : ℝ) ≤ 6))
  have ht := (significant_iff_transition_ne_zero (k := k) _ _).mp hs
  have hf : I.φ ≠ 0 := by intro h; apply ht; rw [← I.φ_ψ, h]; simp
  have hg : I.ψ ≠ 0 := by intro h; apply ht; rw [← I.φ_ψ, h]; simp
  have h₁ := decoratedLE_value (shifted_hom_endpoint_bounds _ _ _ I.ψ hg (0, true))
  have h₂ := decoratedLE_value (shifted_hom_endpoint_bounds _ _ _ I.φ hf (1, false))
  have h₃ := decoratedLE_value (shifted_hom_endpoint_bounds _ _ _ I.φ hf (1, true))
  have h₄ := decoratedLE_value (shifted_hom_endpoint_bounds _ _ _ I.ψ hg (0, false))
  have hr : (ρ : ℝ) < 3 := hρ
  by_contra hj
  fin_cases i <;> fin_cases j <;> norm_num at hi <;> norm_num at hj
  all_goals norm_num [endpoint, source, target, openInterval] at h₁ h₂ h₃ h₄
  all_goals linarith

/-- Below radius 3 the two significant occurrences `source 1` and `source 2`
would both have to match `target 0`, contradicting occurrence injectivity. -/
theorem matching_radius_ge_three {ρ : ℝ≥0}
    {M : OccurrenceMatching (Fin 3) (Fin 3) PEmpty.{1} PEmpty.{1}}
    (hM : IsMatching (k := k) ρ source target M) : 3 ≤ ρ := by
  by_contra h
  have hρ : ρ < 3 := lt_of_not_ge h
  have hs (i : Fin 3) : Significant (ρ + ρ) (source i) :=
    significant_family false i (by have : (ρ : ℝ) < 3 := hρ; exact_mod_cast (by linarith :
      (ρ : ℝ) + (ρ : ℝ) ≤ 6))
  obtain ⟨j, hj⟩ := hM.source_covered 1 (hs 1)
  obtain ⟨l, hl⟩ := hM.source_covered 2 (hs 2)
  obtain ⟨Ij⟩ := hM.paired 1 j hj
  obtain ⟨Il⟩ := hM.paired 2 l hl
  have hj0 := forced_partner hρ (by decide : (1 : Fin 3) ≠ 0) Ij
  have hl0 := forced_partner hρ (by decide : (2 : Fin 3) ≠ 0) Il
  subst j; subst l
  have he := M.finite_injective 1 2 0 hj hl
  exact (by decide : (1 : Fin 3) ≠ 2) he

/-- The infimum over actual occurrence matching radii is exactly 3. -/
theorem bottleneckDistance_eq_three : bottleneckDistance (k := k) source target = 3 := by
  apply le_antisymm
  · exact bottleneckDistance_le_of_matching isMatching_three
  · apply (le_bottleneckDistance_iff source target 3).mpr
    intro ρ M hM
    exact_mod_cast matching_radius_ge_three hM

/-- Every actual interleaving has radius at least 1. This follows from the
proved factor-three matching theorem and the explicit matching obstruction. -/
theorem interleaving_radius_ge_one {ε : ℝ≥0}
    (I : CoordinateInterleaving ε (module (k := k) source) (module target)) : 1 ≤ ε := by
  obtain ⟨M, hM⟩ := exists_matching (by decide : 0 < 2) source target ε I
  have h := matching_radius_ge_three hM
  have h' : (3 : ℝ) ≤ 3 * (ε : ℝ) := by
    simpa [stabilityRadius] using (show (3 : ℝ) ≤ (stabilityRadius 2 ε : ℝ) from h)
  exact_mod_cast (by linarith : (1 : ℝ) ≤ (ε : ℝ))

/-- The infimum over actual natural-transformation interleavings is exactly 1. -/
theorem interleavingDistance_eq_one :
    coordinateInterleavingDistance (module (k := k) source) (module target) = 1 := by
  apply le_antisymm
  · exact interleaving.distance_le
  · apply le_coordinateInterleavingDistance_iff.mpr
    rintro ε ⟨I⟩
    exact_mod_cast interleaving_radius_ge_one I

/-- Factor three is attained, so no universal coefficient below three works
for finite bounded open rectangles in dimension two. -/
theorem sharp_factor : bottleneckDistance (k := k) source target =
    3 * coordinateInterleavingDistance (module (k := k) source) (module target) := by
  rw [bottleneckDistance_eq_three, interleavingDistance_eq_one, mul_one]

/-- The two distances disagree even for these finite sums of open rectangles. -/
theorem interleavingDistance_lt_bottleneckDistance :
    coordinateInterleavingDistance (module (k := k) source) (module target) <
      bottleneckDistance (k := k) source target := by
  rw [interleavingDistance_eq_one, bottleneckDistance_eq_three]
  norm_num

/-- Every smaller proposed coefficient fails on this same fixed pair. -/
theorem fails_smaller_constant {c : ℝ≥0∞} (hc : c < 3) :
    ¬ bottleneckDistance (k := k) source target ≤
      c * coordinateInterleavingDistance (module (k := k) source) (module target) := by
  rw [bottleneckDistance_eq_three, interleavingDistance_eq_one, mul_one]
  exact not_le_of_gt hc

end TDA.Persistence.RectangleSharpExample
