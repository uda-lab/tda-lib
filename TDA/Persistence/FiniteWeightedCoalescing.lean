import TDA.Persistence.FiniteWeightedBoundaryTransport
import TDA.Persistence.BoundaryTransportGeometry

/-!
# Indexed masses and coalesced finite diagrams

A finite family of weighted occurrences may repeat coordinates or contain zero masses.
Coalescing sums the masses at each coordinate. The finite splitting kernel below
retains the original labels while distributing each positive atom proportionally.
-/

set_option autoImplicit false
noncomputable section
namespace TDA.Persistence
open scoped Classical NNReal ENNReal
open BoundaryTransport

universe u v
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

namespace FiniteWeightedDiagram

/-- Coalesce a finite indexed family of masses at strict birth–death coordinates. -/
def ofIndexed (w : I → ℝ≥0) (x : I → Interior) : FiniteWeightedDiagram :=
  ∑ i, Finsupp.single (x i) (w i)

@[simp] theorem ofIndexed_apply (w : I → ℝ≥0) (x : I → Interior) (q : Interior) :
    ofIndexed w x q = ∑ i, if x i = q then w i else 0 := by
  classical
  simp [ofIndexed, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem ofIndexed_apply_real (w : I → ℝ≥0) (x : I → Interior) (q : Interior) :
    ((ofIndexed w x q : ℝ≥0) : ℝ) = ∑ i, if x i = q then (w i : ℝ) else 0 := by
  rw [ofIndexed_apply]
  rw [NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

private theorem ofIndexed_weight_zero_outside (w : I → ℝ≥0) (x : I → Interior)
    (i : I) (hi : x i ∉ (ofIndexed w x).support) : w i = 0 := by
  have hzero : ofIndexed w x (x i) = 0 := Finsupp.notMem_support_iff.mp hi
  rw [ofIndexed_apply] at hzero
  have hle : w i ≤ ∑ k, if x k = x i then w k else 0 := by
    calc
      w i = (if x i = x i then w i else 0) := by simp
      _ ≤ _ := Finset.single_le_sum (s := Finset.univ) (a := i)
        (f := fun k => if x k = x i then w k else 0)
        (fun k _ => by positivity) (Finset.mem_univ i)
  exact nonpos_iff_eq_zero.mp (le_trans hle (le_of_eq hzero))

/-- A support sum against an arbitrary coefficient equals the sum over original labels. -/
theorem ofIndexed_weighted_sum (w : I → ℝ≥0) (x : I → Interior)
    (f : Interior → ℝ) :
    ∑ q : (ofIndexed w x).supportLabels,
      (((ofIndexed w x).weights q : ℝ) * f q.1) =
      ∑ i, (w i : ℝ) * f (x i) := by
  let D := ofIndexed w x
  simp_rw [FiniteWeightedDiagram.weights, ofIndexed_apply_real]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ∈ D.support
  · have hq : (∑ q : D.supportLabels,
        (if x i = q.1 then (w i : ℝ) else 0) * f q.1) = (w i : ℝ) * f (x i) := by
      classical
      rw [Finset.sum_eq_single (⟨x i, hi⟩ : D.supportLabels)]
      · simp
      · intro q _ hq
        simp [Ne.symm (Subtype.coe_ne_coe.mpr hq)]
      · simp
    exact hq
  · have hw := ofIndexed_weight_zero_outside w x i hi
    simp [hw]

/-- Sum a finite label function by the positive coalesced support. -/
private theorem sum_fibers (w : I → ℝ≥0) (x : I → Interior) (f : I → ℝ)
    (hf : ∀ i, x i ∉ (ofIndexed w x).support → f i = 0) :
    (∑ q : (ofIndexed w x).supportLabels, ∑ i, if x i = q.1 then f i else 0) =
      ∑ i, f i := by
  let D := ofIndexed w x
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ∈ D.support
  · rw [Finset.sum_eq_single (⟨x i, hi⟩ : D.supportLabels)]
    · simp
    · intro q _ hq
      simp [Ne.symm (Subtype.coe_ne_coe.mpr hq)]
    · simp
  · have hfi := hf i hi
    simp [hfi]

private theorem sum_fibers_weighted (w : I → ℝ≥0) (x : I → Interior)
    (g : I → ℝ) (f : Interior → ℝ)
    (hg : ∀ i, x i ∉ (ofIndexed w x).support → g i = 0) :
    (∑ q : (ofIndexed w x).supportLabels,
      (∑ i, if x i = q.1 then g i else 0) * f q.1) =
      ∑ i, g i * f (x i) := by
  let D := ofIndexed w x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ∈ D.support
  · rw [Finset.sum_eq_single (⟨x i, hi⟩ : D.supportLabels)]
    · simp
    · intro q _ hq
      simp [Ne.symm (Subtype.coe_ne_coe.mpr hq)]
    · simp
  · have hgi := hg i hi
    simp [hgi]

/-- Coalesced atoms integrate finite indexed coefficients also in extended nonnegative reals. -/
theorem ofIndexed_weighted_sum_ennreal (w : I → ℝ≥0) (x : I → Interior)
    (f : Interior → ℝ≥0∞) :
    (∑ q : (ofIndexed w x).supportLabels,
      ((ofIndexed w x).weights q : ℝ≥0∞) * f q.1) =
      ∑ i, (w i : ℝ≥0∞) * f (x i) := by
  let D := ofIndexed w x
  have hcoe (q : Interior) : (D q : ℝ≥0∞) =
      ∑ i, if x i = q then (w i : ℝ≥0∞) else 0 := by
    rw [ofIndexed_apply]
    rw [ENNReal.ofNNReal_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  change (∑ q : D.supportLabels, (D q.1 : ℝ≥0∞) * f q.1) = _
  simp_rw [hcoe, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ∈ D.support
  · rw [Finset.sum_eq_single (⟨x i, hi⟩ : D.supportLabels)]
    · simp
    · intro q _ hq
      simp [Ne.symm (Subtype.coe_ne_coe.mpr hq)]
    · simp
  · have hw := ofIndexed_weight_zero_outside w x i hi
    simp [hw]

/-- Coalescing preserves total mass, including zero and repeated occurrences. -/
theorem ofIndexed_mass (w : I → ℝ≥0) (x : I → Interior) :
    ∑ q : (ofIndexed w x).supportLabels, ((ofIndexed w x).weights q : ℝ) =
      ∑ i, (w i : ℝ) := by
  simpa using ofIndexed_weighted_sum w x (fun _ => 1)

/-- Fraction of a positive coalesced atom assigned to an original label. -/
def splittingKernel (w : I → ℝ≥0) (x : I → Interior)
    (q : (ofIndexed w x).supportLabels) (i : I) : ℝ :=
  if x i = q.1 then (w i : ℝ) / (ofIndexed w x q.1 : ℝ) else 0

theorem splittingKernel_nonneg (w : I → ℝ≥0) (x : I → Interior)
    (q : (ofIndexed w x).supportLabels) (i : I) :
    0 ≤ splittingKernel w x q i := by
  unfold splittingKernel
  split_ifs <;> positivity

theorem splittingKernel_sum (w : I → ℝ≥0) (x : I → Interior)
    (q : (ofIndexed w x).supportLabels) :
    (∑ i, splittingKernel w x q i) = 1 := by
  have hpos : 0 < (ofIndexed w x q.1 : ℝ) := by
    exact_mod_cast (Finsupp.mem_support_iff.mp q.2).bot_lt
  calc
    (∑ i, splittingKernel w x q i) =
        (∑ i, if x i = q.1 then (w i : ℝ) else 0) / (ofIndexed w x q.1 : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : x i = q.1 <;> simp [splittingKernel, hi]
    _ = (ofIndexed w x q.1 : ℝ) / (ofIndexed w x q.1 : ℝ) := by
      rw [ofIndexed_apply_real]
    _ = 1 := div_self (ne_of_gt hpos)

theorem splittingKernel_mass (w : I → ℝ≥0) (x : I → Interior) (i : I) :
    (∑ q : (ofIndexed w x).supportLabels,
      ((ofIndexed w x).weights q : ℝ) * splittingKernel w x q i) =
      (w i : ℝ) := by
  let D := ofIndexed w x
  by_cases hi : x i ∈ D.support
  · rw [Finset.sum_eq_single (⟨x i, hi⟩ : D.supportLabels)]
    · change (D (x i) : ℝ) * (if x i = x i then (w i : ℝ) /
          (D (x i) : ℝ) else 0) = (w i : ℝ)
      simp only [ite_true]
      have hpos : 0 < (D (x i) : ℝ) := by
        exact_mod_cast (Finsupp.mem_support_iff.mp hi).bot_lt
      field_simp
    · intro q _ hq
      simp [splittingKernel, Ne.symm (Subtype.coe_ne_coe.mpr hq)]
    · simp
  · have hw := ofIndexed_weight_zero_outside w x i hi
    simp [splittingKernel, hw]

private theorem splittingKernel_weighted_sum (w : I → ℝ≥0) (x : I → Interior)
    (q : (ofIndexed w x).supportLabels) (f : Interior → ℝ) :
    (∑ i, splittingKernel w x q i * f (x i)) = f q.1 := by
  have hterm (i : I) : splittingKernel w x q i * f (x i) =
      splittingKernel w x q i * f q.1 := by
    by_cases hi : x i = q.1 <;> simp [splittingKernel, hi]
  simp_rw [hterm, ← Finset.sum_mul, splittingKernel_sum]
  ring

private theorem splittingKernel_linear_sum (w : I → ℝ≥0) (x : I → Interior)
    (g : (ofIndexed w x).supportLabels → ℝ) (f : Interior → ℝ) :
    (∑ i, (∑ q : (ofIndexed w x).supportLabels,
      splittingKernel w x q i * g q) * f (x i)) =
      ∑ q, g q * f q.1 := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  calc
    (∑ i, (splittingKernel w x q i * g q) * f (x i)) =
        (∑ i, splittingKernel w x q i * f (x i)) * g q := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = g q * f q.1 := by
      rw [splittingKernel_weighted_sum]
      ring

end FiniteWeightedDiagram
private theorem linearCost_reduced {w : I → ℝ≥0} {v : J → ℝ≥0}
    (a : FiniteWeightedBoundaryPlan w v) (c : I → J → ℝ)
    (d : I → ℝ) (e : J → ℝ) :
    a.linearCost c d e =
      (∑ i, (w i : ℝ) * d i) + (∑ j, (v j : ℝ) * e j) +
        ∑ i, ∑ j, a.mass i j * (c i j - d i - e j) := by
  simp only [FiniteWeightedBoundaryPlan.linearCost, weightedBoundaryLinearObjective,
    sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => a.mass i j * e j)]
  simp_rw [Finset.sum_mul]
  ring

namespace FiniteWeightedBoundaryPlan

variable {w : I → ℝ≥0} {v : J → ℝ≥0}

private theorem mass_eq_zero_of_source_zero (a : FiniteWeightedBoundaryPlan w v)
    (i : I) (j : J) (h : w i = 0) : a.mass i j = 0 := by
  have hle : a.mass i j ≤ ∑ j, a.mass i j :=
    Finset.single_le_sum (s := Finset.univ) (a := j)
      (f := fun k => a.mass i k) (fun k _ => a.nonneg i k) (Finset.mem_univ j)
  exact le_antisymm (le_trans hle (by simpa [h] using a.row_le i)) (a.nonneg i j)

private theorem mass_eq_zero_of_target_zero (a : FiniteWeightedBoundaryPlan w v)
    (i : I) (j : J) (h : v j = 0) : a.mass i j = 0 := by
  have hle : a.mass i j ≤ ∑ i, a.mass i j :=
    Finset.single_le_sum (s := Finset.univ) (a := i)
      (f := fun k => a.mass k j) (fun k _ => a.nonneg k j) (Finset.mem_univ i)
  exact le_antisymm (le_trans hle (by simpa [h] using a.col_le j)) (a.nonneg i j)

/-- Push every original matrix cell to its pair of coalesced coordinates. -/
def aggregate (a : FiniteWeightedBoundaryPlan w v)
    (x : I → Interior) (y : J → Interior) :
    FiniteWeightedBoundaryPlan (FiniteWeightedDiagram.ofIndexed w x).weights
      (FiniteWeightedDiagram.ofIndexed v y).weights := by
  let D := FiniteWeightedDiagram.ofIndexed w x
  let E := FiniteWeightedDiagram.ofIndexed v y
  let m : D.supportLabels → E.supportLabels → ℝ := fun q r =>
    ∑ i, if x i = q.1 then ∑ j, if y j = r.1 then a.mass i j else 0 else 0
  have hm (q : D.supportLabels) (r : E.supportLabels) : 0 ≤ m q r := by
    dsimp [m]
    exact Finset.sum_nonneg fun i _ => by
      split_ifs with hi
      · exact Finset.sum_nonneg fun j _ => by
          split_ifs with hj
          · exact a.nonneg i j
          · exact le_refl _
      · exact le_refl _
  have hrow (q : D.supportLabels) : (∑ r, m q r) ≤ D.weights q := by
    calc
      (∑ r, m q r) = ∑ i, if x i = q.1 then ∑ j, a.mass i j else 0 := by
        dsimp [m]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : x i = q.1
        · simp only [hi, ite_true]
          exact FiniteWeightedDiagram.sum_fibers v y (fun j => a.mass i j)
            (fun j hj => mass_eq_zero_of_target_zero a i j
              (FiniteWeightedDiagram.ofIndexed_weight_zero_outside v y j hj))
        · simp [hi]
      _ ≤ ∑ i, if x i = q.1 then (w i : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : x i = q.1 <;> simp [hi, a.row_le i]
      _ = D.weights q := by
        simpa only [D, FiniteWeightedDiagram.weights] using
          (FiniteWeightedDiagram.ofIndexed_apply_real w x q.1).symm
  have hcol (r : E.supportLabels) : (∑ q, m q r) ≤ E.weights r := by
    calc
      (∑ q, m q r) = ∑ j, if y j = r.1 then ∑ i, a.mass i j else 0 := by
        dsimp [m]
        calc
          (∑ q : D.supportLabels,
            ∑ i, if x i = q.1 then ∑ j, if y j = r.1 then a.mass i j else 0 else 0) =
              ∑ i, ∑ j, if y j = r.1 then a.mass i j else 0 := by
                exact FiniteWeightedDiagram.sum_fibers w x _ (fun i hi => by
                  have hw := FiniteWeightedDiagram.ofIndexed_weight_zero_outside w x i hi
                  simp [mass_eq_zero_of_source_zero a i _ hw])
          _ = ∑ j, if y j = r.1 then ∑ i, a.mass i j else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : y j = r.1 <;> simp [hj]
      _ ≤ ∑ j, if y j = r.1 then (v j : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : y j = r.1 <;> simp [hj, a.col_le j]
      _ = E.weights r := by
        simpa only [E, FiniteWeightedDiagram.weights] using
          (FiniteWeightedDiagram.ofIndexed_apply_real v y r.1).symm
  exact ⟨m, hm, hrow, hcol⟩

/-- Split each coalesced cell across all original labels in its two fibers. -/
def splitLift (x : I → Interior) (y : J → Interior)
    (b : FiniteWeightedBoundaryPlan
      (FiniteWeightedDiagram.ofIndexed w x).weights
      (FiniteWeightedDiagram.ofIndexed v y).weights) : FiniteWeightedBoundaryPlan w v := by
  let D := FiniteWeightedDiagram.ofIndexed w x
  let E := FiniteWeightedDiagram.ofIndexed v y
  let K := FiniteWeightedDiagram.splittingKernel w x
  let L := FiniteWeightedDiagram.splittingKernel v y
  let m : I → J → ℝ := fun i j =>
    ∑ q : D.supportLabels, ∑ r : E.supportLabels,
      K q i * b.mass q r * L r j
  have hm (i : I) (j : J) : 0 ≤ m i j := by
    exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun r _ =>
      mul_nonneg (mul_nonneg (FiniteWeightedDiagram.splittingKernel_nonneg w x q i)
        (b.nonneg q r)) (FiniteWeightedDiagram.splittingKernel_nonneg v y r j)
  have hrow (i : I) : (∑ j, m i j) ≤ w i := by
    have hsum : (∑ j, m i j) = ∑ q : D.supportLabels, ∑ r : E.supportLabels,
        K q i * b.mass q r := by
      dsimp [m]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      calc
        (∑ j, K q i * b.mass q r * L r j) =
          (K q i * b.mass q r) * ∑ j, L r j := by rw [Finset.mul_sum]
        _ = K q i * b.mass q r := by
          rw [FiniteWeightedDiagram.splittingKernel_sum]
          ring
    rw [hsum]
    calc
      (∑ q : D.supportLabels, ∑ r : E.supportLabels, K q i * b.mass q r) =
          ∑ q : D.supportLabels, K q i * ∑ r, b.mass q r := by
            apply Finset.sum_congr rfl
            intro q _
            rw [Finset.mul_sum]
      _ ≤ ∑ q : D.supportLabels, K q i * D.weights q := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (b.row_le q)
          (FiniteWeightedDiagram.splittingKernel_nonneg w x q i)
      _ = (w i : ℝ) := by
        convert FiniteWeightedDiagram.splittingKernel_mass w x i using 1
        apply Finset.sum_congr rfl
        intro q _
        ring
  have hcol (j : J) : (∑ i, m i j) ≤ v j := by
    have hsum : (∑ i, m i j) = ∑ q : D.supportLabels, ∑ r : E.supportLabels,
        b.mass q r * L r j := by
      dsimp [m]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      calc
        (∑ i, K q i * b.mass q r * L r j) =
          (∑ i, K q i) * (b.mass q r * L r j) := by
            simp_rw [mul_assoc]
            rw [Finset.sum_mul]
        _ = b.mass q r * L r j := by
          rw [FiniteWeightedDiagram.splittingKernel_sum]
          ring
    rw [hsum, Finset.sum_comm]
    calc
      (∑ r : E.supportLabels, ∑ q : D.supportLabels, b.mass q r * L r j) =
          ∑ r : E.supportLabels, (∑ q, b.mass q r) * L r j := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_mul]
      _ ≤ ∑ r : E.supportLabels, E.weights r * L r j := by
        apply Finset.sum_le_sum
        intro r _
        exact mul_le_mul_of_nonneg_right (b.col_le r)
          (FiniteWeightedDiagram.splittingKernel_nonneg v y r j)
      _ = (v j : ℝ) := FiniteWeightedDiagram.splittingKernel_mass v y j
  exact ⟨m, hm, hrow, hcol⟩

/-- The proportional lift preserves every pair coefficient constant on coordinate fibers. -/
theorem splitLift_matrix_sum (x : I → Interior) (y : J → Interior)
    (b : FiniteWeightedBoundaryPlan
      (FiniteWeightedDiagram.ofIndexed w x).weights
      (FiniteWeightedDiagram.ofIndexed v y).weights)
    (f : Interior → Interior → ℝ) :
    (∑ i, ∑ j, (splitLift x y b).mass i j * f (x i) (y j)) =
      ∑ q : (FiniteWeightedDiagram.ofIndexed w x).supportLabels,
        ∑ r : (FiniteWeightedDiagram.ofIndexed v y).supportLabels,
          b.mass q r * f q.1 r.1 := by
  let D := FiniteWeightedDiagram.ofIndexed w x
  let E := FiniteWeightedDiagram.ofIndexed v y
  let K := FiniteWeightedDiagram.splittingKernel w x
  let L := FiniteWeightedDiagram.splittingKernel v y
  change (∑ i, ∑ j,
    (∑ q : D.supportLabels, ∑ r : E.supportLabels, K q i * b.mass q r * L r j) *
      f (x i) (y j)) = _
  calc
    _ = ∑ j, ∑ i,
      (∑ q : D.supportLabels, K q i * (∑ r : E.supportLabels,
        b.mass q r * L r j)) * f (x i) (y j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = ∑ j, ∑ q : D.supportLabels,
        (∑ r : E.supportLabels, b.mass q r * L r j) * f q.1 (y j) := by
          apply Finset.sum_congr rfl
          intro j _
          simpa only [K] using FiniteWeightedDiagram.splittingKernel_linear_sum w x
            (fun q => ∑ r : E.supportLabels, b.mass q r * L r j)
            (fun q => f q (y j))
    _ = ∑ q : D.supportLabels, ∑ j,
        (∑ r : E.supportLabels, b.mass q r * L r j) * f q.1 (y j) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      convert FiniteWeightedDiagram.splittingKernel_linear_sum v y
        (fun r => b.mass q r) (fun r => f q.1 r) using 1
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- Every aggregated cell is the sum of the original cells in its coordinate fibers. -/
theorem aggregate_mass (a : FiniteWeightedBoundaryPlan w v)
    (x : I → Interior) (y : J → Interior)
    (q : (FiniteWeightedDiagram.ofIndexed w x).supportLabels)
    (r : (FiniteWeightedDiagram.ofIndexed v y).supportLabels) :
    (a.aggregate x y).mass q r =
      ∑ i, if x i = q.1 then ∑ j, if y j = r.1 then a.mass i j else 0 else 0 :=
  rfl

/-- Every lifted cell is split by the two normalized within-fiber kernels. -/
theorem splitLift_mass (x : I → Interior) (y : J → Interior)
    (b : FiniteWeightedBoundaryPlan
      (FiniteWeightedDiagram.ofIndexed w x).weights
      (FiniteWeightedDiagram.ofIndexed v y).weights) (i : I) (j : J) :
    (b.splitLift x y).mass i j =
      ∑ q : (FiniteWeightedDiagram.ofIndexed w x).supportLabels,
        ∑ r : (FiniteWeightedDiagram.ofIndexed v y).supportLabels,
          FiniteWeightedDiagram.splittingKernel w x q i * b.mass q r *
            FiniteWeightedDiagram.splittingKernel v y r j :=
  rfl

private theorem matrix_indicator_sum
    {D E : FiniteWeightedDiagram} (m : D.supportLabels → E.supportLabels → ℝ)
    (q₀ : D.supportLabels) (r₀ : E.supportLabels) :
    (∑ q : D.supportLabels, ∑ r : E.supportLabels,
      m q r * (if q.1 = q₀.1 then if r.1 = r₀.1 then 1 else 0 else 0)) =
      m q₀ r₀ := by
  rw [Finset.sum_eq_single q₀]
  · rw [Finset.sum_eq_single r₀]
    · simp
    · intro r _ hr
      simp [Subtype.coe_ne_coe.mpr hr]
    · simp
  · intro q _ hq
    simp [Subtype.coe_ne_coe.mpr hq]
  · simp

/-- Aggregation preserves every pair coefficient constant on coordinate fibers. -/
theorem aggregate_matrix_sum (a : FiniteWeightedBoundaryPlan w v)
    (x : I → Interior) (y : J → Interior) (f : Interior → Interior → ℝ) :
    (∑ q : (FiniteWeightedDiagram.ofIndexed w x).supportLabels,
      ∑ r : (FiniteWeightedDiagram.ofIndexed v y).supportLabels,
        (a.aggregate x y).mass q r * f q.1 r.1) =
      ∑ i, ∑ j, a.mass i j * f (x i) (y j) := by
  let D := FiniteWeightedDiagram.ofIndexed w x
  let E := FiniteWeightedDiagram.ofIndexed v y
  change (∑ q : D.supportLabels, ∑ r : E.supportLabels,
    (∑ i, if x i = q.1 then ∑ j, if y j = r.1 then a.mass i j else 0 else 0) *
      f q.1 r.1) = _
  calc
    _ = ∑ r : E.supportLabels, ∑ q : D.supportLabels,
        (∑ i, if x i = q.1 then ∑ j, if y j = r.1 then a.mass i j else 0 else 0) *
          f q.1 r.1 := Finset.sum_comm
    _ = ∑ r : E.supportLabels, ∑ i,
        (∑ j, if y j = r.1 then a.mass i j else 0) * f (x i) r.1 := by
      apply Finset.sum_congr rfl
      intro r _
      simpa only using FiniteWeightedDiagram.sum_fibers_weighted w x
        (fun i => ∑ j, if y j = r.1 then a.mass i j else 0)
        (fun q => f q r.1) (fun i hi => by
          have hw := FiniteWeightedDiagram.ofIndexed_weight_zero_outside w x i hi
          apply Finset.sum_eq_zero
          intro j _
          by_cases hj : y j = r.1 <;>
            simp [hj, mass_eq_zero_of_source_zero a i j hw])
    _ = ∑ i, ∑ r : E.supportLabels,
        (∑ j, if y j = r.1 then a.mass i j else 0) * f (x i) r.1 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact FiniteWeightedDiagram.sum_fibers_weighted v y _ _ (fun j hj =>
        mass_eq_zero_of_target_zero a i j
          (FiniteWeightedDiagram.ofIndexed_weight_zero_outside v y j hj))

/-- Aggregation retracts proportional splitting on every coalesced matrix cell. -/
theorem aggregate_splitLift_mass (x : I → Interior) (y : J → Interior)
    (b : FiniteWeightedBoundaryPlan
      (FiniteWeightedDiagram.ofIndexed w x).weights
      (FiniteWeightedDiagram.ofIndexed v y).weights)
    (q : (FiniteWeightedDiagram.ofIndexed w x).supportLabels)
    (r : (FiniteWeightedDiagram.ofIndexed v y).supportLabels) :
    ((b.splitLift x y).aggregate x y).mass q r = b.mass q r := by
  let f : Interior → Interior → ℝ := fun z t =>
    if z = q.1 then if t = r.1 then 1 else 0 else 0
  have h₁ := (b.splitLift x y).aggregate_matrix_sum x y f
  have h₂ := b.splitLift_matrix_sum x y f
  have hleft := matrix_indicator_sum ((b.splitLift x y).aggregate x y).mass q r
  have hright := matrix_indicator_sum b.mass q r
  calc
    ((b.splitLift x y).aggregate x y).mass q r =
        ∑ q' : (FiniteWeightedDiagram.ofIndexed w x).supportLabels,
          ∑ r' : (FiniteWeightedDiagram.ofIndexed v y).supportLabels,
            ((b.splitLift x y).aggregate x y).mass q' r' * f q'.1 r'.1 := hleft.symm
    _ = ∑ i, ∑ j, (b.splitLift x y).mass i j * f (x i) (y j) := h₁
    _ = ∑ q' : (FiniteWeightedDiagram.ofIndexed w x).supportLabels,
          ∑ r' : (FiniteWeightedDiagram.ofIndexed v y).supportLabels,
            b.mass q' r' * f q'.1 r'.1 := h₂
    _ = b.mass q r := hright

/-- Proportional splitting preserves the full powered boundary cost. -/
theorem powerCost_splitLift (x : I → Interior) (y : J → Interior)
    (b : FiniteWeightedBoundaryPlan
      (FiniteWeightedDiagram.ofIndexed w x).weights
      (FiniteWeightedDiagram.ofIndexed v y).weights) (p : ℝ) :
    (splitLift x y b).powerCost p (fun i => (x i).1) (fun j => (y j).1) =
      b.powerCost p
        (FiniteWeightedDiagram.ofIndexed w x).coordinates
        (FiniteWeightedDiagram.ofIndexed v y).coordinates := by
  let D := FiniteWeightedDiagram.ofIndexed w x
  let E := FiniteWeightedDiagram.ofIndexed v y
  let c : Interior → Interior → ℝ := fun q r => (finitePairCost q.1 r.1).toReal ^ p
  let d : Interior → ℝ := fun q => (diagonalCost q.1).toReal ^ p
  let e : Interior → ℝ := fun r => (diagonalCost r.1).toReal ^ p
  change (splitLift x y b).linearCost (fun i j => c (x i) (y j))
      (fun i => d (x i)) (fun j => e (y j)) =
    b.linearCost (fun q r => c q.1 r.1) (fun q => d q.1) (fun r => e r.1)
  rw [linearCost_reduced, linearCost_reduced]
  have hd := FiniteWeightedDiagram.ofIndexed_weighted_sum w x d
  have he := FiniteWeightedDiagram.ofIndexed_weighted_sum v y e
  have hc := splitLift_matrix_sum x y b (fun q r => c q r - d q - e r)
  simp only [FiniteWeightedDiagram.weights] at hd he ⊢
  rw [← hd, ← he, hc]

/-- Aggregating duplicate coordinates preserves pair, deletion and insertion charges. -/
theorem powerCost_aggregate (a : FiniteWeightedBoundaryPlan w v) (p : ℝ)
    (x : I → Interior) (y : J → Interior) :
    (a.aggregate x y).powerCost p
      (FiniteWeightedDiagram.ofIndexed w x).coordinates
      (FiniteWeightedDiagram.ofIndexed v y).coordinates =
      a.powerCost p (fun i => (x i).1) (fun j => (y j).1) := by
  let D := FiniteWeightedDiagram.ofIndexed w x
  let E := FiniteWeightedDiagram.ofIndexed v y
  let c : Interior → Interior → ℝ := fun q r => (finitePairCost q.1 r.1).toReal ^ p
  let d : Interior → ℝ := fun q => (diagonalCost q.1).toReal ^ p
  let e : Interior → ℝ := fun r => (diagonalCost r.1).toReal ^ p
  change (a.aggregate x y).linearCost (fun q r => c q.1 r.1)
      (fun q => d q.1) (fun r => e r.1) =
    a.linearCost (fun i j => c (x i) (y j)) (fun i => d (x i)) (fun j => e (y j))
  rw [linearCost_reduced, linearCost_reduced]
  have hd := FiniteWeightedDiagram.ofIndexed_weighted_sum w x d
  have he := FiniteWeightedDiagram.ofIndexed_weighted_sum v y e
  have hc := a.aggregate_matrix_sum x y (fun q r => c q r - d q - e r)
  simp only [FiniteWeightedDiagram.weights] at hd he
  simp only [FiniteWeightedDiagram.weights]
  rw [hd, he, hc]

end FiniteWeightedBoundaryPlan

namespace FiniteWeightedDiagram

/-- Indexed and coalesced powered optima agree for every real exponent. -/
theorem weightedPowerBoundaryTransportCost_ofIndexed (p : ℝ)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior) :
    weightedPowerBoundaryTransportCost p w v (fun i => (x i).1) (fun j => (y j).1) =
      powerBoundaryTransportCost p (ofIndexed w x) (ofIndexed v y) := by
  let D := ofIndexed w x
  let E := ofIndexed v y
  apply le_antisymm
  · obtain ⟨b, hb⟩ := exists_minimizing_powerPlan p D E
    calc
      weightedPowerBoundaryTransportCost p w v (fun i => (x i).1) (fun j => (y j).1) ≤
          (b.splitLift x y).powerCost p (fun i => (x i).1) (fun j => (y j).1) :=
        weightedPowerBoundaryTransportCost_le_plan _ _ _ _ _ _
      _ = powerBoundaryTransportCost p D E := by
        rw [FiniteWeightedBoundaryPlan.powerCost_splitLift, hb]
  · obtain ⟨a, ha⟩ := exists_minimizing_weightedPowerBoundaryPlan p w v
      (fun i => (x i).1) (fun j => (y j).1)
    calc
      powerBoundaryTransportCost p D E ≤
          (a.aggregate x y).powerCost p D.coordinates E.coordinates :=
        weightedPowerBoundaryTransportCost_le_plan _ _ _ _ _ _
      _ = weightedPowerBoundaryTransportCost p w v (fun i => (x i).1)
          (fun j => (y j).1) := by
        rw [FiniteWeightedBoundaryPlan.powerCost_aggregate, ha]

/-- The rooted optimized value has the same identity; rooted minimization is used for `p ≥ 1`. -/
theorem weightedPBoundaryTransportCost_ofIndexed (p : ℝ)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior) :
    weightedPBoundaryTransportCost p w v (fun i => (x i).1) (fun j => (y j).1) =
      pBoundaryTransportCost p (ofIndexed w x) (ofIndexed v y) := by
  exact congrArg (· ^ p⁻¹) (weightedPowerBoundaryTransportCost_ofIndexed p w v x y)

/-- Any indexed powered optimizer aggregates to an actual native optimizer. -/
theorem aggregate_minimizing_powerPlan (p : ℝ)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior)
    (a : FiniteWeightedBoundaryPlan w v)
    (ha : a.powerCost p (fun i => (x i).1) (fun j => (y j).1) =
      weightedPowerBoundaryTransportCost p w v (fun i => (x i).1) (fun j => (y j).1)) :
    (a.aggregate x y).powerCost p (ofIndexed w x).coordinates
      (ofIndexed v y).coordinates = powerBoundaryTransportCost p (ofIndexed w x)
      (ofIndexed v y) := by
  rw [FiniteWeightedBoundaryPlan.powerCost_aggregate, ha,
    weightedPowerBoundaryTransportCost_ofIndexed]

/-- Any native powered optimizer splits to an actual indexed optimizer. -/
theorem splitLift_minimizing_powerPlan (p : ℝ)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior)
    (b : FiniteWeightedBoundaryPlan (ofIndexed w x).weights (ofIndexed v y).weights)
    (hb : b.powerCost p (ofIndexed w x).coordinates
      (ofIndexed v y).coordinates = powerBoundaryTransportCost p (ofIndexed w x)
      (ofIndexed v y)) :
    (b.splitLift x y).powerCost p (fun i => (x i).1) (fun j => (y j).1) =
      weightedPowerBoundaryTransportCost p w v (fun i => (x i).1)
        (fun j => (y j).1) := by
  rw [FiniteWeightedBoundaryPlan.powerCost_splitLift, hb,
    weightedPowerBoundaryTransportCost_ofIndexed]

/-- An indexed plan realizing the rooted value aggregates to one realizing the native root.
For `p ≥ 1` these are rooted minimizers. -/
theorem aggregate_minimizing_pPlan (p : ℝ)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior)
    (a : FiniteWeightedBoundaryPlan w v)
    (ha : a.powerCost p (fun i => (x i).1) (fun j => (y j).1) ^ p⁻¹ =
      weightedPBoundaryTransportCost p w v (fun i => (x i).1) (fun j => (y j).1)) :
    (a.aggregate x y).powerCost p (ofIndexed w x).coordinates
      (ofIndexed v y).coordinates ^ p⁻¹ = pBoundaryTransportCost p (ofIndexed w x)
      (ofIndexed v y) := by
  rw [FiniteWeightedBoundaryPlan.powerCost_aggregate, ha,
    weightedPBoundaryTransportCost_ofIndexed]

/-- A native plan realizing the rooted value splits to one realizing the indexed root. -/
theorem splitLift_minimizing_pPlan (p : ℝ)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior)
    (b : FiniteWeightedBoundaryPlan (ofIndexed w x).weights (ofIndexed v y).weights)
    (hb : b.powerCost p (ofIndexed w x).coordinates
      (ofIndexed v y).coordinates ^ p⁻¹ = pBoundaryTransportCost p (ofIndexed w x)
      (ofIndexed v y)) :
    (b.splitLift x y).powerCost p (fun i => (x i).1) (fun j => (y j).1) ^ p⁻¹ =
      weightedPBoundaryTransportCost p w v (fun i => (x i).1)
        (fun j => (y j).1) := by
  rw [FiniteWeightedBoundaryPlan.powerCost_splitLift, hb,
    weightedPBoundaryTransportCost_ofIndexed]

/-- A rooted indexed minimizer exists and aggregates to a rooted native minimizer. -/
theorem exists_indexed_coalesced_minimizing_pPlans {p : ℝ} (hp : 1 ≤ p)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior) :
    ∃ a : FiniteWeightedBoundaryPlan w v,
      a.powerCost p (fun i => (x i).1) (fun j => (y j).1) ^ p⁻¹ =
        weightedPBoundaryTransportCost p w v (fun i => (x i).1)
          (fun j => (y j).1) ∧
      (a.aggregate x y).powerCost p (ofIndexed w x).coordinates
        (ofIndexed v y).coordinates ^ p⁻¹ = pBoundaryTransportCost p (ofIndexed w x)
          (ofIndexed v y) := by
  obtain ⟨a, ha⟩ := exists_minimizing_weightedPBoundaryPlan hp w v
    (fun i => (x i).1) (fun j => (y j).1)
  exact ⟨a, ha, aggregate_minimizing_pPlan p w v x y a ha⟩

/-- An indexed optimizer exists and its explicit aggregation is an optimizer of the coalesced diagram. -/
theorem exists_indexed_coalesced_minimizing_powerPlans (p : ℝ)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior) :
    ∃ a : FiniteWeightedBoundaryPlan w v,
      a.powerCost p (fun i => (x i).1) (fun j => (y j).1) =
        weightedPowerBoundaryTransportCost p w v (fun i => (x i).1)
          (fun j => (y j).1) ∧
      (a.aggregate x y).powerCost p (ofIndexed w x).coordinates
        (ofIndexed v y).coordinates = powerBoundaryTransportCost p (ofIndexed w x)
          (ofIndexed v y) := by
  obtain ⟨a, ha⟩ := exists_minimizing_weightedPowerBoundaryPlan p w v
    (fun i => (x i).1) (fun j => (y j).1)
  exact ⟨a, ha, aggregate_minimizing_powerPlan p w v x y a ha⟩

/-- Aggregating an existing unit-occurrence plan preserves its powered cost. -/
theorem powerCost_ofUnitPlan_aggregate (p : ℝ)
    (x : I → Interior) (y : J → Interior) (a : FiniteBoundaryPlan I J) :
    ((FiniteWeightedBoundaryPlan.ofUnitPlan a).aggregate x y).powerCost p
      (ofIndexed (fun _ : I => 1) x).coordinates
      (ofIndexed (fun _ : J => 1) y).coordinates =
      a.powerCost p (fun i => (x i).1) (fun j => (y j).1) := by
  rw [FiniteWeightedBoundaryPlan.powerCost_aggregate,
    FiniteWeightedBoundaryPlan.powerCost_ofUnitPlan]

/-- Splitting a native unit-mass diagram plan yields an existing unit-occurrence plan
of exactly the same powered cost. Its entries can be fractional. -/
theorem powerCost_splitLift_toUnitPlan (p : ℝ)
    (x : I → Interior) (y : J → Interior)
    (b : FiniteWeightedBoundaryPlan
      (ofIndexed (fun _ : I => 1) x).weights
      (ofIndexed (fun _ : J => 1) y).weights) :
    ((b.splitLift x y).toUnitPlan).powerCost p
      (fun i => (x i).1) (fun j => (y j).1) =
      b.powerCost p (ofIndexed (fun _ : I => 1) x).coordinates
        (ofIndexed (fun _ : J => 1) y).coordinates := by
  rw [FiniteWeightedBoundaryPlan.powerCost_toUnitPlan,
    FiniteWeightedBoundaryPlan.powerCost_splitLift]

end FiniteWeightedDiagram

end TDA.Persistence
