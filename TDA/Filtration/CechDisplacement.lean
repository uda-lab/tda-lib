import TDA.Filtration.Cech

set_option autoImplicit false

/-!
# Same-label displacement stability of Čech values

Two labelled families `p q : V → X` in a common pseudometric ambient space are compared
label by label. If every labelled point of a face moves by at most `ε`, the enclosing radius
at every ambient point and the Čech value of the face change by at most `ε`. On a finite
label type the displacement is the largest label-wise distance, with zero seed, so the
Čech values are `1`-Lipschitz in it. Under distance-compatible label metrics the Rips
pairwise discrepancy is at most twice the displacement.

These are same-label statements: faces are label sets and repeated labels are allowed.
No Hausdorff distance between the images is involved.
-/

universe w v

namespace TDA.Filtration.Cech

open TDA.Simplicial

variable {X : Type w} {V : Type v} [PseudoMetricSpace X]

/-- Moving each point of `s` by at most `ε ≥ 0` enlarges the radius at `x` by at most `ε`.
The sign condition is needed only for the empty set. -/
theorem radiusAt_le_radiusAt_add_of_dist_le (p q : V → X) (x : X) (s : Finset V) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ v ∈ s, dist (p v) (q v) ≤ ε) :
    radiusAt p x s ≤ radiusAt q x s + ε := by
  refine (radiusAt_le_iff p x s _).2 ⟨add_nonneg (radiusAt_nonneg q x s) hε, fun v hv => ?_⟩
  calc dist x (p v) ≤ dist x (q v) + dist (q v) (p v) := dist_triangle _ _ _
    _ ≤ radiusAt q x s + ε :=
      add_le_add (dist_le_radiusAt q x hv) ((dist_comm _ _).trans_le (h v hv))

theorem abs_radiusAt_sub_le_of_dist_le (p q : V → X) (x : X) (s : Finset V) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ v ∈ s, dist (p v) (q v) ≤ ε) :
    |radiusAt p x s - radiusAt q x s| ≤ ε := by
  have h₁ := radiusAt_le_radiusAt_add_of_dist_le p q x s hε h
  have h₂ := radiusAt_le_radiusAt_add_of_dist_le q p x s hε
    fun v hv => (dist_comm _ _).trans_le (h v hv)
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- On an actual face, a bound on the displacement of its points bounds the Čech value
change; no sign condition is needed because the face is nonempty. -/
theorem filter_value_le_add_of_dist_le (p q : V → X) {ε : ℝ}
    (s : TotalFace (Rips.fullComplex V)) (h : ∀ v ∈ s.val, dist (p v) (q v) ≤ ε) :
    (filter p).value s ≤ (filter q).value s + ε := by
  obtain ⟨v₀, hv₀⟩ : s.val.Nonempty := s.property
  have hε : 0 ≤ ε := dist_nonneg.trans (h v₀ hv₀)
  have : Nonempty X := ⟨p v₀⟩
  have key : (filter p).value s - ε ≤ (filter q).value s := by
    rw [filter_value q]
    refine le_ciInf fun x => ?_
    have := (filter_value_le_radiusAt p s x).trans
      (radiusAt_le_radiusAt_add_of_dist_le p q x s.val hε h)
    linarith
  linarith

theorem abs_filter_value_sub_le_of_dist_le (p q : V → X) {ε : ℝ}
    (s : TotalFace (Rips.fullComplex V)) (h : ∀ v ∈ s.val, dist (p v) (q v) ≤ ε) :
    |(filter p).value s - (filter q).value s| ≤ ε := by
  have h₁ := filter_value_le_add_of_dist_le p q s h
  have h₂ := filter_value_le_add_of_dist_le q p s
    fun v hv => (dist_comm _ _).trans_le (h v hv)
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

section FiniteLabels

variable [Fintype V]

/-- The same-label displacement: the largest label-wise distance, zero on an empty carrier. -/
noncomputable def displacement (p q : V → X) : ℝ :=
  Finset.univ.fold max 0 (fun v => dist (p v) (q v))

theorem displacement_nonneg (p q : V → X) : 0 ≤ displacement p q :=
  (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

theorem dist_le_displacement (p q : V → X) (v : V) : dist (p v) (q v) ≤ displacement p q :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨v, Finset.mem_univ _, le_rfl⟩)

theorem displacement_le_iff (p q : V → X) (ε : ℝ) :
    displacement p q ≤ ε ↔ 0 ≤ ε ∧ ∀ v, dist (p v) (q v) ≤ ε :=
  (Finset.fold_max_le ε).trans (and_congr_right' ⟨fun h v => h v (Finset.mem_univ v),
    fun h v _ => h v⟩)

theorem displacement_comm (p q : V → X) : displacement p q = displacement q p := by
  have key : ∀ p q : V → X, displacement p q ≤ displacement q p := fun p q =>
    (displacement_le_iff p q _).2 ⟨displacement_nonneg q p,
      fun v => (dist_comm _ _).trans_le (dist_le_displacement q p v)⟩
  exact le_antisymm (key p q) (key q p)

@[simp] theorem displacement_self (p : V → X) : displacement p p = 0 :=
  le_antisymm ((displacement_le_iff p p 0).2 ⟨le_rfl, fun _ => (dist_self _).le⟩)
    (displacement_nonneg p p)

@[simp] theorem displacement_of_isEmpty [IsEmpty V] (p q : V → X) : displacement p q = 0 := by
  rw [displacement, Finset.univ_eq_empty, Finset.fold_empty]

/-- Čech values are `1`-Lipschitz in the same-label displacement. -/
theorem abs_filter_value_sub_le_displacement (p q : V → X)
    (s : TotalFace (Rips.fullComplex V)) :
    |(filter p).value s - (filter q).value s| ≤ displacement p q :=
  abs_filter_value_sub_le_of_dist_le p q s fun v _ => dist_le_displacement p q v

/-- Under distance-compatible label metrics, the Rips discrepancy is at most twice the
displacement. -/
theorem pairwiseDiscrepancy_le_two_mul_displacement (d e : MetricSpace V) (p q : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (he : ∀ v w, e.dist v w = dist (q v) (q w)) :
    Rips.pairwiseDiscrepancy d e ≤ 2 * displacement p q := by
  classical
  refine (Finset.fold_max_le _).2
    ⟨mul_nonneg zero_le_two (displacement_nonneg p q), ?_⟩
  rintro ⟨v, w⟩ -
  dsimp only
  rw [hd, he, ← Real.dist_eq]
  calc dist (dist (p v) (p w)) (dist (q v) (q w)) ≤ dist (p v) (q v) + dist (p w) (q w) :=
        dist_dist_dist_le _ _ _ _
    _ ≤ displacement p q + displacement p q :=
        add_le_add (dist_le_displacement p q v) (dist_le_displacement p q w)
    _ = 2 * displacement p q := by ring

/-- Rips diameters are `2`-Lipschitz in the same-label displacement. -/
theorem abs_diameter_sub_le_two_mul_displacement (d e : MetricSpace V) (p q : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (he : ∀ v w, e.dist v w = dist (q v) (q w))
    (s : Finset V) :
    |Rips.diameter d s - Rips.diameter e s| ≤ 2 * displacement p q :=
  (Rips.abs_diameter_sub_le_pairwiseDiscrepancy d e s).trans
    (pairwiseDiscrepancy_le_two_mul_displacement d e p q hd he)

end FiniteLabels

end TDA.Filtration.Cech
