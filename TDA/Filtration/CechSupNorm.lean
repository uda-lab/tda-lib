import TDA.Filtration.CechWitness
import TDA.Filtration.OrderingEquivalent
import Mathlib.Topology.MetricSpace.Pseudo.Pi

set_option autoImplicit false

/-!
# Sup-norm Čech complexes equal Rips complexes

In a finite product `ι → ℝ` with the sup metric, closed balls are axis-parallel boxes, and
boxes have the one-dimensional Helly property coordinatewise. If the points of a nonempty
finite label set are pairwise within `2 * r`, the point whose `i`-th coordinate is the
largest `i`-th label coordinate minus `r` lies within `r` of every label. Hence the second
sandwich inclusion is an equality, `Čech_r = Rips_{2r}`, every Čech value is exactly half
the Rips value, and the Čech and Rips filters are ordering-equivalent.

The ambient metric here is mathlib's sup metric on `ι → ℝ`, not the Euclidean metric of
`EuclideanSpace ℝ ι`. The index type may be empty. The line `ℝ` is reduced to `Fin 1 → ℝ`
by the witness-space transfer.
-/

universe v w

namespace TDA.Filtration.Cech

open TDA.Simplicial

variable {V : Type v} {ι : Type w} [Fintype ι]

/-- The coordinatewise Helly witness: the largest `i`-th label coordinate minus `r`. -/
noncomputable def supNormWitness (p : V → ι → ℝ) (r : ℝ) (s : Finset V) (hs : s.Nonempty) :
    ι → ℝ :=
  fun i => s.sup' hs (fun v => p v i) - r

private theorem nonneg_of_pairwise (p : V → ι → ℝ) {r : ℝ} {s : Finset V} {v : V}
    (hv : v ∈ s) (h : ∀ v ∈ s, ∀ w ∈ s, dist (p v) (p w) ≤ 2 * r) : 0 ≤ r := by
  have h0 := h v hv v hv
  rw [dist_self] at h0
  linarith

/-- If the labels are pairwise within `2 * r`, the coordinatewise witness is within `r` of
each of them. -/
theorem dist_supNormWitness_le (p : V → ι → ℝ) {r : ℝ} {s : Finset V} (hs : s.Nonempty)
    (h : ∀ v ∈ s, ∀ w ∈ s, dist (p v) (p w) ≤ 2 * r) {v : V} (hv : v ∈ s) :
    dist (supNormWitness p r s hs) (p v) ≤ r := by
  have hr := nonneg_of_pairwise p hv h
  refine (dist_pi_le_iff hr).2 fun i => ?_
  rw [Real.dist_eq, abs_le]
  have hle : p v i ≤ s.sup' hs (fun w => p w i) := Finset.le_sup' (fun w => p w i) hv
  have hge : s.sup' hs (fun w => p w i) ≤ p v i + 2 * r := by
    refine Finset.sup'_le hs _ fun w hw => ?_
    have h1 : dist (p w i) (p v i) ≤ 2 * r :=
      (dist_le_pi_dist (p w) (p v) i).trans (h w hw v hv)
    rw [Real.dist_eq] at h1
    linarith [le_abs_self (p w i - p v i)]
  simp only [supNormWitness]
  constructor <;> linarith

/-- Helly in the sup-norm product: a label set is a Čech face at radius `r` exactly when it
is nonempty and its points are pairwise within `2 * r`. -/
theorem mem_complex_iff_pairwise (p : V → ι → ℝ) (r : ℝ) (s : Finset V) :
    s ∈ complex p r ↔ s.Nonempty ∧ ∀ v ∈ s, ∀ w ∈ s, dist (p v) (p w) ≤ 2 * r := by
  constructor
  · intro hs
    exact ⟨((mem_complex_iff p r s).1 hs).1,
      fun v hv w hw => dist_le_two_mul_of_mem_complex p hs hv hw⟩
  · rintro ⟨hs, h⟩
    exact (mem_complex_iff p r s).2
      ⟨hs, supNormWitness p r s hs, fun v hv => dist_supNormWitness_le p hs h hv⟩

/-- Pairwise distances at most `2 * r` bound the sup-norm Čech value by `r`. -/
theorem filter_value_le_of_pairwise (p : V → ι → ℝ) {r : ℝ}
    (s : TotalFace (Rips.fullComplex V))
    (h : ∀ v ∈ s.val, ∀ w ∈ s.val, dist (p v) (p w) ≤ 2 * r) :
    (filter p).value s ≤ r := by
  obtain ⟨v₀, hv₀⟩ : s.val.Nonempty := s.property
  exact (filter_value_le_radiusAt p s (supNormWitness p r s.val s.property)).trans
    ((radiusAt_le_iff _ _ _ _).2 ⟨nonneg_of_pairwise p hv₀ h,
      fun v hv => dist_supNormWitness_le p s.property h hv⟩)

/-- The sup-norm Čech complex at radius `r` is the Rips sublevel at `2 * r`. -/
theorem complex_eq_ripsSublevel_two_mul (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (r : ℝ) :
    complex p r = (Rips.filter d).sublevel (2 * r) := by
  refine le_antisymm (complex_le_ripsSublevel_two_mul d p hd r) fun s hs => ?_
  obtain ⟨hsn, h⟩ := (Rips.mem_sublevel_iff d (2 * r) s).1 hs
  exact (mem_complex_iff_pairwise p r s).2 ⟨hsn, fun v hv w hw => by
    rw [← hd]
    exact h v hv w hw⟩

/-- Every sup-norm Čech value is exactly half the Rips value. -/
theorem filter_value_eq_rips_div_two (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (s : TotalFace (Rips.fullComplex V)) :
    (filter p).value s = (Rips.filter d).value s / 2 := by
  have hup : (filter p).value s ≤ (Rips.filter d).value s / 2 := by
    refine filter_value_le_of_pairwise p s fun v hv w hw => ?_
    rw [← hd, Rips.filter_value]
    have := Rips.dist_le_diameter d hv hw
    linarith
  have hlo := rips_le_two_mul_filter_value d p hd s
  linarith

/-- The sup-norm Čech sublevel at `r` is the Rips sublevel at `2 * r`. -/
theorem sublevel_eq_ripsSublevel_two_mul (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (r : ℝ) :
    (filter p).sublevel r = (Rips.filter d).sublevel (2 * r) := by
  apply le_antisymm
  · intro s hs
    obtain ⟨hsK, hval⟩ := (FilterFunction.mem_sublevel_iff _ r s).1 hs
    rw [filter_value_eq_rips_div_two d p hd] at hval
    exact (FilterFunction.mem_sublevel_iff _ _ s).2 ⟨hsK, by linarith⟩
  · intro s hs
    obtain ⟨hsK, hval⟩ := (FilterFunction.mem_sublevel_iff _ _ s).1 hs
    refine (FilterFunction.mem_sublevel_iff _ r s).2 ⟨hsK, ?_⟩
    rw [filter_value_eq_rips_div_two d p hd]
    linarith

/-- The sup-norm Čech filter and the Rips filter are ordering-equivalent. -/
theorem orderingEquivalent_rips (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    OrderingEquivalent (filter p) (Rips.filter d) := by
  intro s t
  rw [filter_value_eq_rips_div_two d p hd s, filter_value_eq_rips_div_two d p hd t]
  constructor <;> intro h <;> linarith

/-! ### The line -/

/-- The line as the one-coordinate sup-norm product. -/
private def lineEmbed : ℝ → Fin 1 → ℝ := fun x _ => x

private theorem isometry_lineEmbed : Isometry lineEmbed :=
  Isometry.of_dist_eq fun x y => dist_pi_const x y

private theorem lipschitzWith_eval_zero : LipschitzWith 1 fun y : Fin 1 → ℝ => y 0 :=
  LipschitzWith.mk_one fun x y => dist_le_pi_dist x y 0

private theorem complex_lineEmbed (q : V → ℝ) (r : ℝ) :
    complex (lineEmbed ∘ q) r = complex q r :=
  complex_comp_eq_of_retraction isometry_lineEmbed lipschitzWith_eval_zero
    (fun _ => rfl) r

private theorem filter_lineEmbed_value (q : V → ℝ) (s : TotalFace (Rips.fullComplex V)) :
    (filter (lineEmbed ∘ q)).value s = (filter q).value s :=
  filter_comp_value_eq_of_retraction isometry_lineEmbed lipschitzWith_eval_zero
    (fun _ => rfl) s

private theorem dist_lineEmbed (q : V → ℝ) (v w : V) :
    dist ((lineEmbed ∘ q) v) ((lineEmbed ∘ q) w) = dist (q v) (q w) :=
  isometry_lineEmbed.dist_eq (q v) (q w)

/-- Helly on the line: a label set is a Čech face at radius `r` exactly when it is nonempty
and its points are pairwise within `2 * r`. -/
theorem mem_complex_iff_pairwise_real (q : V → ℝ) (r : ℝ) (s : Finset V) :
    s ∈ complex q r ↔ s.Nonempty ∧ ∀ v ∈ s, ∀ w ∈ s, dist (q v) (q w) ≤ 2 * r := by
  rw [← complex_lineEmbed, mem_complex_iff_pairwise]
  simp only [dist_lineEmbed]

/-- On the line, the Čech complex at radius `r` is the Rips sublevel at `2 * r`. -/
theorem complex_eq_ripsSublevel_two_mul_real (d : MetricSpace V) (q : V → ℝ)
    (hd : ∀ v w, d.dist v w = dist (q v) (q w)) (r : ℝ) :
    complex q r = (Rips.filter d).sublevel (2 * r) := by
  rw [← complex_lineEmbed]
  exact complex_eq_ripsSublevel_two_mul d (lineEmbed ∘ q)
    (fun v w => (hd v w).trans (dist_lineEmbed q v w).symm) r

/-- On the line, every Čech value is exactly half the Rips value. -/
theorem filter_value_eq_rips_div_two_real (d : MetricSpace V) (q : V → ℝ)
    (hd : ∀ v w, d.dist v w = dist (q v) (q w)) (s : TotalFace (Rips.fullComplex V)) :
    (filter q).value s = (Rips.filter d).value s / 2 := by
  rw [← filter_lineEmbed_value]
  exact filter_value_eq_rips_div_two d (lineEmbed ∘ q)
    (fun v w => (hd v w).trans (dist_lineEmbed q v w).symm) s

end TDA.Filtration.Cech
