import TDA.Topology.SubdivisionRealization
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Mesh of realized barycentric subdivisions

With at most `d + 1` vertices per original face, each subdivision multiplies the
vertex vertex_mesh bound by `d / (d + 1)`. Convexity extends it to whole closed faces;
measuring through a shared vertex bounds the diameter of a closed closedStarImage.
-/

namespace TDA.Topology.SubdivisionRealization

open TDA.Simplicial Convexity
noncomputable section
universe u

section Barycenters
open Finset Metric
open scoped BigOperators
variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [DecidableEq V] in
private theorem barycenter_mem (p : V → E) {A : Finset V} (hA : A.Nonempty) {S : Set E}
    (hS : Convex ℝ S) (hp : ∀ i ∈ A, p i ∈ S) : barycenter p A ∈ S := by
  simpa [barycenter, Finset.centerMass] using
    hS.centerMass_mem (t := A) (w := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      (by simpa using (show (0 : ℝ) < A.card by exact_mod_cast hA.card_pos)) hp

private theorem dist_barycenter_le (p : V → E) {A B : Finset V} (ha : A.Nonempty) (hab : A ⊆ B)
    {D : ℝ} (hp : ∀ i ∈ B, ∀ j ∈ B, dist (p i) (p j) ≤ D) :
    dist (barycenter p B) (barycenter p A) ≤ ((B \ A).card : ℝ) / B.card * D := by
  have hb := ha.mono hab
  have hba : (B.card : ℝ) ≠ 0 := by exact_mod_cast hb.card_ne_zero
  have haa : (A.card : ℝ) ≠ 0 := by exact_mod_cast ha.card_ne_zero
  have zeroSum : (∑ i ∈ A, (p i - barycenter p A)) = 0 := by
    rw [sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, barycenter, smul_smul]
    simp [haa]
  have rem : (∑ i ∈ B \ A, (p i - barycenter p A)) = ∑ i ∈ B, (p i - barycenter p A) := by
    simpa only [zeroSum, add_zero] using
      (Finset.sum_sdiff hab : (∑ i ∈ B \ A, (p i - barycenter p A)) + ∑ i ∈ A, (p i - barycenter p A) = _)
  have diff : barycenter p B - barycenter p A = (B.card : ℝ)⁻¹ • ∑ i ∈ B \ A, (p i - barycenter p A) := by
    rw [rem, sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul]
    simp [hba, barycenter]
  have hnorm (i) (hi : i ∈ B \ A) : ‖p i - barycenter p A‖ ≤ D := by
    have := barycenter_mem p ha (convex_closedBall (p i) D) (fun j hj => hp j (hab hj) i (mem_sdiff.mp hi).1)
    rwa [← dist_eq_norm, dist_comm]
  rw [dist_eq_norm, diff, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (B.card : ℝ)⁻¹ * ∑ i ∈ B \ A, ‖p i - barycenter p A‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity)
    _ ≤ (B.card : ℝ)⁻¹ * ∑ _i ∈ B \ A, D :=
      mul_le_mul_of_nonneg_left (sum_le_sum hnorm) (by positivity)
    _ = _ := by simp [div_eq_inv_mul, mul_assoc]

private theorem mesh_step (p : V → E) {A B : Finset V} (ha : A.Nonempty) (hab : A ⊆ B)
    {d : ℕ} (hd : B.card ≤ d + 1) {D : ℝ} (hD : 0 ≤ D)
    (hp : ∀ i ∈ B, ∀ j ∈ B, dist (p i) (p j) ≤ D) :
    dist (barycenter p B) (barycenter p A) ≤ ((d : ℝ) / (d + 1)) * D := by
  apply (dist_barycenter_le p ha hab hp).trans
  apply mul_le_mul_of_nonneg_right _ hD
  have hb : (0 : ℝ) < B.card := by exact_mod_cast (ha.mono hab).card_pos
  have ha' : (1 : ℝ) ≤ A.card := by exact_mod_cast ha.card_pos
  rw [card_sdiff_of_subset hab, Nat.cast_sub (card_le_card hab)]
  apply (div_le_div_iff₀ hb (by positivity : (0 : ℝ) < d + 1)).mpr
  have hd' : (B.card : ℝ) ≤ d + 1 := by exact_mod_cast hd
  nlinarith [mul_nonneg (sub_nonneg.mpr ha') (show (0 : ℝ) ≤ d + 1 by positivity)]

private theorem subdivision_vertex_mesh [Fintype V] (Q : PreAbstractSimplicialComplex V) (p : V → E)
    (d : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hsize : ∀ T ∈ Q, T.card ≤ d + 1)
    (hdist : ∀ T ∈ Q, ∀ i ∈ T, ∀ j ∈ T, dist (p i) (p j) ≤ D)
    (F : Finset (Finset V)) (hF : F ∈ barycentricSubdivision Q) :
    F.card ≤ d + 1 ∧ ∀ A ∈ F, ∀ B ∈ F, dist (barycenter p A) (barycenter p B) ≤ (d : ℝ) / (d + 1) * D := by
  have hm (A) (hA : A ∈ F) := (hF.2.1 A hA).1
  have hpair (A) (hA : A ∈ F) (B) (hB : B ∈ F) (hs : A ⊆ B) :=
    mesh_step p (Q.isRelLowerSet_faces (hm A hA)).1 hs (hsize B (hm B hB)) hD (hdist B (hm B hB))
  constructor
  · have h : F.card ≤ (Finset.Icc 1 (d + 1)).card := by
      apply Finset.card_le_card_of_injOn Finset.card
      · intro A hA
        exact Finset.mem_Icc.mpr ⟨(Q.isRelLowerSet_faces (hm A hA)).1.card_pos, hsize A (hm A hA)⟩
      · intro A hA B hB he
        rcases hF.2.2 A hA B hB with h | h
        · exact Finset.eq_of_subset_of_card_le h he.ge
        · exact (Finset.eq_of_subset_of_card_le h he.le).symm
    simpa [Nat.card_Icc] using h
  · intro A hA B hB
    rcases hF.2.2 A hA B hB with h | h
    · rw [dist_comm]
      exact hpair A hA B hB h
    · exact hpair B hB A hA h

end Barycenters

variable {V : Type u} [Fintype V] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem vertex_mesh (K : PreAbstractSimplicialComplex V) (p : V → E) (d : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ A ∈ K, A.card ≤ d + 1) (hm : ∀ A ∈ K, ∀ v ∈ A, ∀ w ∈ A, dist (p v) (p w) ≤ M) :
    ∀ n (F : Finset (Vertex V n)), F ∈ complex K n →
      F.card ≤ d + 1 ∧ ∀ v ∈ F, ∀ w ∈ F,
        dist (vertexPosition p n v) (vertexPosition p n w) ≤ ((d : ℝ) / (d + 1)) ^ n * M := by
  intro n
  induction n with
  | zero =>
    intro F hf
    refine ⟨hc F hf, ?_⟩
    intro v hv w hw
    simpa only [vertexPosition, pow_zero, one_mul] using hm F hf v hv w hw
  | succ n ih =>
    intro F hf
    classical
    have h := subdivision_vertex_mesh (complex K n) (vertexPosition p n) d
      (mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ (d : ℝ) / (d + 1) by positivity) n) hM)
      (fun T hT => (ih T hT).1) (fun T hT => (ih T hT).2) F hf
    exact ⟨h.1, fun v hv w hw => by simpa only [vertexPosition, pow_succ', mul_assoc] using h.2 v hv w hw⟩

/-- Image in the original placement of the entire closed fine face, including its boundary. -/
def faceImage (K : PreAbstractSimplicialComplex V) (p : V → E) (n : ℕ) (F : Finset (Vertex V n)) : Set E :=
  realize p K n '' {x | x.val.weights.support ⊆ F}

/-- Union of the realized closed faces incident to a fine vertex; empty for an unused label. -/
def closedStarImage (K : PreAbstractSimplicialComplex V) (p : V → E) (n : ℕ) (v : Vertex V n) : Set E :=
  {y | ∃ F ∈ complex K n, v ∈ F ∧ y ∈ faceImage K p n F}

private theorem faceImage_subset_convexHull (K : PreAbstractSimplicialComplex V) (p : V → E) (n : ℕ)
    (F : Finset (Vertex V n)) :
    faceImage K p n F ⊆ convexHull ℝ (vertexPosition p n '' (F : Set (Vertex V n))) := by
  classical
  rintro y ⟨x, hx, rfl⟩
  change (∑ w, x.val.weights w • vertexPosition p n w) ∈ _
  rw [← Finset.sum_subset (Finset.subset_univ x.val.weights.support)
    (fun w _ hw => by simp [Finsupp.notMem_support_iff.mp hw])]
  exact (convex_convexHull ℝ _).sum_mem (fun _ _ => x.val.weights_nonneg _) x.val.total
    (fun w hw => subset_convexHull ℝ _ (Set.mem_image_of_mem (vertexPosition p n) (hx hw)))

/-- The image of a fine face is bounded, so its metric diameter bounds all pairwise distances. -/
theorem isBounded_faceImage (K : PreAbstractSimplicialComplex V) (p : V → E) (n : ℕ)
    (F : Finset (Vertex V n)) : Bornology.IsBounded (faceImage K p n F) :=
  (isBounded_convexHull.mpr ((F.finite_toSet.image _).isBounded)).subset
    (faceImage_subset_convexHull K p n F)

/-- The closed star lies in the convex hull of the finitely many placed vertices at its depth. -/
theorem isBounded_closedStarImage (K : PreAbstractSimplicialComplex V) (p : V → E) (n : ℕ)
    (v : Vertex V n) : Bornology.IsBounded (closedStarImage K p n v) := by
  apply (isBounded_convexHull.mpr (Set.finite_range (vertexPosition p n)).isBounded).subset
  rintro x ⟨F, _, _, hx⟩
  exact convexHull_mono (Set.image_subset_range _ _) (faceImage_subset_convexHull K p n F hx)

/-- Face and closed-star diameters in the original metric, for faces of dimension at most `d`. -/
theorem diam_le (K : PreAbstractSimplicialComplex V) (p : V → E) (d : ℕ)
    {M : ℝ} (hM : 0 ≤ M) (hc : ∀ F ∈ K, F.card ≤ d + 1)
    (hp : ∀ F ∈ K, ∀ i ∈ F, ∀ j ∈ F, dist (p i) (p j) ≤ M) (n : ℕ) :
    (∀ F ∈ complex K n, Metric.diam (faceImage K p n F) ≤ ((d : ℝ) / (d + 1)) ^ n * M) ∧
    (∀ v, Metric.diam (closedStarImage K p n v) ≤ 2 * (((d : ℝ) / (d + 1)) ^ n * M)) := by
  let b := ((d : ℝ) / (d + 1)) ^ n * M
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hpair (F) (hf : F ∈ complex K n) (x) (hx : x ∈ convexHull ℝ (vertexPosition p n '' (F : Set _)))
      (y) (hy : y ∈ convexHull ℝ (vertexPosition p n '' (F : Set _))) : dist x y ≤ b := by
    obtain ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, hle⟩ := convexHull_exists_dist_ge2 hx hy
    exact hle.trans ((vertex_mesh K p d hM hc hp n F hf).2 i hi j hj)
  constructor
  · intro F hf
    exact Metric.diam_le_of_forall_dist_le hb (fun x hx y hy =>
      hpair F hf x (faceImage_subset_convexHull K p n F hx) y (faceImage_subset_convexHull K p n F hy))
  · intro v
    have rad (x) (hx : x ∈ closedStarImage K p n v) : dist x (vertexPosition p n v) ≤ b := by
      obtain ⟨F, hf, hv, hx'⟩ := hx
      exact hpair F hf x (faceImage_subset_convexHull K p n F hx') _ (subset_convexHull ℝ _
        (Set.mem_image_of_mem (vertexPosition p n) hv))
    exact Metric.diam_le_of_forall_dist_le (mul_nonneg (by norm_num) hb)
      (fun x hx y hy => (dist_triangle_right x y (vertexPosition p n v)).trans
        (by linarith [rad x hx, rad y hy]))

/-- One subdivision depth makes every realized face and closed star small at all later depths. -/
theorem eventually_diam_lt (K : PreAbstractSimplicialComplex V) (p : V → E) (d : ℕ)
    {M : ℝ} (hM : 0 ≤ M) (hc : ∀ F ∈ K, F.card ≤ d + 1)
    (hp : ∀ F ∈ K, ∀ i ∈ F, ∀ j ∈ F, dist (p i) (p j) ≤ M) {ε : ℝ} (he : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      (∀ F ∈ complex K n, Metric.diam (faceImage K p n F) < ε) ∧
      (∀ v, Metric.diam (closedStarImage K p n v) < ε) := by
  let q := (d : ℝ) / (d + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hlt : q < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have ht : Filter.Tendsto (fun n : ℕ => q ^ n * M) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hlt).mul_const M
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const (half_pos he))
  refine ⟨N, fun n hn => ?_⟩
  have b := diam_le K p d hM hc hp n
  exact ⟨fun F hf => (b.1 F hf).trans_lt ((hN n hn).trans (half_lt_self he)),
    fun v => (b.2 v).trans_lt (by change 2 * (q ^ n * M) < ε; linarith [hN n hn])⟩

/-- In dimension zero, all face and closed-star images have diameter zero, already at depth zero. -/
theorem diam_eq_zero_of_card_le_one (K : PreAbstractSimplicialComplex V) (p : V → E) (h : ∀ F ∈ K, F.card ≤ 1)
    (n : ℕ) : (∀ F ∈ complex K n, Metric.diam (faceImage K p n F) = 0) ∧
      (∀ v, Metric.diam (closedStarImage K p n v) = 0) := by
  have b := diam_le K p 0 (M := 0) le_rfl h (fun F hF i hi j hj => by
    rw [Finset.card_le_one.mp (h F hF) i hi j hj, dist_self]) n
  simp only [mul_zero] at b
  exact ⟨fun F hf => le_antisymm (b.1 F hf) Metric.diam_nonneg,
    fun v => le_antisymm (b.2 v) Metric.diam_nonneg⟩

/-- A shared fine face has the same image in either realization. -/
theorem faceImage_eq_of_mem {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (p : V → E)
    (n : ℕ) {F : Finset (Vertex V n)} (hf : F ∈ complex K n) : faceImage K p n F = faceImage L p n F := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Realization.incl (complex_mono h n) x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, ((complex K n).isRelLowerSet_faces hf).2 hx x.val.support_weights_nonempty⟩, hx, rfl⟩

/-- Every incident face of the subcomplex contributes to the larger closed star. -/
theorem closedStarImage_mono {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (p : V → E)
    (n : ℕ) (v : Vertex V n) : closedStarImage K p n v ⊆ closedStarImage L p n v := by
  rintro y ⟨F, hF, hv, hy⟩
  exact ⟨F, complex_mono h n hF, hv, faceImage_eq_of_mem h p n hF ▸ hy⟩

/-- A single labeling of the common fine vertex type restricts with its star-containment property. -/
theorem closedStarImage_subset_of_labels {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (p : V → E) (n : ℕ)
    {I : Type*} (U : I → Set E) (a : Vertex V n → I) (ha : ∀ v, closedStarImage L p n v ⊆ U (a v)) :
    ∀ v, closedStarImage K p n v ⊆ U (a v) := fun v => (closedStarImage_mono h p n v).trans (ha v)

open Classical in
/-- Standard unit-coordinate placement, with the finite supremum metric on `V → ℝ`. -/
def unitVertex (v i : V) : ℝ := if i = v then 1 else 0

/-- The original unit-coordinate placement has mesh at most one. -/
theorem dist_unitVertex_le_one (v w : V) : dist (unitVertex v) (unitVertex w) ≤ 1 := by
  apply (dist_pi_le_iff zero_le_one).2
  intro i
  classical
  simp only [unitVertex, Real.dist_eq]
  split <;> split <;> norm_num

/-- Coordinates of the standard placement are the weights of the actual barycenter projection. -/
theorem realize_unitVertex_apply (K : PreAbstractSimplicialComplex V) (n : ℕ) (x : Realization (complex K n)) (i : V) :
    realize unitVertex K n x i = (barycentricProjection K n x).val.weights i := by
  rw [realize_eq_comp_projection]
  change (∑ v, (barycentricProjection K n x).val.weights v • unitVertex v) i = _
  classical
  simp [Finset.sum_apply, Pi.smul_apply, unitVertex, smul_eq_mul]

end
end TDA.Topology.SubdivisionRealization
