import TDA.Topology.Realization
import TDA.Simplicial.BarycentricHomology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Order.Preorder.Finite

/-!
# Realization of iterated barycentric subdivision

The labels at each depth depend only on the original vertex type. The projection
assigns each face its barycenter and extends by affine interpolation. It commutes
with the support-preserving inclusion of every subcomplex.
-/

namespace TDA.Topology.SubdivisionRealization

open TDA.Simplicial Convexity
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ambient labels at subdivision depth `n`, shared by every subcomplex on `V`. Not reducible:
`Vertex V (n + 1)` is `Finset (Vertex V n)` by definition, but instances on finsets do not
apply to it, so the label orders of `SubdivisionLastVertex` stay on these labels. -/
def Vertex (V : Type u) : ℕ → Type u
  | 0 => V
  | n + 1 => Finset (Vertex V n)

instance instFintypeVertex [Fintype V] : (n : ℕ) → Fintype (Vertex V n)
  | 0 => ‹Fintype V›
  | n + 1 => letI := instFintypeVertex n; inferInstanceAs (Fintype (Finset (Vertex V n)))

/-- Mean of the placed vertices of a finite face. -/
def barycenter (p : V → E) (A : Finset V) : E :=
  (A.card : ℝ)⁻¹ • ∑ i ∈ A, p i

variable [Fintype V]

/-- Iterate the mass-zero barycentric subdivision on the common ambient labels. -/
def complex (K : PreAbstractSimplicialComplex V) : (n : ℕ) → PreAbstractSimplicialComplex (Vertex V n)
  | 0 => K
  | n + 1 => barycentricSubdivision (complex K n)

/-- A subcomplex inclusion induces an inclusion at every depth. -/
theorem complex_mono {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) :
    ∀ n, complex K n ≤ complex L n
  | 0 => h
  | n + 1 => TDA.Filtration.SubdivisionRips.subdivision_mono (complex_mono h n) le_rfl

/-- Position of a fine vertex in the original space, by iterated barycenters. -/
def vertexPosition (p : V → E) : (n : ℕ) → Vertex V n → E
  | 0 => p
  | n + 1 => barycenter (vertexPosition p n)

/-- Affine interpolation of fine vertex positions on the realization. -/
def realize (p : V → E) (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    C(Realization (complex K n), E) where
  toFun x := ∑ v, x.val.weights v • vertexPosition p n v
  continuous_toFun := by fun_prop

/-- Restricting affine interpolation along a subcomplex inclusion preserves its values. -/
theorem realize_incl (p : V → E) {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (n : ℕ) :
    (realize p L n).comp (Realization.incl (complex_mono h n)) = realize p K n := rfl

/-- The realized point concentrated at an active vertex. -/
def vertexPoint {X : Type*} (N : PreAbstractSimplicialComplex X) (v : X)
    (hv : ({v} : Finset X) ∈ N) : Realization N :=
  ⟨StdSimplex.single v, by simpa using hv⟩

/-- Interpolation evaluates at a realized vertex to its recursively placed position. -/
theorem realize_vertexPoint {X : Type*} [Fintype X]
    (N : PreAbstractSimplicialComplex X) (p : X → E) (n : ℕ) (v : Vertex X n)
    (hv : ({v} : Finset _) ∈ complex N n) :
    realize p N n (vertexPoint _ v hv) = vertexPosition p n v := by
  classical
  change (∑ w, (StdSimplex.single (R := ℝ) v).weights w • vertexPosition p n w) = _
  simp [StdSimplex.weights_single, Finsupp.single_apply, ite_smul]

/-- Each active face supplies a vertex of its barycentric subdivision. -/
theorem singleton_mem_subdivision {X : Type*} [Fintype X] (N : PreAbstractSimplicialComplex X) (s : Finset X)
    (h : s ∈ N) : ({s} : Finset _) ∈ barycentricSubdivision N := by
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · intro A hA
    obtain rfl := Finset.mem_singleton.mp hA
    exact ⟨h, by positivity⟩
  · intro A hA B hB
    obtain rfl := Finset.mem_singleton.mp hA
    obtain rfl := Finset.mem_singleton.mp hB
    exact Or.inl (Finset.Subset.refl _)

section OneStep
variable {I : Type u} [Fintype I] {K : PreAbstractSimplicialComplex I}

omit [Fintype I] in
open Classical in
private theorem centroidWeight_apply (A : Finset I) (i : I) :
    A.centroidWeightsIndicator ℝ i = if i ∈ A then (A.card : ℝ)⁻¹ else 0 := by
  simp [Finset.centroidWeightsIndicator, Set.indicator_apply]

omit [Fintype I] in
private theorem centroidWeight_nonneg (A : Finset I) (i : I) : 0 ≤ A.centroidWeightsIndicator ℝ i := by
  rw [centroidWeight_apply]
  split <;> positivity

private def projectedWeight (x : Realization (barycentricSubdivision K)) (i : I) : ℝ :=
  ∑ A, x.val.weights A * A.centroidWeightsIndicator ℝ i

private theorem weight_pos_iff (x : Realization (barycentricSubdivision K)) (i : I) :
    0 < projectedWeight x i ↔ ∃ A ∈ x.val.weights.support, i ∈ A := by
  rw [projectedWeight, Finset.sum_pos_iff_of_nonneg (fun A _ => mul_nonneg (x.val.weights_nonneg A) (centroidWeight_nonneg A i))]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A, h⟩
    have hA : x.val.weights A ≠ 0 := by intro he; simp [he] at h
    refine ⟨A, Finsupp.mem_support_iff.mpr hA, ?_⟩
    by_contra hi
    simp [centroidWeight_apply, hi] at h
  · rintro ⟨A, hA, hi⟩
    have hp := lt_of_le_of_ne (x.val.weights_nonneg A) (Finsupp.mem_support_iff.mp hA).symm
    have hn : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
    exact ⟨A, mul_pos hp (by simpa [centroidWeight_apply, hi] using inv_pos.mpr hn)⟩

private def projectedSimplex (x : Realization (barycentricSubdivision K)) : StdSimplex ℝ I where
  weights := Finsupp.equivFunOnFinite.symm (projectedWeight x)
  nonneg := fun i => Finset.sum_nonneg (fun A _ => mul_nonneg (x.val.weights_nonneg A) (centroidWeight_nonneg A i))
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i, ∑ A, x.val.weights A * A.centroidWeightsIndicator ℝ i = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    convert (Finsupp.sum_fintype x.val.weights (fun _ z => z) (by simp)).symm.trans x.val.total using 1
    apply Finset.sum_congr rfl
    intro A _
    by_cases ha : A ∈ x.val.weights.support
    · rw [A.sum_centroidWeightsIndicator_eq_one_of_nonempty ℝ (K.isRelLowerSet_faces (x.property.2.1 A ha).1).1, mul_one]
    · simp [Finsupp.notMem_support_iff.mp ha]

private theorem exists_greatest_face {F : Finset (Finset I)} (hf : F ∈ barycentricSubdivision K) :
    ∃ T ∈ F, ∀ A ∈ F, A ⊆ T := by
  obtain ⟨_, _, T, hT, h⟩ := exists_flag_extrema hf
  exact ⟨T, hT, fun A hA => (h A hA).2⟩

private theorem support_eq_greatest (x : Realization (barycentricSubdivision K)) {T : Finset I}
    (ht : T ∈ x.val.weights.support) (hm : ∀ A ∈ x.val.weights.support, A ⊆ T) :
    (projectedSimplex x).weights.support = T := by
  ext i
  have hp : (projectedSimplex x).weights i ≠ 0 ↔ 0 < projectedWeight x i :=
    (lt_iff_le_and_ne.trans (and_iff_right ((projectedSimplex x).weights_nonneg i))).trans ne_comm |>.symm
  rw [Finsupp.mem_support_iff, hp, weight_pos_iff]
  exact ⟨fun ⟨A, hA, hi⟩ => hm A hA hi, fun hi => ⟨T, ht, hi⟩⟩

/-- Average the face barycenters with the weights of a point of the subdivision. -/
def projectStep (K : PreAbstractSimplicialComplex I) :
    C(Realization (barycentricSubdivision K), Realization K) := by
  have h (x : Realization (barycentricSubdivision K)) : (projectedSimplex x).weights.support ∈ K := by
    obtain ⟨T, ht, hm⟩ := exists_greatest_face x.property
    rw [support_eq_greatest x ht hm]
    exact (x.property.2.1 T ht).1
  refine ⟨fun x => ⟨projectedSimplex x, h x⟩, Continuous.subtype_mk ?_ _⟩
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ I).continuous_iff.mpr
  apply continuous_pi
  intro i
  change Continuous fun x : Realization (barycentricSubdivision K) => ∑ A, x.val.weights A * A.centroidWeightsIndicator ℝ i
  fun_prop

/-- Each active face vertex projects to its barycenter in the original realization. -/
theorem projectStep_vertexPoint {A : Finset I} (hA : A ∈ K) :
    projectStep K (vertexPoint _ A (singleton_mem_subdivision K A hA)) =
      (Realization.faceBarycenter hA).val := by
  classical
  apply Subtype.ext
  apply StdSimplex.ext
  ext i
  change (∑ B, (StdSimplex.single (R := ℝ) A).weights B * B.centroidWeightsIndicator ℝ i) = _
  simp only [StdSimplex.weights_single, Finsupp.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hi : i ∈ A
  · simp [centroidWeight_apply, hi, Realization.faceBarycenter_weights_of_mem hA hi]
  · have hzero : i ∉ (Realization.faceBarycenter hA).val.val.weights.support := by
      rwa [Realization.faceBarycenter_support]
    simp [centroidWeight_apply, hi, Finsupp.notMem_support_iff.mp hzero]

end OneStep

/-- Union of the faces in a flag. -/
def flagUnion {X : Type*} (F : Finset (Finset X)) : Finset X := by
  classical exact F.biUnion id

/-- The union of a nonempty flag belongs to the flag. -/
theorem flagUnion_mem {X : Type*} [Fintype X] {K : PreAbstractSimplicialComplex X}
    {F : Finset (Finset X)} (hf : F ∈ barycentricSubdivision K) : flagUnion F ∈ F := by
  classical
  obtain ⟨T, hT, hmax⟩ := exists_greatest_face hf
  suffices flagUnion F = T by rwa [this]
  ext v
  simp only [flagUnion, Finset.mem_biUnion, id_eq]
  exact ⟨fun ⟨A, hA, hv⟩ => hmax A hA hv, fun hv => ⟨T, hT, hv⟩⟩

/-- Each flag member is contained in its union. -/
theorem subset_flagUnion {X : Type*} {F : Finset (Finset X)} {A : Finset X} (ha : A ∈ F) : A ⊆ flagUnion F := by
  classical
  exact fun v hv => Finset.mem_biUnion.mpr ⟨A, ha, hv⟩
/-- The original face supporting a fine face, obtained by taking successive unions. -/
def originalFace : (n : ℕ) → Finset (Vertex V n) → Finset V
  | 0 => id
  | n + 1 => fun F => originalFace n (flagUnion F)

/-- An iterated face is supported by an original face. -/
theorem originalFace_mem (K : PreAbstractSimplicialComplex V) :
    ∀ n (F : Finset (Vertex V n)), F ∈ complex K n → originalFace n F ∈ K := by
  intro n
  induction n with
  | zero => exact fun _ h => h
  | succ n ih => intro F hf; exact ih _ (hf.2.1 _ (flagUnion_mem hf)).1

/-- Continuous barycenter projection from depth `n` to the original realization. -/
def barycentricProjection (K : PreAbstractSimplicialComplex V) :
    (n : ℕ) → C(Realization (complex K n), Realization K)
  | 0 => ContinuousMap.id _
  | n + 1 => (barycentricProjection K n).comp (projectStep (complex K n))

/-- The projections commute with the actual realization inclusions at both depths. -/
theorem projection_incl {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) :
    ∀ n, (barycentricProjection L n).comp (Realization.incl (complex_mono h n)) =
      (Realization.incl h).comp (barycentricProjection K n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    ext1 x
    exact ContinuousMap.congr_fun ih (projectStep (complex K n) x)

private theorem sum_centroidWeightsIndicator_smul (p : V → E) (A : Finset V) :
    (∑ i, A.centroidWeightsIndicator ℝ i • p i) = barycenter p A := by
  simp [centroidWeight_apply, ite_smul, barycenter, Finset.smul_sum]

private theorem realize_succ (K : PreAbstractSimplicialComplex V) (p : V → E) (n : ℕ)
    (x : Realization (complex K (n + 1))) :
    realize p K (n + 1) x = realize p K n (projectStep (complex K n) x) := by
  let q := vertexPosition p n
  change (∑ A, x.val.weights A • barycenter q A) =
    ∑ i, (∑ A, x.val.weights A * A.centroidWeightsIndicator ℝ i) • q i
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  simp_rw [mul_smul, ← Finset.smul_sum]
  exact congrArg (x.val.weights A • ·) (sum_centroidWeightsIndicator_smul q A).symm

/-- Affine interpolation at depth `n` factors through the original realization. -/
theorem realize_eq_comp_projection (K : PreAbstractSimplicialComplex V) (p : V → E) :
    ∀ n, realize p K n = (realize p K 0).comp (barycentricProjection K n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    ext1 x
    exact (realize_succ K p n x).trans (ContinuousMap.congr_fun ih (projectStep (complex K n) x))

/-- A fine face of the larger complex is inherited precisely when its original face is in the smaller complex. -/
theorem mem_iff_originalFace_mem {K L : PreAbstractSimplicialComplex V} :
    ∀ n (F : Finset (Vertex V n)), F ∈ complex L n → (F ∈ complex K n ↔ originalFace n F ∈ K) := by
  intro n
  induction n with
  | zero => exact fun _ _ => Iff.rfl
  | succ n ih =>
    intro F hL
    constructor
    · exact originalFace_mem K _ _
    · intro hA
      have hT := (ih (flagUnion F) (hL.2.1 _ (flagUnion_mem hL)).1).2 hA
      exact ⟨hL.1, fun A hAF => ⟨((complex K n).isRelLowerSet_faces hT).2 (subset_flagUnion hAF)
        (((complex L n).isRelLowerSet_faces (hL.2.1 A hAF).1).1), (hL.2.1 A hAF).2⟩, hL.2.2⟩

/-- The original-coordinate support is exactly the ancestor of the fine support. -/
theorem projection_support (K : PreAbstractSimplicialComplex V) :
    ∀ n (x : Realization (complex K n)),
      (barycentricProjection K n x).val.weights.support = originalFace n x.val.weights.support := by
  intro n
  induction n with
  | zero => exact fun _ => rfl
  | succ n ih =>
    intro x
    have htop := flagUnion_mem x.property
    change (barycentricProjection K n (projectStep (complex K n) x)).val.weights.support = _
    rw [ih]
    exact congrArg (originalFace n) (support_eq_greatest x htop (fun _ hw => subset_flagUnion hw))

/-- A projected point belongs to the smaller realization exactly when its fine support does. -/
theorem projection_support_mem_iff {K L : PreAbstractSimplicialComplex V} (n : ℕ)
    (x : Realization (complex L n)) :
    (barycentricProjection L n x).val.weights.support ∈ K ↔ x.val.weights.support ∈ complex K n := by
  rw [projection_support]
  exact (mem_iff_originalFace_mem n _ x.property).symm

private theorem vertexPosition_congr {K : PreAbstractSimplicialComplex V} {p q : V → E}
    (ha : ∀ v, ({v} : Finset V) ∈ K → p v = q v) :
    ∀ n (F : Finset (Vertex V n)), F ∈ complex K n → ∀ w ∈ F, vertexPosition p n w = vertexPosition q n w := by
  intro n
  induction n with
  | zero =>
    intro F hF w hw
    exact ha w ((K.isRelLowerSet_faces hF).2 (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty _))
  | succ n ih =>
    intro F hF w hw
    change barycenter (vertexPosition p n) w = barycenter (vertexPosition q n) w
    exact congrArg (fun z => (w.card : ℝ)⁻¹ • z)
      (Finset.sum_congr rfl (fun i hi => ih w (hF.2.1 w hw).1 i hi))

/-- Placements agreeing on the active vertices of a subcomplex interpolate identically there. -/
theorem realize_incl_of_agree {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) {p q : V → E}
    (ha : ∀ v, ({v} : Finset V) ∈ K → p v = q v) (n : ℕ) :
    (realize q L n).comp (Realization.incl (complex_mono h n)) = realize p K n := by
  classical
  rw [realize_incl q h n]
  ext1 x
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ x.val.weights.support
  · rw [vertexPosition_congr ha n _ x.property v hv]
  · simp [Finsupp.notMem_support_iff.mp hv]

end
end TDA.Topology.SubdivisionRealization
