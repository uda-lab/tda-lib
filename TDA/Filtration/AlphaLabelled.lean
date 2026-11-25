import TDA.Filtration.Alpha
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

/-!
# The α and Čech filtrations on labelled sites

The closed Voronoi nerve accepts a site function, with the embedding-based α filtration as
a special case. The Čech filtration uses squared grades and both filtrations start at zero.

Nerve form. `labelledComplex sites t` is the nerve of the closed Voronoi cells of the labels,
each cut off at squared distance `t` from its own site. The closed nearest-site inequalities
retain all ties, including in degenerate configurations: for cocircular sites the simplex
spanned by all of them is a face at the squared circumradius, so the complex is the nerve and
not a Delaunay subcomplex.

Negative grades. The canonical comparison target `squaredCechFiltration` is the ambient
Čech filtration on squared grades and is empty below zero, as is the α filtration. The
canonical inclusion for embedded sites is `filtration_le_squaredCech` (the labelled version is
`labelledComplexFiltration_le_squaredCech`), with naturality `inclusion_natural_squaredCech`.
The legacy comparison `filtration_le_cech` of `Alpha.lean` reindexes by `Alpha.radius`, whose
negative grades give radius zero and hence the radius-zero Čech complex. The two targets agree
at `t ≥ 0` (`reindex_radius_cech_eq_squaredCech_of_nonneg`) and the empty target lies below the
legacy one everywhere (`squaredCechFiltration_le_reindex_radius`). The legacy statements are
kept unchanged for the migration period.

For finitely many sites in a real normed vector space, each Čech edge at a nonnegative
grade can be replaced by a path in the α complex at that grade.
-/

namespace TDA.Filtration.Alpha

open TDA.Topology TDA.Simplicial
open scoped Convex

variable {V E : Type*} [NormedAddCommGroup E] (sites : V → E)

/-- The closed Voronoi cell of a label, cut off at squared distance `t`. -/
def restrictedBall (t : ℝ) (v : V) : Set E :=
  {x | ∀ w, dist x (sites v) ≤ dist x (sites w)} ∩ {x | dist x (sites v) ^ 2 ≤ t}

/-- The squared-grade α complex of a labelled site function. Closed nearest-site
inequalities keep all tied labels, including distinct labels at the same site. -/
def labelledComplex (t : ℝ) : PreAbstractSimplicialComplex V := nerve (restrictedBall sites t)

theorem labelledComplex_eq_complex (p : V ↪ E) (t : ℝ) :
    labelledComplex p t = Alpha.complex p t := rfl

/-- A labelled α face has a common closed Voronoi witness within the squared cutoff. -/
theorem mem_labelledComplex_iff (t : ℝ) (s : Finset V) :
    s ∈ labelledComplex sites t ↔ s.Nonempty ∧ ∃ x : E, ∀ v ∈ s,
      (∀ w, dist x (sites v) ≤ dist x (sites w)) ∧ dist x (sites v) ^ 2 ≤ t :=
  Iff.rfl

/-- The ambient Čech radius for the squared-grade convention with empty negative stages. -/
noncomputable def squaredCechRadius : ℝ →o ℝ where
  toFun t := if t < 0 then t else Real.sqrt t
  monotone' := by
    intro s t hst
    change (if s < 0 then s else Real.sqrt s) ≤ (if t < 0 then t else Real.sqrt t)
    split_ifs with hs ht ht
    · exact hst
    · exact hs.le.trans (Real.sqrt_nonneg _)
    · exact (hs (hst.trans_lt ht)).elim
    · exact Real.sqrt_monotone hst

/-- Ambient Čech on squared grades, with no nonempty faces below zero. -/
noncomputable def squaredCechFiltration : SimplicialFiltration ℝ V :=
  reindex squaredCechRadius (Cech.complexFiltration sites)

theorem squaredCechFiltration_apply_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    squaredCechFiltration sites t = Cech.complex sites (Real.sqrt t) := by
  change Cech.complex sites (if t < 0 then t else Real.sqrt t) = _
  simp [not_lt_of_ge ht]

theorem squaredCechFiltration_apply_of_neg {t : ℝ} (ht : t < 0) :
    squaredCechFiltration sites t = ⊥ := by
  change Cech.complex sites (if t < 0 then t else Real.sqrt t) = _
  simp [ht, Cech.complex_eq_bot_of_neg sites ht]

theorem labelledComplex_eq_bot_of_neg {t : ℝ} (ht : t < 0) : labelledComplex sites t = ⊥ := by
  apply le_antisymm _ bot_le
  rintro s ⟨⟨v, hv⟩, x, hx⟩
  exact absurd ((sq_nonneg _).trans (hx v hv).2) ht.not_ge

theorem singleton_mem_labelledComplex (v : V) {t : ℝ} (ht : 0 ≤ t) :
    ({v} : Finset V) ∈ labelledComplex sites t := by
  apply (mem_nerve_singleton_iff _ _).2
  exact ⟨sites v, by simp [restrictedBall, ht]⟩

/-- The closed α filtration of a labelled site function on squared grades. -/
def labelledComplexFiltration : SimplicialFiltration ℝ V :=
  ⟨labelledComplex sites, fun _ _ h => nerve_mono fun _ _ hx => ⟨hx.1, hx.2.trans h⟩⟩

theorem labelledComplexFiltration_eq_complexFiltration (p : V ↪ E) :
    labelledComplexFiltration p = Alpha.complexFiltration p := rfl

/-- Forgetting the nearest-site inequalities gives the inclusion on the same labels. -/
theorem labelledComplexFiltration_le_squaredCech (t : ℝ) :
    labelledComplexFiltration sites t ≤ squaredCechFiltration sites t := by
  change labelledComplex sites t ≤ squaredCechFiltration sites t
  by_cases ht : t < 0
  · rw [labelledComplex_eq_bot_of_neg sites ht]
    exact bot_le
  · rw [squaredCechFiltration_apply_of_nonneg sites (le_of_not_gt ht)]
    exact nerve_mono fun _ _ hx => Real.le_sqrt_of_sq_le hx.2

/-- The legacy radius reindexing agrees with the canonical squared-grade Čech filtration at
every nonnegative grade. -/
theorem reindex_radius_cech_eq_squaredCech_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    reindex radius (Cech.complexFiltration sites) t = squaredCechFiltration sites t := by
  rw [squaredCechFiltration_apply_of_nonneg sites ht, reindex_apply, Cech.complexFiltration_apply]
  rfl

/-- At a negative grade the legacy radius reindexing is the radius-zero Čech complex. -/
theorem reindex_radius_cech_apply_of_neg {t : ℝ} (ht : t < 0) :
    reindex radius (Cech.complexFiltration sites) t = Cech.complex sites 0 := by
  rw [reindex_apply, Cech.complexFiltration_apply]
  congr 1
  exact Real.sqrt_eq_zero'.2 ht.le

/-- The canonical (empty below zero) target is contained in the legacy radius reindexing at
every grade. -/
theorem squaredCechFiltration_le_reindex_radius :
    squaredCechFiltration sites ≤ reindex radius (Cech.complexFiltration sites) := by
  intro t
  by_cases ht : t < 0
  · rw [squaredCechFiltration_apply_of_neg sites ht]
    exact bot_le
  · exact (reindex_radius_cech_eq_squaredCech_of_nonneg sites (le_of_not_gt ht)).ge

/-- Canonical inclusion of the α filtration of embedded sites into the Čech filtration on
squared grades, with empty negative stages. This is the labelled inclusion
`labelledComplexFiltration_le_squaredCech` at an embedding; the legacy counterpart with the
radius-zero-below-zero target is `filtration_le_cech`. -/
theorem filtration_le_squaredCech (p : V ↪ E) :
    complexFiltration p ≤ squaredCechFiltration p :=
  labelledComplexFiltration_le_squaredCech p

/-- The identity on labels commutes with the structure maps of the α filtration and of the
canonical squared-grade Čech filtration. Canonical counterpart of `inclusion_natural`. -/
theorem inclusion_natural_squaredCech (p : V ↪ E) {s t : ℝ} (hst : s ≤ t) :
    VertexMap.comp (inclusionVertexMap ((complexFiltration p).monotone hst))
        (inclusionVertexMap (filtration_le_squaredCech p t)) =
      VertexMap.comp (inclusionVertexMap (filtration_le_squaredCech p s))
        (inclusionVertexMap ((squaredCechFiltration p).monotone hst)) :=
  VertexMap.ext fun _ => rfl

private theorem isClosed_restrictedBall (t : ℝ) (v : V) : IsClosed (restrictedBall sites t v) := by
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun _ => isClosed_le (continuous_id.dist continuous_const)
      (continuous_id.dist continuous_const)
  · exact isClosed_le ((continuous_id.dist continuous_const).pow 2) continuous_const

private theorem exists_restricted_of_ball [Finite V] {x : E} {t : ℝ} {v : V}
    (hv : dist x (sites v) ≤ Real.sqrt t) (ht : 0 ≤ t) :
    ∃ w, x ∈ restrictedBall sites t w := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨w, -, hw⟩ := Finset.exists_min_image Finset.univ
    (fun j => dist x (sites j)) ⟨v, Finset.mem_univ v⟩
  refine ⟨w, fun j => hw j (Finset.mem_univ j), ?_⟩
  exact (Real.le_sqrt dist_nonneg ht).mp ((hw v (Finset.mem_univ v)).trans hv)

/-- Forget the nearest-site constraints at a restricted ball. -/
theorem restrictedBall_subset_closedBall (t : ℝ) (v : V) :
    restrictedBall sites t v ⊆ Metric.closedBall (sites v) (Real.sqrt t) :=
  fun _ hx => Real.le_sqrt_of_sq_le hx.2

/-- At a nonnegative squared grade, choosing a nearest site covers the same union
with restricted balls as with the full ambient balls. -/
theorem iUnion_restrictedBall [Finite V] {t : ℝ} (ht : 0 ≤ t) :
    (⋃ v, restrictedBall sites t v) = ⋃ v, Metric.closedBall (sites v) (Real.sqrt t) := by
  refine Set.Subset.antisymm (Set.iUnion_mono (restrictedBall_subset_closedBall sites t)) ?_
  intro x hx
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr (exists_restricted_of_ball sites (v := v) hv ht)

/-- Restricted balls are compact in a proper ambient space. -/
theorem isCompact_restrictedBall [ProperSpace E] (t : ℝ) (v : V) :
    IsCompact (restrictedBall sites t v) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_restrictedBall sites t v)
    (restrictedBall_subset_closedBall sites t v)

section Euclidean

variable [InnerProductSpace ℝ E]
open scoped RealInnerProductSpace

private theorem dist_le_dist_iff_halfspace (x p q : E) :
    dist x p ≤ dist x q ↔ ‖p‖ ^ 2 - ‖q‖ ^ 2 ≤ 2 * (⟪x, p⟫ - ⟪x, q⟫) := by
  rw [← sq_le_sq₀ dist_nonneg dist_nonneg, dist_eq_norm, dist_eq_norm,
    norm_sub_sq_real, norm_sub_sq_real]
  constructor <;> intro h <;> linarith

/-- Each nearest-site inequality cuts out a closed half-space. Intersecting these
half-spaces with the radius ball gives a convex restricted ball, including tied sites. -/
theorem convex_restrictedBall {t : ℝ} (ht : 0 ≤ t) (v : V) :
    Convex ℝ (restrictedBall sites t v) := by
  have hball : {x | dist x (sites v) ^ 2 ≤ t} = Metric.closedBall (sites v) (Real.sqrt t) := by
    ext x
    exact (Real.le_sqrt dist_nonneg ht).symm
  rw [restrictedBall, hball]
  apply Convex.inter _ (convex_closedBall _ _)
  intro x hx y hy a b ha hb hab j
  apply (dist_le_dist_iff_halfspace _ _ _).2
  simp only [inner_add_left, real_inner_smul_left]
  have h₁ := mul_le_mul_of_nonneg_left ((dist_le_dist_iff_halfspace _ _ _).1 (hx j)) ha
  have h₂ := mul_le_mul_of_nonneg_left ((dist_le_dist_iff_halfspace _ _ _).1 (hy j)) hb
  calc
    _ = (a + b) * (‖sites v‖ ^ 2 - ‖sites j‖ ^ 2) := by rw [hab, one_mul]
    _ ≤ _ := by linarith only [h₁, h₂]

end Euclidean

private def overlapOn (S : Set E) (P : V → Set E) (u v : V) : Prop :=
  ∃ x ∈ S, x ∈ P u ∧ x ∈ P v

private theorem finite_closed_cover_reachable [Finite V] {S : Set E} {P : V → Set E}
    (hS : IsPreconnected S) (hclosed : ∀ j, IsClosed (P j))
    (hcover : ∀ x ∈ S, ∃ j, x ∈ P j)
    {u v : V} (hu : (S ∩ P u).Nonempty) (hv : (S ∩ P v).Nonempty) :
    Relation.EqvGen (overlapOn S P) u v := by
  classical
  let reach := Relation.EqvGen (overlapOn S P) u
  let A : Set E := ⋃ j : {j // reach j}, P j
  let B : Set E := ⋃ j : {j // ¬ reach j}, P j
  have hA : IsClosed A := isClosed_iUnion_of_finite fun j => hclosed j
  have hB : IsClosed B := isClosed_iUnion_of_finite fun j => hclosed j
  have cover : S ⊆ A ∪ B := by
    intro x hx
    obtain ⟨j, hj⟩ := hcover x hx
    by_cases hr : reach j
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨j, hr⟩, hj⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hr⟩, hj⟩)
  have noCross {x : E} (hx : x ∈ S) (hxA : x ∈ A) (hxB : x ∈ B) : False := by
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxA
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxB
    exact b.property (Relation.EqvGen.trans _ _ _ a.property
      (Relation.EqvGen.rel _ _ ⟨x, hx, ha, hb⟩))
  have disjoint : S ∩ (A ∩ B) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, ha, hb⟩
    exact noCross hx ha hb
  have intoA : S ⊆ A := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hS) A B hA hB cover disjoint with h | h
    · exact h
    · obtain ⟨x, hx, hxu⟩ := hu
      exact (noCross hx (Set.mem_iUnion.mpr ⟨⟨u, Relation.EqvGen.refl u⟩, hxu⟩)
        (h hx)).elim
  by_contra h
  obtain ⟨x, hx, hxv⟩ := hv
  exact noCross hx (intoA hx) (Set.mem_iUnion.mpr ⟨⟨v, h⟩, hxv⟩)

/-- The endpoints of a Čech edge can be joined by α edges at the same squared grade. -/
theorem cech_edge_reachable [DecidableEq V] [Finite V] [NormedSpace ℝ E] {t : ℝ} (ht : 0 ≤ t)
    {u v : V}
    (h : ({u, v} : Finset V) ∈ Cech.complex sites (Real.sqrt t)) :
    Relation.EqvGen (fun a b => ({a, b} : Finset V) ∈ labelledComplex sites t) u v := by
  let S := segment ℝ (sites u) (sites v)
  have hS : IsPreconnected S := (convex_segment _ _).isPreconnected
  have hdist := Cech.dist_le_two_mul_of_mem_complex sites h
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hcover (x : E) (hx : x ∈ S) : ∃ j, x ∈ restrictedBall sites t j := by
    have hadd := dist_add_dist_of_mem_segment hx
    rw [dist_comm (sites u) x] at hadd
    by_cases hu : dist x (sites u) ≤ Real.sqrt t
    · exact exists_restricted_of_ball sites hu ht
    · apply exists_restricted_of_ball sites (v := v) _ ht
      linarith
  have endpoint (j : V) (hj : sites j ∈ S) :
      (S ∩ restrictedBall sites t j).Nonempty := by
    refine ⟨sites j, hj, ?_, ?_⟩
    · intro a
      simp
    · simp [ht]
  have reach := finite_closed_cover_reachable hS (isClosed_restrictedBall sites t) hcover
    (endpoint u (left_mem_segment ℝ _ _)) (endpoint v (right_mem_segment ℝ _ _))
  refine Relation.EqvGen.mono ?_ u v reach
  intro a b hab
  obtain ⟨x, -, ha, hb⟩ := hab
  exact ⟨⟨a, Finset.mem_insert_self _ _⟩, x, by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ha
    · obtain rfl := Finset.mem_singleton.mp hj
      exact hb⟩

end TDA.Filtration.Alpha
