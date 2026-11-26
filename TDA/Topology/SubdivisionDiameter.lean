import TDA.Topology.AffineChains
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Diameter contraction under barycentric subdivision of affine simplices

The barycentric subdivision of an affine simplex `σ` with vertices in a convex set `K` of the
standard simplex is built recursively as `sd(σ) = b_σ · sd(∂σ)`, where `b_σ` is the barycentre
`simplexBarycenter hK σ` (the image of `StdSimplex.barycenter` under `realize hK σ`).
`IsSubdivisionSimplex hK σ τ` states that `τ` is a simplex of this recursion: a vertex is its
own subdivision, and the cone from `b_σ` on a simplex of the subdivision of a facet of `σ`
is a simplex of the subdivision of `σ`. `IsIteratedSubdivisionSimplex hK N σ τ` composes `N`
such steps.

Distances are measured after a linear map `L : (Fin (m + 1) →₀ ℝ) →ₗ[ℝ] E` of the weight
vectors into any real normed space `E` (`position L`); every affine map from the standard
simplex to `E` has this form, so this covers any norm. Every simplex of
the subdivision of `σ` lies in `σ` and its realized diameter is at most `n / (n + 1)` times
that of `σ` (`IsSubdivisionSimplex.diam_range_realize_le`); after `N` subdivisions the factor
is `(n / (n + 1)) ^ N` (`IsIteratedSubdivisionSimplex.diam_range_realize_le`). Both relations
are preserved by affine maps between convex subsets of standard simplices.
-/

namespace TDA.Topology.AffineChains

open Convexity Metric Set

noncomputable section

variable {m : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))} (hK : IsConvexSet ℝ K)

/-! ### Barycentres and positions -/

/-- The barycentre `b_σ` of an affine simplex with vertices in `K`. -/
def simplexBarycenter {n : ℕ} (σ : Fin (n + 1) → K) : K :=
  realize hK σ StdSimplex.barycenter

lemma simplexBarycenter_mem_range {n : ℕ} (σ : Fin (n + 1) → K) :
    simplexBarycenter hK σ ∈ range (realize hK σ) :=
  ⟨_, rfl⟩

/-- An affine map of ambient simplices carrying `K` into `K'` preserves barycentres. -/
lemma simplexBarycenter_mapsTo {m' : ℕ} {K' : Set (StdSimplex ℝ (Fin (m' + 1)))}
    (hK' : IsConvexSet ℝ K')
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (m + 1))) (StdSimplex ℝ (Fin (m' + 1))))
    (hF : MapsTo F K K') {n : ℕ} (σ : Fin (n + 1) → K) :
    simplexBarycenter hK' (hF.restrict F K K' ∘ σ) = hF.restrict F K K' (simplexBarycenter hK σ) :=
  Subtype.ext (coe_realize_mapsTo hK hK' F hF σ _)

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  (L : (Fin (m + 1) →₀ ℝ) →ₗ[ℝ] E)

/-- The position of a point of `K` in `E`: the image of its weight vector under `L`. -/
def position (x : K) : E := L (x : StdSimplex ℝ (Fin (m + 1))).weights

variable {L}

lemma position_realize {n : ℕ} (σ : Fin (n + 1) → K) (t : StdSimplex ℝ (Fin (n + 1))) :
    position L (realize hK σ t) = ∑ i, t.weights i • position L (σ i) := by
  rw [position, coe_realize_apply, StdSimplex.affineMapMk_apply,
    (StdSimplex.isAffineMap_weights ℝ (Fin (m + 1))).map_iConvexComb, iConvexComb_eq_sum,
    Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp [position]

lemma position_simplexBarycenter {n : ℕ} (σ : Fin (n + 1) → K) :
    position L (simplexBarycenter hK σ) = ∑ i, ((n : ℝ) + 1)⁻¹ • position L (σ i) := by
  rw [simplexBarycenter, position_realize]
  simp [StdSimplex.weights_barycenter_apply]

lemma position_realize_mem_convexHull {n : ℕ} (σ : Fin (n + 1) → K)
    (t : StdSimplex ℝ (Fin (n + 1))) :
    position L (realize hK σ t) ∈ convexHull ℝ (range (position L ∘ σ)) := by
  rw [position_realize]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => t.weights_nonneg i) t.total_of_fintype
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

lemma isBounded_range_position_realize {n : ℕ} (σ : Fin (n + 1) → K) :
    Bornology.IsBounded (range (position L ∘ realize hK σ)) :=
  (isBounded_convexHull.mpr (finite_range _).isBounded).subset
    (range_subset_iff.mpr fun t => position_realize_mem_convexHull hK σ t)

/-- A realized affine simplex has the diameter of its vertex set. -/
theorem diam_range_position_realize {n : ℕ} (σ : Fin (n + 1) → K) :
    diam (range (position L ∘ realize hK σ)) = diam (range (position L ∘ σ)) := by
  refine le_antisymm ?_ ?_
  · refine (diam_mono (range_subset_iff.mpr fun t => position_realize_mem_convexHull hK σ t)
      (isBounded_convexHull.mpr (finite_range _).isBounded)).trans (convexHull_diam _).le
  · refine diam_mono (range_subset_iff.mpr fun i => ⟨.single i, ?_⟩)
      (isBounded_range_position_realize hK σ)
    simp

/-- The barycentre of points `p 0, …, p n` is within `n / (n + 1)` times their diameter of
every point of their convex hull. -/
private theorem dist_mean_le {n : ℕ} (p : Fin (n + 1) → E) {q : E}
    (hq : q ∈ convexHull ℝ (range p)) :
    dist (∑ i, ((n : ℝ) + 1)⁻¹ • p i) q ≤ n / (n + 1) * diam (range p) := by
  set b := ∑ i, ((n : ℝ) + 1)⁻¹ • p i
  set D := diam (range p)
  have hbd : Bornology.IsBounded (range p) := (finite_range p).isBounded
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hvert (j : Fin (n + 1)) : dist (p j) b ≤ n / (n + 1) * D := by
    have hsum : b - p j = ∑ i, ((n : ℝ) + 1)⁻¹ • (p i - p j) := by
      simp only [b, smul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      rw [Nat.cast_succ, mul_inv_cancel₀ hn.ne', one_smul]
    have hle : ∑ i, ‖p i - p j‖ ≤ n * D := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), sub_self, norm_zero, zero_add]
      have hcard : (Finset.univ.erase j).card = n := by simp
      calc ∑ i ∈ Finset.univ.erase j, ‖p i - p j‖
          ≤ ∑ _i ∈ Finset.univ.erase j, D :=
            Finset.sum_le_sum fun i _ => by
              rw [← dist_eq_norm]
              exact dist_le_diam_of_mem hbd ⟨i, rfl⟩ ⟨j, rfl⟩
        _ = n * D := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rw [dist_comm, dist_eq_norm, hsum]
    calc ‖∑ i, ((n : ℝ) + 1)⁻¹ • (p i - p j)‖
        ≤ ∑ i, ‖((n : ℝ) + 1)⁻¹ • (p i - p j)‖ := norm_sum_le _ _
      _ = ((n : ℝ) + 1)⁻¹ * ∑ i, ‖p i - p j‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ ((n : ℝ) + 1)⁻¹ * (n * D) := by gcongr
      _ = n / (n + 1) * D := by field_simp
  obtain ⟨x, ⟨j, rfl⟩, hx⟩ := convexHull_exists_dist_ge hq b
  rw [dist_comm]
  exact hx.trans (hvert j)

/-- The barycentre of an affine `n`-simplex is within `n / (n + 1)` times its diameter of
every point of the simplex. -/
theorem dist_position_simplexBarycenter_le {n : ℕ} (σ : Fin (n + 1) → K) {x : K}
    (hx : x ∈ range (realize hK σ)) :
    dist (position L (simplexBarycenter hK σ)) (position L x) ≤
      n / (n + 1) * diam (range (position L ∘ σ)) := by
  obtain ⟨t, rfl⟩ := hx
  rw [position_simplexBarycenter]
  exact dist_mean_le _ (position_realize_mem_convexHull hK σ t)

/-! ### Simplices of the barycentric subdivision -/

/-- If every vertex of `τ` lies in the realized simplex `σ`, so does all of `τ`. -/
theorem range_realize_subset {n k : ℕ} {σ : Fin (n + 1) → K} {τ : Fin (k + 1) → K}
    (h : ∀ j, τ j ∈ range (realize hK σ)) : range (realize hK τ) ⊆ range (realize hK σ) := by
  choose s hs using h
  rintro _ ⟨t, rfl⟩
  refine ⟨StdSimplex.affineMapMk s t, Subtype.ext ?_⟩
  have hτ : Subtype.val ∘ τ = StdSimplex.affineMapMk (Subtype.val ∘ σ) ∘ s := by
    funext j
    rw [Function.comp_apply, ← hs j]
    rfl
  rw [coe_realize_apply, coe_realize_apply, hτ, ← StdSimplex.comp_affineMapMk]
  rfl

/-- A face of a realized simplex lies in it. -/
theorem range_realize_comp_subset {n k : ℕ} (σ : Fin (n + 1) → K) (f : Fin (k + 1) → Fin (n + 1)) :
    range (realize hK (σ ∘ f)) ⊆ range (realize hK σ) := by
  rintro _ ⟨t, rfl⟩
  exact ⟨StdSimplex.map f t, (realize_comp hK σ f t).symm⟩

/-- `IsSubdivisionSimplex hK σ τ`: the affine simplex `τ` is a simplex of the barycentric
subdivision `sd(σ) = b_σ · sd(∂σ)` of `σ`. -/
inductive IsSubdivisionSimplex : {n : ℕ} → (Fin (n + 1) → K) → (Fin (n + 1) → K) → Prop
  /-- A vertex is its own subdivision. -/
  | vertex (σ : Fin 1 → K) : IsSubdivisionSimplex σ σ
  /-- The cone from `b_σ` on a simplex of the subdivision of the `i`-th facet of `σ`. -/
  | cone {n : ℕ} (σ : Fin (n + 2) → K) (i : Fin (n + 2)) {τ : Fin (n + 1) → K} :
      IsSubdivisionSimplex (σ ∘ i.succAbove) τ →
        IsSubdivisionSimplex σ (cone (simplexBarycenter hK σ) τ)

variable {hK}

/-- The vertices of a simplex of the subdivision of `σ` lie in `σ`. -/
theorem IsSubdivisionSimplex.mem_range_realize {n : ℕ} {σ τ : Fin (n + 1) → K}
    (h : IsSubdivisionSimplex hK σ τ) (j : Fin (n + 1)) : τ j ∈ range (realize hK σ) := by
  induction h with
  | vertex σ => exact ⟨.single j, realize_single hK σ j⟩
  | cone σ i _ ih =>
    exact Fin.cases (simplexBarycenter_mem_range hK σ)
      (fun j => range_realize_comp_subset hK σ i.succAbove (ih j)) j

/-- A simplex of the subdivision of `σ` lies in `σ`. -/
theorem IsSubdivisionSimplex.range_realize_subset {n : ℕ} {σ τ : Fin (n + 1) → K}
    (h : IsSubdivisionSimplex hK σ τ) : range (realize hK τ) ⊆ range (realize hK σ) :=
  AffineChains.range_realize_subset hK h.mem_range_realize

/-- **Diameter contraction.** The vertex set of a simplex of the barycentric subdivision of an
affine `n`-simplex `σ` has diameter at most `n / (n + 1)` times that of `σ`. -/
theorem IsSubdivisionSimplex.diam_le {n : ℕ} {σ τ : Fin (n + 1) → K}
    (h : IsSubdivisionSimplex hK σ τ) :
    diam (range (position L ∘ τ)) ≤ n / (n + 1) * diam (range (position L ∘ σ)) := by
  induction h with
  | vertex σ =>
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    rw [diam_subsingleton (subsingleton_range _)]
    simp
  | @cone n σ i τ hτ ih =>
    set D := diam (range (position L ∘ σ))
    have hD : 0 ≤ D := diam_nonneg
    have hface : diam (range (position L ∘ σ ∘ i.succAbove)) ≤ D :=
      diam_mono (range_comp_subset_range i.succAbove (position L ∘ σ)) (finite_range _).isBounded
    have hfrac : (n : ℝ) / (n + 1) ≤ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith
    have hapex (j : Fin (n + 1)) :
        dist (position L (simplexBarycenter hK σ)) (position L (τ j)) ≤
          ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1) * D :=
      dist_position_simplexBarycenter_le hK σ
        (range_realize_comp_subset hK σ i.succAbove (hτ.mem_range_realize j))
    have hbase (j k : Fin (n + 1)) :
        dist (position L (τ j)) (position L (τ k)) ≤ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1) * D :=
      calc dist (position L (τ j)) (position L (τ k))
          ≤ diam (range (position L ∘ τ)) :=
            dist_le_diam_of_mem (finite_range _).isBounded ⟨j, rfl⟩ ⟨k, rfl⟩
        _ ≤ n / (n + 1) * D := ih.trans (by gcongr)
        _ ≤ _ := by gcongr
    refine diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) j <;> refine Fin.cases ?_ (fun k => ?_) k
    · simp only [Function.comp_apply, Fin.cons_zero, dist_self]
      positivity
    · simpa only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ] using hapex k
    · simpa only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ, dist_comm] using hapex j
    · simpa only [Function.comp_apply, Fin.cons_succ] using hbase j k

/-- **Diameter contraction**, for the realized simplices: every simplex of the barycentric
subdivision of an affine `n`-simplex `σ` has diameter at most `n / (n + 1) · diam σ`. -/
theorem IsSubdivisionSimplex.diam_range_realize_le {n : ℕ} {σ τ : Fin (n + 1) → K}
    (h : IsSubdivisionSimplex hK σ τ) :
    diam (range (position L ∘ realize hK τ)) ≤
      n / (n + 1) * diam (range (position L ∘ realize hK σ)) := by
  rw [diam_range_position_realize, diam_range_position_realize]
  exact h.diam_le

/-- An affine map of ambient simplices carrying `K` into `K'` carries simplices of the
subdivision of `σ` to simplices of the subdivision of the image of `σ`. -/
theorem IsSubdivisionSimplex.mapsTo {m' : ℕ} {K' : Set (StdSimplex ℝ (Fin (m' + 1)))}
    (hK' : IsConvexSet ℝ K')
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (m + 1))) (StdSimplex ℝ (Fin (m' + 1))))
    (hF : MapsTo F K K') {n : ℕ} {σ τ : Fin (n + 1) → K} (h : IsSubdivisionSimplex hK σ τ) :
    IsSubdivisionSimplex hK' (hF.restrict F K K' ∘ σ) (hF.restrict F K K' ∘ τ) := by
  induction h with
  | vertex σ => exact .vertex _
  | cone σ i _ ih =>
    have h := IsSubdivisionSimplex.cone (hK := hK') (hF.restrict F K K' ∘ σ) i ih
    rw [simplexBarycenter_mapsTo hK hK' F hF] at h
    convert h using 1
    exact Fin.comp_cons _ _ _

/-! ### Iterated subdivision -/

variable (hK) in
/-- `IsIteratedSubdivisionSimplex hK N σ τ`: the affine simplex `τ` is a simplex of the
`N`-fold barycentric subdivision of `σ`. -/
inductive IsIteratedSubdivisionSimplex {n : ℕ} :
    ℕ → (Fin (n + 1) → K) → (Fin (n + 1) → K) → Prop
  /-- No subdivision. -/
  | zero (σ : Fin (n + 1) → K) : IsIteratedSubdivisionSimplex 0 σ σ
  /-- A simplex of the subdivision of a simplex of the `N`-fold subdivision. -/
  | succ {N : ℕ} {σ τ ρ : Fin (n + 1) → K} :
      IsIteratedSubdivisionSimplex N σ τ → IsSubdivisionSimplex hK τ ρ →
        IsIteratedSubdivisionSimplex (N + 1) σ ρ

/-- A simplex of the `N`-fold subdivision of `σ` lies in `σ`. -/
theorem IsIteratedSubdivisionSimplex.range_realize_subset {n N : ℕ} {σ τ : Fin (n + 1) → K}
    (h : IsIteratedSubdivisionSimplex hK N σ τ) :
    range (realize hK τ) ⊆ range (realize hK σ) := by
  induction h with
  | zero σ => exact subset_rfl
  | succ _ hρ ih => exact hρ.range_realize_subset.trans ih

/-- **Iterated diameter contraction.** Every simplex of the `N`-fold barycentric subdivision of
an affine `n`-simplex `σ` has diameter at most `(n / (n + 1)) ^ N · diam σ`. -/
theorem IsIteratedSubdivisionSimplex.diam_range_realize_le {n N : ℕ} {σ τ : Fin (n + 1) → K}
    (h : IsIteratedSubdivisionSimplex hK N σ τ) :
    diam (range (position L ∘ realize hK τ)) ≤
      ((n : ℝ) / (n + 1)) ^ N * diam (range (position L ∘ realize hK σ)) := by
  induction h with
  | zero σ => simp
  | @succ N σ τ ρ _ hρ ih =>
    calc diam (range (position L ∘ realize hK ρ))
        ≤ n / (n + 1) * diam (range (position L ∘ realize hK τ)) := hρ.diam_range_realize_le
      _ ≤ n / (n + 1) * (((n : ℝ) / (n + 1)) ^ N * diam (range (position L ∘ realize hK σ))) := by
          gcongr
      _ = _ := by ring

/-- An affine map of ambient simplices carrying `K` into `K'` preserves iterated subdivision
simplices. -/
theorem IsIteratedSubdivisionSimplex.mapsTo {m' : ℕ} {K' : Set (StdSimplex ℝ (Fin (m' + 1)))}
    (hK' : IsConvexSet ℝ K')
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (m + 1))) (StdSimplex ℝ (Fin (m' + 1))))
    (hF : MapsTo F K K') {n N : ℕ} {σ τ : Fin (n + 1) → K}
    (h : IsIteratedSubdivisionSimplex hK N σ τ) :
    IsIteratedSubdivisionSimplex hK' N (hF.restrict F K K' ∘ σ) (hF.restrict F K K' ∘ τ) := by
  induction h with
  | zero σ => exact .zero _
  | succ _ hρ ih => exact .succ ih (hρ.mapsTo hK' F hF)

end

end TDA.Topology.AffineChains
