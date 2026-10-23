import TDA.Filtration.Cech
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-!
# Witness-space change for ambient Čech complexes

Labels `p : V → W` in a pseudometric witness space `W`, mapped into `X` by `f : W → X`,
define two Čech complexes: one with witnesses in `W` and one with witnesses in `X`. When `f`
is an isometry, every witness in `W` is carried to a witness in `X`, so the Čech complex can
only grow and Čech values can only drop. A `1`-Lipschitz map `g : X → W` that fixes the
labelled points moves every ambient witness back into `W` without increasing distances to
the labels, so it reverses both comparisons; with both maps, the complexes and values agree.

The subspace Čech complex of a set `W ⊆ X` and the intrinsic Čech complex of `q : V → X`,
whose witnesses are the labelled points themselves, are the special cases with `f` the
subtype inclusion.
-/

universe u v w

namespace TDA.Filtration.Cech

open TDA.Simplicial

variable {X : Type u} {V : Type v} {W : Type w} [PseudoMetricSpace X] [PseudoMetricSpace W]
variable {f : W → X}

/-- Isometries preserve enclosing radii. -/
theorem radiusAt_comp_of_isometry (hf : Isometry f) (p : V → W) (x : W) (s : Finset V) :
    radiusAt (f ∘ p) (f x) s = radiusAt p x s := by
  unfold radiusAt
  congr 1
  funext v
  exact hf.dist_eq x (p v)

/-- Isometric witness-space enlargement can only add Čech faces. -/
theorem complex_le_complex_comp (hf : Isometry f) (p : V → W) (r : ℝ) :
    complex p r ≤ complex (f ∘ p) r := by
  intro s hs
  obtain ⟨hsn, x, hx⟩ := (mem_complex_iff p r s).1 hs
  exact (mem_complex_iff (f ∘ p) r s).2 ⟨hsn, f x, fun v hv => by
    rw [Function.comp_apply, hf.dist_eq]
    exact hx v hv⟩

/-- Isometric witness-space enlargement can only lower Čech values. -/
theorem filter_comp_value_le (hf : Isometry f) (p : V → W)
    (s : TotalFace (Rips.fullComplex V)) :
    (filter (f ∘ p)).value s ≤ (filter p).value s := by
  obtain ⟨v₀, -⟩ : s.val.Nonempty := s.property
  have : Nonempty W := ⟨p v₀⟩
  refine le_ciInf fun x => ?_
  rw [← radiusAt_comp_of_isometry hf p x s.val]
  exact filter_value_le_radiusAt (f ∘ p) s (f x)

section Retraction

variable {g : X → W}

private theorem dist_retract_le (hg : LipschitzWith 1 g) {p : V → W}
    (hgp : ∀ v, g (f (p v)) = p v) (x : X) (v : V) :
    dist (g x) (p v) ≤ dist x ((f ∘ p) v) := by
  have h := hg.dist_le_mul x (f (p v))
  rw [hgp, NNReal.coe_one, one_mul] at h
  exact h

private theorem radiusAt_retract_le (hg : LipschitzWith 1 g) {p : V → W}
    (hgp : ∀ v, g (f (p v)) = p v) (x : X) (s : Finset V) :
    radiusAt p (g x) s ≤ radiusAt (f ∘ p) x s :=
  (radiusAt_le_iff p (g x) s _).2 ⟨radiusAt_nonneg _ x s, fun v hv =>
    (dist_retract_le hg hgp x v).trans (dist_le_radiusAt (f ∘ p) x hv)⟩

/-- A `1`-Lipschitz map fixing the labelled points moves ambient witnesses back into `W`. -/
theorem complex_comp_le_complex_of_retraction (hg : LipschitzWith 1 g) {p : V → W}
    (hgp : ∀ v, g (f (p v)) = p v) (r : ℝ) : complex (f ∘ p) r ≤ complex p r := by
  intro s hs
  obtain ⟨hsn, x, hx⟩ := (mem_complex_iff (f ∘ p) r s).1 hs
  exact (mem_complex_iff p r s).2 ⟨hsn, g x, fun v hv =>
    (dist_retract_le hg hgp x v).trans (hx v hv)⟩

/-- A `1`-Lipschitz map fixing the labelled points cannot lower Čech values. -/
theorem filter_value_le_filter_comp_value_of_retraction (hg : LipschitzWith 1 g) {p : V → W}
    (hgp : ∀ v, g (f (p v)) = p v) (s : TotalFace (Rips.fullComplex V)) :
    (filter p).value s ≤ (filter (f ∘ p)).value s := by
  obtain ⟨v₀, -⟩ : s.val.Nonempty := s.property
  have : Nonempty X := ⟨f (p v₀)⟩
  exact le_ciInf fun x =>
    (filter_value_le_radiusAt p s (g x)).trans (radiusAt_retract_le hg hgp x s.val)

/-- An isometry with a `1`-Lipschitz retraction onto the labelled points preserves the
Čech complex. -/
theorem complex_comp_eq_of_retraction (hf : Isometry f) (hg : LipschitzWith 1 g) {p : V → W}
    (hgp : ∀ v, g (f (p v)) = p v) (r : ℝ) : complex (f ∘ p) r = complex p r :=
  le_antisymm (complex_comp_le_complex_of_retraction hg hgp r)
    (complex_le_complex_comp hf p r)

/-- An isometry with a `1`-Lipschitz retraction onto the labelled points preserves Čech
values. -/
theorem filter_comp_value_eq_of_retraction (hf : Isometry f) (hg : LipschitzWith 1 g)
    {p : V → W} (hgp : ∀ v, g (f (p v)) = p v) (s : TotalFace (Rips.fullComplex V)) :
    (filter (f ∘ p)).value s = (filter p).value s :=
  le_antisymm (filter_comp_value_le hf p s)
    (filter_value_le_filter_comp_value_of_retraction hg hgp s)

end Retraction

/-! ### Subspace and intrinsic complexes -/

/-- The subspace Čech complex of `W ⊆ X` lies in the ambient one. -/
theorem complex_le_complex_val (W : Set X) (p : V → W) (r : ℝ) :
    complex p r ≤ complex (Subtype.val ∘ p) r :=
  complex_le_complex_comp isometry_subtype_coe p r

/-- Ambient Čech values are at most subspace Čech values. -/
theorem filter_val_value_le (W : Set X) (p : V → W) (s : TotalFace (Rips.fullComplex V)) :
    (filter (Subtype.val ∘ p)).value s ≤ (filter p).value s :=
  filter_comp_value_le isometry_subtype_coe p s

/-- The intrinsic Čech complex, with witnesses among the labelled points, lies in the
ambient one. -/
theorem complex_rangeFactorization_le (q : V → X) (r : ℝ) :
    complex (Set.rangeFactorization q) r ≤ complex q r :=
  complex_le_complex_val (Set.range q) (Set.rangeFactorization q) r

/-- Ambient Čech values are at most intrinsic Čech values. -/
theorem filter_value_le_filter_rangeFactorization_value (q : V → X)
    (s : TotalFace (Rips.fullComplex V)) :
    (filter q).value s ≤ (filter (Set.rangeFactorization q)).value s :=
  filter_val_value_le (Set.range q) (Set.rangeFactorization q) s

end TDA.Filtration.Cech
