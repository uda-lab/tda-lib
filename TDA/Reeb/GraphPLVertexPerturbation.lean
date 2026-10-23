import TDA.Reeb.GraphPLHeight
import TDA.Reeb.Stability

/-!
# Vertex-height perturbations of a fixed graph

Fix `V : Type u` and `G : SimpleGraph V`, and compare two vertex-height functions
`h g : V → ℝ`. On a dart `d` at parameter `t`, the difference of the affine heights is the convex
combination `(1 - t) (h d.fst - g d.fst) + t (h d.snd - g d.snd)` of the endpoint differences.
Hence a vertex budget `|h v - g v| ≤ ε` for every vertex bounds the difference of the
piecewise-linear heights at every point of the realization (`abs_plHeight_sub_le`). No finiteness,
connectivity, nonemptiness or injectivity of the heights is assumed, and the order and number of
distinct vertex heights of `h` and `g` may differ.

Vertex evaluation gives the converse inequality, so the uniform extended distance of the two
piecewise-linear heights, in mathlib's `UniformFun` metric, equals the uniform extended distance of
the vertex heights (`edist_ofFun_plHeight`). For `[Fintype V]` the latter is mathlib's product
extended distance `edist h g`, the finite supremum of the vertex displacements seeded at `0`
(`edist_ofFun_plHeight_eq_edist`); for empty `V` both sides are `0`. The distance on
`V →ᵤ ℝ` and its pointwise characterization are those of `TDA.Reeb.Stability`.

Composing the pointwise bound with the general perturbation interleaving
`TDA.Reeb.perturbationInterleaving` gives the interleaving `vertexHeightInterleaving` of the
interval-component precosheaves of the two heights. Its components are induced by the inclusions
`plHeight G h ⁻¹' I ⊆ plHeight G g ⁻¹' T_ε I`, with the identity on representatives
(`vertexHeightInterleaving_φ_app_mk`, `vertexHeightInterleaving_ψ_app_mk`). The interleaving
distance of these precosheaves is at most the vertex budget. It is also at most the uniform
distance of the vertex heights, by `interleavingDistance_intervalComponents_le_edist`, and hence at
most `edist h g` for finite `V`.

The bound concerns the piecewise-linear extension only: a continuous function on the realization
that agrees with `h` at the vertices can differ from `plHeight G h` by an arbitrary amount inside
an edge. The general perturbation step is de Silva–Munch–Patel, Theorem 4.6(i); the vertex-to-edge
estimate and its assembly here are library results. See `docs/math/reeb-graph-pl.md`.
-/

open Set CategoryTheory TDA.Reeb.GraphRealization
open scoped NNReal ENNReal UniformConvergence

universe u

namespace TDA.Reeb.GraphPL

variable {V : Type u}

section pointwise

variable {G : SimpleGraph V} {h g : V → ℝ}

/-- A vertex budget bounds the difference of the affine dart heights at every parameter. -/
theorem abs_dartHeight_sub_le {ε : ℝ} (hhg : ∀ v, |h v - g v| ≤ ε) (d : G.Dart)
    (t : unitInterval) : |dartHeight h d t - dartHeight g d t| ≤ ε := by
  have h₀ : 0 ≤ (t : ℝ) := t.2.1
  have h₁ : 0 ≤ 1 - (t : ℝ) := sub_nonneg.2 t.2.2
  have hsub : dartHeight h d t - dartHeight g d t =
      (1 - (t : ℝ)) * (h d.fst - g d.fst) + (t : ℝ) * (h d.snd - g d.snd) := by
    unfold dartHeight
    ring
  rw [hsub]
  calc
    |(1 - (t : ℝ)) * (h d.fst - g d.fst) + (t : ℝ) * (h d.snd - g d.snd)|
        ≤ (1 - (t : ℝ)) * |h d.fst - g d.fst| + (t : ℝ) * |h d.snd - g d.snd| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg h₀, abs_of_nonneg h₁]
    _ ≤ (1 - (t : ℝ)) * ε + (t : ℝ) * ε := by
      gcongr
      · exact hhg _
      · exact hhg _
    _ = ε := by ring

variable (G) in
/-- A vertex budget bounds the difference of the piecewise-linear heights at every point of the
realization. -/
theorem abs_plHeight_sub_le {ε : ℝ} (hhg : ∀ v, |h v - g v| ≤ ε) (x : Realization G) :
    |plHeight G h x - plHeight G g x| ≤ ε := by
  induction x using GraphRealization.ind with
  | vertex v => exact hhg v
  | edgePoint d t => exact abs_dartHeight_sub_le hhg d t

end pointwise

section uniform

variable (G : SimpleGraph V) (h g : V → ℝ)

/-- The uniform extended distance of the piecewise-linear heights equals the uniform extended
distance of the vertex heights. -/
theorem edist_ofFun_plHeight :
    edist (UniformFun.ofFun (plHeight G h)) (UniformFun.ofFun (plHeight G g)) =
      edist (UniformFun.ofFun h) (UniformFun.ofFun g) := by
  apply le_antisymm
  · by_cases htop : edist (UniformFun.ofFun h) (UniformFun.ofFun g) = ⊤
    · rw [htop]
      exact le_top
    · rw [← ENNReal.coe_toNNReal htop]
      exact edist_uniformFun_ofFun_le_coe_iff.2 (abs_plHeight_sub_le G
        (edist_uniformFun_ofFun_le_coe_iff.1 (ENNReal.coe_toNNReal htop).ge))
  · rw [UniformFun.edist_le]
    intro v
    exact UniformFun.edist_eval_le (f := UniformFun.ofFun (plHeight G h))
      (g := UniformFun.ofFun (plHeight G g)) (x := vertex G v)

/-- For finitely many vertices, the uniform extended distance of the piecewise-linear heights is
the product extended distance `edist h g = sup_v edist (h v) (g v)`, which is `0` when `V` is
empty. -/
theorem edist_ofFun_plHeight_eq_edist [Fintype V] :
    edist (UniformFun.ofFun (plHeight G h)) (UniformFun.ofFun (plHeight G g)) = edist h g := by
  rw [edist_ofFun_plHeight, UniformFun.edist_def, edist_pi_def, Finset.sup_univ_eq_iSup]
  rfl

end uniform

section interleaving

variable (G : SimpleGraph V) {h g : V → ℝ}

/-- The `ε`-interleaving of the interval-component precosheaves of two piecewise-linear heights
whose vertex heights differ by at most `ε`: the general `perturbationInterleaving` applied to the
pointwise bound `abs_plHeight_sub_le`. -/
def vertexHeightInterleaving {ε : ℝ≥0} (hhg : ∀ v, |h v - g v| ≤ ε) :
    Interleaving ε (intervalComponents (plHeight G h)) (intervalComponents (plHeight G g)) :=
  perturbationInterleaving (abs_plHeight_sub_le G hhg)

/-- `vertexHeightInterleaving` is the general perturbation interleaving of the two heights. -/
theorem vertexHeightInterleaving_eq {ε : ℝ≥0} (hhg : ∀ v, |h v - g v| ≤ ε) :
    vertexHeightInterleaving G hhg = perturbationInterleaving (abs_plHeight_sub_le G hhg) :=
  rfl

/-- The forward map sends the component of `x ∈ plHeight G h ⁻¹' I` to the component of the same
point in `plHeight G g ⁻¹' T_ε I`. -/
@[simp]
theorem vertexHeightInterleaving_φ_app_mk {ε : ℝ≥0} (hhg : ∀ v, |h v - g v| ≤ ε)
    (I : OpenInterval) (x : {x : Realization G // plHeight G h x ∈ OpenInterval.toOpens I}) :
    (vertexHeightInterleaving G hhg).φ.app I (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨x.1, preimage_subset_preimage_thicken (abs_plHeight_sub_le G hhg) I x.2⟩ :
        {y : Realization G // plHeight G g y ∈ OpenInterval.toOpens (OpenInterval.thicken ε I)}) :=
  rfl

/-- The backward map sends the component of `x ∈ plHeight G g ⁻¹' I` to the component of the same
point in `plHeight G h ⁻¹' T_ε I`. -/
@[simp]
theorem vertexHeightInterleaving_ψ_app_mk {ε : ℝ≥0} (hhg : ∀ v, |h v - g v| ≤ ε)
    (I : OpenInterval) (x : {x : Realization G // plHeight G g x ∈ OpenInterval.toOpens I}) :
    (vertexHeightInterleaving G hhg).ψ.app I (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨x.1, preimage_subset_preimage_thicken
          (perturbationBound_symm (abs_plHeight_sub_le G hhg)) I x.2⟩ :
        {y : Realization G // plHeight G h y ∈ OpenInterval.toOpens (OpenInterval.thicken ε I)}) :=
  rfl

/-- A vertex budget `ε` bounds the interleaving distance of the interval-component precosheaves
of the piecewise-linear heights. -/
theorem interleavingDistance_intervalComponents_plHeight_le {ε : ℝ≥0}
    (hhg : ∀ v, |h v - g v| ≤ ε) :
    interleavingDistance (intervalComponents (plHeight G h))
      (intervalComponents (plHeight G g)) ≤ ε :=
  (vertexHeightInterleaving G hhg).interleavingDistance_le

/-- The interleaving distance of the interval-component precosheaves of the piecewise-linear
heights is at most the uniform extended distance of the vertex heights. -/
theorem interleavingDistance_intervalComponents_plHeight_le_edist_ofFun (h g : V → ℝ) :
    interleavingDistance (intervalComponents (plHeight G h))
      (intervalComponents (plHeight G g)) ≤ edist (UniformFun.ofFun h) (UniformFun.ofFun g) :=
  (interleavingDistance_intervalComponents_le_edist _ _).trans_eq (edist_ofFun_plHeight G h g)

/-- For finitely many vertices, the interleaving distance of the interval-component precosheaves
of the piecewise-linear heights is at most `edist h g`. -/
theorem interleavingDistance_intervalComponents_plHeight_le_edist [Fintype V] (h g : V → ℝ) :
    interleavingDistance (intervalComponents (plHeight G h))
      (intervalComponents (plHeight G g)) ≤ edist h g :=
  (interleavingDistance_intervalComponents_le_edist _ _).trans_eq
    (edist_ofFun_plHeight_eq_edist G h g)

end interleaving

end TDA.Reeb.GraphPL
