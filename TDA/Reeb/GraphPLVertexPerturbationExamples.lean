import TDA.Reeb.GraphPLVertexPerturbation
import TDA.Reeb.GraphRealizationExamples

/-!
# Vertex-height perturbations: fixtures for the piecewise-linear heights

P1. On an empty vertex type, the uniform extended distance of any two piecewise-linear heights is
`0`.

P2. On the single edge, changing the heights from `(0, 0)` to `(0, 1)` turns a horizontal edge into
a nonhorizontal one and gives uniform extended distance exactly `1` between the piecewise-linear
heights.

P3. Interior-bump control. The continuous function `bump` on the single edge vanishes at both
vertices, so its vertex displacement from the zero height is `0`, but it differs from the
piecewise-linear zero height by `1` at the midpoint. The vertex displacement bounds the distance to
the piecewise-linear extension, not to an arbitrary continuous function with the same vertex
values.
-/

namespace TDA.Reeb.Examples.GraphPLVertexPerturbation

open Set TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ half)
open scoped ENNReal

noncomputable section

/-! ## P1. The empty vertex type -/

/-- On an empty vertex type, piecewise-linear heights are at uniform extended distance `0`. -/
theorem empty_edist_ofFun_plHeight (G : SimpleGraph Empty) (h g : Empty → ℝ) :
    edist (UniformFun.ofFun (plHeight G h)) (UniformFun.ofFun (plHeight G g)) = 0 := by
  rw [edist_ofFun_plHeight_eq_edist, edist_pi_def, Finset.univ_eq_empty, Finset.sup_empty]
  rfl

/-! ## P2. The single edge from `(0, 0)` to `(0, 1)` -/

/-- Constant height `0` on the single edge. -/
def flat : Bool → ℝ := fun _ => 0

/-- Height `0` at `false` and `1` at `true`. -/
def tilted : Bool → ℝ := fun b => if b then 1 else 0

/-- The product extended distance of the two vertex heights is `1`. -/
theorem edist_flat_tilted : edist flat tilted = 1 := by
  apply le_antisymm
  · refine edist_pi_le_iff.2 fun b => ?_
    cases b <;> norm_num [flat, tilted, edist_dist, Real.dist_eq]
  · calc (1 : ℝ≥0∞) = edist (flat true) (tilted true) := by
          norm_num [flat, tilted, edist_dist, Real.dist_eq]
      _ ≤ edist flat tilted := edist_le_pi_edist flat tilted true

/-- The horizontal edge becomes nonhorizontal, and the piecewise-linear heights are at uniform
extended distance exactly `1`. -/
theorem flat_tilted_edist_ofFun_plHeight :
    flat d₀.fst = flat d₀.snd ∧ tilted d₀.fst ≠ tilted d₀.snd ∧
      edist (UniformFun.ofFun (plHeight edgeGraph flat))
        (UniformFun.ofFun (plHeight edgeGraph tilted)) = 1 := by
  refine ⟨rfl, by norm_num [tilted, d₀], ?_⟩
  rw [edist_ofFun_plHeight_eq_edist, edist_flat_tilted]

/-! ## P3. Interior-bump control -/

/-- The edge profile `t ↦ 4 t (1 - t)`, symmetric under `t ↦ 1 - t` and `0` at the endpoints. -/
def bumpProfile : C(unitInterval, ℝ) :=
  ⟨fun t => 4 * (t : ℝ) * (1 - (t : ℝ)), by fun_prop⟩

/-- The continuous function on the single edge with vertex values `0` and value
`4 t (1 - t)` at parameter `t` of either dart. -/
def bump : C(Realization edgeGraph, ℝ) :=
  continuousLift edgeGraph (fun _ => 0) (fun _ => bumpProfile)
    (fun _ t => by
      change 4 * ((unitInterval.symm t : unitInterval) : ℝ) *
          (1 - ((unitInterval.symm t : unitInterval) : ℝ)) = 4 * (t : ℝ) * (1 - (t : ℝ))
      rw [unitInterval.coe_symm_eq]
      ring)
    (fun _ => by simp [bumpProfile])

/-- `bump` has vertex displacement `0` from the zero height, yet its uniform extended distance from
the piecewise-linear zero height is at least `1`, attained at the midpoint of the edge. -/
theorem bump_not_controlled :
    edist (UniformFun.ofFun fun v => bump (vertex edgeGraph v)) (UniformFun.ofFun flat) = 0 ∧
      |bump (edgePoint edgeGraph d₀ half) - plHeight edgeGraph flat (edgePoint edgeGraph d₀ half)| =
        1 ∧
      1 ≤ edist (UniformFun.ofFun bump) (UniformFun.ofFun (plHeight edgeGraph flat)) := by
  have hmid : |bump (edgePoint edgeGraph d₀ half) -
      plHeight edgeGraph flat (edgePoint edgeGraph d₀ half)| = 1 := by
    change |4 * (half : ℝ) * (1 - (half : ℝ)) - dartHeight flat d₀ half| = 1
    norm_num [half, dartHeight, flat]
  refine ⟨edist_self _, hmid, ?_⟩
  refine le_trans ?_ (UniformFun.edist_eval_le (x := edgePoint edgeGraph d₀ half))
  rw [edist_dist, Real.dist_eq]
  change 1 ≤ ENNReal.ofReal |bump (edgePoint edgeGraph d₀ half) -
    plHeight edgeGraph flat (edgePoint edgeGraph d₀ half)|
  rw [hmid, ENNReal.ofReal_one]

end

end TDA.Reeb.Examples.GraphPLVertexPerturbation
