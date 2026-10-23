import TDA.Topology.FiniteGromovProkhorovWitness
import TDA.Persistence.MulticoverNerve

/-!
# SR homology comparisons on a common GP ambient

A concrete GP witness supplies natural maps from both normalized
subdivision-Rips homology diagrams to their large-face cover nerves, using
the same finite sup-norm ambient as its spatial multicover interleaving.
Invertibility of these comparison maps remains a separate obligation.
-/

set_option autoImplicit false
open scoped NNReal ENNReal
universe u v w
namespace TDA.Topology.FiniteGromovProkhorov
open CategoryTheory TDA.Topology.MeasureBifiltration
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
variable [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
open TDA.Persistence TDA.Persistence.SubdivisionRips TDA.Simplicial
attribute [local instance] TDA.Persistence.SubdivisionRips.vertexOrder

/-- The same GP witness gives the concrete natural comparison from the first
normalized SR homology diagram to its large-face cover nerve homology. -/
noncomputable def SupNormWitness.leftHomologyComparison {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    homology R (inferInstance : MetricSpace X) n ⟶
      simplicialHomologyPModule R (largeFaceNerveBifiltration s.left) n :=
  ripsHomologyToLargeFaceNerve R _ s.left
    (fun x x' => (s.left_isometry.dist_eq x x').symm) n

/-- The second normalized SR module has its corresponding actual comparison
on the same ambient used by the interleaving. -/
noncomputable def SupNormWitness.rightHomologyComparison {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    homology R (inferInstance : MetricSpace Y) n ⟶
      simplicialHomologyPModule R (largeFaceNerveBifiltration s.right) n :=
  ripsHomologyToLargeFaceNerve R _ s.right
    (fun y y' => (s.right_isometry.dist_eq y y').symm) n
end TDA.Topology.FiniteGromovProkhorov
