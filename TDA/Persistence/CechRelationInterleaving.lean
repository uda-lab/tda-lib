import TDA.Filtration.CechRelation
import TDA.Persistence.SimplicialMultivaluedInterleaving
import TDA.Persistence.SublevelConstructible

/-!
# Different-label ambient Čech interleavings

A relation between two configurations in the same ambient space, total in both
directions, induces canonical homology interleavings at its displacement budget.
This works for both infimum-radius sublevels and exact closed-ball nerves, over
arbitrary rings. Finite labels and field coefficients give a bound on the full
radius-filter diagrams, with each configuration's own critical grid.
-/

universe u v w

namespace TDA.Persistence.Cech

open TDA.Filtration
open scoped NNReal ENNReal

noncomputable section

variable {Z : Type w} [PseudoMetricSpace Z] {V W : Type u}
variable [LinearOrder V] [LinearOrder W]
variable (R : Type v) [Ring R] (p : V → Z) (q : W → Z)
variable {C : SetRel V W} {ε : ℝ≥0}
variable (hCT : Relator.LeftTotal (fun v w => (v, w) ∈ C))
variable (hIT : Relator.LeftTotal (fun w v => (w, v) ∈ C.inv))
variable (h : ∀ v w, (v, w) ∈ C → dist (p v) (q w) ≤ (ε : ℝ))

omit [LinearOrder V] [LinearOrder W] in
include h in
private theorem inverse_displacement :
    ∀ w v, (w, v) ∈ C.inv → dist (q w) (p v) ≤ (ε : ℝ) := by
  intro w v hwv
  exact (dist_comm _ _).trans_le (h v w hwv)

/-- Canonical relation and converse maps interleave the radius-filter homology modules. -/
def relationInterleaving (n : ℕ) :
    RealInterleaving ε (sublevelModule R (Cech.filter p) n)
      (sublevelModule R (Cech.filter q) n) :=
  multivaluedSimplicialHomologyConverseInterleaving R hCT hIT
    (Cech.isShiftedSimplicialRelation_of_dist_le p q h)
    (Cech.isShiftedSimplicialRelation_of_dist_le q p (inverse_displacement p q h)) n

@[simp] theorem relationInterleaving_φ (n : ℕ) :
    (relationInterleaving R p q hCT hIT h n).φ =
      multivaluedSimplicialHomologyMapNNReal R hCT
        (Cech.isShiftedSimplicialRelation_of_dist_le p q h) n := rfl

@[simp] theorem relationInterleaving_ψ (n : ℕ) :
    (relationInterleaving R p q hCT hIT h n).ψ =
      multivaluedSimplicialHomologyMapNNReal R hIT
        (Cech.isShiftedSimplicialRelation_of_dist_le q p (by
          intro w v hwv
          exact (dist_comm _ _).trans_le (h v w hwv))) n := rfl

/-- The same canonical construction applies directly to exact closed-ball nerves. -/
def complexRelationInterleaving (n : ℕ) :
    RealInterleaving ε (simplicialHomologyPModule R (Cech.complexFiltration p) n)
      (simplicialHomologyPModule R (Cech.complexFiltration q) n) :=
  multivaluedSimplicialHomologyConverseInterleaving R hCT hIT
    (Cech.isShiftedSimplicialRelation_complex_of_dist_le p q h)
    (Cech.isShiftedSimplicialRelation_complex_of_dist_le q p
      (inverse_displacement p q h)) n

@[simp] theorem complexRelationInterleaving_φ (n : ℕ) :
    (complexRelationInterleaving R p q hCT hIT h n).φ =
      multivaluedSimplicialHomologyMapNNReal R hCT
        (Cech.isShiftedSimplicialRelation_complex_of_dist_le p q h) n := rfl

@[simp] theorem complexRelationInterleaving_ψ (n : ℕ) :
    (complexRelationInterleaving R p q hCT hIT h n).ψ =
      multivaluedSimplicialHomologyMapNNReal R hIT
        (Cech.isShiftedSimplicialRelation_complex_of_dist_le q p (by
          intro w v hwv
          exact (dist_comm _ _).trans_le (h v w hwv))) n := rfl

include hCT hIT h in
theorem realInterleavingDistance_le_of_relation (n : ℕ) :
    realInterleavingDistance (sublevelModule R (Cech.filter p) n)
      (sublevelModule R (Cech.filter q) n) ≤ (ε : ℝ≥0∞) :=
  (relationInterleaving R p q hCT hIT h n).distance_le

include hCT hIT h in
theorem complex_realInterleavingDistance_le_of_relation (n : ℕ) :
    realInterleavingDistance (simplicialHomologyPModule R (Cech.complexFiltration p) n)
      (simplicialHomologyPModule R (Cech.complexFiltration q) n) ≤ (ε : ℝ≥0∞) :=
  (complexRelationInterleaving R p q hCT hIT h n).distance_le

include hCT hIT h in
/-- Full finite-diagram stability across different label types and critical grids. -/
theorem bottleneck_dgm_le_of_relation [Fintype V] [Fintype W]
    (k : Type u) [Field k] (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) ≤ (ε : ℝ≥0∞) := by
  rw [← moduleDiagram_sublevelModule k n (Cech.filter p),
    ← moduleDiagram_sublevelModule k n (Cech.filter q)]
  exact FiniteConstructible.bottleneck_le_of_interleaving
    (sublevelModule_isConstructible k n (Cech.filter p))
    (sublevelModule_isConstructible k n (Cech.filter q))
    (sublevelModule_finiteDimensional k n (Cech.filter p))
    (sublevelModule_finiteDimensional k n (Cech.filter q))
    (relationInterleaving k p q hCT hIT h n)

end
end TDA.Persistence.Cech
