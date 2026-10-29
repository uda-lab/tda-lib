import TDA.Persistence.QTameFiniteSaturation
import TDA.Persistence.RipsHausdorffInterleaving
import TDA.Persistence.RipsQTame

/-!
# Finite saturation for Rips homology

The q-tame finite-saturation theorem applies to actual Rips interleavings of
totally bounded metric spaces. This module supplies the Rips q-tameness and the
strict-slack Hausdorff interleaving from their established constructions.
-/

universe u v w

namespace TDA.Persistence.Rips

open TDA.Persistence Metric Set
open scoped NNReal ENNReal

/-- If two isometric images have finite Hausdorff distance and an ε with strict
Hausdorff slack, their q-tame Rips modules admit finite injective edge sets
saturating any prescribed finite sets of bars longer than 2 ε and essential
occurrences. Pair costs are bounded by ε. -/
theorem exists_finite_saturating_matching_of_hausdorff_lt
    {X Y : Type u} [LinearOrder X] [LinearOrder Y]
    [MetricSpace X] [MetricSpace Y]
    (k : Type v) [Field k]
    {Z : Type w} [MetricSpace Z] {f : X → Z} {g : Y → Z}
    (hf : Isometry f) (hg : Isometry g)
    (hfin : hausdorffEDist (range f) (range g) ≠ ⊤)
    {ε : ℝ≥0}
    (hε : 2 * hausdorffDist (range f) (range g) < (ε : ℝ))
    (hX : TotallyBounded (univ : Set X))
    (hY : TotallyBounded (univ : Set Y))
    (n : ℕ)
    (F_X : Finset ((LocallyFiniteDecoratedDiagram.ofQModule
      (Rips.qTame_of_totallyBounded k hX n)).finiteOccurrences))
    (F_Y : Finset ((LocallyFiniteDecoratedDiagram.ofQModule
      (Rips.qTame_of_totallyBounded k hY n)).finiteOccurrences))
    (hLongX : ∀ x ∈ F_X, 2 * (ε : ℝ) <
      ((LocallyFiniteDecoratedDiagram.ofQModule
        (Rips.qTame_of_totallyBounded k hX n)).finitePoint x).2 -
      ((LocallyFiniteDecoratedDiagram.ofQModule
        (Rips.qTame_of_totallyBounded k hX n)).finitePoint x).1)
    (hLongY : ∀ y ∈ F_Y, 2 * (ε : ℝ) <
      ((LocallyFiniteDecoratedDiagram.ofQModule
        (Rips.qTame_of_totallyBounded k hY n)).finitePoint y).2 -
      ((LocallyFiniteDecoratedDiagram.ofQModule
        (Rips.qTame_of_totallyBounded k hY n)).finitePoint y).1)
    (E_X : Finset ((LocallyFiniteDecoratedDiagram.ofQModule
      (Rips.qTame_of_totallyBounded k hX n)).essentialOccurrences))
    (E_Y : Finset ((LocallyFiniteDecoratedDiagram.ofQModule
      (Rips.qTame_of_totallyBounded k hY n)).essentialOccurrences)) :
    FiniteSaturatingMatching ε
      (LocallyFiniteDecoratedDiagram.ofQModule
        (Rips.qTame_of_totallyBounded k hX n))
      (LocallyFiniteDecoratedDiagram.ofQModule
        (Rips.qTame_of_totallyBounded k hY n))
      F_X F_Y E_X E_Y := by
  exact RealInterleaving.exists_finite_saturating_matching
      (Rips.hausdorffInterleavingOfLt k hf hg hfin hε n)
      (Rips.qTame_of_totallyBounded k hX n)
      (Rips.qTame_of_totallyBounded k hY n)
      F_X F_Y hLongX hLongY E_X E_Y

end TDA.Persistence.Rips
