import TDA.Reeb.RGraphTranslation
import TDA.Reeb.RGraphExamples

/-!
# Translation of finite ℝ-graphs: fixtures

C1. The 0–1–2–1 cycle at the levels `0 < 1 < 2`, translated by `c`, is the realization of the
same finite data at the levels `c < 1 + c < 2 + c`, and it is at geometric interleaving distance
exactly `|c|` from the cycle.

C2. On the cycle, translation by `0` is isomorphic to the identity, and translation by `1` and
then by `2` is isomorphic to translation by `3`.

E1. The empty graph over `0 < 1` has an empty translate by every `c`, and the distance to it is
`0`. For `c = 1` this differs from `|c| = 1`: the exact self-translation distance needs a
nonempty total space.
-/

open CategoryTheory
open scoped ENNReal

namespace TDA.Reeb.Examples.RGraphTranslation

open TDA.Reeb.RGraph TDA.Reeb.CylinderPresentation
open TDA.Reeb.Examples.Cylinder (S01 emptyData)
open TDA.Reeb.Examples.ConstructibleCylinder (S012)
open TDA.Reeb.RGraph.Examples (cycleData emptyRGraph emptyData_realization_isEmpty)

noncomputable section

/-- The 0–1–2–1 cycle as a graph object. -/
abbrev cycleGraph : RGraphCat := (toRGraph S012).obj cycleData

/-! ## C1. The translated cycle -/

/-- The translate of the cycle is the cycle at the translated levels. -/
def cycleTranslateIso (c : ℝ) :
    (translateRGraph c).obj cycleGraph ≅ (toRGraph (S012.translate c)).obj cycleData :=
  IsRGraph.isoMk (toOverTranslateIso S012 cycleData c)

theorem cycleGraph_nonempty : Nonempty cycleGraph.obj.left :=
  ⟨(ofFiniteData cycleData).ofVertex S012 0 (⟨0, by decide⟩ : cycleData.V 0)⟩

/-- The cycle is at distance exactly `|c|` from its translate by `c`. -/
theorem cycle_translate_distance (c : ℝ) :
    geometricInterleavingDistance cycleGraph ((translateRGraph c).obj cycleGraph) =
      ENNReal.ofReal |c| :=
  geometricInterleavingDistance_translateRGraph_self cycleGraph cycleGraph_nonempty c

/-! ## C2. Zero and composition -/

/-- Translation of the cycle by `0` is isomorphic to the cycle. -/
theorem cycle_translate_zero : Nonempty ((translateRGraph 0).obj cycleGraph ≅ cycleGraph) :=
  ⟨translateRGraphZeroIso.app cycleGraph⟩

/-- Translating the cycle by `1` and then by `2` is translating it by `3`. -/
theorem cycle_translate_one_two :
    Nonempty ((translateRGraph 2).obj ((translateRGraph 1).obj cycleGraph) ≅
      (translateRGraph 3).obj cycleGraph) := by
  rw [show (3 : ℝ) = 1 + 2 by norm_num]
  exact ⟨(translateRGraphCompIso 1 2).app cycleGraph⟩

/-! ## E1. The empty graph -/

/-- The empty graph over `0 < 1`. -/
abbrev emptyGraph : RGraphCat := emptyRGraph 1 S01

theorem emptyGraph_isEmpty : IsEmpty emptyGraph.obj.left :=
  emptyData_realization_isEmpty 1 S01

/-- The translate of the empty graph is empty and at distance `0` from it. -/
theorem empty_translate_distance (c : ℝ) :
    IsEmpty ((translateRGraph c).obj emptyGraph).obj.left ∧
      geometricInterleavingDistance emptyGraph ((translateRGraph c).obj emptyGraph) = 0 :=
  ⟨emptyGraph_isEmpty,
    geometricInterleavingDistance_translateRGraph_self_of_isEmpty _ emptyGraph_isEmpty c⟩

/-- Without a nonempty total space the distance to the translate by `1` is not `|1|`. -/
theorem empty_translate_distance_ne :
    geometricInterleavingDistance emptyGraph ((translateRGraph 1).obj emptyGraph) ≠
      ENNReal.ofReal |1| := by
  rw [(empty_translate_distance 1).2, abs_one, ENNReal.ofReal_one]
  exact zero_ne_one

end

end TDA.Reeb.Examples.RGraphTranslation
