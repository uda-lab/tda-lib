import TDA.Persistence.DecoratedRectangleTopology
import TDA.Persistence.IntegerContentAtoms
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Nat

/-!
# Atomic-content acceptance fixtures

The cut fixtures distinguish both endpoint decorations. Counting finite subsets of the
discrete natural numbers gives a content whose extracted multiplicity is one everywhere:
compact-cell representations are finite although global support is infinite.
-/

namespace TDA.Persistence.RectangleMeasure

open Set MeasureTheory
open scoped Classical

/-- The lower edge excludes the minus cut and includes the plus cut. -/
theorem cutCell_lower_decoration_example :
    minusCut (0 : ℝ) ∉ cutCell 0 1 ∧ plusCut (0 : ℝ) ∈ cutCell 0 1 := by
  norm_num [cutCell, minusCut, plusCut]

/-- The upper edge includes the minus cut and excludes the plus cut. -/
theorem cutCell_upper_decoration_example :
    minusCut (1 : ℝ) ∈ cutCell 0 1 ∧ plusCut (1 : ℝ) ∉ cutCell 0 1 := by
  norm_num [cutCell, minusCut, plusCut]

private theorem finiteNatCells_ring : IsSetRing {U : Set ℕ | U.Finite} where
  empty_mem := finite_empty
  union_mem := by
    intro U V hU hV
    exact hU.union hV
  sdiff_mem := by
    intro U V hU _
    exact hU.sdiff

/-- Counting content on finite subsets, without a bound on total mass. -/
noncomputable def finiteNatCountingContent : AddContent ℕ {U : Set ℕ | U.Finite} :=
  IsSetRing.addContent_of_union Set.ncard finiteNatCells_ring (by simp)
    (fun hU hV hdis => Set.ncard_union_eq hdis hU hV)

/-- The extracted point multiplicities of counting content are one at every natural number. -/
theorem counting_contentMultiplicity (n : ℕ) :
    contentMultiplicity finiteNatCountingContent n = 1 := by
  have hle := contentMultiplicity_le finiteNatCountingContent (finite_singleton n)
    (mem_singleton n)
  change contentMultiplicity finiteNatCountingContent n ≤ ({n} : Set ℕ).ncard at hle
  simp only [ncard_singleton] at hle
  obtain ⟨U, hU, hnU, hmin⟩ := exists_cell_eq_contentMultiplicity finiteNatCountingContent n
    ⟨{n}, finite_singleton n, mem_singleton n⟩
  have hpos : 0 < contentMultiplicity finiteNatCountingContent n := by
    rw [← hmin]
    exact (Set.ncard_pos hU).mpr ⟨n, hnU⟩
  omega

/-- Local atomic extraction permits infinite global support. -/
theorem counting_content_infinite_support :
    Set.Infinite {n : ℕ | 0 < contentMultiplicity finiteNatCountingContent n} := by
  simpa only [counting_contentMultiplicity, Nat.zero_lt_one, ofPred_true] using
    (Set.infinite_univ : Set.Infinite (Set.univ : Set ℕ))

/-- Every finite portion nevertheless has a genuine finite local representation. -/
theorem counting_content_local_representation (K : Set ℕ) (hK : K.Finite) :
    ∃ points : Multiset ℕ, (∀ n ∈ points, n ∈ K) ∧
      ∀ U : Set ℕ, U.Finite → U ⊆ K → U.ncard = (points.filter (· ∈ U)).card := by
  classical
  exact exists_local_atomic_representation finiteNatCells_ring.isSetSemiring
    finiteNatCountingContent (fun _ _ => isOpen_discrete _) hK hK.isCompact

end TDA.Persistence.RectangleMeasure
