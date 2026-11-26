import TDA.Persistence.RealBarcodeRank
import TDA.Persistence.DiagramLaws
import TDA.Persistence.FiniteRankProjectiveResolution
import TDA.Persistence.DiagramRankUniqueness
import Mathlib.Data.Finset.Sort

/-!
# Real barcode ranks and endpoint uniqueness

Actual finite interval families and barcode realizations have structure-map
ranks given by their endpoint occurrence counts. The existing interval-image
and realization-rank formulas supply the rank calculation; no new interval
decomposition is chosen.

Conversely, the counts determine every finite positive endpoint multiset.
This is the real case of `multiset_eq_of_sliceCounts_eq`, which places every
birth and finite death on a common grid and reuses finite-barcode uniqueness
there. It includes empty multisets, repeated intervals and essential right
endpoints.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RealBarcode

open CategoryTheory
open scoped BigOperators Classical

/-- Positive finite endpoint multisets are determined by their interval counts
across all ordered real parameter pairs. This is the real case of
`multiset_eq_of_sliceCounts_eq`; essential deaths remain essential and repeated
endpoints retain their multiplicities. -/
theorem multiset_eq_of_rankCounts_eq (B C : Multiset (ℝ × WithTop ℝ))
    (hB : ∀ p ∈ B, (p.1 : WithTop ℝ) < p.2)
    (hC : ∀ p ∈ C, (p.1 : WithTop ℝ) < p.2)
    (h : ∀ s t : ℝ, s ≤ t →
      B.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) =
      C.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2)) : B = C :=
  multiset_eq_of_sliceCounts_eq B C hB hC h

variable {k : Type u} [Field k]

/-- The rank of an actual barcode realization counts the interval occurrences
covering both parameters. This also permits empty interval supports. -/
theorem rank_realize (D : Diagram ℝ) (s t : ℝ) (hst : s ≤ t) :
    rankOfStructureMap (RealBarcode.realize (k := k) D) hst =
      D.points.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) := by
  exact realize_image_rank D hst

/-- The actual finite product of real interval modules has rank equal to the
number of occurrences covering both parameters. Repeated and empty supports
are allowed, and essential right endpoints are retained. -/
theorem rank_intervalFamily {J : Type} [Fintype J]
    (F : J → ℝ × WithTop ℝ) (s t : ℝ) (hst : s ≤ t) :
    rankOfStructureMap (RealBarcode.familyModule
      (fun a => RealBarcode.intervalModule (k := k) (F a))) hst =
      ∑ a : J, if (F a).1 ≤ s ∧ (t : WithTop ℝ) < (F a).2 then 1 else 0 := by
  classical
  let f := fun i : J => structureMapLinear (intervalModule (k := k) (F i)) hst
  change Module.finrank k (LinearMap.range (LinearMap.piMap f)) = _
  let : ∀ i : J, FiniteDimensional k ((intervalModule (k := k) (F i)).obj s) :=
    fun i => by
      change FiniteDimensional k (fiber (k := k) (F i) s)
      infer_instance
  rw [finrank_range_piMap f]
  apply Finset.sum_congr rfl
  intro i _
  have he : alive (F i) s ∧ alive (F i) t ↔
      (F i).1 ≤ s ∧ (t : WithTop ℝ) < (F i).2 := by
    constructor
    · exact fun h => ⟨h.1.1, h.2.2⟩
    · exact fun h => ⟨⟨h.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hst) h.2⟩,
        ⟨h.1.trans hst, h.2⟩⟩
  change Module.finrank k (persistenceImage (intervalModule (k := k) (F i)) hst) = _
  rw [intervalImage_rank]
  simp only [he]

/-- Positive real barcode diagrams agree whenever their actual realizations
have equal ranks at every ordered pair of parameters. -/
theorem diagram_eq_of_rank_eq (D E : Diagram ℝ) (hD : D.IsPositive) (hE : E.IsPositive)
    (h : ∀ (s t : ℝ) (hst : s ≤ t),
      rankOfStructureMap (realize (k := k) D) hst =
        rankOfStructureMap (realize (k := k) E) hst) : D = E := by
  apply Diagram.ext
  apply multiset_eq_of_rankCounts_eq D.points E.points hD hE
  intro s t hst
  simpa only [rank_realize] using h s t hst

/-- Positive real barcode diagrams with naturally isomorphic realizations are equal,
including multiplicities and essential right endpoints. -/
theorem diagram_eq_of_realize_iso (D E : Diagram ℝ) (hD : D.IsPositive) (hE : E.IsPositive)
    (e : realize (k := k) D ≅ realize (k := k) E) : D = E :=
  diagram_eq_of_rank_eq D E hD hE fun _ _ hst => rankOfStructureMap_iso hst e

/-- Any two positive barcode realizations of one real persistence module have the same
diagram. This is uniqueness of the endpoint multiset, not of the isomorphisms. -/
theorem realization_unique {M : PModule.{u,0,u} k ℝ} (D E : Diagram ℝ)
    (hD : D.IsPositive) (hE : E.IsPositive)
    (e : M ≅ realize (k := k) D) (f : M ≅ realize (k := k) E) : D = E :=
  diagram_eq_of_realize_iso D E hD hE (e.symm ≪≫ f)

end TDA.Persistence.RealBarcode
