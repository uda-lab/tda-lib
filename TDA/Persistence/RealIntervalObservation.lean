import TDA.Persistence.RealIntervalDecomposition
import TDA.Persistence.FiniteObservation

/-!
# Finite observation barcodes of real pointwise finite-dimensional modules

The chosen scalar decomposition is independent of the observation list. Only
finitely many occurrences meet any strict finite sample, and their sampled
intersections, with multiplicities, give exactly the existing rank barcode.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RealIntervalDecomposition

variable {k : Type u} [Field k]
  (M : PModule.{u,0,u} k ℝ) [∀ t, FiniteDimensional k (M.obj t)]

/-- A finite sample meets only finitely many occurrences of the chosen real decomposition. -/
theorem finite_observed_scalar {N : ℕ} (c : Fin N ↪o ℝ) :
    Set.Finite {j : ScalarIndex M | ∃ i : Fin N, c i ∈ scalarSupport M j} :=
  FiniteObservation.finite_visible_occurrences c (scalarSupport M)
    (fun i => scalar_finite_active M (c i))

/-- The occurrence multiset obtained by taking every nonempty sampled intersection. -/
noncomputable def sampledBarcode {N : ℕ} (c : Fin N ↪o ℝ) :
    Multiset (FiniteInterval N) := by
  letI : Fintype {j : ScalarIndex M | ∃ i : Fin N, c i ∈ scalarSupport M j} :=
    (finite_observed_scalar M c).fintype
  exact FiniteObservation.finiteFamilyBarcode c
    (fun j : {j : ScalarIndex M | ∃ i : Fin N, c i ∈ scalarSupport M j} =>
      scalarSupport M j.val)

/-- Every real pointwise finite-dimensional module has precisely the observed
barcode of its scalar interval decomposition, with no finite-grid hypothesis. -/
theorem rankBarcode_eq_sampledBarcode {N : ℕ} (c : Fin N ↪o ℝ) :
    rankBarcode (reindex c.toOrderHom M) = sampledBarcode M c := by
  exact FiniteObservation.rankBarcode_of_pfd_decomposition M c
    (scalarSupport M) (scalarSupport_ordConnected M) (scalarIso M).symm

end TDA.Persistence.RealIntervalDecomposition
