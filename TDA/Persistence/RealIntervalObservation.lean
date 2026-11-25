import TDA.Persistence.RealIntervalDecomposition
import TDA.Persistence.FiniteObservation
import TDA.Persistence.ConstructibleQTame

/-!
# Finite observation barcodes of real pointwise finite-dimensional modules

The chosen scalar decomposition is independent of the observation list. Only
finitely many occurrences meet any strict finite sample, and their sampled
intersections, with multiplicities, give exactly the existing rank barcode.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace TDA.Persistence.RealIntervalDecomposition

open CategoryTheory

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

/-- Only finitely many occurrences of the actual scalar decomposition cross
two specified parameters. No bound on the total occurrence type is needed. -/
theorem scalar_crossing_finite (s t : ℝ) :
    Set.Finite {j : ScalarIndex M |
      s ∈ scalarSupport M j ∧ t ∈ scalarSupport M j} :=
  (scalar_finite_active M s).subset (fun _ h => h.1)

private def strictPair (s t : ℝ) (hst : s < t) : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i => if i = 0 then s else t) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all)

/-- The strict structure-map rank counts precisely the actual scalar
occurrences whose support contains both endpoints. -/
theorem persistenceImage_finrank_eq_scalar_crossing (s t : ℝ) (hst : s < t) :
    Module.finrank k (persistenceImage M hst.le) =
      Nat.card {j : ScalarIndex M //
        s ∈ scalarSupport M j ∧ t ∈ scalarSupport M j} := by
  classical
  let c := strictPair s t hst
  have hc0 : c (0 : Fin 2) = s := rfl
  have hc1 : c (1 : Fin 2) = t := rfl
  let V : Set (ScalarIndex M) :=
    {j | ∃ i : Fin 2, c i ∈ scalarSupport M j}
  have hV : V.Finite := finite_observed_scalar M c
  letI : Fintype V := hV.fintype
  let C : Type _ := {j : ScalarIndex M //
    s ∈ scalarSupport M j ∧ t ∈ scalarSupport M j}
  letI : Fintype C := (scalar_crossing_finite M s t).fintype
  letI : ∀ i : Fin 2, FiniteDimensional k
      ((c.toOrderHom.toFunctor ⋙ M).obj i) :=
    fun i => inferInstanceAs (FiniteDimensional k (M.obj (c i)))
  letI : ∀ i : Fin 2, FiniteDimensional k ((reindex c.toOrderHom M).obj i) :=
    fun i => inferInstanceAs (FiniteDimensional k (M.obj (c i)))
  letI : ∀ i : Fin 2, FiniteDimensional k
      ((c.toOrderHom.toFunctor ⋙
        AlgebraicFamily.familyModule (scalarFamily M)).obj i) := by
    intro i
    exact Module.Finite.equiv (((scalarIso M).symm.app (c i)).toLinearEquiv)
  letI : ∀ i : Fin 2, FiniteDimensional k
      ((reindex c.toOrderHom (AlgebraicFamily.familyModule (scalarFamily M))).obj i) := by
    intro i
    exact Module.Finite.equiv (((scalarIso M).symm.app (c i)).toLinearEquiv)
  letI : ∀ i : Fin 2, FiniteDimensional k
      ((c.toOrderHom.toFunctor ⋙ AlgebraicFamily.familyModule
        (fun j : V => scalarFamily M j.val)).obj i) := by
    intro i
    change FiniteDimensional k (DirectSum V
      (fun j => SupportInterval.fiber (k := k) (scalarSupport M j.val) (c i)))
    infer_instance
  letI : ∀ i : Fin 2, FiniteDimensional k
      ((reindex c.toOrderHom (AlgebraicFamily.familyModule
        (fun j : V => scalarFamily M j.val))).obj i) := by
    intro i
    change FiniteDimensional k (DirectSum V
      (fun j => SupportInterval.fiber (k := k) (scalarSupport M j.val) (c i)))
    infer_instance
  letI : ∀ i : Fin 2, FiniteDimensional k
      ((reindex c.toOrderHom (AlgebraicFamily.familyModule
        (fun j : ScalarIndex M => SupportInterval.module (k := k)
          (scalarSupport M j) (scalarSupport_ordConnected M j)))).obj i) := by
    intro i
    exact Module.Finite.equiv (((scalarIso M).symm.app (c i)).toLinearEquiv)
  letI : ∀ i : Fin 2, FiniteDimensional k
      ((reindex c.toOrderHom (AlgebraicFamily.familyModule
        (fun j : V => SupportInterval.module (k := k)
          (scalarSupport M j.val) (scalarSupport_ordConnected M j.val)))).obj i) := by
    intro i
    change FiniteDimensional k (DirectSum V
      (fun j => SupportInterval.fiber (k := k) (scalarSupport M j.val) (c i)))
    infer_instance
  let eScalar := Functor.isoWhiskerLeft c.toOrderHom.toFunctor (scalarIso M).symm
  let eVisible := FiniteObservation.visibleFamilyIso (k := k) c
    (scalarSupport M) (scalarSupport_ordConnected M) V (fun j h => h)
  have hrank : Module.finrank k (persistenceImage M hst.le) =
      ∑ j : V, if s ∈ scalarSupport M j.val ∧ t ∈ scalarSupport M j.val
        then 1 else 0 := by
    calc
      _ = structureMapRank (reindex c.toOrderHom M) 0 1 (by decide) := by
        unfold structureMapRank persistenceImage
        rw [structureMapLinear_reindex]
        rfl
      _ = structureMapRank (reindex c.toOrderHom
          (AlgebraicFamily.familyModule (scalarFamily M))) 0 1 (by decide) :=
        structureMapRank_eq_of_iso eScalar 0 1 (by decide)
      _ = structureMapRank (reindex c.toOrderHom
          (AlgebraicFamily.familyModule (fun j : V => scalarFamily M j.val)))
          0 1 (by decide) :=
        structureMapRank_eq_of_iso eVisible 0 1 (by decide)
      _ = ∑ j : V, if s ∈ scalarSupport M j.val ∧ t ∈ scalarSupport M j.val
            then 1 else 0 := by
        change structureMapRank (reindex c.toOrderHom
          (AlgebraicFamily.familyModule (fun j : V =>
            SupportInterval.module (k := k) (scalarSupport M j.val)
              (scalarSupport_ordConnected M j.val)))) 0 1 (by decide) = _
        simpa only [hc0, hc1] using
          (FiniteObservation.finite_family_sampled_rank (k := k) c
            (fun j : V => scalarSupport M j.val)
            (fun j : V => scalarSupport_ordConnected M j.val)
            0 1 (by decide))
  rw [hrank]
  let e : {j : V // s ∈ scalarSupport M j.val ∧ t ∈ scalarSupport M j.val} ≃ C :=
    { toFun := fun j => ⟨j.val.val, j.property⟩
      invFun := fun j =>
        ⟨⟨j.val, ⟨0, by change s ∈ scalarSupport M j.val; exact j.property.1⟩⟩,
          j.property⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
  calc
    _ = Fintype.card {j : V //
        s ∈ scalarSupport M j.val ∧ t ∈ scalarSupport M j.val} := by
      rw [Fintype.card_subtype]
      exact Finset.sum_boole
        (fun j : V => s ∈ scalarSupport M j.val ∧ t ∈ scalarSupport M j.val)
        Finset.univ
    _ = Fintype.card C := Fintype.card_congr e
    _ = Nat.card C := (Nat.card_eq_fintype_card).symm

/-- The selected coordinate index types may change under a natural
isomorphism, but their strict crossing multiplicities agree. -/
theorem scalar_crossing_card_eq_of_iso
    {N : PModule.{u,0,u} k ℝ} [∀ t, FiniteDimensional k (N.obj t)]
    (e : M ≅ N) (s t : ℝ) (hst : s < t) :
    Nat.card {j : ScalarIndex M //
      s ∈ scalarSupport M j ∧ t ∈ scalarSupport M j} =
    Nat.card {j : ScalarIndex N //
      s ∈ scalarSupport N j ∧ t ∈ scalarSupport N j} := by
  rw [← persistenceImage_finrank_eq_scalar_crossing M s t hst,
    ← persistenceImage_finrank_eq_scalar_crossing N s t hst]
  exact persistenceImage_finrank_eq_of_iso e hst.le

end TDA.Persistence.RealIntervalDecomposition
