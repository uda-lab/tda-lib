import TDA.Persistence.IntervalDecompositionUniqueness
import TDA.Persistence.RealIntervalDecomposition

set_option autoImplicit false

/-!
# Client statements of the uniqueness of interval decompositions

Each statement is written as a downstream client writes it. The inputs fall in two groups.

* Three statements over the index type `Fin 3`, with the coefficient field `ℚ` and the supports
  `Set.Icc 0 1`, `Set.Ioo 0 1` and `Set.Ico 0 1` of `ℝ` (closed, open and half-open at the right
  end) listed in two orders, `supports₁` and `supports₂`, and an isomorphism of the two algebraic
  sums supplied by the client. They state the bijection of `Fin 3` that preserves supports, its
  value at the position of the closed interval, and the equality of the numbers of summands with
  support `Set.Icc 0 1` (the multiplicity of the closed interval).
* Two statements over an arbitrary index type `J : Type`, with the field `ℚ`, a pointwise
  finite-dimensional module `M`, and a decomposition of `M` into nonempty interval modules
  supplied by the client. They match the client decomposition with the one returned by
  `RealIntervalDecomposition.exists_interval_decomposition` and derive finite activity of the
  client decomposition from that of the returned one. No finiteness of the client index type or
  of the client decomposition is assumed.
-/

namespace TDA.Persistence.IntervalDecompositionUniquenessClientExamples

open CategoryTheory TDA.Persistence TDA.Persistence.AlgebraicFamily

/-- The unit intervals with closed, open and half-open right ends in the order closed, open,
half-open. -/
def supports₁ : Fin 3 → Set ℝ := ![Set.Icc 0 1, Set.Ioo 0 1, Set.Ico 0 1]

/-- The same three supports in the order half-open, closed, open. -/
def supports₂ : Fin 3 → Set ℝ := ![Set.Ico 0 1, Set.Icc 0 1, Set.Ioo 0 1]

theorem supports₁_ordConnected : ∀ j, (supports₁ j).OrdConnected := by
  intro j
  fin_cases j
  · exact Set.ordConnected_Icc
  · exact Set.ordConnected_Ioo
  · exact Set.ordConnected_Ico

theorem supports₂_ordConnected : ∀ j, (supports₂ j).OrdConnected := by
  intro j
  fin_cases j
  · exact Set.ordConnected_Ico
  · exact Set.ordConnected_Icc
  · exact Set.ordConnected_Ioo

theorem supports₁_nonempty : ∀ j, (supports₁ j).Nonempty := by
  intro j
  fin_cases j
  · exact ⟨0, by simp [supports₁]⟩
  · exact ⟨1 / 2, by norm_num [supports₁]⟩
  · exact ⟨0, by simp [supports₁]⟩

theorem supports₂_nonempty : ∀ j, (supports₂ j).Nonempty := by
  intro j
  fin_cases j
  · exact ⟨0, by simp [supports₂]⟩
  · exact ⟨0, by simp [supports₂]⟩
  · exact ⟨1 / 2, by norm_num [supports₂]⟩

/-- Two lists of the closed, open and half-open unit intervals whose algebraic sums are
isomorphic are matched by a bijection of `Fin 3` that preserves the supports. -/
theorem exists_equiv_unit_intervals
    (e : familyModule (fun j => SupportInterval.module (k := ℚ) (supports₁ j)
        (supports₁_ordConnected j)) ≅
      familyModule (fun j => SupportInterval.module (k := ℚ) (supports₂ j)
        (supports₂_ordConnected j))) :
    ∃ σ : Fin 3 ≃ Fin 3, ∀ j, supports₂ (σ j) = supports₁ j :=
  exists_equiv_support_of_iso _ _ supports₁_nonempty _ _ supports₂_nonempty e

/-- The bijection sends the position of the closed interval to its position in the second
list; the three supports are pairwise distinct. -/
theorem equiv_unit_intervals_zero
    (e : familyModule (fun j => SupportInterval.module (k := ℚ) (supports₁ j)
        (supports₁_ordConnected j)) ≅
      familyModule (fun j => SupportInterval.module (k := ℚ) (supports₂ j)
        (supports₂_ordConnected j))) :
    ∃ σ : Fin 3 ≃ Fin 3, (∀ j, supports₂ (σ j) = supports₁ j) ∧ σ 0 = 1 := by
  obtain ⟨σ, hσ⟩ := exists_equiv_unit_intervals e
  refine ⟨σ, hσ, ?_⟩
  have h0 : supports₂ (σ 0) = Set.Icc 0 1 := hσ 0
  have h1 : (1 : ℝ) ∈ supports₂ (σ 0) := by
    rw [h0]
    exact ⟨by norm_num, le_rfl⟩
  generalize σ 0 = a at h0 h1
  fin_cases a
  · simp [supports₂] at h1
  · rfl
  · simp [supports₂] at h1

/-- The number of summands with support the closed unit interval is the same in the two
lists. -/
theorem mk_closed_unit_interval
    (e : familyModule (fun j => SupportInterval.module (k := ℚ) (supports₁ j)
        (supports₁_ordConnected j)) ≅
      familyModule (fun j => SupportInterval.module (k := ℚ) (supports₂ j)
        (supports₂_ordConnected j))) :
    Cardinal.mk {j // supports₁ j = Set.Icc 0 1} =
      Cardinal.mk {j // supports₂ j = Set.Icc 0 1} :=
  mk_support_fiber_eq_of_iso _ _ supports₁_nonempty _ _ supports₂_nonempty e _

/-- A decomposition of a pointwise finite-dimensional real persistence module into nonempty
interval modules, supplied by a client, is matched by a bijection of the index types that
preserves supports with the decomposition returned by `exists_interval_decomposition`, whose
data are returned with the bijection. -/
theorem client_decomposition_matches_chosen (M : PModule.{0,0,0} ℚ ℝ)
    [∀ t, FiniteDimensional ℚ (M.obj t)] {J : Type} (I : J → Set ℝ)
    (hI : ∀ j, (I j).OrdConnected) (hne : ∀ j, (I j).Nonempty)
    (e : M ≅ familyModule (fun j => SupportInterval.module (k := ℚ) (I j) (hI j))) :
    ∃ (J' : Type) (I' : J' → Set ℝ) (hI' : ∀ j, (I' j).OrdConnected),
      (∀ j, (I' j).Nonempty) ∧
      Nonempty (M ≅ familyModule (fun j => SupportInterval.module (k := ℚ) (I' j) (hI' j))) ∧
      (∀ t, {j | t ∈ I' j}.Finite) ∧ ∃ σ : J ≃ J', ∀ j, I' (σ j) = I j := by
  obtain ⟨J', I', hI', hne', he', hfin'⟩ :=
    RealIntervalDecomposition.exists_interval_decomposition M
  obtain ⟨e'⟩ := he'
  exact ⟨J', I', hI', hne', ⟨e'⟩, hfin',
    exists_equiv_support_of_iso_of_iso I hI hne I' hI' hne' e e'⟩

/-- A client decomposition of a pointwise finite-dimensional real persistence module into
nonempty interval modules has finitely many summands active at each parameter: the finite
activity of the decomposition of `exists_interval_decomposition` is transported along the
bijection of the index types. -/
theorem client_decomposition_finite_activity (M : PModule.{0,0,0} ℚ ℝ)
    [∀ t, FiniteDimensional ℚ (M.obj t)] {J : Type} (I : J → Set ℝ)
    (hI : ∀ j, (I j).OrdConnected) (hne : ∀ j, (I j).Nonempty)
    (e : M ≅ familyModule (fun j => SupportInterval.module (k := ℚ) (I j) (hI j))) (t : ℝ) :
    {j | t ∈ I j}.Finite := by
  obtain ⟨J', I', hI', hne', ⟨e'⟩, hfin'⟩ :=
    RealIntervalDecomposition.exists_interval_decomposition M
  obtain ⟨σ, hσ⟩ := exists_equiv_support_of_iso_of_iso I hI hne I' hI' hne' e e'
  refine ((hfin' t).image σ.symm).subset ?_
  intro j hj
  refine ⟨σ j, ?_, σ.symm_apply_apply j⟩
  change t ∈ I' (σ j)
  rw [hσ j]
  exact hj

end TDA.Persistence.IntervalDecompositionUniquenessClientExamples
