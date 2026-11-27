import TDA.Persistence.IntervalDecompositionUniqueness
import TDA.Persistence.RealIntervalDecomposition

set_option autoImplicit false

/-!
# Client statements of the uniqueness of interval decompositions

Regression fixtures for #1255, family 18 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it.

Inputs used: the coefficient field `ℚ`; the index type `Fin 3` for the first two statements and
an arbitrary `Type` for the third; supports that are the closed, open and half-open unit
intervals `Set.Icc 0 1`, `Set.Ioo 0 1` and `Set.Ico 0 1` of `ℝ`, listed in two different orders;
an isomorphism between the two algebraic sums, supplied by the client; for the third statement a
pointwise finite-dimensional module and a decomposition into nonempty interval modules supplied
by the client. No finiteness of the decompositions is assumed.

* A bijection of `Fin 3` that preserves the listed supports, and the value of that bijection at
  the closed interval.
* The number of summands with a given support agrees in the two lists.
* A client decomposition of a pointwise finite-dimensional module is matched with the
  decomposition of `RealIntervalDecomposition.exists_interval_decomposition`, and has finite
  activity at every parameter.
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
interval modules is matched, by a bijection of the index types preserving the supports, with the
decomposition chosen by `exists_interval_decomposition`. -/
theorem client_decomposition_matches_chosen (M : PModule.{0,0,0} ℚ ℝ)
    [∀ t, FiniteDimensional ℚ (M.obj t)] {J : Type} (I : J → Set ℝ)
    (hI : ∀ j, (I j).OrdConnected) (hne : ∀ j, (I j).Nonempty)
    (e : M ≅ familyModule (fun j => SupportInterval.module (k := ℚ) (I j) (hI j))) :
    ∃ (J' : Type) (I' : J' → Set ℝ) (_ : ∀ j, (I' j).OrdConnected) (σ : J ≃ J'),
      (∀ j, I' (σ j) = I j) ∧ ∀ t, {j | t ∈ I j}.Finite := by
  obtain ⟨J', I', hI', hne', ⟨e'⟩, hfin'⟩ :=
    RealIntervalDecomposition.exists_interval_decomposition M
  obtain ⟨σ, hσ⟩ := exists_equiv_support_of_iso_of_iso I hI hne I' hI' hne' e e'
  refine ⟨J', I', hI', σ, hσ, fun t => ?_⟩
  refine ((hfin' t).image σ.symm).subset ?_
  intro j hj
  refine ⟨σ j, ?_, σ.symm_apply_apply j⟩
  change t ∈ I' (σ j)
  rw [hσ j]
  exact hj

end TDA.Persistence.IntervalDecompositionUniquenessClientExamples
