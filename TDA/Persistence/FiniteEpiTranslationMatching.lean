import TDA.Persistence.FiniteEpiTranslationCounts
import TDA.Persistence.FiniteEpiMatching

/-!
# Quantitative canonical epi matchings for monotone translations

Actual kernel shortness bounds the death of every selected source occurrence and
covers every source surviving its translated birth. Birth and occurrence labels
remain those of the existing canonical embedding.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteBarcode

open CategoryTheory

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}
variable [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]

/-- Every matched pair has the canonical death order and translated upper bound.
A terminal target death is treated as the finite observation boundary. -/
theorem epiEmbedding_death_bounds_of_kernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom)
    (hk : TranslationTrivial theta hTheta (finiteKernel p))
    (j : BarcodeOccurrence s (rankBarcode N)) :
    (occurrence (rankBarcode N) j).death ≤
        (occurrence (rankBarcode M) (epiEmbedding p hp j)).death ∧
      (occurrence (rankBarcode M) (epiEmbedding p hp j)).death ≤
        (occurrence (rankBarcode N) j).translatedDeath theta := by
  refine ⟨epiEmbedding_death_le p hp j, ?_⟩
  let I := occurrence (rankBarcode M) (epiEmbedding p hp j)
  let J := occurrence (rankBarcode N) j
  change I.death ≤ J.translatedDeath theta
  by_cases hd : J.death < s
  · rw [FiniteInterval.translatedDeath_of_lt J theta hd]
    by_contra h
    have hlo := birthOrdinal_lt_birthSuffixCount (rankBarcode M) (epiEmbedding p hp j)
      (theta ⟨J.death, hd⟩).val (lt_of_not_ge h)
    have hhi := birthSuffixCount_le_birthOrdinal (rankBarcode N) j J.death (le_refl _)
    change birthSuffixCount (rankBarcode N) J.birth J.death ≤
      birthOrdinal (rankBarcode N) j at hhi
    have hcounts := birthSuffixCount_translated_le_of_kernelTrivial theta hTheta p hp hk
      J.birthStage ⟨J.death, hd⟩ (by change J.birth ≤ J.death; exact J.birth_lt_death.le)
    have hb := epiEmbedding_birth p hp j
    have ho := epiEmbedding_ordinal p hp j
    change (occurrence (rankBarcode M) (epiEmbedding p hp j)).birth = J.birth at hb
    rw [hb] at hlo
    change birthSuffixCount (rankBarcode M) J.birth (theta ⟨J.death, hd⟩).val ≤
      birthSuffixCount (rankBarcode N) J.birth J.death at hcounts
    omega
  · have he : J.death = s := by have := J.death_le_size; omega
    rw [FiniteInterval.translatedDeath_terminal J theta he]
    exact I.death_le_size

/-- Every source surviving its translated birth has exactly one canonical epi preimage. -/
theorem epiEmbedding_covers_long_of_kernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom)
    (hk : TranslationTrivial theta hTheta (finiteKernel p))
    (i : BarcodeOccurrence s (rankBarcode M))
    (hlong : (theta (occurrence (rankBarcode M) i).birthStage).val <
      (occurrence (rankBarcode M) i).death) :
    ∃! j, epiEmbedding p hp j = i := by
  let I := occurrence (rankBarcode M) i
  have hlo := birthOrdinal_lt_birthSuffixCount (rankBarcode M) i
    (theta I.birthStage).val hlong
  have hcounts := birthSuffixCount_translated_le_of_kernelTrivial theta hTheta p hp hk
    I.birthStage I.birthStage (le_refl _)
  have hcard := birthSuffixCount_le_card (rankBarcode N) I.birth I.birth
  obtain ⟨j, hj⟩ := (epiEmbedding_mem_range_iff p hp i).mpr
    (hlo.trans_le (hcounts.trans hcard))
  exact ⟨j, hj, fun j' hj' => (epiEmbedding p hp).injective (hj'.trans hj.symm)⟩

/-- An unselected source is short; short source occurrences may also be selected. -/
theorem epiEmbedding_unmatched_short_of_kernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom)
    (hk : TranslationTrivial theta hTheta (finiteKernel p))
    (i : BarcodeOccurrence s (rankBarcode M)) (hi : i ∉ Set.range (epiEmbedding p hp)) :
    (occurrence (rankBarcode M) i).death ≤
      (theta (occurrence (rankBarcode M) i).birthStage).val := by
  by_contra h
  obtain ⟨j, hj, _⟩ := epiEmbedding_covers_long_of_kernelTrivial
    theta hTheta p hp hk i (lt_of_not_ge h)
  exact hi ⟨j, hj⟩

end TDA.Persistence.FiniteBarcode
