import TDA.Persistence.FiniteMonoTranslationCounts
import TDA.Persistence.FiniteMonoMatching

/-!
# Quantitative canonical mono matchings for monotone translations

Actual cokernel shortness bounds the source birth by the translated target birth
and covers every long target occurrence. The original canonical labels are used.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

namespace FiniteBarcode

open CategoryTheory

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}
variable [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]

/-- Every matched pair satisfies the translated birth bound, even when the target
bar is short. Death remains the exact death of the canonical mono embedding. -/
theorem monoEmbedding_birth_bounds_of_cokernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hf : ∀ i, Function.Injective (f.app i).hom)
    (hc : TranslationTrivial theta hTheta (finiteCokernel f))
    (i : BarcodeOccurrence s (rankBarcode M)) :
    (occurrence (rankBarcode N) (monoEmbedding f hf i)).birth ≤
        (occurrence (rankBarcode M) i).birth ∧
      (occurrence (rankBarcode M) i).birth ≤
        (theta (occurrence (rankBarcode N) (monoEmbedding f hf i)).birthStage).val := by
  refine ⟨monoEmbedding_birth_le f hf i, ?_⟩
  let a := monoEmbedding f hf i
  let I := occurrence (rankBarcode M) i
  let J := occurrence (rankBarcode N) a
  have hd : J.death = I.death := monoEmbedding_death f hf i
  change I.birth ≤ (theta J.birthStage).val
  by_cases hlong : (theta J.birthStage).val < J.death
  · by_contra h
    have hbefore := deathOrdinal_lt_deathPrefixCount (rankBarcode N) a
    have hafter := deathPrefixCount_le_deathOrdinal (rankBarcode M) i
      (theta J.birthStage).val (lt_of_not_ge h)
    have hcounts := deathPrefixCount_le_translated_of_cokernelTrivial
      theta hTheta f hf hc J.birthStage J.death hlong J.death_le_size
    change deathPrefixCount (rankBarcode N) J.birth J.death ≤
      deathPrefixCount (rankBarcode M) (theta J.birthStage).val J.death at hcounts
    have ho := monoEmbedding_ordinal f hf i
    change deathOrdinal (rankBarcode N) a < deathPrefixCount (rankBarcode N) J.birth J.death
      at hbefore
    change deathPrefixCount (rankBarcode M) (theta J.birthStage).val I.death ≤
      deathOrdinal (rankBarcode M) i at hafter
    change deathOrdinal (rankBarcode N) a = deathOrdinal (rankBarcode M) i at ho
    rw [hd] at hbefore hcounts
    omega
  · -- Short targets need no shifted-count comparison: the common death supplies the bound.
    have hshort : J.death ≤ (theta J.birthStage).val := le_of_not_gt hlong
    exact (Nat.le_of_lt I.birth_lt_death).trans (hd ▸ hshort)

/-- Every target bar surviving its translated birth has exactly one canonical preimage. -/
theorem monoEmbedding_covers_long_of_cokernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hf : ∀ i, Function.Injective (f.app i).hom)
    (hc : TranslationTrivial theta hTheta (finiteCokernel f))
    (a : BarcodeOccurrence s (rankBarcode N))
    (hlong : (theta (occurrence (rankBarcode N) a).birthStage).val <
      (occurrence (rankBarcode N) a).death) :
    ∃! i, monoEmbedding f hf i = a := by
  let J := occurrence (rankBarcode N) a
  have hlo := deathOrdinal_lt_deathPrefixCount (rankBarcode N) a
  have hcounts := deathPrefixCount_le_translated_of_cokernelTrivial
    theta hTheta f hf hc J.birthStage J.death hlong J.death_le_size
  have hcard := deathPrefixCount_le_card (rankBarcode M) (theta J.birthStage).val J.death
  obtain ⟨i, hi⟩ := (monoEmbedding_mem_range_iff f hf a).mpr
    (hlo.trans_le (hcounts.trans hcard))
  exact ⟨i, hi, fun i' hi' => (monoEmbedding f hf).injective (hi'.trans hi.symm)⟩

/-- An unmatched target must be short; short targets may also be matched. -/
theorem monoEmbedding_unmatched_short_of_cokernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hf : ∀ i, Function.Injective (f.app i).hom)
    (hc : TranslationTrivial theta hTheta (finiteCokernel f))
    (a : BarcodeOccurrence s (rankBarcode N)) (ha : a ∉ Set.range (monoEmbedding f hf)) :
    (occurrence (rankBarcode N) a).death ≤
      (theta (occurrence (rankBarcode N) a).birthStage).val := by
  by_contra h
  obtain ⟨i, hi, _⟩ := monoEmbedding_covers_long_of_cokernelTrivial
    theta hTheta f hf hc a (lt_of_not_ge h)
  exact ha ⟨i, hi⟩

end FiniteBarcode
end TDA.Persistence
