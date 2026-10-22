import TDA.Persistence.RankReindex
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Finite sampling examples

Private fixtures exercise empty and identity samples, repeated and constant sampling,
skipped stages, merged interval occurrences, and terminal truncation. They compare
structure-map ranks and canonical barcode multiplicities over `ℚ` and `ZMod 2`.
A constant module with carrier `k × k` also exercises the construction independently
of a supplied barcode realization.
-/

universe u
namespace TDA.Persistence
open scoped BigOperators
open CategoryTheory

private def emptySampling (L : ℕ) : Fin 0 →o Fin L where
  toFun := Fin.elim0
  monotone' := by intro i; exact Fin.elim0 i

private theorem emptySample_cut (L e : ℕ) :
    sampledEndpoint (emptySampling L) e = 0 := by simp [sampledEndpoint]

private theorem emptySample_interval (L : ℕ) (I : FiniteInterval L) :
    I.restrictAlong (emptySampling L) = none := by
  simp [FiniteInterval.restrictAlong, emptySample_cut]

private theorem emptySample_barcode (L : ℕ) (B : Multiset (FiniteInterval L)) :
    reindexBarcode (emptySampling L) B = 0 := by
  induction B using Multiset.induction_on with
  | empty => simp [reindexBarcode]
  | @cons I B ih =>
    change Multiset.filterMap (FiniteInterval.restrictAlong (emptySampling L)) (I ::ₘ B) = 0
    rw [Multiset.filterMap_cons_none I B (emptySample_interval L I)]
    exact ih

private theorem emptySample {L : ℕ} {k : Type u} [Field k]
    (M : PModule.{u,0,u} k (Fin L))
    [∀ i : Fin L, FiniteDimensional k (M.obj i)] :
    rankBarcode (reindex (emptySampling L) M) = 0 := by
  rw [rankBarcode_reindex, emptySample_barcode]

private def emptySource (k : Type u) [Field k] : PModule.{u,0,u} k (Fin 0) where
  obj _ := ModuleCat.of k k
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

private instance emptySourceFD {k : Type u} [Field k] (i : Fin 0) :
    FiniteDimensional k ((emptySource k).obj i) := Fin.elim0 i

private theorem emptySource_diagram_eq_zero {k : Type u} [Field k] :
    rankBarcode (reindex (emptySampling 0) (emptySource k)) = 0 :=
  emptySample (emptySource k)

private theorem identitySample {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) :
    rankBarcode (reindex (OrderHom.id : Fin N →o Fin N)
      (barcodeModule (k := k) B)) = B := by
  simpa only [reindex_id] using rankBarcode_barcodeModule (k := k) B

private def repeatedSample : Fin 3 →o Fin 2 where
  toFun j := ⟨j.val / 2, by omega⟩
  monotone' := by
    intro i j hij
    apply Fin.le_iff_val_le_val.mpr
    dsimp
    have h := Fin.le_iff_val_le_val.mp hij
    omega

private def constantSample : Fin 3 →o Fin 2 where
  toFun _ := 0
  monotone' := by
    intro i j hij
    change (0 : Fin 2) ≤ 0
    exact le_refl _

private def mixedSample : Fin 4 →o Fin 6 where
  toFun j := ⟨if j.val < 2 then 1 else if j.val = 2 then 3 else 4, by split_ifs <;> omega⟩
  monotone' := by
    intro i j hij
    apply Fin.le_iff_val_le_val.mpr
    have h := Fin.le_iff_val_le_val.mp hij
    dsimp
    split_ifs <;> omega

private def sourceBar02 : FiniteInterval 2 := ⟨0, 2, by omega, by omega⟩
private def sourceBar01 : FiniteInterval 2 := ⟨0, 1, by omega, by omega⟩
private def sourceBar12 : FiniteInterval 2 := ⟨1, 2, by omega, by omega⟩
private def targetBar03 : FiniteInterval 3 := ⟨0, 3, by omega, by omega⟩
private def targetBar02 : FiniteInterval 3 := ⟨0, 2, by omega, by omega⟩
private def targetBar23 : FiniteInterval 3 := ⟨2, 3, by omega, by omega⟩

private theorem fieldIdRank {k : Type u} [Field k] :
    Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = 1 := by
  rw [LinearMap.range_id, finrank_top]
  exact Module.finrank_self k

private theorem fieldZeroRank {k : Type u} [Field k] :
    Module.finrank k (LinearMap.range (0 : k →ₗ[k] k)) = 0 := by
  rw [LinearMap.range_zero]
  simp

private instance identityTransitionFD {k : Type u} [Field k] (i : Fin 2) :
    FiniteDimensional k ((identityTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

private instance zeroTransitionFD {k : Type u} [Field k] (i : Fin 2) :
    FiniteDimensional k ((zeroTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

private theorem identitySourceBarcode {k : Type u} [Field k] :
    rankBarcode (identityTransitionDiagram k) =
      ({sourceBar02} : Multiset (FiniteInterval 2)) := by
  have hr : ∀ (i j : Fin 2) (hij : i ≤ j),
      structureMapRank (identityTransitionDiagram k) i j hij =
        structureMapRank (barcodeModule (k := k)
          ({sourceBar02} : Multiset (FiniteInterval 2))) i j hij := by
    intro i j hij
    rw [rank_barcodeMap]
    change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = _
    rw [fieldIdRank]
    fin_cases i <;> fin_cases j <;> decide
  have h := (rankBarcode_eq_iff (identityTransitionDiagram k)
    (barcodeModule (k := k) ({sourceBar02} : Multiset (FiniteInterval 2)))).2 hr
  exact h.trans (rankBarcode_barcodeModule (k := k) _)

private theorem zeroSourceBarcode {k : Type u} [Field k] :
    rankBarcode (zeroTransitionDiagram k) =
      ({sourceBar01, sourceBar12} : Multiset (FiniteInterval 2)) := by
  have hr : ∀ (i j : Fin 2) (hij : i ≤ j),
      structureMapRank (zeroTransitionDiagram k) i j hij =
        structureMapRank (barcodeModule (k := k)
          ({sourceBar01, sourceBar12} : Multiset (FiniteInterval 2))) i j hij := by
    intro i j hij
    rw [rank_barcodeMap]
    fin_cases i <;> fin_cases j
    · change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = _
      rw [fieldIdRank]
      decide
    · change Module.finrank k (LinearMap.range (0 : k →ₗ[k] k)) = _
      rw [fieldZeroRank]
      decide
    · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
    · change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = _
      rw [fieldIdRank]
      decide
  have h := (rankBarcode_eq_iff (zeroTransitionDiagram k)
    (barcodeModule (k := k)
      ({sourceBar01, sourceBar12} : Multiset (FiniteInterval 2)))).2 hr
  exact h.trans (rankBarcode_barcodeModule (k := k) _)

private theorem repeatedIdentityBarcode {k : Type u} [Field k] :
    rankBarcode (reindex repeatedSample (identityTransitionDiagram k)) =
      ({targetBar03} : Multiset (FiniteInterval 3)) := by
  rw [rankBarcode_reindex, identitySourceBarcode]
  decide

private theorem repeatedZeroBarcode {k : Type u} [Field k] :
    rankBarcode (reindex repeatedSample (zeroTransitionDiagram k)) =
      ({targetBar02, targetBar23} : Multiset (FiniteInterval 3)) := by
  rw [rankBarcode_reindex, zeroSourceBarcode]
  decide

private theorem repeatedModuleRanks {k : Type u} [Field k] :
    structureMapRank (reindex repeatedSample (identityTransitionDiagram k))
        (0 : Fin 3) 1 (by decide) = 1 ∧
      structureMapRank (reindex repeatedSample (zeroTransitionDiagram k))
        (0 : Fin 3) 1 (by decide) = 1 ∧
      structureMapRank (reindex repeatedSample (identityTransitionDiagram k))
        (0 : Fin 3) 2 (by decide) = 1 ∧
      structureMapRank (reindex repeatedSample (zeroTransitionDiagram k))
        (0 : Fin 3) 2 (by decide) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [structureMapRank_reindex]
    exact fieldIdRank
  · rw [structureMapRank_reindex]
    exact fieldIdRank
  · rw [structureMapRank_reindex]
    exact fieldIdRank
  · rw [structureMapRank_reindex]
    exact fieldZeroRank

private theorem repeatedBoundaryZero {k : Type u} [Field k] :
    moduleMultiplicityInteger (reindex repeatedSample (identityTransitionDiagram k)) 1 3 = 0 ∧
      moduleMultiplicityInteger (reindex repeatedSample (zeroTransitionDiagram k)) 1 3 = 0 ∧
      moduleMultiplicityInteger (reindex repeatedSample (identityTransitionDiagram k)) 0 1 = 0 ∧
      moduleMultiplicityInteger (reindex repeatedSample (zeroTransitionDiagram k)) 0 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [moduleMultiplicityInteger_reindex _ _ _ _ (by omega) (by omega)]
  · change (∑ x ∈ Finset.Icc 1 0, ∑ y ∈ Finset.Ioc 1 2,
      moduleMultiplicityInteger (identityTransitionDiagram k) x y) = 0
    rw [show Finset.Icc (1 : ℕ) 0 = ∅ by decide]
    simp
  · change (∑ x ∈ Finset.Icc 1 0, ∑ y ∈ Finset.Ioc 1 2,
      moduleMultiplicityInteger (zeroTransitionDiagram k) x y) = 0
    rw [show Finset.Icc (1 : ℕ) 0 = ∅ by decide]
    simp
  · change (∑ x ∈ Finset.Icc 0 0, ∑ y ∈ Finset.Ioc 0 0,
      moduleMultiplicityInteger (identityTransitionDiagram k) x y) = 0
    simp
  · change (∑ x ∈ Finset.Icc 0 0, ∑ y ∈ Finset.Ioc 0 0,
      moduleMultiplicityInteger (zeroTransitionDiagram k) x y) = 0
    simp

private theorem repeatedBirthOneZero {k : Type u} [Field k] :
    moduleMultiplicityInteger (reindex repeatedSample (identityTransitionDiagram k)) 1 2 = 0 ∧
      moduleMultiplicityInteger (reindex repeatedSample (zeroTransitionDiagram k)) 1 2 = 0 := by
  constructor
  all_goals rw [moduleMultiplicityInteger_reindex _ _ _ _ (by omega) (by omega)]
  · change (∑ x ∈ Finset.Icc 1 0, ∑ y ∈ Finset.Ioc 0 1,
      moduleMultiplicityInteger (identityTransitionDiagram k) x y) = 0
    rw [show Finset.Icc (1 : ℕ) 0 = ∅ by decide]
    simp
  · change (∑ x ∈ Finset.Icc 1 0, ∑ y ∈ Finset.Ioc 0 1,
      moduleMultiplicityInteger (zeroTransitionDiagram k) x y) = 0
    rw [show Finset.Icc (1 : ℕ) 0 = ∅ by decide]
    simp

private theorem constantSample_identityBarcode {k : Type u} [Field k] :
    rankBarcode (reindex constantSample (identityTransitionDiagram k)) =
      ({targetBar03} : Multiset (FiniteInterval 3)) := by
  rw [rankBarcode_reindex, identitySourceBarcode]
  decide

private theorem constantSample_zeroBarcode {k : Type u} [Field k] :
    rankBarcode (reindex constantSample (zeroTransitionDiagram k)) =
      ({targetBar03} : Multiset (FiniteInterval 3)) := by
  rw [rankBarcode_reindex, zeroSourceBarcode]
  decide

private theorem constantSampleRank {k : Type u} [Field k] :
    structureMapRank (reindex constantSample (zeroTransitionDiagram k))
      (0 : Fin 3) 2 (by decide) = 1 := by
  rw [structureMapRank_reindex]
  exact fieldIdRank

private theorem rationalTransitionFixtures :
    let Mi := reindex repeatedSample (identityTransitionDiagram ℚ)
    let Mz := reindex repeatedSample (zeroTransitionDiagram ℚ)
    rankBarcode Mi = ({targetBar03} : Multiset (FiniteInterval 3)) ∧
    rankBarcode Mz = ({targetBar02, targetBar23} : Multiset (FiniteInterval 3)) ∧
    (structureMapRank Mi 0 1 (by decide) = 1 ∧
     structureMapRank Mz 0 1 (by decide) = 1 ∧
     structureMapRank Mi 0 2 (by decide) = 1 ∧
     structureMapRank Mz 0 2 (by decide) = 0) ∧
    (moduleMultiplicityInteger Mi 1 3 = 0 ∧
     moduleMultiplicityInteger Mz 1 3 = 0 ∧
     moduleMultiplicityInteger Mi 0 1 = 0 ∧
     moduleMultiplicityInteger Mz 0 1 = 0) := by
  exact ⟨repeatedIdentityBarcode, repeatedZeroBarcode,
    repeatedModuleRanks, repeatedBoundaryZero⟩

private theorem binaryTransitionFixtures :
    let Mi := reindex repeatedSample (identityTransitionDiagram (ZMod 2))
    let Mz := reindex repeatedSample (zeroTransitionDiagram (ZMod 2))
    rankBarcode Mi = ({targetBar03} : Multiset (FiniteInterval 3)) ∧
    rankBarcode Mz = ({targetBar02, targetBar23} : Multiset (FiniteInterval 3)) ∧
    (structureMapRank Mi 0 1 (by decide) = 1 ∧
     structureMapRank Mz 0 1 (by decide) = 1 ∧
     structureMapRank Mi 0 2 (by decide) = 1 ∧
     structureMapRank Mz 0 2 (by decide) = 0) ∧
    (moduleMultiplicityInteger Mi 1 3 = 0 ∧
     moduleMultiplicityInteger Mz 1 3 = 0 ∧
     moduleMultiplicityInteger Mi 0 1 = 0 ∧
     moduleMultiplicityInteger Mz 0 1 = 0) := by
  exact ⟨repeatedIdentityBarcode, repeatedZeroBarcode,
    repeatedModuleRanks, repeatedBoundaryZero⟩

private def mixedSource : Multiset (FiniteInterval 6) :=
  {⟨0, 6, by omega, by omega⟩,
   ⟨1, 4, by omega, by omega⟩,
   ⟨1, 4, by omega, by omega⟩,
   ⟨2, 3, by omega, by omega⟩,
   ⟨2, 5, by omega, by omega⟩,
   ⟨3, 6, by omega, by omega⟩,
   ⟨5, 6, by omega, by omega⟩,
   ⟨0, 1, by omega, by omega⟩}

private def mixedTarget : Multiset (FiniteInterval 4) :=
  {⟨0, 4, by omega, by omega⟩,
   ⟨0, 3, by omega, by omega⟩,
   ⟨0, 3, by omega, by omega⟩,
   ⟨2, 4, by omega, by omega⟩,
   ⟨2, 4, by omega, by omega⟩}

private theorem nonterminalBecomesTerminal :
    FiniteInterval.restrictAlong mixedSample
      (⟨2, 5, by omega, by omega⟩ : FiniteInterval 6) =
      some (⟨2, 4, by omega, by omega⟩ : FiniteInterval 4) := by decide

private theorem mixedModuleBarcode {k : Type u} [Field k] :
    rankBarcode (reindex mixedSample (barcodeModule (k := k) mixedSource)) =
      mixedTarget := by
  rw [rankBarcode_reindex, rankBarcode_barcodeModule]
  decide

private theorem mixedModuleRanks {k : Type u} [Field k] :
    structureMapRank (reindex mixedSample (barcodeModule (k := k) mixedSource))
      (0 : Fin 4) 1 (by decide) = 3 ∧
    structureMapRank (reindex mixedSample (barcodeModule (k := k) mixedSource))
      (0 : Fin 4) 3 (by decide) = 1 ∧
    structureMapRank (reindex mixedSample (barcodeModule (k := k) mixedSource))
      (2 : Fin 4) 2 (by decide) = 5 ∧
    structureMapRank (reindex mixedSample (barcodeModule (k := k) mixedSource))
      (2 : Fin 4) 3 (by decide) = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [structureMapRank_reindex, rank_barcodeMap]
    decide

private theorem mixedNaturalBlocks {k : Type u} [Field k] :
    barcodeMultiplicity
      (rankBarcode (reindex mixedSample (barcodeModule (k := k) mixedSource))) 0 3 = 2 ∧
    barcodeMultiplicity
      (rankBarcode (reindex mixedSample (barcodeModule (k := k) mixedSource))) 2 4 = 2 ∧
    barcodeMultiplicity
      (rankBarcode (reindex mixedSample (barcodeModule (k := k) mixedSource))) 1 4 = 0 ∧
    barcodeMultiplicity
      (rankBarcode (reindex mixedSample (barcodeModule (k := k) mixedSource))) 0 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [barcodeMultiplicity_rankBarcode_reindex _ _ _ _ (by omega) (by omega),
      rankBarcode_barcodeModule]
    decide

private theorem mixedIntegerFromNatural {k : Type u} [Field k]
    (b d n : ℕ) (hbd : b < d) (hd : d ≤ 4)
    (hn : barcodeMultiplicity
      (rankBarcode (reindex mixedSample (barcodeModule (k := k) mixedSource))) b d = n) :
    moduleMultiplicityInteger
      (reindex mixedSample (barcodeModule (k := k) mixedSource)) b d = (n : ℤ) ∧
    (let A := if b = 0 then 0 else (mixedSample ⟨b - 1, by omega⟩).val + 1
     let B := (mixedSample ⟨b, by omega⟩).val
     let C := (mixedSample ⟨d - 1, by omega⟩).val
     let D := if hdN : d < 4 then (mixedSample ⟨d, hdN⟩).val else 6
     ∑ x ∈ Finset.Icc A B, ∑ y ∈ Finset.Ioc C D,
       moduleMultiplicityInteger (barcodeModule (k := k) mixedSource) x y) = (n : ℤ) := by
  have hcast := barcodeMultiplicity_rankBarcode
    (reindex mixedSample (barcodeModule (k := k) mixedSource)) b d hbd hd
  rw [hn] at hcast
  have hdiagram := hcast.symm
  have hrectangle := moduleMultiplicityInteger_reindex
    (barcodeModule (k := k) mixedSource) mixedSample b d hbd hd
  exact ⟨hdiagram, hrectangle.symm.trans hdiagram⟩

private theorem mixedIntegerBlocks {k : Type u} [Field k] :
    moduleMultiplicityInteger
      (reindex mixedSample (barcodeModule (k := k) mixedSource)) 0 3 = 2 ∧
    moduleMultiplicityInteger
      (reindex mixedSample (barcodeModule (k := k) mixedSource)) 2 4 = 2 ∧
    moduleMultiplicityInteger
      (reindex mixedSample (barcodeModule (k := k) mixedSource)) 1 4 = 0 ∧
    moduleMultiplicityInteger
      (reindex mixedSample (barcodeModule (k := k) mixedSource)) 0 1 = 0 := by
  have h := mixedNaturalBlocks (k := k)
  exact ⟨(mixedIntegerFromNatural 0 3 2 (by omega) (by omega) h.1).1,
    (mixedIntegerFromNatural 2 4 2 (by omega) (by omega) h.2.1).1,
    (mixedIntegerFromNatural 1 4 0 (by omega) (by omega) h.2.2.1).1,
    (mixedIntegerFromNatural 0 1 0 (by omega) (by omega) h.2.2.2).1⟩

private theorem mixedRectangle24 {k : Type u} [Field k] :
    (∑ x ∈ Finset.Icc 2 3, ∑ y ∈ Finset.Ioc 4 6,
      moduleMultiplicityInteger (barcodeModule (k := k) mixedSource) x y) = 2 := by
  have h := (mixedIntegerFromNatural 2 4 2 (by omega) (by omega)
    (mixedNaturalBlocks (k := k)).2.1).2
  simpa [mixedSample] using h

private theorem rationalMixedFixtures :
    let M := reindex mixedSample (barcodeModule (k := ℚ) mixedSource)
    rankBarcode M = mixedTarget ∧
      (barcodeMultiplicity (rankBarcode M) 0 3 = 2 ∧
       barcodeMultiplicity (rankBarcode M) 2 4 = 2 ∧
       barcodeMultiplicity (rankBarcode M) 1 4 = 0 ∧
       barcodeMultiplicity (rankBarcode M) 0 1 = 0) ∧
      (moduleMultiplicityInteger M 0 3 = 2 ∧
       moduleMultiplicityInteger M 2 4 = 2 ∧
       moduleMultiplicityInteger M 1 4 = 0 ∧
       moduleMultiplicityInteger M 0 1 = 0) := by
  exact ⟨mixedModuleBarcode, mixedNaturalBlocks, mixedIntegerBlocks⟩

private theorem binaryMixedFixtures :
    let M := reindex mixedSample (barcodeModule (k := ZMod 2) mixedSource)
    rankBarcode M = mixedTarget ∧
      (barcodeMultiplicity (rankBarcode M) 0 3 = 2 ∧
       barcodeMultiplicity (rankBarcode M) 2 4 = 2 ∧
       barcodeMultiplicity (rankBarcode M) 1 4 = 0 ∧
       barcodeMultiplicity (rankBarcode M) 0 1 = 0) ∧
      (moduleMultiplicityInteger M 0 3 = 2 ∧
       moduleMultiplicityInteger M 2 4 = 2 ∧
       moduleMultiplicityInteger M 1 4 = 0 ∧
       moduleMultiplicityInteger M 0 1 = 0) := by
  exact ⟨mixedModuleBarcode, mixedNaturalBlocks, mixedIntegerBlocks⟩

private def twoCopies (k : Type u) [Field k] : PModule.{u,0,u} k (Fin 2) where
  obj _ := ModuleCat.of k (k × k)
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

private instance twoCopiesFD {k : Type u} [Field k] (i : Fin 2) :
    FiniteDimensional k ((twoCopies k).obj i) := by
  change FiniteDimensional k (k × k)
  infer_instance

private theorem twoCopiesRank {k : Type u} [Field k] (i j : Fin 2) (hij : i ≤ j) :
    structureMapRank (twoCopies k) i j hij = 2 := by
  change Module.finrank k
    (LinearMap.range (LinearMap.id : (k × k) →ₗ[k] (k × k))) = 2
  rw [LinearMap.range_id, finrank_top]
  simp [Module.finrank_prod, Module.finrank_self]

private theorem twoCopiesSourceBarcode {k : Type u} [Field k] :
    rankBarcode (twoCopies k) =
      (Multiset.replicate 2 sourceBar02 : Multiset (FiniteInterval 2)) := by
  have hr : ∀ (i j : Fin 2) (hij : i ≤ j),
      structureMapRank (twoCopies k) i j hij =
        structureMapRank (barcodeModule (k := k)
          (Multiset.replicate 2 sourceBar02 : Multiset (FiniteInterval 2))) i j hij := by
    intro i j hij
    rw [twoCopiesRank, rank_barcodeMap]
    fin_cases i <;> fin_cases j <;> decide
  have h := (rankBarcode_eq_iff (twoCopies k)
    (barcodeModule (k := k)
      (Multiset.replicate 2 sourceBar02 : Multiset (FiniteInterval 2)))).2 hr
  exact h.trans (rankBarcode_barcodeModule (k := k) _)

private theorem twoCopiesSampleBarcode {k : Type u} [Field k] :
    rankBarcode (reindex repeatedSample (twoCopies k)) =
      (Multiset.replicate 2 targetBar03 : Multiset (FiniteInterval 3)) := by
  rw [rankBarcode_reindex, twoCopiesSourceBarcode]
  decide

private theorem twoCopiesSampleRank {k : Type u} [Field k] :
    structureMapRank (reindex repeatedSample (twoCopies k))
      (0 : Fin 3) 2 (by decide) = 2 := by
  rw [structureMapRank_reindex]
  exact twoCopiesRank (0 : Fin 2) 1 (by decide)

private theorem rationalTwoCopies :
    rankBarcode (reindex repeatedSample (twoCopies ℚ)) =
      (Multiset.replicate 2 targetBar03 : Multiset (FiniteInterval 3)) ∧
    structureMapRank (reindex repeatedSample (twoCopies ℚ))
      (0 : Fin 3) 2 (by decide) = 2 :=
  ⟨twoCopiesSampleBarcode, twoCopiesSampleRank⟩

private theorem binaryTwoCopies :
    rankBarcode (reindex repeatedSample (twoCopies (ZMod 2))) =
      (Multiset.replicate 2 targetBar03 : Multiset (FiniteInterval 3)) ∧
    structureMapRank (reindex repeatedSample (twoCopies (ZMod 2)))
      (0 : Fin 3) 2 (by decide) = 2 :=
  ⟨twoCopiesSampleBarcode, twoCopiesSampleRank⟩

private theorem rationalConstantZero :
    rankBarcode (reindex constantSample (identityTransitionDiagram ℚ)) =
      ({targetBar03} : Multiset (FiniteInterval 3)) ∧
    rankBarcode (reindex constantSample (zeroTransitionDiagram ℚ)) =
      ({targetBar03} : Multiset (FiniteInterval 3)) ∧
    structureMapRank (reindex constantSample (zeroTransitionDiagram ℚ))
      (0 : Fin 3) 2 (by decide) = 1 :=
  ⟨constantSample_identityBarcode, constantSample_zeroBarcode, constantSampleRank⟩

private theorem binaryConstantZero :
    rankBarcode (reindex constantSample (identityTransitionDiagram (ZMod 2))) =
      ({targetBar03} : Multiset (FiniteInterval 3)) ∧
    rankBarcode (reindex constantSample (zeroTransitionDiagram (ZMod 2))) =
      ({targetBar03} : Multiset (FiniteInterval 3)) ∧
    structureMapRank (reindex constantSample (zeroTransitionDiagram (ZMod 2)))
      (0 : Fin 3) 2 (by decide) = 1 :=
  ⟨constantSample_identityBarcode, constantSample_zeroBarcode, constantSampleRank⟩

end TDA.Persistence
