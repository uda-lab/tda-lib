import TDA.Persistence.RankBarcodeIso
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

universe u
namespace TDA.Persistence
open CategoryTheory
variable {k : Type u} [Field k]

private noncomputable def emptyStage : PModule.{u,0,u} k (Fin 0) :=
  barcodeModule (k := k) (0 : Multiset (FiniteInterval 0))

private instance emptyFD (i : Fin 0) :
    FiniteDimensional k ((emptyStage (k := k)).obj i) := i.elim0

private theorem emptyBarcode_zero :
    rankBarcode (emptyStage (k := k)) = 0 := by
  calc
    rankBarcode (emptyStage (k := k)) = rankBarcode (emptyStage (k := k)) :=
      rankBarcode_eq_of_iso (Iso.refl _)
    _ = 0 := by
      change rankBarcode (barcodeModule (k := k) (0 : Multiset (FiniteInterval 0))) = 0
      exact rankBarcode_barcodeModule _

private def onePair : PModule.{u,0,u} k (Fin 1) where
  obj _ := ModuleCat.of k (k × k)
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

private instance onePairFD (i : Fin 1) :
    FiniteDimensional k ((onePair (k := k)).obj i) := by
  change FiniteDimensional k (k × k)
  infer_instance

private noncomputable def onePairSwap :
    onePair (k := k) ≅ onePair (k := k) := by
  refine NatIso.ofComponents
    (fun _ => (LinearEquiv.prodComm k k k).toModuleIso) ?_
  intro i j f
  simp [onePair]

private theorem onePairSwap_nontrivial :
    (onePairSwap (k := k)).hom.app 0 ≠ 𝟙 _ := by
  intro h
  have he := congrArg (fun f : (onePair (k := k)).obj 0 ⟶ _ => f.hom (1, 0)) h
  have hs : (0 : k) = 1 := congrArg Prod.fst he
  exact zero_ne_one hs

private theorem onePairBarcodeInvariant :
    rankBarcode (onePair (k := k)) = rankBarcode (onePair (k := k)) := by
  exact rankBarcode_eq_of_iso (onePairSwap (k := k))

private def leftProjection : (k × k) →ₗ[k] (k × k) where
  toFun x := (x.1, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private def rightFromFirst : (k × k) →ₗ[k] (k × k) where
  toFun x := (0, x.1)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private def twoStage (f : (k × k) →ₗ[k] (k × k)) :
    PModule.{u,0,u} k (Fin 2) where
  obj _ := ModuleCat.of k (k × k)
  map {p q} _ := if p = q then 𝟙 _ else ModuleCat.ofHom f
  map_id p := by simp
  map_comp {p q r} g h := by
    have hpq : p ≤ q := leOfHom g
    have hqr : q ≤ r := leOfHom h
    fin_cases p <;> fin_cases q <;> fin_cases r <;> simp_all

private instance twoStageFD (f : (k × k) →ₗ[k] (k × k)) (i : Fin 2) :
    FiniteDimensional k ((twoStage f).obj i) := by
  change FiniteDimensional k (k × k)
  infer_instance

private noncomputable def projectionIso :
    twoStage (leftProjection (k := k)) ≅
      twoStage (rightFromFirst (k := k)) := by
  refine NatIso.ofComponents
    (fun i => if i = (0 : Fin 2) then Iso.refl _
      else (LinearEquiv.prodComm k k k).toModuleIso) ?_
  intro i j f
  have hij : i ≤ j := leOfHom f
  fin_cases i <;> fin_cases j <;> simp_all [twoStage]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem projectionBarcodeInvariant :
    rankBarcode (twoStage (leftProjection (k := k))) =
      rankBarcode (twoStage (rightFromFirst (k := k))) := by
  exact rankBarcode_eq_of_iso (projectionIso (k := k))


private theorem leftRank :
    structureMapRank (twoStage (leftProjection (k := k))) 0 1 (by decide) = 1 := by
  change Module.finrank k (LinearMap.range (leftProjection (k := k))) = 1
  have h : leftProjection (k := k) =
      (LinearMap.inl k k k).comp (LinearMap.fst k k k) := by
    apply LinearMap.ext
    intro x
    rfl
  have hf : LinearMap.range (LinearMap.fst k k k) = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.fst_surjective)
  rw [h, LinearMap.range_comp_of_range_eq_top _ hf]
  rw [LinearMap.finrank_range_of_inj (LinearMap.inl_injective)]
  exact Module.finrank_self k

private theorem rightRank :
    structureMapRank (twoStage (rightFromFirst (k := k))) 0 1 (by decide) = 1 := by
  change Module.finrank k (LinearMap.range (rightFromFirst (k := k))) = 1
  have h : rightFromFirst (k := k) =
      (LinearMap.inr k k k).comp (LinearMap.fst k k k) := by
    apply LinearMap.ext
    intro x
    rfl
  have hf : LinearMap.range (LinearMap.fst k k k) = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.fst_surjective)
  rw [h, LinearMap.range_comp_of_range_eq_top _ hf]
  rw [LinearMap.finrank_range_of_inj (LinearMap.inr_injective)]
  exact Module.finrank_self k

private theorem leftNotInjective :
    ¬ Function.Injective (leftProjection (k := k)) := by
  intro h
  have he : ((0, 1) : k × k) = (0, 0) := h rfl
  exact one_ne_zero (congrArg Prod.snd he)

private theorem rightNotInjective :
    ¬ Function.Injective (rightFromFirst (k := k)) := by
  intro h
  have he : ((0, 1) : k × k) = (0, 0) := h rfl
  exact one_ne_zero (congrArg Prod.snd he)

private theorem projectionsDistinct :
    leftProjection (k := k) ≠ rightFromFirst (k := k) := by
  intro h
  have he := congrArg (fun f : (k × k) →ₗ[k] (k × k) => f (1, 0)) h
  exact one_ne_zero (congrArg Prod.fst he)

private theorem rationalProjectionFixture :
    Nonempty (twoStage (leftProjection (k := ℚ)) ≅ twoStage (rightFromFirst (k := ℚ))) ∧
    structureMapRank (twoStage (leftProjection (k := ℚ))) 0 1 (by decide) = 1 ∧
    structureMapRank (twoStage (rightFromFirst (k := ℚ))) 0 1 (by decide) = 1 ∧
    leftProjection (k := ℚ) ≠ rightFromFirst (k := ℚ) := by
  exact ⟨⟨projectionIso (k := ℚ)⟩, leftRank, rightRank, projectionsDistinct⟩

private theorem zmodProjectionFixture :
    Nonempty (twoStage (leftProjection (k := ZMod 2)) ≅
      twoStage (rightFromFirst (k := ZMod 2))) ∧
    structureMapRank (twoStage (leftProjection (k := ZMod 2))) 0 1 (by decide) = 1 ∧
    structureMapRank (twoStage (rightFromFirst (k := ZMod 2))) 0 1 (by decide) = 1 ∧
    leftProjection (k := ZMod 2) ≠ rightFromFirst (k := ZMod 2) := by
  exact ⟨⟨projectionIso (k := ZMod 2)⟩, leftRank, rightRank, projectionsDistinct⟩

private instance identityFD (i : Fin 2) :
    FiniteDimensional k ((identityTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

private instance zeroFD (i : Fin 2) :
    FiniteDimensional k ((zeroTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

private theorem identityRank :
    structureMapRank (identityTransitionDiagram k) 0 1 (by decide) = 1 := by
  change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = 1
  rw [LinearMap.range_id, finrank_top]
  exact Module.finrank_self k

private theorem zeroRank :
    structureMapRank (zeroTransitionDiagram k) 0 1 (by decide) = 0 := by
  change Module.finrank k (LinearMap.range (0 : k →ₗ[k] k)) = 0
  simp

private theorem identityZeroNotIso :
    ¬ Nonempty (identityTransitionDiagram k ≅ zeroTransitionDiagram k) := by
  rintro ⟨e⟩
  have h := structureMapRank_eq_of_iso e (0 : Fin 2) 1 (by decide)
  rw [identityRank, zeroRank] at h
  exact Nat.one_ne_zero h


private def bar01 : FiniteInterval 1 := ⟨0, 1, by omega, by omega⟩

private theorem onePairRank :
    structureMapRank (onePair (k := k)) 0 0 (le_refl _) = 2 := by
  change Module.finrank k (LinearMap.range (LinearMap.id : (k × k) →ₗ[k] (k × k))) = 2
  rw [LinearMap.range_id, finrank_top, Module.finrank_prod, Module.finrank_self]

private theorem onePairTwoBars :
    rankBarcode (onePair (k := k)) =
      (Multiset.replicate 2 bar01 : Multiset (FiniteInterval 1)) := by
  let B : Multiset (FiniteInterval 1) := Multiset.replicate 2 bar01
  have heq : rankBarcode (onePair (k := k)) = rankBarcode (barcodeModule (k := k) B) := by
    apply (rankBarcode_eq_iff (onePair (k := k)) (barcodeModule (k := k) B)).2
    intro i j hij
    fin_cases i
    fin_cases j
    change structureMapRank (onePair (k := k)) 0 0 (le_refl _) =
      structureMapRank (barcodeModule (k := k) B) 0 0 (le_refl _)
    rw [onePairRank, rank_barcodeMap]
    change 2 = List.countP
      (fun I : FiniteInterval 1 => I.birth ≤ 0 ∧ 0 < I.death) [bar01, bar01]
    decide
  simpa [B, rankBarcode_barcodeModule] using heq

private theorem onePairSwapTwoBars :
    rankBarcode (onePair (k := k)) =
      (Multiset.replicate 2 bar01 : Multiset (FiniteInterval 1)) := by
  rw [rankBarcode_eq_of_iso (onePairSwap (k := k))]
  exact onePairTwoBars

private def bar03 : FiniteInterval 3 := ⟨0, 3, by omega, by omega⟩
private def bar12 : FiniteInterval 3 := ⟨1, 2, by omega, by omega⟩
private def repeatedBars : Multiset (FiniteInterval 3) := [bar03, bar12, bar03]
private def reorderedBars : List (FiniteInterval 3) := [bar03, bar03, bar12]

private theorem reorderedPerm : reorderedBars.Perm repeatedBars.toList := by
  have hm : (reorderedBars : Multiset (FiniteInterval 3)) = repeatedBars := by
    change ([bar03, bar03, bar12] : Multiset (FiniteInterval 3)) =
      [bar03, bar12, bar03]
    exact Multiset.coe_eq_coe.mpr
      (List.Perm.cons _ (List.Perm.swap _ _ _))
  exact Multiset.coe_eq_coe.mp (hm.trans (Multiset.coe_toList repeatedBars).symm)

private def otherBars : List (FiniteInterval 3) := [bar12, bar03, bar03]

private theorem otherPerm : otherBars.Perm repeatedBars.toList := by
  have hm : (otherBars : Multiset (FiniteInterval 3)) = repeatedBars := by
    change ([bar12, bar03, bar03] : Multiset (FiniteInterval 3)) =
      [bar03, bar12, bar03]
    exact Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _)
  exact Multiset.coe_eq_coe.mp (hm.trans (Multiset.coe_toList repeatedBars).symm)

private theorem differentOrders : reorderedBars ≠ otherBars := by
  decide

private noncomputable def chosenBars : List (FiniteInterval 3) :=
  if reorderedBars = repeatedBars.toList then otherBars else reorderedBars

private theorem chosenPerm : chosenBars.Perm repeatedBars.toList := by
  classical
  by_cases h : reorderedBars = repeatedBars.toList
  · simpa [chosenBars, h] using otherPerm
  · simpa [chosenBars, h] using reorderedPerm

private theorem chosenNonreflexive : chosenBars ≠ repeatedBars.toList := by
  classical
  by_cases h : reorderedBars = repeatedBars.toList
  · simp only [chosenBars, if_pos h]
    rw [← h]
    exact differentOrders.symm
  · simp [chosenBars, h]

private noncomputable def reorderedIso :
    barcodeModuleOfList (k := k) chosenBars ≅ barcodeModule (k := k) repeatedBars := by
  unfold barcodeModule
  exact barcodeEnumerationNatIso (k := k) chosenPerm

private theorem reorderedModuleRanks (i j : Fin 3) (hij : i ≤ j) :
    structureMapRank (barcodeModuleOfList (k := k) chosenBars) i j hij =
      structureMapRank (barcodeModule (k := k) repeatedBars) i j hij := by
  exact structureMapRank_eq_of_iso (reorderedIso (k := k)) i j hij

private theorem reorderedCanonicalBarcode :
    rankBarcode (barcodeModuleOfList (k := k) chosenBars) = repeatedBars := by
  exact rankBarcode_eq_of_iso_barcodeModule repeatedBars (reorderedIso (k := k))

private theorem reorderedRankOne :
    structureMapRank (barcodeModuleOfList (k := k) chosenBars)
      (1 : Fin 3) 1 (by decide) = 3 := by
  rw [reorderedModuleRanks, rank_barcodeMap]
  decide


private theorem rationalBarcodeFixture :
    rankBarcode (twoStage (leftProjection (k := ℚ))) =
      rankBarcode (twoStage (rightFromFirst (k := ℚ))) := by
  exact projectionBarcodeInvariant (k := ℚ)

private theorem zmodBarcodeFixture :
    rankBarcode (twoStage (leftProjection (k := ZMod 2))) =
      rankBarcode (twoStage (rightFromFirst (k := ZMod 2))) := by
  exact projectionBarcodeInvariant (k := ZMod 2)


private theorem directReorderedRanks (i j : Fin 3) (hij : i ≤ j) :
    structureMapRank (barcodeModuleOfList (k := k) reorderedBars) i j hij =
      structureMapRank (barcodeModule (k := k) repeatedBars) i j hij := by
  unfold barcodeModule
  exact structureMapRank_eq_of_iso
    (barcodeEnumerationNatIso (k := k) reorderedPerm) i j hij

private theorem directOtherRanks (i j : Fin 3) (hij : i ≤ j) :
    structureMapRank (barcodeModuleOfList (k := k) otherBars) i j hij =
      structureMapRank (barcodeModule (k := k) repeatedBars) i j hij := by
  unfold barcodeModule
  exact structureMapRank_eq_of_iso
    (barcodeEnumerationNatIso (k := k) otherPerm) i j hij

private theorem directReorderedBarcode :
    rankBarcode (barcodeModuleOfList (k := k) reorderedBars) = repeatedBars := by
  calc
    rankBarcode (barcodeModuleOfList (k := k) reorderedBars) =
        rankBarcode (barcodeModuleOfList (k := k) repeatedBars.toList) :=
      rankBarcode_eq_of_iso (barcodeEnumerationNatIso (k := k) reorderedPerm)
    _ = repeatedBars := rankBarcode_barcodeModule repeatedBars

private theorem directOtherBarcode :
    rankBarcode (barcodeModuleOfList (k := k) otherBars) = repeatedBars := by
  calc
    rankBarcode (barcodeModuleOfList (k := k) otherBars) =
        rankBarcode (barcodeModuleOfList (k := k) repeatedBars.toList) :=
      rankBarcode_eq_of_iso (barcodeEnumerationNatIso (k := k) otherPerm)
    _ = repeatedBars := rankBarcode_barcodeModule repeatedBars

private theorem identityZeroEqualStagesButNotIso :
    (∀ i : Fin 2,
      Module.finrank k ((identityTransitionDiagram k).obj i) =
        Module.finrank k ((zeroTransitionDiagram k).obj i)) ∧
      ¬ Nonempty (identityTransitionDiagram k ≅ zeroTransitionDiagram k) := by
  exact ⟨fun _ => rfl, identityZeroNotIso⟩

end TDA.Persistence
