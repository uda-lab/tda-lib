import TDA.Persistence.RankBarcode
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

universe u
namespace TDA.Persistence
open scoped BigOperators
open CategoryTheory
variable {N : ℕ} {k : Type u} [Field k]
variable (M : PModule.{u,0,u} k (Fin N))
variable [∀ i : Fin N, FiniteDimensional k (M.obj i)]

private theorem rankBarcode_count_eq (B C : Multiset (FiniteInterval N))
    (h : ∀ b d, b < d → d ≤ N → barcodeMultiplicity B b d = barcodeMultiplicity C b d) :
    B = C := by
  classical
  apply Multiset.ext'
  intro I
  have hpred (J : FiniteInterval N) :
      (J.birth = I.birth ∧ J.death = I.death) ↔ J = I := by
    constructor
    · rintro ⟨hb, hd⟩
      cases J with
      | mk jb jd hjb hjd =>
        cases I with
        | mk ib id hib hid => simp_all
    · intro h
      subst J
      exact ⟨rfl, rfl⟩
  have he := h I.birth I.death I.birth_lt_death I.death_le_size
  have hB : B.count I = barcodeMultiplicity B I.birth I.death := by
    simpa [barcodeMultiplicity, Multiset.count, eq_comm] using
      (Multiset.countP_congr (s := B) (s' := B) rfl
        (fun J _ => propext (hpred J)))
  have hC : C.count I = barcodeMultiplicity C I.birth I.death := by
    simpa [barcodeMultiplicity, Multiset.count, eq_comm] using
      (Multiset.countP_congr (s := C) (s' := C) rfl
        (fun J _ => propext (hpred J)))
  rw [hB, hC, he]

-- Genuine boundary and discriminating fixtures. These propositions all mention rankBarcode
-- or ranks of actual persistence modules.
private def bar01 : FiniteInterval 1 := ⟨0, 1, by omega, by omega⟩
private def bar02 : FiniteInterval 2 := ⟨0, 2, by omega, by omega⟩
private def bar01two : FiniteInterval 2 := ⟨0, 1, by omega, by omega⟩
private def bar12two : FiniteInterval 2 := ⟨1, 2, by omega, by omega⟩
private def bar03 : FiniteInterval 3 := ⟨0, 3, by omega, by omega⟩
private def bar12three : FiniteInterval 3 := ⟨1, 2, by omega, by omega⟩
private def bar02three : FiniteInterval 3 := ⟨0, 2, by omega, by omega⟩

private theorem emptyRankBarcode (M : PModule.{u,0,u} k (Fin 0))
    [∀ i : Fin 0, FiniteDimensional k (M.obj i)] : rankBarcode M = 0 := by
  simp [rankBarcode]

private def oneField : PModule.{u,0,u} k (Fin 1) where
  obj _ := ModuleCat.of k k
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

private instance oneFieldFD (i : Fin 1) : FiniteDimensional k ((oneField (k := k)).obj i) := by
  change FiniteDimensional k k
  infer_instance

private def oneZero : PModule.{u,0,u} k (Fin 1) where
  obj _ := ModuleCat.of k (Fin 0 → k)
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

private instance oneZeroFD (i : Fin 1) : FiniteDimensional k ((oneZero (k := k)).obj i) := by
  change FiniteDimensional k (Fin 0 → k)
  infer_instance

private theorem oneStageMultiplicity (M : PModule.{u,0,u} k (Fin 1))
    [∀ i : Fin 1, FiniteDimensional k (M.obj i)] :
    moduleMultiplicityInteger M 0 1 = Module.finrank k (M.obj 0) := by
  have hself := moduleRankInteger_fin M (0 : Fin 1) (0 : Fin 1) (le_refl _)
  have hr : structureMapRank M (0 : Fin 1) 0 (le_refl _) =
      Module.finrank k (M.obj 0) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  simp only [moduleMultiplicityInteger, Nat.cast_zero, Nat.cast_one]
  norm_num only
  simp only [moduleRankInteger_neg_one]
  rw [show moduleRankInteger M 0 1 = 0 from moduleRankInteger_at_size M 0]
  change moduleRankInteger M 0 0 = _ at hself
  rw [hself, hr]
  ring

private theorem oneFieldMultiplicity :
    moduleMultiplicityInteger (oneField (k := k)) 0 1 = 1 := by
  rw [oneStageMultiplicity]
  change ((Module.finrank k k : ℕ) : ℤ) = 1
  rw [Module.finrank_self]
  rfl

private theorem oneZeroMultiplicity :
    moduleMultiplicityInteger (oneZero (k := k)) 0 1 = 0 := by
  rw [oneStageMultiplicity]
  have hz : Subsingleton ((oneZero (k := k)).obj (0 : Fin 1)) := by
    change Subsingleton (Fin 0 → k)
    infer_instance
  exact_mod_cast Module.finrank_zero_of_subsingleton (R := k)
    (M := (oneZero (k := k)).obj (0 : Fin 1))

private theorem oneFieldRankBarcode :
    rankBarcode (oneField (k := k)) = ({bar01} : Multiset (FiniteInterval 1)) := by
  apply rankBarcode_count_eq
  intro b d hbd hd
  have hb : b = 0 := by omega
  have hd' : d = 1 := by omega
  subst b
  subst d
  have h := barcodeMultiplicity_rankBarcode (oneField (k := k)) 0 1 (by omega) (by omega)
  rw [oneFieldMultiplicity] at h
  exact_mod_cast (show barcodeMultiplicity (rankBarcode (oneField (k := k))) 0 1 = 1 by
    exact_mod_cast h).trans (by decide)

private theorem oneZeroRankBarcode : rankBarcode (oneZero (k := k)) = 0 := by
  apply rankBarcode_count_eq
  intro b d hbd hd
  have hb : b = 0 := by omega
  have hd' : d = 1 := by omega
  subst b
  subst d
  have h := barcodeMultiplicity_rankBarcode (oneZero (k := k)) 0 1 (by omega) (by omega)
  rw [oneZeroMultiplicity] at h
  exact_mod_cast (show barcodeMultiplicity (rankBarcode (oneZero (k := k))) 0 1 = 0 by
    exact_mod_cast h).trans (by simp [barcodeMultiplicity])

private instance identityFD (i : Fin 2) :
    FiniteDimensional k ((identityTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

private instance zeroFD (i : Fin 2) :
    FiniteDimensional k ((zeroTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

private theorem twoStageValues (M : PModule.{u,0,u} k (Fin 2))
    [∀ i : Fin 2, FiniteDimensional k (M.obj i)] :
    moduleMultiplicityInteger M 0 1 =
      (Module.finrank k (M.obj (0 : Fin 2)) : ℤ) -
        structureMapRank M 0 1 (by decide) ∧
    moduleMultiplicityInteger M 0 2 =
      (structureMapRank M 0 1 (by decide) : ℤ) ∧
    moduleMultiplicityInteger M 1 2 =
      (Module.finrank k (M.obj (1 : Fin 2)) : ℤ) -
        structureMapRank M 0 1 (by decide) := by
  have h00 := moduleRankInteger_fin M (0 : Fin 2) 0 (le_refl _)
  have h01 := moduleRankInteger_fin M (0 : Fin 2) 1 (by decide)
  have h11 := moduleRankInteger_fin M (1 : Fin 2) 1 (le_refl _)
  have h0 : structureMapRank M 0 0 (le_refl (0 : Fin 2)) =
      Module.finrank k (M.obj 0) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  have h1 : structureMapRank M 1 1 (le_refl (1 : Fin 2)) =
      Module.finrank k (M.obj 1) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  simp only [moduleMultiplicityInteger, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  norm_num only
  simp only [moduleRankInteger_neg_one]
  rw [show moduleRankInteger M 0 2 = 0 from moduleRankInteger_at_size M 0,
    show moduleRankInteger M 1 2 = 0 from moduleRankInteger_at_size M 1]
  change moduleRankInteger M 0 0 = _ at h00
  change moduleRankInteger M 0 1 = _ at h01
  change moduleRankInteger M 1 1 = _ at h11
  rw [h00, h01, h11, h0, h1]
  constructor
  · ring
  · constructor <;> ring

private theorem identityActualRank :
    structureMapRank (identityTransitionDiagram k) 0 1 (by decide) = 1 :=
  (equal_dimensions_different_structureMapRanks (k := k)).2.1

private theorem zeroActualRank :
    structureMapRank (zeroTransitionDiagram k) 0 1 (by decide) = 0 :=
  (equal_dimensions_different_structureMapRanks (k := k)).2.2

private theorem identityMu :
    moduleMultiplicityInteger (identityTransitionDiagram k) 0 1 = 0 ∧
    moduleMultiplicityInteger (identityTransitionDiagram k) 0 2 = 1 ∧
    moduleMultiplicityInteger (identityTransitionDiagram k) 1 2 = 0 := by
  have h := twoStageValues (identityTransitionDiagram k)
  rw [identityActualRank] at h
  simpa only [show Module.finrank k ((identityTransitionDiagram k).obj (0 : Fin 2)) = 1
      from Module.finrank_self k,
    show Module.finrank k ((identityTransitionDiagram k).obj (1 : Fin 2)) = 1
      from Module.finrank_self k, Nat.cast_one, sub_self] using h

private theorem zeroMu :
    moduleMultiplicityInteger (zeroTransitionDiagram k) 0 1 = 1 ∧
    moduleMultiplicityInteger (zeroTransitionDiagram k) 0 2 = 0 ∧
    moduleMultiplicityInteger (zeroTransitionDiagram k) 1 2 = 1 := by
  have h := twoStageValues (zeroTransitionDiagram k)
  rw [zeroActualRank] at h
  simpa only [show Module.finrank k ((zeroTransitionDiagram k).obj (0 : Fin 2)) = 1
      from Module.finrank_self k,
    show Module.finrank k ((zeroTransitionDiagram k).obj (1 : Fin 2)) = 1
      from Module.finrank_self k, Nat.cast_one, Nat.cast_zero, sub_zero] using h

private theorem twoStageClassify (b d : ℕ) (hbd : b < d) (hd : d ≤ 2) :
    (b = 0 ∧ d = 1) ∨ (b = 0 ∧ d = 2) ∨ (b = 1 ∧ d = 2) := by omega

private theorem identityBarcode :
    rankBarcode (identityTransitionDiagram k) =
      ({bar02} : Multiset (FiniteInterval 2)) := by
  apply rankBarcode_count_eq
  intro b d hbd hd
  rcases twoStageClassify b d hbd hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := barcodeMultiplicity_rankBarcode (identityTransitionDiagram k) 0 1 (by omega) (by omega)
    rw [identityMu.1] at h
    exact_mod_cast (show barcodeMultiplicity (rankBarcode (identityTransitionDiagram k)) 0 1 = 0 by
      exact_mod_cast h).trans (by decide)
  · have h := barcodeMultiplicity_rankBarcode (identityTransitionDiagram k) 0 2 (by omega) (by omega)
    rw [identityMu.2.1] at h
    exact_mod_cast (show barcodeMultiplicity (rankBarcode (identityTransitionDiagram k)) 0 2 = 1 by
      exact_mod_cast h).trans (by decide)
  · have h := barcodeMultiplicity_rankBarcode (identityTransitionDiagram k) 1 2 (by omega) (by omega)
    rw [identityMu.2.2] at h
    exact_mod_cast (show barcodeMultiplicity (rankBarcode (identityTransitionDiagram k)) 1 2 = 0 by
      exact_mod_cast h).trans (by decide)

private theorem zeroBarcode :
    rankBarcode (zeroTransitionDiagram k) =
      ({bar01two, bar12two} : Multiset (FiniteInterval 2)) := by
  apply rankBarcode_count_eq
  intro b d hbd hd
  rcases twoStageClassify b d hbd hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := barcodeMultiplicity_rankBarcode (zeroTransitionDiagram k) 0 1 (by omega) (by omega)
    rw [zeroMu.1] at h
    exact_mod_cast (show barcodeMultiplicity (rankBarcode (zeroTransitionDiagram k)) 0 1 = 1 by
      exact_mod_cast h).trans (by decide)
  · have h := barcodeMultiplicity_rankBarcode (zeroTransitionDiagram k) 0 2 (by omega) (by omega)
    rw [zeroMu.2.1] at h
    exact_mod_cast (show barcodeMultiplicity (rankBarcode (zeroTransitionDiagram k)) 0 2 = 0 by
      exact_mod_cast h).trans (by decide)
  · have h := barcodeMultiplicity_rankBarcode (zeroTransitionDiagram k) 1 2 (by omega) (by omega)
    rw [zeroMu.2.2] at h
    exact_mod_cast (show barcodeMultiplicity (rankBarcode (zeroTransitionDiagram k)) 1 2 = 1 by
      exact_mod_cast h).trans (by decide)

private theorem sameDimensionsDifferentBarcodes :
    (∀ i : Fin 2,
      Module.finrank k ((identityTransitionDiagram k).obj i) =
        Module.finrank k ((zeroTransitionDiagram k).obj i)) ∧
    rankBarcode (identityTransitionDiagram k) ≠ rankBarcode (zeroTransitionDiagram k) := by
  constructor
  · exact (equal_dimensions_different_structureMapRanks (k := k)).1
  · intro he
    have hr := (rankBarcode_eq_iff (identityTransitionDiagram k)
      (zeroTransitionDiagram k)).mp he 0 1 (by decide)
    rw [identityActualRank, zeroActualRank] at hr
    omega

private theorem equalityCriterionForward :
    ∀ (i j : Fin 2) (hij : i ≤ j),
      structureMapRank (identityTransitionDiagram k) i j hij =
        structureMapRank (barcodeModule (k := k) ({bar02} : Multiset (FiniteInterval 2))) i j hij := by
  apply (rankBarcode_eq_iff (identityTransitionDiagram k)
    (barcodeModule (k := k) ({bar02} : Multiset (FiniteInterval 2)))).mp
  rw [identityBarcode, rankBarcode_barcodeModule]

private theorem identityRealizationRanks :
    ∀ (i j : Fin 2) (hij : i ≤ j),
      structureMapRank (identityTransitionDiagram k) i j hij =
        structureMapRank (barcodeModule (k := k) ({bar02} : Multiset (FiniteInterval 2))) i j hij := by
  intro i j hij
  have hleft : structureMapRank (identityTransitionDiagram k) i j hij = 1 := by
    change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = 1
    rw [LinearMap.range_id, finrank_top]
    exact Module.finrank_self k
  have hright :
      structureMapRank (barcodeModule (k := k) ({bar02} : Multiset (FiniteInterval 2)))
        i j hij = 1 := by
    rw [rank_barcodeMap]
    fin_cases i <;> fin_cases j <;> decide
  rw [hleft, hright]

private theorem equalityCriterionReverse :
    rankBarcode (identityTransitionDiagram k) =
      rankBarcode (barcodeModule (k := k) ({bar02} : Multiset (FiniteInterval 2))) := by
  apply (rankBarcode_eq_iff (identityTransitionDiagram k)
    (barcodeModule (k := k) ({bar02} : Multiset (FiniteInterval 2)))).mpr
  exact identityRealizationRanks

-- The product module has a genuine identity transition on k×k at both stages.
private def twoCopies : PModule.{u,0,u} k (Fin 2) where
  obj _ := ModuleCat.of k (k × k)
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

private instance twoCopiesFD (i : Fin 2) :
    FiniteDimensional k ((twoCopies (k := k)).obj i) := by
  change FiniteDimensional k (k × k)
  infer_instance

private theorem twoCopiesDimension : Module.finrank k (k × k) = 2 := by
  simp only [Module.finrank_prod, Module.finrank_self]

private theorem twoCopiesActualRank :
    structureMapRank (twoCopies (k := k)) 0 1 (by decide) = 2 := by
  change Module.finrank k (LinearMap.range (LinearMap.id : (k × k) →ₗ[k] (k × k))) = 2
  rw [LinearMap.range_id, finrank_top]
  exact twoCopiesDimension

private theorem twoCopiesMu :
    moduleMultiplicityInteger (twoCopies (k := k)) 0 1 = 0 ∧
    moduleMultiplicityInteger (twoCopies (k := k)) 0 2 = 2 ∧
    moduleMultiplicityInteger (twoCopies (k := k)) 1 2 = 0 := by
  have h := twoStageValues (twoCopies (k := k))
  rw [twoCopiesActualRank] at h
  simpa only [show Module.finrank k ((twoCopies (k := k)).obj (0 : Fin 2)) = 2
      from twoCopiesDimension,
    show Module.finrank k ((twoCopies (k := k)).obj (1 : Fin 2)) = 2
      from twoCopiesDimension, Nat.cast_ofNat, sub_self] using h

private theorem twoCopiesBarcode :
    rankBarcode (twoCopies (k := k)) =
      (Multiset.replicate 2 bar02 : Multiset (FiniteInterval 2)) := by
  apply rankBarcode_count_eq
  intro b d hbd hd
  rcases twoStageClassify b d hbd hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := barcodeMultiplicity_rankBarcode (twoCopies (k := k)) 0 1 (by omega) (by omega)
    rw [twoCopiesMu.1] at h
    exact_mod_cast (show barcodeMultiplicity (rankBarcode (twoCopies (k := k))) 0 1 = 0 by
      exact_mod_cast h).trans (by decide)
  · have h := barcodeMultiplicity_rankBarcode (twoCopies (k := k)) 0 2 (by omega) (by omega)
    rw [twoCopiesMu.2.1] at h
    exact_mod_cast (show barcodeMultiplicity (rankBarcode (twoCopies (k := k))) 0 2 = 2 by
      exact_mod_cast h).trans (by decide)
  · have h := barcodeMultiplicity_rankBarcode (twoCopies (k := k)) 1 2 (by omega) (by omega)
    rw [twoCopiesMu.2.2] at h
    exact_mod_cast (show barcodeMultiplicity (rankBarcode (twoCopies (k := k))) 1 2 = 0 by
      exact_mod_cast h).trans (by decide)

private theorem twoCopiesMultiplicity :
    barcodeMultiplicity (rankBarcode (twoCopies (k := k))) 0 2 = 2 := by
  have h := barcodeMultiplicity_rankBarcode (twoCopies (k := k)) 0 2 (by omega) (by omega)
  rw [twoCopiesMu.2.1] at h
  exact_mod_cast h

private def mixed3 : Multiset (FiniteInterval 3) :=
  {bar12three, bar03, bar02three, bar03}

private theorem mixed3RoundTrip :
    rankBarcode (barcodeModule (k := k) mixed3) = mixed3 :=
  rankBarcode_barcodeModule mixed3

private theorem mixed3ActualRank :
    structureMapRank (barcodeModule (k := k) mixed3) (0 : Fin 3) 2 (by decide) = 2 := by
  rw [rank_barcodeMap]
  decide

private theorem mixed3CanonicalActualRank :
    structureMapRank (barcodeModule (k := k)
      (rankBarcode (barcodeModule (k := k) mixed3))) (0 : Fin 3) 2 (by decide) = 2 := by
  rw [mixed3RoundTrip]
  exact mixed3ActualRank

private theorem mixed3Interior : barcodeMultiplicity mixed3 1 2 = 1 := by
  decide
private theorem mixed3BirthZero : barcodeMultiplicity mixed3 0 2 = 1 := by
  decide
private theorem mixed3RepeatedDeathN : barcodeMultiplicity mixed3 0 3 = 2 := by
  decide

private theorem rationalInstances :
    rankBarcode (identityTransitionDiagram ℚ) = ({bar02} : Multiset (FiniteInterval 2)) ∧
    rankBarcode (zeroTransitionDiagram ℚ) =
      ({bar01two, bar12two} : Multiset (FiniteInterval 2)) ∧
    barcodeMultiplicity (rankBarcode (twoCopies (k := ℚ))) 0 2 = 2 ∧
    structureMapRank (twoCopies (k := ℚ)) 0 1 (by decide) = 2 ∧
    rankBarcode (identityTransitionDiagram ℚ) ≠
      rankBarcode (zeroTransitionDiagram ℚ) := by
  exact ⟨identityBarcode, zeroBarcode, twoCopiesMultiplicity,
    twoCopiesActualRank, (sameDimensionsDifferentBarcodes (k := ℚ)).2⟩

private theorem zmodTwoInstances :
    rankBarcode (identityTransitionDiagram (ZMod 2)) =
      ({bar02} : Multiset (FiniteInterval 2)) ∧
    rankBarcode (zeroTransitionDiagram (ZMod 2)) =
      ({bar01two, bar12two} : Multiset (FiniteInterval 2)) ∧
    barcodeMultiplicity (rankBarcode (twoCopies (k := ZMod 2))) 0 2 = 2 ∧
    structureMapRank (twoCopies (k := ZMod 2)) 0 1 (by decide) = 2 ∧
    rankBarcode (identityTransitionDiagram (ZMod 2)) ≠
      rankBarcode (zeroTransitionDiagram (ZMod 2)) := by
  exact ⟨identityBarcode, zeroBarcode, twoCopiesMultiplicity,
    twoCopiesActualRank, (sameDimensionsDifferentBarcodes (k := ZMod 2)).2⟩

end TDA.Persistence
