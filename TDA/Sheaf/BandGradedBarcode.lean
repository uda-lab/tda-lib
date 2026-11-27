import TDA.Sheaf.BandGradedMatching
import TDA.Sheaf.RealConstructibleRefinement
import Mathlib.Data.List.OfFn

/-!
# Occurrences of the real constructible graded barcode

An occurrence of an interval in a cohomological degree is indexed by its position in
the list of that degree's barcode. The biproduct of the occurrence objects recovers
the given bounded constructible complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open TDA.Persistence TDA.Sheaf.AlternatingDiagram TDA.Sheaf.RealStratification
open TDA.Sheaf.RealConstructible
open scoped ENNReal ZeroObject

namespace TDA.Sheaf.BandConvolution

variable (k : Type) [Field k] {m n : ℕ} {p : Fin m → ℝ} {q : Fin n → ℝ}

local notation "Sh[" k "]" => realLine.Sheaf (ModuleCat k)
local notation "D⁺[" k "]" => DerivedCategory.Plus (Sh[k])
local notation "Dᵇ[" k "]" => DerivedCategory.Bounded (Sh[k])

/-- An interval of the strata path and the cohomological degree of its sheaf. -/
structure GradedInterval (m : ℕ) where
  interval : FiniteInterval (2 * m + 1)
  degree : ℤ

variable [HasDerivedCategory (Sh[k])]

/-- Realize the interval sheaf in its given cohomological degree in the bounded category. -/
def GradedInterval.objB (hp : StrictMono p) (J : GradedInterval m) : Dᵇ[k] :=
  ⟨(singleFunctor _ J.degree).obj
      ((extension k hp).obj (AlternatingDiagram.interval (orient m) J.interval)),
    ⟨⟨J.degree, inferInstance⟩, ⟨J.degree, inferInstance⟩⟩⟩

/-- Realize the interval sheaf in its given cohomological degree in the bounded-below category. -/
def GradedInterval.obj (hp : StrictMono p) (J : GradedInterval m) : D⁺[k] :=
  (boundedToPlus (Sh[k])).obj (J.objB k hp)

/-- Copies in a degree are labelled by their separate positions in the barcode multiset's list. -/
def gradedBarcodeOccurrence (S : Finset ℤ) (B : ℤ → Multiset (FiniteInterval (2 * m + 1)))
    (i : Σ d : S, Fin (B d).toList.length) : GradedInterval m :=
  ⟨(B i.1).toList.get i.2, i.1⟩

/-- The occurrence supports in each degree give the multiset `gradedBarcodeSets`. -/
theorem gradedBarcodeOccurrence_sets (hp : StrictMono p) (K : DerivedCategory (Sh[k]))
    (hK : HasConstructibleCohomology k p K) (S : Finset ℤ) (d : S) :
    (List.ofFn (fun j : Fin (gradedBarcode k hp K hK d).toList.length =>
      intervalSet p (gradedBarcodeOccurrence S (gradedBarcode k hp K hK) ⟨d, j⟩).interval) :
        Multiset (Set ℝ)) = gradedBarcodeSets k hp K hK d := by
  simp only [gradedBarcodeOccurrence, List.ofFn_comp', List.ofFn_get,
    ← Multiset.map_coe, Multiset.coe_toList, gradedBarcodeSets]

private def biproductFinSuccIso {C : Type*} [Category C] [HasZeroMorphisms C]
    {n : ℕ} (f : Fin (n + 1) → C) [HasBiproduct f]
    [HasBiproduct (fun i : Fin n => f i.succ)]
    [HasBinaryBiproduct (f 0) (⨁ fun i : Fin n => f i.succ)] :
    (⨁ f) ≅ f 0 ⊞ (⨁ fun i : Fin n => f i.succ) where
  hom := biproduct.desc (Fin.cases (motive := fun i => f i ⟶ _) biprod.inl
    fun i => biproduct.ι (fun j : Fin n => f j.succ) i ≫ biprod.inr)
  inv := biprod.desc (biproduct.ι f 0) (biproduct.desc fun i => biproduct.ι f i.succ)
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp
    · apply biproduct.hom_ext'
      intro i
      simp

private def intervalSheafSumIsoBiproduct (hp : StrictMono p)
    (xs : List (FiniteInterval (2 * m + 1))) :
    intervalSheafSum k hp xs ≅
      (⨁ fun j : Fin xs.length => (extension k hp).obj (interval (orient m) (xs.get j))) := by
  induction xs with
  | nil =>
    change (0 : Sh[k]) ≅ _
    exact (isZero_zero _).iso (isZero_biproduct_of_isZero _ fun i => Fin.elim0 i)
  | cons J xs e =>
    let f (j : Fin (xs.length + 1)) :=
      (extension k hp).obj (interval (orient m) ((J :: xs).get j))
    exact biprod.mapIso (Iso.refl _) e ≪≫ (biproductFinSuccIso f).symm

/-- The bounded complex is the biproduct of its individual graded barcode occurrences. -/
theorem nonempty_iso_biproduct_gradedBarcode (hp : StrictMono p) (K : Dᵇ[k]) (a b : ℤ)
    [K.obj.IsGE a] [K.obj.IsLE b] (hK : HasConstructibleCohomology k p K.obj) :
    Nonempty (K ≅ ⨁ fun i =>
      (gradedBarcodeOccurrence (Finset.Icc a b) (gradedBarcode k hp K.obj hK) i).objB k hp) := by
  let S := Finset.Icc a b
  let B := gradedBarcode k hp K.obj hK
  let X := fun i => (gradedBarcodeOccurrence S B i).objB k hp
  let E := Bounded.ι (C := Sh[k])
  obtain ⟨e⟩ := exists_iso_biproduct_barcodeSheaf k hp K.obj a b hK
  have h (i : S) : (singleFunctor (Sh[k]) (i : ℤ)).obj (barcodeSheaf k hp (B i)) ≅
      (⨁ fun j : Fin (B i).toList.length =>
        E.obj (X (⟨i, j⟩ : Σ d : S, Fin (B d).toList.length))) := by
    let f := singleFunctor (Sh[k]) (i : ℤ)
    let G (j : Fin (B i).toList.length) :=
      (extension k hp).obj (interval (orient m) ((B i).toList.get j))
    change f.obj (barcodeSheaf k hp (B i)) ≅ ⨁ f.obj ∘ G
    exact f.mapIso (intervalSheafSumIsoBiproduct k hp (B i).toList) ≪≫ f.mapBiproduct G
  exact ⟨E.preimageIso (e ≪≫ biproduct.mapIso h ≪≫ biproductBiproductIso _ _ ≪≫
    (E.mapBiproduct X).symm)⟩

variable
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

/-- Matching the graded barcode occurrences bounds the bounded band distance. -/
theorem distanceB_le_gradedBarcodeMatchingDistance (hp : StrictMono p) (hq : StrictMono q)
    (K L : Dᵇ[k]) (a b c d : ℤ) [K.obj.IsGE a] [K.obj.IsLE b] [L.obj.IsGE c] [L.obj.IsLE d]
    (hK : HasConstructibleCohomology k p K.obj) (hL : HasConstructibleCohomology k q L.obj) :
    distanceB K L ≤ matchingDistance
      (fun i =>
        (gradedBarcodeOccurrence (Finset.Icc a b) (gradedBarcode k hp K.obj hK) i).obj k hp)
      (fun j =>
        (gradedBarcodeOccurrence (Finset.Icc c d) (gradedBarcode k hq L.obj hL) j).obj k hq) := by
  obtain ⟨e⟩ := nonempty_iso_biproduct_gradedBarcode k hp K a b hK
  obtain ⟨f⟩ := nonempty_iso_biproduct_gradedBarcode k hq L c d hL
  exact distanceB_le_matchingDistance e f

end TDA.Sheaf.BandConvolution
