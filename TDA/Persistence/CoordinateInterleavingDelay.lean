import TDA.Persistence.CoordinateInterleaving
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Finite-family comparisons between shifted and unshifted modules

An asymmetric delay comparison records maps from a finite direct sum to its
degreewise shifted version and back into one common shift. Its two equations
retain the original structure maps, which is the form needed to remove
degree-dependent shifts from a Schanuel comparison.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory CoordinateShift
open CategoryTheory.Limits
open scoped ZeroObject
open scoped TDA.Persistence NNReal

variable {R : Type u} [Ring R] {n : ℕ}

private instance : HasFiniteBiproducts (PModule.{u,0,w} R (Fin n → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private instance shift_preservesZeroMorphisms (ε : ℝ≥0) :
    (shift (R := R) (n := n) ε).PreservesZeroMorphisms where
  map_zero _ _ := by
    apply NatTrans.ext
    funext a
    rfl

/-- Maps comparing an object with a family of differently shifted summands.
The two equations are intentionally asymmetric: the forward map has no
shift, while the reverse map lands in the single common shift `δ`. -/
structure CoordinateInterleavingDelayComparison (δ : ℝ≥0)
    (M M' : PModule.{u,0,w} R (Fin n → ℝ)) where
  /-- Map from the unshifted object to the degreewise shifted object. -/
  forward : M ⟶ M'
  /-- Map from the degreewise shifted object to the common `δ`-shift. -/
  reverse : M' ⟶ (shift δ).obj M
  /-- The forward and reverse maps recover the `δ`-transition on `M`. -/
  forward_reverse : forward ≫ reverse = transition δ M
  /-- The reverse map followed by the shifted forward map recovers the
  `δ`-transition on `M'`. -/
  reverse_shift_forward : reverse ≫ (shift δ).map forward = transition δ M'

namespace CoordinateInterleavingDelayComparison

variable {δ ε : ℝ≥0}
  {M M' N N' : PModule.{u,0,w} R (Fin n → ℝ)}

private theorem transport_equation
    (cM : CoordinateInterleavingDelayComparison δ M M')
    (cN : CoordinateInterleavingDelayComparison δ N N')
    (i : CoordinateInterleaving ε M' N') :
    (cM.forward ≫ i.φ ≫ (shift ε).map cN.reverse ≫ (compIso ε δ N).hom) ≫
      (shift (ε + δ)).map
        (cN.forward ≫ i.ψ ≫ (shift ε).map cM.reverse ≫ (compIso ε δ M).hom) ≫
      (compIso (ε + δ) (ε + δ) M).hom = transition ((ε + δ) + (ε + δ)) M := by
  simp only [Functor.map_comp, Category.assoc]
  have hIso := (compIso_naturality ε δ cN.forward).symm
  rw [← Category.assoc (compIso ε δ N).hom
    ((shift (ε + δ)).map cN.forward)
    ((shift (ε + δ)).map i.ψ ≫
      (shift (ε + δ)).map ((shift ε).map cM.reverse) ≫
        (shift (ε + δ)).map (compIso ε δ M).hom ≫
          (compIso (ε + δ) (ε + δ) M).hom)]
  rw [hIso]
  have hN : (shift ε).map cN.reverse ≫
      (shift ε).map ((shift δ).map cN.forward) =
      (shift ε).map (transition δ N') := by
    rw [← Functor.map_comp, cN.reverse_shift_forward]
  have hNt := congrArg (fun q => q ≫
    (compIso ε δ N').hom ≫
      (shift (ε + δ)).map i.ψ ≫
        (shift (ε + δ)).map ((shift ε).map cM.reverse) ≫
          (shift (ε + δ)).map (compIso ε δ M).hom ≫
            (compIso (ε + δ) (ε + δ) M).hom) hN
  simp only [Category.assoc] at hNt
  simp only [Category.assoc]
  rw [hNt]
  have hIsoψ := compIso_naturality ε δ i.ψ
  have hIsoψt := congrArg (fun q => q ≫
    (shift (ε + δ)).map ((shift ε).map cM.reverse) ≫
      (shift (ε + δ)).map (compIso ε δ M).hom ≫
        (compIso (ε + δ) (ε + δ) M).hom) hIsoψ
  simp only [Category.assoc] at hIsoψt
  rw [← hIsoψt]
  let tail := (shift (ε + δ)).map ((shift ε).map cM.reverse) ≫
    (shift (ε + δ)).map (compIso ε δ M).hom ≫
      (compIso (ε + δ) (ε + δ) M).hom
  have hMid := congrArg (fun q => q ≫
      (compIso ε δ ((shift ε).obj M')).hom ≫ tail)
    (congrArg (fun q => (shift ε).map q)
      ((transition_naturality (ε := δ) i.ψ).symm))
  simp only [Functor.map_comp, Category.assoc] at hMid
  rw [hMid]
  apply NatTrans.ext
  funext a
  dsimp only [tail, NatTrans.comp_app, shift_map_app, compIso_hom_app]
  erw [← Category.assoc (i.φ.app a) (i.ψ.app (translation ε a)),
    i.φ_ψ_structureMap]
  let q := translation ε (translation (ε + δ) a)
  have hComp : cM.forward.app q ≫ cM.reverse.app q =
      (transition δ M).app q := by
    simpa only [NatTrans.comp_app] using
      congrArg (fun f => f.app q) cM.forward_reverse
  change cM.forward.app a ≫ M'.map _ ≫ M'.map _ ≫ M'.map _ ≫
    cM.reverse.app q ≫ M.map _ ≫ M.map _ = M.map _
  erw [← M'.map_comp_assoc, ← M'.map_comp_assoc]
  erw [← cM.forward.naturality_assoc]
  erw [← Category.assoc (cM.forward.app q) (cM.reverse.app q), hComp]
  change M.map _ ≫ M.map _ ≫ M.map _ ≫ M.map _ = M.map _
  erw [← M.map_comp, ← M.map_comp, ← M.map_comp]
  congr 1

/-- Transport an interleaving across two asymmetric delay comparisons. -/
noncomputable def transport
    (cM : CoordinateInterleavingDelayComparison δ M M')
    (cN : CoordinateInterleavingDelayComparison δ N N')
    (i : CoordinateInterleaving ε M' N') :
    CoordinateInterleaving (ε + δ) M N where
  φ := cM.forward ≫ i.φ ≫ (shift ε).map cN.reverse ≫ (compIso ε δ N).hom
  ψ := cN.forward ≫ i.ψ ≫ (shift ε).map cM.reverse ≫ (compIso ε δ M).hom
  φ_ψ := transport_equation cM cN i
  ψ_φ := transport_equation cN cM i.symm

/-- The transported forward map is the explicit composite through the two
asymmetric comparison maps. -/
@[simp] theorem transport_φ
    (cM : CoordinateInterleavingDelayComparison δ M M')
    (cN : CoordinateInterleavingDelayComparison δ N N')
    (i : CoordinateInterleaving ε M' N') :
    (transport cM cN i).φ =
      cM.forward ≫ i.φ ≫ (shift ε).map cN.reverse ≫ (compIso ε δ N).hom := rfl

/-- The transported reverse map is the explicit composite through the two
asymmetric comparison maps. -/
@[simp] theorem transport_ψ
    (cM : CoordinateInterleavingDelayComparison δ M M')
    (cN : CoordinateInterleavingDelayComparison δ N N')
    (i : CoordinateInterleaving ε M' N') :
    (transport cM cN i).ψ =
      cN.forward ≫ i.ψ ≫ (shift ε).map cM.reverse ≫ (compIso ε δ M).hom := rfl

end CoordinateInterleavingDelayComparison

section FiniteFamily

variable {ι : Type*} [Finite ι]

/-- The reverse component for a summand whose delay is at most the common
bound is the canonical structure map between shifts. -/
noncomputable def finiteFamilyDelayReverseComponent
    (δ : ℝ≥0) (X : ι → PModule.{u,0,w} R (Fin n → ℝ))
    (t : ι → ℝ≥0) (i : ι)
    (_h : t i ≤ δ ∨ IsZero (X i)) :
    (shift (t i)).obj (X i) ⟶ (shift δ).obj (X i) := by
  classical
  exact if hle : t i ≤ δ then shiftLE hle (X i) else 0

omit [Finite ι] in
@[simp] theorem finiteFamilyDelayReverseComponent_of_le
    (δ : ℝ≥0) (X : ι → PModule.{u,0,w} R (Fin n → ℝ))
    (t : ι → ℝ≥0) (i : ι) (h : t i ≤ δ)
    (hcase : t i ≤ δ ∨ IsZero (X i)) :
    finiteFamilyDelayReverseComponent δ X t i hcase = shiftLE h (X i) := by
  classical
  simp [finiteFamilyDelayReverseComponent, h]

omit [Finite ι] in
theorem finiteFamilyDelayReverseComponent_eq_zero
    (δ : ℝ≥0) (X : ι → PModule.{u,0,w} R (Fin n → ℝ))
    (t : ι → ℝ≥0) (i : ι) (hcase : t i ≤ δ ∨ IsZero (X i))
    (hnot : ¬ t i ≤ δ) :
    finiteFamilyDelayReverseComponent δ X t i hcase = 0 := by
  classical
  simp [finiteFamilyDelayReverseComponent, hnot]

private theorem transition_comp_shiftLE
    {t δ : ℝ≥0} (h : t ≤ δ) (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    transition t M ≫ shiftLE h M = transition δ M := by
  apply NatTrans.ext
  funext a
  change M.map _ ≫ M.map _ = M.map _
  erw [← M.map_comp]
  congr 1

private theorem shiftLE_comp_shift_transition
    {t δ : ℝ≥0} (h : t ≤ δ) (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    shiftLE h M ≫ (shift δ).map (transition t M) =
      transition δ ((shift t).obj M) := by
  apply NatTrans.ext
  funext a
  change M.map _ ≫ M.map _ = M.map _
  erw [← M.map_comp]
  congr 1

/-- Construct the asymmetric comparison for a finite family whenever each
summand's delay is at most `δ` or that summand is zero. Zero summands can
therefore carry arbitrarily large delays. -/
noncomputable def finiteFamilyDelayComparison
    (δ : ℝ≥0) (X : ι → PModule.{u,0,w} R (Fin n → ℝ))
    (t : ι → ℝ≥0) (hdelay : ∀ i, t i ≤ δ ∨ IsZero (X i)) :
    CoordinateInterleavingDelayComparison δ (⨁ X)
      (⨁ fun i => (shift (t i)).obj (X i)) := by
  classical
  let X' : ι → PModule.{u,0,w} R (Fin n → ℝ) := fun i =>
    (shift (t i)).obj (X i)
  let forward := biproduct.desc (fun i =>
    transition (t i) (X i) ≫ biproduct.ι X' i)
  let reverse := biproduct.desc (fun i =>
    finiteFamilyDelayReverseComponent δ X t i (hdelay i) ≫
      (shift δ).map (biproduct.ι X i))
  refine
    { forward := forward
      reverse := reverse
      forward_reverse := ?_
      reverse_shift_forward := ?_ }
  · apply biproduct.hom_ext'
    intro i
    by_cases hle : t i ≤ δ
    · calc
        biproduct.ι X i ≫ forward ≫ reverse =
            transition (t i) (X i) ≫ biproduct.ι X' i ≫ reverse := by
              dsimp [forward]
              rw [biproduct.ι_desc_assoc, Category.assoc]
        _ = transition (t i) (X i) ≫
            (finiteFamilyDelayReverseComponent δ X t i (hdelay i) ≫
              (shift δ).map (biproduct.ι X i)) := by
                dsimp [reverse]
                rw [biproduct.ι_desc]
        _ = biproduct.ι X i ≫ transition δ (⨁ X) := by
              rw [finiteFamilyDelayReverseComponent_of_le (δ := δ) (X := X)
                (t := t) (i := i) hle (hdelay i)]
              rw [← Category.assoc]
              rw [transition_comp_shiftLE hle]
              rw [transition_naturality (ε := δ) (biproduct.ι X i)]
    · have hzero : IsZero (X i) := (hdelay i).resolve_left hle
      calc
        biproduct.ι X i ≫ forward ≫ reverse =
            transition (t i) (X i) ≫ biproduct.ι X' i ≫ reverse := by
              dsimp [forward]
              rw [biproduct.ι_desc_assoc, Category.assoc]
        _ = transition (t i) (X i) ≫
            (finiteFamilyDelayReverseComponent δ X t i (hdelay i) ≫
              (shift δ).map (biproduct.ι X i)) := by
                dsimp [reverse]
                rw [biproduct.ι_desc]
        _ = biproduct.ι X i ≫ transition δ (⨁ X) := by
              rw [finiteFamilyDelayReverseComponent_eq_zero (δ := δ) (X := X)
                (t := t) (i := i) (hdelay i) hle]
              simp
              exact hzero.eq_of_src _ _
  · apply biproduct.hom_ext'
    intro i
    by_cases hle : t i ≤ δ
    · calc
        biproduct.ι X' i ≫ reverse ≫ (shift δ).map forward =
            finiteFamilyDelayReverseComponent δ X t i (hdelay i) ≫
              (shift δ).map (biproduct.ι X i) ≫ (shift δ).map forward := by
                dsimp [reverse]
                rw [biproduct.ι_desc_assoc, Category.assoc]
        _ = finiteFamilyDelayReverseComponent δ X t i (hdelay i) ≫
            (shift δ).map (biproduct.ι X i ≫ forward) := by
                rw [← Functor.map_comp]
        _ = finiteFamilyDelayReverseComponent δ X t i (hdelay i) ≫
            (shift δ).map (transition (t i) (X i) ≫ biproduct.ι X' i) := by
                dsimp [forward]
                rw [biproduct.ι_desc]
        _ = (shiftLE hle (X i) ≫ (shift δ).map (transition (t i) (X i))) ≫
            (shift δ).map (biproduct.ι X' i) := by
                rw [finiteFamilyDelayReverseComponent_of_le (δ := δ) (X := X)
                  (t := t) (i := i) hle (hdelay i)]
                exact (Category.assoc (shiftLE hle (X i))
                  ((shift δ).map (transition (t i) (X i)))
                  ((shift δ).map (biproduct.ι X' i))).symm
        _ = transition δ (X' i) ≫ (shift δ).map (biproduct.ι X' i) := by
              rw [shiftLE_comp_shift_transition hle]
        _ = biproduct.ι X' i ≫ transition δ (⨁ X') :=
              (transition_naturality (ε := δ) (biproduct.ι X' i)).symm
    · have hzero : IsZero (X i) := (hdelay i).resolve_left hle
      have hshift : IsZero (X' i) := by
        dsimp [X']
        exact Functor.map_isZero (shift (t i)) hzero
      exact hshift.eq_of_src _ _

@[reassoc, simp] theorem finiteFamilyDelayComparison_ι_forward
    (δ : ℝ≥0) (X : ι → PModule.{u,0,w} R (Fin n → ℝ))
    (t : ι → ℝ≥0) (hdelay : ∀ i, t i ≤ δ ∨ IsZero (X i)) (i : ι) :
    biproduct.ι X i ≫ (finiteFamilyDelayComparison δ X t hdelay).forward =
      transition (t i) (X i) ≫ biproduct.ι (fun j => (shift (t j)).obj (X j)) i := by
  classical
  simp [finiteFamilyDelayComparison]

@[reassoc, simp] theorem finiteFamilyDelayComparison_ι_reverse
    (δ : ℝ≥0) (X : ι → PModule.{u,0,w} R (Fin n → ℝ))
    (t : ι → ℝ≥0) (hdelay : ∀ i, t i ≤ δ ∨ IsZero (X i)) (i : ι) :
    biproduct.ι (fun j => (shift (t j)).obj (X j)) i ≫
        (finiteFamilyDelayComparison δ X t hdelay).reverse =
      finiteFamilyDelayReverseComponent δ X t i (hdelay i) ≫
        (shift δ).map (biproduct.ι X i) := by
  classical
  simp [finiteFamilyDelayComparison]

end FiniteFamily

end TDA.Persistence
