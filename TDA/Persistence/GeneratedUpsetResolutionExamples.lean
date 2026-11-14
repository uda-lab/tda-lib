import TDA.Persistence.GeneratedUpsetProjectiveDimension

/-!
# Examples for join-indexed upset resolutions

These fixtures specialize the resolution and its ordinary projective-dimension bound to
singleton, repeated and empty families, and to a nonprojective upset on the Boolean square.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.GeneratedUpsetResolution.Examples

open TDA.Persistence.GeneratedUpsetResolution
open CategoryTheory
open CategoryTheory.Limits

abbrev singletonFamily : Fin 1 → ℕ := fun _ => 2

/-- The singleton-family augmentation is onto at every index. -/
theorem singleton_augmentation_surjective (p : ℕ) :
    Function.Surjective ((augmentation (k := ℚ) singletonFamily).app p).hom :=
  augmentation_surjective_at (k := ℚ) singletonFamily p

/-- The degree-zero kernel for one generator is filled by the next term. -/
theorem singleton_exact_at_zero (p : ℕ)
    (x : (term (k := ℚ) singletonFamily 0).obj p)
    (hx : ((augmentation (k := ℚ) singletonFamily).app p).hom x = 0) :
    ∃ y : (term (k := ℚ) singletonFamily 1).obj p,
      ((differential (k := ℚ) singletonFamily 0).app p).hom y = x :=
  augmentation_exact_at_zero (k := ℚ) singletonFamily p x hx

/-- The resolution term above the singleton family's top degree is zero. -/
theorem singleton_top_term_isZero :
    IsZero (term (k := ℚ) singletonFamily 1) :=
  term_isZero_of_degree_ge (k := ℚ) singletonFamily (by decide)

abbrev repeatedFamily : Fin 2 → ℕ := fun _ => 1

def repeatedFaceZero : FaceIndex 2 0 := singletonFaceIndex (0 : Fin 2)
def repeatedFaceOne : FaceIndex 2 0 := singletonFaceIndex (1 : Fin 2)

/-- Equal generator values still give separate degree-zero summands. -/
theorem repeated_occurrences_are_distinct :
    repeatedFaceZero ≠ repeatedFaceOne := by
  intro h
  have hsets := congrArg Subtype.val h
  norm_num [repeatedFaceZero, repeatedFaceOne, singletonFaceIndex] at hsets

/-- At the common birth, the two equal-valued occurrences remain distinct active vertices. -/
theorem repeated_active_faces_are_distinct :
    activeFaceEquiv repeatedFamily 1
      ⟨repeatedFaceZero, by simp [repeatedFamily, repeatedFaceZero,
        faceJoin_singleton]⟩ ≠
    activeFaceEquiv repeatedFamily 1
      ⟨repeatedFaceOne, by simp [repeatedFamily, repeatedFaceOne,
        faceJoin_singleton]⟩ := by
  intro h
  apply repeated_occurrences_are_distinct
  exact congrArg Subtype.val ((activeFaceEquiv repeatedFamily 1).injective h)

abbrev threeFamily : Fin 3 → ℕ := fun i => i.val

/-- A cycle in the nontrivial three-generator fiber is a boundary in the actual resolution. -/
theorem three_generator_cycle_is_boundary
    (x : (term (k := ℚ) threeFamily 1).obj 2)
    (hx : ((differential (k := ℚ) threeFamily 0).app 2).hom x = 0) :
    ∃ y : (term (k := ℚ) threeFamily 2).obj 2,
      ((differential (k := ℚ) threeFamily 1).app 2).hom y = x :=
  differential_exact_at_succ (k := ℚ) threeFamily 2 0 x hx

abbrev emptyFamily : Fin 0 → ℕ := fun i => Fin.elim0 i

/-- The empty family has empty support, zero support module, and zero face-sum fibers. -/
theorem empty_family_boundary :
    generatedSupport emptyFamily = ∅ ∧
      IsZero (SupportInterval.module (k := ℚ)
        (generatedSupport emptyFamily)
        (generatedSupport_ordConnected emptyFamily)) ∧
      ∀ r (p : ℕ) (x : (term (k := ℚ) emptyFamily r).obj p), x = 0 := by
  refine ⟨generatedSupport_fin_zero _, generatedSupport_fin_zero_module_isZero _, ?_⟩
  intro r p x
  exact term_fin_zero_eq_zero (k := ℚ) _ r p x

/-- The uniform dimension bound includes the empty indexed family. -/
theorem empty_hasProjectiveDimensionLE_zero :
    HasProjectiveDimensionLE (SupportInterval.module (k := ℚ)
      (generatedSupport emptyFamily) (generatedSupport_ordConnected emptyFamily)) 0 :=
  generatedSupport_hasProjectiveDimensionLE emptyFamily

/-- The empty family's numerical dimension is the zero-object value. -/
theorem empty_projectiveDimension_eq_bot :
    projectiveDimension (SupportInterval.module (k := ℚ)
      (generatedSupport emptyFamily) (generatedSupport_ordConnected emptyFamily)) = ⊥ :=
  (projectiveDimension_eq_bot_iff _).2 (generatedSupport_fin_zero_module_isZero emptyFamily)

/-- A singleton-generated upset is an ordinary projective object. -/
theorem singleton_projective :
    Projective (SupportInterval.module (k := ℚ)
      (generatedSupport singletonFamily) (generatedSupport_ordConnected singletonFamily)) :=
  (projective_iff_hasProjectiveDimensionLE_zero _).2
    (generatedSupport_hasProjectiveDimensionLE singletonFamily)

/-- The occurrence-count bound applies to two equal labels. -/
theorem repeated_hasProjectiveDimensionLE_one :
    HasProjectiveDimensionLE (SupportInterval.module (k := ℚ)
      (generatedSupport repeatedFamily) (generatedSupport_ordConnected repeatedFamily)) 1 :=
  generatedSupport_hasProjectiveDimensionLE repeatedFamily

/-- Repeating a single birth can give a nonminimal occurrence-count bound. -/
theorem repeated_projective :
    Projective (SupportInterval.module (k := ℚ)
      (generatedSupport repeatedFamily) (generatedSupport_ordConnected repeatedFamily)) := by
  have he : generatedSupport repeatedFamily =
      generatedSupport (fun _ : Fin 1 => (1 : ℕ)) := by
    ext p
    simp [generatedSupport, repeatedFamily]
  simpa only [he] using (projective_iff_hasProjectiveDimensionLE_zero _).2
    (generatedSupport_hasProjectiveDimensionLE (k := ℚ) (fun _ : Fin 1 => (1 : ℕ)))

private instance : SmallCategory (Bool × Bool) := Preorder.smallCategory _

/-- The two incomparable atoms of the Boolean square. -/
abbrev twoIncomparableFamily : Fin 2 → Bool × Bool := ![(true, false), (false, true)]
/-- The module on the upset generated by the two Boolean-square atoms. -/
noncomputable abbrev twoIncomparableModule (k : Type u) [Field k] : PModule.{u,0,u} k (Bool × Bool) :=
  SupportInterval.module (k := k) (generatedSupport twoIncomparableFamily)
    (generatedSupport_ordConnected twoIncomparableFamily)

/-- The selected births are incomparable in the product order. -/
theorem two_incomparable_generators :
    ¬ twoIncomparableFamily 0 ≤ twoIncomparableFamily 1 ∧
      ¬ twoIncomparableFamily 1 ≤ twoIncomparableFamily 0 := by decide

variable {k : Type u} [Field k]

private theorem two_mem_left : (true, false) ∈ generatedSupport twoIncomparableFamily :=
  ⟨0, by simp [twoIncomparableFamily]⟩
private theorem two_mem_right : (false, true) ∈ generatedSupport twoIncomparableFamily :=
  ⟨1, by simp [twoIncomparableFamily]⟩
private theorem two_mem_top : (true, true) ∈ generatedSupport twoIncomparableFamily :=
  ⟨0, by simp [twoIncomparableFamily]⟩

private theorem two_unit_naturality
    (s : twoIncomparableModule k ⟶ freeTerm (k := k) twoIncomparableFamily 0)
    (p : Bool × Bool) (hp : p ∈ generatedSupport twoIncomparableFamily) :
    ((s.app (true, true)).hom (SupportInterval.one _ two_mem_top)).val =
      ((s.app p).hom (SupportInterval.one _ hp)).val := by
  have h : p ≤ (true, true) := by constructor <;> simp
  have hunit : structureMapLinear (twoIncomparableModule k) h (SupportInterval.one _ hp) =
      SupportInterval.one _ two_mem_top := by
    apply Subtype.ext
    rw [SupportInterval.structureMap_val]
    simp [two_mem_top, SupportInterval.one]
  have he := congrArg (fun α => (α.hom (SupportInterval.one (k := k) _ hp)).val)
    (s.naturality (homOfLE h))
  change ((s.app (true, true)).hom
    (structureMapLinear (twoIncomparableModule k) h (SupportInterval.one _ hp))).val =
    (structureMapLinear (freeTerm (k := k) twoIncomparableFamily 0) h
      ((s.app p).hom (SupportInterval.one _ hp))).val at he
  rw [hunit] at he
  exact he

private theorem two_unit_image_zero (s : twoIncomparableModule k ⟶ freeTerm (k := k) twoIncomparableFamily 0) :
    (s.app (true, true)).hom (SupportInterval.one _ two_mem_top) = 0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro A
  have ha := congrArg (fun z => z A) (two_unit_naturality s (true, false) two_mem_left)
  have hb := congrArg (fun z => z A) (two_unit_naturality s (false, true) two_mem_right)
  by_cases hA : faceJoin twoIncomparableFamily A ≤ (true, false)
  · have hB : ¬ faceJoin twoIncomparableFamily A ≤ (false, true) := by
      intro hB
      obtain ⟨i, hi⟩ := face_nonempty A
      have hiA := (faceJoin_le_iff twoIncomparableFamily A _).mp hA i hi
      have hiB := (faceJoin_le_iff twoIncomparableFamily A _).mp hB i hi
      fin_cases i
      · exact (by decide : ¬ (true : Bool) ≤ false) hiB.1
      · exact (by decide : ¬ (true : Bool) ≤ false) hiA.2
    rw [hb]
    exact (Finsupp.mem_supported' k
      ((s.app (false, true)).hom (SupportInterval.one _ two_mem_right)).val).mp
        ((s.app (false, true)).hom (SupportInterval.one _ two_mem_right)).property A hB
  · rw [ha]
    exact (Finsupp.mem_supported' k
      ((s.app (true, false)).hom (SupportInterval.one _ two_mem_left)).val).mp
        ((s.app (true, false)).hom (SupportInterval.one _ two_mem_left)).property A hA

/-- The ordinary bound for this two-generator upset is at most one. -/
theorem two_incomparable_hasProjectiveDimensionLE_one :
    HasProjectiveDimensionLE (twoIncomparableModule k) 1 :=
  generatedSupport_hasProjectiveDimensionLE twoIncomparableFamily

/-- The two-generator upset admits no section of its ordinary free augmentation. -/
theorem two_incomparable_not_projective : ¬ Projective (twoIncomparableModule k) := by
  intro hprojective
  let := hprojective
  let : Epi (augmentation (k := k) twoIncomparableFamily) :=
    (NatTrans.epi_iff_epi_app _).2 (fun p =>
      (ModuleCat.epi_iff_surjective _).2 (augmentation_surjective_at twoIncomparableFamily p))
  let π : freeTerm (k := k) twoIncomparableFamily 0 ⟶ twoIncomparableModule k :=
    (termBiproductIso (k := k) twoIncomparableFamily 0).inv ≫ augmentation twoIncomparableFamily
  have : Epi π := by dsimp [π]; infer_instance
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 (twoIncomparableModule k)) π
  have he := congrArg (fun α => ((α.app (true, true)).hom
    (SupportInterval.one (k := k) _ two_mem_top) : k)) hs
  change ((π.app (true, true)).hom
    ((s.app (true, true)).hom (SupportInterval.one _ two_mem_top)) : k) = 1 at he
  rw [two_unit_image_zero, map_zero] at he
  exact zero_ne_one he

/-- The nonprojective two-generator upset has ordinary projective dimension exactly one. -/
theorem two_incomparable_projectiveDimension_eq_one : projectiveDimension (twoIncomparableModule k) = 1 := by
  apply le_antisymm
  · exact generatedSupport_projectiveDimension_le twoIncomparableFamily
  · apply (projectiveDimension_ge_iff _ 1).2
    intro h
    exact two_incomparable_not_projective ((projective_iff_hasProjectiveDimensionLT_one).2 h)


end TDA.Persistence.GeneratedUpsetResolution.Examples
