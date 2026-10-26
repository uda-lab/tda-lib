import TDA.Persistence.GeneratedUpsetResolutionMap
import TDA.Persistence.RankExactGenerated

/-!
# Consumers of generated-upset resolution maps

These examples exercise proper principal-upset inclusions, occurrence multiplicity, empty and
high-degree terms, and rank exactness for a nonzero bottom-generated split row.
-/

set_option autoImplicit false

namespace TDA.Persistence.GeneratedUpsetResolutionMap.Examples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.GeneratedUpsetResolution

private instance : HasFiniteBiproducts (PModule ℚ ℕ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private def upperGenerator : Fin 1 → ℕ := fun _ => 1
private def lowerGenerator : Fin 1 → ℕ := fun _ => 0
private theorem lower_le_upper (i : Fin 1) : lowerGenerator i ≤ upperGenerator i := by
  simp [lowerGenerator, upperGenerator]

private def oneFace : FaceIndex 1 0 := singletonFaceIndex 0

private theorem lowerBirth_nonzero :
    HookInfinity.birth (R := ℚ) (0 : ℕ) ≠ 0 := by
  intro hz
  let e := HookInfinity.fiberEquivOfLe (R := ℚ) (le_rfl : (0 : ℕ) ≤ 0)
  have hval : e (HookInfinity.birth (R := ℚ) (0 : ℕ)) = 1 := by
    simpa [e] using (principalBirth_coefficient (k := ℚ) (le_rfl : (0 : ℕ) ≤ 0))
  have hzero := congrArg e hz
  rw [hval, map_zero] at hzero
  norm_num at hzero

private noncomputable def lowerTargetBirth : (term (k := ℚ) lowerGenerator 0).obj 0 := by
  have hjoin : faceJoin lowerGenerator oneFace = 0 := by
    simp [oneFace, lowerGenerator, faceJoin_singleton]
  rw [← hjoin]
  exact ((biproduct.ι (fun A : FaceIndex 1 0 => faceModule (k := ℚ) lowerGenerator A)
    oneFace).app 0).hom (HookInfinity.birth (R := ℚ) (faceJoin lowerGenerator oneFace))

private theorem lowerTargetBirth_nonzero : lowerTargetBirth ≠ 0 := by
  intro hz
  haveI : Mono (biproduct.ι
      (fun A : FaceIndex 1 0 => faceModule (k := ℚ) lowerGenerator A) oneFace) := inferInstance
  have hinj := (ModuleCat.mono_iff_injective _).mp
    ((NatTrans.mono_iff_mono_app _).mp (inferInstance : Mono
      (biproduct.ι (fun A : FaceIndex 1 0 => faceModule (k := ℚ) lowerGenerator A)
        oneFace)) 0)
  have hz' : ((biproduct.ι
      (fun A : FaceIndex 1 0 => faceModule (k := ℚ) lowerGenerator A) oneFace).app 0).hom
        (HookInfinity.birth (R := ℚ) (faceJoin lowerGenerator oneFace)) = 0 := by
    change lowerTargetBirth = 0
    exact hz
  have heq :
      ((biproduct.ι
        (fun A : FaceIndex 1 0 => faceModule (k := ℚ) lowerGenerator A) oneFace).app 0).hom
          (HookInfinity.birth (R := ℚ) (faceJoin lowerGenerator oneFace)) =
        ((biproduct.ι
          (fun A : FaceIndex 1 0 => faceModule (k := ℚ) lowerGenerator A) oneFace).app 0).hom 0 := by
    calc
      _ = 0 := hz'
      _ = _ := (map_zero _).symm
  have hbirth : HookInfinity.birth (R := ℚ)
      (faceJoin lowerGenerator oneFace) = 0 := hinj heq
  have hbirth' : HookInfinity.birth (R := ℚ) (0 : ℕ) = 0 := by
    have hj : faceJoin lowerGenerator oneFace = 0 := by
      simp [oneFace, lowerGenerator, faceJoin_singleton]
    cases hj
    exact hbirth
  exact lowerBirth_nonzero hbirth'

private theorem resolutionMap_component_not_surjective :
    ¬ Function.Surjective
      ((resolutionMap (k := ℚ) lower_le_upper 0).app 0).hom := by
  intro hsurj
  let y := lowerTargetBirth
  obtain ⟨x, hx⟩ := hsurj y
  have hno : ¬ Nonempty (ActiveIndex upperGenerator 0) := by
    rintro ⟨⟨i, hi⟩⟩
    change upperGenerator i ≤ 0 at hi
    simp [upperGenerator] at hi
  have hxzero := term_eq_zero_of_no_active (k := ℚ) upperGenerator 0 hno x
  have hxmap : ((resolutionMap (k := ℚ) lower_le_upper 0).app 0).hom x = 0 := by
    rw [hxzero]
    exact map_zero _
  exact lowerTargetBirth_nonzero (hx.symm.trans hxmap)

/-- The inclusion of the degree-zero resolutions of `↑{1}` into `↑{0}` is not an isomorphism. -/
theorem proper_principal_inclusion_not_iso :
    ¬ IsIso (resolutionMap (k := ℚ) lower_le_upper 0) := by
  intro hIso
  have hAppIso : IsIso ((resolutionMap (k := ℚ) lower_le_upper 0).app 0) :=
    (NatTrans.isIso_iff_isIso_app _).mp hIso 0
  letI : IsIso ((resolutionMap (k := ℚ) lower_le_upper 0).app 0) := hAppIso
  have hAppEpi : Epi ((resolutionMap (k := ℚ) lower_le_upper 0).app 0) := inferInstance
  exact resolutionMap_component_not_surjective
    ((ModuleCat.epi_iff_surjective _).mp hAppEpi)

private def repeatedGenerator : Fin 2 → ℕ := fun _ => 0

/-- Equal generator values retain distinct occurrence-indexed singleton faces. -/
theorem repeated_occurrences_remain_distinct :
    singletonFaceIndex (0 : Fin 2) ≠ singletonFaceIndex 1 := by
  intro h
  have hmem : (0 : Fin 2) ∈ (singletonFaceIndex (1 : Fin 2)).1 := by
    rw [← h]
    simp [singletonFaceIndex]
  simp [singletonFaceIndex] at hmem

/-- Each repeated occurrence has its own corresponding face map into the target term. -/
theorem repeated_occurrence_maps {g : Fin 2 → ℕ}
    (h : ∀ i, g i ≤ repeatedGenerator i) (i : Fin 2) :
    biproduct.ι (fun A : FaceIndex 2 0 => faceModule (k := ℚ) repeatedGenerator A)
        (singletonFaceIndex i) ≫ resolutionMap (k := ℚ) h 0 =
      faceMap (k := ℚ) h (singletonFaceIndex i) ≫
        biproduct.ι (fun A : FaceIndex 2 0 => faceModule (k := ℚ) g A)
          (singletonFaceIndex i) :=
  resolutionMap_ι (k := ℚ) h 0 (singletonFaceIndex i)

/-- With no generator occurrences, every degree term is zero and the map is still defined. -/
theorem empty_family_term_isZero (r : ℕ) (f : Fin 0 → ℕ) :
    IsZero (term (k := ℚ) f r) :=
  term_isZero_of_degree_ge (k := ℚ) f (by omega)

/-- The degreewise map remains a monomorphism for an empty occurrence family. -/
theorem empty_family_resolutionMap_mono {f g : Fin 0 → ℕ}
    (h : ∀ i, g i ≤ f i) (r : ℕ) : Mono (resolutionMap (k := ℚ) h r) :=
  resolutionMap_mono (k := ℚ) h r

/-- All terms and maps in degrees at least the number of occurrences are covered. -/
theorem high_degree_term_isZero {m r : ℕ} (f : Fin m → ℕ) (hmr : m ≤ r) :
    IsZero (term (k := ℚ) f r) :=
  term_isZero_of_degree_ge (k := ℚ) f hmr

theorem high_degree_resolutionMap_mono {m r : ℕ} {f g : Fin m → ℕ}
    (h : ∀ i, g i ≤ f i) : Mono (resolutionMap (k := ℚ) h r) :=
  resolutionMap_mono (k := ℚ) h r

private abbrev constantModule : PModule ℚ ℕ :=
  (Functor.const ℕ).obj (ModuleCat.of ℚ ℚ)

private abbrev constantPairModule : PModule ℚ ℕ :=
  (Functor.const ℕ).obj (ModuleCat.of ℚ (ℚ × ℚ))

private def constantLinearMap {V W : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (L : V →ₗ[ℚ] W) :
    (Functor.const ℕ).obj (ModuleCat.of ℚ V) ⟶
      (Functor.const ℕ).obj (ModuleCat.of ℚ W) where
  app _ := ModuleCat.ofHom L
  naturality := by intros; simp

private def splitInclusion : constantModule ⟶ constantPairModule :=
  constantLinearMap (LinearMap.inl ℚ ℚ ℚ)

private def splitProjection : constantPairModule ⟶ constantModule :=
  constantLinearMap (LinearMap.snd ℚ ℚ ℚ)

private theorem splitRow_shortExact : IsPointwiseShortExact splitInclusion splitProjection where
  injective := by
    intro p x y hxy
    change (LinearMap.inl ℚ ℚ ℚ) x = (LinearMap.inl ℚ ℚ ℚ) y at hxy
    exact LinearMap.inl_injective hxy
  surjective := by
    intro p y
    refine ⟨(0, y), ?_⟩
    change (LinearMap.snd ℚ ℚ ℚ) (0, y) = y
    rfl
  range_eq_ker := by
    intro p
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      change (LinearMap.snd ℚ ℚ ℚ) ((LinearMap.inl ℚ ℚ ℚ) x) = 0
      simp
    · intro hz
      rw [LinearMap.mem_ker] at hz
      rcases z with ⟨x, y⟩
      change y = 0 at hz
      refine ⟨x, ?_⟩
      change (x, 0) = (x, y)
      simp [hz]

private theorem constant_generatedAtBottom : GeneratedAtBottom constantModule := by
  intro p y
  refine ⟨y, ?_⟩
  simp [constantModule, structureMapLinear, structureMap]

private theorem constantPair_finiteDimensional :
    ∀ p, FiniteDimensional ℚ (constantPairModule.obj p) := by
  intro p
  change FiniteDimensional ℚ (ℚ × ℚ)
  infer_instance

/-- A nonzero split exact row of bottom-generated finite-rank modules is rank exact. -/
theorem nonzero_split_row_rankExact : IsRankExact splitInclusion splitProjection :=
  IsPointwiseShortExact.rankExact_of_generatedAtBottom splitRow_shortExact
    constant_generatedAtBottom constantPair_finiteDimensional

/-- The left module in the split row has a nonzero fiber. -/
theorem split_row_left_fiber_nontrivial : Nontrivial (constantModule.obj 0) := by
  change Nontrivial ℚ
  infer_instance

end TDA.Persistence.GeneratedUpsetResolutionMap.Examples
