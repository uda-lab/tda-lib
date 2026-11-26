import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import TDA.Sheaf.RightDerivedHomology

/-!
# Acyclic classes for a left exact functor

Let `A` and `B` be abelian categories, `F : A ⥤ B` an additive left exact functor and `P` a class
of objects of `A`. `AcyclicClass F P` collects the closure and exactness properties under which
bounded below complexes of objects of `P` compute the right derived functor of `F`:

* zero objects lie in `P`, and so does the cokernel of a short exact sequence whose first two
  terms lie in `P`;
* an object `Z` with `𝟙 Z = p₁ ≫ i₁ + p₂ ≫ i₂` for maps through objects of `P` lies in `P` (such
  as a biproduct, or a term of a mapping cone);
* `F` keeps a short exact sequence with first term in `P` short exact;
* injective objects lie in `P`.

For such a class:

* `acyclic_map_of_acyclicClass`: `F` keeps a bounded below acyclic complex of objects of `P`
  acyclic. Its cycle objects lie in `P`, by induction from the bottom.
* `quasiIso_map_of_acyclicClass`: `F` keeps a quasi-isomorphism between bounded below complexes
  of objects of `P` a quasi-isomorphism, through the mapping cone.
* `isIso_rightDerivedFunctorPlusUnit_app_of_acyclicClass`: for a bounded below complex `K` of
  objects of `P`, the comparison `F K ⟶ RF(K)` in `D⁺` is an isomorphism, so such complexes
  compute `RF`.

Flasque sheaves for a direct image (`TDA.Sheaf.FlasqueAcyclic`) and germ-surjective sheaves for
global sections on a compact interval (`TDA.Sheaf.IntervalAcyclic`) are instances.
-/

noncomputable section
open CategoryTheory Limits

namespace TDA.Sheaf

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- **Acyclic class.** A class `P` of objects of `A` adapted to an additive functor `F : A ⥤ B`:
it contains zero objects and injective objects, it is closed under cokernels of short exact
sequences and under retracts of a sum of two members, and `F` keeps short exact sequences with
first term in `P` short exact. -/
structure AcyclicClass (F : A ⥤ B) [F.Additive] (P : A → Prop) : Prop where
  /-- Zero objects lie in `P`. -/
  zero : ∀ X : A, IsZero X → P X
  /-- The cokernel of a short exact sequence with first two terms in `P` lies in `P`. -/
  quot : ∀ S : ShortComplex A, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃
  /-- An object `Z` with `𝟙 Z = p₁ ≫ i₁ + p₂ ≫ i₂` through objects of `P` lies in `P`. -/
  retract : ∀ {Z A₁ A₂ : A} (p₁ : Z ⟶ A₁) (i₁ : A₁ ⟶ Z) (p₂ : Z ⟶ A₂) (i₂ : A₂ ⟶ Z),
    P A₁ → P A₂ → p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 Z → P Z
  /-- `F` keeps a short exact sequence with first term in `P` short exact. -/
  shortExact : ∀ S : ShortComplex A, S.ShortExact → P S.X₁ → (S.map F).ShortExact
  /-- Injective objects lie in `P`. -/
  injective : ∀ I : A, Injective I → P I

section cycles

/-- The short complex `Zⁱ ⟶ Cⁱ ⟶ Zʲ` of cycles of a cochain complex, for `i + 1 = j`. -/
private abbrev cyclesSc (C : CochainComplex A ℤ) (i j : ℤ) : ShortComplex A :=
  ShortComplex.mk (C.iCycles i) (C.toCycles i j) (by
    rw [← cancel_mono (C.iCycles j), Category.assoc, C.toCycles_i, C.iCycles_d, zero_comp])

/-- If a cochain complex is exact in degree `j = i + 1`, then `0 ⟶ Zⁱ ⟶ Cⁱ ⟶ Zʲ ⟶ 0` is short
exact. -/
private theorem cyclesSc_shortExact (C : CochainComplex A ℤ) {i j l : ℤ} (hij : i + 1 = j)
    (hjl : j + 1 = l) (hC : C.ExactAt j) : (cyclesSc C i j).ShortExact := by
  have hT : (ShortComplex.mk (C.iCycles i) (C.d i j) (C.iCycles_d i j)).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (C.cyclesIsKernel i j ((ComplexShape.up ℤ).next_eq' hij))
  let φ : cyclesSc C i j ⟶ ShortComplex.mk (C.iCycles i) (C.d i j) (C.iCycles_d i j) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := C.iCycles j }
  have hE : (C.sc' i j l).Exact :=
    (C.exactAt_iff' i j l ((ComplexShape.up ℤ).prev_eq' hij)
      ((ComplexShape.up ℤ).next_eq' hjl)).1 hC
  have := hE.epi_toCycles
  have heq : C.toCycles i j = (C.sc' i j l).toCycles ≫
      (C.cyclesIsoSc' i j l ((ComplexShape.up ℤ).prev_eq' hij)
        ((ComplexShape.up ℤ).next_eq' hjl)).inv := by
    rw [← C.toCycles_cyclesIsoSc'_hom i j l ((ComplexShape.up ℤ).prev_eq' hij)
      ((ComplexShape.up ℤ).next_eq' hjl), Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ShortComplex.ShortExact.mk' ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hT)
    (inferInstanceAs (Mono (C.iCycles i))) ?_
  change Epi (C.toCycles i j)
  rw [heq]
  infer_instance

/-- A morphism of cochain complexes is a quasi-isomorphism exactly when its mapping cone is
acyclic. -/
private theorem acyclic_mappingCone_iff {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    (CochainComplex.mappingCone φ).Acyclic ↔ QuasiIso φ := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  refine ((HomotopyCategory.subcategoryAcyclic A).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)).symm.trans ?_
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff φ).trans
    (HomologicalComplex.mem_quasiIso_iff φ)

end cycles

section acyclic

variable {F : A ⥤ B} [F.Additive] {P : A → Prop}

/-- In a bounded below acyclic complex of objects of an acyclic class, every cycle object lies in
the class. -/
private theorem AcyclicClass.cycles (hP : AcyclicClass F P) (C : CochainComplex A ℤ) (n₀ : ℤ)
    [C.IsStrictlyGE n₀] (hC : ∀ n, P (C.X n)) (hCa : C.Acyclic) (m : ℤ) : P (C.cycles m) := by
  have hzero (i : ℤ) (hi : i < n₀) : P (C.cycles i) :=
    hP.zero _ (IsZero.of_mono (C.iCycles i) (C.isZero_of_isStrictlyGE n₀ i hi))
  refine Int.inductionOn' m (n₀ - 1) (hzero _ (by omega)) (fun i _ hi => ?_)
    (fun i hi _ => hzero _ (by omega))
  exact hP.quot _ (cyclesSc_shortExact C (i := i) (j := i + 1) (l := i + 1 + 1) rfl rfl
    (hCa (i + 1))) hi (hC i)

/-- **Acyclic complexes of an acyclic class.** For an acyclic class `P` of a left exact additive
functor `F`, `F` keeps a bounded below acyclic complex of objects of `P` acyclic. -/
theorem acyclic_map_of_acyclicClass [PreservesFiniteLimits F] (hP : AcyclicClass F P)
    (C : CochainComplex A ℤ) (n₀ : ℤ) [C.IsStrictlyGE n₀] (hC : ∀ n, P (C.X n))
    (hCa : C.Acyclic) : ((F.mapHomologicalComplex _).obj C).Acyclic := by
  intro j
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hS := hP.shortExact _
    (cyclesSc_shortExact C (i := i) (j := i + 1) (l := i + 1 + 1) rfl rfl (hCa (i + 1)))
    (hP.cycles C n₀ hC hCa i)
  rw [HomologicalComplex.exactAt_iff' _ i (i + 1) (i + 1 + 1)
    ((ComplexShape.up ℤ).prev_eq' rfl) ((ComplexShape.up ℤ).next_eq' rfl)]
  -- `F` keeps `Zⁱ⁺¹` the kernel of the differential.
  have key : PreservesFiniteLimits F → ∀ S : ShortComplex A,
      S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae F).out 4 2).1
  have hT := key inferInstance
    (ShortComplex.mk (C.iCycles (i + 1)) (C.d (i + 1) (i + 1 + 1)) (C.iCycles_d _ _))
    ⟨ShortComplex.exact_of_f_is_kernel _
      (C.cyclesIsKernel _ _ ((ComplexShape.up ℤ).next_eq' rfl)), inferInstance⟩
  let ψ : ((F.mapHomologicalComplex _).obj C).sc' i (i + 1) (i + 1 + 1) ⟶
      (ShortComplex.mk (C.iCycles (i + 1)) (C.d (i + 1) (i + 1 + 1))
        (C.iCycles_d _ _)).map F :=
    { τ₁ := F.map (C.toCycles i (i + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        simp only [ShortComplex.map_f, HomologicalComplex.shortComplexFunctor'_obj_f,
          Functor.mapHomologicalComplex_obj_d, Category.comp_id, ← F.map_comp, C.toCycles_i]
      comm₂₃ := by
        simp only [ShortComplex.map_g, HomologicalComplex.shortComplexFunctor'_obj_g,
          Functor.mapHomologicalComplex_obj_d, Category.comp_id, Category.id_comp] }
  have : Epi ψ.τ₁ := hS.epi_g
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hT.1

/-- **Quasi-isomorphisms of complexes of an acyclic class.** For an acyclic class `P` of a left
exact additive functor `F`, `F` keeps a quasi-isomorphism between bounded below complexes of
objects of `P` a quasi-isomorphism. -/
theorem quasiIso_map_of_acyclicClass [PreservesFiniteLimits F] (hP : AcyclicClass F P)
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) [QuasiIso φ] (n₀ : ℤ) [K.IsStrictlyGE n₀]
    [L.IsStrictlyGE n₀] (hK : ∀ n, P (K.X n)) (hL : ∀ n, P (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  have : (CochainComplex.mappingCone φ).IsStrictlyGE (n₀ - 1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyGE n₀ _ (by omega), L.isZero_of_isStrictlyGE n₀ _ (by omega)⟩
  have hcone (n : ℤ) : P ((CochainComplex.mappingCone φ).X n) :=
    hP.retract _ _ _ _ (hK _) (hL _) (CochainComplex.mappingCone.id_X φ n (n + 1) rfl)
  have h := acyclic_map_of_acyclicClass hP (CochainComplex.mappingCone φ) (n₀ - 1) hcone
    ((acyclic_mappingCone_iff φ).2 inferInstance)
  rw [← acyclic_mappingCone_iff]
  exact fun n => (h n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso φ F)

/-- **Complexes of an acyclic class compute the right derived functor.** For an acyclic class `P`
of a left exact additive functor `F` and a bounded below complex `K` of objects of `P`, the
comparison `F K ⟶ RF(K)` of the right derived functor on `D⁺` is an isomorphism. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_of_acyclicClass [HasDerivedCategory A]
    [HasDerivedCategory B] [EnoughInjectives A] [PreservesFiniteLimits F]
    (hP : AcyclicClass F P) (K : CochainComplex.Plus A) (hK : ∀ n, P (K.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨n, hn⟩ := K.property
  obtain ⟨L, _, j, hj⟩ := CochainComplex.Plus.exists_quasiIso_injective K n
  let I := (InjectiveObject.ι A).mapCochainComplexPlus.obj L
  have (m : ℤ) : Injective (I.obj.X m) := (L.obj.X m).property
  have : I.obj.IsStrictlyGE n := inferInstanceAs (CochainComplex.IsStrictlyGE
    (((InjectiveObject.ι _).mapHomologicalComplex _).obj L.obj) n)
  have : QuasiIso j.hom := hj
  have hFj := quasiIso_map_of_acyclicClass hP j.hom n hK
    (fun m => hP.injective _ inferInstance)
  have := isIso_Q_map_comp_rightDerivedFunctorPlusUnit F (𝟙 _) j hj (by
    rw [Category.id_comp]
    exact hFj)
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using this

end acyclic

end TDA.Sheaf
