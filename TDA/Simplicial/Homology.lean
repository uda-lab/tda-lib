import TDA.Simplicial.Inclusion
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Homology of actual ordered simplicial chains

The cycles and boundaries below are those of the existing actual-face chain
complex. Inclusion acts on representatives by the existing chain inclusion.
-/

universe u v
set_option backward.defeqAttrib.useBackward true

namespace TDA.Simplicial

open CategoryTheory Module

variable {V : Type u} [LinearOrder V]
variable (R : Type v) [Ring R]
variable {K L M : PreAbstractSimplicialComplex V}

noncomputable def simplicialHomology
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (n : ℕ) :
    ModuleCat.{max u v} R :=
  (simplicialChainComplex K R).homology n

noncomputable def simplicialCycles
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (n : ℕ) :
    Submodule R (Chain K R n) :=
  LinearMap.ker ((simplicialChainComplex K R).sc n).g.hom

noncomputable def simplicialBoundaries
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (n : ℕ) :
    Submodule R (simplicialCycles K R n) :=
  LinearMap.range ((simplicialChainComplex K R).sc n).moduleCatToCycles

noncomputable local instance cyclesHasQuotient
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (n : ℕ) :
    HasQuotient (simplicialCycles K R n) (Submodule R (simplicialCycles K R n)) :=
  Submodule.hasQuotient (R := R) (M := simplicialCycles K R n)

theorem simplicialCycles_zero (K : PreAbstractSimplicialComplex V) :
    simplicialCycles K R 0 = ⊤ := by
  change LinearMap.ker ((simplicialChainComplex K R).sc 0).g.hom = ⊤
  have hg : ((simplicialChainComplex K R).sc 0).g = 0 := by
    change (simplicialChainComplex K R).d 0 ((ComplexShape.down ℕ).next 0) = 0
    rw [ChainComplex.next_nat_zero]
    exact simplicialChainComplex_d_zero K R 0
  rw [hg]
  exact LinearMap.ker_zero

theorem simplicialCycles_succ (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    simplicialCycles K R (n + 1) = LinearMap.ker (boundary K R n) := by
  change LinearMap.ker ((simplicialChainComplex K R).d
    (n + 1) ((ComplexShape.down ℕ).next (n + 1))).hom = _
  rw [ChainComplex.next_nat_succ, simplicialChainComplex_d]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem mem_simplicialBoundaries_iff
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (z : simplicialCycles K R n) :
    z ∈ simplicialBoundaries K R n ↔
      ∃ c : Chain K R (n + 1), boundary K R n c = (z : Chain K R n) := by
  simp [simplicialBoundaries, simplicialCycles, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor', simplicialChainComplex,
    ShortComplex.moduleCatToCycles, LinearMap.mem_range,
    Subtype.ext_iff]
  have hmem (m : ℕ) (hm : m = n + 1) :
      (∃ y : (simplicialChainComplex K R).X m,
        ((simplicialChainComplex K R).d m n).hom y = (z : Chain K R n)) ↔
      ∃ c : Chain K R (n + 1), boundary K R n c = (z : Chain K R n) := by
    subst m
    simp [simplicialChainComplex_d]
  exact hmem _ (ChainComplex.prev ℕ n)

private noncomputable def homologyShortMap (h : K ≤ L) (n : ℕ) :
    (simplicialChainComplex K R).sc n ⟶ (simplicialChainComplex L R).sc n :=
  (HomologicalComplex.shortComplexFunctor _ _ n).map (simplicialChainIncl R h)

private noncomputable def shortCycleMap
    (S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)) (φ : S₁ ⟶ S₂) :
    LinearMap.ker S₁.g.hom →ₗ[R] LinearMap.ker S₂.g.hom :=
  (φ.τ₂.hom.comp (LinearMap.ker S₁.g.hom).subtype).codRestrict _ (by
    intro z
    have hc := congrArg (fun f : S₁.X₂ ⟶ S₂.X₃ => f.hom (z : S₁.X₂)) φ.comm₂₃
    change S₂.g.hom (φ.τ₂.hom (z : S₁.X₂)) =
      φ.τ₃.hom (S₁.g.hom (z : S₁.X₂)) at hc
    exact hc.trans (by simp))

private theorem shortCycleMap_toCycles
    (S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)) (φ : S₁ ⟶ S₂) :
    (shortCycleMap R S₁ S₂ φ).comp S₁.moduleCatToCycles =
      S₂.moduleCatToCycles.comp φ.τ₁.hom := by
  ext c
  have hc := congrArg (fun f : S₁.X₁ ⟶ S₂.X₂ => f.hom c) φ.comm₁₂
  exact hc.symm

private theorem shortRange_le
    (S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)) (φ : S₁ ⟶ S₂) :
    LinearMap.range S₁.moduleCatToCycles ≤
      (LinearMap.range S₂.moduleCatToCycles).comap (shortCycleMap R S₁ S₂ φ) := by
  intro z hz
  obtain ⟨c, rfl⟩ := hz
  change shortCycleMap R S₁ S₂ φ (S₁.moduleCatToCycles c) ∈
    LinearMap.range S₂.moduleCatToCycles
  rw [← LinearMap.comp_apply, shortCycleMap_toCycles, LinearMap.comp_apply]
  exact LinearMap.mem_range_self _ _

private noncomputable def shortQuotientMap
    (S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)) (φ : S₁ ⟶ S₂) :
    (LinearMap.ker S₁.g.hom ⧸ LinearMap.range S₁.moduleCatToCycles) →ₗ[R]
      (LinearMap.ker S₂.g.hom ⧸ LinearMap.range S₂.moduleCatToCycles) :=
  (LinearMap.range S₁.moduleCatToCycles).mapQ
    (LinearMap.range S₂.moduleCatToCycles) (shortCycleMap R S₁ S₂ φ)
    (shortRange_le R S₁ S₂ φ)

private theorem shortQuotientMap_mkQ
    (S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)) (φ : S₁ ⟶ S₂)
    (z : LinearMap.ker S₁.g.hom) :
    shortQuotientMap R S₁ S₂ φ ((LinearMap.range S₁.moduleCatToCycles).mkQ z) =
      (LinearMap.range S₂.moduleCatToCycles).mkQ (shortCycleMap R S₁ S₂ φ z) := rfl

noncomputable def simplicialCycleIncl (h : K ≤ L) (n : ℕ) :
    simplicialCycles K R n →ₗ[R] simplicialCycles L R n :=
  shortCycleMap R _ _ (homologyShortMap R h n)

theorem simplicialCycleIncl_coe (h : K ≤ L) (n : ℕ)
    (z : simplicialCycles K R n) :
    (simplicialCycleIncl R h n z : Chain L R n) =
      chainIncl R h n (z : Chain K R n) := rfl

theorem simplicialCycleIncl_id (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    simplicialCycleIncl R (le_refl K) n = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simp [simplicialCycleIncl_coe, chainIncl_id]

theorem simplicialCycleIncl_comp (h : K ≤ L) (g : L ≤ M) (n : ℕ) :
    simplicialCycleIncl R (h.trans g) n =
      (simplicialCycleIncl R g n).comp (simplicialCycleIncl R h n) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simp only [simplicialCycleIncl_coe, LinearMap.comp_apply]
  exact congrArg (fun f => f (z : Chain K R n)) (chainIncl_comp R h g n)

theorem simplicialCycleIncl_toCycles (h : K ≤ L) (n : ℕ) :
    (simplicialCycleIncl R h n).comp
        ((simplicialChainComplex K R).sc n).moduleCatToCycles =
      (((simplicialChainComplex L R).sc n).moduleCatToCycles).comp
        (chainIncl R h ((ComplexShape.down ℕ).prev n)) := by
  have hs := shortCycleMap_toCycles R _ _ (homologyShortMap R h n)
  have hc : (homologyShortMap R h n).τ₁.hom =
      chainIncl R h ((ComplexShape.down ℕ).prev n) := rfl
  rw [hc] at hs
  exact hs

theorem simplicialBoundaries_le_comap (h : K ≤ L) (n : ℕ) :
    simplicialBoundaries K R n ≤
      (simplicialBoundaries L R n).comap (simplicialCycleIncl R h n) := by
  exact shortRange_le R _ _ (homologyShortMap R h n)

set_option backward.isDefEq.respectTransparency false in
noncomputable def simplicialQuotientIncl (h : K ≤ L) (n : ℕ) :
    (simplicialCycles K R n ⧸ simplicialBoundaries K R n) →ₗ[R]
      (simplicialCycles L R n ⧸ simplicialBoundaries L R n) :=
  shortQuotientMap R _ _ (homologyShortMap R h n)

theorem simplicialQuotientIncl_mkQ (h : K ≤ L) (n : ℕ)
    (z : simplicialCycles K R n) :
    simplicialQuotientIncl R h n
        (Submodule.mkQ (R := R) (M := simplicialCycles K R n)
          (simplicialBoundaries K R n) z) =
      Submodule.mkQ (R := R) (M := simplicialCycles L R n)
        (simplicialBoundaries L R n) (simplicialCycleIncl R h n z) := rfl

theorem simplicialQuotientIncl_id (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    simplicialQuotientIncl R (le_refl K) n = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using Quotient.inductionOn' with
  | _ z =>
    change simplicialQuotientIncl R (le_refl K) n
      (Submodule.mkQ (R := R) (M := simplicialCycles K R n)
        (simplicialBoundaries K R n) z) = _
    rw [simplicialQuotientIncl_mkQ, simplicialCycleIncl_id]
    rfl

theorem simplicialQuotientIncl_comp (h : K ≤ L) (g : L ≤ M) (n : ℕ) :
    simplicialQuotientIncl R (h.trans g) n =
      (simplicialQuotientIncl R g n).comp (simplicialQuotientIncl R h n) := by
  apply LinearMap.ext
  intro z
  induction z using Quotient.inductionOn' with
  | _ z =>
    change simplicialQuotientIncl R (h.trans g) n
      (Submodule.mkQ (R := R) (M := simplicialCycles K R n)
        (simplicialBoundaries K R n) z) = _
    simp only [simplicialQuotientIncl_mkQ, LinearMap.comp_apply]
    rw [simplicialCycleIncl_comp]
    rfl

noncomputable def simplicialHomologyIncl (h : K ≤ L) (n : ℕ) :
    simplicialHomology K R n ⟶ simplicialHomology L R n :=
  HomologicalComplex.homologyMap (simplicialChainIncl R h) n

theorem simplicialHomologyIncl_id (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    simplicialHomologyIncl R (le_refl K) n = 𝟙 (simplicialHomology K R n) := by
  unfold simplicialHomologyIncl
  rw [simplicialChainIncl_id]
  exact HomologicalComplex.homologyMap_id _ n

theorem simplicialHomologyIncl_comp (h : K ≤ L) (g : L ≤ M) (n : ℕ) :
    simplicialHomologyIncl R (h.trans g) n =
      simplicialHomologyIncl R h n ≫ simplicialHomologyIncl R g n := by
  unfold simplicialHomologyIncl
  rw [simplicialChainIncl_comp]
  exact HomologicalComplex.homologyMap_comp _ _ n

private noncomputable def homologyMapData
    (S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)) (φ : S₁ ⟶ S₂) :
    ShortComplex.LeftHomologyMapData φ
      S₁.moduleCatLeftHomologyData S₂.moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (shortCycleMap R S₁ S₂ φ)
  φH := ModuleCat.ofHom (shortQuotientMap R S₁ S₂ φ)
  commi := by
    apply ModuleCat.hom_ext
    ext z
    rfl
  commf' := by
    apply ModuleCat.hom_ext
    exact shortCycleMap_toCycles R S₁ S₂ φ
  commπ := by
    apply ModuleCat.hom_ext
    ext z
    rfl

theorem simplicialHomologyIncl_quotient_naturality (h : K ≤ L) (n : ℕ) :
    simplicialHomologyIncl R h n ≫
        (homologyKernelQuotient.{v,u,v} R (simplicialChainComplex L R) n).hom =
      (homologyKernelQuotient.{v,u,v} R (simplicialChainComplex K R) n).hom ≫
        ModuleCat.ofHom (simplicialQuotientIncl R h n) := by
  exact (homologyMapData R _ _ (homologyShortMap R h n)).homologyMap_comm

private theorem zeroBoundaryNormalization
    (S : ShortComplex (ModuleCat.{max u v} R)) (hf : S.f = 0) (hg : S.g = 0) :
    S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv ≫
        (ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyIso.hom =
      S.moduleCatLeftHomologyData.i := by
  rw [← Category.assoc, ← S.moduleCatCyclesIso_inv_π]
  rw [Category.assoc,
    (ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyπ_comp_homologyIso_hom]
  simp only [ShortComplex.LeftHomologyData.ofZeros_π]
  have hci : (ShortComplex.LeftHomologyData.ofZeros S hf hg).cyclesIso.hom =
      S.iCycles := by
    simpa [ShortComplex.LeftHomologyData.ofZeros] using
      (ShortComplex.LeftHomologyData.ofZeros S hf hg).cyclesIso_hom_comp_i
  rw [hci]
  exact S.moduleCatCyclesIso_inv_iCycles

private noncomputable abbrev singletonShort (x : V) :=
  (simplicialChainComplex (Filtration.singletonFace x) R).sc 0

private theorem singletonShort_f_zero (x : V) : (singletonShort R x).f = 0 := by
  have hf : (simplicialChainComplex (Filtration.singletonFace x) R).d 1 0 = 0 := by
    apply ModuleCat.hom_ext
    ext c
    change (boundary (Filtration.singletonFace x) R 0) c = 0
    have hc := singletonHigherChain_eq_zero x R 0 c
    rw [hc]
    simp
  change (simplicialChainComplex (Filtration.singletonFace x) R).d
    ((ComplexShape.down ℕ).prev 0) 0 = 0
  rw [ChainComplex.prev]
  exact hf

private theorem singletonShort_g_zero (x : V) : (singletonShort R x).g = 0 := by
  change (simplicialChainComplex (Filtration.singletonFace x) R).d
    0 ((ComplexShape.down ℕ).next 0) = 0
  rw [ChainComplex.next_nat_zero]
  exact simplicialChainComplex_d_zero _ R 0

theorem simplicialHomology_bot_zero
    (z : simplicialHomology (⊥ : PreAbstractSimplicialComplex V) R 0) : z = 0 := by
  let S := (simplicialChainComplex (⊥ : PreAbstractSimplicialComplex V) R).sc 0
  have hf : S.f = 0 := by
    have hf' : (simplicialChainComplex (⊥ : PreAbstractSimplicialComplex V) R).d 1 0 = 0 := by
      apply ModuleCat.hom_ext
      ext c
      change boundary (⊥ : PreAbstractSimplicialComplex V) R 0 c = 0
      have hc := emptyChain_eq_zero R 1 c
      rw [hc]
      simp
    change (simplicialChainComplex (⊥ : PreAbstractSimplicialComplex V) R).d
      ((ComplexShape.down ℕ).prev 0) 0 = 0
    rw [ChainComplex.prev]
    exact hf'
  have hg : S.g = 0 := by
    change (simplicialChainComplex (⊥ : PreAbstractSimplicialComplex V) R).d
      0 ((ComplexShape.down ℕ).next 0) = 0
    rw [ChainComplex.next_nat_zero]
    exact simplicialChainComplex_d_zero _ R 0
  apply (ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyIso.toLinearEquiv.injective
  let e := (ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyIso.toLinearEquiv
  change e z = e 0
  exact (emptyChain_eq_zero R 0 (e z)).trans e.map_zero.symm

noncomputable def simplicialSingletonH0Equiv (x : V) :
    simplicialHomology (Filtration.singletonFace x) R 0 ≃ₗ[R] R :=
  ((ShortComplex.LeftHomologyData.ofZeros (singletonShort R x)
      (singletonShort_f_zero R x) (singletonShort_g_zero R x)).homologyIso.toLinearEquiv).trans
    (Finsupp.uniqueLinearEquiv R R (singletonVertex x))

private noncomputable def singletonVertexCycle (x : V) (a : R) :
    LinearMap.ker (singletonShort R x).g.hom :=
  ⟨Finsupp.single (singletonVertex x) a, by
    change (singletonShort R x).g.hom (Finsupp.single (singletonVertex x) a) = 0
    rw [singletonShort_g_zero R x]
    rfl⟩

/-- The actual vertex class is sent to its coefficient. The quotient projection
and comparison inverse are those of the actual degree-zero short complex. -/
private theorem singletonVertex_normalization (x : V) (a : R) :
    simplicialSingletonH0Equiv R x
      ((homologyKernelQuotient.{v,u,v} R
        (simplicialChainComplex (Filtration.singletonFace x) R) 0).inv.hom
          ((LinearMap.range (singletonShort R x).moduleCatToCycles).mkQ
            (singletonVertexCycle R x a))) = a := by
  let S := singletonShort R x
  let h0 := ShortComplex.LeftHomologyData.ofZeros S
    (singletonShort_f_zero R x) (singletonShort_g_zero R x)
  change (Finsupp.uniqueLinearEquiv R R (singletonVertex x))
    ((S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv ≫ h0.homologyIso.hom).hom
      (singletonVertexCycle R x a)) = a
  rw [zeroBoundaryNormalization R S (singletonShort_f_zero R x)
    (singletonShort_g_zero R x)]
  change (Finsupp.uniqueLinearEquiv R R (singletonVertex x))
    ((singletonVertexCycle R x a).1) = a
  simp [singletonVertexCycle, Finsupp.uniqueLinearEquiv_apply]

theorem simplicialSingletonH0Equiv_symm_one_ne_zero [Nontrivial R] (x : V) :
    (simplicialSingletonH0Equiv R x).symm (1 : R) ≠ 0 := by
  intro hz
  have h := congrArg (simplicialSingletonH0Equiv R x) hz
  simp at h

-- Include private implementation declarations in the owning module's audit.
#print axioms cyclesHasQuotient
#print axioms homologyShortMap
#print axioms shortCycleMap
#print axioms shortCycleMap_toCycles
#print axioms shortRange_le
#print axioms shortQuotientMap
#print axioms shortQuotientMap_mkQ
#print axioms homologyMapData
#print axioms zeroBoundaryNormalization
#print axioms singletonShort
#print axioms singletonShort_f_zero
#print axioms singletonShort_g_zero
#print axioms singletonVertexCycle
#print axioms singletonVertex_normalization

end TDA.Simplicial
