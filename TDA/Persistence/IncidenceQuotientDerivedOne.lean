import TDA.Persistence.IncidenceQuotientBaseChange
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Degree-one exactness for quotient extension

This file proves the first derived vanishing for extension from the right incidence algebra
to its actual diagonal quotient. The argument uses idempotency of the quotient kernel and
short exact rows whose cokernel is already a restricted quotient module.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceQuotientDerivedOne

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.IncidenceQuotientBaseChange

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : DecidableLE S := Classical.decRel _
local instance : DecidableLT S := Classical.decRel _
local instance : DecidableEq S := Classical.decEq _
local instance : DecidableEq (WithTop S) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset S) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop S × WithTop S => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset S) := Classical.decRel _
local instance : DecidableLT (PairPoset S) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset S) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset S) := Classical.decEq _
local instance : Fintype (ComparablePair S) := Fintype.ofFinite _

local instance diagonalIdealTwoSided :
    (DiagonalIdeal (k := k) (S := S)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := S)

abbrev R := RightIncidence (k := k) (S := S)
abbrev C := RightQuotient (k := k) (S := S)
abbrev J : Ideal (R (k := k) (S := S)) := RingHom.ker (quotientHom (k := k) (S := S))

/-- Membership in the right quotient kernel is the opposite of membership in the actual
diagonal ideal. -/
theorem mem_kernel_iff_unop_mem (r : R (k := k) (S := S)) :
    r ∈ J (k := k) (S := S) ↔
      MulOpposite.unop r ∈ DiagonalIdeal (k := k) (S := S) := by
  change r ∈ RingHom.ker (quotientHom (k := k) (S := S)) ↔ _
  rw [RingHom.mem_ker]
  change MulOpposite.op
      (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S)) (MulOpposite.unop r)) = 0 ↔ _
  constructor
  · intro h
    have h' : Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))
        (MulOpposite.unop r) = 0 := MulOpposite.op_injective (by simpa using h)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h'
  · intro h
    have h' : Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))
        (MulOpposite.unop r) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    simpa using congrArg MulOpposite.op h'

/-- The actual kernel of the opposite quotient is idempotent. -/
theorem quotientKernel_mul_self :
    J (k := k) (S := S) * J (k := k) (S := S) = J (k := k) (S := S) := by
  let I := DiagonalIdeal (k := k) (S := S)
  let e := diagonalIdempotent (k := k) (S := S)
  let K := J (k := k) (S := S)
  letI : K.IsTwoSided := inferInstance
  letI : (K * K).IsTwoSided := inferInstance
  apply le_antisymm
  · exact Ideal.mul_le_right
  · intro x hx
    have he : MulOpposite.op e ∈ K := by
      apply (mem_kernel_iff_unop_mem (k := k) (S := S) (MulOpposite.op e)).2
      change e ∈ Ideal.span (Set.range fun z :
        FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) ×
          FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) => z.1 * e * z.2)
      apply Ideal.subset_span
      exact ⟨(1, 1), by simp [e]⟩
    have hxI := (mem_kernel_iff_unop_mem (k := k) (S := S) x).1 hx
    have hspan : MulOpposite.unop x ∈
        Ideal.span (Set.range fun z :
          FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) ×
            FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) => z.1 * e * z.2) := by
      change MulOpposite.unop x ∈ Ideal.span (Set.range fun z :
        FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) ×
          FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) =>
            z.1 * diagonalIdempotent (k := k) (S := S) * z.2) at hxI
      simpa [e] using hxI
    have htarget (a : FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S))
        (ha : a ∈ Ideal.span (Set.range fun z :
          FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) ×
            FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) => z.1 * e * z.2)) :
        MulOpposite.op a ∈ K * K := by
      induction ha using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨⟨b, c⟩, rfl⟩ := hz
        have h₁ : MulOpposite.op c * MulOpposite.op e ∈ K :=
          Ideal.mul_mem_left K _ he
        have h₂ : MulOpposite.op e * MulOpposite.op b ∈ K :=
          Ideal.mul_mem_right (MulOpposite.op b) K he
        have hp := Ideal.mul_mem_mul h₁ h₂
        have he₂ : MulOpposite.op e * MulOpposite.op e = MulOpposite.op e := by
          exact congrArg MulOpposite.op (diagonalIdempotent_mul_self (k := k) (S := S))
        have hrepr : MulOpposite.op (b * e * c) =
            (MulOpposite.op c * MulOpposite.op e) *
              (MulOpposite.op e * MulOpposite.op b) := by
          calc
            MulOpposite.op (b * e * c) =
                MulOpposite.op c * (MulOpposite.op e * MulOpposite.op b) := by simp
            _ = MulOpposite.op c *
                ((MulOpposite.op e * MulOpposite.op e) * MulOpposite.op b) := by rw [he₂]
            _ = (MulOpposite.op c * MulOpposite.op e) *
                (MulOpposite.op e * MulOpposite.op b) := by simp [mul_assoc]
        rw [hrepr]
        exact hp
      | zero => simp
      | add a b ha hb h₁ h₂ =>
        simpa using Ideal.add_mem (K * K) h₁ h₂
      | smul r a ha h₁ =>
        change MulOpposite.op (r * a) ∈ K * K
        rw [MulOpposite.op_mul]
        exact Ideal.mul_mem_right (MulOpposite.op r) (K * K) h₁
    have hx' := htarget (MulOpposite.unop x) hspan
    simpa using hx'

/-- The quotient relations on a module are exactly the submodule generated by the kernel
action. -/
theorem relation_eq_kernel_smul_top
    (M : ModuleCat (R (k := k) (S := S))) :
    relation (k := k) (S := S) M =
      J (k := k) (S := S) • (⊤ : Submodule (R (k := k) (S := S)) M) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨z, rfl⟩
    exact Submodule.smul_mem_smul z.1.property Submodule.mem_top
  · refine Submodule.smul_le.2 ?_
    intro a ha m hm
    apply Submodule.subset_span
    exact ⟨(⟨a, ha⟩, m), rfl⟩

/-- Elements of the quotient kernel act by zero on every restricted quotient module. -/
theorem kernel_smul_restricted
    (N : ModuleCat (C (k := k) (S := S)))
    (a : R (k := k) (S := S)) (ha : a ∈ J (k := k) (S := S))
    (n : (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) :
    a • n = 0 := by
  change quotientHom (k := k) (S := S) a • (n : N) = 0
  have hq : quotientHom (k := k) (S := S) a = 0 := (RingHom.mem_ker).1 ha
  rw [hq, zero_smul]

/-- The relation submodule on a restricted quotient module is zero. -/
theorem relation_restricted_eq_bot
    (N : ModuleCat (C (k := k) (S := S))) :
    relation (k := k) (S := S)
        ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) = ⊥ := by
  rw [relation_eq_kernel_smul_top]
  apply le_antisymm
  · refine Submodule.smul_le.2 ?_
    intro a ha n hn
    exact (Submodule.mem_bot _).2
      (kernel_smul_restricted (k := k) (S := S) N a ha n)
  · exact bot_le

/-- Extension sends a short exact row with restricted quotient cokernel to a short exact row.
The restricted cokernel condition is used to control the kernel action on the middle object. -/
theorem extension_maps_shortExact_restricted
    {X Y : ModuleCat (R (k := k) (S := S))}
    (N : ModuleCat (C (k := k) (S := S)))
    (f : X ⟶ Y)
    (g : Y ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)
    (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact) :
    ((ShortComplex.mk f g hfg).map (extensionFunctor (k := k) (S := S))).ShortExact := by
  let S₀ := ShortComplex.mk f g hfg
  let E := extensionFunctor (k := k) (S := S)
  let QX := relation (k := k) (S := S) X
  let QY := relation (k := k) (S := S) Y
  let q := quotientHom (k := k) (S := S)
  have hJY_le_range :
      J (k := k) (S := S) • (⊤ : Submodule (R (k := k) (S := S)) Y) ≤
        LinearMap.range f.hom := by
    rw [hS.exact.moduleCat_range_eq_ker]
    refine Submodule.smul_le.2 ?_
    intro a ha y hy
    change g.hom (a • y) = 0
    rw [g.hom.map_smul, kernel_smul_restricted (k := k) (S := S) N a ha]
  have hJY_eq_range :
      J (k := k) (S := S) • (⊤ : Submodule (R (k := k) (S := S)) Y) =
        J (k := k) (S := S) • LinearMap.range f.hom := by
    apply le_antisymm
    · calc
        J (k := k) (S := S) • (⊤ : Submodule (R (k := k) (S := S)) Y) =
            (J (k := k) (S := S) * J (k := k) (S := S)) •
              (⊤ : Submodule (R (k := k) (S := S)) Y) := by
                rw [quotientKernel_mul_self (k := k) (S := S)]
        _ = J (k := k) (S := S) •
            (J (k := k) (S := S) • (⊤ : Submodule (R (k := k) (S := S)) Y)) :=
              Submodule.mul_smul _ _ _
        _ ≤ J (k := k) (S := S) • LinearMap.range f.hom :=
              smul_mono_right _ hJY_le_range
    · exact smul_mono_right _ le_top
  have hrelation_map : QX.map f.hom = QY := by
    rw [show QX = J (k := k) (S := S) • (⊤ : Submodule (R (k := k) (S := S)) X) from
      relation_eq_kernel_smul_top (k := k) (S := S) X]
    rw [Submodule.map_smul'', Submodule.map_top]
    rw [← hJY_eq_range]
    exact (relation_eq_kernel_smul_top (k := k) (S := S) Y).symm
  have hinj : Function.Injective f.hom :=
    (ModuleCat.mono_iff_injective f).mp (show Mono f from hS.mono_f)
  have hmono : Mono ((S₀.map E).f) := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    obtain ⟨x₀, rfl⟩ := QX.mkQ_surjective x
    obtain ⟨y₀, rfl⟩ := QX.mkQ_surjective y
    change (extensionMap (k := k) (S := S) f).hom (QX.mkQ x₀) =
      (extensionMap (k := k) (S := S) f).hom (QX.mkQ y₀) at hxy
    rw [extensionMap_mkQ] at hxy
    have hdiff : f.hom (x₀ - y₀) ∈ QY := by
      have hh := (Submodule.Quotient.eq QY).1 hxy
      simpa only [map_sub] using hh
    have hpre : x₀ - y₀ ∈ (QX.map f.hom).comap f.hom :=
      Submodule.mem_comap.mpr (by simpa [hrelation_map] using hdiff)
    rw [Submodule.comap_map_eq_of_injective hinj] at hpre
    apply (Submodule.Quotient.eq QX).2
    exact hpre)
  have hright : (S₀.map E).Exact ∧ Epi ((S₀.map E).g) :=
    (S₀.map E).exact_and_epi_g_iff_g_is_cokernel |>.2
      ⟨CokernelCofork.mapIsColimit _ hS.gIsCokernel E⟩
  exact { exact := hright.1, mono_f := hmono, epi_g := hright.2 }

/-- The projective resolution after applying quotient extension termwise. -/
abbrev extensionMappedResolution {M : ModuleCat (R (k := k) (S := S))}
    (P : ProjectiveResolution M) : ChainComplex (ModuleCat (C (k := k) (S := S))) ℕ :=
  ((extensionFunctor (k := k) (S := S)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    P.complex

/-- Every projective resolution of a restricted quotient module stays exact at degree one after
quotient extension. -/
theorem extensionMappedResolution_exactAt_one
    (N : ModuleCat (C (k := k) (S := S)))
    (P : ProjectiveResolution
      ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)) :
    (extensionMappedResolution (k := k) (S := S) P).ExactAt 1 := by
  let E := extensionFunctor (k := k) (S := S)
  let p₀ := P.π.f 0
  let i := kernel.ι p₀
  let d₁₀ := P.complex.d 1 0
  let d₂₁ := P.complex.d 2 1
  let φ := kernel.lift p₀ d₁₀ P.complex_d_comp_π_f_zero
  have hp₀ : Epi p₀ := inferInstance
  have hkernelRow : (ShortComplex.mk i p₀ (kernel.condition p₀)).ShortExact := by
    exact { exact := ShortComplex.exact_kernel p₀ }
  have hEkernelRow :
      ((ShortComplex.mk i p₀ (kernel.condition p₀)).map E).ShortExact :=
    extension_maps_shortExact_restricted (k := k) (S := S) N i p₀
      (kernel.condition p₀) hkernelRow
  have hφEpi : Epi φ := P.exact₀.epi_kernelLift
  have hzero : d₂₁ ≫ φ = 0 := by
    apply (cancel_mono i).1
    calc
      d₂₁ ≫ φ ≫ i = d₂₁ ≫ d₁₀ := by
        change d₂₁ ≫ (kernel.lift p₀ d₁₀ P.complex_d_comp_π_f_zero ≫
          kernel.ι p₀) = _
        rw [kernel.lift_ι]
      _ = 0 := P.complex.d_comp_d 2 1 0
      _ = 0 ≫ i := zero_comp.symm
  let T := ShortComplex.mk d₂₁ φ hzero
  let U := ShortComplex.mk d₂₁ d₁₀ (P.complex.d_comp_d 2 1 0)
  let α : T ⟶ U :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := i
      comm₁₂ := by simp [T, U]
      comm₂₃ := by
        change d₁₀ = φ ≫ i
        change d₁₀ = kernel.lift p₀ d₁₀ P.complex_d_comp_π_f_zero ≫ kernel.ι p₀
        rw [kernel.lift_ι] }
  have hTExact : T.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 (P.exact_succ 0)
  have hTgEpi : Epi T.g := hφEpi
  letI : Epi T.g := hTgEpi
  have hTmapRight : (T.map E).Exact ∧ Epi ((T.map E).g) :=
    (T.map E).exact_and_epi_g_iff_g_is_cokernel |>.2
      ⟨CokernelCofork.mapIsColimit _ hTExact.gIsCokernel E⟩
  let β : T.map E ⟶ U.map E :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := E.map i
      comm₁₂ := by
        change 𝟙 _ ≫ E.map d₂₁ = E.map d₂₁ ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]
      comm₂₃ := by
        change 𝟙 _ ≫ E.map d₁₀ = E.map φ ≫ E.map i
        rw [Category.id_comp, ← E.map_comp]
        change E.map d₁₀ = E.map
          (kernel.lift p₀ d₁₀ P.complex_d_comp_π_f_zero ≫ kernel.ι p₀)
        rw [kernel.lift_ι] }
  have hEimono : Mono (E.map i) := hEkernelRow.mono_f
  letI : Mono (E.map i) := hEimono
  have hβEpi : Epi β.τ₁ := by
    change Epi (𝟙 (T.map E).X₁)
    infer_instance
  letI : Epi β.τ₁ := hβEpi
  have hβIso : IsIso β.τ₂ := by
    change IsIso (𝟙 (T.map E).X₂)
    infer_instance
  letI : IsIso β.τ₂ := hβIso
  have hβMono : Mono β.τ₃ := by
    change Mono (E.map i)
    exact hEimono
  letI : Mono β.τ₃ := hβMono
  have hUmapExact : (U.map E).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono β).1 hTmapRight.1
  change ((E.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).ExactAt 1
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  change (U.map E).Exact
  exact hUmapExact

/-- The first left-derived quotient extension vanishes on every restricted quotient module. -/
theorem extension_leftDerived_one_isZero
    (N : ModuleCat (C (k := k) (S := S))) :
    IsZero (((extensionFunctor (k := k) (S := S)).leftDerived 1).obj
      ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)) := by
  let E := extensionFunctor (k := k) (S := S)
  let M := (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N
  let P := ProjectiveResolution.of M
  have hExact := extensionMappedResolution_exactAt_one (k := k) (S := S) N P
  have hHomology : IsZero (P.complex |> fun K =>
      ((E.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology 1) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hExact
  exact IsZero.of_iso hHomology (P.isoLeftDerivedObj E 1)

/-- The first left-derived quotient extension also vanishes on the zero quotient module. -/
theorem extension_leftDerived_one_isZero_zero :
    IsZero (((extensionFunctor (k := k) (S := S)).leftDerived 1).obj
      ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj
        (ModuleCat.of (C (k := k) (S := S)) PUnit))) :=
  extension_leftDerived_one_isZero (k := k) (S := S)
    (ModuleCat.of (C (k := k) (S := S)) PUnit)

/-- The degree-one vanishing specializes to every actual restricted strict-vertex module. -/
theorem rightVertexExtension_leftDerived_one_isZero
    (v : TDA.Persistence.FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    IsZero (((extensionFunctor (k := k) (S := S)).leftDerived 1).obj
      (RightVertexRestrictedModule (k := k) (S := S) v)) :=
  extension_leftDerived_one_isZero (k := k) (S := S)
    (TDA.Persistence.IncidenceQuotientSimple.RightVertexModule (k := k) (S := S) v)

end

end TDA.Persistence.IncidenceQuotientDerivedOne
