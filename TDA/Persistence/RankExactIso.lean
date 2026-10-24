import TDA.Persistence.RankExact
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Isomorphism transport for rank-exact sequences

Ordinary short exactness and rank exactness are transported along actual
componentwise module isomorphisms. The rank condition is re-established from
the dying-element lifting criterion for the transported sequence.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.IsPointwiseShortExact

open CategoryTheory

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- Transport a pointwise short exact sequence along isomorphisms of its
three objects. The new maps are the actual conjugated composites. -/
theorem of_iso {L₀ M₀ N₀ L M N : PModule.{u,v,u} k P}
    {ι : L₀ ⟶ M₀} {π : M₀ ⟶ N₀} (hs : IsPointwiseShortExact ι π)
    (eL : L₀ ≅ L) (eM : M₀ ≅ M) (eN : N₀ ≅ N) :
    IsPointwiseShortExact (eL.inv ≫ ι ≫ eM.hom) (eM.inv ≫ π ≫ eN.hom) := by
  let f : L ⟶ M := eL.inv ≫ ι ≫ eM.hom
  let g : M ⟶ N := eM.inv ≫ π ≫ eN.hom
  have hzero : ι ≫ π = 0 := by
    ext a x
    have hx : (ι.app a).hom x ∈ LinearMap.range (ι.app a).hom := ⟨x, rfl⟩
    rw [hs.range_eq_ker a] at hx
    exact hx
  have hfg : f ≫ g = 0 := by
    calc
      f ≫ g = eL.inv ≫ (ι ≫ π) ≫ eN.hom := by simp [f, g, Category.assoc]
      _ = 0 := by simp [hzero]
  refine ⟨?_, ?_, ?_⟩
  · intro a x y hxy
    have hM : Function.Injective (eM.hom.app a).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have hL : Function.Injective (eL.inv.app a).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have hmid : (ι.app a).hom ((eL.inv.app a).hom x) =
        (ι.app a).hom ((eL.inv.app a).hom y) := by
      apply hM
      simpa [f, NatTrans.comp_app, ModuleCat.hom_comp] using hxy
    apply hL
    exact hs.injective a hmid
  · intro a z
    obtain ⟨m, hm⟩ := hs.surjective a ((eN.inv.app a).hom z)
    refine ⟨(eM.hom.app a).hom m, ?_⟩
    change (eN.hom.app a).hom ((π.app a).hom
      ((eM.inv.app a).hom ((eM.hom.app a).hom m))) = z
    have hcancel : (eM.inv.app a).hom ((eM.hom.app a).hom m) = m := by
      simp
    rw [hcancel, hm]
    simp
  · intro a
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      have hz := congrArg (fun q : L ⟶ N => (q.app a).hom x) hfg
      simpa [f, g, NatTrans.comp_app, ModuleCat.hom_comp] using hz
    · intro hz
      have hN : Function.Injective (eN.hom.app a).hom :=
        (ModuleCat.mono_iff_injective _).mp inferInstance
      have hz' : (π.app a).hom ((eM.inv.app a).hom z) = 0 := by
        apply hN
        simpa [g, NatTrans.comp_app, ModuleCat.hom_comp] using hz
      have hmem : (eM.inv.app a).hom z ∈ LinearMap.range (ι.app a).hom := by
        rw [hs.range_eq_ker a]
        exact hz'
      obtain ⟨x, hx⟩ := hmem
      refine ⟨(eL.hom.app a).hom x, ?_⟩
      change (eM.hom.app a).hom ((ι.app a).hom
        ((eL.inv.app a).hom ((eL.hom.app a).hom x))) = z
      have hcancelL : (eL.inv.app a).hom ((eL.hom.app a).hom x) = x := by
        simp
      rw [hcancelL, hx]
      simp

end TDA.Persistence.IsPointwiseShortExact

namespace TDA.Persistence.IsRankExact

open CategoryTheory

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- Transport rank exactness along object isomorphisms. Rank additivity is
derived by transporting dying-element lifts through the component
isomorphisms. -/
theorem of_iso {L₀ M₀ N₀ L M N : PModule.{u,v,u} k P}
    {ι : L₀ ⟶ M₀} {π : M₀ ⟶ N₀} (hs : IsRankExact ι π)
    (eL : L₀ ≅ L) (eM : M₀ ≅ M) (eN : N₀ ≅ N) :
    IsRankExact (eL.inv ≫ ι ≫ eM.hom) (eM.inv ≫ π ≫ eN.hom) := by
  let f : L ⟶ M := eL.inv ≫ ι ≫ eM.hom
  let g : M ⟶ N := eM.inv ≫ π ≫ eN.hom
  let hs' := hs.toIsPointwiseShortExact.of_iso eL eM eN
  refine
    { toIsPointwiseShortExact := hs'
      finiteDimensional := ?_
      rank_add := ?_ }
  · intro a
    letI : FiniteDimensional k (M₀.obj a) := hs.finiteDimensional a
    exact FiniteDimensional.of_injective (eM.inv.app a).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  · intro a b hab
    letI : FiniteDimensional k (M.obj a) := by
      letI : FiniteDimensional k (M₀.obj a) := hs.finiteDimensional a
      exact FiniteDimensional.of_injective (eM.inv.app a).hom
        ((ModuleCat.mono_iff_injective _).mp inferInstance)
    apply (hs'.rank_add_iff_lift_kernel hab).mpr
    intro z hz
    let z₀ := (eN.inv.app a).hom z
    have hz₀ : structureMapLinear N₀ hab z₀ = 0 := by
      have hn := congrArg (fun q : N₀.obj a ⟶ N.obj b => q.hom z₀)
        (eN.hom.naturality (homOfLE hab))
      change (eN.hom.app b).hom (structureMapLinear N₀ hab z₀) =
        structureMapLinear N hab ((eN.hom.app a).hom z₀) at hn
      have hcancel : (eN.hom.app a).hom z₀ = z := by
        simp [z₀]
      rw [hcancel, hz] at hn
      apply ((ModuleCat.mono_iff_injective (eN.hom.app b)).mp inferInstance)
      simpa using hn
    obtain ⟨m₀, hm₀, hdie₀⟩ := hs.lift_kernel hab z₀ hz₀
    refine ⟨(eM.hom.app a).hom m₀, ?_, ?_⟩
    · change (eN.hom.app a).hom ((π.app a).hom
        ((eM.inv.app a).hom ((eM.hom.app a).hom m₀))) = z
      have hcancel : (eM.inv.app a).hom ((eM.hom.app a).hom m₀) = m₀ := by
        simp
      rw [hcancel, hm₀]
      simp [z₀]
    · have hn := congrArg (fun q : M₀.obj a ⟶ M.obj b => q.hom m₀)
        (eM.hom.naturality (homOfLE hab))
      change (eM.hom.app b).hom (structureMapLinear M₀ hab m₀) =
        structureMapLinear M hab ((eM.hom.app a).hom m₀) at hn
      rw [hdie₀, map_zero] at hn
      exact hn.symm

end TDA.Persistence.IsRankExact
