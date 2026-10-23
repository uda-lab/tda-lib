import TDA.Persistence.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Rank exact sequences and lifting of dying elements

A pointwise short exact sequence is rank exact when the dimensions of all structure-map
images are additive. For pointwise finite dimensional modules, this condition is equivalent
to surjectivity on the kernels of all structure maps: an element that dies in the quotient
can be lifted to an element that dies at the same grade in the middle module.

This is the element-level lifting criterion behind hook projectivity in Botnan, Oppermann,
Oudot and Scoccola, *On the bottleneck stability of rank decompositions of multi-parameter
persistence modules*, arXiv:2208.00300v3, Section 2.14 and Theorem 2.7. It does not construct
an exact-category instance, hook modules, or rank projective resolutions.
-/

set_option autoImplicit false

universe u v w x

namespace TDA.Persistence

open CategoryTheory

variable {k : Type u} [Field k] {P : Type v} [Preorder P]
variable {L M N : PModule.{u,v,w} k P}

/-- Ordinary short exactness, expressed on the vector spaces at every index. -/
structure IsPointwiseShortExact (ι : L ⟶ M) (π : M ⟶ N) : Prop where
  injective : ∀ p, Function.Injective (ι.app p).hom
  surjective : ∀ p, Function.Surjective (π.app p).hom
  range_eq_ker : ∀ p, LinearMap.range (ι.app p).hom = LinearMap.ker (π.app p).hom

/-- Rank exactness for pointwise finite-dimensional modules. Short exactness
derives finite dimensionality of the outer fibers from the middle fibers. -/
structure IsRankExact (ι : L ⟶ M) (π : M ⟶ N) : Prop extends
    IsPointwiseShortExact ι π where
  finiteDimensional : ∀ a, FiniteDimensional k (M.obj a)
  rank_add : ∀ {a b : P} (hab : a ≤ b),
    Module.finrank k (LinearMap.range (structureMapLinear M hab)) =
      Module.finrank k (LinearMap.range (structureMapLinear L hab)) +
      Module.finrank k (LinearMap.range (structureMapLinear N hab))

private def kernelMap (π : M ⟶ N) {a b : P} (hab : a ≤ b) :
    LinearMap.ker (structureMapLinear M hab) →ₗ[k]
      LinearMap.ker (structureMapLinear N hab) :=
  ((π.app a).hom.comp (LinearMap.ker (structureMapLinear M hab)).subtype).codRestrict
    (LinearMap.ker (structureMapLinear N hab)) (by
      intro m
      change structureMapLinear N hab ((π.app a).hom m.val) = 0
      have hn := congrArg (fun f : M.obj a ⟶ N.obj b => f.hom m.val)
        (π.naturality (homOfLE hab))
      change (π.app b).hom (structureMapLinear M hab m.val) =
        structureMapLinear N hab ((π.app a).hom m.val) at hn
      rw [m.property, map_zero] at hn
      exact hn.symm)

private def kernelInclusion (ι : L ⟶ M) {a b : P} (hab : a ≤ b) :
    LinearMap.ker (structureMapLinear L hab) →ₗ[k]
      LinearMap.ker (structureMapLinear M hab) := kernelMap ι hab

private theorem kernelInclusion_injective (ι : L ⟶ M) {a b : P} (hab : a ≤ b)
    (hi : Function.Injective (ι.app a).hom) :
    Function.Injective (kernelInclusion ι hab) := by
  intro x y h
  apply Subtype.ext
  apply hi
  exact congrArg Subtype.val h

private theorem kernelInclusion_range (ι : L ⟶ M) (π : M ⟶ N)
    (hs : IsPointwiseShortExact ι π) {a b : P} (hab : a ≤ b) :
    LinearMap.range (kernelInclusion ι hab) = LinearMap.ker (kernelMap π hab) := by
  ext m
  constructor
  · rintro ⟨l, rfl⟩
    apply Subtype.ext
    change (π.app a).hom ((ι.app a).hom l.val) = 0
    have hr : (ι.app a).hom l.val ∈ LinearMap.range (ι.app a).hom := ⟨l.val, rfl⟩
    rw [hs.range_eq_ker a] at hr
    exact hr
  · intro hm
    have hz : (π.app a).hom m.val = 0 := congrArg Subtype.val hm
    have hmrange : m.val ∈ LinearMap.range (ι.app a).hom := by
      rw [hs.range_eq_ker a]
      exact hz
    obtain ⟨l, hl⟩ := hmrange
    have hdie : structureMapLinear L hab l = 0 := by
      apply hs.injective b
      have hn := congrArg (fun f : L.obj a ⟶ M.obj b => f.hom l)
        (ι.naturality (homOfLE hab))
      change (ι.app b).hom (structureMapLinear L hab l) =
        structureMapLinear M hab ((ι.app a).hom l) at hn
      rw [hl, m.property] at hn
      simpa using hn
    exact ⟨⟨l, hdie⟩, Subtype.ext hl⟩

private theorem shortExact_finrank (ι : L ⟶ M) (π : M ⟶ N)
    (hs : IsPointwiseShortExact ι π) (a : P)
    [FiniteDimensional k (M.obj a)] :
    Module.finrank k (M.obj a) =
      Module.finrank k (L.obj a) + Module.finrank k (N.obj a) := by
  have hd := LinearMap.finrank_range_add_finrank_ker (π.app a).hom
  rw [LinearMap.range_eq_top.mpr (hs.surjective a), finrank_top,
    ← hs.range_eq_ker a, LinearMap.finrank_range_of_inj (hs.injective a)] at hd
  omega

private theorem kernelMap_rank_formula (ι : L ⟶ M) (π : M ⟶ N)
    (hs : IsPointwiseShortExact ι π) {a b : P} (hab : a ≤ b)
    [FiniteDimensional k (M.obj a)] :
    Module.finrank k (LinearMap.range (kernelMap π hab)) +
      Module.finrank k (LinearMap.ker (structureMapLinear L hab)) =
        Module.finrank k (LinearMap.ker (structureMapLinear M hab)) := by
  have hd := LinearMap.finrank_range_add_finrank_ker (kernelMap π hab)
  rw [← kernelInclusion_range ι π hs hab,
    LinearMap.finrank_range_of_inj (kernelInclusion_injective ι hab (hs.injective a))] at hd
  exact hd

/-- In a finite dimensional short exact sequence, rank additivity at `a ≤ b` is equivalent
to lifting every quotient element killed by `a → b` to a middle element killed by `a → b`.
Only the source fibers need be finite dimensional. -/
theorem IsPointwiseShortExact.rank_add_iff_lift_kernel
    {ι : L ⟶ M} {π : M ⟶ N} (hs : IsPointwiseShortExact ι π)
    {a b : P} (hab : a ≤ b)
    [FiniteDimensional k (M.obj a)] :
    (Module.finrank k (LinearMap.range (structureMapLinear M hab)) =
      Module.finrank k (LinearMap.range (structureMapLinear L hab)) +
      Module.finrank k (LinearMap.range (structureMapLinear N hab))) ↔
    (∀ n : N.obj a, structureMapLinear N hab n = 0 →
      ∃ m : M.obj a, (π.app a).hom m = n ∧ structureMapLinear M hab m = 0) := by
  have : FiniteDimensional k (L.obj a) :=
    FiniteDimensional.of_injective (ι.app a).hom (hs.injective a)
  have : FiniteDimensional k (N.obj a) :=
    FiniteDimensional.of_surjective (π.app a).hom (hs.surjective a)
  have hdim := shortExact_finrank ι π hs a
  have hkernel := kernelMap_rank_formula ι π hs hab
  have hL := LinearMap.finrank_range_add_finrank_ker (structureMapLinear L hab)
  have hM := LinearMap.finrank_range_add_finrank_ker (structureMapLinear M hab)
  have hN := LinearMap.finrank_range_add_finrank_ker (structureMapLinear N hab)
  constructor
  · intro hr n hn
    have hfull : LinearMap.range (kernelMap π hab) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      omega
    obtain ⟨m, hm⟩ := (LinearMap.range_eq_top.mp hfull) ⟨n, hn⟩
    exact ⟨m.val, congrArg Subtype.val hm, m.property⟩
  · intro hlift
    have hsurj : Function.Surjective (kernelMap π hab) := by
      intro n
      obtain ⟨m, hm, hdie⟩ := hlift n.val n.property
      exact ⟨⟨m, hdie⟩, Subtype.ext hm⟩
    have hfull := LinearMap.range_eq_top.mpr hsurj
    have hdimrange : Module.finrank k (LinearMap.range (kernelMap π hab)) =
        Module.finrank k (LinearMap.ker (structureMapLinear N hab)) := by
      rw [hfull, finrank_top]
    omega

/-- Rank exactness supplies lifts preserving the grade where an element dies. -/
theorem IsRankExact.lift_kernel {ι : L ⟶ M} {π : M ⟶ N} (hs : IsRankExact ι π)
    {a b : P} (hab : a ≤ b)
    (n : N.obj a) (hn : structureMapLinear N hab n = 0) :
    ∃ m : M.obj a, (π.app a).hom m = n ∧ structureMapLinear M hab m = 0 := by
  letI := hs.finiteDimensional a
  exact (hs.toIsPointwiseShortExact.rank_add_iff_lift_kernel hab).mp (hs.rank_add hab) n hn

/-- A natural section makes an ordinary short exact sequence rank exact. -/
theorem IsPointwiseShortExact.rankExact_of_section
    {ι : L ⟶ M} {π : M ⟶ N} (hs : IsPointwiseShortExact ι π)
    [∀ a, FiniteDimensional k (M.obj a)]
    (σ : N ⟶ M) (hσ : σ ≫ π = 𝟙 N) : IsRankExact ι π where
  toIsPointwiseShortExact := hs
  finiteDimensional _ := inferInstance
  rank_add := by
    intro a b hab
    apply (hs.rank_add_iff_lift_kernel hab).mpr
    intro n hn
    refine ⟨(σ.app a).hom n, ?_, ?_⟩
    · have he := congrArg (fun f : N ⟶ N => (f.app a).hom n) hσ
      exact he
    · have he := congrArg (fun f : N.obj a ⟶ M.obj b => f.hom n)
        (σ.naturality (homOfLE hab))
      change (σ.app b).hom (structureMapLinear N hab n) =
        structureMapLinear M hab ((σ.app a).hom n) at he
      rw [hn, map_zero] at he
      exact he.symm

/-- Pointwise short exactness is preserved by restriction along any monotone map. -/
theorem IsPointwiseShortExact.reindex {Q : Type x} [Preorder Q]
    {ι : L ⟶ M} {π : M ⟶ N} (hs : IsPointwiseShortExact ι π) (f : Q →o P) :
    IsPointwiseShortExact (reindexNatTrans f ι) (reindexNatTrans f π) where
  injective q := hs.injective (f q)
  surjective q := hs.surjective (f q)
  range_eq_ker q := hs.range_eq_ker (f q)

/-- Rank exactness is preserved by restriction; diagonal shifts are a special case. -/
theorem IsRankExact.reindex {Q : Type x} [Preorder Q]
    {ι : L ⟶ M} {π : M ⟶ N} (hs : IsRankExact ι π) (f : Q →o P) :
    IsRankExact (reindexNatTrans f ι) (reindexNatTrans f π) where
  toIsPointwiseShortExact := hs.toIsPointwiseShortExact.reindex f
  finiteDimensional q := hs.finiteDimensional (f q)
  rank_add hab := hs.rank_add (f.monotone hab)

end TDA.Persistence
