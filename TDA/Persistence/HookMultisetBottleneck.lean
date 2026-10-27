import TDA.Persistence.HookMatching

/-!
# Bottleneck matching for finite hook multisets

Finite hook multisets are compared by enumerating every occurrence and using
the existing partial matching, whose paired entries and deletions carry actual
coordinate interleavings. Multiset equality records repeated hook tags with
their full multiplicities.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence NNReal ENNReal ZeroObject

variable {k : Type u} [Field k] {n : ℕ}

private instance : HasFiniteBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable def flattenedHookIndex
    {J : Type} [Fintype J]
    {X : J → PModule.{u,0,u} k (Fin n → ℝ)}
    (P : ∀ j, FiniteHookSumPresentation (k := k) (n := n)
      (X j)) : Fin (Fintype.card (Σ j, Fin (P j).count)) ≃
        Σ j, Fin (P j).count :=
  (Fintype.equivFin _).symm

private noncomputable def flattenedHookTag
    {J : Type} [Fintype J]
    {X : J → PModule.{u,0,u} k (Fin n → ℝ)}
    (P : ∀ j, FiniteHookSumPresentation (k := k) (n := n) (X j)) :
    Fin (Fintype.card (Σ j, Fin (P j).count)) → RealHookTag (n := n) :=
  fun r => (P (flattenedHookIndex (k := k) P r).1).tag
    (flattenedHookIndex (k := k) P r).2

/-- Present the biproduct of finitely many presented hook sums as one hook
sum. The flattened index type contains a separate index for every
constituent occurrence. -/
noncomputable def FiniteHookSumPresentation.biproduct
    {J : Type} [Fintype J]
    (X : J → PModule.{u,0,u} k (Fin n → ℝ))
    (P : ∀ j, FiniteHookSumPresentation (k := k) (n := n) (X j)) :
    FiniteHookSumPresentation (k := k) (n := n) (⨁ X) := by
  classical
  let I := Σ j, Fin (P j).count
  let e : Fin (Fintype.card I) ≃ I := flattenedHookIndex (k := k) P
  let tag := flattenedHookTag (k := k) P
  let tagModule : I → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun a => FiniteRankProjectiveClassification.rankProjectiveHookModule
      (k := k) ((P a.1).tag a.2)
  let eInner : (⨁ fun j => ⨁ fun a : Fin (P j).count =>
      FiniteRankProjectiveClassification.rankProjectiveHookModule
        (k := k) ((P j).tag a)) ≅ ⨁ tagModule :=
    biproductBiproductIso (fun j => Fin (P j).count) (fun j a =>
      FiniteRankProjectiveClassification.rankProjectiveHookModule
        (k := k) ((P j).tag a))
  let eReindex : (⨁ fun r : Fin (Fintype.card I) =>
      tagModule (e r)) ≅
      ⨁ tagModule := biproduct.reindex
        (β := Fin (Fintype.card I)) (γ := I) e tagModule
  refine ⟨Fintype.card I, tag, ?_⟩
  exact (biproduct.mapIso (fun j => (P j).iso)).trans
    (eInner.trans eReindex.symm)

/-- Flattening a finite family of hook presentations adds their tag
multisets, preserving the multiplicity of every tag. -/
theorem FiniteHookSumPresentation.hookTagMultiset_biproduct
    {J : Type} [Fintype J]
    (X : J → PModule.{u,0,u} k (Fin n → ℝ))
    (P : ∀ j, FiniteHookSumPresentation (k := k) (n := n) (X j)) :
    hookTagMultiset (FiniteHookSumPresentation.biproduct
      (k := k) (n := n) X P).tag =
      ∑ j, hookTagMultiset (P j).tag := by
  classical
  let I := Σ j, Fin (P j).count
  let e : Fin (Fintype.card I) ≃ I := flattenedHookIndex (k := k) P
  let tag := flattenedHookTag (k := k) P
  ext t
  unfold FiniteHookSumPresentation.biproduct
  change (hookTagMultiset tag).count t = _
  calc
    (hookTagMultiset tag).count t = Fintype.card {r : Fin (Fintype.card I) // tag r = t} :=
      hookTagMultiset_count tag t
    _ = Fintype.card (Σ j, {a : Fin (P j).count // (P j).tag a = t}) := by
      let indexedTag : I → RealHookTag (n := n) :=
        fun a => (P a.1).tag a.2
      let eToFiber : {r : Fin (Fintype.card I) // tag r = t} ≃
          {a : I // indexedTag a = t} :=
        e.subtypeEquiv (by intro r; rfl)
      let fiberSigma : {a : I // indexedTag a = t} ≃
          (Σ j : J, {a : Fin (P j).count // (P j).tag a = t}) := {
        toFun := fun a => ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
        left_inv := by rintro ⟨⟨j, a⟩, h⟩; rfl
        right_inv := by rintro ⟨j, ⟨a, h⟩⟩; rfl }
      let occurrenceEquiv := eToFiber.trans fiberSigma
      exact Fintype.card_congr occurrenceEquiv
    _ = ∑ j, Fintype.card {a : Fin (P j).count // (P j).tag a = t} :=
      Fintype.card_sigma
    _ = (∑ j, hookTagMultiset (P j).tag).count t := by
      rw [Multiset.count_sum']
      simp only [hookTagMultiset_count]

/-- A matching of finite multisets consists of exact occurrence enumerations
and an existing hook occurrence matching on those enumerations. -/
def HasMultisetMatching (ρ : ℝ≥0)
    (A B : Multiset (RealHookTag (n := n))) : Prop :=
  ∃ (m ℓ : ℕ) (F : Fin m → RealHookTag (n := n))
      (G : Fin ℓ → RealHookTag (n := n)),
    hookTagMultiset F = A ∧ hookTagMultiset G = B ∧
      ∃ M : OccurrenceMatching (Fin m) (Fin ℓ) PEmpty.{1} PEmpty.{1},
        HookMatching.IsMatching (k := k) ρ F G M

/-- Package exact multiset enumerations and an actual occurrence matching as
a matching witness for their multiset values. -/
theorem HasMultisetMatching.intro {ρ : ℝ≥0}
    {A B : Multiset (RealHookTag (n := n))} {m ℓ : ℕ}
    (F : Fin m → RealHookTag (n := n)) (G : Fin ℓ → RealHookTag (n := n))
    (hF : hookTagMultiset F = A) (hG : hookTagMultiset G = B)
    (M : OccurrenceMatching (Fin m) (Fin ℓ) PEmpty.{1} PEmpty.{1})
    (hM : HookMatching.IsMatching (k := k) ρ F G M) :
    HasMultisetMatching (k := k) ρ A B :=
  ⟨m, ℓ, F, G, hF, hG, M, hM⟩

/-- Extract the finite enumerations and actual occurrence matching from a
multiset matching witness. -/
theorem HasMultisetMatching.elim {ρ : ℝ≥0}
    {A B : Multiset (RealHookTag (n := n))}
    (h : HasMultisetMatching (k := k) ρ A B) :
    ∃ (m ℓ : ℕ) (F : Fin m → RealHookTag (n := n))
        (G : Fin ℓ → RealHookTag (n := n)),
      hookTagMultiset F = A ∧ hookTagMultiset G = B ∧
        ∃ M : OccurrenceMatching (Fin m) (Fin ℓ) PEmpty.{1} PEmpty.{1},
          HookMatching.IsMatching (k := k) ρ F G M := h

/-- The extended bottleneck dissimilarity of finite hook multisets, defined
as the infimum of finite radii admitting an actual occurrence matching. -/
noncomputable def hookMultisetBottleneckDistance
    (A B : Multiset (RealHookTag (n := n))) : ℝ≥0∞ :=
  ⨅ (ρ : ℝ≥0) (_ : HasMultisetMatching (k := k) ρ A B), (ρ : ℝ≥0∞)

/-- Any actual multiset matching bounds the bottleneck infimum. -/
theorem hookMultisetBottleneckDistance_le_of_matching
    {A B : Multiset (RealHookTag (n := n))} {ρ : ℝ≥0}
    (h : HasMultisetMatching (k := k) ρ A B) :
    hookMultisetBottleneckDistance (k := k) A B ≤ ρ :=
  iInf_le_of_le ρ (iInf_le _ h)

/-- A lower bound for the hook-multiset bottleneck distance is equivalent to
the same bound for every radius admitting an actual matching. -/
theorem le_hookMultisetBottleneckDistance_iff
    (A B : Multiset (RealHookTag (n := n))) (r : ℝ≥0∞) :
    r ≤ hookMultisetBottleneckDistance (k := k) A B ↔
      ∀ ρ, ∀ _h : HasMultisetMatching (k := k) ρ A B, r ≤ (ρ : ℝ≥0∞) := by
  simp only [hookMultisetBottleneckDistance, le_iInf_iff]

/-- Strictly above the hook-multiset bottleneck infimum is equivalent to
being above the radius of some actual matching; no minimizer is required. -/
theorem hookMultisetBottleneckDistance_lt_iff
    (A B : Multiset (RealHookTag (n := n))) (r : ℝ≥0∞) :
    hookMultisetBottleneckDistance (k := k) A B < r ↔
      ∃ ρ, ∃ _h : HasMultisetMatching (k := k) ρ A B, (ρ : ℝ≥0∞) < r := by
  simp only [hookMultisetBottleneckDistance, iInf_lt_iff, exists_prop]

end TDA.Persistence
