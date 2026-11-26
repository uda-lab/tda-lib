import Mathlib.Algebra.Homology.DerivedCategory.Plus
import TDA.Sheaf.StalkPullback

/-!
# Isomorphisms in `D⁺(Sh X)` are detected on stalks of homology sheaves

Let `k` be a ring and `X : TopCat.{0}`. A morphism `φ` of `DerivedCategory.Plus (Sh X)`, where
`Sh X = X.Sheaf (ModuleCat k)`, is an isomorphism if and only if, for every degree `i` and every
point `x`, the stalk at `x` of the `i`-th homology sheaf map `Hⁱ(φ)` is an isomorphism
(`isIso_iff_isIso_stalk_homology`).

The proof combines two Mathlib facts: a morphism of `D⁺` is an isomorphism when all its homology
maps are (`DerivedCategory.Plus.isIso_iff`), and a morphism of sheaves of modules is an
isomorphism when all its stalk maps are (`TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`).
-/

noncomputable section
open CategoryTheory

namespace TDA.Sheaf

variable {k : Type} [Ring k]

/-- **Stalkwise detection of isomorphisms in `D⁺(Sh X)`.** A morphism `φ` of bounded below
complexes of sheaves of `k`-modules in the derived category is an isomorphism if and only if, in
every degree `i` and at every point `x`, the stalk map of the homology sheaf map `Hⁱ(φ)` is an
isomorphism. -/
theorem isIso_iff_isIso_stalk_homology {X : TopCat.{0}}
    [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
    {K L : DerivedCategory.Plus (X.Sheaf (ModuleCat.{0} k))} (φ : K ⟶ L) :
    IsIso φ ↔ ∀ (i : ℤ) (x : X), IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).map
      ((DerivedCategory.Plus.homologyFunctor _ i).map φ).hom) := by
  rw [DerivedCategory.Plus.isIso_iff]
  exact forall_congr' fun i => TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _

end TDA.Sheaf
