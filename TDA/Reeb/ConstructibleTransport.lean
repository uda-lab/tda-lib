import TDA.Reeb.ConstructibleGeometricInterleaving

/-!
# Constructible ℝ-spaces transported along homeomorphisms

`IsConstructibleSpace`, `constructibleInterleavingDistance` and the objects of
`ConstructibleSpaceCat` live in `Over (TopCat.of ℝ)`, a slice of `TopCat.{0}`; their carriers are
types in universe `0`. A space `X : Type u` with a height `f : C(X, ℝ)` is transported to a
universe-`0` model `Z` by a homeomorphism `e : X ≃ₜ Z`, with height `f ∘ e.symm`.

* `overIsoOfHomeomorph`: a height-compatible homeomorphism of universe-`0` carriers is an
  isomorphism in `Over (TopCat.of ℝ)`.
* `isConstructibleSpace_iff_of_homeomorph`: constructibility is invariant under it.
* `constructibleInterleavingDistance_eq_of_homeomorph`: so is the constructible interleaving
  distance of two constructible spaces; the value does not depend on the universe-`0` model.
* `constructibleInterleavingDistance_le_edist_of_homeomorph`: the sup-norm stability bound of
  `constructibleInterleavingDistance_le_edist` for heights `f g : C(X, ℝ)` on a carrier
  `X : Type u`, whose transports to a universe-`0` model are constructible.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

universe u

namespace TDA.Reeb

noncomputable section

namespace RGraph

/-- A homeomorphism of universe-`0` carriers compatible with the heights is an isomorphism in the
slice over `ℝ`. -/
def overIsoOfHomeomorph {Z Z' : Type} [TopologicalSpace Z] [TopologicalSpace Z'] (e : Z ≃ₜ Z')
    {f : C(Z, ℝ)} {f' : C(Z', ℝ)} (h : ∀ z, f' (e z) = f z) :
    Over.mk (TopCat.ofHom f) ≅ Over.mk (TopCat.ofHom f') :=
  Over.isoMk (TopCat.isoOfHomeo e) (by ext z; exact h z)

/-- Constructibility of a space over `ℝ` is invariant under height-compatible homeomorphism. -/
theorem isConstructibleSpace_iff_of_homeomorph {Z Z' : Type} [TopologicalSpace Z]
    [TopologicalSpace Z'] (e : Z ≃ₜ Z') {f : C(Z, ℝ)} {f' : C(Z', ℝ)}
    (h : ∀ z, f' (e z) = f z) :
    IsConstructibleSpace (Over.mk (TopCat.ofHom f)) ↔
      IsConstructibleSpace (Over.mk (TopCat.ofHom f')) := by
  have i := overIsoOfHomeomorph e h
  constructor
  · rintro ⟨n, S, P, a, b, c, d, ⟨j⟩⟩
    exact ⟨n, S, P, a, b, c, d, ⟨i.symm ≪≫ j⟩⟩
  · rintro ⟨n, S, P, a, b, c, d, ⟨j⟩⟩
    exact ⟨n, S, P, a, b, c, d, ⟨i ≪≫ j⟩⟩

/-- The constructible interleaving distance of two constructible spaces over `ℝ` equals that of
their transports along a height-compatible homeomorphism. -/
theorem constructibleInterleavingDistance_eq_of_homeomorph {Z Z' : Type} [TopologicalSpace Z]
    [TopologicalSpace Z'] (e : Z ≃ₜ Z') {f g : C(Z, ℝ)} {f' g' : C(Z', ℝ)}
    (hf : ∀ z, f' (e z) = f z) (hg : ∀ z, g' (e z) = g z)
    (hF : IsConstructibleSpace (Over.mk (TopCat.ofHom f)))
    (hG : IsConstructibleSpace (Over.mk (TopCat.ofHom g))) :
    constructibleInterleavingDistance ⟨_, hF⟩ ⟨_, hG⟩ =
      constructibleInterleavingDistance ⟨_, (isConstructibleSpace_iff_of_homeomorph e hf).1 hF⟩
        ⟨_, (isConstructibleSpace_iff_of_homeomorph e hg).1 hG⟩ :=
  constructibleInterleavingDistance_congr
    (ObjectProperty.isoMk _ (overIsoOfHomeomorph e hf))
    (ObjectProperty.isoMk _ (overIsoOfHomeomorph e hg))

/-- Sup-norm stability for heights on a carrier `X : Type u` homeomorphic to a universe-`0` space
`Z`: if the transports `f ∘ e.symm` and `g ∘ e.symm` are constructible, their constructible
interleaving distance is at most the uniform extended distance of `f` and `g`. -/
theorem constructibleInterleavingDistance_le_edist_of_homeomorph
    {X : Type u} [TopologicalSpace X] {Z : Type} [TopologicalSpace Z] (e : X ≃ₜ Z)
    {f g : C(X, ℝ)}
    (hf : IsConstructibleSpace (Over.mk (TopCat.ofHom (f.comp ⟨e.symm, e.symm.continuous⟩))))
    (hg : IsConstructibleSpace (Over.mk (TopCat.ofHom (g.comp ⟨e.symm, e.symm.continuous⟩)))) :
    constructibleInterleavingDistance ⟨_, hf⟩ ⟨_, hg⟩ ≤
      edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) := by
  refine (constructibleInterleavingDistance_le_edist hf hg).trans ?_
  rw [UniformFun.edist_def, UniformFun.edist_def]
  refine iSup_le fun z => ?_
  simpa using le_iSup (fun x => edist (f x) (g x)) (e.symm z)

end RGraph

end

end TDA.Reeb
