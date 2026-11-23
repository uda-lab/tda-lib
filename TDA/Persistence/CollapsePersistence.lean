import TDA.Simplicial.CollapseHomology
import TDA.Persistence.SublevelInterleaving

set_option autoImplicit false

/-!
# Collapses of filtrations and homology persistence

Let `F` and `G` be simplicial filtrations over a preorder with `F p ≤ G p` at every index. If
`G p` collapses to `F p` at every index, the inclusion morphism `inclusionHom R n hle` of their
homology persistence modules is an isomorphism (`isIso_inclusionHom_of_collapsesTo`), in every
degree `n` and over every ring `R`. Its components are the homology maps of the actual
inclusions `F p ≤ G p`, and naturality is the functoriality of those inclusions; the
retractions of the collapses enter only through the componentwise isomorphism, so no
compatibility between retractions at different indices is needed or assumed.
`collapseInclusionIso` packages the isomorphism, with forward map `inclusionHom R n hle`.

The collapses are hypotheses here: nothing in this module produces or checks them. These are
library derivations; no source theorem is attributed to them.
-/

universe u v w

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration

variable {V : Type u} [LinearOrder V]
variable (R : Type v) [Ring R] (n : ℕ)
variable {P : Type w} [Preorder P] {F G : SimplicialFiltration P V}

/-- If `G p` collapses to `F p` at every index, the inclusion morphism of homology persistence
modules is an isomorphism, in every degree and over every ring. -/
theorem isIso_inclusionHom_of_collapsesTo (hle : ∀ p, F p ≤ G p)
    (h : ∀ p, CollapsesTo (G p) (F p)) : IsIso (inclusionHom R n hle) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro p
  exact (h p).isIso_simplicialHomologyIncl R (hle p) n

/-- The natural isomorphism of homology persistence modules induced by the inclusions, when
each stage of `G` collapses to the stage of `F` at the same index. -/
noncomputable def collapseInclusionIso (hle : ∀ p, F p ≤ G p)
    (h : ∀ p, CollapsesTo (G p) (F p)) :
    simplicialHomologyPModule R F n ≅ simplicialHomologyPModule R G n :=
  haveI := isIso_inclusionHom_of_collapsesTo R n hle h
  asIso (inclusionHom R n hle)

/-- The forward map of `collapseInclusionIso` is the inclusion morphism. -/
@[simp] theorem collapseInclusionIso_hom (hle : ∀ p, F p ≤ G p)
    (h : ∀ p, CollapsesTo (G p) (F p)) :
    (collapseInclusionIso R n hle h).hom = inclusionHom R n hle := rfl

end TDA.Persistence
