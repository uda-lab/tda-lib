import TDA.Persistence.CollapsePersistence
import TDA.Persistence.AlphaH0
import TDA.Filtration.AlphaCollapseExamples

set_option autoImplicit false

/-!
# Collapse-induced persistence isomorphisms on the obtuse triangle

On the exact obtuse triangle of `RationalAlpha.Examples.obtuse`, with labels `0, 1, 2` at the
sites `(0,0)`, `(4,0)` and `(1,1)`, the squared-grade Čech stage collapses to the α stage at
every grade (`AlphaCollapseExamples.collapsesTo`): by deleting the free pair
`({0,1}, {0,1,2})` on `[4, 5)` and by the empty sequence elsewhere.

At grade `4` the deletion of the long edge, and the labelled inclusion of the α stage into the
Čech stage, induce isomorphisms of ordinary homology in every degree and over every ring
(`isIso_deletion_long_edge`, `isIso_alpha_cech_four`). Over all grades, the labelled inclusions
induce a natural isomorphism of the homology persistence modules in every degree and over every
ring (`isIso_inclusionHom`, `alphaCechIso`). In degree zero over a field its forward map is the
existing `alphaH0Comparison` (`alphaCechIso_zero_hom`, a definitional equality by `rfl`, not an
independent comparison).
-/

namespace TDA.Persistence.CollapsePersistenceExamples

open CategoryTheory TDA.Simplicial TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.Examples TDA.Filtration.AlphaCollapseExamples

/-- At grade `4`, deleting the long edge from the Čech stage induces an isomorphism of ordinary
homology in every degree, over every ring. -/
theorem isIso_deletion_long_edge (R : Type*) [Ring R] (n : ℕ) :
    IsIso (simplicialHomologyIncl R
      (deletion_le (Alpha.squaredCechFiltration (realSites obtuse) 4) {0,1}) n) :=
  (isFreePair_long_edge le_rfl).isIso_simplicialHomologyIncl R n

/-- At grade `4`, the labelled inclusion of the α stage into the Čech stage induces an
isomorphism of ordinary homology in every degree, over every ring. -/
theorem isIso_alpha_cech_four (R : Type*) [Ring R] (n : ℕ) :
    IsIso (simplicialHomologyIncl R
      (Alpha.labelledComplexFiltration_le_squaredCech (realSites obtuse) 4) n) :=
  (collapsesTo 4).isIso_simplicialHomologyIncl R _ n

/-- The labelled inclusions induce an isomorphism of homology persistence modules, in every
degree and over every ring. -/
theorem isIso_inclusionHom (R : Type*) [Ring R] (n : ℕ) :
    IsIso (inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech (realSites obtuse))) :=
  isIso_inclusionHom_of_collapsesTo R n _ collapsesTo

/-- The natural isomorphism from α persistence to squared-grade Čech persistence of the obtuse
triangle induced by the labelled inclusions. -/
noncomputable def alphaCechIso (R : Type*) [Ring R] (n : ℕ) :
    simplicialHomologyPModule R (Alpha.labelledComplexFiltration (realSites obtuse)) n ≅
      simplicialHomologyPModule R (Alpha.squaredCechFiltration (realSites obtuse)) n :=
  collapseInclusionIso R n (Alpha.labelledComplexFiltration_le_squaredCech (realSites obtuse))
    collapsesTo

/-- The forward map of `alphaCechIso` is the inclusion morphism. -/
theorem alphaCechIso_hom (R : Type*) [Ring R] (n : ℕ) :
    (alphaCechIso R n).hom =
      inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech (realSites obtuse)) :=
  rfl

/-- In degree zero over a field, the forward map of `alphaCechIso` is `alphaH0Comparison`.
The proof is `rfl`: both sides are defined as the same inclusion morphism, so this records that
the two definitions agree and is not an independent comparison. -/
theorem alphaCechIso_zero_hom (k : Type*) [Field k] :
    (alphaCechIso k 0).hom = alphaH0Comparison (realSites obtuse) k :=
  rfl

end TDA.Persistence.CollapsePersistenceExamples
