import TDA.Reeb.ThickeningPresentation
import TDA.Reeb.RGraphThickening
import TDA.Reeb.ConstructibleGeometricInterleaving

/-!
# Thickenings of constructible ℝ-spaces are constructible

For every constructible ℝ-space `(X, f)` (`IsConstructibleSpace`) and every `ε ≥ 0`, the geometric
thickening `(X × [-ε, ε], (x, t) ↦ f x + t)` is constructible
(de Silva–Munch–Patel, *Categorified Reeb Graphs*, Theorem 4.27, in general form). No Hausdorff
hypothesis is placed on `X` or on the pieces of its presentation, and `ε = 0` is not treated
separately.

## Assembly

For a presentation `P` over levels `S`, `thickOverIso` is the isomorphism over `ℝ` from the
thickening of the realization to the realization of the thickening presentation
`P.shiftedThick S ε` on the shifted witness `S.shifted ε`, whose levels are the distinct values of
`(S - ε) ∪ (S + ε)` in increasing order. It is `shiftedThickHomeomorph` with its height equation.
The pieces of `P.shiftedThick S ε` are compact and locally path-connected when those of `P` are,
so the thickening of the realization is constructible
(`isConstructibleSpace_thickening_realization`). For an arbitrary constructible `A`, the
thickening functor carries the isomorphism `A ≅ |P|` supplied by `IsConstructibleSpace` to an
isomorphism of thickenings (`thickOverIsoOfIso`), which gives
`isConstructibleSpace_thickening_of_isConstructibleSpace`. No geometric argument beyond the
thickening presentation is used here.

The shifted witness is an admissible critical set for the thickening, not necessarily the minimal
one: some of the values `a i ± ε` can be regular for the thickened height. Its exact critical set
(DMP Corollary 4.28) is not claimed.

## Functor and specializations

`thickeningFunctor ε` lifts `GeometricThickening.functor ε` to an endofunctor of constructible
ℝ-spaces on all height-preserving maps. On graph input the general theorem specializes to the
graph statement (`isConstructibleSpace_thickening_of_isRGraph`), and the lift restricts to
`RGraph.thickeningToConstructible` (`rgraphToConstructible_comp_thickeningFunctor`); followed by
the Reeb quotient it is `RGraph.thickeningQuotient`
(`thickeningFunctor_comp_quotientRGraphFunctor`).

The vertex piece of the thickening presentation at a shifted level `b j` is homeomorphic to the
fiber of the thickened height over `b j` (`windowFiberHomeomorph`).

See `docs/math/reeb-thickening-constructible.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

open GeometricThickening (Band)

namespace CylinderPresentation

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{0} n) (ε : ℝ≥0)

/-- **The thickening over `ℝ`.** The thickening of the realization of `P` is isomorphic over `ℝ`
to the realization of the thickening presentation on the shifted witness `S.shifted ε`. No
hypothesis on the pieces is used. -/
def thickOverIso :
    (GeometricThickening.functor ε).obj (Over.mk (TopCat.ofHom (P.height S))) ≅
      Over.mk (TopCat.ofHom ((P.shiftedThick S ε).height (S.shifted ε))) :=
  Over.isoMk (TopCat.isoOfHomeo
      (X := ((GeometricThickening.functor ε).obj (Over.mk (TopCat.ofHom (P.height S)))).left)
      (Y := TopCat.of ((P.shiftedThick S ε).Realization (S.shifted ε)))
      (P.shiftedThickHomeomorph S ε).symm) (by
    ext z
    change (P.shiftedThick S ε).height (S.shifted ε) ((P.shiftedThickHomeomorph S ε).symm z) =
      GeometricThickening.height (P.height S) ε z
    exact P.height_thickHomeomorph_symm S ε _ _ z)

theorem thickOverIso_hom_left_apply
    (z : ((GeometricThickening.functor ε).obj (Over.mk (TopCat.ofHom (P.height S)))).left) :
    (P.thickOverIso S ε).hom.left z = (P.shiftedThickHomeomorph S ε).symm z :=
  rfl

theorem thickOverIso_inv_left_apply
    (x : (Over.mk (TopCat.ofHom ((P.shiftedThick S ε).height (S.shifted ε)))).left) :
    (P.thickOverIso S ε).inv.left x = P.shiftedThickHomeomorph S ε x :=
  rfl

/-- **Transport.** An isomorphism `A ≅ |P|` over `ℝ` gives an isomorphism from the thickening of
`A` to the realization of the thickening presentation on the shifted witness. -/
def thickOverIsoOfIso {A : Over (TopCat.of ℝ)} (i : A ≅ Over.mk (TopCat.ofHom (P.height S))) :
    (GeometricThickening.functor ε).obj A ≅
      Over.mk (TopCat.ofHom ((P.shiftedThick S ε).height (S.shifted ε))) :=
  (GeometricThickening.functor ε).mapIso i ≪≫ P.thickOverIso S ε

/-- **Presentation-level form on the shifted grid.** If the pieces of `P` are compact and locally
path-connected, the thickening of its realization is constructible, presented by
`P.shiftedThick S ε` over `S.shifted ε`. -/
theorem isConstructibleSpace_thickening_realization [∀ i, CompactSpace (P.V i)]
    [∀ i, LocallyPathConnectedSpace (P.V i)] [∀ e, CompactSpace (P.E e)]
    [∀ e, LocallyPathConnectedSpace (P.E e)] :
    IsConstructibleSpace
      ((GeometricThickening.functor ε).obj (Over.mk (TopCat.ofHom (P.height S)))) :=
  ⟨_, S.shifted ε, P.shiftedThick S ε, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, ⟨P.thickOverIso S ε⟩⟩

/-- **The vertex pieces as fibers.** The vertex piece of the thickening presentation at the
shifted level `b j`, the window at `b j`, is homeomorphic to the fiber of the thickened height
over `b j`. -/
def windowFiberHomeomorph (j : Fin (S.shiftedCount ε + 1)) :
    P.Window S ε ((S.shifted ε).value j) ≃ₜ
      GeometricThickening.height (P.height S) ε ⁻¹' {(S.shifted ε).value j} :=
  ((P.shiftedThick S ε).criticalFiberHomeomorph (S.shifted ε) j).trans
    ((P.shiftedThickHomeomorph S ε).subtype fun x => by
      rw [mem_preimage, mem_preimage, height_shiftedThickHomeomorph])

/-- The fiber homeomorphism sends a window point `ξ` to `(ξ, b j - f ξ)`. -/
theorem coe_windowFiberHomeomorph (j : Fin (S.shiftedCount ε + 1))
    (ξ : P.Window S ε ((S.shifted ε).value j)) :
    (P.windowFiberHomeomorph S ε j ξ : P.Realization S × Band ε) =
      (P.windowToSpace S ε _ ξ, ⟨(S.shifted ε).value j - P.height S (P.windowToSpace S ε _ ξ),
        GeometricThickening.sub_mem_band _ (P.height_windowToSpace_mem S ε _ ξ)⟩) :=
  rfl

end CylinderPresentation

/-- **DMP Theorem 4.27, general form.** The geometric thickening of every constructible ℝ-space is
constructible, for every `ε ≥ 0`, with no Hausdorff hypothesis. If `A` is presented by `P` over
`S`, its thickening is presented by `P.shiftedThick S ε` over the shifted witness `S.shifted ε`,
an admissible, not necessarily minimal, critical set. -/
theorem isConstructibleSpace_thickening_of_isConstructibleSpace {A : Over (TopCat.of ℝ)}
    (hA : IsConstructibleSpace A) (ε : ℝ≥0) :
    IsConstructibleSpace ((GeometricThickening.functor ε).obj A) := by
  obtain ⟨n, S, P, h1, h2, h3, h4, ⟨i⟩⟩ := hA
  exact ⟨_, S.shifted ε, P.shiftedThick S ε, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, ⟨P.thickOverIsoOfIso S ε i⟩⟩

/-- **The thickening functor on constructible ℝ-spaces**, on all height-preserving maps. -/
def thickeningFunctor (ε : ℝ≥0) : ConstructibleSpaceCat ⥤ ConstructibleSpaceCat :=
  IsConstructibleSpace.lift (IsConstructibleSpace.ι ⋙ GeometricThickening.functor ε)
    fun A => isConstructibleSpace_thickening_of_isConstructibleSpace A.property ε

theorem thickeningFunctor_comp_ι (ε : ℝ≥0) :
    thickeningFunctor ε ⋙ IsConstructibleSpace.ι =
      IsConstructibleSpace.ι ⋙ GeometricThickening.functor ε :=
  rfl

theorem thickeningFunctor_obj_obj (ε : ℝ≥0) (A : ConstructibleSpaceCat) :
    ((thickeningFunctor ε).obj A).obj = (GeometricThickening.functor ε).obj A.obj :=
  rfl

theorem thickeningFunctor_map_hom (ε : ℝ≥0) {A B : ConstructibleSpaceCat} (φ : A ⟶ B) :
    ((thickeningFunctor ε).map φ).hom = (GeometricThickening.functor ε).map φ.hom :=
  rfl

/-- **Graph input as a specialization.** The thickening of a graph object is constructible,
derived from the general theorem through `isConstructibleSpace_of_isRGraph`; compare
`RGraph.isConstructibleSpace_thickening` (DMP Proposition 4.26). -/
theorem isConstructibleSpace_thickening_of_isRGraph {A : Over (TopCat.of ℝ)}
    (hA : RGraph.IsRGraph A) (ε : ℝ≥0) :
    IsConstructibleSpace ((GeometricThickening.functor ε).obj A) :=
  isConstructibleSpace_thickening_of_isConstructibleSpace (isConstructibleSpace_of_isRGraph hA) ε

/-- On graph objects the lift is the graph thickening lift `RGraph.thickeningToConstructible`. -/
theorem rgraphToConstructible_comp_thickeningFunctor (ε : ℝ≥0) :
    RGraph.rgraphToConstructible ⋙ thickeningFunctor ε = RGraph.thickeningToConstructible ε :=
  rfl

/-- Followed by the Reeb quotient, the lift is `RGraph.thickeningQuotient`. -/
theorem thickeningFunctor_comp_quotientRGraphFunctor (ε : ℝ≥0) :
    thickeningFunctor ε ⋙ quotientRGraphFunctor = RGraph.thickeningQuotient ε :=
  rfl

end

end TDA.Reeb
