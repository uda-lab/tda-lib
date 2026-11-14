import TDA.Reeb.ThickeningCosheafComparison
import TDA.Reeb.ThickeningConstructibleExamples
import TDA.Reeb.RGraphSmoothingExamples

/-!
# Fixtures for the thickening–cosheaf comparison on constructible ℝ-spaces

Acceptance fixtures for `TDA.Reeb.ThickeningCosheafComparison`. The constant-height spaces
`constOver X c`, the indiscrete two-point space `IndiscreteBool` and its non-Hausdorff thickening
are those of `TDA.Reeb.ThickeningConstructibleExamples`; the single edge over `0 < 1`, its
subdivision over `0 < 1/2 < 1` and the subdivision isomorphism are those of
`TDA.Reeb.RGraphCosheafEquivalenceExamples`.

* **Empty input.** For the empty space at constant height, every value of `C'(T_ε X)` and of
  `C''(ℛ T_ε X)` is empty, for every `ε`, transported from the empty values of `C'(X)`
  (`thickening_empty_isEmpty`, `thickeningQuotient_empty_isEmpty`).
* **`ε = 0`.** The zero comparisons on the indiscrete two-point space, for the comparison and for
  the companion (`indiscrete_zero_comparison`, `indiscrete_zero_companion`), and the value of
  `C'(T_0 X)` at `I` corresponds to the value of `C'(X)` at `I` (`zeroValueEquiv`).
* **A non-Hausdorff constant-height input.** For the indiscrete two-point space at height `c`,
  any two points of an inverse image are joined (`joined_indiscreteBool`). So every value of
  `C'(T_ε X)` and of `C''(ℛ T_ε X)` has at most one element, although `T_ε X` is not Hausdorff
  (`indiscrete_thickening_subsingleton`, `indiscrete_thickeningQuotient_subsingleton`), and it is
  nonempty when `c ∈ I^ε` (`indiscrete_thickening_nonempty`). The classes of `(true, s)` and
  `(false, t)` agree, as do those of their Reeb classes (`indiscrete_thickening_class_eq`,
  `indiscrete_thickeningQuotient_class_eq`), and both comparisons send them to `[true]`.
* **Naturality for a nontrivial map across presentations.** The map `collapse` sends the
  indiscrete two-point space at height `0`, presented over the one level `0`, to the lower vertex
  of the single edge, presented over `0 < 1`; it is not injective (`collapse_not_injective`).
  Both comparisons are natural along it (`collapse_naturality`, `collapse_companion_naturality`),
  and along the subdivision isomorphism between the single edge over `0 < 1/2 < 1` and over
  `0 < 1`, where the companion's square is the graph square `subdivision_naturality`
  (`subdivision_companion_naturality`).
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb.Examples.ThickeningCosheafComparison

noncomputable section

open TDA.Reeb OpenInterval CylinderPresentation
open TDA.Reeb.Examples.ThickeningConstructible (constOver IndiscreteBool
  isConstructibleSpace_constOver not_t2Space_thickening_indiscreteBool)
open TDA.Reeb.Examples.Cylinder (S01 S01_value_zero)
open TDA.Reeb.RGraph.Examples (singleEdge)
open TDA.Reeb.Examples.RGraphCosheafEquivalence (singleGraph singleHalfGraph subdivisionIso)

/-- A compact locally path-connected space at constant height `c`, as a constructible ℝ-space. -/
abbrev constSpace (X : Type) [TopologicalSpace X] [CompactSpace X] [LocallyPathConnectedSpace X]
    (c : ℝ) : ConstructibleSpaceCat :=
  ⟨constOver X c, isConstructibleSpace_constOver X c⟩

/-! ### Empty input -/

/-- The empty space at constant height `c`. -/
abbrev emptySpace (c : ℝ) : ConstructibleSpaceCat := constSpace Empty c

theorem emptySpace_value_isEmpty (c : ℝ) (I : OpenInterval) :
    IsEmpty ((intervalComponents (overBaseMap (emptySpace c).obj)).obj I) :=
  ⟨fun q => by
    obtain ⟨x, -⟩ := ZerothHomotopy.mk_surjective q
    exact (x.1 : Empty).elim⟩

/-- **Empty input.** Every value of `C'(T_ε X)` is empty. -/
theorem thickening_empty_isEmpty (c : ℝ) (ε : ℝ≥0) (I : OpenInterval) :
    IsEmpty ((constructibleCosheafFunctor.obj ((thickeningFunctor ε).obj (emptySpace c))).obj.obj
      I) :=
  (constructibleThickeningValueEquiv ε (emptySpace c) I).isEmpty_congr.2
    (emptySpace_value_isEmpty c _)

/-- **Empty input.** Every value of `C''(ℛ T_ε X)` is empty. -/
theorem thickeningQuotient_empty_isEmpty (c : ℝ) (ε : ℝ≥0) (I : OpenInterval) :
    IsEmpty ((RGraph.cosheafFunctor.obj ((RGraph.thickeningQuotient ε).obj (emptySpace c))).obj.obj
      I) :=
  (constructibleThickeningQuotientValueEquiv ε (emptySpace c) I).isEmpty_congr.2
    (emptySpace_value_isEmpty c _)

/-! ### A non-Hausdorff constant-height input -/

/-- The indiscrete two-point space at constant height `c`. -/
abbrev indiscreteSpace (c : ℝ) : ConstructibleSpaceCat := constSpace IndiscreteBool c

/-- Any two points of a subspace of the indiscrete two-point space are joined: every map into it
is continuous. -/
theorem joined_indiscreteBool {p : IndiscreteBool → Prop} (x y : {b : IndiscreteBool // p b}) :
    Joined x y :=
  ⟨{ toFun := fun t => if (t : ℝ) = 0 then x else y
     continuous_toFun := continuous_induced_rng.2 continuous_top
     source' := by simp
     target' := by simp }⟩

/-- Every value of `C'(X)` has at most one element. -/
theorem indiscrete_value_subsingleton (c : ℝ) (I : OpenInterval) :
    Subsingleton ((intervalComponents (overBaseMap (indiscreteSpace c).obj)).obj I) :=
  ⟨fun a b => by
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective b
    exact Quotient.sound (joined_indiscreteBool x y)⟩

/-- **A non-Hausdorff input.** `T_ε X` is not Hausdorff, and every value of `C'(T_ε X)` has at
most one element, through the comparison. -/
theorem indiscrete_thickening_subsingleton (c : ℝ) (ε : ℝ≥0) :
    ¬ T2Space ((thickeningFunctor ε).obj (indiscreteSpace c)).obj.left ∧
      ∀ I : OpenInterval, Subsingleton
        ((constructibleCosheafFunctor.obj ((thickeningFunctor ε).obj (indiscreteSpace c))).obj.obj
          I) :=
  ⟨not_t2Space_thickening_indiscreteBool c ε, fun I =>
    (constructibleThickeningValueEquiv ε (indiscreteSpace c) I).subsingleton_congr.2
      (indiscrete_value_subsingleton c _)⟩

/-- **A non-Hausdorff input.** Every value of `C''(ℛ T_ε X)` has at most one element, through the
companion. -/
theorem indiscrete_thickeningQuotient_subsingleton (c : ℝ) (ε : ℝ≥0) (I : OpenInterval) :
    Subsingleton ((RGraph.cosheafFunctor.obj
      ((RGraph.thickeningQuotient ε).obj (indiscreteSpace c))).obj.obj I) :=
  (constructibleThickeningQuotientValueEquiv ε (indiscreteSpace c) I).subsingleton_congr.2
    (indiscrete_value_subsingleton c _)

/-- **A non-Hausdorff input.** The value of `C'(T_ε X)` at `I` is nonempty when `c ∈ I^ε`. -/
theorem indiscrete_thickening_nonempty (c : ℝ) (ε : ℝ≥0) {I : OpenInterval}
    (hc : c ∈ thicken ε I) :
    Nonempty
      ((constructibleCosheafFunctor.obj ((thickeningFunctor ε).obj (indiscreteSpace c))).obj.obj
        I) :=
  ⟨(constructibleThickeningValueEquiv ε (indiscreteSpace c) I).symm
    (ZerothHomotopy.mk ⟨(true : Bool), hc⟩)⟩

/-- A point `(b, t)` of the thickening with `c + t ∈ I`. -/
def thickPoint (c : ℝ) (ε : ℝ≥0) {I : OpenInterval} (b : Bool) (t : GeometricThickening.Band ε)
    (ht : c + (t : ℝ) ∈ I) :
    {z : (indiscreteSpace c).obj.left × GeometricThickening.Band ε //
      GeometricThickening.height (overBaseMap (indiscreteSpace c).obj) ε z ∈ I} :=
  ⟨((b : IndiscreteBool), t), ht⟩

/-- **A non-Hausdorff input.** The classes of `(true, s)` and `(false, t)` agree in `C'(T_ε X)(I)`,
and the comparison sends them to `[true]`. -/
theorem indiscrete_thickening_class_eq (c : ℝ) (ε : ℝ≥0) {I : OpenInterval}
    (s t : GeometricThickening.Band ε) (hs : c + (s : ℝ) ∈ I) (ht : c + (t : ℝ) ∈ I) :
    ZerothHomotopy.mk (thickPoint c ε true s hs) = ZerothHomotopy.mk (thickPoint c ε false t ht) ∧
      ((constructibleThickeningComparisonIso ε).hom.app (indiscreteSpace c)).hom.app I
          (ZerothHomotopy.mk (thickPoint c ε false t ht)) =
        ZerothHomotopy.mk (⟨(true : Bool),
            GeometricThickening.fst_mem_thicken (thickPoint c ε true s hs).2⟩ :
          {x : (indiscreteSpace c).obj.left // overBaseMap (indiscreteSpace c).obj x ∈
            thicken ε I}) := by
  refine ⟨(constructibleThickeningValueEquiv ε (indiscreteSpace c) I).injective
    ((indiscrete_value_subsingleton c _).elim _ _), ?_⟩
  rw [constructibleThickeningComparisonIso_hom_app_hom_app_mk]
  exact @Subsingleton.elim _ (indiscrete_value_subsingleton c (thicken ε I)) _ _

/-- **A non-Hausdorff input.** The classes of the Reeb classes of `(true, s)` and `(false, t)`
agree in `C''(ℛ T_ε X)(I)`, and the companion sends them to `[true]`. -/
theorem indiscrete_thickeningQuotient_class_eq (c : ℝ) (ε : ℝ≥0) {I : OpenInterval}
    (s t : GeometricThickening.Band ε) (hs : c + (s : ℝ) ∈ I) (ht : c + (t : ℝ) ∈ I) :
    ZerothHomotopy.mk (⟨ReebQuotient.mk _ (thickPoint c ε true s hs).1, hs⟩ :
        {q : ReebQuotient (GeometricThickening.height (overBaseMap (indiscreteSpace c).obj) ε) //
          ReebQuotient.height _ q ∈ I}) =
      ZerothHomotopy.mk (⟨ReebQuotient.mk _ (thickPoint c ε false t ht).1, ht⟩ :
        {q : ReebQuotient (GeometricThickening.height (overBaseMap (indiscreteSpace c).obj) ε) //
          ReebQuotient.height _ q ∈ I}) ∧
      ((constructibleThickeningQuotientComparisonIso ε).hom.app (indiscreteSpace c)).hom.app I
          (ZerothHomotopy.mk (⟨ReebQuotient.mk _ (thickPoint c ε false t ht).1, ht⟩ :
            {q : ReebQuotient
                (GeometricThickening.height (overBaseMap (indiscreteSpace c).obj) ε) //
              ReebQuotient.height _ q ∈ I})) =
        ZerothHomotopy.mk (⟨(true : Bool),
            GeometricThickening.fst_mem_thicken (thickPoint c ε true s hs).2⟩ :
          {x : (indiscreteSpace c).obj.left // overBaseMap (indiscreteSpace c).obj x ∈
            thicken ε I}) := by
  refine ⟨(indiscrete_thickeningQuotient_subsingleton c ε I).elim _ _, ?_⟩
  rw [constructibleThickeningQuotientComparisonIso_hom_app_hom_app_mk ε (indiscreteSpace c) I
    (thickPoint c ε false t ht)]
  exact @Subsingleton.elim _ (indiscrete_value_subsingleton c (thicken ε I)) _ _

/-! ### `ε = 0` -/

/-- **`ε = 0`.** The zero comparison on the indiscrete two-point space. -/
theorem indiscrete_zero_comparison (c : ℝ) :
    constructibleCosheafFunctor.map (thickeningFunctorZeroIso.hom.app (indiscreteSpace c)) =
      (constructibleThickeningComparisonIso 0).hom.app (indiscreteSpace c) ≫
        constructibleSmoothingZeroIso.hom.app
          (constructibleCosheafFunctor.obj (indiscreteSpace c)) :=
  constructibleCosheafFunctor_map_thickeningFunctorZeroIso_hom_app _

/-- **`ε = 0`.** The zero comparison for the companion on the indiscrete two-point space. -/
theorem indiscrete_zero_companion (c : ℝ) :
    RGraph.cosheafFunctor.map
          (quotientRGraphFunctor.map (thickeningFunctorZeroIso.hom.app (indiscreteSpace c))) ≫
        constructibleCosheafComparisonIso.inv.app (indiscreteSpace c) =
      (constructibleThickeningQuotientComparisonIso 0).hom.app (indiscreteSpace c) ≫
        constructibleSmoothingZeroIso.hom.app
          (constructibleCosheafFunctor.obj (indiscreteSpace c)) :=
  cosheafFunctor_map_thickeningFunctorZeroIso_comp_constructibleThickeningQuotientComparisonIso _

/-- **`ε = 0`.** For every constructible ℝ-space, the value of `C'(T_0 X)` at `I` corresponds to
the value of `C'(X)` at `I`. -/
def zeroValueEquiv (A : ConstructibleSpaceCat) (I : OpenInterval) :
    (constructibleCosheafFunctor.obj ((thickeningFunctor 0).obj A)).obj.obj I ≃
      (intervalComponents (overBaseMap A.obj)).obj I :=
  (constructibleThickeningValueEquiv 0 A I).trans
    (((intervalComponents (overBaseMap A.obj)).mapIso (eqToIso (thicken_zero I))).toEquiv)

/-! ### Naturality for a nontrivial map across presentations -/

/-- The lower vertex of the single edge over `0 < 1`. -/
def lowerVertex : (ofFiniteData singleEdge).Realization S01 :=
  (ofFiniteData singleEdge).ofVertex S01 0 ()

/-- The collapse of the indiscrete two-point space at height `0`, presented over the one level `0`,
to the lower vertex of the single edge, presented over `0 < 1`. -/
def collapse : indiscreteSpace 0 ⟶ RGraph.rgraphToConstructible.obj singleGraph :=
  ObjectProperty.homMk (Over.homMk (TopCat.ofHom ⟨fun _ => lowerVertex, continuous_const⟩) (by
    ext x
    change (ofFiniteData singleEdge).height S01 lowerVertex = 0
    exact S01_value_zero))

/-- The collapse identifies the two points: it is not injective. -/
theorem collapse_not_injective : ¬ Function.Injective collapse.hom.left.hom := fun h =>
  Bool.noConfusion (h rfl : ((true : Bool) : IndiscreteBool) = (false : Bool))

/-- **Naturality across presentations** for the comparison, along the collapse. -/
theorem collapse_naturality (ε : ℝ≥0) :
    constructibleCosheafFunctor.map ((thickeningFunctor ε).map collapse) ≫
        (constructibleThickeningComparisonIso ε).hom.app
          (RGraph.rgraphToConstructible.obj singleGraph) =
      (constructibleThickeningComparisonIso ε).hom.app (indiscreteSpace 0) ≫
        (constructibleSmoothing ε).map (constructibleCosheafFunctor.map collapse) :=
  (constructibleThickeningComparisonIso ε).hom.naturality collapse

/-- **Naturality across presentations** for the companion, along the collapse. -/
theorem collapse_companion_naturality (ε : ℝ≥0) :
    RGraph.cosheafFunctor.map (quotientRGraphFunctor.map ((thickeningFunctor ε).map collapse)) ≫
        (constructibleThickeningQuotientComparisonIso ε).hom.app
          (RGraph.rgraphToConstructible.obj singleGraph) =
      (constructibleThickeningQuotientComparisonIso ε).hom.app (indiscreteSpace 0) ≫
        (constructibleSmoothing ε).map (constructibleCosheafFunctor.map collapse) :=
  (constructibleThickeningQuotientComparisonIso ε).hom.naturality collapse

/-- **Naturality across critical lists** for the companion, along the subdivision isomorphism
from the single edge over `0 < 1/2 < 1` to the single edge over `0 < 1`; it is the graph square
`RGraphSmoothing.subdivision_naturality`. -/
theorem subdivision_companion_naturality (ε : ℝ≥0) :
    RGraph.cosheafFunctor.map (quotientRGraphFunctor.map
          ((thickeningFunctor ε).map (RGraph.rgraphToConstructible.map subdivisionIso.hom))) ≫
        (constructibleThickeningQuotientComparisonIso ε).hom.app
          (RGraph.rgraphToConstructible.obj singleGraph) =
      (constructibleThickeningQuotientComparisonIso ε).hom.app
          (RGraph.rgraphToConstructible.obj singleHalfGraph) ≫
        (constructibleSmoothing ε).map
          (constructibleCosheafFunctor.map (RGraph.rgraphToConstructible.map subdivisionIso.hom)) :=
  Examples.RGraphSmoothing.subdivision_naturality ε

end

end TDA.Reeb.Examples.ThickeningCosheafComparison
