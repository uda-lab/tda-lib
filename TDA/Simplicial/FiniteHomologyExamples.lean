import TDA.Simplicial.FiniteHomology
import TDA.Simplicial.FiniteCyclesExamples
import TDA.Simplicial.FiniteComplex
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex

set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v


/-! # Face coordinate fixtures

The quotient-level fixtures reuse the proved finite-cycle examples instead of
copying their boundary and inclusion matrix developments.
-/


open scoped BigOperators Matrix
open Module

namespace TDA.Simplicial

open TDA.Simplicial.InternalFiniteCycleFixtures

variable {V : Type u} [LinearOrder V]

private noncomputable abbrev simplicialCyclesQuotientWitnessExamples
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R] (n : ℕ) :
    HasQuotient (simplicialCycles K R n) (Submodule R (simplicialCycles K R n)) :=
  Submodule.hasQuotient (R := R) (M := simplicialCycles K R n)

private noncomputable abbrev coordinateCyclesQuotientWitnessExamples
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Finite (Face K n)] :
    HasQuotient (coordinateCycles K R n) (Submodule R (coordinateCycles K R n)) :=
  Submodule.hasQuotient (R := R) (M := coordinateCycles K R n)

attribute [local instance] simplicialCyclesQuotientWitnessExamples coordinateCyclesQuotientWitnessExamples

section TheoryFixtures

noncomputable local instance finiteHomologyFaceFintype
    (K : PreAbstractSimplicialComplex V) [Finite (TotalFace K)]
    (n : ℕ) : Fintype (Face K n) := faceFintypeOfTotalFinite K n

section HomologyQuotientFixtures

private theorem quotientBottom_zero (n : ℕ) (x :
    coordinateHomology (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ n) : x = 0 := by
  induction x using Quotient.inductionOn' with
  | _ z =>
    change (coordinateBoundaries (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ n).mkQ z = 0
    rw [bottom_cycles_zero n z]
    simp

private theorem quotientBottom_zero0 (x :
    coordinateHomology (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 0) : x = 0 :=
  quotientBottom_zero 0 x

private theorem quotientBottom_zero1 (x :
    coordinateHomology (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 1) : x = 0 :=
  quotientBottom_zero 1 x

private noncomputable def bottomHomologyIso0 :=
  simplicialHomologyCoordinates (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 0
private noncomputable def bottomHomologyIso1 :=
  simplicialHomologyCoordinates (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 1

private theorem bottomEdge_quotient_naturality :
    (coordinateHomologyIncl ℤ
      (bot_le : (⊥ : PreAbstractSimplicialComplex (Fin 3)) ≤ edgeK) 0).comp
        (quotientCoordinates (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 0).toLinearMap =
      (quotientCoordinates edgeK ℤ 0).toLinearMap.comp
        (simplicialQuotientIncl ℤ bot_le 0) :=
  quotientCoordinates_naturality ℤ bot_le 0

private theorem singletonQuotient_normalization (a : ℤ) :
    simplicialHomologyCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
      ((homologyKernelQuotient.{0,0,0} ℤ
        (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
          ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
            (singletonCycle a))) =
      (coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
        (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
          (singletonCycle a)) :=
  simplicialHomologyCoordinates_mkQ _ ℤ 0 (singletonCycle a)

private theorem singletonQuotient_one_ne_zero :
    (coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
      (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0 (singletonCycle 1)) ≠ 0 := by
  intro h
  exact singleton_one_not_boundary
    ((Submodule.Quotient.mk_eq_zero _).mp h)

private theorem singletonHomology_one_ne_zero :
    (homologyKernelQuotient.{0,0,0} ℤ
      (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
        ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
          (singletonCycle 1)) ≠ 0 := by
  intro h
  have hc := congrArg
    (simplicialHomologyCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0) h
  have hn := singletonQuotient_normalization 1
  have hzero : (coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
      (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
        (singletonCycle 1)) = 0 :=
    hn.symm.trans (hc.trans (map_zero _))
  exact singletonQuotient_one_ne_zero hzero

private theorem signedQuotient_nonzero :
    (coordinateBoundaries unfilledK ℤ 1).mkQ signedUnfilledCoord ≠ 0 := by
  intro h
  exact signedUnfilledCoord_not_boundary ((Submodule.Quotient.mk_eq_zero _).mp h)

private theorem signedSimplicialHomology_nonzero :
    (homologyKernelQuotient.{0,0,0} ℤ (simplicialChainComplex unfilledK ℤ) 1).inv.hom
      ((simplicialBoundaries unfilledK ℤ 1).mkQ signedUnfilledCycle) ≠ 0 := by
  intro h
  have hc := congrArg (simplicialHomologyCoordinates unfilledK ℤ 1) h
  have hn := simplicialHomologyCoordinates_mkQ unfilledK ℤ 1 signedUnfilledCycle
  have hzero : (coordinateBoundaries unfilledK ℤ 1).mkQ signedUnfilledCoord = 0 :=
    hn.symm.trans (hc.trans (map_zero _))
  exact signedQuotient_nonzero hzero

private theorem signedIncludedCycle_nonzero :
    coordinateCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCoord ≠ 0 :=
  signedUnfilled_included_ne_zero

private theorem signedIncludedClass_zero :
    (coordinateBoundaries triangleK ℤ 1).mkQ
      (coordinateCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCoord) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr signedUnfilled_included_boundary

private theorem signedQuotient_image_zero :
    coordinateHomologyIncl ℤ unfilled_le_triangle 1
      ((coordinateBoundaries unfilledK ℤ 1).mkQ signedUnfilledCoord) = 0 := by
  rw [coordinateHomologyIncl_mkQ]
  exact signedIncludedClass_zero

private theorem signedSimplicialHomology_image_zero :
    (simplicialHomologyIncl ℤ unfilled_le_triangle 1).hom
      ((homologyKernelQuotient.{0,0,0} ℤ (simplicialChainComplex unfilledK ℤ) 1).inv.hom
        ((simplicialBoundaries unfilledK ℤ 1).mkQ signedUnfilledCycle)) = 0 := by
  apply (simplicialHomologyCoordinates triangleK ℤ 1).injective
  let x := (homologyKernelQuotient.{0,0,0} ℤ
    (simplicialChainComplex unfilledK ℤ) 1).inv.hom
      ((simplicialBoundaries unfilledK ℤ 1).mkQ signedUnfilledCycle)
  have hn := congrArg (fun f => f x)
    (simplicialHomologyCoordinates_naturality ℤ unfilled_le_triangle 1)
  change coordinateHomologyIncl ℤ unfilled_le_triangle 1
      (simplicialHomologyCoordinates unfilledK ℤ 1 x) =
    simplicialHomologyCoordinates triangleK ℤ 1
      ((simplicialHomologyIncl ℤ unfilled_le_triangle 1).hom x) at hn
  have hs := simplicialHomologyCoordinates_mkQ unfilledK ℤ 1 signedUnfilledCycle
  calc
    _ = coordinateHomologyIncl ℤ unfilled_le_triangle 1
          (simplicialHomologyCoordinates unfilledK ℤ 1 x) := hn.symm
    _ = coordinateHomologyIncl ℤ unfilled_le_triangle 1
          ((coordinateBoundaries unfilledK ℤ 1).mkQ signedUnfilledCoord) := by
            exact congrArg (coordinateHomologyIncl ℤ unfilled_le_triangle 1) hs
    _ = 0 := signedQuotient_image_zero
    _ = (simplicialHomologyCoordinates triangleK ℤ 1) 0 := (map_zero _).symm


private noncomputable def edgeVertexCycle (i : Fin 2) : simplicialCycles edgeK ℤ 0 :=
  ⟨Finsupp.single (edgeVertex i) 1, by rw [simplicialCycles_zero]; trivial⟩

private noncomputable def edgeCoordVertexCycle (i : Fin 2) : coordinateCycles edgeK ℤ 0 :=
  cycleCoordinates edgeK ℤ 0 (edgeVertexCycle i)

private theorem edgeCoordVertex_coeff (i j : Fin 2) :
    (edgeCoordVertexCycle i : Face edgeK 0 → ℤ) (edgeVertex j) =
      if j = i then 1 else 0 := by
  rw [edgeCoordVertexCycle, cycleCoordinates_coe, chainCoordinates_apply]
  change (Finsupp.single (edgeVertex i) 1 : Chain edgeK ℤ 0) (edgeVertex j) = _
  by_cases h : i = j
  · subst j
    simp
  · have hs : edgeVertex i ≠ edgeVertex j := fun he => h (edgeVertex_bijective.1 he)
    simp [hs, h, eq_comm]

private theorem edgeVertex_difference_boundary :
    edgeCoordVertexCycle 1 - edgeCoordVertexCycle 0 =
      coordinateBoundaryToCycles edgeK ℤ 0 (fun _ => 1) := by
  apply Subtype.ext
  funext σ
  obtain ⟨i, rfl⟩ := edgeVertex_bijective.2 σ
  fin_cases i <;>
    simp [edgeCoordVertex_coeff, edge_boundary_scalar]

private theorem edgeEndpoint_classes_equal :
    (coordinateBoundaries edgeK ℤ 0).mkQ (edgeCoordVertexCycle 1) =
      (coordinateBoundaries edgeK ℤ 0).mkQ (edgeCoordVertexCycle 0) := by
  apply (Submodule.Quotient.eq (coordinateBoundaries edgeK ℤ 0)).mpr
  rw [edgeVertex_difference_boundary]
  exact LinearMap.mem_range_self _ _

private theorem edgeVertexEndpoint_classes_equal :
    (homologyKernelQuotient.{0,0,0} ℤ (simplicialChainComplex edgeK ℤ) 0).inv.hom
      ((simplicialBoundaries edgeK ℤ 0).mkQ (edgeVertexCycle 1)) =
    (homologyKernelQuotient.{0,0,0} ℤ (simplicialChainComplex edgeK ℤ) 0).inv.hom
      ((simplicialBoundaries edgeK ℤ 0).mkQ (edgeVertexCycle 0)) := by
  apply (simplicialHomologyCoordinates edgeK ℤ 0).injective
  calc
    _ = (coordinateBoundaries edgeK ℤ 0).mkQ (edgeCoordVertexCycle 1) :=
      simplicialHomologyCoordinates_mkQ edgeK ℤ 0 (edgeVertexCycle 1)
    _ = (coordinateBoundaries edgeK ℤ 0).mkQ (edgeCoordVertexCycle 0) :=
      edgeEndpoint_classes_equal
    _ = _ := (simplicialHomologyCoordinates_mkQ edgeK ℤ 0
      (edgeVertexCycle 0)).symm

private theorem singletonEdge_class_naturality (a : ℤ) :
    coordinateHomologyIncl ℤ singleton_le_edge 0
      ((coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
        (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0 (singletonCycle a))) =
      (coordinateBoundaries edgeK ℤ 0).mkQ
        (cycleCoordinates edgeK ℤ 0
          (simplicialCycleIncl ℤ singleton_le_edge 0 (singletonCycle a))) := by
  rw [coordinateHomologyIncl_mkQ, singleton_edge_naturality]

private theorem singletonEdge_naturality (a : ℤ) :
    coordinateHomologyIncl ℤ singleton_le_edge 0
      (simplicialHomologyCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
        ((homologyKernelQuotient.{0,0,0} ℤ
          (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
            ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
              (singletonCycle a)))) =
      simplicialHomologyCoordinates edgeK ℤ 0
        ((simplicialHomologyIncl ℤ singleton_le_edge 0).hom
          ((homologyKernelQuotient.{0,0,0} ℤ
            (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
              ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
                (singletonCycle a)))) := by
  let x := (homologyKernelQuotient.{0,0,0} ℤ
    (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
      ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
        (singletonCycle a))
  have hn := congrArg (fun f => f x)
    (simplicialHomologyCoordinates_naturality ℤ singleton_le_edge 0)
  change coordinateHomologyIncl ℤ singleton_le_edge 0
      (simplicialHomologyCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0 x) =
    simplicialHomologyCoordinates edgeK ℤ 0
      ((simplicialHomologyIncl ℤ singleton_le_edge 0).hom x) at hn
  exact hn

private theorem zmod1_quotient_naturality :
    (coordinateHomologyIncl (ZMod 1) edge_le_triangle 0).comp
      (quotientCoordinates edgeK (ZMod 1) 0).toLinearMap =
    (quotientCoordinates triangleK (ZMod 1) 0).toLinearMap.comp
      (simplicialQuotientIncl (ZMod 1) edge_le_triangle 0) :=
  quotientCoordinates_naturality (ZMod 1) edge_le_triangle 0

private theorem zmod1_naturality :
    (coordinateHomologyIncl (ZMod 1) edge_le_triangle 0).comp
      (simplicialHomologyCoordinates edgeK (ZMod 1) 0).toLinearMap =
    (simplicialHomologyCoordinates triangleK (ZMod 1) 0).toLinearMap.comp
      (simplicialHomologyIncl (ZMod 1) edge_le_triangle 0).hom :=
  simplicialHomologyCoordinates_naturality (ZMod 1) edge_le_triangle 0

private theorem finiteTotal_quotient_and_simplicialHomology
    {A B : PreAbstractSimplicialComplex V}
    [Finite (TotalFace A)] [Finite (TotalFace B)]
    (S : Type v) [CommRing S] (h : A ≤ B) (n : ℕ) :
    (coordinateHomologyIncl S h n).comp (quotientCoordinates A S n).toLinearMap =
      (quotientCoordinates B S n).toLinearMap.comp (simplicialQuotientIncl S h n) ∧
    (coordinateHomologyIncl S h n).comp (simplicialHomologyCoordinates A S n).toLinearMap =
      (simplicialHomologyCoordinates B S n).toLinearMap.comp
        (simplicialHomologyIncl S h n).hom := by
  exact ⟨quotientCoordinates_naturality S h n,
    simplicialHomologyCoordinates_naturality S h n⟩


private theorem singletonClass_identity (a : ℤ) :
    coordinateHomologyIncl ℤ
      (le_refl (Filtration.singletonFace (0 : Fin 3))) 0
      ((coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
        (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
          (singletonCycle a))) =
      (coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
        (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
          (singletonCycle a)) := by
  have h := congrArg (fun f => f
    ((coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
      (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
        (singletonCycle a))))
    (coordinateHomologyIncl_id ℤ (Filtration.singletonFace (0 : Fin 3)) 0)
  simpa only [LinearMap.id_apply] using h

private theorem singletonEdgeTriangle_class_comp (a : ℤ) :
    coordinateHomologyIncl ℤ (singleton_le_edge.trans edge_le_triangle) 0
      ((coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
        (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
          (singletonCycle a))) =
      coordinateHomologyIncl ℤ edge_le_triangle 0
        (coordinateHomologyIncl ℤ singleton_le_edge 0
          ((coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
            (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
              (singletonCycle a)))) := by
  have h := congrArg (fun f => f
    ((coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
      (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
        (singletonCycle a))))
    (coordinateHomologyIncl_comp ℤ singleton_le_edge edge_le_triangle 0)
  simpa only [LinearMap.comp_apply] using h

private theorem singletonEdgeTriangle_comp (a : ℤ) :
    coordinateHomologyIncl ℤ (singleton_le_edge.trans edge_le_triangle) 0
      (simplicialHomologyCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
        ((homologyKernelQuotient.{0,0,0} ℤ
          (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
            ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
              (singletonCycle a)))) =
      simplicialHomologyCoordinates triangleK ℤ 0
        ((simplicialHomologyIncl ℤ (singleton_le_edge.trans edge_le_triangle) 0).hom
          ((homologyKernelQuotient.{0,0,0} ℤ
            (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
              ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
                (singletonCycle a)))) := by
  let x := (homologyKernelQuotient.{0,0,0} ℤ
    (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
      ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
        (singletonCycle a))
  have hn := congrArg (fun f => f x)
    (simplicialHomologyCoordinates_naturality ℤ
      (singleton_le_edge.trans edge_le_triangle) 0)
  change coordinateHomologyIncl ℤ (singleton_le_edge.trans edge_le_triangle) 0
      (simplicialHomologyCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0 x) =
    simplicialHomologyCoordinates triangleK ℤ 0
      ((simplicialHomologyIncl ℤ (singleton_le_edge.trans edge_le_triangle) 0).hom x) at hn
  exact hn


private theorem singletonEdgeTriangle_two_step (a : ℤ) :
    (simplicialHomologyIncl ℤ (singleton_le_edge.trans edge_le_triangle) 0).hom
      ((homologyKernelQuotient.{0,0,0} ℤ
        (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
          ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
            (singletonCycle a))) =
      (simplicialHomologyIncl ℤ edge_le_triangle 0).hom
        ((simplicialHomologyIncl ℤ singleton_le_edge 0).hom
          ((homologyKernelQuotient.{0,0,0} ℤ
            (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
              ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
                (singletonCycle a)))) := by
  let x := (homologyKernelQuotient.{0,0,0} ℤ
    (simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ) 0).inv.hom
      ((simplicialBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0).mkQ
        (singletonCycle a))
  have hc := congrArg (fun f => f.hom x)
    (simplicialHomologyIncl_comp ℤ singleton_le_edge edge_le_triangle 0)
  change (simplicialHomologyIncl ℤ (singleton_le_edge.trans edge_le_triangle) 0).hom x =
    (simplicialHomologyIncl ℤ edge_le_triangle 0).hom
      ((simplicialHomologyIncl ℤ singleton_le_edge 0).hom x) at hc
  exact hc

end HomologyQuotientFixtures

end TheoryFixtures

end TDA.Simplicial
