import TDA.Topology.SingularSubdivision

/-!
# Examples for singular barycentric subdivision

On a singular `1`-simplex `σ`, singular subdivision is the difference of the two half-segments
`σ|[b, v₁] - σ|[b, v₀]` from the midpoint `b`, which start at `σ(b)` and end at the endpoints of
`σ`; its boundary is the boundary of `σ`; and it commutes with the map induced by a continuous
map. Coefficients are in an arbitrary ring.
-/

namespace TDA.Topology.SingularSubdivisionExamples

open CategoryTheory Convexity Simplicial TDA.Topology.AffineChains

noncomputable section

universe u

/-- The midpoint of the model `1`-simplex. -/
def segmentMidpoint : modelSimplex 1 := ⟨StdSimplex.barycenter, trivial⟩

/-- The barycentre of the identity `1`-simplex is the midpoint. -/
theorem simplexBarycenter_idSimplex_one :
    simplexBarycenter (isConvexSet_modelSimplex 1) (idSimplex 1) = segmentMidpoint := by
  rw [simplexBarycenter, realize_idSimplex]
  rfl

/-- The half-segment of a singular `1`-simplex `σ` from the midpoint to the vertex `i`. -/
def halfSegment {X : TopCat.{u}} (σ : (TopCat.toSSet.obj X) _⦋1⦌) (i : Fin 2) :
    (TopCat.toSSet.obj X) _⦋1⦌ :=
  (toSingular (isConvexSet_modelSimplex 1) X (modelMap σ)).app _
    (affineSSet.mk ![segmentMidpoint, idSimplex 1 i])

/-- The half-segment starts at the image of the midpoint. -/
theorem halfSegment_apply_zero {X : TopCat.{u}} (σ : (TopCat.toSSet.obj X) _⦋1⦌) (i : Fin 2) :
    X.toSSetObjEquiv _ (halfSegment σ i) (.single 0) =
      X.toSSetObjEquiv _ σ StdSimplex.barycenter := by
  simp [halfSegment, segmentMidpoint]

/-- The half-segment ends at the vertex `i` of `σ`. -/
theorem halfSegment_apply_one {X : TopCat.{u}} (σ : (TopCat.toSSet.obj X) _⦋1⦌) (i : Fin 2) :
    X.toSSetObjEquiv _ (halfSegment σ i) (.single 1) = X.toSSetObjEquiv _ σ (.single i) := by
  simp [halfSegment, idSimplex]

variable {k : Type u} [Ring k]

/-- **Subdivision of a segment**: `sd(σ) = σ|[b, v₁] - σ|[b, v₀]`. -/
theorem singularSubdivision_segment {X : TopCat.{u}} (σ : (TopCat.toSSet.obj X) _⦋1⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) σ ≫
        (singularSubdivision (ModuleCat.of k k) X).f 1 =
      (TopCat.toSSet.obj X).ιChainComplex (halfSegment σ 1) -
        (TopCat.toSSet.obj X).ιChainComplex (halfSegment σ 0) := by
  rw [ιChainComplex_singularSubdivision_f, ← Category.assoc,
    ιChainComplex_affineSubdivision_f_one, simplexBarycenter_idSimplex_one,
    Preadditive.sub_comp, SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]
  rfl

/-- The chain-map identity on a segment: `∂ sd(σ) = ∂σ`. -/
theorem singularSubdivision_segment_d {X : TopCat.{u}} (σ : (TopCat.toSSet.obj X) _⦋1⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) σ ≫
        (singularSubdivision (ModuleCat.of k k) X).f 1 ≫
          ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of k k)).d 1 0 =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of k k)).d 1 0 := by
  rw [(singularSubdivision (ModuleCat.of k k) X).comm, singularSubdivision_f_zero,
    Category.comp_id]

/-- A naturality instance: subdividing `σ` and pushing forward along `f` is subdividing the
pushed-forward simplex `f ∘ σ`. -/
theorem singularSubdivision_segment_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    (σ : (TopCat.toSSet.obj X) _⦋1⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) σ ≫
        (singularSubdivision (ModuleCat.of k k) X).f 1 ≫
          (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of k k)).f 1 =
      (TopCat.toSSet.obj Y).ιChainComplex ((TopCat.toSSet.map f).app _ σ) ≫
        (singularSubdivision (ModuleCat.of k k) Y).f 1 := by
  have h := HomologicalComplex.congr_hom (singularSubdivision_naturality (ModuleCat.of k k) f) 1
  simp only [HomologicalComplex.comp_f] at h
  rw [h, SSet.ι_chainComplexMap_f_assoc]

end

end TDA.Topology.SingularSubdivisionExamples
