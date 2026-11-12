import TDA.Persistence.Reduction.FiniteInputHomologyMap
import TDA.Persistence.Reduction.FiniteInputVertexMapChains

/-! The computed matrices represent the existing actual homology maps on every class. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration CategoryTheory

theorem vectorSublevelClass_basisRecord (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (i : BasisIndex xs p a) :
    vectorSublevelClass xs h p a (chainVector (basisRecord xs p a i).cycle)
      (basisRecord_cycleInput xs h p a i) = basisClass xs h p a i := by
  apply (sublevelCoordinates xs h p a).injective
  rw [← rawCycleCoordinates_correct xs h p a _ _, sublevelCoordinates_basisClass]
  exact rawCycleCoordinates_basisRecord xs p a i

theorem homologyMapMatrix_column (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f)
    (j : BasisIndex xs p a) :
    (homologyMapMatrix xs ys p a b f).col j =
      sublevelCoordinates ys hy p b
        ((simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom
          (basisClass xs hx p a j)) := by
  funext i
  rw [Matrix.col_apply, homologyMapMatrix_apply, rawCycleCoordinates_correct ys hy p b _
    (vertexVector_cycleInput xs ys hx hy p a b f hm _ (basisRecord_cycleInput xs hx p a j)),
    ← vertexVector_class xs ys hx hy p a b f hm _ (basisRecord_cycleInput xs hx p a j),
    vectorSublevelClass_basisRecord]

/-- Every actual homology class is transported by the executed matrix in the existing bases. -/
theorem homologyMapMatrix_correct (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f)
    (x : simplicialHomology ((gradeFilter xs hx).sublevel a) (ZMod 2) p) :
    sublevelCoordinates ys hy p b
        ((simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom x) =
      (homologyMapMatrix xs ys p a b f).mulVec (sublevelCoordinates xs hx p a x) := by
  have he : (sublevelCoordinates ys hy p b).toLinearMap.comp
      (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom =
      (homologyMapMatrix xs ys p a b f).mulVecLin.comp (sublevelCoordinates xs hx p a).toLinearMap := by
    apply (sublevelBasis xs hx p a).ext
    intro i
    rw [sublevelBasis_apply]
    change _ = (homologyMapMatrix xs ys p a b f).mulVec
      (sublevelCoordinates xs hx p a (basisClass xs hx p a i))
    rw [sublevelCoordinates_basisClass, Matrix.mulVec_single_one]
    exact (homologyMapMatrix_column xs ys hx hy p a b f hm i).symm
  exact LinearMap.congr_fun he x

theorem homologyMapMatrix_cycle (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    rawCycleCoordinates ys p b (vertexVector xs ys a f v) =
      (homologyMapMatrix xs ys p a b f).mulVec (rawCycleCoordinates xs p a v) := by
  rw [rawCycleCoordinates_correct ys hy p b _ (vertexVector_cycleInput xs ys hx hy p a b f hm v hv),
    ← vertexVector_class xs ys hx hy p a b f hm v hv, homologyMapMatrix_correct,
    rawCycleCoordinates_correct xs hx p a v hv]

/-- Successful execution supplies the geometric map conditions and its every-class semantics. -/
theorem runHomologyMap_correct (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (out : List (List (ZMod 2))) (hout : runHomologyMap xs ys p a b f = some out) :
    ∃ (hx : Valid xs) (hy : Valid ys) (hm : VertexMapCondition xs ys a b f),
      out = homologyMapRows xs ys p a b f ∧
      ∀ x : simplicialHomology ((gradeFilter xs hx).sublevel a) (ZMod 2) p,
        sublevelCoordinates ys hy p b
            ((simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom x) =
          (homologyMapMatrix xs ys p a b f).mulVec (sublevelCoordinates xs hx p a x) := by
  obtain ⟨⟨hx, hy, hm⟩, he⟩ := (runHomologyMap_eq_some_iff xs ys p a b f out).mp hout
  exact ⟨hx, hy, hm, he, homologyMapMatrix_correct xs ys hx hy p a b f hm⟩

theorem homologyMapMatrix_id (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    homologyMapMatrix xs xs p a a id = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨x, rfl⟩ := (sublevelCoordinates xs h p a).surjective v
  rw [← homologyMapMatrix_correct xs xs h h p a a id (vertexMapCondition_id xs a a le_rfl)]
  have he : validatedVertexMap xs xs h h a a id (vertexMapCondition_id xs a a le_rfl) =
      VertexMap.id ((gradeFilter xs h).sublevel a) := by ext; rfl
  rw [he, simplicialHomologyMap_id, Matrix.one_mulVec]
  rfl

/-- Composition uses target-after-source multiplication, including rectangular and empty matrices. -/
theorem homologyMapMatrix_comp (xs ys zs : Input) (hx : Valid xs) (hy : Valid ys) (hz : Valid zs)
    (p : ℕ) (a b c : ℤ) (f g : ℕ → ℕ)
    (hf : VertexMapCondition xs ys a b f) (hg : VertexMapCondition ys zs b c g) :
    homologyMapMatrix xs zs p a c (g ∘ f) =
      homologyMapMatrix ys zs p b c g * homologyMapMatrix xs ys p a b f := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨x, rfl⟩ := (sublevelCoordinates xs hx p a).surjective v
  rw [← Matrix.mulVec_mulVec,
    ← homologyMapMatrix_correct xs ys hx hy p a b f hf,
    ← homologyMapMatrix_correct ys zs hy hz p b c g hg,
    ← homologyMapMatrix_correct xs zs hx hz p a c (g ∘ f) (vertexMapCondition_comp xs ys zs a b c f g hf hg)]
  have he : validatedVertexMap xs zs hx hz a c (g ∘ f)
      (vertexMapCondition_comp xs ys zs a b c f g hf hg) =
      VertexMap.comp (validatedVertexMap xs ys hx hy a b f hf)
        (validatedVertexMap ys zs hy hz b c g hg) := by ext; rfl
  rw [he, simplicialHomologyMap_comp]
  rfl

/-- Identity vertex functions between sublevels recover the existing inclusion-coordinate matrix. -/
theorem homologyMapMatrix_inclusion (xs : Input) (h : Valid xs) (p : ℕ) (a b : ℤ) (hab : a ≤ b) :
    homologyMapMatrix xs xs p a b id = basisTransition xs p a b := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨x, rfl⟩ := (sublevelCoordinates xs h p a).surjective v
  rw [← homologyMapMatrix_correct xs xs h h p a b id (vertexMapCondition_id xs a b hab),
    ← sublevelCoordinates_naturality xs h p a b hab]
  have he : validatedVertexMap xs xs h h a b id (vertexMapCondition_id xs a b hab) =
      inclusionVertexMap ((gradeFilter xs h).sublevel_mono hab) := by ext; rfl
  rw [he, simplicialHomologyMap_inclusion]

end TDA.Persistence.Reduction.FiniteInput
