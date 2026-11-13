import TDA.Persistence.Reduction.FiniteInputHomologyDimensions

/-! Dimensions of the actual signed simplicial homology map, in every degree. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- Target coordinates carry the actual image onto the computed matrix image. -/
theorem homologyMapMatrix_range (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f) :
    LinearMap.range (homologyMapMatrix xs ys p a b f).mulVecLin =
      (LinearMap.range
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom).map
          (sublevelCoordinates ys hy p b).toLinearMap := by
  have he : (homologyMapMatrix xs ys p a b f).mulVecLin.comp
        (sublevelCoordinates xs hx p a).toLinearMap =
      (sublevelCoordinates ys hy p b).toLinearMap.comp
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom := by
    ext x i
    exact congrFun (homologyMapMatrix_correct xs ys hx hy p a b f hm x).symm i
  rw [← LinearEquiv.range_comp (sublevelCoordinates xs hx p a)
    (homologyMapMatrix xs ys p a b f).mulVecLin, he, LinearMap.range_comp]

/-- The computed rank is the dimension of the actual induced homology-map image. -/
theorem homologyMapDimensions_rank_actual (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f) :
    (homologyMapDimensions xs ys p a b f).rank = Module.finrank (ZMod 2)
      (LinearMap.range
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom) := by
  rw [homologyMapDimensions_rank, homologyMapMatrix_range xs ys hx hy p a b f hm]
  exact (sublevelCoordinates ys hy p b).finrank_map_eq _

/-- Natural-number subtraction loses no information: it gives the actual kernel dimension. -/
theorem homologyMapDimensions_nullity_actual (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f) :
    (homologyMapDimensions xs ys p a b f).nullity = Module.finrank (ZMod 2)
      (LinearMap.ker
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom) := by
  let := (sublevelCoordinates xs hx p a).symm.finiteDimensional
  have hr := (simplicialHomologyMap (ZMod 2)
    (validatedVertexMap xs ys hx hy a b f hm) p).hom.finrank_range_add_finrank_ker
  rw [sublevelHomology_finrank] at hr
  have hc := homologyMapDimensions_rank_nullity xs ys p a b f
  rw [homologyMapDimensions_rank_actual xs ys hx hy p a b f hm] at hc
  omega

theorem homologyMapDimensions_injective_iff (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f) :
    (homologyMapDimensions xs ys p a b f).nullity = 0 ↔ Function.Injective
      (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom := by
  let := (sublevelCoordinates xs hx p a).symm.finiteDimensional
  rw [homologyMapDimensions_nullity_actual xs ys hx hy p a b f hm,
    Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]

theorem homologyMapDimensions_surjective_iff (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f) :
    (homologyMapDimensions xs ys p a b f).rank = (activeRepresentatives ys p b).length ↔
      Function.Surjective
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom := by
  let := (sublevelCoordinates ys hy p b).symm.finiteDimensional
  rw [homologyMapDimensions_rank_actual xs ys hx hy p a b f hm, ← sublevelHomology_finrank ys hy p b]
  constructor
  · intro h
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq h)
  · intro h
    rw [LinearMap.range_eq_top.mpr h, finrank_top]

/-- Success supplies the geometric hypotheses and exact image/kernel dimensions. -/
theorem runHomologyDimensions_correct (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (out : HomologyMapDimensions) (hout : runHomologyDimensions xs ys p a b f = some out) :
    ∃ (hx : Valid xs) (hy : Valid ys) (hm : VertexMapCondition xs ys a b f),
      out.rank = Module.finrank (ZMod 2) (LinearMap.range
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom) ∧
      out.nullity = Module.finrank (ZMod 2) (LinearMap.ker
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom) := by
  obtain ⟨⟨hx, hy, hm⟩, rfl⟩ := (runHomologyDimensions_eq_some_iff xs ys p a b f out).mp hout
  exact ⟨hx, hy, hm, homologyMapDimensions_rank_actual xs ys hx hy p a b f hm,
    homologyMapDimensions_nullity_actual xs ys hx hy p a b f hm⟩

end TDA.Persistence.Reduction.FiniteInput
