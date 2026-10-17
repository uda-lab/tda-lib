import TDA.Persistence.SublevelInterleaving
import TDA.Persistence.FiniteFilterStabilitySingletonExamples
import TDA.Filtration.CechExamples
import TDA.Filtration.FilterFunctionMap

set_option autoImplicit false

/-!
# Fixtures for inclusion-induced sublevel interleavings

The additive interleaving is tested on the merged one-vertex filter, including the identity
components of the zero-parameter witness, and the face-difference bound on the two-point
Rips filter against its scaling by `2`.
-/

namespace TDA.Persistence.SublevelInterleavingExamples

open CategoryTheory TDA.Simplicial TDA.Filtration TDA.Persistence
open TDA.Persistence.StabilityExamples TDA.Filtration.Cech.Examples
open scoped NNReal ENNReal

/-! ### Additive interleaving on one vertex -/

/-- Two one-vertex filters at values `a` and `b` are `|a - b|`-interleaved. -/
noncomputable def vertexInterleaving (a b : ℝ) :
    RealInterleaving (Real.toNNReal |a - b|) (sublevelModule (ZMod 2) (vertexFilter a) 0)
      (sublevelModule (ZMod 2) (vertexFilter b) 0) :=
  sublevelInterleaving (ZMod 2) 0 (f := vertexFilter a) (g := vertexFilter b)
    (fun _ => Real.le_coe_toNNReal _)

theorem vertex_distance_le (a b : ℝ) :
    realInterleavingDistance (sublevelModule (ZMod 2) (vertexFilter a) 0)
      (sublevelModule (ZMod 2) (vertexFilter b) 0) ≤ ENNReal.ofReal |a - b| :=
  (vertexInterleaving a b).distance_le

/-- The zero-parameter self-interleaving of one vertex. -/
noncomputable def vertexSelfInterleaving (a : ℝ) :
    RealInterleaving 0 (sublevelModule (ZMod 2) (vertexFilter a) 0)
      (sublevelModule (ZMod 2) (vertexFilter a) 0) :=
  sublevelInterleaving (ZMod 2) 0 (f := vertexFilter a) (g := vertexFilter a)
    (fun _ => by simp)

/-- After the canonical zero-shift identification, the first map of the zero-parameter witness
is the identity. -/
theorem vertexSelfInterleaving_φ (a : ℝ) :
    (vertexSelfInterleaving a).φ ≫ (RealShift.zeroIso _).hom = 𝟙 _ := by
  have : (vertexSelfInterleaving a).φ ≫ (RealShift.zeroIso _).hom =
      inclusionHom (ZMod 2) 0 (fun t => le_refl ((vertexFilter a).sublevelFiltration t)) := by
    apply NatTrans.ext
    funext t
    exact (simplicialHomologyIncl_comp _ _ _ _).symm
  rw [this, inclusionHom_refl]

/-- After the canonical zero-shift identification, the second map of the zero-parameter
witness is the identity. -/
theorem vertexSelfInterleaving_ψ (a : ℝ) :
    (vertexSelfInterleaving a).ψ ≫ (RealShift.zeroIso _).hom = 𝟙 _ := by
  have : (vertexSelfInterleaving a).ψ ≫ (RealShift.zeroIso _).hom =
      inclusionHom (ZMod 2) 0 (fun t => le_refl ((vertexFilter a).sublevelFiltration t)) := by
    apply NatTrans.ext
    funext t
    exact (simplicialHomologyIncl_comp _ _ _ _).symm
  rw [this, inclusionHom_refl]

/-! ### Face difference bound on two points -/

/-- The two-point Rips filter and its scaling by `2` have sublevel modules within the maximal
face difference. -/
theorem twoPoints_scale_distance_le :
    realInterleavingDistance (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) 0)
      (sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 zero_lt_two) 0) ≤
      ENNReal.ofReal (faceSupDifference (Rips.filter TwoPoints.metric)
        ((Rips.filter TwoPoints.metric).scale 2 zero_lt_two)) :=
  realInterleavingDistance_sublevel_le_faceSupDifference (ZMod 2) 0 _ _

/-- The per-face bound used in the proof, at the edge, where the difference is `2`. -/
theorem twoPoints_edge_difference :
    |(Rips.filter TwoPoints.metric).value TwoPoints.edgeFace -
        ((Rips.filter TwoPoints.metric).scale 2 zero_lt_two).value TwoPoints.edgeFace| = 2 ∧
      |(Rips.filter TwoPoints.metric).value TwoPoints.edgeFace -
        ((Rips.filter TwoPoints.metric).scale 2 zero_lt_two).value TwoPoints.edgeFace| ≤
        faceSupDifference (Rips.filter TwoPoints.metric)
          ((Rips.filter TwoPoints.metric).scale 2 zero_lt_two) := by
  refine ⟨?_, abs_face_difference_le _ _ _⟩
  rw [FilterFunction.scale_value, TwoPoints.rips_value]
  norm_num

end TDA.Persistence.SublevelInterleavingExamples
