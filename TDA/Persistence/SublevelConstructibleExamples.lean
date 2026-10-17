import TDA.Persistence.SublevelConstructible
import TDA.Persistence.DiagramMap
import TDA.Persistence.FiniteFilterStabilitySingletonExamples
import TDA.Persistence.Reduction.ActualTriangleDiagrams
import TDA.Persistence.Reduction.ActualEmpty
import TDA.Filtration.CechExamples
import TDA.Filtration.FilterFunctionMap

set_option autoImplicit false

/-!
# Fixtures for the sublevel constructibility bridge

The bridge is tested on the two-point and Euclidean-triangle Čech and Rips filters, on the
certified filled, hollow, tied and empty ℕ-graded examples transported to `ℝ`, and on the
one-vertex filter, where the isometry gives the exact interleaving distance. Two negative
controls refute the actual constructibility predicate on a grid above the first critical value
and on a grid omitting a critical value.
-/

namespace TDA.Persistence.SublevelConstructibleExamples

open CategoryTheory CategoryTheory.Limits TDA.Simplicial TDA.Filtration TDA.Persistence
open TDA.Persistence.FiniteConstructible TDA.Persistence.StabilityExamples
open TDA.Filtration.Cech.Examples TDA.Persistence.Reduction.Examples
open scoped NNReal ENNReal

/-! ### Rank of a sublevel fiber -/

/-- The dimension of a sublevel homology fiber is its count of diagram points alive there. -/
private theorem finrank_sublevelHomology {V : Type} [LinearOrder V]
    {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)] (f : FilterFunction K ℝ)
    (n : ℕ) (t : ℝ) :
    Module.finrank (ZMod 2) (simplicialHomology (f.sublevel t) (ZMod 2) n) =
      (dgm (ZMod 2) f n).points.countP (fun p => p.1 ≤ t ∧ (t : WithTop ℝ) < p.2) := by
  rw [← rank_sublevelHomologyMap (ZMod 2) f n t t le_rfl]
  have h : simplicialHomologyIncl (ZMod 2) (f.sublevel_mono (le_refl t)) n = 𝟙 _ :=
    simplicialHomologyIncl_id (ZMod 2) (f.sublevel t) n
  rw [h, ModuleCat.hom_id, LinearMap.range_id, finrank_top]

/-- Sublevel homology of a filter on a finite complex is finite-dimensional. -/
private theorem sublevelHomology_finiteDimensional {V : Type} [LinearOrder V]
    {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)] (f : FilterFunction K ℝ)
    (n : ℕ) (t : ℝ) :
    FiniteDimensional (ZMod 2) (simplicialHomology (f.sublevel t) (ZMod 2) n) := by
  let _ : Finite (Face K n) := faceFiniteOfTotalFinite K n
  let _ : Finite (Face (f.sublevel t) n) :=
    Finite.of_injective (faceIncl (f.sublevel_le t) n) (by
      intro a b hab
      exact Subtype.ext (congrArg (fun s : Face K n => s.1) hab))
  infer_instance

/-- The grid with no values. -/
noncomputable def emptyGrid : Fin 0 ↪o ℝ :=
  OrderEmbedding.ofStrictMono Fin.elim0 (Subsingleton.strictMono _)

/-! ### Two points on the line -/

/-- Both two-point sublevel modules are constructible on their critical grids. -/
theorem twoPoints_isConstructible (n : ℕ) :
    IsConstructible (Cech.filter TwoPoints.pts).criticalValue
        (sublevelModule (ZMod 2) (Cech.filter TwoPoints.pts) n) ∧
      IsConstructible (Rips.filter TwoPoints.metric).criticalValue
        (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) n) :=
  ⟨sublevelModule_isConstructible (ZMod 2) n _, sublevelModule_isConstructible (ZMod 2) n _⟩

/-- The two-point module diagrams in degree zero are the filter diagrams. -/
theorem twoPoints_moduleDiagram_zero :
    moduleDiagram (Cech.filter TwoPoints.pts).criticalValue
        (sublevelModule (ZMod 2) (Cech.filter TwoPoints.pts) 0)
        (sublevelModule_finiteDimensional (ZMod 2) 0 _) =
        dgm (ZMod 2) (Cech.filter TwoPoints.pts) 0 ∧
      moduleDiagram (Rips.filter TwoPoints.metric).criticalValue
        (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) 0)
        (sublevelModule_finiteDimensional (ZMod 2) 0 _) =
        dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0 :=
  ⟨moduleDiagram_sublevelModule (ZMod 2) 0 _, moduleDiagram_sublevelModule (ZMod 2) 0 _⟩

/-- The two-point module diagrams in degree one are the filter diagrams. -/
theorem twoPoints_moduleDiagram_one :
    moduleDiagram (Cech.filter TwoPoints.pts).criticalValue
        (sublevelModule (ZMod 2) (Cech.filter TwoPoints.pts) 1)
        (sublevelModule_finiteDimensional (ZMod 2) 1 _) =
        dgm (ZMod 2) (Cech.filter TwoPoints.pts) 1 ∧
      moduleDiagram (Rips.filter TwoPoints.metric).criticalValue
        (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) 1)
        (sublevelModule_finiteDimensional (ZMod 2) 1 _) =
        dgm (ZMod 2) (Rips.filter TwoPoints.metric) 1 :=
  ⟨moduleDiagram_sublevelModule (ZMod 2) 1 _, moduleDiagram_sublevelModule (ZMod 2) 1 _⟩

/-- The two-point Čech and Rips diagrams are at the interleaving distance of their modules. -/
theorem twoPoints_bottleneck_eq (n : ℕ) :
    bottleneck (dgm (ZMod 2) (Cech.filter TwoPoints.pts) n)
        (dgm (ZMod 2) (Rips.filter TwoPoints.metric) n) =
      realInterleavingDistance (sublevelModule (ZMod 2) (Cech.filter TwoPoints.pts) n)
        (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) n) :=
  bottleneck_dgm_eq_realInterleavingDistance (ZMod 2) n _ _

/-- The two-point Čech and Rips diagrams have equally many essential classes. -/
theorem twoPoints_essential_card_eq (n : ℕ) :
    (essentialPart (dgm (ZMod 2) (Cech.filter TwoPoints.pts) n).points).card =
      (essentialPart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) n).points).card :=
  essentialPart_card_dgm_eq (ZMod 2) n _ _

/-! ### The Euclidean triangle -/

/-- Both triangle sublevel modules are constructible on their critical grids. -/
theorem triangle_isConstructible (n : ℕ) :
    IsConstructible (Cech.filter Triangle.pts).criticalValue
        (sublevelModule (ZMod 2) (Cech.filter Triangle.pts) n) ∧
      IsConstructible (Rips.filter Triangle.metric).criticalValue
        (sublevelModule (ZMod 2) (Rips.filter Triangle.metric) n) :=
  ⟨sublevelModule_isConstructible (ZMod 2) n _, sublevelModule_isConstructible (ZMod 2) n _⟩

/-- The triangle module diagrams in degree zero are the filter diagrams. -/
theorem triangle_moduleDiagram_zero :
    moduleDiagram (Cech.filter Triangle.pts).criticalValue
        (sublevelModule (ZMod 2) (Cech.filter Triangle.pts) 0)
        (sublevelModule_finiteDimensional (ZMod 2) 0 _) =
        dgm (ZMod 2) (Cech.filter Triangle.pts) 0 ∧
      moduleDiagram (Rips.filter Triangle.metric).criticalValue
        (sublevelModule (ZMod 2) (Rips.filter Triangle.metric) 0)
        (sublevelModule_finiteDimensional (ZMod 2) 0 _) =
        dgm (ZMod 2) (Rips.filter Triangle.metric) 0 :=
  ⟨moduleDiagram_sublevelModule (ZMod 2) 0 _, moduleDiagram_sublevelModule (ZMod 2) 0 _⟩

/-- The triangle module diagrams in degree one are the filter diagrams. -/
theorem triangle_moduleDiagram_one :
    moduleDiagram (Cech.filter Triangle.pts).criticalValue
        (sublevelModule (ZMod 2) (Cech.filter Triangle.pts) 1)
        (sublevelModule_finiteDimensional (ZMod 2) 1 _) =
        dgm (ZMod 2) (Cech.filter Triangle.pts) 1 ∧
      moduleDiagram (Rips.filter Triangle.metric).criticalValue
        (sublevelModule (ZMod 2) (Rips.filter Triangle.metric) 1)
        (sublevelModule_finiteDimensional (ZMod 2) 1 _) =
        dgm (ZMod 2) (Rips.filter Triangle.metric) 1 :=
  ⟨moduleDiagram_sublevelModule (ZMod 2) 1 _, moduleDiagram_sublevelModule (ZMod 2) 1 _⟩

/-- The triangle Čech and Rips diagrams are at the interleaving distance of their modules. -/
theorem triangle_bottleneck_eq (n : ℕ) :
    bottleneck (dgm (ZMod 2) (Cech.filter Triangle.pts) n)
        (dgm (ZMod 2) (Rips.filter Triangle.metric) n) =
      realInterleavingDistance (sublevelModule (ZMod 2) (Cech.filter Triangle.pts) n)
        (sublevelModule (ZMod 2) (Rips.filter Triangle.metric) n) :=
  bottleneck_dgm_eq_realInterleavingDistance (ZMod 2) n _ _

/-- The triangle Čech and Rips diagrams have equally many essential classes. -/
theorem triangle_essential_card_eq (n : ℕ) :
    (essentialPart (dgm (ZMod 2) (Cech.filter Triangle.pts) n).points).card =
      (essentialPart (dgm (ZMod 2) (Rips.filter Triangle.metric) n).points).card :=
  essentialPart_card_dgm_eq (ZMod 2) n _ _

/-! ### Certified triangles transported to `ℝ` -/

/-- The filled triangle with its dimension grading cast to `ℝ`. -/
noncomputable def filledReal : FilterFunction FilledTriangle.C.toPre ℝ :=
  FilledTriangle.f.map Nat.castOrderEmbedding

/-- The degree-zero diagram of the transported filled triangle. -/
theorem filledReal_dgm_zero :
    (dgm (ZMod 2) filledReal 0).points =
      {((0 : ℝ), ((1 : ℝ) : WithTop ℝ)), (0, ((1 : ℝ) : WithTop ℝ)), (0, ⊤)} := by
  rw [filledReal, dgm_map, Diagram.map_points, FilledTriangle.actual_diagram_zero]
  simp

/-- The degree-zero module diagram of the transported filled triangle. -/
theorem filledReal_moduleDiagram_zero :
    (moduleDiagram filledReal.criticalValue (sublevelModule (ZMod 2) filledReal 0)
        (sublevelModule_finiteDimensional (ZMod 2) 0 _)).points =
      {((0 : ℝ), ((1 : ℝ) : WithTop ℝ)), (0, ((1 : ℝ) : WithTop ℝ)), (0, ⊤)} := by
  rw [moduleDiagram_sublevelModule, filledReal_dgm_zero]

/-- The degree-one module diagram of the transported filled triangle. -/
theorem filledReal_moduleDiagram_one :
    (moduleDiagram filledReal.criticalValue (sublevelModule (ZMod 2) filledReal 1)
        (sublevelModule_finiteDimensional (ZMod 2) 1 _)).points =
      {((1 : ℝ), ((2 : ℝ) : WithTop ℝ))} := by
  rw [moduleDiagram_sublevelModule, filledReal, dgm_map, Diagram.map_points,
    FilledTriangle.actual_diagram_one]
  simp

/-- The hollow triangle with its dimension grading cast to `ℝ`. -/
noncomputable def hollowReal : FilterFunction HollowTriangle.C.toPre ℝ :=
  HollowTriangle.f.map Nat.castOrderEmbedding

/-- The degree-one module diagram of the transported hollow triangle is one essential class. -/
theorem hollowReal_moduleDiagram_one :
    (moduleDiagram hollowReal.criticalValue (sublevelModule (ZMod 2) hollowReal 1)
        (sublevelModule_finiteDimensional (ZMod 2) 1 _)).points = {((1 : ℝ), ⊤)} := by
  rw [moduleDiagram_sublevelModule, hollowReal, dgm_map, Diagram.map_points,
    HollowTriangle.actual_diagram_one]
  simp

/-! ### One vertex -/

/-- The one-vertex filter has a single critical value. -/
theorem vertex_criticalValues_card (a : ℝ) : (vertexFilter a).criticalValues.card = 1 := by
  have hface : ({0} : Finset (Fin 2)) ∈ singletonFace (0 : Fin 2) :=
    (mem_singletonFace_iff _ _).2 rfl
  change (Finset.univ.image fun _ => a).card = 1
  rw [Finset.image_const ⟨⟨{0}, hface⟩, Finset.mem_univ _⟩, Finset.card_singleton]

/-- The one-vertex module is constructible on its one-value critical grid. -/
theorem vertex_isConstructible (a : ℝ) :
    IsConstructible (vertexFilter a).criticalValue (sublevelModule (ZMod 2) (vertexFilter a) 0) :=
  sublevelModule_isConstructible (ZMod 2) 0 _

/-- The isometry gives the exact interleaving distance of two one-vertex modules. -/
theorem vertex_distance_eq (a b : ℝ) :
    realInterleavingDistance (sublevelModule (ZMod 2) (vertexFilter a) 0)
      (sublevelModule (ZMod 2) (vertexFilter b) 0) = ENNReal.ofReal |a - b| := by
  rw [← bottleneck_dgm_eq_realInterleavingDistance]
  exact vertex_bottleneck_sharp a b

/-- Algebraic stability on one vertex. -/
theorem vertex_algebraic_stability (a b : ℝ) :
    bottleneck (dgm (ZMod 2) (vertexFilter a) 0) (dgm (ZMod 2) (vertexFilter b) 0) ≤
      ENNReal.ofReal (faceSupDifference (vertexFilter a) (vertexFilter b)) :=
  bottleneck_dgm_le_faceSupDifference_algebraic (ZMod 2) 0 _ _

/-- The algebraic bound on one vertex is attained, as in the face-order proof. -/
theorem vertex_algebraic_stability_sharp (a b : ℝ) :
    realInterleavingDistance (sublevelModule (ZMod 2) (vertexFilter a) 0)
      (sublevelModule (ZMod 2) (vertexFilter b) 0) =
        ENNReal.ofReal (faceSupDifference (vertexFilter a) (vertexFilter b)) := by
  rw [← bottleneck_dgm_eq_realInterleavingDistance]
  exact vertex_stability_bound_sharp a b

/-! ### Tied triangle: a zero module -/

/-- The tied filled triangle with its grading cast to `ℝ`. -/
noncomputable def tiedReal : FilterFunction FilledTriangle.C.toPre ℝ :=
  FilledTriangle.tiedFilter.map Nat.castOrderEmbedding

/-- The degree-one diagram of the transported tied triangle is empty. -/
theorem tiedReal_dgm_one : (dgm (ZMod 2) tiedReal 1).points = 0 := by
  rw [tiedReal, dgm_map, Diagram.map_points, FilledTriangle.tied_diagram_one]
  simp

/-- The degree-one tied module is constructible on its critical grid. -/
theorem tiedReal_isConstructible :
    IsConstructible tiedReal.criticalValue (sublevelModule (ZMod 2) tiedReal 1) :=
  sublevelModule_isConstructible (ZMod 2) 1 _

/-- The degree-one tied module is also constructible on the empty grid, since every fiber is
zero: the critical grid is sufficient, not minimal. -/
theorem tiedReal_isConstructible_emptyGrid :
    IsConstructible emptyGrid (sublevelModule (ZMod 2) tiedReal 1) := by
  rw [isConstructible_empty_iff]
  intro t
  change IsZero (simplicialHomology (tiedReal.sublevel t) (ZMod 2) 1)
  have := sublevelHomology_finiteDimensional tiedReal 1 t
  have hfin :
      Module.finrank (ZMod 2) (simplicialHomology (tiedReal.sublevel t) (ZMod 2) 1) = 0 := by
    rw [finrank_sublevelHomology, tiedReal_dgm_one, Multiset.countP_zero]
  have := Module.finrank_zero_iff.1 hfin
  exact ModuleCat.isZero_of_subsingleton _

/-- The degree-one tied module diagram is empty. -/
theorem tiedReal_moduleDiagram_one :
    (moduleDiagram tiedReal.criticalValue (sublevelModule (ZMod 2) tiedReal 1)
        (sublevelModule_finiteDimensional (ZMod 2) 1 _)).points = 0 := by
  rw [moduleDiagram_sublevelModule, tiedReal_dgm_one]

/-! ### Empty complex -/

/-- The empty filter with values cast to `ℝ`. -/
noncomputable def emptyReal : FilterFunction Empty.C.toPre ℝ :=
  Empty.f.map Nat.castOrderEmbedding

/-- The empty filter has an empty critical grid. -/
theorem emptyReal_criticalValues_card : emptyReal.criticalValues.card = 0 := by
  change (Finset.univ.image emptyReal.value).card = 0
  rw [Finset.univ_eq_empty, Finset.image_empty, Finset.card_empty]

/-- The empty sublevel module is constructible on its critical grid. -/
theorem emptyReal_isConstructible (n : ℕ) :
    IsConstructible emptyReal.criticalValue (sublevelModule (ZMod 2) emptyReal n) :=
  sublevelModule_isConstructible (ZMod 2) n _

/-- Both sides of the diagram identity for the empty filter have no points. -/
theorem emptyReal_moduleDiagram (n : ℕ) :
    (moduleDiagram emptyReal.criticalValue (sublevelModule (ZMod 2) emptyReal n)
        (sublevelModule_finiteDimensional (ZMod 2) n _)).points = 0 ∧
      (dgm (ZMod 2) emptyReal n).points = 0 := by
  have h : (dgm (ZMod 2) emptyReal n).points = 0 := by
    rw [emptyReal, dgm_map, Diagram.map_points, Empty.empty_actual_diagram, Multiset.map_zero]
  exact ⟨h, h⟩

/-- The empty sublevel module is constructible on the empty grid, with empty module diagram. -/
theorem emptyReal_emptyGrid (n : ℕ) :
    IsConstructible emptyGrid (sublevelModule (ZMod 2) emptyReal n) ∧
      (moduleDiagram emptyGrid (sublevelModule (ZMod 2) emptyReal n)
        (fun i => Fin.elim0 i)).points = 0 := by
  refine ⟨(isConstructible_empty_iff _ _).2 fun t => ?_, moduleDiagram_empty_grid _ _⟩
  change IsZero (simplicialHomology (emptyReal.sublevel t) (ZMod 2) n)
  rw [emptyReal.sublevel_eq_bot_of_forall_lt t (fun s => isEmptyElim s)]
  exact isZero_simplicialHomology_bot (ZMod 2) n

/-! ### Negative controls -/

/-- The one-point grid one unit above the vertex value. -/
noncomputable def gridAbove (a : ℝ) : Fin 1 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun _ => a + 1) (Subsingleton.strictMono _)

/-- A grid above the first critical value violates the zero left tail: the vertex homology at
the vertex value is `ZMod 2`, not zero. -/
theorem not_isConstructible_gridAbove (a : ℝ) :
    ¬ IsConstructible (gridAbove a) (sublevelModule (ZMod 2) (vertexFilter a) 0) := by
  intro h
  have hz := h.zero_left a (fun _ => by change a < a + 1; linarith)
  change IsZero (simplicialHomology ((vertexFilter a).sublevel a) (ZMod 2) 0) at hz
  rw [(vertexFilter a).sublevel_eq_self_of_forall_le a (fun _ => le_rfl)] at hz
  have := ModuleCat.isZero_iff_subsingleton.1 hz
  have : Subsingleton (ZMod 2) :=
    (simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).toEquiv.symm.subsingleton
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 2) 1)

/-- The one-point grid at `0`, omitting the critical values `1` and `2`. -/
noncomputable def gridZero : Fin 1 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun _ => 0) (Subsingleton.strictMono _)

/-- A grid omitting a critical value violates the within-cell isomorphisms: `0` and `1` lie in
one cell, but the degree-zero fibers there have dimensions `3` and `1`. -/
theorem not_isConstructible_gridZero :
    ¬ IsConstructible gridZero (sublevelModule (ZMod 2) filledReal 0) := by
  intro h
  have hcell : cellIndex gridZero 0 = cellIndex gridZero 1 := by
    have h0 := (lt_cellIndex_iff gridZero 0 0).2 (by change (0 : ℝ) ≤ 0; exact le_rfl)
    have h1 := (lt_cellIndex_iff gridZero 0 1).2 (by change (0 : ℝ) ≤ 1; norm_num)
    have h0' := (cellIndex gridZero 0).isLt
    have h1' := (cellIndex gridZero 1).isLt
    apply Fin.ext
    simp only [Fin.val_zero] at h0 h1
    omega
  have := h.isIso_map 0 1 zero_le_one hcell
  have hdim := (asIso (structureMap (sublevelModule (ZMod 2) filledReal 0)
    (zero_le_one : (0 : ℝ) ≤ 1))).toLinearEquiv.finrank_eq
  change Module.finrank (ZMod 2) (simplicialHomology (filledReal.sublevel 0) (ZMod 2) 0) =
    Module.finrank (ZMod 2) (simplicialHomology (filledReal.sublevel 1) (ZMod 2) 0) at hdim
  rw [finrank_sublevelHomology, finrank_sublevelHomology, filledReal_dgm_zero] at hdim
  simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.countP_cons,
    Multiset.countP_zero] at hdim
  norm_num at hdim

end TDA.Persistence.SublevelConstructibleExamples
