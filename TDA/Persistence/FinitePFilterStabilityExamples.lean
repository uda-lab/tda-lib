import TDA.Persistence.FinitePFilterStability
import TDA.Persistence.Reduction.ActualTriangleDiagrams
import TDA.Persistence.DiagramMap

/-! Cardinality, empty-input and actual-sublevel acceptance fixtures. -/

namespace TDA.Persistence.FinitePFilterStabilityExamples

noncomputable section

open TDA.Filtration TDA.Simplicial

private def emptyDiagram : Diagram ℝ := ⟨0, by simp⟩

private def repeated : Diagram ℝ where
  points := {(0, (2 : WithTop ℝ)), (0, 2)}
  offDiagonal := by norm_num

private def essential : Diagram ℝ where
  points := {(0, ⊤)}
  offDiagonal := by simp

private theorem repeated_finite_part :
    finitePart repeated.points = {((0, 2) : ℝ × ℝ), (0, 2)} := rfl

private theorem repeated_essential_part : essentialPart repeated.points = 0 := rfl

private theorem essential_finite_part : finitePart essential.points = 0 := rfl

private theorem essential_essential_part : essentialPart essential.points = {(0 : ℝ)} := rfl

private theorem repeated_positive : repeated.IsPositive := by
  norm_num [Diagram.IsPositive, repeated]

private theorem repeated_card : Fintype.card repeated.finiteOccurrences = 2 := by
  rw [Multiset.card_coe]
  rw [repeated_finite_part]
  rfl

private theorem empty_card : Fintype.card emptyDiagram.finiteOccurrences = 0 := by
  rw [Multiset.card_coe]
  simp [emptyDiagram, finitePart]

private theorem repeated_coordinates (q : repeated.finiteOccurrences) :
    q.1 = ((0, 2) : ℝ × ℝ) := by
  have h := Multiset.coe_mem (x := q)
  simpa [repeated_finite_part, eq_comm] using h

/-- Every repeated unit-height deletion contributes exactly one powered charge. -/
private theorem repeated_to_empty (p : ℝ) (E : Diagram ℝ)
    (hE : Fintype.card E.finiteOccurrences = 0) :
    finitePBoundaryTransportCost p (fun q : repeated.finiteOccurrences => q.1)
      (fun q : E.finiteOccurrences => q.1) = (2 : ℝ) ^ p⁻¹ := by
  have : IsEmpty E.finiteOccurrences := Fintype.card_eq_zero_iff.mp hE
  rw [finitePBoundaryTransportCost_of_isEmpty_right]
  have hd : (diagonalCost ((0, 2) : ℝ × ℝ)).toReal = 1 := by norm_num [diagonalCost]
  simp only [repeated_coordinates, hd, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    repeated_card, nsmul_eq_mul, Nat.cast_ofNat, mul_one]

private theorem repeated_bottleneck : bottleneck repeated emptyDiagram = 1 := by
  have hz : emptyDiagram = orderedQ 0 0
      ((Fin.elim0 : Fin 0 → ℝ × ℝ), (Fin.elim0 : Fin 0 → ℝ)) := by
    apply Diagram.ext
    simp [emptyDiagram, orderedQ]
  have : Nonempty repeated.finiteOccurrences := Fintype.card_pos_iff.mp (by
    rw [repeated_card]; decide)
  rw [hz, bottleneck_finite_only_empty repeated repeated_essential_part]
  simp only [repeated_coordinates]
  norm_num [diagonalCost]
  exact Finset.sup_const Finset.univ_nonempty 1

private theorem repeated_bound_is_equality (p : ℝ) :
    finitePBoundaryTransportCost p (fun q : repeated.finiteOccurrences => q.1)
        (fun q : emptyDiagram.finiteOccurrences => q.1) =
      (((Fintype.card repeated.finiteOccurrences +
        Fintype.card emptyDiagram.finiteOccurrences : ℕ) : ℝ) ^ p⁻¹) *
        (bottleneck repeated emptyDiagram).toReal := by
  rw [repeated_to_empty p emptyDiagram empty_card, repeated_card, empty_card,
    repeated_bottleneck]
  norm_num

private theorem repeated_squared_cost :
    finitePBoundaryTransportCost 2 (fun q : repeated.finiteOccurrences => q.1)
      (fun q : emptyDiagram.finiteOccurrences => q.1) = Real.sqrt 2 := by
  simpa [Real.sqrt_eq_rpow] using repeated_to_empty 2 emptyDiagram empty_card

private theorem repeated_noninteger_cost :
    finitePBoundaryTransportCost ((3 : ℝ) / 2) (fun q : repeated.finiteOccurrences => q.1)
      (fun q : emptyDiagram.finiteOccurrences => q.1) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
  simpa using repeated_to_empty ((3 : ℝ) / 2) emptyDiagram empty_card

/-- The occurrence-count factor cannot be dropped, even for two positive bars. -/
private theorem repeated_not_bounded_by_bottleneck :
    ¬ finitePBoundaryTransportCost 2 (fun q : repeated.finiteOccurrences => q.1)
        (fun q : emptyDiagram.finiteOccurrences => q.1) ≤
      (bottleneck repeated emptyDiagram).toReal := by
  rw [repeated_to_empty 2 emptyDiagram empty_card, repeated_bottleneck]
  norm_num only [ENNReal.toReal_one]
  exact not_le_of_gt (Real.one_lt_rpow (by norm_num) (by norm_num))

private theorem empty_budget {p : ℝ} (hp : 1 ≤ p) :
    finitePBoundaryTransportCost p (fun q : emptyDiagram.finiteOccurrences => q.1)
        (fun q : emptyDiagram.finiteOccurrences => q.1) ≤ 0 := by
  have hcard : Fintype.card emptyDiagram.finiteOccurrences +
      Fintype.card emptyDiagram.finiteOccurrences ≤ 0 := by norm_num only [empty_card]
  simpa using finitePBoundaryTransportCost_le_cardBound_rpow_mul_of_bottleneck_le
    hp emptyDiagram emptyDiagram hcard (r := 0) (le_refl 0) (by simp [bottleneck_self])

private theorem first_order_recovery (D E : Diagram ℝ) (hfinite : bottleneck D E < ⊤) :
    finiteFirstOrderMatchingCost (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) ≤
      ((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) *
        (bottleneck D E).toReal := by
  simpa using finitePMatchingCost_le_card_rpow_mul_bottleneck (p := 1) (le_refl 1)
    D E hfinite

private theorem essential_mismatch_top : bottleneck repeated essential = ⊤ := by
  by_contra h
  have hc := (bottleneck_lt_top_iff repeated essential).mp (lt_top_iff_ne_top.mpr h)
  rw [repeated_essential_part, essential_essential_part] at hc
  norm_num at hc

/-- Converting an infinite bottleneck to real would give a false zero upper bound. -/
private theorem essential_mismatch_invalid_real_bound :
    ¬ finitePBoundaryTransportCost 1 (fun q : repeated.finiteOccurrences => q.1)
        (fun q : essential.finiteOccurrences => q.1) ≤
      (((Fintype.card repeated.finiteOccurrences +
        Fintype.card essential.finiteOccurrences : ℕ) : ℝ) ^ (1 : ℝ)⁻¹) *
        (bottleneck repeated essential).toReal := by
  have hc : Fintype.card essential.finiteOccurrences = 0 := by
    rw [Multiset.card_coe]
    rw [essential_finite_part]
    rfl
  rw [repeated_to_empty 1 essential hc, essential_mismatch_top]
  norm_num

private def triangleFilter : FilterFunction Reduction.Examples.FilledTriangle.C.toPre ℝ :=
  Reduction.Examples.FilledTriangle.f.map Nat.castOrderEmbedding

private def tiedTriangleFilter : FilterFunction Reduction.Examples.FilledTriangle.C.toPre ℝ :=
  Reduction.Examples.FilledTriangle.tiedFilter.map Nat.castOrderEmbedding

/-- An actual positive finite H₁ bar disappears when the final grades tie. -/
private theorem triangle_finite_parts :
    finitePart (dgm (ZMod 2) triangleFilter 1).points = {(1, 2)} ∧
      finitePart (dgm (ZMod 2) tiedTriangleFilter 1).points = 0 := by
  constructor
  · rw [triangleFilter, dgm_map, finitePart_map_points,
      Reduction.Examples.FilledTriangle.actual_diagram_one]
    change Multiset.map (fun q : ℕ × ℕ => ((q.1 : ℝ), (q.2 : ℝ))) {(1, 2)} = _
    norm_num
  · rw [tiedTriangleFilter, dgm_map, finitePart_map_points,
      Reduction.Examples.FilledTriangle.tied_diagram_one]
    simp [finitePart]

private theorem triangle_card_budget :
    Fintype.card (dgm (ZMod 2) triangleFilter 1).finiteOccurrences +
      Fintype.card (dgm (ZMod 2) tiedTriangleFilter 1).finiteOccurrences = 1 := by
  simp only [Diagram.finiteOccurrences, Multiset.card_coe, triangle_finite_parts.1,
    triangle_finite_parts.2]
  rfl

private theorem triangle_face_perturbation : faceSupDifference triangleFilter tiedTriangleFilter ≤ 1 := by
  classical
  unfold faceSupDifference
  apply (Finset.fold_max_le (1 : ℝ)).mpr
  refine ⟨by norm_num, ?_⟩
  intro σ _
  have hc : σ.1.card ≤ 3 := (Finset.card_le_univ σ.1).trans_eq (by decide)
  have hd : σ.1.card - 1 ≤ 2 := by omega
  change |((σ.1.card - 1 : ℕ) : ℝ) - ((min (σ.1.card - 1) 1 : ℕ) : ℝ)| ≤ 1
  generalize σ.1.card - 1 = a at hd ⊢
  interval_cases a <;> norm_num

private theorem actual_triangle_bound {p : ℝ} (hp : 1 ≤ p) :
    finitePBoundaryTransportCost p (fun q : (dgm (ZMod 2) triangleFilter 1).finiteOccurrences => q.1)
      (fun q : (dgm (ZMod 2) tiedTriangleFilter 1).finiteOccurrences => q.1) ≤ 1 := by
  have hc : Fintype.card (dgm (ZMod 2) triangleFilter 1).finiteOccurrences +
      Fintype.card (dgm (ZMod 2) tiedTriangleFilter 1).finiteOccurrences ≤ 1 :=
    triangle_card_budget.le
  have h := finitePBoundaryTransportCost_dgm_le_cardBound_rpow_mul_faceSupDifference hp
    (ZMod 2) triangleFilter tiedTriangleFilter 1 hc
  have h' : finitePBoundaryTransportCost p
      (fun q : (dgm (ZMod 2) triangleFilter 1).finiteOccurrences => q.1)
      (fun q : (dgm (ZMod 2) tiedTriangleFilter 1).finiteOccurrences => q.1) ≤
      faceSupDifference triangleFilter tiedTriangleFilter := by simpa using h
  exact h'.trans triangle_face_perturbation

private theorem actual_triangle_squared :
    finitePBoundaryTransportCost 2 (fun q : (dgm (ZMod 2) triangleFilter 1).finiteOccurrences => q.1)
      (fun q : (dgm (ZMod 2) tiedTriangleFilter 1).finiteOccurrences => q.1) ≤ 1 :=
  actual_triangle_bound (by norm_num)

private theorem actual_triangle_noninteger :
    finitePBoundaryTransportCost ((3 : ℝ) / 2)
      (fun q : (dgm (ZMod 2) triangleFilter 1).finiteOccurrences => q.1)
      (fun q : (dgm (ZMod 2) tiedTriangleFilter 1).finiteOccurrences => q.1) ≤ 1 :=
  actual_triangle_bound (by norm_num)

end

end TDA.Persistence.FinitePFilterStabilityExamples
