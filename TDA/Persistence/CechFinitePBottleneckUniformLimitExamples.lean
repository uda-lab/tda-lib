import TDA.Persistence.CechFinitePBottleneckUniformLimit
import TDA.Persistence.TriangleCechRipsExamples
import TDA.Persistence.TotalPersistenceRipsCechExamples
import TDA.Persistence.FinitePBoundaryTransportLaws

/-!
# Actual Čech diagrams in a displacement-budget class

The acute triangle has a positive degree-one bar, whereas the right triangle's
degree-one diagram is empty. Both optimized rooted costs equal their positive
bottleneck distance for every p ≥ 1. The error is zero in this example; it is
not a sharp multiplicity or convergence-rate fixture.

The self pair tests zero radius with a nonempty diagram. Empty and repeated
labels test the domain without replacing the nonzero example.
-/

noncomputable section

universe u w

open scoped Classical Topology ENNReal

namespace TDA.Persistence.CechFinitePBottleneckUniformLimitExamples

open TDA.Filtration TDA.Filtration.Cech.Examples TriangleCechRipsExamples Filter

private abbrev matching (p : ℝ) (D E : Diagram ℝ) : ℝ :=
  finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
    (fun q : E.finiteOccurrences => q.1)

private abbrev transport (p : ℝ) (D E : Diagram ℝ) : ℝ :=
  finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
    (fun q : E.finiteOccurrences => q.1)

private abbrev uniformLimits {V : Type u} [LinearOrder V] [Fintype V]
    {X : Type w} [PseudoMetricSpace X] (k : Type u) [Field k] (n : ℕ) (R : ℝ) : Prop :=
  TendstoUniformlyOn
    (fun p : ℝ => fun z : (V → X) × (V → X) =>
      matching p (dgm k (Cech.filter z.1) n) (dgm k (Cech.filter z.2) n))
    (fun z => (bottleneck (dgm k (Cech.filter z.1) n) (dgm k (Cech.filter z.2) n)).toReal)
    atTop {z : (V → X) × (V → X) | Cech.displacement z.1 z.2 ≤ R} ∧
  TendstoUniformlyOn
    (fun p : ℝ => fun z : (V → X) × (V → X) =>
      transport p (dgm k (Cech.filter z.1) n) (dgm k (Cech.filter z.2) n))
    (fun z => (bottleneck (dgm k (Cech.filter z.1) n) (dgm k (Cech.filter z.2) n)).toReal)
    atTop {z : (V → X) × (V → X) | Cech.displacement z.1 z.2 ≤ R}

private theorem uniform_limits {V : Type u} [LinearOrder V] [Fintype V]
    {X : Type w} [PseudoMetricSpace X] (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n)
    {R : ℝ} (hR : 0 ≤ R) : uniformLimits (V := V) (X := X) k n R :=
  ⟨Cech.finitePMatchingCost_dgm_tendstoUniformlyOn_bottleneck k n hn R hR,
    Cech.finitePBoundaryTransportCost_dgm_tendstoUniformlyOn_bottleneck k n hn R hR⟩

private abbrev errorBounds {V : Type u} [LinearOrder V] [Fintype V]
    {X : Type w} [PseudoMetricSpace X] (p : ℝ) (k : Type u) [Field k]
    (a b : V → X) (n : ℕ) (R : ℝ) : Prop :=
  |matching p (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n) -
      (bottleneck (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n)).toReal| ≤
    ((((max 1 (2 * Nat.choose (Fintype.card V) (n + 2)) : ℕ) : ℝ) ^ p⁻¹) - 1) * R ∧
  |transport p (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n) -
      (bottleneck (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n)).toReal| ≤
    ((((max 1 (2 * Nat.choose (Fintype.card V) (n + 2)) : ℕ) : ℝ) ^ p⁻¹) - 1) * R

private theorem error_bounds {V : Type u} [LinearOrder V] [Fintype V]
    {X : Type w} [PseudoMetricSpace X] {p : ℝ} (hp : 1 ≤ p) (k : Type u) [Field k]
    (a b : V → X) {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R)
    (hδ : Cech.displacement a b ≤ R) : errorBounds p k a b n R :=
  ⟨Cech.finitePMatchingCost_dgm_abs_sub_bottleneck_le_uniformBound hp k a b hn hR hδ,
    Cech.finitePBoundaryTransportCost_dgm_abs_sub_bottleneck_le_uniformBound hp k a b hn hR hδ⟩

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private abbrev acute : Fin 3 → Plane := Triangle.pts
private abbrev right : Fin 3 → Plane := RightTriangle.pts
private abbrev acuteDiagram : Diagram ℝ := dgm (ZMod 2) (Cech.filter acute) 1
private abbrev rightDiagram : Diagram ℝ := dgm (ZMod 2) (Cech.filter right) 1
private abbrev radius : ℝ := (5 / 4 - Real.sqrt 5 / 2) / 2

private theorem radius_pos : 0 < radius := by
  have h := sqrt_five_bounds.2.1
  dsimp only [radius]
  linarith

private theorem acute_points :
    acuteDiagram.points = {((Real.sqrt 5 / 2 : ℝ), ((5 / 4 : ℝ) : WithTop ℝ))} :=
  triangle_cech_dgm_one

private theorem right_points : rightDiagram.points = 0 := RightTriangle.rightTriangle_cech_dgm_one

private theorem acute_finitePart :
    finitePart acuteDiagram.points = {((Real.sqrt 5 / 2, 5 / 4) : ℝ × ℝ)} := by
  rw [acute_points]
  rfl

private theorem right_finitePart : finitePart rightDiagram.points = 0 := by
  rw [right_points]
  rfl

private theorem acute_card : Fintype.card acuteDiagram.finiteOccurrences = 1 := by
  simp only [Multiset.card_coe, acute_finitePart, Multiset.card_singleton]

private theorem right_card : Fintype.card rightDiagram.finiteOccurrences = 0 := by
  simp only [Multiset.card_coe, right_finitePart, Multiset.card_zero]

private instance right_occurrences : IsEmpty rightDiagram.finiteOccurrences :=
  Fintype.card_eq_zero_iff.mp right_card

private theorem acute_coordinates (q : acuteDiagram.finiteOccurrences) :
    q.1 = ((Real.sqrt 5 / 2, 5 / 4) : ℝ × ℝ) :=
  Multiset.mem_singleton.mp
    (by simpa only [acute_finitePart] using (Multiset.coe_mem (x := q)))

/-- Both clouds are actual certified reducer-to-diagram computations. -/
private theorem actual_diagram_counts :
    Fintype.card acuteDiagram.finiteOccurrences = 1 ∧
    Fintype.card rightDiagram.finiteOccurrences = 0 ∧
    2 * Nat.choose (Fintype.card (Fin 3)) (1 + 2) = 2 := by
  exact ⟨acute_card, right_card, by norm_num [Nat.choose]⟩

private theorem label_distances (v : Fin 3) :
    dist (acute v) (right v) = if v = 2 then 1 else 0 := by
  fin_cases v
  · norm_num [acute, right]; decide
  · norm_num [acute, right]; decide
  · change dist (acute 2) (right 2) = 1
    calc
      dist (acute 2) (right 2) = √(dist (acute 2) (right 2) ^ 2) :=
        (Real.sqrt_sq dist_nonneg).symm
      _ = 1 := by
        rw [Triangle.dist_sq]
        norm_num [acute, right]

private theorem acute_right_displacement : Cech.displacement acute right = 1 := by
  apply le_antisymm
  · apply (Cech.displacement_le_iff acute right 1).2
    refine ⟨by norm_num, fun v => ?_⟩
    rw [label_distances]
    split <;> norm_num
  · calc
      1 = dist (acute 2) (right 2) := by rw [label_distances]; norm_num
      _ ≤ Cech.displacement acute right := Cech.dist_le_displacement acute right 2

private theorem acute_diagonal :
    diagonalCost ((Real.sqrt 5 / 2, 5 / 4) : ℝ × ℝ) = ENNReal.ofReal radius := by
  have h : 0 < (5 / 4 : ℝ) - Real.sqrt 5 / 2 := by linarith [sqrt_five_bounds.2.1]
  dsimp only [diagonalCost, radius]
  rw [abs_of_pos h]

private theorem right_eq_empty_rips : rightDiagram = dgm (ZMod 2) ripsT 1 := by
  apply Diagram.ext
  rw [right_points, triangle_rips_dgm_one]

private theorem acute_right_bottleneck :
    bottleneck acuteDiagram rightDiagram = ENNReal.ofReal radius := by
  rw [right_eq_empty_rips, bottleneck_comm]
  exact triangle_bottleneck_one

/-- Reindex the actual canonical occurrences, retaining their certified values. -/
private theorem acute_right_matching_reindex (p : ℝ) :
    matching p acuteDiagram rightDiagram =
      finitePMatchingCost p (fun _ : Fin 1 => ((Real.sqrt 5 / 2, 5 / 4) : ℝ × ℝ))
        (Fin.elim0 : Fin 0 → ℝ × ℝ) := by
  let u := (Fintype.equivFinOfCardEq acute_card).symm
  let v := (Fintype.equivFinOfCardEq right_card).symm
  have hx : (fun q : acuteDiagram.finiteOccurrences => q.1) ∘ u =
      fun _ : Fin 1 => ((Real.sqrt 5 / 2, 5 / 4) : ℝ × ℝ) := by
    funext i
    exact acute_coordinates _
  have hy : (fun q : rightDiagram.finiteOccurrences => q.1) ∘ v =
      (Fin.elim0 : Fin 0 → ℝ × ℝ) := by
    funext i
    exact Fin.elim0 i
  simpa only [hx, hy] using
    (finitePMatchingCost_reindex u v p (fun q : acuteDiagram.finiteOccurrences => q.1)
      (fun q : rightDiagram.finiteOccurrences => q.1)).symm

private theorem acute_right_matching {p : ℝ} (hp : 1 ≤ p) :
    matching p acuteDiagram rightDiagram = radius := by
  rw [acute_right_matching_reindex, finitePMatchingCost_of_isEmpty_right]
  simp only [acute_diagonal, ENNReal.toReal_ofReal radius_pos.le, Fin.sum_univ_one]
  exact Real.rpow_rpow_inv radius_pos.le (ne_of_gt (lt_of_lt_of_le zero_lt_one hp))

/-- A positive full bottleneck and both actual optimized costs, for every real p ≥ 1. -/
private theorem acute_right_actual_costs {p : ℝ} (hp : 1 ≤ p) :
    0 < radius ∧ bottleneck acuteDiagram rightDiagram = ENNReal.ofReal radius ∧
    matching p acuteDiagram rightDiagram = radius ∧
    transport p acuteDiagram rightDiagram = radius := by
  refine ⟨radius_pos, acute_right_bottleneck, acute_right_matching hp, ?_⟩
  rw [transport, finitePBoundaryTransportCost_eq_matchingCost]
  exact acute_right_matching hp

/-- This nonempty displacement class exercises both uniform capstones. -/
private theorem acute_right_budget_and_uniform :
    (acute, right) ∈ {z : (Fin 3 → Plane) × (Fin 3 → Plane) |
      Cech.displacement z.1 z.2 ≤ 1} ∧
    uniformLimits (V := Fin 3) (X := Plane) (ZMod 2) 1 1 := by
  exact ⟨by change Cech.displacement acute right ≤ 1; exact acute_right_displacement.le,
    uniform_limits (ZMod 2) 1 (le_refl 1) (by norm_num)⟩

/-- The four concrete error instances include a nonintegral real exponent. -/
private theorem acute_right_error_examples :
    errorBounds 2 (ZMod 2) acute right 1 1 ∧
    errorBounds (3 / 2) (ZMod 2) acute right 1 1 := by
  have hδ : Cech.displacement acute right ≤ 1 := acute_right_displacement.le
  exact ⟨error_bounds (by norm_num) (ZMod 2) acute right (le_refl 1) (by norm_num) hδ,
    error_bounds (by norm_num) (ZMod 2) acute right (le_refl 1) (by norm_num) hδ⟩

/-- The nonzero example has exact error zero; no sharp rate is claimed from it. -/
private theorem acute_right_errors_zero {p : ℝ} (hp : 1 ≤ p) :
    |matching p acuteDiagram rightDiagram - (bottleneck acuteDiagram rightDiagram).toReal| = 0 ∧
    |transport p acuteDiagram rightDiagram - (bottleneck acuteDiagram rightDiagram).toReal| = 0 := by
  rcases acute_right_actual_costs hp with ⟨hr, hB, hm, ht⟩
  simp only [hB, hm, ht, ENNReal.toReal_ofReal hr.le, sub_self, abs_zero, and_self]

/-- Zero displacement is tested on the retained positive triangle bar. -/
private theorem nonempty_zero_radius {p : ℝ} (hp : 1 ≤ p) :
    Fintype.card acuteDiagram.finiteOccurrences = 1 ∧
    (acute, acute) ∈ {z : (Fin 3 → Plane) × (Fin 3 → Plane) |
      Cech.displacement z.1 z.2 ≤ 0} ∧ bottleneck acuteDiagram acuteDiagram = 0 ∧
    matching p acuteDiagram acuteDiagram = 0 ∧ transport p acuteDiagram acuteDiagram = 0 ∧
    errorBounds p (ZMod 2) acute acute 1 0 ∧
    uniformLimits (V := Fin 3) (X := Plane) (ZMod 2) 1 0 := by
  refine ⟨acute_card, by simp, bottleneck_self _, finitePMatchingCost_self hp _,
    finitePBoundaryTransportCost_self hp _, ?_, uniform_limits (ZMod 2) 1 (le_refl 1) le_rfl⟩
  exact error_bounds hp (ZMod 2) acute acute (le_refl 1) le_rfl (by simp)

private theorem diagram_points_zero_of_parts (D : Diagram ℝ)
    (hf : finitePart D.points = 0) (he : essentialPart D.points = 0) : D.points = 0 := by
  have h := parts_reconstruct D.points
  simpa only [hf, he, Multiset.map_zero, zero_add] using h.symm

/-- Empty labels require no chosen ambient point, even when the ambient type is empty. -/
private theorem empty_actual_diagram {X : Type w} [PseudoMetricSpace X]
    (a : Fin 0 → X) (n : ℕ) : (dgm (ZMod 2) (Cech.filter a) n).points = 0 := by
  let : IsEmpty (TDA.Simplicial.TotalFace (Rips.fullComplex (Fin 0))) :=
    ⟨fun s => by obtain ⟨v, _⟩ := s.property; exact Fin.elim0 v⟩
  exact dgm_empty_faces (ZMod 2) (Cech.filter a) n

private theorem empty_label_controls {X : Type w} [PseudoMetricSpace X]
    (a b : Fin 0 → X) {p : ℝ} (hp : 1 ≤ p) :
    (a, b) ∈ {z : (Fin 0 → X) × (Fin 0 → X) | Cech.displacement z.1 z.2 ≤ 0} ∧
    Fintype.card (dgm (ZMod 2) (Cech.filter a) 1).finiteOccurrences = 0 ∧
    bottleneck (dgm (ZMod 2) (Cech.filter a) 1) (dgm (ZMod 2) (Cech.filter b) 1) = 0 ∧
    matching p (dgm (ZMod 2) (Cech.filter a) 1) (dgm (ZMod 2) (Cech.filter b) 1) = 0 ∧
    transport p (dgm (ZMod 2) (Cech.filter a) 1) (dgm (ZMod 2) (Cech.filter b) 1) = 0 ∧
    2 * Nat.choose (Fintype.card (Fin 0)) (1 + 2) = 0 ∧
    max 1 (2 * Nat.choose (Fintype.card (Fin 0)) (1 + 2)) = 1 ∧
    errorBounds p (ZMod 2) a b 1 0 ∧
    uniformLimits (V := Fin 0) (X := X) (ZMod 2) 1 0 := by
  have hc (c : Fin 0 → X) :
      Fintype.card (dgm (ZMod 2) (Cech.filter c) 1).finiteOccurrences = 0 := by
    rw [Multiset.card_coe, empty_actual_diagram c 1]
    rfl
  let : IsEmpty (dgm (ZMod 2) (Cech.filter a) 1).finiteOccurrences :=
    Fintype.card_eq_zero_iff.mp (hc a)
  let : IsEmpty (dgm (ZMod 2) (Cech.filter b) 1).finiteOccurrences :=
    Fintype.card_eq_zero_iff.mp (hc b)
  have heq : dgm (ZMod 2) (Cech.filter a) 1 = dgm (ZMod 2) (Cech.filter b) 1 := by
    apply Diagram.ext
    rw [empty_actual_diagram a 1, empty_actual_diagram b 1]
  refine ⟨by simp, hc a, ?_, finitePMatchingCost_empty hp _ _,
    finitePBoundaryTransportCost_empty hp _ _, by norm_num [Nat.choose],
    by norm_num [Nat.choose], ?_,
    uniform_limits (ZMod 2) 1 (le_refl 1) le_rfl⟩
  · rw [heq]
    exact bottleneck_self _
  · exact error_bounds hp (ZMod 2) a b (le_refl 1) le_rfl (by simp)

private abbrev repeatedDiagram : Diagram ℝ := dgm (ZMod 2) (Cech.filter Repeated.pts) 1

private theorem repeated_points : repeatedDiagram.points = 0 := by
  exact diagram_points_zero_of_parts _
    (TotalPersistenceRipsCechExamples.repeated_cech_finitePart_eq_zero 1)
    (Cech.essentialPart_dgm_eq_zero (ZMod 2) Repeated.pts (le_refl 1))

/-- Repeated labels remain in the input class without any compatible label metric. -/
private theorem repeated_label_controls {p : ℝ} (hp : 1 ≤ p) :
    ¬Function.Injective Repeated.pts ∧ repeatedDiagram.points = 0 ∧
    (Repeated.pts, Repeated.pts) ∈ {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) |
      Cech.displacement z.1 z.2 ≤ 0} ∧
    matching p repeatedDiagram repeatedDiagram = 0 ∧
    transport p repeatedDiagram repeatedDiagram = 0 ∧
    errorBounds p (ZMod 2) Repeated.pts Repeated.pts 1 0 ∧
    uniformLimits (V := Fin 2) (X := ℝ) (ZMod 2) 1 0 := by
  refine ⟨?_, repeated_points, by simp, finitePMatchingCost_self hp _,
    finitePBoundaryTransportCost_self hp _, ?_,
    uniform_limits (ZMod 2) 1 (le_refl 1) le_rfl⟩
  · intro h
    have he : (0 : Fin 2) = 1 := h (by rfl)
    exact (by decide : (0 : Fin 2) ≠ 1) he
  · exact error_bounds hp (ZMod 2) Repeated.pts Repeated.pts (le_refl 1) le_rfl (by simp)

end TDA.Persistence.CechFinitePBottleneckUniformLimitExamples
