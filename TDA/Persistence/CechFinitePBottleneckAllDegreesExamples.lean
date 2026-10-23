import TDA.Persistence.CechFinitePBottleneckAllDegrees
import TDA.Persistence.CechFinitePBottleneckUniformLimitExamples
import TDA.Persistence.CechSupNormDiagramExamples
import TDA.Persistence.TriangleCechRipsExamples
import TDA.Persistence.DiagramBottleneckTranslation
import TDA.Persistence.LogScaleScaling
import TDA.Persistence.LogScaleDiagramComparisonExamples
import TDA.Persistence.FinitePBoundaryTransportExamples
import TDA.Persistence.FinitePBottleneckLimitExamples

/-!
# All-degree Čech recovery examples
-/

noncomputable section

universe u w

open scoped Classical Topology ENNReal

namespace TDA.Persistence.CechFinitePBottleneckAllDegreesExamples

open TDA.Filtration TDA.Simplicial Filter
open TDA.Persistence.Reduction TDA.Persistence.FiniteConstructible

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
    {X : Type w} [PseudoMetricSpace X] (k : Type u) [Field k] (n : ℕ)
    {R : ℝ} (hR : 0 ≤ R) : uniformLimits (V := V) (X := X) k n R :=
  ⟨Cech.finitePMatchingCost_dgm_tendstoUniformlyOn_bottleneck_allDegrees k n R hR,
    Cech.finitePBoundaryTransportCost_dgm_tendstoUniformlyOn_bottleneck_allDegrees k n R hR⟩

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
    (a b : V → X) (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hδ : Cech.displacement a b ≤ R) : errorBounds p k a b n R :=
  ⟨Cech.finitePMatchingCost_dgm_abs_sub_bottleneck_le_uniformBound_allDegrees hp k a b n hR hδ,
    Cech.finitePBoundaryTransportCost_dgm_abs_sub_bottleneck_le_uniformBound_allDegrees
      hp k a b n hR hδ⟩

private theorem card_of_empty_finitePart (D : Diagram ℝ) (h : finitePart D.points = 0) :
    Fintype.card D.finiteOccurrences = 0 := by
  simp only [Multiset.card_coe, h, Multiset.card_zero]

/-- Presentations label occurrences, so this also retains repeated values. -/
private def finiteEnum {I : Type*} [Fintype I] (D : Diagram ℝ) (x : I → ℝ × ℝ)
    (hx : Finset.univ.val.map x = finitePart D.points) :
    {e : I ≃ D.finiteOccurrences // ∀ i, (e i).1 = x i} := by
  classical
  exact presentationEquiv x (fun q : D.finiteOccurrences => q.1)
    (hx.trans (Multiset.map_univ_coe _).symm)

private theorem matching_presentation {I J : Type*} [Fintype I] [Fintype J]
    (D E : Diagram ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : Finset.univ.val.map x = finitePart D.points)
    (hy : Finset.univ.val.map y = finitePart E.points) (p : ℝ) :
    matching p D E = finitePMatchingCost p x y := by
  let u := finiteEnum D x hx
  let v := finiteEnum E y hy
  have hu : (fun q : D.finiteOccurrences => q.1) ∘ u.1 = x := funext u.2
  have hv : (fun q : E.finiteOccurrences => q.1) ∘ v.1 = y := funext v.2
  simpa only [hu, hv] using (finitePMatchingCost_reindex u.1 v.1 p
    (fun q : D.finiteOccurrences => q.1) (fun q : E.finiteOccurrences => q.1)).symm

private theorem constant_value {V X : Type*} [PseudoMetricSpace X]
    (x : X) (s : TotalFace (Rips.fullComplex V)) :
    (Cech.filter (fun _ : V => x)).value s = 0 := by
  apply le_antisymm _ (Cech.filter_value_nonneg _ _)
  exact (Cech.filter_value_le_radiusAt _ s x).trans
    ((Cech.radiusAt_le_iff _ x s.val 0).mpr ⟨le_rfl, by simp⟩)

private theorem constant_finitePart {V : Type u} [LinearOrder V] [Fintype V]
    {X : Type w} [PseudoMetricSpace X] (k : Type u) [Field k] (x : X) (n : ℕ) :
    finitePart (dgm k (Cech.filter (fun _ : V => x)) n).points = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro q hq
  have h := dgm_finitePart_mem_Icc k n
    (fun s => (constant_value x s).ge) (fun s => (constant_value x s).le) q hq
  linarith [h.1, h.2.1, h.2.2]

/-! ### Singleton H₀, arbitrary fields and zero input budgets -/

private theorem singleton_finitePart {X : Type w} [PseudoMetricSpace X]
    (k : Type) [Field k] (a : Fin 1 → X) :
    finitePart (dgm k (Cech.filter a) 0).points = 0 := by
  have h := card_finiteOccurrences_dgm_fullComplex_le k (Cech.filter a) 0
  have hc : Fintype.card (dgm k (Cech.filter a) 0).finiteOccurrences = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa using h
  apply Multiset.card_eq_zero.mp
  simpa only [Multiset.card_coe] using hc

private theorem singleton_points {X : Type w} [PseudoMetricSpace X]
    (k : Type) [Field k] (a : Fin 1 → X) :
    (dgm k (Cech.filter a) 0).points = {((0 : ℝ), (⊤ : WithTop ℝ))} := by
  have h := parts_reconstruct (dgm k (Cech.filter a) 0).points
  simpa only [singleton_finitePart k a, Cech.essentialPart_dgm_zero_eq_singleton k a,
    Multiset.map_zero, Multiset.map_singleton, zero_add] using h.symm

private theorem singleton_costs {X : Type w} [PseudoMetricSpace X]
    (k : Type) [Field k] (a b : Fin 1 → X) {p : ℝ} (hp : 1 ≤ p) :
    essentialPart (dgm k (Cech.filter a) 0).points = ({0} : Multiset ℝ) ∧
    Fintype.card (dgm k (Cech.filter a) 0).finiteOccurrences = 0 ∧
    bottleneck (dgm k (Cech.filter a) 0) (dgm k (Cech.filter b) 0) = 0 ∧
    matching p (dgm k (Cech.filter a) 0) (dgm k (Cech.filter b) 0) = 0 ∧
    transport p (dgm k (Cech.filter a) 0) (dgm k (Cech.filter b) 0) = 0 := by
  have ha := card_of_empty_finitePart _ (singleton_finitePart k a)
  have hb := card_of_empty_finitePart _ (singleton_finitePart k b)
  letI := Fintype.card_eq_zero_iff.mp ha
  letI := Fintype.card_eq_zero_iff.mp hb
  have he : dgm k (Cech.filter a) 0 = dgm k (Cech.filter b) 0 := by
    apply Diagram.ext
    rw [singleton_points k a, singleton_points k b]
  refine ⟨Cech.essentialPart_dgm_zero_eq_singleton k a, ha, ?_,
    finitePMatchingCost_empty hp _ _, finitePBoundaryTransportCost_empty hp _ _⟩
  rw [he]
  exact bottleneck_self _

private def oneCloud (x : ℝ) : Fin 1 → ℝ := fun _ => x

private theorem singleton_displacement (x y : ℝ) :
    Cech.displacement (oneCloud x) (oneCloud y) = |x - y| := by
  apply le_antisymm
  · exact (Cech.displacement_le_iff _ _ _).mpr ⟨abs_nonneg _, fun _ => by
      simp only [oneCloud, Real.dist_eq]; exact le_rfl⟩
  · simpa only [oneCloud, Real.dist_eq] using
      Cech.dist_le_displacement (oneCloud x) (oneCloud y) 0

private theorem singleton_zero_budget (k : Type) [Field k] (x : ℝ)
    {p : ℝ} (hp : 1 ≤ p) :
    Cech.displacement (oneCloud x) (oneCloud x) = 0 ∧
    2 * Nat.choose (Fintype.card (Fin 1)) (0 + 2) = 0 ∧
    errorBounds p k (oneCloud x) (oneCloud x) 0 0 ∧
    uniformLimits (V := Fin 1) (X := ℝ) k 0 0 := by
  exact ⟨by simp, by norm_num [Nat.choose],
    error_bounds hp k _ _ 0 le_rfl (by simp), uniform_limits k 0 le_rfl⟩

/-- Moving a lone point gives a finite displacement budget, although its
ordinary H₀ diagram remains the same essential singleton. -/
private theorem singleton_moving_budget (k : Type) [Field k] (x y : ℝ)
    {p : ℝ} (hp : 1 ≤ p) :
    (oneCloud x, oneCloud y) ∈ {z : (Fin 1 → ℝ) × (Fin 1 → ℝ) |
      Cech.displacement z.1 z.2 ≤ |x-y|} ∧
    errorBounds p k (oneCloud x) (oneCloud y) 0 |x-y| ∧
    uniformLimits (V := Fin 1) (X := ℝ) k 0 |x-y| := by
  exact ⟨(singleton_displacement x y).le,
    error_bounds hp k _ _ 0 (abs_nonneg _) (singleton_displacement x y).le,
    uniform_limits k 0 (abs_nonneg _)⟩

/-! ### Empty labels, including an empty ambient space -/

private theorem empty_diagram {X : Type w} [PseudoMetricSpace X]
    (k : Type) [Field k] (a : Fin 0 → X) (n : ℕ) :
    (dgm k (Cech.filter a) n).points = 0 := by
  letI : IsEmpty (TotalFace (Rips.fullComplex (Fin 0))) :=
    ⟨fun s => by obtain ⟨v, _⟩ := s.property; exact Fin.elim0 v⟩
  exact dgm_empty_faces k (Cech.filter a) n

private theorem empty_costs {X : Type w} [PseudoMetricSpace X]
    (k : Type) [Field k] (a b : Fin 0 → X) (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    finitePart (dgm k (Cech.filter a) n).points = 0 ∧
    essentialPart (dgm k (Cech.filter a) n).points = 0 ∧
    Fintype.card (dgm k (Cech.filter a) n).finiteOccurrences = 0 ∧
    Cech.displacement a b = 0 ∧
    bottleneck (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n) = 0 ∧
    matching p (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n) = 0 ∧
    transport p (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n) = 0 ∧
    errorBounds p k a b n 0 ∧ uniformLimits (V := Fin 0) (X := X) k n 0 := by
  have hf (c : Fin 0 → X) : finitePart (dgm k (Cech.filter c) n).points = 0 := by
    rw [empty_diagram k c n]
    rfl
  have he : essentialPart (dgm k (Cech.filter a) n).points = 0 := by
    rw [empty_diagram k a n]
    rfl
  have ha := card_of_empty_finitePart _ (hf a)
  have hb := card_of_empty_finitePart _ (hf b)
  letI := Fintype.card_eq_zero_iff.mp ha
  letI := Fintype.card_eq_zero_iff.mp hb
  have heq : dgm k (Cech.filter a) n = dgm k (Cech.filter b) n := by
    apply Diagram.ext
    rw [empty_diagram k a n, empty_diagram k b n]
  refine ⟨hf a, he, ha, by simp, ?_, finitePMatchingCost_empty hp _ _,
    finitePBoundaryTransportCost_empty hp _ _,
    error_bounds hp k a b n le_rfl (by simp), uniform_limits k n le_rfl⟩
  rw [heq]
  exact bottleneck_self _

private instance emptyAmbient : PseudoMetricSpace Empty :=
  PseudoMetricSpace.induced (Empty.elim : Empty → ℝ) inferInstance

private theorem empty_ambient_diagram (n : ℕ) :
    (dgm (ZMod 2) (Cech.filter (Fin.elim0 : Fin 0 → Empty)) n).points = 0 :=
  empty_diagram (ZMod 2) _ n

private theorem empty_ambient_bounds_and_uniform (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    errorBounds p (ZMod 2) (Fin.elim0 : Fin 0 → Empty) Fin.elim0 n 0 ∧
    uniformLimits (V := Fin 0) (X := Empty) (ZMod 2) n 0 :=
  (empty_costs (ZMod 2) (Fin.elim0 : Fin 0 → Empty) Fin.elim0 n hp).2.2.2.2.2.2.2

private theorem nonempty_labels_cannot_map_to_empty : ¬ Nonempty (Fin 1 → Empty) := by
  rintro ⟨a⟩
  exact Empty.elim (a 0)

/-! ### Two two-point clouds and a change of optimizer -/

private abbrev twoA : Fin 2 → ℝ := Cech.Examples.TwoPoints.pts
private def twoB : Fin 2 → ℝ := fun i => (3 : ℝ) • twoA i
private abbrev twoDA := dgm (ZMod 2) (Cech.filter twoA) 0
private abbrev twoDB := dgm (ZMod 2) (Cech.filter twoB) 0

private theorem twoA_points : twoDA.points =
    {((0 : ℝ), (⊤ : WithTop ℝ)), (0, ((1 : ℝ) : WithTop ℝ))} :=
  LogScaleDiagramComparisonExamples.twoPoints_cech_dgm_zero

private theorem twoB_points : twoDB.points =
    {((0 : ℝ), (⊤ : WithTop ℝ)), (0, ((3 : ℝ) : WithTop ℝ))} := by
  change (dgm (ZMod 2) (Cech.filter twoB) 0).points = _
  rw [show Cech.filter twoB = (Cech.filter twoA).scale 3 (by norm_num) from
    Cech.filter_smul twoA (by norm_num), dgm_scale, Diagram.scale,
    Diagram.map_points, twoA_points]
  norm_num

private theorem two_parts :
    finitePart twoDA.points = {((0 : ℝ), 1)} ∧
    finitePart twoDB.points = {((0 : ℝ), 3)} ∧
    essentialPart twoDA.points = ({0} : Multiset ℝ) ∧
    essentialPart twoDB.points = ({0} : Multiset ℝ) := by
  rw [twoA_points, twoB_points]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem two_presentations :
    Finset.univ.val.map (fun _ : Fin 1 => ((0 : ℝ), 1)) = finitePart twoDA.points ∧
    Finset.univ.val.map (fun _ : Fin 1 => ((0 : ℝ), 3)) = finitePart twoDB.points := by
  simp [two_parts.1, two_parts.2.1]

private theorem two_counts :
    Fintype.card twoDA.finiteOccurrences = 1 ∧
    Fintype.card twoDB.finiteOccurrences = 1 ∧
    Fintype.card twoDA.finiteOccurrences + Fintype.card twoDB.finiteOccurrences = 2 := by
  simp only [Multiset.card_coe, two_parts.1, two_parts.2.1, Multiset.card_singleton]
  norm_num

private theorem two_source_value (q : twoDA.finiteOccurrences) : q.1 = ((0 : ℝ), 1) := by
  simpa only [two_parts.1, Multiset.mem_singleton] using Multiset.coe_mem (x := q)

private theorem two_target_value (q : twoDB.finiteOccurrences) : q.1 = ((0 : ℝ), 3) := by
  simpa only [two_parts.2.1, Multiset.mem_singleton] using Multiset.coe_mem (x := q)

private theorem two_displacement : Cech.displacement twoA twoB = 4 := by
  apply le_antisymm
  · apply (Cech.displacement_le_iff _ _ _).mpr
    refine ⟨by norm_num, ?_⟩
    intro i
    fin_cases i <;> norm_num [twoA, twoB, Cech.Examples.TwoPoints.pts, Real.dist_eq]
  · have h := Cech.dist_le_displacement twoA twoB 1
    norm_num [twoA, twoB, Cech.Examples.TwoPoints.pts, Real.dist_eq] at h
    exact h

private theorem two_bottleneck : bottleneck twoDA twoDB = ENNReal.ofReal (3 / 2) := by
  rw [bottleneck_eq_presentation twoDA twoDB
    (fun _ : Fin 1 => ((0 : ℝ), 1)) (fun _ : Fin 1 => ((0 : ℝ), 3))
    (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))
    two_presentations.1 two_presentations.2
    (by simp [two_parts.2.2.1]) (by simp [two_parts.2.2.2])]
  let M : OccurrenceMatching (Fin 1) (Fin 1) (Fin 1) (Fin 1) :=
    ⟨fun _ => none, by simp, Equiv.refl _⟩
  apply le_antisymm
  · apply (presentationBottleneck_le_cost _ _ _ _ M).trans_eq
    norm_num [M, OccurrenceMatching.cost, finitePairCost, diagonalCost, essentialPairCost,
      reduceCtorEq]
    rw [if_neg (by decide : (none : Option (Fin 1)) ≠ some 0)]
    exact max_eq_right (ENNReal.ofReal_le_ofReal (by norm_num))
  · apply le_iInf
    intro N
    cases h : N.finite 0 with
    | none =>
      have hn : ¬ ∃ i, N.finite i = some (0 : Fin 1) := by
        rintro ⟨i, hi⟩
        have hi0 : i = 0 := Subsingleton.elim _ _
        simp [hi0, h] at hi
      have ht := N.target_le_cost
        (fun _ => ((0 : ℝ), 1)) (fun _ => ((0 : ℝ), 3))
        (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (0 : Fin 1)
      simpa [hn, diagonalCost] using ht
    | some j =>
      have hj : j = 0 := Subsingleton.elim _ _
      have hs := N.source_le_cost
        (fun _ => ((0 : ℝ), 1)) (fun _ => ((0 : ℝ), 3))
        (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (0 : Fin 1)
      have htwo : ENNReal.ofReal 2 ≤ N.cost
          (fun _ => ((0 : ℝ), 1)) (fun _ => ((0 : ℝ), 3))
          (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) := by
        norm_num [h, hj, finitePairCost] at hs
        convert hs using 1 <;> norm_num
      exact (ENNReal.ofReal_le_ofReal (by norm_num : (3 / 2 : ℝ) ≤ 2)).trans htwo

private theorem two_matching (p : ℝ) : matching p twoDA twoDB =
    (min ((2 : ℝ) ^ p) (((1 / 2 : ℝ) ^ p) + ((3 / 2 : ℝ) ^ p))) ^ p⁻¹ := by
  rw [matching_presentation _ _ _ _ two_presentations.1 two_presentations.2,
    finitePMatchingCost, finitePowerMatchingCost_singleton]
  norm_num [finitePairCost, diagonalCost]

private theorem two_costs_at_one :
    matching 1 twoDA twoDB = 2 ∧ transport 1 twoDA twoDB = 2 ∧
    |matching 1 twoDA twoDB - (bottleneck twoDA twoDB).toReal| = 1 / 2 ∧
    |transport 1 twoDA twoDB - (bottleneck twoDA twoDB).toReal| = 1 / 2 := by
  have hm : matching 1 twoDA twoDB = 2 := by
    rw [two_matching]
    norm_num
  have ht : transport 1 twoDA twoDB = 2 := by
    rw [transport, finitePBoundaryTransportCost_eq_matchingCost]
    exact hm
  norm_num [hm, ht, two_bottleneck]

private theorem two_costs_at_two :
    matching 2 twoDA twoDB = Real.sqrt (5 / 2) ∧
    transport 2 twoDA twoDB = Real.sqrt (5 / 2) := by
  rw [show transport 2 twoDA twoDB = matching 2 twoDA twoDB from
    finitePBoundaryTransportCost_eq_matchingCost _ _ _]
  norm_num [two_matching, Real.rpow_two, Real.sqrt_eq_rpow]

private theorem two_bounds_and_uniform {p : ℝ} (hp : 1 ≤ p) :
    (twoA, twoB) ∈ {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) |
      Cech.displacement z.1 z.2 ≤ 4} ∧
    errorBounds p (ZMod 2) twoA twoB 0 4 ∧
    errorBounds (3 / 2) (ZMod 2) twoA twoB 0 4 ∧
    uniformLimits (V := Fin 2) (X := ℝ) (ZMod 2) 0 4 := by
  exact ⟨two_displacement.le,
    error_bounds hp _ _ _ 0 (by norm_num) two_displacement.le,
    error_bounds (by norm_num) _ _ _ 0 (by norm_num) two_displacement.le,
    uniform_limits _ 0 (by norm_num)⟩

/-- This is a matching of the canonical occurrence types. -/
private def twoCanonicalPair : OccurrenceMatching twoDA.finiteOccurrences
    twoDB.finiteOccurrences PEmpty.{1} PEmpty.{1} :=
  FinitePBoundaryTransportExamples.pairSingletons.relabel
    (finiteEnum twoDA (fun _ : Fin 1 => ((0 : ℝ), 1)) two_presentations.1).1.symm
    (finiteEnum twoDB (fun _ : Fin 1 => ((0 : ℝ), 3)) two_presentations.2).1.symm
    (Equiv.refl _) (Equiv.refl _)

private theorem two_pair_power (p : ℝ) :
    twoCanonicalPair.totalFinitePowerCost p
      (fun q : twoDA.finiteOccurrences => q.1)
      (fun q : twoDB.finiteOccurrences => q.1) = (2 : ℝ) ^ p := by
  let u := (finiteEnum twoDA (fun _ : Fin 1 => ((0 : ℝ), 1)) two_presentations.1).1.symm
  let v := (finiteEnum twoDB (fun _ : Fin 1 => ((0 : ℝ), 3)) two_presentations.2).1.symm
  have hu : (fun q : twoDA.finiteOccurrences => q.1) =
      (fun _ : Fin 1 => ((0 : ℝ), 1)) ∘ u := by
    funext q
    exact two_source_value q
  have hv : (fun q : twoDB.finiteOccurrences => q.1) =
      (fun _ : Fin 1 => ((0 : ℝ), 3)) ∘ v := by
    funext q
    exact two_target_value q
  rw [hu, hv]
  change (FinitePBoundaryTransportExamples.pairSingletons.relabel u v
    (Equiv.refl _) (Equiv.refl _)).totalFinitePowerCost _ _ _ = _
  rw [OccurrenceMatching.totalFinitePowerCost_relabel]
  norm_num [FinitePBoundaryTransportExamples.pairSingletons,
    OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost,
    finitePairCost, diagonalCost, reduceCtorEq]

private theorem two_zero_plan_power (p : ℝ) :
    (FiniteBoundaryPlan.zero : FiniteBoundaryPlan twoDA.finiteOccurrences
      twoDB.finiteOccurrences).powerCost p
      (fun q => q.1) (fun q => q.1) = (1 / 2 : ℝ) ^ p + (3 / 2 : ℝ) ^ p := by
  norm_num [FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost,
    FiniteBoundaryPlan.zero, FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass,
    two_source_value, two_target_value, two_counts.1, two_counts.2.1, diagonalCost]

private theorem two_real_optimizer_change :
    (FiniteBoundaryPlan.ofMatching twoCanonicalPair).powerCost 1
        (fun q => q.1) (fun q => q.1) =
      (transport 1 twoDA twoDB) ^ (1 : ℝ) ∧
    (transport 2 twoDA twoDB) ^ (2 : ℝ) <
      (FiniteBoundaryPlan.ofMatching twoCanonicalPair).powerCost 2
        (fun q => q.1) (fun q => q.1) ∧
    (FiniteBoundaryPlan.zero : FiniteBoundaryPlan twoDA.finiteOccurrences
      twoDB.finiteOccurrences).powerCost 2 (fun q => q.1) (fun q => q.1) =
      (transport 2 twoDA twoDB) ^ (2 : ℝ) := by
  rw [FiniteBoundaryPlan.powerCost_ofMatching, FiniteBoundaryPlan.powerCost_ofMatching,
    two_pair_power, two_pair_power, two_zero_plan_power,
    two_costs_at_one.2.1, two_costs_at_two.2]
  simp only [Real.rpow_one, Real.rpow_two]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 2)]
  norm_num

/-! ### The Euclidean triangle versus a constant cloud -/

private theorem deleting_common_essential {I : Type*} [Fintype I] (x : I → ℝ × ℝ) :
    presentationBottleneck x (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) =
      Finset.univ.sup (fun i => diagonalCost (x i)) := by
  classical
  let M : OccurrenceMatching I (Fin 0) (Fin 1) (Fin 1) :=
    ⟨fun _ => none, by simp, Equiv.refl _⟩
  letI : Nonempty (OccurrenceMatching I (Fin 0) (Fin 1) (Fin 1)) := ⟨M⟩
  have hc (N : OccurrenceMatching I (Fin 0) (Fin 1) (Fin 1)) :
      N.cost x Fin.elim0 (fun _ => 0) (fun _ => 0) =
        Finset.univ.sup (fun i => diagonalCost (x i)) := by
    have hn (i : I) : N.finite i = none := by
      cases h : N.finite i with
      | none => rfl
      | some j => exact Fin.elim0 j
    simp [OccurrenceMatching.cost, hn, essentialPairCost]
  simp only [presentationBottleneck, hc, ciInf_const]

private abbrev triA := Cech.Examples.Triangle.pts
private def triB := fun _ : Fin 3 => triA 0
private abbrev triDA := dgm (ZMod 2) (Cech.filter triA) 0
private abbrev triDB := dgm (ZMod 2) (Cech.filter triB) 0
private def triValues : Fin 2 → ℝ × ℝ := ![(0, 1), (0, Real.sqrt 5 / 2)]

private theorem tri_parts :
    finitePart triDA.points = {((0 : ℝ), 1), (0, Real.sqrt 5 / 2)} ∧
    finitePart triDB.points = 0 ∧
    essentialPart triDA.points = ({0} : Multiset ℝ) ∧
    essentialPart triDB.points = ({0} : Multiset ℝ) := by
  refine ⟨?_, constant_finitePart (ZMod 2) (triA 0) 0,
    Cech.essentialPart_dgm_zero_eq_singleton _ _,
    Cech.essentialPart_dgm_zero_eq_singleton _ _⟩
  change finitePart (dgm (ZMod 2) TriangleCechRipsExamples.cechT 0).points = _
  rw [TriangleCechRipsExamples.triangle_cech_dgm_zero]
  rfl

private theorem tri_presentations :
    Finset.univ.val.map triValues = finitePart triDA.points ∧
    Finset.univ.val.map (Fin.elim0 : Fin 0 → ℝ × ℝ) = finitePart triDB.points := by
  simp [tri_parts.1, tri_parts.2.1, triValues, Finset.univ_fin2]

private theorem tri_counts :
    Fintype.card triDA.finiteOccurrences + Fintype.card triDB.finiteOccurrences = 2 ∧
    2 * Nat.choose (Fintype.card (Fin 3)) (0 + 2) = 6 := by
  norm_num [Multiset.card_coe, tri_parts.1, tri_parts.2.1, Nat.choose]

private theorem tri_displacement : Cech.displacement triA triB ≤ 3 := by
  apply (Cech.displacement_le_iff _ _ _).mpr
  refine ⟨by norm_num, ?_⟩
  intro i
  change dist (triA i) (triA 0) ≤ 3
  fin_cases i
  · simp
  · change dist (Cech.Examples.Triangle.pts 1) (Cech.Examples.Triangle.pts 0) ≤ 3
    rw [dist_comm, TriangleCechRipsExamples.triangle_dist01]
    norm_num
  · change dist (Cech.Examples.Triangle.pts 2) (Cech.Examples.Triangle.pts 0) ≤ 3
    rw [dist_comm, TriangleCechRipsExamples.triangle_dist02]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg (5 : ℝ)]

private theorem tri_bottleneck : bottleneck triDA triDB = ENNReal.ofReal (Real.sqrt 5 / 4) := by
  rw [bottleneck_eq_presentation triDA triDB triValues (Fin.elim0 : Fin 0 → ℝ × ℝ)
    (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))
    tri_presentations.1 tri_presentations.2
    (by simp [tri_parts.2.2.1]) (by simp [tri_parts.2.2.2]), deleting_common_essential]
  have hs : 2 ≤ Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg (5 : ℝ)]
  have hdiv : 0 ≤ Real.sqrt 5 / 2 := by positivity
  norm_num [Finset.univ_fin2, triValues, diagonalCost, abs_of_nonneg hdiv,
    show |0 - Real.sqrt 5 / 2| = Real.sqrt 5 / 2 by rw [zero_sub, abs_neg,
      abs_of_nonneg hdiv]]
  rw [show Real.sqrt 5 / 2 / 2 = Real.sqrt 5 / 4 by ring]
  exact max_eq_right (show ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (Real.sqrt 5 / 4) from
    ENNReal.ofReal_le_ofReal (by linarith))

private theorem tri_costs {p : ℝ} (_hp : 1 ≤ p) :
    matching p triDA triDB = ((1 / 2 : ℝ) ^ p + (Real.sqrt 5 / 4) ^ p) ^ p⁻¹ ∧
    transport p triDA triDB = ((1 / 2 : ℝ) ^ p + (Real.sqrt 5 / 4) ^ p) ^ p⁻¹ := by
  have hm : matching p triDA triDB =
      ((1 / 2 : ℝ) ^ p + (Real.sqrt 5 / 4) ^ p) ^ p⁻¹ := by
    rw [matching_presentation _ _ _ _ tri_presentations.1 tri_presentations.2,
      finitePMatchingCost_of_isEmpty_right, Fin.sum_univ_two]
    have hs : 0 ≤ Real.sqrt 5 / 2 := by positivity
    norm_num [triValues, diagonalCost, abs_of_nonneg hs,
      show |0 - Real.sqrt 5 / 2| = Real.sqrt 5 / 2 by rw [zero_sub, abs_neg,
        abs_of_nonneg hs]]
    rw [show Real.sqrt 5 / 2 / 2 = Real.sqrt 5 / 4 by ring,
      ENNReal.toReal_ofReal (by positivity)]
  exact ⟨hm, (finitePBoundaryTransportCost_eq_matchingCost _ _ _).trans hm⟩

private theorem tri_nonzero_error :
    |matching 1 triDA triDB - (bottleneck triDA triDB).toReal| = 1 / 2 ∧
    |transport 1 triDA triDB - (bottleneck triDA triDB).toReal| = 1 / 2 := by
  rw [(tri_costs (by norm_num : (1 : ℝ) ≤ 1)).1,
    (tri_costs (by norm_num : (1 : ℝ) ≤ 1)).2, tri_bottleneck,
    ENNReal.toReal_ofReal (by positivity)]
  norm_num

private theorem tri_bounds_and_uniform {p : ℝ} (hp : 1 ≤ p) :
    (triA, triB) ∈ {z : (Fin 3 → EuclideanSpace ℝ (Fin 2)) ×
      (Fin 3 → EuclideanSpace ℝ (Fin 2)) | Cech.displacement z.1 z.2 ≤ 3} ∧
    errorBounds p (ZMod 2) triA triB 0 3 ∧
    errorBounds (3 / 2) (ZMod 2) triA triB 0 3 ∧
    uniformLimits (V := Fin 3) (X := EuclideanSpace ℝ (Fin 2)) (ZMod 2) 0 3 := by
  exact ⟨tri_displacement,
    error_bounds hp _ _ _ 0 (by norm_num) tri_displacement,
    error_bounds (by norm_num) _ _ _ 0 (by norm_num) tri_displacement,
    uniform_limits _ 0 (by norm_num)⟩

/-! ### Repeated labels, with the zero-length merge removed -/

private def repeatedA : Fin 3 → ℝ := ![0, 0, 2]
private def repeatedB : Fin 3 → ℝ := fun _ => 0
private abbrev repeatedDA := dgm (ZMod 2) (Cech.filter repeatedA) 0
private abbrev repeatedDB := dgm (ZMod 2) (Cech.filter repeatedB) 0

private theorem repeated_not_injective : ¬ Function.Injective repeatedA := by
  intro h
  have he := h (show repeatedA 0 = repeatedA 1 by rfl)
  exact (by decide : (0 : Fin 3) ≠ 1) he

private theorem value_zero_on_face {V X : Type*} [PseudoMetricSpace X]
    (a : V → X) (s : TotalFace (Rips.fullComplex V)) (x : X)
    (hx : ∀ v ∈ s.val, a v = x) : (Cech.filter a).value s = 0 := by
  apply le_antisymm _ (Cech.filter_value_nonneg _ _)
  exact (Cech.filter_value_le_radiusAt a s x).trans
    ((Cech.radiusAt_le_iff a x s.val 0).mpr ⟨le_rfl, fun v hv => by simp [hx v hv]⟩)

private theorem repeated_mixed_value (s : TotalFace (Rips.fullComplex (Fin 3)))
    (v : Fin 3) (hv : v ∈ s.val) (hzero : repeatedA v = 0) (htwo : 2 ∈ s.val) :
    (Cech.filter repeatedA).value s = 1 := by
  apply le_antisymm
  · apply (Cech.filter_value_le_radiusAt repeatedA s 1).trans
    apply (Cech.radiusAt_le_iff repeatedA 1 s.val 1).mpr
    refine ⟨by norm_num, fun i _ => ?_⟩
    fin_cases i <;> norm_num [repeatedA, Real.dist_eq]
  · rw [Cech.filter_value]
    apply le_ciInf
    intro x
    have h0 := Cech.dist_le_radiusAt repeatedA x hv
    have h2 := Cech.dist_le_radiusAt repeatedA x htwo
    rw [hzero] at h0
    change dist x (2 : ℝ) ≤ Cech.radiusAt repeatedA x s.val at h2
    have hd : (2 : ℝ) ≤ dist x 0 + dist x 2 := by
      have h := dist_triangle_left (0 : ℝ) 2 x
      norm_num [Real.dist_eq] at h ⊢
      exact h
    linarith

private def repeatedVals (i : ℕ) : ℝ := if i < 4 then 0 else 1

private theorem repeated_enum_values
    (i : Fin (faceCount Reduction.Examples.FilledTriangle.C.toPre)) :
    (TriangleCechRipsExamples.pullTriangle (Cech.filter repeatedA)).value
      (Reduction.Examples.FilledTriangle.e.enum i) = repeatedVals i.val := by
  fin_cases i
  · change (Cech.filter repeatedA).value ⟨{0}, by simp⟩ = _
    rw [TriangleCechRipsExamples.cech_value_singleton]
    norm_num [repeatedVals]
  · change (Cech.filter repeatedA).value ⟨{1}, by simp⟩ = _
    rw [TriangleCechRipsExamples.cech_value_singleton]
    norm_num [repeatedVals]
  · change (Cech.filter repeatedA).value ⟨{2}, by simp⟩ = _
    rw [TriangleCechRipsExamples.cech_value_singleton]
    norm_num [repeatedVals]
  · change (Cech.filter repeatedA).value ⟨{0, 1}, by simp⟩ = _
    rw [value_zero_on_face repeatedA _ 0 (by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> rfl)]
    norm_num [repeatedVals]
  · change (Cech.filter repeatedA).value ⟨{1, 2}, by simp⟩ = _
    rw [repeated_mixed_value _ 1 (by simp) rfl (by simp)]
    norm_num [repeatedVals]
  · change (Cech.filter repeatedA).value ⟨{0, 2}, by simp⟩ = _
    rw [repeated_mixed_value _ 0 (by simp) rfl (by simp)]
    norm_num [repeatedVals]
  · change (Cech.filter repeatedA).value ⟨{0, 1, 2}, by simp⟩ = _
    rw [repeated_mixed_value _ 0 (by simp) rfl (by simp)]
    norm_num [repeatedVals]

private theorem repeated_monotone_enum :
    Monotone ((TriangleCechRipsExamples.pullTriangle (Cech.filter repeatedA)).value ∘
      Reduction.Examples.FilledTriangle.e.enum) := by
  intro i j hij
  simp only [Function.comp_apply, repeated_enum_values]
  have hle : i.val ≤ j.val := hij
  unfold repeatedVals
  split_ifs <;> first | (norm_num; done) | omega

private theorem repeated_points : repeatedDA.points =
    {((0 : ℝ), (⊤ : WithTop ℝ)), (0, ((1 : ℝ) : WithTop ℝ))} := by
  change (dgm (ZMod 2) (Cech.filter repeatedA) 0).points = _
  rw [← TriangleCechRipsExamples.dgm_pullTriangle,
    ← evaluatePivotTemplate_eq_dgm (ZMod 2) Reduction.Examples.FilledTriangle.e _
      repeated_monotone_enum 0]
  simp only [evaluatePivotTemplate]
  rw [Reduction.Examples.FilledTriangle.exact_pairs_zero,
    Reduction.Examples.FilledTriangle.exact_essential_zero]
  simp [Multiset.filter_singleton, pairValues, birthValue,
    -TriangleCechRipsExamples.pullTriangle_value, repeated_enum_values, repeatedVals]
  simp only [← Multiset.cons_zero, Multiset.cons_swap]

private theorem repeated_parts :
    finitePart repeatedDA.points = {((0 : ℝ), 1)} ∧
    finitePart repeatedDB.points = 0 ∧
    essentialPart repeatedDA.points = ({0} : Multiset ℝ) ∧
    essentialPart repeatedDB.points = ({0} : Multiset ℝ) := by
  refine ⟨?_, constant_finitePart (ZMod 2) (0 : ℝ) 0,
    Cech.essentialPart_dgm_zero_eq_singleton _ _,
    Cech.essentialPart_dgm_zero_eq_singleton _ _⟩
  rw [repeated_points]
  rfl

private theorem repeated_presentations :
    Finset.univ.val.map (fun _ : Fin 1 => ((0 : ℝ), 1)) = finitePart repeatedDA.points ∧
    Finset.univ.val.map (Fin.elim0 : Fin 0 → ℝ × ℝ) = finitePart repeatedDB.points := by
  simp [repeated_parts.1, repeated_parts.2.1]

private theorem repeated_counts :
    Fintype.card repeatedDA.finiteOccurrences = 1 ∧
    Fintype.card repeatedDB.finiteOccurrences = 0 ∧
    2 * Nat.choose (Fintype.card (Fin 3)) (0 + 2) = 6 := by
  norm_num [Multiset.card_coe, repeated_parts.1, repeated_parts.2.1, Nat.choose]

private theorem repeated_displacement : Cech.displacement repeatedA repeatedB = 2 := by
  apply le_antisymm
  · apply (Cech.displacement_le_iff _ _ _).mpr
    refine ⟨by norm_num, fun i => ?_⟩
    fin_cases i <;> norm_num [repeatedA, repeatedB, Real.dist_eq]
  · have h := Cech.dist_le_displacement repeatedA repeatedB 2
    change dist (2 : ℝ) 0 ≤ Cech.displacement repeatedA repeatedB at h
    norm_num [Real.dist_eq] at h
    exact h

private theorem repeated_bottleneck :
    bottleneck repeatedDA repeatedDB = ENNReal.ofReal (1 / 2) := by
  rw [bottleneck_eq_presentation repeatedDA repeatedDB
    (fun _ : Fin 1 => ((0 : ℝ), 1)) (Fin.elim0 : Fin 0 → ℝ × ℝ)
    (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))
    repeated_presentations.1 repeated_presentations.2
    (by simp [repeated_parts.2.2.1]) (by simp [repeated_parts.2.2.2]),
    deleting_common_essential]
  norm_num [diagonalCost]

private theorem repeated_costs {p : ℝ} (hp : 1 ≤ p) :
    matching p repeatedDA repeatedDB = 1 / 2 ∧ transport p repeatedDA repeatedDB = 1 / 2 := by
  have hm : matching p repeatedDA repeatedDB = 1 / 2 := by
    rw [matching_presentation _ _ _ _ repeated_presentations.1 repeated_presentations.2,
      finitePMatchingCost_of_isEmpty_right]
    norm_num [diagonalCost]
    exact Real.rpow_rpow_inv (by norm_num) (ne_of_gt (lt_of_lt_of_le zero_lt_one hp))
  exact ⟨hm, (finitePBoundaryTransportCost_eq_matchingCost _ _ _).trans hm⟩

private theorem repeated_bounds_and_uniform {p : ℝ} (hp : 1 ≤ p) :
    (repeatedA, repeatedB) ∈ {z : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      Cech.displacement z.1 z.2 ≤ 2} ∧
    errorBounds p (ZMod 2) repeatedA repeatedB 0 2 ∧
    uniformLimits (V := Fin 3) (X := ℝ) (ZMod 2) 0 2 := by
  exact ⟨repeated_displacement.le,
    error_bounds hp _ _ _ 0 (by norm_num) repeated_displacement.le,
    uniform_limits _ 0 (by norm_num)⟩

/-! ### Translated filter values, the logarithmic obstruction and positive degree -/

private abbrev baseSingleton := dgm (ZMod 2) (Cech.filter (oneCloud 0)) 0
private abbrev shiftedSingleton := dgm (ZMod 2)
  ((Cech.filter (oneCloud 0)).map (OrderIso.addRight (1 : ℝ)).toOrderEmbedding) 0

private theorem shifted_singleton_points : shiftedSingleton.points =
    {((1 : ℝ), (⊤ : WithTop ℝ))} := by
  change (dgm (ZMod 2)
    ((Cech.filter (oneCloud 0)).map (OrderIso.addRight (1 : ℝ)).toOrderEmbedding) 0).points = _
  rw [dgm_map, Diagram.map_points, singleton_points]
  norm_num

private theorem singleton_translation_boundary {p : ℝ} (hp : 1 ≤ p) :
    essentialPart baseSingleton.points = ({0} : Multiset ℝ) ∧
    essentialPart shiftedSingleton.points = ({1} : Multiset ℝ) ∧
    (essentialPart baseSingleton.points).card = 1 ∧
    (essentialPart shiftedSingleton.points).card = 1 ∧
    essentialPart shiftedSingleton.points ≠ ({0} : Multiset ℝ) ∧
    matching p baseSingleton shiftedSingleton = 0 ∧
    transport p baseSingleton shiftedSingleton = 0 ∧
    bottleneck baseSingleton shiftedSingleton = 1 := by
  have hbase : baseSingleton = FinitePBottleneckLimitExamples.essentialBirth 0 := by
    apply Diagram.ext
    rw [singleton_points]
    simp [FinitePBottleneckLimitExamples.essentialBirth, orderedQ, List.ofFn_succ]
  have hshift : shiftedSingleton = FinitePBottleneckLimitExamples.essentialBirth 1 := by
    apply Diagram.ext
    rw [shifted_singleton_points]
    simp [FinitePBottleneckLimitExamples.essentialBirth, orderedQ, List.ofFn_succ]
  have hc := FinitePBottleneckLimitExamples.essential_births_zero_one hp
  have he : essentialPart shiftedSingleton.points = ({1} : Multiset ℝ) := by
    rw [shifted_singleton_points]
    rfl
  have hb := Cech.essentialPart_dgm_zero_eq_singleton (ZMod 2) (oneCloud 0)
  have hm : matching p baseSingleton shiftedSingleton = 0 := by
    rw [hbase, hshift]
    exact hc.1
  refine ⟨hb, he, by rw [hb]; rfl, by rw [he]; rfl, ?_, hm,
    (finitePBoundaryTransportCost_eq_matchingCost _ _ _).trans hm, ?_⟩
  · rw [he]
    norm_num
  · rw [hbase, hshift]
    exact hc.2

private theorem cech_h0_log_obstruction (k : Type) [Field k]
    {m : ℕ} (c : Fin m ↪o ℝ) (x : ℝ) :
    ¬ IsConstructible c (logModule k (Cech.filter (oneCloud x)) 0) := by
  let σ : TotalFace (Rips.fullComplex (Fin 1)) := ⟨{0}, by simp⟩
  exact not_isConstructible_logModule_zero k c σ (by simp [σ])
    (TriangleCechRipsExamples.cech_value_singleton _ 0).le

private theorem positive_triangle_nonzero :
    (dgm (ZMod 2) (Cech.filter triA) 1).points ≠ 0 ∧
    (Real.sqrt 5 / 2 : ℝ) < 5 / 4 := by
  constructor
  · change (dgm (ZMod 2) TriangleCechRipsExamples.cechT 1).points ≠ 0
    rw [TriangleCechRipsExamples.triangle_cech_dgm_one]
    simp
  · exact TriangleCechRipsExamples.sqrt_five_bounds.2.1

private theorem positive_degree_old_and_new_bounds {p : ℝ} (hp : 1 ≤ p) :
    errorBounds p (ZMod 2) triA triA 1 0 ∧
    errorBounds p (ZMod 2) triA triA 1 0 := by
  constructor
  · exact ⟨Cech.finitePMatchingCost_dgm_abs_sub_bottleneck_le_uniformBound
      hp (ZMod 2) triA triA (by norm_num : 1 ≤ 1) le_rfl (by simp),
      Cech.finitePBoundaryTransportCost_dgm_abs_sub_bottleneck_le_uniformBound
        hp (ZMod 2) triA triA (by norm_num : 1 ≤ 1) le_rfl (by simp)⟩
  · exact error_bounds hp (ZMod 2) triA triA 1 le_rfl (by simp)

private theorem positive_degree_old_and_new_uniform :
    uniformLimits (V := Fin 3) (X := EuclideanSpace ℝ (Fin 2)) (ZMod 2) 1 0 ∧
    uniformLimits (V := Fin 3) (X := EuclideanSpace ℝ (Fin 2)) (ZMod 2) 1 0 := by
  exact ⟨⟨Cech.finitePMatchingCost_dgm_tendstoUniformlyOn_bottleneck
      (ZMod 2) 1 (by norm_num) 0 le_rfl,
    Cech.finitePBoundaryTransportCost_dgm_tendstoUniformlyOn_bottleneck
      (ZMod 2) 1 (by norm_num) 0 le_rfl⟩,
    uniform_limits (ZMod 2) 1 le_rfl⟩

end TDA.Persistence.CechFinitePBottleneckAllDegreesExamples
