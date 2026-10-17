import TDA.Persistence.CechSupNormPersistenceImage
import TDA.Persistence.DiagramBottleneckLaws

set_option autoImplicit false

/-!
# Additive Rips-versus-Čech comparison

Positive scaling moves a real diagram by at most `|1 - c|` times a coordinate
bound, via the identity matching. Coordinates of actual diagrams are critical
values, and Rips values are at most the carrier diameter. Hence in the
sup-metric product and on the line the Rips and Čech diagrams of one
configuration are at bottleneck distance at most half the carrier diameter,
with kernel and image consequences in the sup-norm product. These are
elementary library results with no external source. No Euclidean or general-
ambient claim is made, since the halving identity fails there.
-/

universe u w

namespace TDA.Persistence

open TDA.Filtration

private theorem finitePart_scale_points' (D : Diagram ℝ) {c : ℝ} (hc : 0 < c) :
    finitePart (D.scale c hc).points = (finitePart D.points).map (scaleFinitePair c) := by
  rw [Diagram.scale, finitePart_map_points]
  rfl

private theorem essentialPart_scale_points' (D : Diagram ℝ) {c : ℝ} (hc : 0 < c) :
    essentialPart (D.scale c hc).points = (essentialPart D.points).map (fun b => c * b) := by
  rw [Diagram.scale, essentialPart_map_points]
  rfl

private def indexEndpoints {α : Type w} [LinearOrder α] {N : ℕ}
    (v : Fin N → α) (I : FiniteInterval N) : α × WithTop α :=
  (v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
    if hd : I.death < N then (v ⟨I.death, hd⟩ : WithTop α) else ⊤)

private theorem ofIndexBars_points' {α : Type w} [LinearOrder α] {N : ℕ}
    (v : Fin N → α) (hv : StrictMono v) (B : Multiset (FiniteInterval N)) :
    (ofIndexBars v hv B).points = B.map (indexEndpoints v) := rfl

/-- Scaling a real persistence diagram by a positive factor moves it by at most
`|1 - c|` times a bound on all of its coordinates. -/
theorem bottleneck_self_scale_le (D : Diagram ℝ) {c : ℝ} (hc : 0 < c) {M : ℝ}
    (hfin : ∀ p ∈ finitePart D.points, |p.1| ≤ M ∧ |p.2| ≤ M)
    (hess : ∀ b ∈ essentialPart D.points, |b| ≤ M) :
    bottleneck D (D.scale c hc) ≤ ENNReal.ofReal (|1 - c| * M) := by
  rw [bottleneck_eq_presentation D (D.scale c hc)
    (fun p : D.finiteOccurrences => p.1)
    (scaleFinitePair c ∘ fun p : D.finiteOccurrences => p.1)
    (fun e : D.essentialOccurrences => e.1)
    (fun e : D.essentialOccurrences => c * e.1)
    (Multiset.map_univ_coe _)
    ((Multiset.map_univ _ _).trans (finitePart_scale_points' D hc).symm)
    (Multiset.map_univ_coe _)
    ((Multiset.map_univ _ _).trans (essentialPart_scale_points' D hc).symm)]
  let matching : OccurrenceMatching D.finiteOccurrences D.finiteOccurrences
      D.essentialOccurrences D.essentialOccurrences :=
    ⟨some, fun i i' j hi hi' => Option.some.inj (hi.trans hi'.symm), Equiv.refl _⟩
  refine (presentationBottleneck_le_cost
    (fun p : D.finiteOccurrences => p.1)
    (scaleFinitePair c ∘ fun p : D.finiteOccurrences => p.1)
    (fun e : D.essentialOccurrences => e.1)
    (fun e : D.essentialOccurrences => c * e.1) matching).trans ?_
  apply OccurrenceMatching.cost_le_of matching
  · intro i
    change finitePairCost i.1 (scaleFinitePair c i.1) ≤ _
    have hi : i.1 ∈ finitePart D.points := Multiset.coe_mem (x := i)
    have hdiff (a : ℝ) : |a - c * a| = |1 - c| * |a| := by
      rw [← one_sub_mul, abs_mul]
    unfold finitePairCost scaleFinitePair
    apply ENNReal.ofReal_le_ofReal
    rw [hdiff, hdiff, ← mul_max_of_nonneg _ _ (abs_nonneg (1 - c))]
    exact mul_le_mul_of_nonneg_left
      (max_le (hfin i.1 hi).1 (hfin i.1 hi).2) (abs_nonneg _)
  · intro j
    rw [if_pos ⟨j, rfl⟩]
    exact zero_le
  · intro i
    change essentialPairCost i.1 (c * i.1) ≤ _
    have hi : i.1 ∈ essentialPart D.points := Multiset.coe_mem (x := i)
    unfold essentialPairCost
    apply ENNReal.ofReal_le_ofReal
    rw [← one_sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hess i.1 hi) (abs_nonneg _)

section CriticalCoordinates

variable {V : Type u} [LinearOrder V] (k : Type u) [Field k]
  {K : PreAbstractSimplicialComplex V} [Fintype (TDA.Simplicial.TotalFace K)]
  {α : Type w} [LinearOrder α]
  (f : TDA.Filtration.FilterFunction K α)

/-- Each finite coordinate of an actual diagram is a critical value of its
filter function. -/
theorem mem_criticalValues_of_mem_finitePart_dgm {n : ℕ} {p : α × α}
    (hp : p ∈ finitePart (dgm k f n).points) :
    p.1 ∈ f.criticalValues ∧ p.2 ∈ f.criticalValues := by
  unfold dgm at hp
  rw [ofIndexBars_points'] at hp
  obtain ⟨z, hz, hzp⟩ := (Multiset.mem_filterMap _ _).mp hp
  obtain ⟨I, hI, rfl⟩ := Multiset.mem_map.mp hz
  by_cases hdeath : I.death < f.criticalValues.card
  · let ib : Fin (f.criticalValues.card) :=
      ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩
    let id : Fin (f.criticalValues.card) := ⟨I.death, hdeath⟩
    have hpoint : (f.criticalValue ib, f.criticalValue id) = p := by
      apply Option.some.inj
      simpa [indexEndpoints, ib, id, hdeath] using hzp
    have hbirth := TDA.Filtration.FilterFunction.criticalValue_mem f ib
    have hdeath' := TDA.Filtration.FilterFunction.criticalValue_mem f id
    have hfirst := congrArg Prod.fst hpoint
    have hsecond := congrArg Prod.snd hpoint
    exact ⟨hfirst ▸ hbirth, hsecond ▸ hdeath'⟩
  · simp [indexEndpoints, hdeath] at hzp

/-- Each essential birth coordinate of an actual diagram is a critical value
of its filter function. -/
theorem mem_criticalValues_of_mem_essentialPart_dgm {n : ℕ} {b : α}
    (hb : b ∈ essentialPart (dgm k f n).points) :
    b ∈ f.criticalValues := by
  unfold dgm at hb
  rw [ofIndexBars_points'] at hb
  obtain ⟨z, hz, hzb⟩ := (Multiset.mem_filterMap _ _).mp hb
  obtain ⟨I, hI, rfl⟩ := Multiset.mem_map.mp hz
  by_cases hdeath : I.death < f.criticalValues.card
  · simp [indexEndpoints, hdeath] at hzb
  · let ib : Fin (f.criticalValues.card) :=
      ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩
    have hpoint : f.criticalValue ib = b := by
      apply Option.some.inj
      simpa [indexEndpoints, ib, hdeath] using hzb
    have hbirth := TDA.Filtration.FilterFunction.criticalValue_mem f ib
    exact hpoint ▸ hbirth

end CriticalCoordinates

end TDA.Persistence

namespace TDA.Filtration.Rips

open TDA.Simplicial

/-- Every Rips filter value is bounded by the diameter of the full carrier. -/
theorem filter_value_le_diameter_univ {V : Type u} [Fintype V]
    (d : MetricSpace V) (s : TotalFace (fullComplex V)) :
    (Rips.filter d).value s ≤ diameter d Finset.univ := by
  rw [filter_value]
  exact diameter_mono d (Finset.subset_univ _)

end TDA.Filtration.Rips

namespace TDA.Persistence.Cech

open TDA.Filtration MeasureTheory Set PersistenceImage

variable {V : Type u} [LinearOrder V] [Fintype V] (k : Type u) [Field k]
  {ι : Type w} [Fintype ι] {A B : ℝ}

private theorem rips_dgm_coordinate_bounds (d : MetricSpace V) (n : ℕ) :
    (∀ x ∈ finitePart (dgm k (Rips.filter d) n).points,
      |x.1| ≤ Rips.diameter d Finset.univ ∧ |x.2| ≤ Rips.diameter d Finset.univ) ∧
      (∀ b ∈ essentialPart (dgm k (Rips.filter d) n).points,
        |b| ≤ Rips.diameter d Finset.univ) := by
  constructor
  · intro x hx
    have hcrit := TDA.Persistence.mem_criticalValues_of_mem_finitePart_dgm
      k (Rips.filter d) hx
    obtain ⟨s, hs⟩ :=
      (TDA.Filtration.FilterFunction.mem_criticalValues
        (Rips.filter d) x.1).1 hcrit.1
    obtain ⟨t, ht⟩ :=
      (TDA.Filtration.FilterFunction.mem_criticalValues
        (Rips.filter d) x.2).1 hcrit.2
    have hxnonneg : 0 ≤ x.1 := by
      rw [← hs, Rips.filter_value]
      exact Rips.diameter_nonneg d _
    have hxle : x.1 ≤ Rips.diameter d Finset.univ := by
      rw [← hs]
      exact TDA.Filtration.Rips.filter_value_le_diameter_univ d s
    have hynonneg : 0 ≤ x.2 := by
      rw [← ht, Rips.filter_value]
      exact Rips.diameter_nonneg d _
    have hyle : x.2 ≤ Rips.diameter d Finset.univ := by
      rw [← ht]
      exact TDA.Filtration.Rips.filter_value_le_diameter_univ d t
    exact ⟨by simpa [abs_of_nonneg hxnonneg] using hxle,
      by simpa [abs_of_nonneg hynonneg] using hyle⟩
  · intro b hb
    have hcrit := TDA.Persistence.mem_criticalValues_of_mem_essentialPart_dgm
      k (Rips.filter d) hb
    obtain ⟨s, hs⟩ :=
      (TDA.Filtration.FilterFunction.mem_criticalValues
        (Rips.filter d) b).1 hcrit
    have hnonneg : 0 ≤ b := by
      rw [← hs, Rips.filter_value]
      exact Rips.diameter_nonneg d _
    have hle : b ≤ Rips.diameter d Finset.univ := by
      rw [← hs]
      exact TDA.Filtration.Rips.filter_value_le_diameter_univ d s
    simpa [abs_of_nonneg hnonneg] using hle

private theorem bottleneck_rips_scale_le (d : MetricSpace V) (n : ℕ) :
    bottleneck (dgm k (Rips.filter d) n)
        ((dgm k (Rips.filter d) n).scale 2⁻¹ (inv_pos.2 zero_lt_two)) ≤
      ENNReal.ofReal (Rips.diameter d Finset.univ / 2) := by
  have h := bottleneck_self_scale_le (dgm k (Rips.filter d) n)
    (c := (2 : ℝ)⁻¹) (inv_pos.2 zero_lt_two)
    (M := Rips.diameter d Finset.univ)
    (rips_dgm_coordinate_bounds k d n).1
    (rips_dgm_coordinate_bounds k d n).2
  have hfactor :
      |(1 : ℝ) - (2 : ℝ)⁻¹| * Rips.diameter d Finset.univ =
        Rips.diameter d Finset.univ / 2 := by
    rw [show |(1 : ℝ) - (2 : ℝ)⁻¹| = (1 : ℝ) / 2 by norm_num]
    ring
  rw [← hfactor]
  exact h

/-- In the sup-norm product, the Rips and Čech diagrams of one configuration
are at bottleneck distance at most half the carrier diameter. -/
theorem bottleneck_rips_cech_dgm_le_half_diameter (d : MetricSpace V)
    (p : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ) :
    bottleneck (dgm k (Rips.filter d) n) (dgm k (Cech.filter p) n) ≤
      ENNReal.ofReal (Rips.diameter d Finset.univ / 2) := by
  rw [dgm_eq_scale_rips k d p hd n]
  exact bottleneck_rips_scale_le k d n

/-- On the line, the Rips and Čech diagrams of one configuration are at
bottleneck distance at most half the carrier diameter. -/
theorem bottleneck_rips_cech_dgm_le_half_diameter_real (d : MetricSpace V)
    (q : V → ℝ) (hd : ∀ v w, d.dist v w = dist (q v) (q w)) (n : ℕ) :
    bottleneck (dgm k (Rips.filter d) n) (dgm k (Cech.filter q) n) ≤
      ENNReal.ofReal (Rips.diameter d Finset.univ / 2) := by
  rw [dgm_eq_scale_rips_real k d q hd n]
  exact bottleneck_rips_scale_le k d n

/-- The weighted-kernel embedding difference between one Rips diagram and its
sup-norm Čech diagram is bounded by the half-diameter bottleneck estimate. -/
theorem norm_diagramEmbedding_rips_sub_cech_le (d : MetricSpace V)
    (p : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ)
    (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w (dgm k (Rips.filter d) n) -
        WeightedKernel.diagramEmbedding σ w (dgm k (Cech.filter p) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.diameter d Finset.univ / 2) := by
  have hbound := bottleneck_rips_cech_dgm_le_half_diameter k d p hd n
  have hfinite : bottleneck (dgm k (Rips.filter d) n)
      (dgm k (Cech.filter p) n) < ⊤ := hbound.trans_lt ENNReal.ofReal_lt_top
  have hreal : (bottleneck (dgm k (Rips.filter d) n)
      (dgm k (Cech.filter p) n)).toReal ≤ Rips.diameter d Finset.univ / 2 := by
    simpa only [ENNReal.toReal_ofReal
      (div_nonneg (Rips.diameter_nonneg d Finset.univ) zero_le_two)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  exact (WeightedKernel.norm_diagramEmbedding_sub_le_card_mul_bottleneck σ hA hB w _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) hfinite).trans
      (mul_le_mul_of_nonneg_left hreal
        (mul_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (Nat.cast_nonneg _)))

/-- The Gaussian diagram kernel difference between one Rips diagram and its
sup-norm Čech diagram is bounded by the half-diameter estimate. -/
theorem abs_gaussianDiagramKernel_rips_sub_cech_le (d : MetricSpace V)
    (p : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ)
    (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ w D (dgm k (Rips.filter d) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (dgm k (Cech.filter p) n)| ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.diameter d Finset.univ / 2) := by
  have hbound := bottleneck_rips_cech_dgm_le_half_diameter k d p hd n
  have hfinite : bottleneck (dgm k (Rips.filter d) n)
      (dgm k (Cech.filter p) n) < ⊤ := hbound.trans_lt ENNReal.ofReal_lt_top
  have hreal : (bottleneck (dgm k (Rips.filter d) n)
      (dgm k (Cech.filter p) n)).toReal ≤ Rips.diameter d Finset.univ / 2 := by
    simpa only [ENNReal.toReal_ofReal
      (div_nonneg (Rips.diameter_nonneg d Finset.univ) zero_le_two)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  exact (WeightedKernel.abs_gaussianDiagramKernel_sub_le_card_mul_bottleneck σ τ hA hB w D _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) hfinite).trans
      (mul_le_mul_of_nonneg_left hreal
        (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (abs_nonneg τ)) (Nat.cast_nonneg _)))

/-- The finite-part persistence-image difference between one Rips diagram and
its sup-norm Čech diagram is bounded by the half-diameter estimate. -/
theorem norm_finiteDiagramImage_rips_sub_cech_le (d : MetricSpace V)
    (p : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ)
    {K : Type*} [Fintype K] {σ : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (P : K → Set (ℝ × ℝ))
    (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ w P (dgm k (Rips.filter d) n) -
        PersistenceImage.finiteDiagramImage σ w P (dgm k (Cech.filter p) n)‖ ≤
      PersistenceImage.stabilityConstant σ A B *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.diameter d Finset.univ / 2) := by
  have hbound := bottleneck_rips_cech_dgm_le_half_diameter k d p hd n
  have hfinite : bottleneck (dgm k (Rips.filter d) n)
      (dgm k (Cech.filter p) n) < ⊤ := hbound.trans_lt ENNReal.ofReal_lt_top
  have hreal : (bottleneck (dgm k (Rips.filter d) n)
      (dgm k (Cech.filter p) n)).toReal ≤ Rips.diameter d Finset.univ / 2 := by
    simpa only [ENNReal.toReal_ofReal
      (div_nonneg (Rips.diameter_nonneg d Finset.univ) zero_le_two)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  exact (PersistenceImage.norm_finiteDiagramImage_sub_le_card_mul_bottleneck hσ hA hB w P hm hdisj
    _ _ (dgm_isPositive k _ n) (dgm_isPositive k _ n) hfinite).trans
      (mul_le_mul_of_nonneg_left hreal
        (mul_nonneg (PersistenceImage.stabilityConstant_nonneg hσ hA hB)
          (Nat.cast_nonneg _)))

end TDA.Persistence.Cech
