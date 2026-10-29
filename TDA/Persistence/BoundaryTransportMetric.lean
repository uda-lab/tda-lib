import TDA.Persistence.BoundaryTransportNorm

/-! Sharp metric laws for native boundary transport of finite interior measures. -/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal ProbabilityTheory
namespace TDA.Persistence.BoundaryTransport

/-- Separation of finite original measures, with no persistence-moment hypothesis. -/
theorem boundaryTransportDistance_eq_zero_iff (p : ℝ) (hp : 1 ≤ p)
    (μ ν : Measure Interior) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    boundaryTransportDistance p μ ν = 0 ↔ μ = ν := by
  constructor
  · intro hzero
    let R : ℝ≥0∞ := μ univ + ν univ + 1
    have hRtop : R < ∞ := ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨measure_lt_top μ _, measure_lt_top ν _⟩, by simp⟩
    have hRpos : 0 < R := (zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le le_add_self
    have htotal : μ univ + ν univ ≤ R := le_self_add
    obtain ⟨γ, hγ₁, hγ₂, hcost⟩ :=
      exists_minimizing_reservoirPlan p (by linarith) μ ν R hRtop hRpos htotal
    have hnorm : eLpNorm (fun z : Space × Space => dist z.1 z.2)
        (ENNReal.ofReal p) γ = 0 := by
      rw [eLpNorm_dist_eq_collapsedPowerCost p (by linarith) γ, hcost,
        ← boundaryTransportPowerValue_eq_reservoirPowerValue p hp μ ν R hRtop htotal]
      exact hzero
    have hae : (fun z : Space × Space => dist z.1 z.2) =ᵐ[γ] 0 :=
      (eLpNorm_eq_zero_iff (p := ENNReal.ofReal p)
        (by fun_prop : AEStronglyMeasurable
          (fun z : Space × Space => dist z.1 z.2) γ)
        (ENNReal.ofReal_ne_zero_iff.mpr (by linarith))).mp hnorm
    have hcoord : Prod.fst =ᵐ[γ] Prod.snd := by
      filter_upwards [hae] with z hz
      exact (dist_eq_zero.mp hz)
    have hres : reservoirMeasure μ R = reservoirMeasure ν R := by
      calc
        reservoirMeasure μ R = γ.map Prod.fst := hγ₁.symm
        _ = γ.map Prod.snd := Measure.map_congr hcoord
        _ = reservoirMeasure ν R := hγ₂
    have hmap : μ.map Space.point = ν.map Space.point := by
      have hr := congrArg (fun η : Measure Space => η.restrict (Set.range Space.point)) hres
      simpa [reservoirMeasure_restrict_interior] using hr
    exact measurableEmbedding_point.map_injective hmap
  · rintro rfl
    exact boundaryTransportDistance_self p (by linarith) μ

private theorem glue_reservoirCouplings
    (π σ : Measure (Space × Space)) [IsFiniteMeasure π] [IsFiniteMeasure σ]
    (hmiddle : π.map Prod.snd = σ.map Prod.fst) :
    ∃ τ : Measure ((Space × Space) × Space),
      τ.map Prod.fst = π ∧
      τ.map (fun a => (a.1.2, a.2)) = σ := by
  let κ := σ.condKernel
  let τ : Measure ((Space × Space) × Space) :=
    π ⊗ₘ (κ.comap Prod.snd (measurable_snd : Measurable (Prod.snd : Space × Space → Space)))
  refine ⟨τ, ?_, ?_⟩
  · exact Measure.fst_compProd π (κ.comap Prod.snd (measurable_snd : Measurable (Prod.snd : Space × Space → Space)))
  · apply Measure.ext
    intro s hs
    rw [Measure.map_apply (by fun_prop : Measurable
      (fun a : (Space × Space) × Space => (a.1.2, a.2))) hs,
      Measure.compProd_apply (hs.preimage (by fun_prop))]
    have hmeas : Measurable (fun y : Space => κ y (Prod.mk y ⁻¹' s)) :=
      ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs
    have hsection (a : Space × Space) :
        (κ.comap Prod.snd (measurable_snd : Measurable (Prod.snd : Space × Space → Space))) a
          ((fun z : Space => (a, z)) ⁻¹' ((fun b : (Space × Space) × Space => (b.1.2, b.2)) ⁻¹' s)) =
        κ a.2 (Prod.mk a.2 ⁻¹' s) := rfl
    simp_rw [hsection]
    rw [← lintegral_map hmeas measurable_snd, hmiddle]
    calc
      (∫⁻ y, κ y (Prod.mk y ⁻¹' s) ∂σ.map Prod.fst) =
          (σ.fst ⊗ₘ σ.condKernel) s := (Measure.compProd_apply hs).symm
      _ = σ s := congrArg (fun η : Measure (Space × Space) => η s)
        (σ.disintegrate σ.condKernel)

/-- Sharp triangle inequality, using one reservoir capacity for all three finite inputs. -/
theorem boundaryTransportDistance_triangle (p : ℝ) (hp : 1 ≤ p)
    (μ ν ξ : Measure Interior)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    boundaryTransportDistance p μ ξ ≤
      boundaryTransportDistance p μ ν + boundaryTransportDistance p ν ξ := by
  let R : ℝ≥0∞ := μ univ + ν univ + ξ univ + 1
  have hRtop : R < ∞ := by
    simp only [R]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨measure_lt_top μ _, measure_lt_top ν _⟩,
       measure_lt_top ξ _⟩, by simp⟩
  have hRpos : 0 < R := (zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le le_add_self
  have hμν : μ univ + ν univ ≤ R := by
    calc
      μ univ + ν univ ≤ μ univ + ν univ + ξ univ := le_self_add
      _ ≤ R := le_self_add
  have hνξ : ν univ + ξ univ ≤ R := by
    calc
      ν univ + ξ univ ≤ ν univ + ξ univ + μ univ := le_self_add
      _ = μ univ + ν univ + ξ univ := by ac_rfl
      _ ≤ R := le_self_add
  have hμξ : μ univ + ξ univ ≤ R := by
    calc
      μ univ + ξ univ ≤ μ univ + ξ univ + ν univ := le_self_add
      _ = μ univ + ν univ + ξ univ := by ac_rfl
      _ ≤ R := le_self_add
  obtain ⟨π, hπ₁, hπ₂, hπcost⟩ :=
    exists_minimizing_reservoirPlan p (by linarith) μ ν R hRtop hRpos hμν
  obtain ⟨σ, hσ₁, hσ₂, hσcost⟩ :=
    exists_minimizing_reservoirPlan p (by linarith) ν ξ R hRtop hRpos hνξ
  have hπmass : π univ = R := by
    have h := congrArg (fun η : Measure Space => η univ) hπ₁
    simpa [Measure.map_apply measurable_fst MeasurableSet.univ,
      reservoirMeasure_mass μ R (le_self_add.trans hμν)] using h
  have hσmass : σ univ = R := by
    have h := congrArg (fun η : Measure Space => η univ) hσ₁
    simpa [Measure.map_apply measurable_fst MeasurableSet.univ,
      reservoirMeasure_mass ν R (le_self_add.trans hνξ)] using h
  obtain ⟨τ, hτxy, hτyz⟩ := @glue_reservoirCouplings π σ
    ⟨hπmass ▸ hRtop⟩ ⟨hσmass ▸ hRtop⟩ (hπ₂.trans hσ₁.symm)
  let γ : Measure (Space × Space) := τ.map (fun a => (a.1.1, a.2))
  have hγ₁ : γ.map Prod.fst = reservoirMeasure μ R := by
    dsimp only [γ]
    rw [Measure.map_map measurable_fst (by fun_prop)]
    have heq : (Prod.fst ∘ fun a : (Space × Space) × Space => (a.1.1, a.2)) =
        Prod.fst ∘ Prod.fst := rfl
    rw [heq, ← Measure.map_map measurable_fst measurable_fst, hτxy, hπ₁]
  have hγ₂ : γ.map Prod.snd = reservoirMeasure ξ R := by
    dsimp only [γ]
    rw [Measure.map_map measurable_snd (by fun_prop)]
    have heq : (Prod.snd ∘ fun a : (Space × Space) × Space => (a.1.1, a.2)) =
        Prod.snd ∘ (fun a : (Space × Space) × Space => (a.1.2, a.2)) := rfl
    rw [heq, ← Measure.map_map measurable_snd (by fun_prop), hτyz, hσ₂]
  let e : ℝ≥0∞ := ENNReal.ofReal p
  let dxy : (Space × Space) × Space → ℝ := fun a => dist a.1.1 a.1.2
  let dyz : (Space × Space) × Space → ℝ := fun a => dist a.1.2 a.2
  have hγcost : reservoirDistance p μ ξ R ≤
      eLpNorm (fun z : Space × Space => dist z.1 z.2) e γ := by
    dsimp only [e]
    rw [eLpNorm_dist_eq_collapsedPowerCost p (by linarith) γ]
    exact ENNReal.rpow_le_rpow
      (reservoirPowerValue_le_plan p μ ξ R γ hγ₁ hγ₂) (one_div_nonneg.mpr (by linarith))
  have hmono : eLpNorm (fun z : Space × Space => dist z.1 z.2) e γ ≤
      eLpNorm (dxy + dyz) e τ := by
    dsimp only [γ]
    rw [eLpNorm_map_measure
      (by fun_prop : AEStronglyMeasurable
        (fun z : Space × Space => dist z.1 z.2)
        (τ.map (fun a => (a.1.1, a.2))))
      (by fun_prop : AEMeasurable (fun a : (Space × Space) × Space => (a.1.1, a.2)) τ)]
    exact eLpNorm_mono_ae_real (Filter.Eventually.of_forall fun a => by
      simpa [dxy, dyz] using dist_triangle a.1.1 a.1.2 a.2)
  have hxy_norm : eLpNorm dxy e τ = reservoirDistance p μ ν R := by
    change eLpNorm ((fun z : Space × Space => dist z.1 z.2) ∘ Prod.fst) e τ = _
    rw [← eLpNorm_map_measure
      (by fun_prop : AEStronglyMeasurable
        (fun z : Space × Space => dist z.1 z.2) (τ.map Prod.fst))
      (by fun_prop : AEMeasurable Prod.fst τ), hτxy,
      eLpNorm_dist_eq_collapsedPowerCost p (by linarith), hπcost]
    rfl
  have hyz_norm : eLpNorm dyz e τ = reservoirDistance p ν ξ R := by
    change eLpNorm ((fun z : Space × Space => dist z.1 z.2) ∘
      (fun a : (Space × Space) × Space => (a.1.2, a.2))) e τ = _
    rw [← eLpNorm_map_measure
      (by fun_prop : AEStronglyMeasurable
        (fun z : Space × Space => dist z.1 z.2)
          (τ.map (fun a => (a.1.2, a.2))))
      (by fun_prop : AEMeasurable (fun a : (Space × Space) × Space => (a.1.2, a.2)) τ),
      hτyz, eLpNorm_dist_eq_collapsedPowerCost p (by linarith), hσcost]
    rfl
  calc
    boundaryTransportDistance p μ ξ = reservoirDistance p μ ξ R :=
      boundaryTransportDistance_eq_reservoirDistance p hp μ ξ R hRtop hμξ
    _ ≤ eLpNorm (fun z : Space × Space => dist z.1 z.2) e γ := hγcost
    _ ≤ eLpNorm (dxy + dyz) e τ := hmono
    _ ≤ eLpNorm dxy e τ + eLpNorm dyz e τ :=
      eLpNorm_add_le (by fun_prop) (by fun_prop)
        (by simpa [e] using (ENNReal.ofReal_le_ofReal hp))
    _ = boundaryTransportDistance p μ ν + boundaryTransportDistance p ν ξ := by
      rw [hxy_norm, hyz_norm,
        ← boundaryTransportDistance_eq_reservoirDistance p hp μ ν R hRtop hμν,
        ← boundaryTransportDistance_eq_reservoirDistance p hp ν ξ R hRtop hνξ]

end TDA.Persistence.BoundaryTransport
