import TDA.Persistence.RipsSampling
import TDA.Persistence.RipsGromovHausdorffExamples
import TDA.Persistence.EssentialVanishing
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Concrete atomic examples of sampled Rips laws and the vanishing-mass input. -/

noncomputable section
namespace TDA.Persistence.RipsSamplingExamples

open TDA.Probability TDA.Persistence.Rips
open scoped ENNReal NNReal

/-- The two nonnegative masses are allowed to reach zero at either endpoint. -/
def twoPointWeights (ε : ℝ≥0) (hε : ε ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ((if b then ε else 1 - ε : ℝ≥0) : ℝ≥0∞)) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le hε]
    rfl)

/-- Points at distance one, with masses `1-ε` and `ε`. -/
def twoPointLaw (ε : ℝ≥0) (hε : ε ≤ 1) : PMF ℝ :=
  (twoPointWeights ε hε).map (fun b => if b then (1 : ℝ) else 0)

/-- The two-draw moment is `2ε(1-ε)` for every positive exponent. Thus the
whole-support diagram cannot replace the sampled diagram law in a GW estimate. -/
theorem twoPoint_gromovWasserstein_singleton (ε : ℝ≥0) (hε : ε ≤ 1)
    {p : ℝ} (hp : 0 < p) :
    gromovWasserstein p (twoPointLaw ε hε) (PMF.pure (() : Unit)) =
      (2 : ℝ≥0∞)⁻¹ * (2 * (ε : ℝ≥0∞) * ((1 - ε : ℝ≥0) : ℝ≥0∞)) ^ p⁻¹ := by
  rw [gromovWasserstein_of_subsingleton]
  simp only [twoPointLaw, expectation_map]
  congr 2
  simp [expectation, tsum_fintype, Fintype.sum_bool, twoPointWeights, PMF.ofFintype_apply,
    Real.dist_eq, ENNReal.zero_rpow_of_pos hp, mul_comm, mul_left_comm, mul_assoc]
  ring

/-- The sharp law theorem applies to this weighted nonuniform input, with a
one-point target, in positive degree and with iid replacement. -/
theorem weighted_twoPoint_sampleLaw_bound (ε : ℝ≥0) (hε : ε ≤ 1)
    {p : ℝ} (hp : 1 ≤ p) (n degree : ℕ) (hn : 2 ≤ n) :
    wasserstein p bottleneck
      (sampleLaw (ZMod 2) (twoPointLaw ε hε) n (degree + 1))
      (sampleLaw (ZMod 2) (PMF.pure (() : Unit)) n (degree + 1)) ≤
      (n.choose 2 : ℝ≥0∞) ^ p⁻¹ *
        (2 * gromovWasserstein p (twoPointLaw ε hε)
          (PMF.pure (() : Unit))) :=
  wasserstein_sampleLaw_le_gromovWasserstein (ZMod 2)
    (twoPointLaw ε hε) (PMF.pure (() : Unit)) hp n degree hn

/-- The all-degree law theorem applies to the same weighted input and one-point
target at degree zero, where the diagrams are the full H₀ diagrams. For two
draws, the source law then has the full-H₀ atom of exact mass `2ε(1-ε)`
(`epsilonTwoPoint_realSampleLaw_nontrivial_mass`). -/
theorem weighted_twoPoint_sampleLaw_bound_degreeZero (ε : ℝ≥0) (hε : ε ≤ 1)
    {p : ℝ} (hp : 1 ≤ p) (n : ℕ) (hn : 2 ≤ n) :
    wasserstein p bottleneck
      (sampleLaw (ZMod 2) (twoPointLaw ε hε) n 0)
      (sampleLaw (ZMod 2) (PMF.pure (() : Unit)) n 0) ≤
      (n.choose 2 : ℝ≥0∞) ^ p⁻¹ *
        (2 * gromovWasserstein p (twoPointLaw ε hε)
          (PMF.pure (() : Unit))) :=
  wasserstein_sampleLaw_le_gromovWasserstein_allDegrees (ZMod 2)
    (twoPointLaw ε hε) (PMF.pure (() : Unit)) hp n 0 hn

section EpsilonRegression

open TDA.Filtration.Cech.Examples
open TDA.Filtration.Cech.Examples.TwoPoints
open TDA.Persistence.Rips.GromovHausdorffExamples
open TDA.Filtration

local instance epsilonFinTwoMetric : MetricSpace (Fin 2) := TwoPoints.metric

private def epsilonPointBase (b : Bool) : ℝ := if b then 2 else 0

private def epsilonPointUnit (b : Bool) : ℝ := if b then 1 else 0

/-- The metric on `Bool` induced by placing its two points at `0` and `1` in `ℝ`.
This is the finite metric model used by the ε-weighted two-point sample fixture. -/
abbrev epsilonTwoPointMetric : MetricSpace Bool :=
  MetricSpace.induced (fun b => if b then (1 : ℝ) else 0)
    (by
      intro b c h
      cases b <;> cases c <;> simp_all)
    inferInstance

private theorem epsilonPointBase_injective : Function.Injective epsilonPointBase := by
  intro b c h
  cases b <;> cases c <;> simp_all [epsilonPointBase]

private abbrev epsilonBaseMetric : MetricSpace Bool :=
  MetricSpace.induced epsilonPointBase epsilonPointBase_injective inferInstance

local instance epsilonUnitMetric : MetricSpace Bool :=
  epsilonTwoPointMetric

private theorem epsilonUnitMetric_dist (b c : Bool) :
    epsilonUnitMetric.dist b c = (1 / 2 : ℝ) * epsilonBaseMetric.dist b c := by
  change dist (epsilonPointUnit b) (epsilonPointUnit c) =
    (1 / 2 : ℝ) * dist (epsilonPointBase b) (epsilonPointBase c)
  cases b <;> cases c <;>
    norm_num [epsilonPointUnit, epsilonPointBase, Real.dist_eq]

private theorem rips_diameter_scale {V : Type*} (d e : MetricSpace V) (c : ℝ)
    (hc : 0 < c) (hdist : ∀ x y, e.dist x y = c * d.dist x y)
    (s : Finset V) :
    Rips.diameter e s = c * Rips.diameter d s := by
  apply le_antisymm
  · apply (Rips.diameter_le_iff e s _).2
    refine ⟨mul_nonneg hc.le (Rips.diameter_nonneg d s), ?_⟩
    intro x hx y hy
    rw [hdist]
    exact mul_le_mul_of_nonneg_left (Rips.dist_le_diameter d hx hy) hc.le
  · have hbase : Rips.diameter d s ≤ c⁻¹ * Rips.diameter e s := by
      apply (Rips.diameter_le_iff d s _).2
      refine ⟨mul_nonneg (inv_nonneg.mpr hc.le) (Rips.diameter_nonneg e s), ?_⟩
      intro x hx y hy
      have hdist' : d.dist x y = c⁻¹ * e.dist x y := by
        rw [hdist]
        field_simp
      rw [hdist']
      exact mul_le_mul_of_nonneg_left (Rips.dist_le_diameter e hx hy)
        (inv_nonneg.mpr hc.le)
    calc
      c * Rips.diameter d s ≤ c * (c⁻¹ * Rips.diameter e s) :=
        mul_le_mul_of_nonneg_left hbase hc.le
      _ = Rips.diameter e s := by field_simp

private theorem epsilonUnitFilter_eq_scale :
    Rips.filter epsilonUnitMetric =
      (Rips.filter epsilonBaseMetric).scale (1 / 2) (by norm_num) := by
  ext s
  rw [Rips.filter_value, FilterFunction.scale_value, Rips.filter_value,
    rips_diameter_scale epsilonBaseMetric epsilonUnitMetric (1 / 2) (by norm_num)
      epsilonUnitMetric_dist]

private def boolFinTwo : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := if i = 1 then true else false
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem epsilonBaseDgm_eq_twoPoints :
    dgm (ZMod 2) (Rips.filter epsilonBaseMetric) 0 = diagram (ZMod 2) (Fin 2) 0 := by
  letI : MetricSpace Bool := epsilonBaseMetric
  let e : Bool ≃ᵢ Fin 2 :=
    { boolFinTwo with
      isometry_toFun := Isometry.of_dist_eq (by
        intro b c
        change dist (TwoPoints.pts (boolFinTwo b)) (TwoPoints.pts (boolFinTwo c)) =
          dist (epsilonPointBase b) (epsilonPointBase c)
        cases b <;> cases c <;>
          norm_num [boolFinTwo, epsilonPointBase, TwoPoints.pts, Real.dist_eq]) }
  rw [diagram_eq_dgm]
  exact dgm_eq_of_isometryEquiv (ZMod 2) e 0

/-- The two-point Rips diagram has an essential component and a finite H₀ bar
dying at distance one. -/
theorem epsilonTwoPoint_fullH0_points :
    (diagram (ZMod 2) Bool 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), ((0 : ℝ), ((1 : ℝ) : WithTop ℝ))} := by
  rw [diagram_eq_dgm]
  rw [epsilonUnitFilter_eq_scale, dgm_scale, epsilonBaseDgm_eq_twoPoints]
  rw [Diagram.scale, Diagram.map_points]
  rw [two_points_diagram]
  norm_num [scaleFinitePair]

end EpsilonRegression

section NontrivialLaw

open TDA.Persistence.Rips.GromovHausdorffExamples
open TDA.Persistence TDA.Filtration

local instance : MetricSpace (Fin 2) := TDA.Filtration.Cech.Examples.TwoPoints.metric
local instance : MetricSpace (Fin 1) :=
  MetricSpace.induced (fun _ : Fin 1 => (0 : ℝ))
    (fun a b _ => Subsingleton.elim a b) inferInstance

/-- Equal positive masses on the two points at distance two. -/
def uniformTwoPoints : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => (2 : ℝ≥0∞)⁻¹) (by
    simp only [Fin.sum_univ_two, ← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- The ordered two-draw tuple visiting both points. -/
def distinctDraws : Fin 2 → Fin 2 := Fin.cons 0 (Fin.cons 1 Fin.elim0)

/-- Two different draws retain both the essential H₀ occurrence and the
finite bar dying at the edge's diameter time. -/
theorem distinctDraws_fullH0_points :
    (sampleDiagram (ZMod 2) distinctDraws 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), (0, ((2 : ℝ) : WithTop ℝ))} := by
  rw [sampleDiagram_eq_diagram_of_surjective (ZMod 2) distinctDraws (by
    intro i
    fin_cases i <;> simp [distinctDraws]) 0]
  exact two_points_diagram

/-- A one-point Rips sample has exactly its essential H₀ occurrence. -/
theorem singleton_fullH0_points :
    (diagram (ZMod 2) (Fin 1) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ))} := by
  rw [diagram_eq_dgm]
  let d : MetricSpace (Fin 1) := inferInstance
  let D := dgm (ZMod 2) (Rips.filter d) 0
  have hd0 : Rips.diameter d (Finset.univ : Finset (Fin 1)) = 0 := by
    rw [show (Finset.univ : Finset (Fin 1)) = {0} by decide]
    exact Rips.diameter_singleton d 0
  have hfin : finitePart D.points = 0 := by
    have h := card_finiteOccurrences_dgm_fullComplex_le (ZMod 2) (Rips.filter d) 0
    apply Multiset.card_eq_zero.mp
    have hc : Fintype.card D.finiteOccurrences = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [D] using h
    simpa only [Multiset.card_coe] using hc
  have hess : essentialPart D.points = {0} := by
    have hc := Rips.card_essentialPart_dgm_zero (ZMod 2) d
    obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hc
    have hbmem : b ∈ essentialPart D.points := by rw [hb]; simp
    have hbounds := (Rips.dgm_coordinates_le_diameter (ZMod 2) d 0).2 b hbmem
    have hb0 : b = 0 := by linarith [hd0]
    simpa [hb0] using hb
  have h := parts_reconstruct D.points
  simpa only [hfin, hess, Multiset.map_zero, Multiset.map_singleton, zero_add] using h.symm

/-- Two equal ordered draws, parameterized by the point drawn. -/
def repeatedDraws (b : Fin 2) : Fin 2 → Fin 2 := fun _ => b

/-- Repetition collapses to a one-point metric sample. -/
theorem repeatedDraws_diagram_eq_singleton (b : Fin 2) :
    sampleDiagram (ZMod 2) (repeatedDraws b) 0 = diagram (ZMod 2) (Fin 1) 0 := by
  let t : Fin 2 → Fin 2 := repeatedDraws b
  letI : Subsingleton (Sample t) := ⟨by
    intro a c
    apply Subtype.ext
    rcases a.property with ⟨i, hi⟩
    rcases c.property with ⟨j, hj⟩
    simpa [t, repeatedDraws] using hi.symm.trans hj⟩
  let e : Sample t ≃ᵢ Fin 1 :=
    { Equiv.ofBijective (fun _ : Sample t => (0 : Fin 1))
        ⟨fun a c _ => Subsingleton.elim a c,
         fun y => ⟨sampleProjection t 0, Subsingleton.elim _ y⟩⟩ with
      isometry_toFun := by
        intro a c
        have hac : a = c := Subsingleton.elim a c
        subst c
        simp }
  exact diagram_eq_of_isometryEquiv (ZMod 2) e 0

/-- Equal draws retain the sole essential H₀ occurrence. -/
theorem repeatedDraws_fullH0_points (b : Fin 2) :
    (sampleDiagram (ZMod 2) (repeatedDraws b) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ))} := by
  rw [repeatedDraws_diagram_eq_singleton b]
  exact singleton_fullH0_points

private theorem mass_ge_half_of_two_orders (D : Diagram ℝ) (y₀ y₁ : Fin 2)
    (h₀ : sampleDiagram (ZMod 2)
      (Fin.cons (0 : Fin 2) (Fin.cons y₀ Fin.elim0)) 0 = D)
    (h₁ : sampleDiagram (ZMod 2)
      (Fin.cons (1 : Fin 2) (Fin.cons y₁ Fin.elim0)) 0 = D) :
    (2 : ℝ≥0∞)⁻¹ ≤ (sampleLaw (ZMod 2) uniformTwoPoints 2 0) D := by
  classical
  have hmass : expectation (sampleLaw (ZMod 2) uniformTwoPoints 2 0)
      (fun E => if E = D then 1 else 0) =
      (sampleLaw (ZMod 2) uniformTwoPoints 2 0) D := by
    simp [expectation]
  rw [← hmass]
  unfold sampleLaw
  rw [expectation_map]
  rw [iid_succ, expectation_bind]
  simp only [expectation_map, iid_succ, expectation_bind, iid_zero, expectation_pure]
  unfold expectation
  simp only [tsum_fintype]
  rw [Fin.sum_univ_two]
  calc
    (2 : ℝ≥0∞)⁻¹ = uniformTwoPoints 0 * (uniformTwoPoints y₀ *
        if (sampleDiagram (ZMod 2)
          (Fin.cons (0 : Fin 2) (Fin.cons y₀ Fin.elim0)) 0) = D
          then 1 else 0) + uniformTwoPoints 1 * (uniformTwoPoints y₁ *
        if (sampleDiagram (ZMod 2)
          (Fin.cons (1 : Fin 2) (Fin.cons y₁ Fin.elim0)) 0) = D
          then 1 else 0) := by
      simp only [h₀, h₁, ↓reduceIte, mul_one, uniformTwoPoints, PMF.ofFintype_apply]
      calc
        (2 : ℝ≥0∞)⁻¹ = 2 * (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
          simp
        _ = (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ +
            (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by ring
    _ ≤ uniformTwoPoints 0 * (∑ x_1 : Fin 2, uniformTwoPoints x_1 *
        if (sampleDiagram (ZMod 2)
          (Fin.cons (0 : Fin 2) (Fin.cons x_1 Fin.elim0)) 0) = D
          then 1 else 0) + uniformTwoPoints 1 * (∑ x_1 : Fin 2, uniformTwoPoints x_1 *
        if (sampleDiagram (ZMod 2)
          (Fin.cons (1 : Fin 2) (Fin.cons x_1 Fin.elim0)) 0) = D
          then 1 else 0) := by
      gcongr
      · simpa only [tsum_fintype] using (ENNReal.le_tsum (f := fun x_1 : Fin 2 =>
          uniformTwoPoints x_1 * if (sampleDiagram (ZMod 2)
            (Fin.cons (0 : Fin 2) (Fin.cons x_1 Fin.elim0)) 0) = D
            then 1 else 0) y₀)
      · simpa only [tsum_fintype] using (ENNReal.le_tsum (f := fun x_1 : Fin 2 =>
          uniformTwoPoints x_1 * if (sampleDiagram (ZMod 2)
            (Fin.cons (1 : Fin 2) (Fin.cons x_1 Fin.elim0)) 0) = D
            then 1 else 0) y₁)

/-- At least half of the two-draw law is concentrated at the nontrivial full
H₀ diagram. The two orders of the distinct draws each contribute one quarter. -/
theorem uniformTwoPoints_nontrivial_fullH0_mass :
    (2 : ℝ≥0∞)⁻¹ ≤
      (sampleLaw (ZMod 2) uniformTwoPoints 2 0) (diagram (ZMod 2) (Fin 2) 0) := by
  apply mass_ge_half_of_two_orders _ 1 0
  · change sampleDiagram (ZMod 2) distinctDraws 0 = _
    exact sampleDiagram_eq_diagram_of_surjective (ZMod 2) distinctDraws (by
      intro i
      fin_cases i <;> simp [distinctDraws]) 0
  · exact sampleDiagram_eq_diagram_of_surjective (ZMod 2)
      (Fin.cons (1 : Fin 2) (Fin.cons 0 Fin.elim0)) (by
        intro i
        fin_cases i <;> simp) 0

/-- The other two ordered outcomes both have the singleton diagram, also with
probability at least one half. -/
theorem uniformTwoPoints_singleton_fullH0_mass :
    (2 : ℝ≥0∞)⁻¹ ≤
      (sampleLaw (ZMod 2) uniformTwoPoints 2 0) (diagram (ZMod 2) (Fin 1) 0) := by
  apply mass_ge_half_of_two_orders _ 0 1
  · have ht : (Fin.cons (0 : Fin 2) (Fin.cons 0 Fin.elim0) : Fin 2 → Fin 2) =
        repeatedDraws 0 := by
      funext i
      fin_cases i <;> rfl
    exact (congrArg (fun t : Fin 2 → Fin 2 => sampleDiagram (ZMod 2) t 0) ht).trans
      (repeatedDraws_diagram_eq_singleton 0)
  · have ht : (Fin.cons (1 : Fin 2) (Fin.cons 1 Fin.elim0) : Fin 2 → Fin 2) =
        repeatedDraws 1 := by
      funext i
      fin_cases i <;> rfl
    exact (congrArg (fun t : Fin 2 → Fin 2 => sampleDiagram (ZMod 2) t 0) ht).trans
      (repeatedDraws_diagram_eq_singleton 1)

/-- The two sampled full H₀ diagrams have different occurrence counts. -/
theorem distinctDraws_ne_repeatedDraws :
    sampleDiagram (ZMod 2) distinctDraws 0 ≠
      sampleDiagram (ZMod 2) (repeatedDraws 0) 0 := by
  intro h
  have hc := congrArg (fun D : Diagram ℝ => D.points.card) h
  rw [distinctDraws_fullH0_points, repeatedDraws_fullH0_points] at hc
  norm_num at hc

/-- The iid two-point H₀ sample law has two distinct atoms of positive mass. -/
theorem uniformTwoPoints_sampleLaw_nonconstant :
    ∃ D E : Diagram ℝ, D ≠ E ∧
      0 < (sampleLaw (ZMod 2) uniformTwoPoints 2 0) D ∧
      0 < (sampleLaw (ZMod 2) uniformTwoPoints 2 0) E := by
  refine ⟨diagram (ZMod 2) (Fin 2) 0, diagram (ZMod 2) (Fin 1) 0, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun D : Diagram ℝ => D.points.card) h
    rw [two_points_diagram, singleton_fullH0_points] at hc
    norm_num at hc
  · exact lt_of_lt_of_le (by norm_num) uniformTwoPoints_nontrivial_fullH0_mass
  · exact lt_of_lt_of_le (by norm_num) uniformTwoPoints_singleton_fullH0_mass

end NontrivialLaw

section EpsilonSampleLaw

open Filter
open scoped _root_.Topology

/-- The one-point metric on the singleton sample used in the bottleneck comparison. -/
abbrev epsilonSingletonMetric : MetricSpace (Fin 1) :=
  MetricSpace.induced (fun _ : Fin 1 => (0 : ℝ))
    (fun a b _ => Subsingleton.elim a b) inferInstance

local instance epsilonSamplingMetric : MetricSpace Bool :=
  epsilonTwoPointMetric

local instance epsilonSamplingSingletonMetric : MetricSpace (Fin 1) :=
  epsilonSingletonMetric

private theorem epsilonPointUnit_isometry : Isometry epsilonPointUnit := by
  intro b c
  change edist (epsilonPointUnit b) (epsilonPointUnit c) = edist b c
  rfl

/-- Both atoms of the weighted two-point input have positive mass exactly when
`ε` lies strictly between zero and one. -/
theorem twoPointWeights_fullSupport (ε : ℝ≥0) (hε : ε ≤ 1)
    (hεpos : 0 < ε) (hεlt : ε < 1) :
    0 < twoPointWeights ε hε false ∧ 0 < twoPointWeights ε hε true := by
  constructor
  · change 0 < ((1 - ε : ℝ≥0) : ℝ≥0∞)
    exact ENNReal.coe_pos.mpr (tsub_pos_of_lt hεlt)
  · change 0 < (ε : ℝ≥0∞)
    exact ENNReal.coe_pos.mpr hεpos

/-- The real-valued input law has the prescribed masses at its two support points. -/
theorem twoPointLaw_atom_masses (ε : ℝ≥0) (hε : ε ≤ 1) :
    twoPointLaw ε hε 0 = ((1 - ε : ℝ≥0) : ℝ≥0∞) ∧
    twoPointLaw ε hε 1 = (ε : ℝ≥0∞) := by
  constructor <;>
    simp [twoPointLaw, PMF.map_apply, tsum_fintype, twoPointWeights,
      PMF.ofFintype_apply]

/-- The real-valued two-point input has full support for `0 < ε < 1`. -/
theorem twoPointLaw_fullSupport (ε : ℝ≥0) (hε : ε ≤ 1)
    (hεpos : 0 < ε) (hεlt : ε < 1) :
    0 < twoPointLaw ε hε 0 ∧ 0 < twoPointLaw ε hε 1 := by
  rcases twoPointLaw_atom_masses ε hε with ⟨h0, h1⟩
  rw [h0, h1]
  exact ⟨ENNReal.coe_pos.mpr (tsub_pos_of_lt hεlt), ENNReal.coe_pos.mpr hεpos⟩

private def epsilonRepeatedDraws (b : Bool) : Fin 2 → Bool := fun _ => b

private def epsilonTwoDraws (b c : Bool) : Fin 2 → Bool :=
  Fin.cons b (Fin.cons c Fin.elim0)

private theorem epsilonRepeatedDraws_diagram_eq_singleton (b : Bool) :
    sampleDiagram (ZMod 2) (epsilonRepeatedDraws b) 0 = diagram (ZMod 2) (Fin 1) 0 := by
  let t : Fin 2 → Bool := epsilonRepeatedDraws b
  letI : Subsingleton (Sample t) := ⟨by
    intro a c
    apply Subtype.ext
    rcases a.property with ⟨i, hi⟩
    rcases c.property with ⟨j, hj⟩
    simpa [t, epsilonRepeatedDraws] using hi.symm.trans hj⟩
  let e : Sample t ≃ᵢ Fin 1 :=
    { Equiv.ofBijective (fun _ : Sample t => (0 : Fin 1))
        ⟨fun a c _ => Subsingleton.elim a c,
         fun y => ⟨sampleProjection t 0, Subsingleton.elim _ y⟩⟩ with
      isometry_toFun := by
        intro a c
        have hac : a = c := Subsingleton.elim a c
        subst c
        simp }
  exact diagram_eq_of_isometryEquiv (ZMod 2) e 0

private theorem epsilonTwoDraws_diagram (b c : Bool) :
    sampleDiagram (ZMod 2) (Fin.cons b (Fin.cons c Fin.elim0)) 0 =
      if b = c then diagram (ZMod 2) (Fin 1) 0 else diagram (ZMod 2) Bool 0 := by
  cases b <;> cases c
  · have h : epsilonTwoDraws false false = epsilonRepeatedDraws false := by
      funext i
      fin_cases i <;> rfl
    change sampleDiagram (ZMod 2)
      (Fin.cons false (Fin.cons false Fin.elim0)) 0 = _
    rw [show Fin.cons false (Fin.cons false Fin.elim0) = epsilonRepeatedDraws false by
      funext i
      fin_cases i <;> rfl, if_pos rfl]
    exact epsilonRepeatedDraws_diagram_eq_singleton false
  · have h : Function.Surjective (epsilonTwoDraws false true) := by
      intro x
      cases x
      · exact ⟨0, by simp [epsilonTwoDraws]⟩
      · exact ⟨1, by simp [epsilonTwoDraws]⟩
    rw [if_neg (by decide)]
    exact sampleDiagram_eq_diagram_of_surjective (ZMod 2) _ h 0
  · have h : Function.Surjective (epsilonTwoDraws true false) := by
      intro x
      cases x
      · exact ⟨1, by simp [epsilonTwoDraws]⟩
      · exact ⟨0, by simp [epsilonTwoDraws]⟩
    rw [if_neg (by decide)]
    exact sampleDiagram_eq_diagram_of_surjective (ZMod 2) _ h 0
  · have h : epsilonTwoDraws true true = epsilonRepeatedDraws true := by
      funext i
      fin_cases i <;> rfl
    change sampleDiagram (ZMod 2)
      (Fin.cons true (Fin.cons true Fin.elim0)) 0 = _
    rw [show Fin.cons true (Fin.cons true Fin.elim0) = epsilonRepeatedDraws true by
      funext i
      fin_cases i <;> rfl, if_pos rfl]
    exact epsilonRepeatedDraws_diagram_eq_singleton true

private theorem epsilon_bar_diagonalCost :
    diagonalCost ((0 : ℝ), (1 : ℝ)) = (2 : ℝ≥0∞)⁻¹ := by
  rw [diagonalCost]
  have hreal : |(1 : ℝ) - 0| / 2 = (2 : ℝ)⁻¹ := by norm_num
  rw [hreal, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The nontrivial full H₀ diagram and the singleton diagram are separated by
exactly half the finite bar's lifetime. -/
theorem epsilonTwoPoint_bottleneck_singleton :
    bottleneck (diagram (ZMod 2) Bool 0) (diagram (ZMod 2) (Fin 1) 0) =
      (2 : ℝ≥0∞)⁻¹ := by
  classical
  let x : Fin 1 → ℝ × ℝ := fun _ => ((0 : ℝ), (1 : ℝ))
  let y : Fin 0 → ℝ × ℝ := Fin.elim0
  let b : Fin 1 → ℝ := fun _ => 0
  let D : Diagram ℝ := orderedQ 1 1 (x, b)
  let E : Diagram ℝ := orderedQ 0 1 (y, b)
  have hD : diagram (ZMod 2) Bool 0 = D := by
    apply Diagram.ext
    rw [epsilonTwoPoint_fullH0_points]
    simp [D, x, b, orderedQ, List.ofFn_succ]
    change ((0 : ℝ), (⊤ : WithTop ℝ)) ::ₘ
        (((0 : ℝ), ((1 : ℝ) : WithTop ℝ)) ::ₘ 0) =
      ((0 : ℝ), ((1 : ℝ) : WithTop ℝ)) ::ₘ
        (((0 : ℝ), (⊤ : WithTop ℝ)) ::ₘ 0)
    exact Multiset.cons_swap _ _ _
  have hE : diagram (ZMod 2) (Fin 1) 0 = E := by
    apply Diagram.ext
    rw [singleton_fullH0_points]
    simp [E, y, b, orderedQ, List.ofFn_succ]
  have hfD : (Finset.univ : Finset (Fin 1)).val.map x = finitePart D.points := by
    change (Finset.univ : Finset (Fin 1)).val.map x =
      finitePart (orderedQ 1 1 (x, b)).points
    rw [finitePart_orderedQ]
    simp [x]
  have hfE : (Finset.univ : Finset (Fin 0)).val.map y = finitePart E.points := by
    change (Finset.univ : Finset (Fin 0)).val.map y =
      finitePart (orderedQ 0 1 (y, b)).points
    rw [finitePart_orderedQ]
    simp [y]
  have heD : (Finset.univ : Finset (Fin 1)).val.map b = essentialPart D.points := by
    change (Finset.univ : Finset (Fin 1)).val.map b =
      essentialPart (orderedQ 1 1 (x, b)).points
    rw [essentialPart_orderedQ]
    simp [b]
  have heE : (Finset.univ : Finset (Fin 1)).val.map b = essentialPart E.points := by
    change (Finset.univ : Finset (Fin 1)).val.map b =
      essentialPart (orderedQ 0 1 (y, b)).points
    rw [essentialPart_orderedQ]
    simp [b]
  rw [hD, hE, bottleneck_eq_presentation D E x y b b hfD hfE heD heE]
  let M : OccurrenceMatching (Fin 1) (Fin 0) (Fin 1) (Fin 1) :=
    { finite := fun _ => none
      finite_injective := by simp
      essential := Equiv.refl _ }
  have hupper : presentationBottleneck
      (fun _ : Fin 1 => ((0 : ℝ), (1 : ℝ)))
      (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) ≤
      (2 : ℝ≥0∞)⁻¹ := by
    calc
      _ ≤ M.cost x y b b := presentationBottleneck_le_cost x y b b M
      _ = (2 : ℝ≥0∞)⁻¹ := by
        simp [M, OccurrenceMatching.cost, essentialPairCost, x, y, b]
        exact epsilon_bar_diagonalCost
  have hlower : (2 : ℝ≥0∞)⁻¹ ≤ presentationBottleneck
      (fun _ : Fin 1 => ((0 : ℝ), (1 : ℝ)))
      (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) := by
    have hhalf : (2 : ℝ≥0∞)⁻¹ = diagonalCost ((0 : ℝ), (1 : ℝ)) := by
      exact epsilon_bar_diagonalCost.symm
    apply le_iInf
    intro M
    unfold OccurrenceMatching.cost
    apply le_trans ?_ (le_max_left _ _)
    have h := Finset.le_sup (s := (Finset.univ : Finset (Fin 1)))
      (f := fun i => match M.finite i with
        | some j => finitePairCost (x i) (y j)
        | none => diagonalCost (x i))
      (Finset.mem_univ (0 : Fin 1))
    rw [hhalf]
    cases hm : M.finite 0 with
    | none =>
        simp [hm, x, diagonalCost]
    | some j => exact Fin.elim0 j
  exact le_antisymm hupper hlower

private theorem epsilonSingleton_ne_twoPoint :
    diagram (ZMod 2) (Fin 1) 0 ≠ diagram (ZMod 2) Bool 0 := by
  intro h
  have hc := congrArg (fun D : Diagram ℝ => D.points.card) h
  rw [singleton_fullH0_points, epsilonTwoPoint_fullH0_points] at hc
  norm_num at hc

/-- In two iid draws, the diagram with the finite H₀ bar occurs exactly when
the two positive-mass points are both sampled, with mass `2ε(1-ε)`. -/
theorem epsilonTwoPoint_sampleLaw_nontrivial_mass (ε : ℝ≥0) (hε : ε ≤ 1) :
    (sampleLaw (ZMod 2) (twoPointWeights ε hε) 2 0) (diagram (ZMod 2) Bool 0) =
      (2 : ℝ≥0∞) * (ε : ℝ≥0∞) * ((1 - ε : ℝ≥0) : ℝ≥0∞) := by
  classical
  let μ := twoPointWeights ε hε
  let D := diagram (ZMod 2) Bool 0
  have hmass : expectation (sampleLaw (ZMod 2) μ 2 0)
      (fun E => if E = D then 1 else 0) = (sampleLaw (ZMod 2) μ 2 0) D := by
    simp [expectation]
  rw [← hmass]
  unfold sampleLaw
  rw [expectation_map, iid_succ, expectation_bind]
  simp only [expectation_map, iid_succ, expectation_bind, iid_zero, expectation_pure]
  simp [expectation, tsum_fintype, epsilonTwoDraws_diagram,
    epsilonSingleton_ne_twoPoint, twoPointWeights, PMF.ofFintype_apply, μ, D]
  ring

/-- The actual real-valued two-point sample law has the same exact rare atom
as its Bool metric chart, transported by the isometric coordinate map `0,1`. -/
theorem epsilonTwoPoint_realSampleLaw_nontrivial_mass (ε : ℝ≥0) (hε : ε ≤ 1) :
    (sampleLaw (ZMod 2) (twoPointLaw ε hε) 2 0) (diagram (ZMod 2) Bool 0) =
      (2 : ℝ≥0∞) * (ε : ℝ≥0∞) * ((1 - ε : ℝ≥0) : ℝ≥0∞) := by
  rw [show twoPointLaw ε hε = (twoPointWeights ε hε).map epsilonPointUnit by rfl]
  rw [sampleLaw_map_isometry (ZMod 2) (twoPointWeights ε hε) epsilonPointUnit
    epsilonPointUnit_isometry 2 0]
  exact epsilonTwoPoint_sampleLaw_nontrivial_mass ε hε

/-- The exact rare-atom mass tends to zero as the second point's weight tends to zero. -/
theorem epsilonTwoPoint_sampleLaw_nontrivial_mass_tendsto_zero :
    Tendsto (fun ε : ℝ≥0 =>
      (2 : ℝ≥0∞) * (ε : ℝ≥0∞) * ((1 - ε : ℝ≥0) : ℝ≥0∞))
      (𝓝 0) (𝓝 0) := by
  let f : ℝ≥0 → ℝ≥0∞ := fun ε =>
    (2 : ℝ≥0∞) * (ε : ℝ≥0∞) * ((1 - ε : ℝ≥0) : ℝ≥0∞)
  have hcoe : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
    simpa only [ENNReal.coe_zero] using
      (ENNReal.continuous_coe.continuousAt (x := 0)).tendsto
  have hupper : Tendsto (fun ε : ℝ≥0 => (2 : ℝ≥0∞) * (ε : ℝ≥0∞))
      (𝓝 0) (𝓝 0) := by
    have hm : Continuous (fun x : ℝ≥0∞ => (2 : ℝ≥0∞) * x) :=
      ENNReal.continuous_const_mul (by norm_num)
    have hc : Continuous (fun ε : ℝ≥0 => (2 : ℝ≥0∞) * (ε : ℝ≥0∞)) :=
      hm.comp ENNReal.continuous_coe
    simpa using (hc.continuousAt (x := 0)).tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro ε
    exact bot_le
  · intro ε
    have hsubNN : (1 - ε : ℝ≥0) ≤ 1 := tsub_le_self
    have hsub : ((1 - ε : ℝ≥0) : ℝ≥0∞) ≤ 1 := by
      exact_mod_cast hsubNN
    calc
      f ε = ((2 : ℝ≥0∞) * (ε : ℝ≥0∞)) * ((1 - ε : ℝ≥0) : ℝ≥0∞) := rfl
      _ ≤ ((2 : ℝ≥0∞) * (ε : ℝ≥0∞)) * 1 := by gcongr
      _ = (2 : ℝ≥0∞) * (ε : ℝ≥0∞) := by simp

/-- The all-degree law theorem compares two weighted two-point inputs on `ℝ` at
degree zero with two draws. Each H₀ sample law has the full-H₀ atom of exact
mass `2ε(1-ε)` for its own weight, so the two sample laws differ whenever these
masses differ. -/
theorem twoPoint_pair_sampleLaw_bound_degreeZero (ε ε' : ℝ≥0) (hε : ε ≤ 1)
    (hε' : ε' ≤ 1) {p : ℝ} (hp : 1 ≤ p) :
    wasserstein p bottleneck
        (sampleLaw (ZMod 2) (twoPointLaw ε hε) 2 0)
        (sampleLaw (ZMod 2) (twoPointLaw ε' hε') 2 0) ≤
        2 * gromovWasserstein p (twoPointLaw ε hε) (twoPointLaw ε' hε') ∧
      (sampleLaw (ZMod 2) (twoPointLaw ε hε) 2 0) (diagram (ZMod 2) Bool 0) =
        (2 : ℝ≥0∞) * (ε : ℝ≥0∞) * ((1 - ε : ℝ≥0) : ℝ≥0∞) ∧
      (sampleLaw (ZMod 2) (twoPointLaw ε' hε') 2 0) (diagram (ZMod 2) Bool 0) =
        (2 : ℝ≥0∞) * (ε' : ℝ≥0∞) * ((1 - ε' : ℝ≥0) : ℝ≥0∞) ∧
      ((2 : ℝ≥0∞) * (ε : ℝ≥0∞) * ((1 - ε : ℝ≥0) : ℝ≥0∞) ≠
          (2 : ℝ≥0∞) * (ε' : ℝ≥0∞) * ((1 - ε' : ℝ≥0) : ℝ≥0∞) →
        sampleLaw (ZMod 2) (twoPointLaw ε hε) 2 0 ≠
          sampleLaw (ZMod 2) (twoPointLaw ε' hε') 2 0) := by
  have h₁ := epsilonTwoPoint_realSampleLaw_nontrivial_mass ε hε
  have h₂ := epsilonTwoPoint_realSampleLaw_nontrivial_mass ε' hε'
  refine ⟨?_, h₁, h₂, fun hne hlaw => hne ?_⟩
  · simpa using wasserstein_sampleLaw_le_gromovWasserstein_allDegrees (ZMod 2)
      (twoPointLaw ε hε) (twoPointLaw ε' hε') hp 2 0 le_rfl
  · rw [← h₁, ← h₂, hlaw]

end EpsilonSampleLaw

end TDA.Persistence.RipsSamplingExamples
