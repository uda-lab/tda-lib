import TDA.Persistence.RipsGromovHausdorff
import TDA.Probability.GromovWasserstein

/-!
# Rips diagrams of tuples sampled with replacement

A tuple represents the finite metric subspace consisting of its values. Repeated
values are identified in this carrier. Its full Rips diagram uses diameter time,
retains occurrence multiplicities, and does not depend on an enumeration.
-/

noncomputable section

universe u v w

namespace TDA.Persistence.Rips

open TDA.Probability
open scoped ENNReal NNReal

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y] {n : ℕ}

/-- The metric quotient of the tuple pseudometric, realised as its finite range. -/
abbrev Sample (t : Fin n → X) := Set.range t

instance sampleFintype (t : Fin n → X) : Fintype (Sample t) := Fintype.ofFinite _

/-- Repeated draws have the same image point in the finite metric sample. -/
def sampleProjection (t : Fin n → X) (i : Fin n) : Sample t := ⟨t i, i, rfl⟩

theorem sampleProjection_surjective (t : Fin n → X) :
    Function.Surjective (sampleProjection t) := by
  rintro ⟨x, i, rfl⟩
  exact ⟨i, rfl⟩

@[simp] theorem dist_sampleProjection (t : Fin n → X) (i j : Fin n) :
    dist (sampleProjection t i) (sampleProjection t j) = dist (t i) (t j) := rfl

/-- Equality in the sample is precisely zero pseudodistance in the tuple. -/
theorem sampleProjection_eq_iff (t : Fin n → X) (i j : Fin n) :
    sampleProjection t i = sampleProjection t j ↔ dist (t i) (t j) = 0 := by
  simp [sampleProjection, Subtype.ext_iff]

/-- The full diagram of the finite sample, with arbitrary repeated draws allowed. -/
def sampleDiagram (k : Type w) [Field k] (t : Fin n → X) (degree : ℕ) : Diagram ℝ :=
  diagram k (Sample t) degree

/-- An isometric embedding of metric spaces preserves the full Rips diagram of
every finite tuple range, including tuples with repeated values. -/
theorem sampleDiagram_eq_of_isometry (k : Type w) [Field k]
    (f : X → Y) (hf : Isometry f) (t : Fin n → X) (degree : ℕ) :
    sampleDiagram k (fun i => f (t i)) degree = sampleDiagram k t degree := by
  let g : Sample t → Sample (fun i => f (t i)) := fun x =>
    ⟨f x.1, by
      rcases x.2 with ⟨i, hi⟩
      exact ⟨i, congrArg f hi⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact hf.injective (congrArg Subtype.val hab)
    · rintro ⟨y, i, rfl⟩
      exact ⟨sampleProjection t i, by apply Subtype.ext; rfl⟩
  let e : Sample t ≃ᵢ Sample (fun i => f (t i)) :=
    { Equiv.ofBijective g hg with
      isometry_toFun := by
        intro a b
        change edist (f a.1) (f b.1) = edist a.1 b.1
        exact hf a.1 b.1 }
  exact (diagram_eq_of_isometryEquiv k e degree).symm

/-- The diagram depends on the set of sampled values, so relabelling and changing
the number of repeated occurrences do not change this sample diagram. -/
theorem sampleDiagram_eq_of_range_eq (k : Type w) [Field k]
    {m : ℕ} (t : Fin n → X) (s : Fin m → X) (h : Set.range t = Set.range s)
    (degree : ℕ) : sampleDiagram k t degree = sampleDiagram k s degree := by
  let e : Sample t ≃ᵢ Sample s :=
    { Equiv.setCongr h with isometry_toFun := fun _ _ => rfl }
  exact diagram_eq_of_isometryEquiv k e degree

/-- A tuple that visits every point has exactly the ordinary finite-space diagram.
The hypothesis concerns coverage, and places no condition on occurrence counts. -/
theorem sampleDiagram_eq_diagram_of_surjective (k : Type w) [Field k]
    [Fintype X] (t : Fin n → X) (ht : Function.Surjective t) (degree : ℕ) :
    sampleDiagram k t degree = diagram k X degree := by
  let e : Sample t ≃ᵢ X :=
    { Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun x => by
        obtain ⟨i, rfl⟩ := ht x
        exact ⟨sampleProjection t i, rfl⟩⟩ with
      isometry_toFun := fun _ _ => rfl }
  exact diagram_eq_of_isometryEquiv k e degree

/-- A uniform bound on corresponding distance entries controls the actual diagrams.
The correspondence pairs values drawn at the same index, including repeated values. -/
theorem bottleneck_sampleDiagram_le (k : Type w) [Field k]
    (t : Fin n → X) (s : Fin n → Y) {ε : ℝ≥0}
    (h : ∀ i j, |dist (t i) (t j) - dist (s i) (s j)| ≤ (ε : ℝ))
    (degree : ℕ) :
    bottleneck (sampleDiagram k t degree) (sampleDiagram k s degree) ≤ (ε : ℝ≥0∞) := by
  let C : SetRel (Sample t) (Sample s) :=
    {p | ∃ i, p.1 = sampleProjection t i ∧ p.2 = sampleProjection s i}
  apply bottleneck_diagram_le_of_relation k (C := C) (ε := ε) _ _ _ degree
  · intro x
    obtain ⟨i, rfl⟩ := sampleProjection_surjective t x
    exact ⟨sampleProjection s i, i, rfl, rfl⟩
  · intro y
    obtain ⟨i, rfl⟩ := sampleProjection_surjective s y
    exact ⟨sampleProjection t i, i, rfl, rfl⟩
  · rintro x x' y y' ⟨i, rfl, rfl⟩ ⟨j, rfl, rfl⟩
    exact h i j

/-- The distance-matrix maximum uses each metric difference with its actual
extended nonnegative value, without converting infinite costs to zero. -/
theorem bottleneck_sampleDiagram_le_pairMaximum (k : Type w) [Field k]
    (t : Fin n → X × Y) (degree : ℕ) :
    bottleneck (sampleDiagram k (fun i => (t i).1) degree)
      (sampleDiagram k (fun i => (t i).2) degree) ≤ pairMaximum distortion t := by
  by_cases hm : pairMaximum distortion t = ⊤
  · simp [hm]
  · have h := bottleneck_sampleDiagram_le k
        (fun i => (t i).1) (fun i => (t i).2)
        (ε := (pairMaximum distortion t).toNNReal) (fun i j => ?_) degree
    · simpa only [ENNReal.coe_toNNReal hm] using h
    · exact (ENNReal.ofReal_le_iff_le_toReal hm).mp
        (cost_le_pairMaximum distortion t i j)

/-- The probability law of an iid sample's full Rips diagram. In particular, an
empty diagram remains a point of this probability law. -/
def sampleLaw (k : Type w) [Field k] (μ : PMF X) (n degree : ℕ) : PMF (Diagram ℝ) :=
  (iid μ n).map (fun t => sampleDiagram k t degree)

/-- Isometric embeddings preserve the iid law of full finite-sample Rips
diagrams: mapping every input draw before sampling leaves the diagram law
unchanged. -/
theorem sampleLaw_map_isometry (k : Type w) [Field k]
    (μ : PMF X) (f : X → Y) (hf : Isometry f) (n degree : ℕ) :
    sampleLaw k (μ.map f) n degree = sampleLaw k μ n degree := by
  change (iid (μ.map f) n).map (fun t => sampleDiagram k t degree) =
    (iid μ n).map (fun t => sampleDiagram k t degree)
  rw [← iid_map μ f n, PMF.map_comp]
  congr 1
  funext t
  exact sampleDiagram_eq_of_isometry k f hf t degree

/-- The iid joint input law pushes forward to an exact coupling of diagram laws. -/
def sampleLawCoupling (k : Type w) [Field k] {μ : PMF X} {ν : PMF Y}
    (π : Coupling μ ν) (n degree : ℕ) :
    Coupling (sampleLaw k μ n degree) (sampleLaw k ν n degree) :=
  π.sampleLaw n (fun t => sampleDiagram k t degree) (fun s => sampleDiagram k s degree)

/-- Every input coupling gives the sharp finite-p diagram-law moment bound.
The cost is between entire diagrams, and the outer coupling has total mass one. -/
theorem transportCost_sampleLaw_le (k : Type w) [Field k]
    {μ : PMF X} {ν : PMF Y} (π : Coupling μ ν) {p : ℝ} (hp : 0 < p)
    (n degree : ℕ) :
    transportCost (fun D E => bottleneck D E ^ p)
      (sampleLaw k μ n degree) (sampleLaw k ν n degree) ≤
      (n.choose 2 : ℝ≥0∞) * π.distortionMoment p := by
  apply (transportCost_le_coupling _ _ _ (sampleLawCoupling k π n degree)).trans
  change expectation ((π.tuples n).joint.map
      (fun ts => (sampleDiagram k ts.1 degree, sampleDiagram k ts.2 degree)))
    (fun de => bottleneck de.1 de.2 ^ p) ≤ _
  rw [expectation_map]
  change expectation ((iid π.joint n).map
      (fun t => (fun i => (t i).1, fun i => (t i).2))) _ ≤ _
  rw [expectation_map]
  apply (expectation_mono _ (fun t => ENNReal.rpow_le_rpow
    (bottleneck_sampleDiagram_le_pairMaximum k t degree) hp.le)).trans
  exact expectation_pairMaximum_rpow_le π.joint distortion distortion_self distortion_comm hp n

/-- Finite-p stability of iid laws of full Rips diagrams in every degree,
including ordinary H₀ and its essential bar. Uses diameter time and the
standard half-distortion GW convention, without assuming a minimizer. -/
theorem wasserstein_sampleLaw_le_gromovWasserstein_allDegrees (k : Type w) [Field k]
    (μ : PMF X) (ν : PMF Y) {p : ℝ} (hp : 1 ≤ p) (n q : ℕ) (hn : 2 ≤ n) :
    wasserstein p bottleneck (sampleLaw k μ n q) (sampleLaw k ν n q) ≤
      (n.choose 2 : ℝ≥0∞) ^ p⁻¹ * (2 * gromovWasserstein p μ ν) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hC0 : (n.choose 2 : ℝ≥0∞) ^ p⁻¹ ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.rpow_pos
    · exact_mod_cast Nat.choose_pos hn
    · exact ENNReal.natCast_ne_top _
  have hCtop : (n.choose 2 : ℝ≥0∞) ^ p⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp0.le) (ENNReal.natCast_ne_top _)
  have hGW : 2 * gromovWasserstein p μ ν =
      ⨅ π : Coupling μ ν, π.distortionMoment p ^ p⁻¹ := by
    simp only [gromovWasserstein, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  rw [hGW, ENNReal.mul_iInf_of_ne hC0 hCtop]
  apply le_iInf
  intro π
  exact (ENNReal.rpow_le_rpow (transportCost_sampleLaw_le k π hp0 n q)
    (inv_nonneg.mpr hp0.le)).trans_eq
      (ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0.le))

/-- Positive-degree specialization of the all-degree finite-p theorem. -/
theorem wasserstein_sampleLaw_le_gromovWasserstein (k : Type w) [Field k]
    (μ : PMF X) (ν : PMF Y) {p : ℝ} (hp : 1 ≤ p) (n degree : ℕ) (hn : 2 ≤ n) :
    wasserstein p bottleneck (sampleLaw k μ n (degree + 1)) (sampleLaw k ν n (degree + 1)) ≤
      (n.choose 2 : ℝ≥0∞) ^ p⁻¹ * (2 * gromovWasserstein p μ ν) :=
  wasserstein_sampleLaw_le_gromovWasserstein_allDegrees k μ ν hp n (degree + 1) hn

/-- Infinity stability is independent of the tuple length; zero-mass points
are excluded by essential suprema on both sides. -/
theorem wassersteinInfinity_sampleLaw_le_gromovWassersteinInfinity
    (k : Type w) [Field k] (μ : PMF X) (ν : PMF Y) (n degree : ℕ) :
    wassersteinInfinity bottleneck (sampleLaw k μ n (degree + 1)) (sampleLaw k ν n (degree + 1)) ≤
      2 * gromovWassersteinInfinity μ ν := by
  have hGW : 2 * gromovWassersteinInfinity μ ν =
      ⨅ π : Coupling μ ν, π.distortionInfinity := by
    simp only [gromovWassersteinInfinity, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  rw [hGW]
  apply le_iInf
  intro π
  apply (iInf_le _ (sampleLawCoupling k π n (degree + 1))).trans
  change essentialSup ((π.tuples n).joint.map
      (fun ts => (sampleDiagram k ts.1 (degree + 1),
        sampleDiagram k ts.2 (degree + 1))))
    (fun de => bottleneck de.1 de.2) ≤ _
  rw [essentialSup_map]
  change essentialSup ((iid π.joint n).map
      (fun t => (fun i => (t i).1, fun i => (t i).2))) _ ≤ _
  rw [essentialSup_map]
  apply le_trans _ (essentialSup_pairMaximum_le π.joint distortion n)
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact (bottleneck_sampleDiagram_le_pairMaximum k t (degree + 1)).trans
    (le_iSup_of_le t (le_iSup_of_le ht le_rfl))

end TDA.Persistence.Rips
