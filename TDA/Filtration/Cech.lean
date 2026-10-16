import TDA.Topology.Nerve
import TDA.Filtration.Rips
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false

/-!
# Closed ambient Čech complexes and the Rips/Čech sandwich

Fix a pseudometric ambient space `X` and labelled points `p : V → X`. The closed Čech
complex at radius `r` is the ordinary nerve of the closed balls of radius `r` about the
labelled points; witnesses range over all of `X`. Čech time is the ball radius, while Rips
time is the diameter, so the sandwich reads `Rips_r ⊆ Čech_r ⊆ Rips_{2r}`.

The pairwise forms of both inclusions hold for arbitrary labels, including repeated points.
The Rips forms take an explicit metric `d` on the labels that agrees with the ambient
distances. The Čech radius filter is the infimum over the ambient space of the largest
distance to the face's points; every Čech complex lies in its sublevel, with equality when
`X` is proper.
-/

universe u v

namespace TDA.Filtration.Cech

open TDA.Simplicial

variable {X : Type u} {V : Type v} [PseudoMetricSpace X]

/-- The closed balls of radius `r` about the labelled points. -/
def ballFamily (p : V → X) (r : ℝ) : TDA.Topology.CoverFamily X V :=
  fun v => Metric.closedBall (p v) r

/-- The closed ambient Čech complex at radius `r`: the nerve of the closed-ball family. -/
def complex (p : V → X) (r : ℝ) : PreAbstractSimplicialComplex V :=
  TDA.Topology.nerve (ballFamily p r)

/-- A Čech face is a nonempty finite label set whose closed `r`-balls share an ambient point. -/
theorem mem_complex_iff (p : V → X) (r : ℝ) (s : Finset V) :
    s ∈ complex p r ↔ s.Nonempty ∧ ∃ x : X, ∀ v ∈ s, dist x (p v) ≤ r :=
  Iff.rfl

/-- Enlarging the radius can only add Čech faces. -/
theorem complex_mono (p : V → X) {r q : ℝ} (h : r ≤ q) : complex p r ≤ complex p q :=
  TDA.Topology.nerve_mono fun _ => Metric.closedBall_subset_closedBall h

/-- Every labelled vertex is present exactly at nonnegative radii. -/
theorem singleton_mem_complex_iff (p : V → X) (r : ℝ) (v : V) :
    ({v} : Finset V) ∈ complex p r ↔ 0 ≤ r :=
  (TDA.Topology.mem_nerve_singleton_iff _ v).trans Metric.nonempty_closedBall

/-- Below radius zero the Čech complex has no faces. -/
theorem complex_eq_bot_of_neg (p : V → X) {r : ℝ} (hr : r < 0) : complex p r = ⊥ := by
  apply le_antisymm _ bot_le
  intro s hs
  obtain ⟨⟨v, hv⟩, x, hx⟩ := (mem_complex_iff p r s).1 hs
  exact absurd (dist_nonneg.trans (hx v hv)) (not_le.2 hr)

/-- Pairwise distances at most `r` give a Čech face at radius `r`, witnessed by a vertex. -/
theorem mem_complex_of_pairwise (p : V → X) {r : ℝ} {s : Finset V} (hs : s.Nonempty)
    (h : ∀ v ∈ s, ∀ w ∈ s, dist (p v) (p w) ≤ r) : s ∈ complex p r := by
  obtain ⟨v₀, hv₀⟩ := hs
  exact (mem_complex_iff p r s).2 ⟨⟨v₀, hv₀⟩, p v₀, fun v hv => h v₀ hv₀ v hv⟩

/-- The points of a Čech face at radius `r` are pairwise within `2 * r`. -/
theorem dist_le_two_mul_of_mem_complex (p : V → X) {r : ℝ} {s : Finset V}
    (hs : s ∈ complex p r) {v w : V} (hv : v ∈ s) (hw : w ∈ s) :
    dist (p v) (p w) ≤ 2 * r := by
  obtain ⟨_, x, hx⟩ := (mem_complex_iff p r s).1 hs
  calc dist (p v) (p w) ≤ dist x (p v) + dist x (p w) := dist_triangle_left _ _ _
    _ ≤ r + r := add_le_add (hx v hv) (hx w hw)
    _ = 2 * r := by ring

/-- The Rips sublevel at `r` lies in the Čech complex at radius `r`. -/
theorem ripsSublevel_le_complex (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (r : ℝ) :
    (Rips.filter d).sublevel r ≤ complex p r := by
  intro s hs
  obtain ⟨hsn, h⟩ := (Rips.mem_sublevel_iff d r s).1 hs
  exact mem_complex_of_pairwise p hsn fun v hv w hw => by
    rw [← hd]
    exact h v hv w hw

/-- The Čech complex at radius `r` lies in the Rips sublevel at `2 * r`. -/
theorem complex_le_ripsSublevel_two_mul (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (r : ℝ) :
    complex p r ≤ (Rips.filter d).sublevel (2 * r) := by
  intro s hs
  refine (Rips.mem_sublevel_iff d (2 * r) s).2
    ⟨((mem_complex_iff p r s).1 hs).1, fun v hv w hw => ?_⟩
  rw [hd]
  exact dist_le_two_mul_of_mem_complex p hs hv hw

/-- The largest distance from `x` to the points of `s`, with empty maximum zero. -/
noncomputable def radiusAt (p : V → X) (x : X) (s : Finset V) : ℝ :=
  s.fold max 0 (fun v => dist x (p v))

theorem radiusAt_nonneg (p : V → X) (x : X) (s : Finset V) : 0 ≤ radiusAt p x s :=
  (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

/-- The zero seed records the auxiliary empty-set convention explicitly. -/
theorem radiusAt_le_iff (p : V → X) (x : X) (s : Finset V) (r : ℝ) :
    radiusAt p x s ≤ r ↔ 0 ≤ r ∧ ∀ v ∈ s, dist x (p v) ≤ r :=
  Finset.fold_max_le r

theorem dist_le_radiusAt (p : V → X) (x : X) {s : Finset V} {v : V} (hv : v ∈ s) :
    dist x (p v) ≤ radiusAt p x s :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨v, hv, le_rfl⟩)

theorem radiusAt_mono (p : V → X) (x : X) {s t : Finset V} (hst : s ⊆ t) :
    radiusAt p x s ≤ radiusAt p x t :=
  (radiusAt_le_iff p x s _).mpr
    ⟨radiusAt_nonneg p x t, fun _ hv => dist_le_radiusAt p x (hst hv)⟩

/-- Moving the centre changes the radius by at most the distance moved. -/
theorem radiusAt_le_radiusAt_add_dist (p : V → X) (x y : X) (s : Finset V) :
    radiusAt p x s ≤ radiusAt p y s + dist x y := by
  refine (radiusAt_le_iff p x s _).mpr
    ⟨add_nonneg (radiusAt_nonneg p y s) dist_nonneg, fun v hv => ?_⟩
  calc dist x (p v) ≤ dist x y + dist y (p v) := dist_triangle _ _ _
    _ ≤ dist x y + radiusAt p y s := add_le_add_right (dist_le_radiusAt p y hv) _
    _ = radiusAt p y s + dist x y := add_comm _ _

theorem continuous_radiusAt (p : V → X) (s : Finset V) :
    Continuous fun x => radiusAt p x s :=
  (LipschitzWith.of_le_add fun x y => radiusAt_le_radiusAt_add_dist p x y s).continuous

theorem bddBelow_range_radiusAt (p : V → X) (s : Finset V) :
    BddBelow (Set.range fun x => radiusAt p x s) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    exact radiusAt_nonneg p x s⟩

/-- The Čech radius filter: a face's value is the infimal enclosing radius over `X`. -/
noncomputable def filter (p : V → X) : FilterFunction (Rips.fullComplex V) ℝ where
  value s := ⨅ x : X, radiusAt p x s.val
  mono h := ciInf_mono (bddBelow_range_radiusAt p _) fun x => radiusAt_mono p x h

@[simp] theorem filter_value (p : V → X) (s : TotalFace (Rips.fullComplex V)) :
    (filter p).value s = ⨅ x : X, radiusAt p x s.val := rfl

theorem filter_value_nonneg (p : V → X) (s : TotalFace (Rips.fullComplex V)) :
    0 ≤ (filter p).value s :=
  Real.iInf_nonneg fun x => radiusAt_nonneg p x s.val

theorem filter_value_le_radiusAt (p : V → X) (s : TotalFace (Rips.fullComplex V)) (x : X) :
    (filter p).value s ≤ radiusAt p x s.val :=
  ciInf_le (bddBelow_range_radiusAt p s.val) x

/-- Every Čech complex lies in the corresponding sublevel of the radius filter. -/
theorem complex_le_sublevel (p : V → X) (r : ℝ) : complex p r ≤ (filter p).sublevel r := by
  intro s hs
  obtain ⟨hsn, x, hx⟩ := (mem_complex_iff p r s).1 hs
  obtain ⟨v₀, hv₀⟩ := hsn
  refine (FilterFunction.mem_sublevel_iff _ r s).2 ⟨⟨v₀, hv₀⟩, ?_⟩
  exact (filter_value_le_radiusAt p ⟨s, ⟨v₀, hv₀⟩⟩ x).trans
    ((radiusAt_le_iff p x s r).2 ⟨dist_nonneg.trans (hx v₀ hv₀), hx⟩)

/-- In a proper ambient space, every actual face attains its Čech value. -/
theorem exists_radiusAt_eq_value [ProperSpace X] (p : V → X)
    (s : TotalFace (Rips.fullComplex V)) :
    ∃ x, radiusAt p x s.val = (filter p).value s := by
  obtain ⟨v₀, hv₀⟩ : s.val.Nonempty := s.property
  have : Nonempty X := ⟨p v₀⟩
  set R := radiusAt p (p v₀) s.val
  have hmem : p v₀ ∈ Metric.closedBall (p v₀) R :=
    Metric.mem_closedBall_self (radiusAt_nonneg p (p v₀) s.val)
  obtain ⟨y, -, hy⟩ := (isCompact_closedBall (p v₀) R).exists_isMinOn ⟨_, hmem⟩
    (continuous_radiusAt p s.val).continuousOn
  have hglob : ∀ x, radiusAt p y s.val ≤ radiusAt p x s.val := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (p v₀) R
    · exact isMinOn_iff.mp hy x hx
    · rw [Metric.mem_closedBall, not_le] at hx
      exact (isMinOn_iff.mp hy _ hmem).trans (hx.le.trans (dist_le_radiusAt p x hv₀))
  exact ⟨y, le_antisymm (le_ciInf hglob) (filter_value_le_radiusAt p s y)⟩

/-- In a proper ambient space, the radius-filter sublevel is exactly the Čech complex. -/
theorem sublevel_eq_complex [ProperSpace X] (p : V → X) (r : ℝ) :
    (filter p).sublevel r = complex p r := by
  apply le_antisymm _ (complex_le_sublevel p r)
  intro s hs
  obtain ⟨hsn, hval⟩ := (FilterFunction.mem_sublevel_iff _ r s).1 hs
  obtain ⟨x, hx⟩ := exists_radiusAt_eq_value p ⟨s, hsn⟩
  exact (mem_complex_iff p r s).2 ⟨hsn, x, ((radiusAt_le_iff p x s r).1 (hx.trans_le hval)).2⟩

/-- The Čech value of a face is at most its Rips value. -/
theorem filter_value_le_rips (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (s : TotalFace (Rips.fullComplex V)) :
    (filter p).value s ≤ (Rips.filter d).value s := by
  obtain ⟨v₀, hv₀⟩ : s.val.Nonempty := s.property
  refine (filter_value_le_radiusAt p s (p v₀)).trans ((radiusAt_le_iff p _ _ _).2
    ⟨Rips.diameter_nonneg d s.val, fun v hv => ?_⟩)
  rw [Rips.filter_value, ← hd]
  exact Rips.dist_le_diameter d hv₀ hv

/-- The Rips value of a face is at most twice its Čech value. -/
theorem rips_le_two_mul_filter_value (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (s : TotalFace (Rips.fullComplex V)) :
    (Rips.filter d).value s ≤ 2 * (filter p).value s := by
  obtain ⟨v₀, hv₀⟩ : s.val.Nonempty := s.property
  have : Nonempty X := ⟨p v₀⟩
  have key : (Rips.filter d).value s / 2 ≤ (filter p).value s := by
    refine le_ciInf fun x => ?_
    have h : Rips.diameter d s.val ≤ 2 * radiusAt p x s.val := by
      refine (Rips.diameter_le_iff d s.val _).2
        ⟨mul_nonneg zero_le_two (radiusAt_nonneg p x s.val), fun v hv w hw => ?_⟩
      rw [hd]
      calc dist (p v) (p w) ≤ dist x (p v) + dist x (p w) := dist_triangle_left _ _ _
        _ ≤ radiusAt p x s.val + radiusAt p x s.val :=
          add_le_add (dist_le_radiusAt p x hv) (dist_le_radiusAt p x hw)
        _ = 2 * radiusAt p x s.val := by ring
    rw [Rips.filter_value]
    linarith
  linarith

end TDA.Filtration.Cech
