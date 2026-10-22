import TDA.Persistence.FaceOrderTemplate
import TDA.Persistence.DiagramBottleneckLaws
import TDA.Filtration.CompatibleOrderExistence
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

/-!
# Bottleneck stability for finite-complex sublevel diagrams

The interpolation is divided at the finitely many times when two face
values meet. Each resulting closed segment has one face-compatible order;
the orders on adjacent segments need not agree. A midpoint order stays compatible at
both endpoints by continuity of the weak face-value inequalities. The template bound
therefore applies across each closed segment, and the triangle inequality combines the
segments without assuming one pairing works for the whole interpolation.
-/

universe u

namespace TDA.Persistence

open TDA.Filtration TDA.Simplicial

variable {V : Type u} [LinearOrder V]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]

/-- Linear interpolation of two real face filters. -/
def filterInterpolate (f g : FilterFunction K ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : FilterFunction K ℝ where
  value σ := (1 - t) * f.value σ + t * g.value σ
  mono := by
    intro τ σ hτσ
    exact add_le_add
      (mul_le_mul_of_nonneg_left (f.mono hτσ) (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left (g.mono hτσ) ht0)

@[simp] theorem filterInterpolate_zero (f g : FilterFunction K ℝ) :
    filterInterpolate f g 0 (le_refl 0) (by norm_num) = f := by
  cases f
  simp [filterInterpolate]

@[simp] theorem filterInterpolate_one (f g : FilterFunction K ℝ) :
    filterInterpolate f g 1 (by norm_num) (le_refl 1) = g := by
  cases g
  simp [filterInterpolate]

/-- Interpolation with the parameter restricted to the unit interval. -/
def intervalFilter (f g : FilterFunction K ℝ) (t : Set.Icc (0 : ℝ) 1) :
    FilterFunction K ℝ :=
  filterInterpolate f g t t.property.1 t.property.2

@[simp] theorem intervalFilter_value (f g : FilterFunction K ℝ)
    (t : Set.Icc (0 : ℝ) 1) (σ : TotalFace K) :
    (intervalFilter f g t).value σ = (1 - t) * f.value σ + t * g.value σ := rfl

/-- Maximum absolute change over faces; the empty maximum is zero. -/
noncomputable def faceSupDifference (f g : FilterFunction K ℝ) : ℝ :=
  Finset.univ.fold max 0 (fun σ : TotalFace K => |f.value σ - g.value σ|)

theorem faceSupDifference_nonneg (f g : FilterFunction K ℝ) :
    0 ≤ faceSupDifference f g := by
  classical
  unfold faceSupDifference
  exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

theorem abs_face_difference_le (f g : FilterFunction K ℝ)
    (σ : TotalFace K) :
    |f.value σ - g.value σ| ≤ faceSupDifference f g := by
  classical
  unfold faceSupDifference
  exact (Finset.le_fold_max _).mpr
    (Or.inr ⟨σ, Finset.mem_univ _, le_rfl⟩)

theorem faceSupDifference_self (f : FilterFunction K ℝ) :
    faceSupDifference f f = 0 := by
  apply le_antisymm
  · unfold faceSupDifference
    apply (Finset.fold_max_le 0).mpr
    simp
  · exact faceSupDifference_nonneg f f

theorem faceSupDifference_of_isEmpty (f g : FilterFunction K ℝ)
    [IsEmpty (TotalFace K)] : faceSupDifference f g = 0 := by
  classical
  simp [faceSupDifference]

private def faceLine (f g : FilterFunction K ℝ) (σ : TotalFace K) (t : ℝ) : ℝ :=
  (1 - t) * f.value σ + t * g.value σ

private def faceDifference (f g : FilterFunction K ℝ)
    (σ τ : TotalFace K) (t : ℝ) : ℝ :=
  faceLine f g σ t - faceLine f g τ t

private def faceDifferenceSlope (f g : FilterFunction K ℝ)
    (σ τ : TotalFace K) : ℝ :=
  (g.value σ - f.value σ) - (g.value τ - f.value τ)

private theorem faceDifference_affine (f g : FilterFunction K ℝ)
    (σ τ : TotalFace K) (t : ℝ) :
    faceDifference f g σ τ t =
      (f.value σ - f.value τ) + t * faceDifferenceSlope f g σ τ := by
  unfold faceDifference faceLine faceDifferenceSlope
  ring

private theorem faceDifference_continuous (f g : FilterFunction K ℝ)
    (σ τ : TotalFace K) : Continuous (faceDifference f g σ τ) := by
  unfold faceDifference faceLine
  fun_prop

/-- The isolated time when the values of two faces cross. Constant differences
are deliberately omitted from the critical set. -/
private noncomputable def faceCrossingTime (f g : FilterFunction K ℝ)
    (σ τ : TotalFace K) : ℝ :=
  -(f.value σ - f.value τ) / faceDifferenceSlope f g σ τ

private theorem faceDifference_eq_zero_iff_crossing (f g : FilterFunction K ℝ)
    (σ τ : TotalFace K) (hsl : faceDifferenceSlope f g σ τ ≠ 0) (t : ℝ) :
    faceDifference f g σ τ t = 0 ↔ t = faceCrossingTime f g σ τ := by
  rw [faceDifference_affine]
  unfold faceCrossingTime
  constructor
  · intro h
    apply (eq_div_iff hsl).mpr
    nlinarith
  · intro h
    rw [h]
    field_simp
    ring

private theorem faceDifference_eq_zero_of_slope_zero (f g : FilterFunction K ℝ)
    (σ τ : TotalFace K) (hsl : faceDifferenceSlope f g σ τ = 0)
    {t : ℝ} (ht : faceDifference f g σ τ t = 0) (s : ℝ) :
    faceDifference f g σ τ s = 0 := by
  rw [faceDifference_affine, hsl, mul_zero, add_zero] at ht ⊢
  exact ht

/-- All crossing times in the unit interval, plus both endpoints. This finite
set deduplicates simultaneous crossings and does not require a face. -/
noncomputable def faceCrossingTimes (f g : FilterFunction K ℝ) : Finset ℝ := by
  classical
  let candidates : Finset ℝ := (Finset.univ.filter (fun p : TotalFace K × TotalFace K =>
      faceDifferenceSlope f g p.1 p.2 ≠ 0 ∧
      faceCrossingTime f g p.1 p.2 ∈ Set.Icc (0 : ℝ) 1)).image
      (fun p : TotalFace K × TotalFace K => faceCrossingTime f g p.1 p.2)
  exact insert 1 (insert 0 candidates)

private theorem zero_mem_faceCrossingTimes (f g : FilterFunction K ℝ) :
    0 ∈ faceCrossingTimes f g := by
  classical
  simp [faceCrossingTimes]

private theorem one_mem_faceCrossingTimes (f g : FilterFunction K ℝ) :
    1 ∈ faceCrossingTimes f g := by
  classical
  simp [faceCrossingTimes]

private theorem faceCrossingTimes_subset_Icc (f g : FilterFunction K ℝ) :
    ∀ t ∈ faceCrossingTimes f g, t ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  intro t ht
  simp only [faceCrossingTimes, Finset.mem_insert, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and] at ht
  rcases ht with rfl | rfl | ⟨p, hp, rfl⟩
  · norm_num
  · norm_num
  · exact hp.2

private theorem crossing_mem_faceCrossingTimes (f g : FilterFunction K ℝ)
    (σ τ : TotalFace K) (hsl : faceDifferenceSlope f g σ τ ≠ 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hz : faceDifference f g σ τ t = 0) :
    t ∈ faceCrossingTimes f g := by
  classical
  have heq := (faceDifference_eq_zero_iff_crossing f g σ τ hsl t).mp hz
  subst t
  unfold faceCrossingTimes
  simp only [Finset.mem_insert, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr (Or.inr ⟨(σ, τ), ⟨hsl, ht⟩, rfl⟩)

private theorem nonpos_on_closed_segment (d : ℝ → ℝ) (hd : Continuous d)
    {a m b : ℝ} (ham : a < m) (hmb : m < b)
    (hmid : d m ≤ 0)
    (hzero : ∀ r ∈ Set.Ioo a b, d r = 0 → ∀ x, d x = 0)
    {t : ℝ} (ht : t ∈ Set.Icc a b) : d t ≤ 0 := by
  by_cases hdm0 : d m = 0
  · simp [hzero m ⟨ham, hmb⟩ hdm0 t]
  by_contra hnot
  have hdt : 0 < d t := lt_of_not_ge hnot
  have hdm : d m < 0 := lt_of_le_of_ne hmid hdm0
  rcases le_total t m with htm | hmt
  · have htm' : t < m := lt_of_le_of_ne htm (by
      intro he
      subst t
      exact (not_lt_of_ge hmid) hdt)
    obtain ⟨r, hr, hz⟩ :=
      (intermediate_value_Ioo' htm'.le hd.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (d m) (d t) from ⟨hdm, hdt⟩))
    have hr' : r ∈ Set.Ioo a b := ⟨lt_of_le_of_lt ht.1 hr.1, hr.2.trans hmb⟩
    exact hdm0 (hzero r hr' hz m)
  · have hmt' : m < t := lt_of_le_of_ne hmt (by
      intro he
      subst t
      exact (not_lt_of_ge hmid) hdt)
    obtain ⟨r, hr, hz⟩ :=
      (intermediate_value_Ioo hmt'.le hd.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (d m) (d t) from ⟨hdm, hdt⟩))
    have hr' : r ∈ Set.Ioo a b := ⟨ham.trans hr.1, lt_of_lt_of_le hr.2 ht.2⟩
    exact hdm0 (hzero r hr' hz m)

/-- A midpoint-compatible enumeration works on the entire closed segment if
its open interior contains no isolated face crossing. Endpoint ties are weak. -/
private theorem exists_segment_compatibleOrder (f g : FilterFunction K ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hgap : ∀ r ∈ Set.Ioo a b, r ∉ faceCrossingTimes f g) :
    ∃ (m : Set.Icc (0 : ℝ) 1) (e : CompatibleOrder (intervalFilter f g m)),
      ∀ (t : Set.Icc (0 : ℝ) 1), a ≤ t → t ≤ b →
        Monotone ((intervalFilter f g t).value ∘ e.enum) := by
  let m : Set.Icc (0 : ℝ) 1 :=
    ⟨(a + b) / 2, ⟨by linarith, by linarith⟩⟩
  have ham : a < (m : ℝ) := by dsimp [m]; linarith
  have hmb : (m : ℝ) < b := by dsimp [m]; linarith
  obtain ⟨e⟩ := exists_compatibleOrder (intervalFilter f g m)
  refine ⟨m, e, ?_⟩
  intro t hat htb i j hij
  apply sub_nonpos.mp
  change faceDifference f g (e.enum i) (e.enum j) t ≤ 0
  apply nonpos_on_closed_segment
    (faceDifference f g (e.enum i) (e.enum j))
    (faceDifference_continuous f g _ _) ham hmb
  · apply sub_nonpos.mpr
    exact e.monotone hij
  · intro r hr hz x
    by_cases hsl : faceDifferenceSlope f g (e.enum i) (e.enum j) = 0
    · exact faceDifference_eq_zero_of_slope_zero f g _ _ hsl hz x
    · have hrunit : r ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨ha.trans hr.1.le, hr.2.le.trans hb⟩
      exact (hgap r hr (crossing_mem_faceCrossingTimes f g _ _ hsl hrunit hz)).elim
  · exact ⟨hat, htb⟩

private theorem faceLine_sub_abs_le (f g : FilterFunction K ℝ)
    (σ : TotalFace K) {s t : ℝ} (hst : s ≤ t) :
    |faceLine f g σ t - faceLine f g σ s| ≤
      (t - s) * faceSupDifference f g := by
  have h : faceLine f g σ t - faceLine f g σ s =
      (t - s) * (g.value σ - f.value σ) := by
    unfold faceLine
    ring
  rw [h, abs_mul, abs_of_nonneg (sub_nonneg.mpr hst)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [abs_sub_comm] using abs_face_difference_le f g σ)
    (sub_nonneg.mpr hst)

private noncomputable def templateCoordinates (k : Type u) [Field k]
    {f : FilterFunction K ℝ} (e : CompatibleOrder f) (n : ℕ)
    (h : FilterFunction K ℝ) :
    (Fin (faceTemplatePairs k e n).toList.length → ℝ × ℝ) ×
      (Fin (faceTemplateEssential k e n).toList.length → ℝ) :=
  ((fun i => pairValues h e ((faceTemplatePairs k e n).toList.get i)),
    fun i => birthValue h e ((faceTemplateEssential k e n).toList.get i))

private theorem templateCoordinates_eq_orderedQ (k : Type u) [Field k]
    {f : FilterFunction K ℝ} (e : CompatibleOrder f) (n : ℕ)
    (h : FilterFunction K ℝ) (hh : Monotone (h.value ∘ e.enum)) :
    dgm k h n = orderedQ _ _ (templateCoordinates k e n h) := by
  rw [← evaluateFaceTemplate_eq_dgm k e h hh n]
  apply evaluateFaceTemplate_eq_orderedQ_of_enumerations k e h hh n
  · classical
    simp only [templateCoordinates, List.ofFn_comp', List.ofFn_get]
    change Multiset.map (pairValues h e) (↑(faceTemplatePairs k e n).toList) = _
    rw [Multiset.coe_toList]
  · classical
    simp only [templateCoordinates, List.ofFn_comp', List.ofFn_get]
    change Multiset.map (birthValue h e) (↑(faceTemplateEssential k e n).toList) = _
    rw [Multiset.coe_toList]

private theorem templateCoordinates_norm_le (k : Type u) [Field k]
    (f g : FilterFunction K ℝ) {h : FilterFunction K ℝ}
    (e : CompatibleOrder h) (n : ℕ)
    (s t : Set.Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t) :
    ‖templateCoordinates k e n (intervalFilter f g t) -
      templateCoordinates k e n (intervalFilter f g s)‖ ≤
        ((t : ℝ) - s) * faceSupDifference f g := by
  have hr : 0 ≤ ((t : ℝ) - s) * faceSupDifference f g :=
    mul_nonneg (sub_nonneg.mpr hst) (faceSupDifference_nonneg f g)
  rw [norm_prod_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    rw [norm_prod_le_iff]
    constructor
    · change |faceLine f g (e.enum ((faceTemplatePairs k e n).toList.get i).1) t -
          faceLine f g (e.enum ((faceTemplatePairs k e n).toList.get i).1) s| ≤ _
      exact faceLine_sub_abs_le f g _ hst
    · change |faceLine f g (e.enum ((faceTemplatePairs k e n).toList.get i).2) t -
          faceLine f g (e.enum ((faceTemplatePairs k e n).toList.get i).2) s| ≤ _
      exact faceLine_sub_abs_le f g _ hst
  · apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    change |faceLine f g (e.enum ((faceTemplateEssential k e n).toList.get i)) t -
        faceLine f g (e.enum ((faceTemplateEssential k e n).toList.get i)) s| ≤ _
    exact faceLine_sub_abs_le f g _ hst

private theorem segment_bottleneck_le (k : Type u) [Field k]
    (f g : FilterFunction K ℝ) (n : ℕ)
    {h : FilterFunction K ℝ} (e : CompatibleOrder h)
    (s t : Set.Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t)
    (hs : Monotone ((intervalFilter f g s).value ∘ e.enum))
    (ht : Monotone ((intervalFilter f g t).value ∘ e.enum)) :
    bottleneck (dgm k (intervalFilter f g s) n)
      (dgm k (intervalFilter f g t) n) ≤
        ENNReal.ofReal (((t : ℝ) - s) * faceSupDifference f g) := by
  rw [templateCoordinates_eq_orderedQ k e n _ hs,
    templateCoordinates_eq_orderedQ k e n _ ht]
  have hnorm := templateCoordinates_norm_le k f g e n s t hst
  rw [norm_sub_rev] at hnorm
  exact (bottleneck_orderedQ_le_norm _ _ _ _).trans
    (ENNReal.ofReal_le_ofReal hnorm)

private theorem gap_bottleneck_le (k : Type u) [Field k]
    (f g : FilterFunction K ℝ) (n : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hgap : ∀ r ∈ Set.Ioo a b, r ∉ faceCrossingTimes f g) :
    bottleneck (dgm k (intervalFilter f g ⟨a, ⟨ha, hab.le.trans hb⟩⟩) n)
      (dgm k (intervalFilter f g ⟨b, ⟨ha.trans hab.le, hb⟩⟩) n) ≤
        ENNReal.ofReal ((b - a) * faceSupDifference f g) := by
  obtain ⟨m, e, he⟩ := exists_segment_compatibleOrder f g ha hab hb hgap
  exact segment_bottleneck_le k f g n e
    ⟨a, ⟨ha, hab.le.trans hb⟩⟩ ⟨b, ⟨ha.trans hab.le, hb⟩⟩ hab.le
    (he _ le_rfl hab.le) (he _ hab.le le_rfl)

/-- The finite set of crossing times subdivides `[0,1]` into closed segments
with compatible face orders. This induction is the bottleneck triangle telescope:
it splits at one interior crossing, and terminates when the interior is empty. -/
private theorem crossing_telescope (k : Type u) [Field k]
    (f g : FilterFunction K ℝ) (n : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    bottleneck (dgm k (intervalFilter f g ⟨a, ⟨ha, hab.trans hb⟩⟩) n)
      (dgm k (intervalFilter f g ⟨b, ⟨ha.trans hab, hb⟩⟩) n) ≤
        ENNReal.ofReal ((b - a) * faceSupDifference f g) := by
  classical
  let C (x y : ℝ) :=
    (faceCrossingTimes f g).filter (fun r => r ∈ Set.Ioo x y)
  suffices h : ∀ q : ℕ, ∀ (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1),
      (C x y).card = q →
      bottleneck (dgm k (intervalFilter f g ⟨x, ⟨hx, hxy.trans hy⟩⟩) n)
        (dgm k (intervalFilter f g ⟨y, ⟨hx.trans hxy, hy⟩⟩) n) ≤
          ENNReal.ofReal ((y - x) * faceSupDifference f g) by
    exact h (C a b).card a b ha hab hb rfl
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro x y hx hxy hy hcard
    by_cases heq : x = y
    · subst y
      simp [bottleneck_self]
    have hxy' : x < y := lt_of_le_of_ne hxy heq
    by_cases hnone : C x y = ∅
    · apply gap_bottleneck_le k f g n hx hxy' hy
      intro r hr hmem
      have : r ∈ C x y := Finset.mem_filter.mpr ⟨hmem, hr⟩
      simp [hnone] at this
    · obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hnone
      have hrS : r ∈ faceCrossingTimes f g := (Finset.mem_filter.mp hr).1
      have hrxy : r ∈ Set.Ioo x y := (Finset.mem_filter.mp hr).2
      have hleft : (C x r).card < q := by
        rw [← hcard]
        apply Finset.card_lt_card
        apply (Finset.ssubset_iff_of_subset ?_).mpr
          ⟨r, hr, by simp [C]⟩
        intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzS, hzr⟩
        exact Finset.mem_filter.mpr ⟨hzS, ⟨hzr.1, hzr.2.trans hrxy.2⟩⟩
      have hright : (C r y).card < q := by
        rw [← hcard]
        apply Finset.card_lt_card
        apply (Finset.ssubset_iff_of_subset ?_).mpr
          ⟨r, hr, by simp [C]⟩
        intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzS, hzr⟩
        exact Finset.mem_filter.mpr ⟨hzS, ⟨hrxy.1.trans hzr.1, hzr.2⟩⟩
      have h₁ := ih (C x r).card hleft x r hx hrxy.1.le (hrxy.2.le.trans hy) rfl
      have h₂ := ih (C r y).card hright r y (hx.trans hrxy.1.le) hrxy.2.le hy rfl
      calc
        bottleneck (dgm k (intervalFilter f g ⟨x, _⟩) n)
            (dgm k (intervalFilter f g ⟨y, _⟩) n) ≤
          bottleneck (dgm k (intervalFilter f g ⟨x, _⟩) n)
            (dgm k (intervalFilter f g ⟨r, _⟩) n) +
          bottleneck (dgm k (intervalFilter f g ⟨r, _⟩) n)
            (dgm k (intervalFilter f g ⟨y, _⟩) n) := bottleneck_triangle _ _ _
        _ ≤ ENNReal.ofReal ((r - x) * faceSupDifference f g) +
            ENNReal.ofReal ((y - r) * faceSupDifference f g) := add_le_add h₁ h₂
        _ = ENNReal.ofReal ((y - x) * faceSupDifference f g) := by
          rw [← ENNReal.ofReal_add
            (mul_nonneg (sub_nonneg.mpr hrxy.1.le) (faceSupDifference_nonneg f g))
            (mul_nonneg (sub_nonneg.mpr hrxy.2.le) (faceSupDifference_nonneg f g))]
          congr 1
          ring

/-- The deduplicated critical times in increasing order. The empty-face case
is `[0,1]`; simultaneous crossings occupy one list position. -/
noncomputable def finiteFilterCrossingSubdivision (f g : FilterFunction K ℝ) : List ℝ :=
  (faceCrossingTimes f g).sort

theorem finiteFilterCrossingSubdivision_strict (f g : FilterFunction K ℝ) :
    (finiteFilterCrossingSubdivision f g).SortedLT := by
  exact Finset.sortedLT_sort _

theorem mem_finiteFilterCrossingSubdivision_iff (f g : FilterFunction K ℝ)
    (t : ℝ) :
    t ∈ finiteFilterCrossingSubdivision f g ↔ t ∈ faceCrossingTimes f g := by
  exact Finset.mem_sort (· ≤ ·)

theorem finiteFilterCrossingSubdivision_endpoints (f g : FilterFunction K ℝ) :
    0 ∈ finiteFilterCrossingSubdivision f g ∧
      1 ∈ finiteFilterCrossingSubdivision f g ∧
      ∀ t ∈ finiteFilterCrossingSubdivision f g, 0 ≤ t ∧ t ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_finiteFilterCrossingSubdivision_iff f g 0).mpr
      (zero_mem_faceCrossingTimes f g)
  · exact (mem_finiteFilterCrossingSubdivision_iff f g 1).mpr
      (one_mem_faceCrossingTimes f g)
  · intro t ht
    exact faceCrossingTimes_subset_Icc f g t
      ((mem_finiteFilterCrossingSubdivision_iff f g t).mp ht)

theorem finiteFilterCrossingSubdivision_consecutive_gap (f g : FilterFunction K ℝ)
    (i j : Fin (finiteFilterCrossingSubdivision f g).length)
    (hij : j.val = i.val + 1) (r : ℝ)
    (hr : r ∈ finiteFilterCrossingSubdivision f g) :
    ¬ ((finiteFilterCrossingSubdivision f g).get i < r ∧
       r < (finiteFilterCrossingSubdivision f g).get j) := by
  let L := finiteFilterCrossingSubdivision f g
  have horder : L.Pairwise (· ≤ ·) := by
    exact Finset.pairwise_sort _ _
  obtain ⟨q, hq⟩ := List.mem_iff_get.mp hr
  intro hbetween
  by_cases hqi : q ≤ i
  · have hle := horder.rel_get_of_le hqi
    rw [hq] at hle
    exact (not_lt_of_ge hle) hbetween.1
  · have hjq : j ≤ q := by
      apply Fin.le_iff_val_le_val.mpr
      have hiq : i < q := lt_of_not_ge hqi
      omega
    have hle := horder.rel_get_of_le hjq
    rw [hq] at hle
    exact (not_lt_of_ge hle) hbetween.2

/-- Every consecutive pair of subdivision times has a common enumeration
compatible through both closed endpoints. -/
theorem finiteFilterCrossingSubdivision_segment (f g : FilterFunction K ℝ)
    {a b : ℝ} (ha : a ∈ finiteFilterCrossingSubdivision f g)
    (hb : b ∈ finiteFilterCrossingSubdivision f g) (hab : a < b)
    (hadj : ∀ r ∈ finiteFilterCrossingSubdivision f g, ¬ (a < r ∧ r < b)) :
    ∃ (m : Set.Icc (0 : ℝ) 1) (e : CompatibleOrder (intervalFilter f g m)),
      ∀ (t : Set.Icc (0 : ℝ) 1), a ≤ t → t ≤ b →
        Monotone ((intervalFilter f g t).value ∘ e.enum) := by
  have hends := finiteFilterCrossingSubdivision_endpoints f g
  exact exists_segment_compatibleOrder f g (hends.2.2 a ha).1 hab
    (hends.2.2 b hb).2 (by
      intro r hr hmem
      exact hadj r ((mem_finiteFilterCrossingSubdivision_iff f g r).mpr hmem) hr)

theorem finiteFilterCrossingSubdivision_consecutive_order
    (f g : FilterFunction K ℝ)
    (i j : Fin (finiteFilterCrossingSubdivision f g).length)
    (hij : j.val = i.val + 1) :
    ∃ (m : Set.Icc (0 : ℝ) 1)
      (e : CompatibleOrder (intervalFilter f g m)),
      ∀ (t : Set.Icc (0 : ℝ) 1),
        (finiteFilterCrossingSubdivision f g).get i ≤ t →
        t ≤ (finiteFilterCrossingSubdivision f g).get j →
          Monotone ((intervalFilter f g t).value ∘ e.enum) := by
  have hij' : i < j := Fin.lt_iff_val_lt_val.mpr (by omega)
  have hlt := (finiteFilterCrossingSubdivision_strict f g).pairwise.rel_get_of_lt hij'
  exact finiteFilterCrossingSubdivision_segment f g
    ((finiteFilterCrossingSubdivision f g).get_mem i)
    ((finiteFilterCrossingSubdivision f g).get_mem j) hlt
    (finiteFilterCrossingSubdivision_consecutive_gap f g i j hij)

/-- Bottleneck stability of sublevel persistence diagrams on a finite
complex. The coefficient field and ordered-vertex assumptions are those of
`dgm`; no genericity or essential-cardinality assumption is used. -/
theorem bottleneck_dgm_le_faceSupDifference (k : Type u) [Field k]
    (f g : FilterFunction K ℝ) (n : ℕ) :
    bottleneck (dgm k f n) (dgm k g n) ≤
      ENNReal.ofReal (faceSupDifference f g) := by
  have h := crossing_telescope k f g n (a := 0) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)
  simpa [intervalFilter, filterInterpolate_zero, filterInterpolate_one] using h

theorem dgm_empty_faces (k : Type u) [Field k]
    (f : FilterFunction K ℝ) (n : ℕ) [IsEmpty (TotalFace K)] :
    (dgm k f n).points = 0 := by
  classical
  have hm : faceCount K = 0 := Fintype.card_eq_zero
  obtain ⟨e⟩ := exists_compatibleOrder f
  rw [← evaluateFaceTemplate_eq_dgm k e f e.monotone n]
  simp [evaluateFaceTemplate, faceTemplatePairs_empty k e n hm,
    faceTemplateEssential_empty k e n hm]

theorem bottleneck_dgm_self (k : Type u) [Field k]
    (f : FilterFunction K ℝ) (n : ℕ) :
    bottleneck (dgm k f n) (dgm k f n) = 0 :=
  bottleneck_self _

end TDA.Persistence
