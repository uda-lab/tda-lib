import TDA.Persistence.GaussianKernel

/-!
# Gaussian persistence images in the finite ℓ¹ norm

A fixed finite family of measurable disjoint pixels integrates the Gaussian surface
into `PiLp 1`, whose norm is the sum of absolute coordinate values. Weight conditions
are stated in birth–persistence coordinates. The final bound charges every finite
partial matching in the existing birth–death maximum norm, with no essential bars.
-/

namespace TDA.Persistence.PersistenceImage

open MeasureTheory Set
open GaussianKernel

variable {K : Type*} [Fintype K]

/-- Integrate a scalar surface over each fixed pixel. -/
noncomputable def pixelIntegral (P : K → Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) :
    PiLp 1 (fun _ : K => ℝ) := WithLp.toLp 1 (fun k => ∫ z in P k, f z)

omit [Fintype K] in
@[simp] theorem pixelIntegral_apply (P : K → Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) (k : K) :
    pixelIntegral P f k = ∫ z in P k, f z := rfl

/-- Disjoint pixels cannot increase the L¹ norm of an integrable surface. -/
theorem norm_pixelIntegral_le (P : K → Set (ℝ × ℝ))
    (hm : ∀ k, MeasurableSet (P k)) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ℝ × ℝ → ℝ) (hf : Integrable f) :
    ‖pixelIntegral P f‖ ≤ ∫ z, |f z| := by
  classical
  rw [PiLp.norm_eq_of_L1]
  change (∑ k, |∫ z in P k, f z|) ≤ _
  calc
    _ ≤ ∑ k, ∫ z in P k, |f z| := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (f := f) (μ := volume.restrict (P k))
    _ = ∫ z in ⋃ k, P k, |f z| :=
      (integral_iUnion_fintype hm hd (fun _ => hf.abs.integrableOn)).symm
    _ ≤ _ := setIntegral_le_integral hf.abs (ae_of_all _ (fun z => abs_nonneg (f z)))

/-- Pixel integration also contracts integrable surface differences in ℓ¹. -/
theorem norm_pixelIntegral_sub_le (P : K → Set (ℝ × ℝ))
    (hm : ∀ k, MeasurableSet (P k)) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f g : ℝ × ℝ → ℝ) (hf : Integrable f) (hg : Integrable g) :
    ‖pixelIntegral P f - pixelIntegral P g‖ ≤ ∫ z, |f z - g z| := by
  have he : pixelIntegral P f - pixelIntegral P g = pixelIntegral P (fun z => f z - g z) := by
    apply PiLp.ext
    intro k
    change (∫ z in P k, f z) - (∫ z in P k, g z) = ∫ z in P k, f z - g z
    exact (integral_sub hf.integrableOn hg.integrableOn).symm
  rw [he]
  exact norm_pixelIntegral_le P hm hd _ (hf.sub hg)

theorem norm_gaussianPixels_le_one {σ : ℝ} (hσ : 0 < σ) (P : K → Set (ℝ × ℝ))
    (hm : ∀ k, MeasurableSet (P k)) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (u : ℝ × ℝ) : ‖pixelIntegral P (density2D σ u)‖ ≤ 1 := by
  calc
    _ ≤ ∫ z, |density2D σ u z| :=
      norm_pixelIntegral_le P hm hd _ (integrable_density2D σ u)
    _ = 1 := by
      simp_rw [abs_of_nonneg (density2D_nonneg σ u _)]
      exact integral_density2D hσ u

theorem norm_gaussianPixels_sub_le {σ : ℝ} (hσ : 0 < σ) (P : K → Set (ℝ × ℝ))
    (hm : ∀ k, MeasurableSet (P k)) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (u v : ℝ × ℝ) :
    ‖pixelIntegral P (density2D σ u) - pixelIntegral P (density2D σ v)‖ ≤
      translationConstant σ * (|u.1 - v.1| + |u.2 - v.2|) :=
  (norm_pixelIntegral_sub_le P hm hd _ _ (integrable_density2D σ u)
    (integrable_density2D σ v)).trans (integral_abs_density2D_sub_le hσ u v)

/-- Primitive conditions on a weight in birth–persistence coordinates.
No Gaussian or diagram stability estimate is stored in this structure. -/
structure Weight (A B : ℝ) where
  toFun : ℝ × ℝ → ℝ
  nonneg : ∀ u, 0 ≤ toFun u
  bounded : ∀ u, toFun u ≤ B
  lipschitz : ∀ u v, |toFun u - toFun v| ≤ A * ‖u - v‖
  zero_persistence : ∀ b, toFun (b, 0) = 0

instance {A B : ℝ} : CoeFun (Weight A B) (fun _ => ℝ × ℝ → ℝ) := ⟨Weight.toFun⟩

/-- One birth–death occurrence's weighted Gaussian pixel feature. -/
noncomputable def feature {A B : ℝ} (σ : ℝ) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (p : ℝ × ℝ) : PiLp 1 (fun _ : K => ℝ) :=
  w (birthPersistence p) • pixelIntegral P (density2D σ (birthPersistence p))

omit [Fintype K] in
/-- Each feature coordinate is the integral of the weighted density. -/
theorem feature_apply {A B : ℝ} (σ : ℝ) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (p : ℝ × ℝ) (k : K) :
    feature σ w P p k = ∫ z in P k, w (birthPersistence p) *
      density2D σ (birthPersistence p) z := by
  change w (birthPersistence p) * (∫ z in P k, density2D σ (birthPersistence p) z) = _
  exact (integral_const_mul _ _).symm

theorem integrable_weighted_density {A B : ℝ} (σ : ℝ) (w : Weight A B)
    (p : ℝ × ℝ) : Integrable (fun z => w (birthPersistence p) *
      density2D σ (birthPersistence p) z) :=
  (integrable_density2D σ (birthPersistence p)).const_mul _

theorem norm_feature_le_weight {σ A B : ℝ} (hσ : 0 < σ) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ k, MeasurableSet (P k))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (p : ℝ × ℝ) :
    ‖feature σ w P p‖ ≤ w (birthPersistence p) := by
  rw [feature, norm_smul, Real.norm_eq_abs, abs_of_nonneg (w.nonneg _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (norm_gaussianPixels_le_one hσ P hm hd (birthPersistence p)) (w.nonneg _)

/-- The coordinate ℓ¹ displacement of T is at most three times the birth–death
maximum-norm displacement. -/
theorem birthPersistence_l1_sub_le (p q : ℝ × ℝ) :
    |(birthPersistence p).1 - (birthPersistence q).1| +
      |(birthPersistence p).2 - (birthPersistence q).2| ≤ 3 * ‖p - q‖ := by
  have ht : |(p.2 - q.2) - (p.1 - q.1)| ≤ |p.2 - q.2| + |p.1 - q.1| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (p.2 - q.2) 0 (p.1 - q.1)
  simp only [birthPersistence, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  rw [show p.2 - p.1 - (q.2 - q.1) = (p.2 - q.2) - (p.1 - q.1) by ring]
  have h₁ := le_max_left |p.1 - q.1| |p.2 - q.2|
  have h₂ := le_max_right |p.1 - q.1| |p.2 - q.2|
  linarith

/-- Explicit nonsharp coefficient for maximum-norm Lipschitz weights. -/
noncomputable def stabilityConstant (σ A B : ℝ) : ℝ :=
  2 * A + 3 * B * translationConstant σ

theorem stabilityConstant_nonneg {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ stabilityConstant σ A B := by
  unfold stabilityConstant
  have hc := translationConstant_nonneg hσ
  positivity

/-- The Gaussian and pixel estimates discharge the paired feature-map hypothesis. -/
theorem norm_feature_sub_le {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : Weight A B) (P : K → Set (ℝ × ℝ)) (hm : ∀ k, MeasurableSet (P k))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (p q : ℝ × ℝ) :
    ‖feature σ w P p - feature σ w P q‖ ≤ stabilityConstant σ A B * ‖p - q‖ := by
  let u := birthPersistence p
  let v := birthPersistence q
  let G := fun a => pixelIntegral P (density2D σ a)
  have hc := translationConstant_nonneg hσ
  have hv : ‖G v‖ ≤ 1 := norm_gaussianPixels_le_one hσ P hm hd v
  have hg : ‖G u - G v‖ ≤ (3 * translationConstant σ) * ‖p - q‖ := by
    calc
      _ ≤ translationConstant σ * (|u.1 - v.1| + |u.2 - v.2|) :=
        norm_gaussianPixels_sub_le hσ P hm hd u v
      _ ≤ translationConstant σ * (3 * ‖p - q‖) :=
        mul_le_mul_of_nonneg_left (birthPersistence_l1_sub_le p q) hc
      _ = _ := by ring
  have hw : |w u - w v| ≤ (2 * A) * ‖p - q‖ := by
    calc
      _ ≤ A * ‖u - v‖ := w.lipschitz u v
      _ ≤ A * (2 * ‖p - q‖) :=
        mul_le_mul_of_nonneg_left (norm_birthPersistence_sub_le p q) hA
      _ = _ := by ring
  have hwb : |w u| ≤ B := by rw [abs_of_nonneg (w.nonneg _)]; exact w.bounded _
  have he : feature σ w P p - feature σ w P q =
      (w u - w v) • G v + w u • (G u - G v) := by
    dsimp [feature, G, u, v]
    module
  rw [he]
  calc
    _ ≤ ‖(w u - w v) • G v‖ + ‖w u • (G u - G v)‖ := norm_add_le _ _
    _ = |w u - w v| * ‖G v‖ + |w u| * ‖G u - G v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ((2 * A) * ‖p - q‖) * 1 + B * ((3 * translationConstant σ) * ‖p - q‖) :=
      add_le_add (mul_le_mul hw hv (norm_nonneg _) (by positivity))
        (mul_le_mul hwb hg (norm_nonneg _) hB)
    _ = _ := by unfold stabilityConstant; ring

/-- Vanishing of the weight at persistence zero discharges the diagonal hypothesis. -/
theorem norm_feature_diagonal_le {σ A B : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B)
    (w : Weight A B) (P : K → Set (ℝ × ℝ)) (hm : ∀ k, MeasurableSet (P k))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (p : ℝ × ℝ) (hp : p.1 < p.2) :
    ‖feature σ w P p‖ ≤ stabilityConstant σ A B * (diagonalCost p).toReal := by
  have hw := w.lipschitz (birthPersistence p) (p.1, 0)
  have ht : ‖birthPersistence p - (p.1, 0)‖ = p.2 - p.1 := by
    simp [birthPersistence, Prod.norm_def, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hp)]
    exact hp.le
  rw [w.zero_persistence, sub_zero, abs_of_nonneg (w.nonneg _), ht] at hw
  have hcost : (diagonalCost p).toReal = (p.2 - p.1) / 2 := by
    rw [diagonalCost_toReal, abs_of_pos (sub_pos.mpr hp)]
  have hC : 2 * A ≤ stabilityConstant σ A B := by
    unfold stabilityConstant
    have hc := translationConstant_nonneg hσ
    have hnonneg : 0 ≤ 3 * B * translationConstant σ := by positivity
    linarith
  calc
    _ ≤ w (birthPersistence p) := norm_feature_le_weight hσ w P hm hd p
    _ ≤ A * (p.2 - p.1) := hw
    _ = (2 * A) * (diagonalCost p).toReal := by rw [hcost]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC ENNReal.toReal_nonneg

/-- A finite image sums occurrence features, retaining multiplicity. -/
noncomputable def image {I : Type*} [Fintype I] {A B : ℝ} (σ : ℝ) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (x : I → ℝ × ℝ) : PiLp 1 (fun _ : K => ℝ) :=
  finiteFeatureSum (feature σ w P) x

omit [Fintype K] in
/-- The image coordinates are integrals of the finite weighted Gaussian surface. -/
theorem image_apply {I : Type*} [Fintype I] {A B : ℝ} (σ : ℝ) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (x : I → ℝ × ℝ) (k : K) :
    image σ w P x k = ∫ z in P k, ∑ i, w (birthPersistence (x i)) *
      density2D σ (birthPersistence (x i)) z := by
  classical
  have hsum (s : Finset I) : (∑ i ∈ s, feature σ w P (x i)) k =
      ∑ i ∈ s, feature σ w P (x i) k := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, PiLp.add_apply, ih]
  change (∑ i, feature σ w P (x i)) k = _
  rw [hsum]
  simp_rw [feature_apply]
  exact (integral_finsetSum _ (fun i _ =>
    (integrable_weighted_density σ w (x i)).integrableOn)).symm

/-- Gaussian PI stability for every finite partial occurrence matching.
The norm is the pixel vector ℓ¹ norm; all deaths are finite and essential bars are absent. -/
theorem norm_image_sub_le_matching {I J : Type*} [Fintype I] [Fintype J]
    {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ k, MeasurableSet (P k))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    ‖image σ w P x - image σ w P y‖ ≤
      stabilityConstant σ A B * M.totalFiniteCost x y :=
  M.norm_featureSum_sub_le (feature σ w P) (stabilityConstant σ A B)
    (stabilityConstant_nonneg hσ hA hB)
    (fun p q _ _ => norm_feature_sub_le hσ hA hB w P hm hd p q)
    (fun p hp => norm_feature_diagonal_le hσ hB w P hm hd p hp) x y hx hy

end TDA.Persistence.PersistenceImage
