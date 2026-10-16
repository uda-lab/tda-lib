import TDA.Persistence.PersistenceImage

/-! Nonzero Gaussian pixel integrals, repeated occurrences and empty inputs. -/

namespace TDA.Persistence.PersistenceImage.Examples

open MeasureTheory Set GaussianKernel

/-- Clip the absolute persistence coordinate at one. -/
private noncomputable def clippedWeight : Weight 1 1 where
  toFun u := min |u.2| 1
  nonneg u := le_min (abs_nonneg _) (by norm_num)
  bounded u := min_le_right _ _
  lipschitz u v := by
    have h := abs_min_sub_min_le_max |u.2| 1 |v.2| 1
    simp only [sub_self, abs_zero] at h
    rw [max_eq_left (abs_nonneg (|u.2| - |v.2|))] at h
    calc
      _ ≤ abs (abs u.2 - abs v.2) := h
      _ ≤ |u.2 - v.2| := abs_abs_sub_abs_le_abs_sub _ _
      _ ≤ 1 * ‖u - v‖ := by
        simpa only [one_mul, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
          using le_max_right |u.1 - v.1| |u.2 - v.2|
  zero_persistence b := by simp

private def wholePixel : Unit → Set (ℝ × ℝ) := fun _ => univ

private theorem wholePixel_measurable (k : Unit) : MeasurableSet (wholePixel k) :=
  MeasurableSet.univ

private theorem wholePixel_disjoint : Pairwise (fun i j => Disjoint (wholePixel i) (wholePixel j)) := by
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

private theorem whole_feature {σ : ℝ} (hσ : 0 < σ) (p : ℝ × ℝ) :
    feature σ clippedWeight wholePixel p () = min |p.2 - p.1| 1 := by
  rw [feature_apply]
  simp [wholePixel, integral_const_mul, integral_density2D hσ, clippedWeight, birthPersistence]

-- The actual integral is nonzero; this is not a zero-feature fixture.
private theorem nonzero_feature {σ : ℝ} (hσ : 0 < σ) :
    feature σ clippedWeight wholePixel (0, 2) () = 1 := by
  rw [whole_feature hσ]
  norm_num

private def duplicate : Fin 2 → ℝ × ℝ := fun _ => (0, 2)

private theorem repeated_image {σ : ℝ} (hσ : 0 < σ) :
    image σ clippedWeight wholePixel duplicate () = 2 := by
  change (∑ i : Fin 2, feature σ clippedWeight wholePixel (duplicate i)) () = 2
  rw [Fin.sum_univ_two, PiLp.add_apply]
  norm_num [duplicate, whole_feature hσ]

private def eraseAll : OccurrenceMatching (Fin 2) (Fin 0) PEmpty.{1} PEmpty.{1} where
  finite _ := none
  finite_injective := by simp
  essential := Equiv.refl _

private theorem duplicate_to_empty_bound {σ : ℝ} (hσ : 0 < σ) :
    ‖image σ clippedWeight wholePixel duplicate -
      image σ clippedWeight wholePixel (Fin.elim0 : Fin 0 → ℝ × ℝ)‖ ≤
      stabilityConstant σ 1 1 * eraseAll.totalFiniteCost duplicate Fin.elim0 := by
  exact norm_image_sub_le_matching hσ (by norm_num) (by norm_num) clippedWeight
    wholePixel wholePixel_measurable wholePixel_disjoint eraseAll duplicate Fin.elim0
    (fun _ => by norm_num [duplicate]) (fun i => Fin.elim0 i)

private theorem empty_image {σ : ℝ} :
    image σ clippedWeight wholePixel (Fin.elim0 : Fin 0 → ℝ × ℝ) = 0 := by
  simp [image, finiteFeatureSum]

private theorem empty_pixels {I : Type*} [Fintype I] (σ : ℝ) (x : I → ℝ × ℝ) :
    image σ clippedWeight (fun _ : Fin 0 => (univ : Set (ℝ × ℝ))) x = 0 := by
  apply PiLp.ext
  intro k
  exact Fin.elim0 k

end TDA.Persistence.PersistenceImage.Examples
