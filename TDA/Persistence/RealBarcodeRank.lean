import TDA.Persistence.RealIntervalInterleaving
import TDA.Persistence.PersistenceMeasure

/-!
# Ranks of finite real barcode realizations

Each occurrence contributes one to a structure-map rank exactly when the interval
contains both parameters. Repeated intervals are separate coordinates.
-/

set_option autoImplicit false

universe u
namespace TDA.Persistence.RealBarcode
open CategoryTheory
open scoped Classical
variable {k : Type u} [Field k]

/-- An interval structure map has rank one precisely when both endpoints are alive. -/
theorem intervalImage_rank (p : ℝ × WithTop ℝ) {s t : ℝ} (hst : s ≤ t) :
    Module.finrank k (persistenceImage (RealBarcode.intervalModule (k := k) p) hst) =
      if RealBarcode.alive p s ∧ RealBarcode.alive p t then 1 else 0 := by
  classical
  let f := structureMapLinear (RealBarcode.intervalModule (k := k) p) hst
  by_cases h : RealBarcode.alive p s ∧ RealBarcode.alive p t
  · rw [if_pos h]
    have hf : Function.Surjective f := by
      intro y
      let x : RealBarcode.fiber (k := k) p s :=
        ⟨y.val, by simp [RealBarcode.fiber, h.1]⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      simpa [f, structureMapLinear, structureMap, h.2] using
        RealBarcode.map_val p (homOfLE hst) x
    change Module.finrank k (LinearMap.range f) = 1
    rw [LinearMap.range_eq_top.mpr hf, finrank_top]
    change Module.finrank k (RealBarcode.fiber (k := k) p t) = 1
    rw [show RealBarcode.fiber (k := k) p t = ⊤ by
      unfold RealBarcode.fiber
      exact if_pos h.2]
    rw [finrank_top]
    exact Module.finrank_self k
  · rw [if_neg h]
    have hf : f = 0 := by
      ext x
      apply Subtype.ext
      change (f x).val = 0
      have hv : (f x).val = if RealBarcode.alive p t then x.val else 0 :=
        RealBarcode.map_val p (homOfLE hst) x
      rw [hv]
      by_cases ht : RealBarcode.alive p t
      · rw [if_pos ht]
        have hs : ¬ RealBarcode.alive p s := fun hs => h ⟨hs, ht⟩
        have hx : (show RealBarcode.fiber (k := k) p s from x).val = 0 := by
          simpa only [RealBarcode.fiber, if_neg hs, Submodule.mem_bot] using
            (show RealBarcode.fiber (k := k) p s from x).property
        exact hx
      · rw [if_neg ht]
    change Module.finrank k (LinearMap.range f) = 0
    rw [hf, LinearMap.range_zero]
    exact finrank_bot k _


/-- The rank of a finite real barcode is its number of surviving occurrences. -/
theorem realize_image_rank (D : Diagram ℝ) {s t : ℝ} (hst : s ≤ t) :
    Module.finrank k (persistenceImage (realize (k := k) D) hst) =
      D.points.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) := by
  classical
  let f := fun i : Fin D.points.toList.length =>
    structureMapLinear (intervalModule (k := k) (D.points.toList.get i)) hst
  change Module.finrank k (LinearMap.range (LinearMap.piMap f)) = _
  letI : ∀ i : Fin D.points.toList.length,
      FiniteDimensional k ((intervalModule (k := k) (D.points.toList.get i)).obj s) :=
    fun i => by
      change FiniteDimensional k (fiber (k := k) (D.points.toList.get i) s)
      infer_instance
  rw [finrank_range_piMap f]
  calc
    _ = ∑ i : Fin D.points.toList.length,
        if (D.points.toList.get i).1 ≤ s ∧
          (t : WithTop ℝ) < (D.points.toList.get i).2 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have he : alive (D.points.toList.get i) s ∧ alive (D.points.toList.get i) t ↔
          (D.points.toList.get i).1 ≤ s ∧ (t : WithTop ℝ) < (D.points.toList.get i).2 := by
        constructor
        · exact fun h => ⟨h.1.1, h.2.2⟩
        · exact fun h => ⟨⟨h.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hst) h.2⟩,
            ⟨h.1.trans hst, h.2⟩⟩
      change Module.finrank k (persistenceImage
        (intervalModule (k := k) (D.points.toList.get i)) hst) = _
      rw [intervalImage_rank]
      simp only [he]
    _ = _ := by
      simpa only [Multiset.coe_toList] using
        (list_get_sum_countP D.points.toList
          (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2))

end TDA.Persistence.RealBarcode
