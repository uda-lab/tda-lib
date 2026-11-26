import TDA.Reeb.IntervalSingularHomologyStability
import TDA.Reeb.IntervalSingularHomologyExamples

/-!
# Perturbation stability of interval singular homology: fixtures

Fixtures for `TDA.Reeb.intervalSingularHomologyInterleaving`, over an arbitrary ring `k : Type`:

* an empty source space, where every parameter works, including `0`, and the distance is `0`
  (`empty_interleaving`, `empty_distance_eq_zero`);
* parameter `ε = 0`: the pointwise bound `|f x − g x| ≤ 0` gives an isomorphism of the interval
  functors (`zero_nonempty_iso`), and `f = g` gives the identity witness at every parameter;
* empty preimages: if no point of `X` lies over `I`, degree-zero homology at `I` vanishes
  (`isZero_obj_of_preimage_empty`);
* constant maps from a point at heights `a` and `b`, over a nontrivial ring: the distance is
  exactly `|a − b|` (`interleavingDistance_const`). The upper bound is the stability theorem. For
  the lower bound, if `ε < |a − b|`, a small open interval `I` around `a` has an `ε`-thickening
  omitting `b`; then `H₀(g ⁻¹ T_ε I) = 0`, so the first composite
  `H₀(f ⁻¹ I) ⟶ H₀(g ⁻¹ T_ε I) ⟶ H₀(f ⁻¹ T_ε T_ε I)` factors through zero, while the transition
  `H₀(f ⁻¹ I) ⟶ H₀(f ⁻¹ T_ε T_ε I)` of the point is an isomorphism, the identity on `k`
  (`isEmpty_interleaving_const`). Hence unequal heights are not isomorphic
  (`not_nonempty_iso_const`).
-/

open Set CategoryTheory Limits AlgebraicTopology TDA.Topology
open scoped NNReal ENNReal UniformConvergence

namespace TDA.Reeb.Examples.IntervalSingularHomologyStability

open TDA.Reeb TDA.Reeb.OpenInterval

variable (k : Type) [Ring k]

/-! ### Empty source -/

/-- Over an empty source every parameter is attained, in every degree. -/
noncomputable def empty_interleaving (n : ℕ) {X : Type} [TopologicalSpace X] [IsEmpty X] (f g : C(X, ℝ))
    (ε : ℝ≥0) :
    Interleaving ε (intervalSingularHomology k n f) (intervalSingularHomology k n g) :=
  intervalSingularHomologyInterleaving (fun x => isEmptyElim x)

/-- Over an empty source the distance is `0`, derived through the supremum bound. -/
theorem empty_distance_eq_zero (n : ℕ) {X : Type} [TopologicalSpace X] [IsEmpty X]
    (f g : C(X, ℝ)) :
    interleavingDistance (intervalSingularHomology k n f) (intervalSingularHomology k n g) = 0 := by
  have he : edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) = 0 := by
    rw [edist_uniformFun_ofFun_eq_iSup, iSup_of_empty, bot_eq_zero]
  exact le_antisymm
    ((interleavingDistance_intervalSingularHomology_le_edist f g).trans_eq he) zero_le

/-! ### Parameter zero -/

/-- At `ε = 0` the pointwise bound makes the interval functors isomorphic. -/
theorem zero_nonempty_iso (n : ℕ) {X : Type} [TopologicalSpace X] {f g : C(X, ℝ)}
    (h : ∀ x, |f x - g x| ≤ ((0 : ℝ≥0) : ℝ)) :
    Nonempty (intervalSingularHomology k n f ≅ intervalSingularHomology k n g) :=
  ⟨(intervalSingularHomologyInterleaving h).toIso⟩

/-- `f = g` at `ε = 0` is the identity witness. -/
example (n : ℕ) {X : Type} [TopologicalSpace X] (f : C(X, ℝ)) :
    intervalSingularHomologyInterleaving (k := k) (n := n)
        (f := f) (g := f) (ε := 0) (fun x => by simp) =
      Interleaving.refl 0 (intervalSingularHomology k n f) :=
  intervalSingularHomologyInterleaving_self f _

/-! ### Empty preimages -/

/-- If no point lies over `I`, the degree-zero homology at `I` vanishes. -/
theorem isZero_obj_of_preimage_empty {X : Type} [TopologicalSpace X] (f : C(X, ℝ))
    (I : OpenInterval) (h : ∀ x, f x ∉ I) : IsZero ((intervalSingularHomology k 0 f).obj I) := by
  have : IsEmpty ((intervalComponents f).obj I) :=
    ⟨fun c => by
      induction c using ZerothHomotopy.rec with
      | mk x => exact h x.1 x.2⟩
  exact IsZero.of_iso (isZero_sigma_of_isEmpty _) ((intervalSingularHomologyIso₀ k f).app I)

/-! ### Constant maps from a point -/

/-- The constant map from a point at height `a`. -/
def pointAt (a : ℝ) : C(Unit, ℝ) := ContinuousMap.const Unit a

/-- The preimage of an interval containing the height of a constant map is a point, hence path
connected. -/
theorem pathConnectedSpace_pointAt (a : ℝ) (I : OpenInterval) (ha : a ∈ I) :
    PathConnectedSpace ((intervalPreimageTopCat (pointAt a)).obj I) :=
  ⟨⟨⟨(), ha⟩⟩, fun x y => by
    have hxy : x = y := Subtype.ext (Subsingleton.elim x.1 y.1)
    rw [hxy]⟩

/-- If `ε < |a − b|`, there is an open interval around `a` containing `a` whose `ε`-thickening
omits `b`. -/
theorem exists_interval_not_mem_thicken {a b : ℝ} {ε : ℝ≥0} (hε : (ε : ℝ) < |a - b|) :
    ∃ I : OpenInterval, a ∈ I ∧ b ∉ thicken ε I := by
  set η : ℝ := (|a - b| - ε) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  refine ⟨ioo (a - η) (a + η), ⟨by linarith, by linarith⟩, fun hb => ?_⟩
  obtain ⟨z, hz, hbz⟩ := mem_thicken.1 hb
  have hz' : |z - a| < η := abs_lt.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have h1 : |a - b| ≤ |a - z| + |z - b| := abs_sub_le a z b
  rw [abs_sub_comm a z, abs_sub_comm z b] at h1
  linarith

/-- **Sharpness.** Over a nontrivial ring there is no `ε`-interleaving of the interval
homologies of two constant maps from a point at heights at distance more than `ε`. -/
theorem isEmpty_interleaving_const [Nontrivial k] {a b : ℝ} {ε : ℝ≥0} (hε : (ε : ℝ) < |a - b|) :
    IsEmpty (Interleaving ε (intervalSingularHomology k 0 (pointAt a))
      (intervalSingularHomology k 0 (pointAt b))) := by
  refine ⟨fun i => ?_⟩
  obtain ⟨I, haI, hbI⟩ := exists_interval_not_mem_thicken hε
  -- the target value at the thickening is zero: its preimage is empty
  have hZ : IsZero ((intervalSingularHomology k 0 (pointAt b)).obj (thicken ε I)) :=
    isZero_obj_of_preimage_empty k _ _ fun _ => hbI
  -- hence the first composite is zero
  have hφ : i.φ.app I = 0 := hZ.eq_of_tgt _ _
  have htri := i.φ_ψ_app I
  rw [hφ, zero_comp] at htri
  -- the transition on `H₀` of the point is an isomorphism, so it cannot vanish
  set J : OpenInterval := thicken ε (thicken ε I)
  set u : I ⟶ J := homOfLE ((le_thicken ε I).trans (le_thicken ε _))
  have hmap : (intervalSingularHomology k 0 (pointAt a)).map u = 0 := htri.symm
  have h1 := singularHomology₀ε_naturality (C := ModuleCat k)
    ((intervalPreimageTopCat (pointAt a)).map u) (ModuleCat.of k k)
  have hpc := pathConnectedSpace_pointAt a I haI
  have hε0 : TopCat.singularHomology₀ε ((intervalPreimageTopCat (pointAt a)).obj I)
      (ModuleCat.of k k) = 0 := by
    rw [← h1]
    exact (congrArg (· ≫ _) hmap).trans (zero_comp)
  have hid : 𝟙 _ = (0 : ((singularHomologyFunctor (ModuleCat k) 0).obj (ModuleCat.of k k)).obj
      ((intervalPreimageTopCat (pointAt a)).obj I) ⟶ _) := by
    rw [← cancel_mono (TopCat.singularHomology₀ε ((intervalPreimageTopCat (pointAt a)).obj I)
      (ModuleCat.of k k)), hε0]
    simp
  have hsub : Subsingleton (ModuleCat.of k k) := by
    have hz : IsZero (((singularHomologyFunctor (ModuleCat k) 0).obj (ModuleCat.of k k)).obj
        ((intervalPreimageTopCat (pointAt a)).obj I)) := (IsZero.iff_id_eq_zero _).2 hid
    exact ModuleCat.subsingleton_of_isZero
      (IsZero.of_iso hz (asIso (TopCat.singularHomology₀ε ((intervalPreimageTopCat (pointAt a)).obj I)
        (ModuleCat.of k k))).symm)
  exact not_subsingleton k (inferInstanceAs (Subsingleton k))

/-- The supremum distance of two constant maps from a point is the difference of the heights. -/
theorem edist_pointAt (a b : ℝ) :
    edist (UniformFun.ofFun ⇑(pointAt a)) (UniformFun.ofFun ⇑(pointAt b)) =
      ENNReal.ofReal |a - b| := by
  rw [edist_uniformFun_ofFun_eq_iSup, ciSup_unique]
  rfl

/-- **Constant maps from a point.** Over a nontrivial ring, the interval homologies of the
constant maps at heights `a` and `b` are at interleaving distance exactly `|a − b|`: the upper
bound is the supremum stability theorem and the lower bound is `isEmpty_interleaving_const`. -/
theorem interleavingDistance_const [Nontrivial k] (a b : ℝ) :
    interleavingDistance (intervalSingularHomology k 0 (pointAt a))
      (intervalSingularHomology k 0 (pointAt b)) = ENNReal.ofReal |a - b| := by
  refine le_antisymm
    ((interleavingDistance_intervalSingularHomology_le_edist _ _).trans_eq (edist_pointAt a b)) ?_
  refine le_interleavingDistance_iff.2 fun ε ⟨i⟩ => ?_
  by_contra hlt
  rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal] at hlt
  exact (isEmpty_interleaving_const k (not_le.1 hlt)).false i

/-- The distance is attained at the parameter `|a − b|`, by the stability witness. -/
example (a b : ℝ) :
    Nonempty (Interleaving (Real.nnabs (a - b)) (intervalSingularHomology k 0 (pointAt a))
      (intervalSingularHomology k 0 (pointAt b))) :=
  nonempty_interleaving_intervalSingularHomology fun _ => by
    rw [Real.coe_nnabs]
    exact le_rfl

/-- Parameter zero: constant maps at different heights have non-isomorphic interval
homologies. -/
theorem not_nonempty_iso_const [Nontrivial k] {a b : ℝ} (hab : a ≠ b) :
    ¬ Nonempty (intervalSingularHomology k 0 (pointAt a) ≅
      intervalSingularHomology k 0 (pointAt b)) := fun ⟨e⟩ =>
  (isEmpty_interleaving_const k (ε := 0) (by simpa [sub_eq_zero] using hab)).false
    (Interleaving.ofIso e)

/-- Equal heights: both sides are `0`. -/
example [Nontrivial k] (a : ℝ) :
    interleavingDistance (intervalSingularHomology k 0 (pointAt a))
      (intervalSingularHomology k 0 (pointAt a)) = 0 := by
  rw [interleavingDistance_const]
  simp

/-! ### The class of a point under the witness -/

/-- In degree zero, the witness sends the class of a point to the class of the same point. -/
example {X : Type} [TopologicalSpace X] {f g : C(X, ℝ)} {ε : ℝ≥0} (h : ∀ x, |f x - g x| ≤ ε)
    (I : OpenInterval) (x : (intervalPreimageTopCat f).obj I) :
    intervalClass k f I x ≫ (intervalSingularHomologyInterleaving (k := k) (n := 0) h).φ.app I =
      intervalClass k g (thicken ε I) ⟨x.1, preimage_subset_preimage_thicken h I x.2⟩ :=
  intervalClass_comp_intervalSingularHomologyPerturbation_app h I x

end TDA.Reeb.Examples.IntervalSingularHomologyStability
