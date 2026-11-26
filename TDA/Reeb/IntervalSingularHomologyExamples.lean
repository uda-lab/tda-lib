import TDA.Reeb.IntervalSingularHomology
import Mathlib.Analysis.Convex.PathConnected

/-!
# Degree-zero interval singular homology fixtures

Fixtures for `TDA.Reeb.intervalSingularHomologyIso₀`, over an arbitrary ring `k : Type`:

* the empty interval `⊥` has zero homology (`bot_isZero`);
* an empty source space has zero homology on every interval (`emptySource_isZero`);
* for the identity of `ℝ`, the preimage of a nonempty interval is path connected, so
  `H₀(I; k) ⟶ k` is an isomorphism and every inclusion of nonempty intervals induces an
  isomorphism (`id_map_isIso`); the class of a point is unchanged by the identity arrow of an
  interval (`class_comp_map_id`);
* for `f t = t²`, the preimage of the narrow band `(1, 4)` has exactly two path components,
  `(-2, -1)` and `(1, 2)`, told apart by the sign of the point (`signEquiv`), and the preimage of
  the band `(-1, 4)` is the connected interval `(-2, 2)`. The inclusion of the narrow band
  into the wide band induces the fold `k ⊕ k ⟶ k`, the codiagonal `Sigma.desc (fun _ => 𝟙 k)`
  of two copies of `k` (`fold`), so the two components of the narrow band merge.
-/

open Set CategoryTheory Limits TDA.Topology

namespace TDA.Reeb.Examples.IntervalSingularHomology

open TDA.Reeb TDA.Reeb.OpenInterval

variable (k : Type) [Ring k]

/-! ### The empty interval and the empty source -/

/-- The empty interval has zero degree-zero homology, for any map. -/
theorem bot_isZero (f : C(ℝ, ℝ)) : IsZero ((intervalSingularHomology k 0 f).obj ⊥) :=
  isZero_intervalSingularHomology₀_obj_bot f

/-- The map out of the empty space. -/
def emptyMap : C(Empty, ℝ) :=
  ⟨fun e => e.elim, continuous_of_discreteTopology⟩

/-- Over an empty source space every interval has zero degree-zero homology. -/
theorem emptySource_isZero (I : OpenInterval) :
    IsZero ((intervalSingularHomology k 0 emptyMap).obj I) := by
  have : IsEmpty ((intervalComponents emptyMap).obj I) :=
    ⟨fun c => by
      induction c using ZerothHomotopy.rec with
      | mk x => exact x.1.elim⟩
  exact IsZero.of_iso (isZero_sigma_of_isEmpty _) ((intervalSingularHomologyIso₀ k emptyMap).app I)

/-! ### The identity of `ℝ` -/

/-- The preimage of a nonempty interval under the identity of `ℝ` is path connected. -/
theorem pathConnectedSpace_id (I : OpenInterval) (h : (I : Set ℝ).Nonempty) :
    PathConnectedSpace ((intervalPreimageTopCat (ContinuousMap.id ℝ)).obj I) :=
  isPathConnected_iff_pathConnectedSpace.1 (I.ordConnected.convex.isPathConnected h)

/-- Under the identity of `ℝ`, an inclusion of intervals with nonempty source induces an
isomorphism in degree-zero homology. -/
theorem id_map_isIso {I J : OpenInterval} (i : I ⟶ J) (h : (I : Set ℝ).Nonempty) :
    IsIso ((intervalSingularHomology k 0 (ContinuousMap.id ℝ)).map i) := by
  have hJ : (J : Set ℝ).Nonempty := h.mono (OpenInterval.le_iff_subset.1 (leOfHom i))
  have := pathConnectedSpace_id I h
  have := pathConnectedSpace_id J hJ
  have h : IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)).map
      ((intervalPreimageTopCat (ContinuousMap.id ℝ)).map i)) :=
    IsIso.of_isIso_fac_right
      (singularHomology₀ε_naturality (C := ModuleCat.{0} k)
        ((intervalPreimageTopCat (ContinuousMap.id ℝ)).map i) (ModuleCat.of k k))
  exact h

/-- The identity arrow of an interval fixes the class of a point. -/
theorem class_comp_map_id (f : C(ℝ, ℝ)) (I : OpenInterval) (x : (intervalPreimageTopCat f).obj I) :
    intervalClass k f I x ≫ (intervalSingularHomology k 0 f).map (𝟙 I) = intervalClass k f I x := by
  simp

/-! ### `f t = t²`: two components merging -/

/-- The map `t ↦ t²`. -/
def sq : C(ℝ, ℝ) := ⟨fun t => t ^ 2, by fun_prop⟩

/-- The narrow positive band `(1, 4)`, whose preimage is `(-2, -1) ∪ (1, 2)`. -/
def narrow : OpenInterval := ioo 1 4

/-- The band `(-1, 4)` from negative to positive values, whose preimage is `(-2, 2)`. -/
def wide : OpenInterval := ioo (-1) 4

theorem narrow_le_wide : narrow ≤ wide :=
  OpenInterval.le_iff_subset.2 (Ioo_subset_Ioo_left (by norm_num))

/-- The narrow band included into the wide band. -/
def narrowToWide : narrow ⟶ wide := homOfLE narrow_le_wide

theorem mem_narrow_preimage (x : ℝ) : sq x ∈ narrow ↔ 1 < x ^ 2 ∧ x ^ 2 < 4 := Iff.rfl

theorem mem_wide_preimage (x : ℝ) : sq x ∈ wide ↔ -1 < x ^ 2 ∧ x ^ 2 < 4 := Iff.rfl

/-- A path in the preimage of the narrow band cannot leave the positive half-line. -/
theorem not_path_pos_nonpos {a b : (intervalPreimageTopCat sq).obj narrow} (γ : Path a b)
    (ha : 0 < a.1) (hb : b.1 ≤ 0) : False := by
  have hg : Continuous fun t : unitInterval => (γ t).1 := continuous_subtype_val.comp γ.continuous
  obtain ⟨t, ht⟩ := intermediate_value_univ (1 : unitInterval) 0 hg
    (show (0 : ℝ) ∈ Icc ((γ 1).1) ((γ 0).1) by
      rw [γ.source, γ.target]; exact ⟨hb, ha.le⟩)
  have h := (γ t).2
  simp only [mem_narrow_preimage] at h
  have : (γ t).1 = 0 := ht
  rw [this] at h
  norm_num at h

theorem sign_iff_of_joined {a b : (intervalPreimageTopCat sq).obj narrow} (h : Joined a b) :
    0 < a.1 ↔ 0 < b.1 := by
  obtain ⟨γ⟩ := h
  constructor
  · intro ha
    by_contra hb
    exact not_path_pos_nonpos γ ha (not_lt.1 hb)
  · intro hb
    by_contra ha
    exact not_path_pos_nonpos γ.symm hb (not_lt.1 ha)

/-- The point `3/2` of the positive component. -/
noncomputable def posPoint : (intervalPreimageTopCat sq).obj narrow :=
  ⟨3 / 2, by rw [mem_narrow_preimage]; norm_num⟩

/-- The point `-3/2` of the negative component. -/
noncomputable def negPoint : (intervalPreimageTopCat sq).obj narrow :=
  ⟨-3 / 2, by rw [mem_narrow_preimage]; norm_num⟩

theorem joined_posPoint (x : (intervalPreimageTopCat sq).obj narrow) (hx : 0 < x.1) :
    Joined posPoint x := by
  have hx' : x.1 ∈ Ioo (1 : ℝ) 2 := by
    have h := x.2
    rw [mem_narrow_preimage] at h
    constructor <;> nlinarith [h.1, h.2]
  have hJ := ((convex_Ioo (1 : ℝ) 2).isPathConnected ⟨3 / 2, by norm_num⟩).joinedIn
    (3 / 2) (by norm_num) x.1 hx'
  have hsub : Ioo (1 : ℝ) 2 ⊆ sq ⁻¹' (narrow : Set ℝ) := fun y hy => by
    show sq y ∈ narrow
    rw [mem_narrow_preimage]
    constructor <;> nlinarith [hy.1, hy.2]
  exact (hJ.mono hsub).joined_subtype

theorem joined_negPoint (x : (intervalPreimageTopCat sq).obj narrow) (hx : ¬ 0 < x.1) :
    Joined negPoint x := by
  have hx' : x.1 ∈ Ioo (-2 : ℝ) (-1) := by
    have h := x.2
    rw [mem_narrow_preimage] at h
    have hx0 : x.1 < 0 := lt_of_le_of_ne (not_lt.1 hx) (by rintro h0; rw [h0] at h; norm_num at h)
    constructor <;> nlinarith [h.1, h.2]
  have hJ := ((convex_Ioo (-2 : ℝ) (-1)).isPathConnected ⟨-3 / 2, by norm_num⟩).joinedIn
    (-3 / 2) (by norm_num) x.1 hx'
  have hsub : Ioo (-2 : ℝ) (-1) ⊆ sq ⁻¹' (narrow : Set ℝ) := fun y hy => by
    show sq y ∈ narrow
    rw [mem_narrow_preimage]
    constructor <;> nlinarith [hy.1, hy.2]
  exact (hJ.mono hsub).joined_subtype

/-- The preimage of the narrow band has exactly two path components, the sign of the point
telling them apart. -/
noncomputable def signEquiv : ZerothHomotopy ((intervalPreimageTopCat sq).obj narrow) ≃ Bool where
  toFun := ZerothHomotopy.lift (fun x => decide (0 < x.1))
    (fun _ _ h => by simpa using sign_iff_of_joined ⟨h⟩)
  invFun b := ZerothHomotopy.mk (if b then posPoint else negPoint)
  left_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x =>
      by_cases hx : 0 < x.1
      · simp only [hx, ZerothHomotopy.lift_mk, decide_true, ite_true]
        exact ZerothHomotopy.sound (joined_posPoint x hx).somePath
      · simp only [hx, ZerothHomotopy.lift_mk, decide_false, Bool.false_eq_true, ite_false]
        exact ZerothHomotopy.sound (joined_negPoint x hx).somePath
  right_inv b := by
    cases b
    · simp only [Bool.false_eq_true, ZerothHomotopy.lift_mk, decide_eq_false_iff_not,
        not_lt, negPoint]
      norm_num
    · simp only [ZerothHomotopy.lift_mk, decide_eq_true_eq, posPoint]
      norm_num

@[simp]
theorem signEquiv_mk (x : (intervalPreimageTopCat sq).obj narrow) :
    signEquiv (ZerothHomotopy.mk x) = decide (0 < x.1) := rfl

/-- The preimage of the wide band is the interval `(-2, 2)`, hence path connected. -/
instance wide_pathConnectedSpace : PathConnectedSpace ((intervalPreimageTopCat sq).obj wide) := by
  have hset : (sq ⁻¹' (wide : Set ℝ)) = Ioo (-2) 2 := by
    ext x
    rw [mem_preimage, SetLike.mem_coe, mem_wide_preimage, mem_Ioo]
    constructor
    · rintro ⟨-, h⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  have hc : IsPathConnected (sq ⁻¹' (wide : Set ℝ)) := by
    rw [hset]
    exact (convex_Ioo (-2 : ℝ) 2).isPathConnected ⟨0, by norm_num⟩
  exact isPathConnected_iff_pathConnectedSpace.1 hc

set_option backward.isDefEq.respectTransparency false in
/-- **Fold.** The two components of `f ⁻¹ (1, 4)` merge in the connected `f ⁻¹ (-1, 4)`: the
inclusion induces, up to isomorphisms, the codiagonal `k ⊕ k ⟶ k`. -/
theorem fold :
    ∃ (a : (intervalSingularHomology k 0 sq).obj narrow ≅
        ∐ fun _ : Bool => ModuleCat.of k k)
      (b : (intervalSingularHomology k 0 sq).obj wide ≅ ModuleCat.of k k),
      a.inv ≫ (intervalSingularHomology k 0 sq).map narrowToWide ≫ b.hom =
        Sigma.desc fun _ => 𝟙 (ModuleCat.of k k) := by
  let b := asIso (TopCat.singularHomology₀ε ((intervalPreimageTopCat sq).obj wide)
    (ModuleCat.of k k))
  refine ⟨(intervalSingularHomologyIso₀ k sq).app narrow ≪≫
      (sigmaConst.obj (ModuleCat.of k k)).mapIso signEquiv.toIso, b, ?_⟩
  have hnat : (intervalSingularHomology k 0 sq).map narrowToWide ≫
      TopCat.singularHomology₀ε ((intervalPreimageTopCat sq).obj wide) (ModuleCat.of k k) =
        TopCat.singularHomology₀ε ((intervalPreimageTopCat sq).obj narrow) (ModuleCat.of k k) :=
    singularHomology₀ε_naturality (C := ModuleCat.{0} k)
      ((intervalPreimageTopCat sq).map narrowToWide) (ModuleCat.of k k)
  have hI := TopCat.singularHomology₀Iso_sigma_desc_id ((intervalPreimageTopCat sq).obj narrow)
    (ModuleCat.of k k)
  show (_ ≪≫ _).inv ≫ ((intervalSingularHomology k 0 sq).map narrowToWide ≫
    TopCat.singularHomology₀ε _ _) = _
  rw [hnat, ← hI]
  refine Sigma.hom_ext _ _ fun c => ?_
  simp [sigmaConst, intervalSingularHomologyIso₀_inv_app]
  exact Sigma.ι_comp_desc (fun _ => 𝟙 (ModuleCat.of k k)) _

end TDA.Reeb.Examples.IntervalSingularHomology
