import TDA.Reeb.GeometricThickening

/-!
# Fixtures for the geometric thickening

Acceptance fixtures for `TDA.Reeb.GeometricThickening`, with the actual comparison
`componentComparison` into the actual smoothing of the actual interval components:

* **Every kind of open interval.** For an arbitrary space and height, both inverse images are empty
  at `⊥`, and the comparison is bijective at `⊥`, at bounded intervals, at both kinds of rays and
  at `⊤`.
* **`ε = 0`.** The clamp is `0`, clamp membership holds for an arbitrary interval, and the
  comparison is bijective.
* **Empty space.** At every universe, both sides are empty and the comparison is bijective.
* **Constant height on a point.** The thickened point `(*, 1)` has height `1` while its projection
  has height `0`, so the first projection is not a map over `ℝ`.
* **Constant height on `[0, 1]`.** At `ε = 1` and `I = ℝ` the first projection is not injective,
  while the comparison is bijective.
* **Collapse.** `Bool → PUnit` over height `0` is a noninjective height-preserving map. Both
  composites of its component square send the class of `(true, 0)` to the class of the point. The
  target is a single class, so this square alone cannot detect a wrong map.
* **Exchange.** `Bool.not` over height `0` is a height-preserving map. Both composites of its
  component square send the class of `(true, 0)` to the class of `false`, and the classes of `false`
  and `true` differ.
* **Reparametrization.** `bandHomeomorph` evaluated at a point.
-/

open Set Topology CategoryTheory
open scoped NNReal

universe u

namespace TDA.Reeb

noncomputable section

namespace Examples.GeometricThickening

open OpenInterval TDA.Reeb.GeometricThickening

/-! ### Every kind of open interval, for an arbitrary space -/

section Intervals

variable {X : Type u} [TopologicalSpace X] (f : C(X, ℝ)) (ε : ℝ≥0)

/-- At `⊥` both inverse images are empty. -/
theorem bot_isEmpty :
    IsEmpty {z : X × Band ε // height f ε z ∈ (⊥ : OpenInterval)} ∧
      IsEmpty {x : X // f x ∈ thicken ε ⊥} :=
  ⟨⟨fun z => z.2⟩, ⟨fun x => by
    obtain ⟨y, hy⟩ := nonempty_of_mem_thicken x.2
    exact hy⟩⟩

theorem bijective_bot : Function.Bijective ((componentComparison f ε).app ⊥) :=
  componentComparison_app_bijective f ε ⊥

theorem bijective_ioo (a b : ℝ) :
    Function.Bijective ((componentComparison f ε).app (ioo a b)) :=
  componentComparison_app_bijective f ε _

theorem bijective_ioi (a : ℝ) : Function.Bijective ((componentComparison f ε).app (ioi a)) :=
  componentComparison_app_bijective f ε _

theorem bijective_iio (b : ℝ) : Function.Bijective ((componentComparison f ε).app (iio b)) :=
  componentComparison_app_bijective f ε _

theorem bijective_top : Function.Bijective ((componentComparison f ε).app ⊤) :=
  componentComparison_app_bijective f ε ⊤

end Intervals

/-! ### `ε = 0` -/

/-- At `ε = 0` the clamp is `0`. -/
theorem clamp_zero (c s : ℝ) : (clamp 0 c s : ℝ) = 0 :=
  eq_zero_of_mem_band_zero (clamp 0 c s).2

/-- The clamp membership lemma at `ε = 0`, for an arbitrary interval. -/
theorem add_clamp_mem_zero {I : OpenInterval} {c s : ℝ} (hc : c ∈ I) (hs : s ∈ I) :
    s + (clamp 0 c s : ℝ) ∈ I :=
  add_clamp_mem hc (by rwa [thicken_zero])

theorem bijective_zero {X : Type u} [TopologicalSpace X] (f : C(X, ℝ)) (I : OpenInterval) :
    Function.Bijective ((componentComparison f 0).app I) :=
  componentComparison_app_bijective f 0 I

/-! ### The empty space, at an arbitrary universe -/

theorem empty_isEmpty (f : C(PEmpty.{u + 1}, ℝ)) (ε : ℝ≥0) (I : OpenInterval) :
    IsEmpty ((intervalComponents (height f ε)).obj I) ∧
      IsEmpty (((smoothing ε).obj (intervalComponents f)).obj I) :=
  ⟨componentFunctor_obj_isEmpty_of_isEmpty _ _, componentFunctor_obj_isEmpty_of_isEmpty _ _⟩

theorem empty_bijective (f : C(PEmpty.{u + 1}, ℝ)) (ε : ℝ≥0) (I : OpenInterval) :
    Function.Bijective ((componentComparison f ε).app I) :=
  componentComparison_app_bijective f ε I

/-! ### Constant height on a point: the projection is not height-preserving -/

/-- The constant height `0` on a point. -/
def pointHeight : C(PUnit.{1}, ℝ) := ContinuousMap.const _ 0

/-- The point `(*, ε)` of the thickened point has height `ε`, while its projection has height
`0`: the first projection is not a map over `ℝ` for `ε > 0`. -/
theorem point_projection_not_height_preserving :
    height pointHeight 1 (PUnit.unit, ⟨((1 : ℝ≥0) : ℝ), right_mem_Icc.2 (neg_le_band 1)⟩) ≠
      pointHeight PUnit.unit := by
  simp [pointHeight]

/-! ### Constant height on an interval: the projection is not injective -/

/-- The constant height `0` on `[0, 1]`. -/
def intervalHeight : C(unitInterval, ℝ) := ContinuousMap.const _ 0

/-- At `ε = 1` and `I = ℝ`, `(0, 0)` and `(0, 1)` have the same projection. -/
theorem interval_projection_not_injective :
    ¬ Function.Injective (preimageProjection intervalHeight 1 ⊤) := by
  intro hinj
  have h := hinj (a₁ := ⟨((0 : unitInterval), ⟨0, zero_mem_band 1⟩), Set.mem_univ _⟩)
    (a₂ := ⟨((0 : unitInterval), ⟨((1 : ℝ≥0) : ℝ), right_mem_Icc.2 (neg_le_band 1)⟩),
      Set.mem_univ _⟩) rfl
  have h' := congrArg (fun z : {z : unitInterval × Band 1 // height intervalHeight 1 z ∈
    (⊤ : OpenInterval)} => (z.1.2 : ℝ)) h
  norm_num at h'

/-- Nevertheless the comparison is bijective there. -/
theorem interval_bijective_top :
    Function.Bijective ((componentComparison intervalHeight 1).app ⊤) :=
  componentComparison_app_bijective _ _ _

/-! ### A height-preserving map collapsing two points -/

/-- Two points at height `0`. -/
def boolHeight : C(Bool, ℝ) := ContinuousMap.const _ 0

/-- The collapse `Bool → PUnit` over `ℝ`. -/
def collapse : C(Bool, PUnit.{1}) := ContinuousMap.const _ PUnit.unit

theorem collapse_comm : ∀ x, pointHeight (collapse x) = boolHeight x := fun _ => rfl

/-- The thickened point `(true, 0)` over `ℝ`. -/
def trueZero : {z : Bool × Band 1 // height boolHeight 1 z ∈ (⊤ : OpenInterval)} :=
  ⟨(true, ⟨0, zero_mem_band 1⟩), Set.mem_univ _⟩

/-- The component square for the collapse, evaluated at the class of `(true, 0)` over `ℝ`: both
composites give the class of the point. -/
theorem collapse_square_mk :
    (intervalComponentNatTrans (map collapse 1) (height_map collapse collapse_comm 1) ≫
        componentComparison pointHeight 1).app ⊤ (ZerothHomotopy.mk trueZero) =
      ZerothHomotopy.mk (⟨PUnit.unit, le_thicken 1 ⊤ (Set.mem_univ _)⟩ :
        {x : PUnit.{1} // pointHeight x ∈ thicken 1 ⊤}) ∧
    (componentComparison boolHeight 1 ≫
        (smoothing 1).map (intervalComponentNatTrans collapse collapse_comm)).app ⊤
        (ZerothHomotopy.mk trueZero) =
      ZerothHomotopy.mk (⟨PUnit.unit, le_thicken 1 ⊤ (Set.mem_univ _)⟩ :
        {x : PUnit.{1} // pointHeight x ∈ thicken 1 ⊤}) :=
  ⟨rfl, rfl⟩

/-- The same square, from the general naturality theorem. -/
theorem collapse_square :
    intervalComponentNatTrans (map collapse 1) (height_map collapse collapse_comm 1) ≫
        componentComparison pointHeight 1 =
      componentComparison boolHeight 1 ≫
        (smoothing 1).map (intervalComponentNatTrans collapse collapse_comm) :=
  componentComparison_natural collapse collapse_comm 1

/-! ### A height-preserving map exchanging two points -/

/-- The exchange `Bool.not` of two points at height `0`. -/
def swapB : C(Bool, Bool) := ⟨Bool.not, continuous_of_discreteTopology⟩

theorem swapB_comm : ∀ x, boolHeight (swapB x) = boolHeight x := fun _ => rfl

/-- The component square for the exchange, evaluated at the class of `(true, 0)` over `ℝ`: both
composites give the class of `false`. -/
theorem swap_square_mk :
    (intervalComponentNatTrans (map swapB 1) (height_map swapB swapB_comm 1) ≫
        componentComparison boolHeight 1).app ⊤ (ZerothHomotopy.mk trueZero) =
      ZerothHomotopy.mk (⟨false, le_thicken 1 ⊤ (Set.mem_univ _)⟩ :
        {x : Bool // boolHeight x ∈ thicken 1 ⊤}) ∧
    (componentComparison boolHeight 1 ≫
        (smoothing 1).map (intervalComponentNatTrans swapB swapB_comm)).app ⊤
        (ZerothHomotopy.mk trueZero) =
      ZerothHomotopy.mk (⟨false, le_thicken 1 ⊤ (Set.mem_univ _)⟩ :
        {x : Bool // boolHeight x ∈ thicken 1 ⊤}) :=
  ⟨rfl, rfl⟩

/-- The classes of `false` and `true` in the target differ, so the square distinguishes the
exchange from the identity. -/
theorem swap_target_distinct :
    (ZerothHomotopy.mk (⟨false, le_thicken 1 ⊤ (Set.mem_univ _)⟩ :
        {x : Bool // boolHeight x ∈ thicken 1 ⊤})) ≠
      ZerothHomotopy.mk (⟨true, le_thicken 1 ⊤ (Set.mem_univ _)⟩ :
        {x : Bool // boolHeight x ∈ thicken 1 ⊤}) := by
  intro h
  exact Bool.false_ne_true (congrArg Subtype.val (joined_eq_of_discrete (Quotient.exact h)))

/-- The same square, from the general naturality theorem. -/
theorem swap_square :
    intervalComponentNatTrans (map swapB 1) (height_map swapB swapB_comm 1) ≫
        componentComparison boolHeight 1 =
      componentComparison boolHeight 1 ≫
        (smoothing 1).map (intervalComponentNatTrans swapB swapB_comm) :=
  componentComparison_natural swapB swapB_comm 1

/-! ### The band reparametrization -/

theorem bandHomeomorph_point :
    (bandHomeomorph boolHeight 1 (true, ⟨0, zero_mem_band 1⟩) : Bool × ℝ) = (true, 0) :=
  Prod.ext rfl (show boolHeight true + 0 = 0 by simp [boolHeight])

end Examples.GeometricThickening

end

end TDA.Reeb
