import TDA.Reeb.IntervalMayerVietoris
import TDA.Reeb.SingularHomologyZero
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The circle test for the interval Mayer–Vietoris connecting map

The space is Mathlib's unit circle `Circle` (a subtype of `ℂ`) with the height function
`circleHeight = Im`, and the coefficients are `ℚ`. The square is the endpoint square
`circleSquare = IntervalMVSquare.ofEndpoints (1/2) (1/2) 2 2`: its corners are
`SW = (-1/2, 1/2)`, `left = (-2, 1/2)`, `right = (-1/2, 2)` and `NE = (-2, 2)`
(`circleSquare_corners`). So `f ⁻¹ NE` is the whole circle (`circleHeight_mem_ne`), the two pieces
are the arcs `{Im < 1/2}` and `{Im > -1/2}`, and the overlap `f ⁻¹ SW = {|Im| < 1/2}`.

* **Two overlap components (C1).** The overlap misses `Re = 0`
  (`re_ne_zero_of_mem_overlap`), and it is the union of the disjoint nonempty open sets
  `overlapPos = {Re > 0}` and `overlapNeg = {Re < 0}`, each preconnected as the continuous image of
  the interval `(-1/2, 1/2)` under `y ↦ (±√(1 - y²), y)` (`circle_overlap_two_components`).
* **The connecting map is nonzero (C2).** The class `c = [1] - [-1]` in `H₀(overlap; ℚ)`
  (`overlapClassDiff`) is killed by `intervalMVInterMap`, because the two points are joined by a
  half circle inside each arc (`overlapClassDiff_comp_intervalMVInterMap`). It is nonzero: the
  locally constant indicator of `{Re > 0}` induces a functional on `H₀` with value `1` on `c`
  (`overlapClassDiff_ne_zero`). By exactness at `H₀(overlap)`, `c` would be zero if the connecting
  map were, so `intervalMVδ circleHeight circleSquare ℚ 0 ≠ 0` (`circle_intervalMVδ_ne_zero`).
* **Sign reversal on swapping the arcs.** By `intervalMVδ_swap`, the connecting map of the
  swapped square is minus the original one; over `ℚ` it is therefore different from it
  (`circle_intervalMVδ_swap_ne`).
-/

namespace TDA.Reeb.Examples.CircleMayerVietoris

open CategoryTheory Limits AlgebraicTopology TDA.Reeb TDA.Reeb.OpenInterval

noncomputable section

/-- The height function `Im` on the unit circle. -/
def circleHeight : C(Circle, ℝ) :=
  ⟨fun z => (z : ℂ).im, Complex.continuous_im.comp continuous_subtype_val⟩

@[simp]
theorem circleHeight_apply (z : Circle) : circleHeight z = (z : ℂ).im :=
  rfl

/-- The circle square: the endpoint square of `(a, b) = (1/2, 1/2)` and `(a', b') = (2, 2)`. -/
def circleSquare : IntervalMVSquare :=
  IntervalMVSquare.ofEndpoints (1 / 2) (1 / 2) 2 2 (by norm_num) (by norm_num) (by norm_num)

/-- The corners of the circle square. -/
theorem circleSquare_corners :
    circleSquare.sw = ioo (-(1 / 2)) (1 / 2) ∧ circleSquare.left = ioo (-2) (1 / 2) ∧
      circleSquare.right = ioo (-(1 / 2)) 2 ∧ circleSquare.ne = ioo (-2) 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- On the circle, `Re² + Im² = 1`. -/
private theorem re_sq_add_im_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  have h := Circle.normSq_coe z
  rw [Complex.normSq_apply] at h
  nlinarith [h]

/-- The preimage of the northeast corner is the whole circle: `|Im| ≤ 1 < 2`. -/
theorem circleHeight_mem_ne (z : Circle) : circleHeight z ∈ circleSquare.ne := by
  have h := re_sq_add_im_sq z
  change -2 < (z : ℂ).im ∧ (z : ℂ).im < 2
  constructor <;> nlinarith [sq_nonneg (z : ℂ).re, sq_nonneg ((z : ℂ).im + 2),
    sq_nonneg ((z : ℂ).im - 2)]

/-- The overlap `f ⁻¹ SW = {|Im| < 1/2}` of the two arcs. -/
abbrev Overlap : TopCat := (intervalPreimageTopCat circleHeight).obj circleSquare.sw

/-- A point of the overlap has `|Im| < 1/2`. -/
private theorem abs_im_lt (y : Overlap) : -(1 / 2 : ℝ) < (y.1 : ℂ).im ∧ (y.1 : ℂ).im < 1 / 2 :=
  y.2

/-- **The overlap misses the imaginary axis**: `|Im z| < 1/2` forces `Re z ≠ 0`. -/
theorem re_ne_zero_of_mem_overlap (y : Overlap) : (y.1 : ℂ).re ≠ 0 := by
  intro h0
  have hn := re_sq_add_im_sq y.1
  have h := abs_im_lt y
  rw [h0] at hn
  nlinarith [h.1, h.2]

/-- The part `{Re > 0}` of the overlap. -/
def overlapPos : Set Overlap :=
  {y | 0 < (y.1 : ℂ).re}

/-- The part `{Re < 0}` of the overlap. -/
def overlapNeg : Set Overlap :=
  {y | (y.1 : ℂ).re < 0}

/-- The real part as a continuous function on the overlap. -/
private theorem continuous_re : Continuous fun y : Overlap => (y.1 : ℂ).re :=
  Complex.continuous_re.comp (continuous_subtype_val.comp continuous_subtype_val)

/-- The point `1` of the overlap. -/
def pointPos : Overlap :=
  ⟨1, by change -(1 / 2 : ℝ) < (1 : ℂ).im ∧ (1 : ℂ).im < 1 / 2; norm_num⟩

/-- The point `-1` of the overlap. -/
def pointNeg : Overlap :=
  ⟨-1, by
    change -(1 / 2 : ℝ) < ((-1 : Circle) : ℂ).im ∧ ((-1 : Circle) : ℂ).im < 1 / 2
    rw [Circle.coe_neg]
    norm_num⟩

/-- The complex number `s √(1 - y²) + y i`. -/
private def arcComplex (s y : ℝ) : ℂ :=
  ((s * √(1 - y ^ 2) : ℝ) : ℂ) + (y : ℂ) * Complex.I

private theorem arcComplex_re (s y : ℝ) : (arcComplex s y).re = s * √(1 - y ^ 2) := by
  simp [arcComplex]

private theorem arcComplex_im (s y : ℝ) : (arcComplex s y).im = y := by
  simp [arcComplex]

/-- The point `y ↦ (s √(1 - y²), y)` of the overlap, for `|y| < 1/2` and `s = ±1`. -/
private def arcPoint (s : ℝ) (hs : s ^ 2 = 1) (y : Set.Ioo (-(1 / 2) : ℝ) (1 / 2)) : Overlap :=
  ⟨⟨arcComplex s y, by
      have h₁ : 0 ≤ 1 - (y : ℝ) ^ 2 := by nlinarith [y.2.1, y.2.2]
      refine mem_sphere_zero_iff_norm.2 ?_
      rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_eq_one, arcComplex_re, arcComplex_im,
        mul_pow, hs, Real.sq_sqrt h₁]
      ring⟩, by
    change -(1 / 2 : ℝ) < (arcComplex s y).im ∧ (arcComplex s y).im < 1 / 2
    rw [arcComplex_im]
    exact y.2⟩

private theorem continuous_arcPoint (s : ℝ) (hs : s ^ 2 = 1) : Continuous (arcPoint s hs) := by
  have h : Continuous fun y : Set.Ioo (-(1 / 2) : ℝ) (1 / 2) => arcComplex s y := by
    unfold arcComplex
    fun_prop
  exact (h.subtype_mk _).subtype_mk _

/-- The image of `arcPoint s` is the part of the overlap where `s Re > 0`. -/
private theorem range_arcPoint (s : ℝ) (hs : s ^ 2 = 1) :
    Set.range (arcPoint s hs) = {y : Overlap | 0 < s * (y.1 : ℂ).re} := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    have h₁ : 0 < 1 - (y : ℝ) ^ 2 := by nlinarith [y.2.1, y.2.2]
    change 0 < s * (arcComplex s y).re
    rw [arcComplex_re, ← mul_assoc, ← sq, hs, one_mul]
    exact Real.sqrt_pos.2 h₁
  · intro hp
    change 0 < s * (p.1 : ℂ).re at hp
    have hs' : s = 1 ∨ s = -1 := by
      have h : (s - 1) * (s + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    refine ⟨⟨(p.1 : ℂ).im, abs_im_lt p⟩, Subtype.ext (Circle.ext (Complex.ext ?_ ?_))⟩
    · change (arcComplex s (p.1 : ℂ).im).re = (p.1 : ℂ).re
      rw [arcComplex_re]
      have hn := re_sq_add_im_sq p.1
      have ht : 1 - (p.1 : ℂ).im ^ 2 = (p.1 : ℂ).re ^ 2 := by linarith
      rw [ht, Real.sqrt_sq_eq_abs]
      rcases hs' with rfl | rfl
      · rw [one_mul] at hp ⊢
        exact abs_of_pos hp
      · rw [neg_one_mul] at hp ⊢
        rw [abs_of_neg (by linarith), neg_neg]
    · change (arcComplex s (p.1 : ℂ).im).im = (p.1 : ℂ).im
      rw [arcComplex_im]

/-- The parts `{s Re > 0}` of the overlap, `s = ±1`, are preconnected. -/
private theorem isPreconnected_setOf_mul_re (s : ℝ) (hs : s ^ 2 = 1) :
    IsPreconnected {y : Overlap | 0 < s * (y.1 : ℂ).re} := by
  have : PreconnectedSpace (Set.Ioo (-(1 / 2) : ℝ) (1 / 2)) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  rw [← range_arcPoint s hs]
  exact isPreconnected_range (continuous_arcPoint s hs)

/-- **Two overlap components (C1).** The overlap `{|Im| < 1/2}` is the union of the two disjoint
nonempty open sets `{Re > 0}` and `{Re < 0}`, and each of them is preconnected. -/
theorem circle_overlap_two_components :
    IsOpen overlapPos ∧ IsOpen overlapNeg ∧ Disjoint overlapPos overlapNeg ∧
      overlapPos ∪ overlapNeg = Set.univ ∧ overlapPos.Nonempty ∧ overlapNeg.Nonempty ∧
      IsPreconnected overlapPos ∧ IsPreconnected overlapNeg := by
  refine ⟨isOpen_lt continuous_const continuous_re, isOpen_lt continuous_re continuous_const,
    Set.disjoint_left.2 fun y (h₁ : 0 < (y.1 : ℂ).re) h₂ => lt_asymm h₁ h₂, ?_, ⟨pointPos, ?_⟩, ⟨pointNeg, ?_⟩, ?_, ?_⟩
  · ext y
    simp only [overlapPos, overlapNeg, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (lt_or_gt_of_ne (re_ne_zero_of_mem_overlap y)).symm
  · change (0 : ℝ) < (1 : ℂ).re
    norm_num
  · change ((-1 : Circle) : ℂ).re < 0
    rw [Circle.coe_neg]
    norm_num
  · have h := isPreconnected_setOf_mul_re 1 (by norm_num)
    simpa only [overlapPos, one_mul] using h
  · have h := isPreconnected_setOf_mul_re (-1) (by norm_num)
    simpa only [overlapNeg, neg_mul, one_mul, neg_pos] using h

/-! ### The connecting map is nonzero -/

/-- The coefficients `ℚ`. -/
local notation "Rℚ" => ModuleCat.of ℚ ℚ

/-- The upper half circle `t ↦ exp(iπt)` from `1` to `-1`. -/
private def upperHalf : Path (1 : Circle) (-1) where
  toFun t := Circle.exp (Real.pi * t)
  continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by
    ext1
    simp [Circle.coe_exp, Complex.exp_pi_mul_I]

/-- The lower half circle `t ↦ exp(-iπt)` from `1` to `-1`. -/
private def lowerHalf : Path (1 : Circle) (-1) where
  toFun t := Circle.exp (-(Real.pi * t))
  continuous_toFun :=
    Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val).neg
  source' := by simp
  target' := by
    ext1
    simp [Circle.coe_exp, Complex.exp_pi_mul_I]

private theorem im_upperHalf (t : unitInterval) :
    ((upperHalf t : Circle) : ℂ).im = Real.sin (Real.pi * t) := by
  change (Circle.exp (Real.pi * t) : ℂ).im = _
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

private theorem im_lowerHalf (t : unitInterval) :
    ((lowerHalf t : Circle) : ℂ).im = -Real.sin (Real.pi * t) := by
  change (Circle.exp (-(Real.pi * t)) : ℂ).im = _
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

private theorem sin_pi_mul_nonneg (t : unitInterval) : 0 ≤ Real.sin (Real.pi * t) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le t.2.1)
    (mul_le_of_le_one_right Real.pi_pos.le t.2.2)

/-- In the lower arc `{Im < 1/2}`, the images of `1` and `-1` are joined by the lower half
circle. -/
private def lowerArcPath :
    Path ((intervalPreimageTopCat circleHeight).map (homOfLE circleSquare.sw_le_left) pointPos)
      ((intervalPreimageTopCat circleHeight).map (homOfLE circleSquare.sw_le_left) pointNeg) :=
  (JoinedIn.joined_subtype (F := {z : Circle | circleHeight z ∈ circleSquare.left})
    ⟨lowerHalf, fun t => by
      change -2 < ((lowerHalf t : Circle) : ℂ).im ∧ ((lowerHalf t : Circle) : ℂ).im < 1 / 2
      rw [im_lowerHalf]
      have h₀ := sin_pi_mul_nonneg t
      have h₁ := Real.sin_le_one (Real.pi * t)
      constructor <;> linarith⟩).somePath

/-- In the upper arc `{Im > -1/2}`, the images of `1` and `-1` are joined by the upper half
circle. -/
private def upperArcPath :
    Path ((intervalPreimageTopCat circleHeight).map (homOfLE circleSquare.sw_le_right) pointPos)
      ((intervalPreimageTopCat circleHeight).map (homOfLE circleSquare.sw_le_right) pointNeg) :=
  (JoinedIn.joined_subtype (F := {z : Circle | circleHeight z ∈ circleSquare.right})
    ⟨upperHalf, fun t => by
      change -(1 / 2) < ((upperHalf t : Circle) : ℂ).im ∧ ((upperHalf t : Circle) : ℂ).im < 2
      rw [im_upperHalf]
      have h₀ := sin_pi_mul_nonneg t
      have h₁ := Real.sin_le_one (Real.pi * t)
      constructor <;> linarith⟩).somePath

/-- The class `[1] - [-1]` in `H₀` of the overlap, with coefficients `ℚ`. -/
def overlapClassDiff : Rℚ ⟶ ((singularHomologyFunctor (ModuleCat.{0} ℚ) 0).obj Rℚ).obj Overlap :=
  singularHomology₀Class Overlap Rℚ pointPos - singularHomology₀Class Overlap Rℚ pointNeg

/-- The class `[1] - [-1]` is killed by `(inc, -inc)`: in each arc the two points are joined by a
half circle. -/
theorem overlapClassDiff_comp_intervalMVInterMap :
    overlapClassDiff ≫ intervalMVInterMap circleHeight circleSquare ℚ 0 = 0 := by
  apply biprod.hom_ext
  · simp only [overlapClassDiff, intervalMVInterMap, Category.assoc, biprod.lift_fst,
      Preadditive.sub_comp, singularHomology₀Class_comp_map, zero_comp]
    rw [singularHomology₀Class_eq_of_path _ Rℚ lowerArcPath, sub_self]
  · simp only [overlapClassDiff, intervalMVInterMap, Category.assoc, biprod.lift_snd,
      Preadditive.comp_neg, Preadditive.sub_comp, singularHomology₀Class_comp_map, zero_comp]
    rw [singularHomology₀Class_eq_of_path _ Rℚ upperArcPath, sub_self]

/-- The indicator of `{Re > 0}` on the overlap, with values in the endomorphisms of `ℚ`. -/
private def posIndicator (y : Overlap) : Rℚ ⟶ Rℚ :=
  if 0 < (y.1 : ℂ).re then 𝟙 _ else 0

private theorem isLocallyConstant_posIndicator : IsLocallyConstant posIndicator := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rcases lt_or_gt_of_ne (re_ne_zero_of_mem_overlap x) with h | h
  · filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds h] with y hy
    have hy' : (y.1 : ℂ).re < 0 := hy
    simp [posIndicator, not_lt.2 hy'.le, not_lt.2 h.le]
  · filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds h] with y hy
    have hy' : 0 < (y.1 : ℂ).re := hy
    simp [posIndicator, hy', h]

/-- The class `[1] - [-1]` is nonzero: the functional induced by the locally constant indicator of
`{Re > 0}` takes the value `1` on it. -/
theorem overlapClassDiff_ne_zero : overlapClassDiff ≠ 0 := by
  intro h
  have e : overlapClassDiff ≫ singularHomology₀Desc Overlap Rℚ posIndicator
      isLocallyConstant_posIndicator = 𝟙 Rℚ := by
    have hP : 0 < ((pointPos.1 : Circle) : ℂ).re := by
      change (0 : ℝ) < (1 : ℂ).re
      norm_num
    have hN : ¬ 0 < ((pointNeg.1 : Circle) : ℂ).re := by
      change ¬ (0 : ℝ) < ((-1 : Circle) : ℂ).re
      rw [Circle.coe_neg]
      norm_num
    simp only [overlapClassDiff, Preadditive.sub_comp,
      singularHomology₀Class_comp_singularHomology₀Desc, posIndicator, hP, hN, ite_true, ite_false,
      sub_zero]
  rw [h, zero_comp] at e
  have e₁ := congrArg (fun φ : Rℚ ⟶ Rℚ => φ.hom (1 : ℚ)) e
  simp at e₁

/-- **The connecting map is nonzero (C2).** `δ : H₁(S¹; ℚ) ⟶ H₀({|Im| < 1/2}; ℚ)` is not the zero
map: if it were, `(inc, -inc)` would be a monomorphism by exactness at `H₀` of the overlap, and the
nonzero class `[1] - [-1]` in its kernel would vanish. -/
theorem circle_intervalMVδ_ne_zero : intervalMVδ circleHeight circleSquare ℚ 0 ≠ 0 := by
  intro hδ
  have hmono := (intervalMV_exact_inter circleHeight circleSquare ℚ 0).mono_g hδ
  apply overlapClassDiff_ne_zero
  rw [← cancel_mono (intervalMVInterMap circleHeight circleSquare ℚ 0), zero_comp]
  exact overlapClassDiff_comp_intervalMVInterMap

/-- **Sign reversal on swapping the arcs, over `ℚ`.** The connecting map of the swapped circle
square is minus the original one (`intervalMVδ_swap`), and it is different from it, since the
original one is nonzero and `ℚ` has characteristic zero. -/
theorem circle_intervalMVδ_swap_ne :
    intervalMVδ circleHeight circleSquare.swap ℚ 0 ≠ intervalMVδ circleHeight circleSquare ℚ 0 := by
  rw [intervalMVδ_swap]
  intro h
  apply circle_intervalMVδ_ne_zero
  have h₂ : (2 : ℚ) • intervalMVδ circleHeight circleSquare ℚ 0 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  have h₃ := congrArg (fun φ => (2 : ℚ)⁻¹ • φ) h₂
  simpa [smul_smul] using h₃

end

end TDA.Reeb.Examples.CircleMayerVietoris
