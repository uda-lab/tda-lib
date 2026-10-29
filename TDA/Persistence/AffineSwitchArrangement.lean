import TDA.Persistence.EndpointCostSign
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite affine cuts for endpoint-cost comparisons

The parameter pair `(m,c)` represents `y = m*x+c`; positive slopes are the intended
geometric domain. All sign-cell statements also hold on the full parameter plane.
The construction retains zero forms and both signed factors of a squared comparison.
It establishes endpoint-cost order invariance, not a matching-distance maximum theorem.
-/

noncomputable section

namespace TDA.Persistence.AffineSwitch

/-- An affine cut, including the identically zero and nonzero constant cases. -/
@[ext] structure Form where
  A : ℝ
  B : ℝ
  C : ℝ

/-- Evaluate an affine cut at slope/intercept parameters. -/
def Form.eval (f : Form) (p : ℝ × ℝ) : ℝ := f.A * p.1 + f.B * p.2 + f.C

/-- Coefficientwise addition of affine forms. -/
def Form.add (f g : Form) : Form := ⟨f.A + g.A, f.B + g.B, f.C + g.C⟩

/-- Coefficientwise subtraction of affine forms. -/
def Form.sub (f g : Form) : Form := ⟨f.A - g.A, f.B - g.B, f.C - g.C⟩

/-- Scalar multiplication of affine forms. -/
def Form.scale (r : ℝ) (f : Form) : Form := ⟨r * f.A, r * f.B, r * f.C⟩

@[simp] theorem Form.eval_add (f g : Form) (p : ℝ × ℝ) :
    (f.add g).eval p = f.eval p + g.eval p := by
  simp only [eval, add]; ring

@[simp] theorem Form.eval_sub (f g : Form) (p : ℝ × ℝ) :
    (f.sub g).eval p = f.eval p - g.eval p := by
  simp only [eval, sub]; ring

@[simp] theorem Form.eval_scale (r : ℝ) (f : Form) (p : ℝ × ℝ) :
    (f.scale r).eval p = r * f.eval p := by
  simp only [eval, scale]; ring

@[simp] theorem Form.eval_zero (p : ℝ × ℝ) : (Form.mk 0 0 0).eval p = 0 := by
  simp [eval]

/-- A form is identically zero exactly when all three coefficients vanish. -/
theorem Form.eval_eq_zero_iff (f : Form) :
    (∀ p, f.eval p = 0) ↔ f = ⟨0, 0, 0⟩ := by
  constructor
  · intro h
    have h0 := h (0, 0)
    have h1 := h (1, 0)
    have h2 := h (0, 1)
    simp only [eval, mul_zero, mul_one, add_zero, zero_add] at h0 h1 h2
    ext <;> simp_all
  · rintro rfl; exact eval_zero

/-- The two affine expressions whose maximum is the push height: `true` selects `m*s₁`. -/
def branch (s : ℝ × ℝ) (b : Bool) : Form :=
  if b then ⟨s.1, 0, 0⟩ else ⟨0, -1, s.2⟩

/-- Scaled height of the coordinatewise upward push onto a positive-slope line. -/
def push (s p : ℝ × ℝ) : ℝ := max (p.1 * s.1) (s.2 - p.2)

/-- Endpoint-pair cost, with denominator `1` for a pair and `2` for a diagonal cost. -/
def cost (u v p : ℝ × ℝ) (δ : ℝ) : ℝ :=
  |push u p - push v p| / (δ * max 1 p.1)

/-- The common normalization never vanishes, even on the full parameter plane. -/
theorem normalization_pos (p : ℝ × ℝ) : 0 < max 1 p.1 :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem cost_denominator_pos (p : ℝ × ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 < δ * max 1 p.1 := mul_pos hδ (normalization_pos p)

theorem cost_of_slope_le_one (u v p : ℝ × ℝ) (δ : ℝ) (hm : p.1 ≤ 1) :
    cost u v p δ = |push u p - push v p| / δ := by
  simp [cost, max_eq_left hm]

theorem cost_of_one_le_slope (u v p : ℝ × ℝ) (δ : ℝ) (hm : 1 ≤ p.1) :
    cost u v p δ = |push u p - push v p| / (δ * p.1) := by
  simp [cost, max_eq_right hm]

/-- The sign of this cut selects the maximum branch, retaining equality. -/
def pushCut (s : ℝ × ℝ) : Form := ⟨s.1, 1, -s.2⟩

/-- The normalization changes formula at slope one. -/
def slopeCut : Form := ⟨1, 0, -1⟩

/-- Select a push branch; at a tie either affine expression gives the same height. -/
noncomputable def active (s p : ℝ × ℝ) : Bool := by
  classical
  exact decide (s.2 - p.2 ≤ p.1 * s.1)

theorem branch_active (s p : ℝ × ℝ) : (branch s (active s p)).eval p = push s p := by
  classical
  by_cases h : s.2 - p.2 ≤ p.1 * s.1
  · have he : active s p = true := by simp only [active, h, decide_true]
    rw [he]
    simp only [branch, ↓reduceIte, Form.eval, push, max_eq_left h]
    ring
  · have he : active s p = false := by simp only [active, h, decide_false]
    rw [he]
    simp only [branch, Bool.false_eq_true, ↓reduceIte, Form.eval, push,
      max_eq_right (le_of_not_ge h)]
    ring

/-- The two allowed multiplicity denominators. -/
def denominator (b : Bool) : ℝ := if b then 2 else 1

theorem denominator_pos (b : Bool) : 0 < denominator b := by
  cases b <;> norm_num [denominator]

theorem denominator_eq_one_or_two (b : Bool) : denominator b = 1 ∨ denominator b = 2 := by
  cases b <;> simp [denominator]

theorem exists_denominator_iff (δ : ℝ) : (∃ b, denominator b = δ) ↔ δ = 1 ∨ δ = 2 := by
  constructor
  · rintro ⟨b, rfl⟩; exact denominator_eq_one_or_two b
  · rintro (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

/-- Both signed factors are included, without ordering restrictions on endpoints. -/
def switchForm (u v w x : ℝ × ℝ) (bu bv bw bx : Bool) (δ η : ℝ) (plus : Bool) : Form :=
  let f := ((branch u bu).sub (branch v bv)).scale η
  let g := ((branch w bw).sub (branch x bx)).scale δ
  if plus then f.add g else f.sub g

theorem eval_switchForm (u v w x p : ℝ × ℝ) (bu bv bw bx : Bool)
    (δ η : ℝ) (plus : Bool) :
    (switchForm u v w x bu bv bw bx δ η plus).eval p =
      if plus then
        η * ((branch u bu).eval p - (branch v bv).eval p) +
          δ * ((branch w bw).eval p - (branch x bx).eval p)
      else
        η * ((branch u bu).eval p - (branch v bv).eval p) -
          δ * ((branch w bw).eval p - (branch x bx).eval p) := by
  cases plus <;> simp [switchForm]

/-- Finite input for the exhaustive signed comparison cuts. Repeated endpoints are allowed. -/
structure SwitchIndex (S : Finset (ℝ × ℝ)) where
  u : S
  v : S
  w : S
  x : S
  bu : Bool
  bv : Bool
  bw : Bool
  bx : Bool
  δ : Bool
  η : Bool
  plus : Bool

noncomputable instance (S : Finset (ℝ × ℝ)) : Fintype (SwitchIndex S) := by
  classical
  exact Fintype.ofEquiv
    ((S × S × S × S) × (Bool × Bool × Bool × Bool) × (Bool × Bool × Bool))
    { toFun := fun a => ⟨a.1.1, a.1.2.1, a.1.2.2.1, a.1.2.2.2,
        a.2.1.1, a.2.1.2.1, a.2.1.2.2.1, a.2.1.2.2.2,
        a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩
      invFun := fun i => ((i.u, i.v, i.w, i.x), (i.bu, i.bv, i.bw, i.bx), (i.δ, i.η, i.plus))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The affine form corresponding to one finite choice. -/
def SwitchIndex.form {S : Finset (ℝ × ℝ)} (i : SwitchIndex S) : Form :=
  switchForm i.u i.v i.w i.x i.bu i.bv i.bw i.bx
    (denominator i.δ) (denominator i.η) i.plus

/-- The finite arrangement: branch cuts, normalization cut, and both comparison factors.
Zero forms are deliberately retained. -/
noncomputable def cuts (S : Finset (ℝ × ℝ)) : Finset Form := by
  classical
  exact insert slopeCut (S.image pushCut ∪ Finset.univ.image (SwitchIndex.form (S := S)))

theorem slopeCut_mem (S : Finset (ℝ × ℝ)) : slopeCut ∈ cuts S := by
  classical
  simp [cuts]

theorem pushCut_mem {S : Finset (ℝ × ℝ)} {s : ℝ × ℝ} (hs : s ∈ S) :
    pushCut s ∈ cuts S := by
  classical
  simp only [cuts, Finset.mem_insert, Finset.mem_union]
  exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨s, hs, rfl⟩))

theorem switchForm_mem {S : Finset (ℝ × ℝ)} (i : SwitchIndex S) : i.form ∈ cuts S := by
  classical
  simp only [cuts, Finset.mem_insert, Finset.mem_union]
  exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- Repeated endpoints produce the zero form; it is retained for every nonempty input. -/
theorem zero_mem_cuts {S : Finset (ℝ × ℝ)} (hS : S.Nonempty) : Form.mk 0 0 0 ∈ cuts S := by
  obtain ⟨s, hs⟩ := hS
  let i : SwitchIndex S := ⟨⟨s, hs⟩, ⟨s, hs⟩, ⟨s, hs⟩, ⟨s, hs⟩,
    false, false, false, false, false, false, false⟩
  have hi : i.form = ⟨0, 0, 0⟩ := by
    ext <;> simp [i, SwitchIndex.form, switchForm, Form.sub, Form.scale]
  rw [← hi]
  exact switchForm_mem i

/-- A sign profile includes zero signs, so cells include all boundary strata. -/
noncomputable def signProfile (S : Finset (ℝ × ℝ)) (p : ℝ × ℝ) :
    {f // f ∈ cuts S} → SignType := fun f => SignType.sign (f.val.eval p)

/-- Two parameter pairs are in the same sign cell of the explicit finite arrangement. -/
def SameCell (S : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : Prop := signProfile S p = signProfile S q

theorem sameCell_iff (S : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) :
    SameCell S p q ↔ ∀ f ∈ cuts S, SignType.sign (f.eval p) = SignType.sign (f.eval q) := by
  constructor
  · intro h f hf; exact congrFun h ⟨f, hf⟩
  · intro h; funext f; exact h f.val f.property

/-- Only finitely many sign cells can be realized. -/
theorem finite_signProfiles (S : Finset (ℝ × ℝ)) : (Set.range (signProfile S)).Finite := by
  classical
  exact Set.toFinite _

theorem SameCell.refl (S : Finset (ℝ × ℝ)) (p : ℝ × ℝ) : SameCell S p p := rfl

theorem SameCell.symm {S : Finset (ℝ × ℝ)} {p q : ℝ × ℝ} (h : SameCell S p q) :
    SameCell S q p := Eq.symm h

theorem SameCell.trans {S : Finset (ℝ × ℝ)} {p q r : ℝ × ℝ}
    (h : SameCell S p q) (h' : SameCell S q r) : SameCell S p r := Eq.trans h h'

/-- The slope-one cut keeps the formula for the normalization fixed on each cell. -/
theorem SameCell.slope_le_one_iff {S : Finset (ℝ × ℝ)} {p q : ℝ × ℝ}
    (h : SameCell S p q) : p.1 ≤ 1 ↔ q.1 ≤ 1 := by
  have he := (sameCell_iff S p q).mp h slopeCut (slopeCut_mem S)
  have ht : SignType.sign (slopeCut.eval p) ≤ 0 ↔ SignType.sign (slopeCut.eval q) ≤ 0 := by
    rw [he]
  simpa only [sign_nonpos_iff, slopeCut, Form.eval, one_mul, zero_mul, add_zero,
    ← sub_eq_add_neg, sub_nonpos] using ht

theorem SameCell.active_eq {S : Finset (ℝ × ℝ)} {p q : ℝ × ℝ}
    (h : SameCell S p q) {s : ℝ × ℝ} (hs : s ∈ S) : active s p = active s q := by
  have he := (sameCell_iff S p q).mp h (pushCut s) (pushCut_mem hs)
  have hn : 0 ≤ (pushCut s).eval p ↔ 0 ≤ (pushCut s).eval q := by
    have ht : (0 ≤ SignType.sign ((pushCut s).eval p) ↔
        0 ≤ SignType.sign ((pushCut s).eval q)) := by rw [he]
    simpa only [sign_nonneg_iff] using ht
  have hb : s.2 - p.2 ≤ p.1 * s.1 ↔ s.2 - q.2 ≤ q.1 * s.1 := by
    simp only [pushCut, Form.eval] at hn
    constructor <;> intro ht
    · have := hn.mp (by nlinarith); nlinarith
    · have := hn.mpr (by nlinarith); nlinarith
  simp only [active, hb]

/-- Every pairwise endpoint-cost comparison, including equality, is invariant on a cell. -/
theorem SameCell.sign_cost_sub_eq {S : Finset (ℝ × ℝ)} {p q : ℝ × ℝ}
    (h : SameCell S p q) (u v w x : S) (δ η : Bool) :
    SignType.sign (cost u v p (denominator δ) - cost w x p (denominator η)) =
      SignType.sign (cost u v q (denominator δ) - cost w x q (denominator η)) := by
  let idx (b : Bool) : SwitchIndex S :=
    ⟨u, v, w, x, active u p, active v p, active w p, active x p, δ, η, b⟩
  have he (b : Bool) := (sameCell_iff S p q).mp h (idx b).form (switchForm_mem (idx b))
  have ha (s : S) : (branch s (active s p)).eval q = push s q := by
    rw [h.active_eq s.property, branch_active]
  have hf (b : Bool) :
      SignType.sign (if b then
        denominator η * (push u p - push v p) + denominator δ * (push w p - push x p)
        else denominator η * (push u p - push v p) - denominator δ * (push w p - push x p)) =
      SignType.sign (if b then
        denominator η * (push u q - push v q) + denominator δ * (push w q - push x q)
        else denominator η * (push u q - push v q) - denominator δ * (push w q - push x q)) := by
    simpa only [idx, SwitchIndex.form, eval_switchForm, branch_active, ha] using he b
  simp only [cost]
  rw [EndpointCost.sign_abs_div_mul_sub_eq_sign_factors (denominator_pos δ)
      (denominator_pos η) (normalization_pos p),
    EndpointCost.sign_abs_div_mul_sub_eq_sign_factors (denominator_pos δ)
      (denominator_pos η) (normalization_pos q), sign_mul, sign_mul]
  exact congrArg₂ (· * ·) (hf false) (hf true)

/-- The order relation itself is available without manipulating signs. -/
theorem SameCell.cost_le_iff {S : Finset (ℝ × ℝ)} {p q : ℝ × ℝ}
    (h : SameCell S p q) (u v w x : S) (δ η : Bool) :
    cost u v p (denominator δ) ≤ cost w x p (denominator η) ↔
      cost u v q (denominator δ) ≤ cost w x q (denominator η) := by
  have ht : (SignType.sign (cost u v p (denominator δ) - cost w x p (denominator η)) ≤ 0 ↔
      SignType.sign (cost u v q (denominator δ) - cost w x q (denominator η)) ≤ 0) := by
    rw [h.sign_cost_sub_eq u v w x δ η]
  simpa only [sign_nonpos_iff, sub_nonpos] using ht

/-- Equal-cost degeneracies are preserved, including coincident endpoints. -/
theorem SameCell.cost_eq_iff {S : Finset (ℝ × ℝ)} {p q : ℝ × ℝ}
    (h : SameCell S p q) (u v w x : S) (δ η : Bool) :
    cost u v p (denominator δ) = cost w x p (denominator η) ↔
      cost u v q (denominator δ) = cost w x q (denominator η) := by
  have ht : (SignType.sign (cost u v p (denominator δ) - cost w x p (denominator η)) = 0 ↔
      SignType.sign (cost u v q (denominator δ) - cost w x q (denominator η)) = 0) := by
    rw [h.sign_cost_sub_eq u v w x δ η]
  simpa only [sign_eq_zero_iff, sub_eq_zero] using ht

end TDA.Persistence.AffineSwitch
