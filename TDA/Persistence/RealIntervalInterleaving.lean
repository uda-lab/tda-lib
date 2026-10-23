import TDA.Persistence.RealInterleaving
import TDA.Persistence.RealBarcode
import Mathlib.Tactic.Linarith

/-!
# Comparison maps for real half-open intervals

Interval comparisons preserve the coefficient on their overlap. Endpoint bounds
ensure naturality, including when the overlap is empty. Opposite comparisons give
interleavings; short intervals have zero double-shift maps at equality too.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RealBarcode

open CategoryTheory RealShift
open scoped NNReal ZeroObject Classical

variable {k : Type u} [Field k]

private theorem val_eq_zero {p : ℝ × WithTop ℝ} {t : ℝ}
    (h : ¬ alive p t) (x : fiber (k := k) p t) : (x : k) = 0 := by
  simpa only [fiber, if_neg h, Submodule.mem_bot] using x.property

/-- The interval structure map preserves coefficients until the excluded death. -/
theorem map_val (p : ℝ × WithTop ℝ) {s t : ℝ} (f : s ⟶ t)
    (x : fiber (k := k) p s) :
    ((show fiber (k := k) p t from ((intervalModule p).map f).hom x) : k) = if alive p t then (x : k) else 0 := by
  classical
  change (((if h : alive p s ∧ alive p t then
    Submodule.inclusion (show fiber (k := k) p s ≤ fiber p t by
      simp [fiber, h.1, h.2]) else 0) x) : k) = _
  by_cases hs : alive p s <;> by_cases ht : alive p t
  · simp [hs, ht]
  · simp [hs, ht]
  · simp [hs, ht, val_eq_zero hs x]
  · simp [hs, ht]

private noncomputable def comparisonLinear (p q : ℝ × WithTop ℝ) (s t : ℝ) :
    fiber (k := k) p s →ₗ[k] fiber (k := k) q t := by
  classical
  exact if h : alive q t then
    Submodule.inclusion (show fiber (k := k) p s ≤ fiber (k := k) q t by
      rw [show fiber (k := k) q t = ⊤ by simp [fiber, h]]
      exact le_top) else 0

private theorem comparisonLinear_val (p q : ℝ × WithTop ℝ) (s t : ℝ)
    (x : fiber (k := k) p s) :
    (comparisonLinear p q s t x : k) = if alive q t then (x : k) else 0 := by
  classical
  by_cases h : alive q t <;> simp [comparisonLinear, h]

private theorem cancel_shift_lt {a : ℝ} {d e : WithTop ℝ} (ε : ℝ≥0)
    (h : ((a + (ε : ℝ) : ℝ) : WithTop ℝ) < e)
    (he : e ≤ d + ((ε : ℝ) : WithTop ℝ)) : (a : WithTop ℝ) < d := by
  apply (WithTop.add_lt_add_iff_right (WithTop.coe_ne_top :
    ((ε : ℝ) : WithTop ℝ) ≠ ⊤)).mp
  simpa only [← WithTop.coe_add] using h.trans_le he

/-- The normalized map into a positive evaluation shift. The weak endpoint bounds
allow an empty overlap, in which case every component is zero. -/
noncomputable def comparison (ε : ℝ≥0) (p q : ℝ × WithTop ℝ)
    (hb : q.1 ≤ p.1 + (ε : ℝ))
    (hd : q.2 ≤ p.2 + ((ε : ℝ) : WithTop ℝ)) :
    intervalModule (k := k) p ⟶ (shift ε).obj (intervalModule q) where
  app t := ModuleCat.ofHom (comparisonLinear p q t (t + (ε : ℝ)))
  naturality {s t} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (comparisonLinear p q t (t + (ε : ℝ)) (((intervalModule p).map f).hom x) : k) =
      ((show fiber (k := k) q (t + (ε : ℝ)) from
        ((intervalModule q).map (homOfLE (add_le_add (leOfHom f) le_rfl))).hom
          (comparisonLinear p q s (s + (ε : ℝ)) x)) : k)
    erw [comparisonLinear_val, map_val, map_val, comparisonLinear_val]
    by_cases hs : alive p s
    · by_cases ht : alive q (t + (ε : ℝ))
      · have hpt : alive p t := ⟨hs.1.trans (leOfHom f), cancel_shift_lt ε ht.2 hd⟩
        have hqs : alive q (s + (ε : ℝ)) :=
          ⟨hb.trans (add_le_add hs.1 le_rfl),
            lt_of_le_of_lt (WithTop.coe_le_coe.mpr (add_le_add (leOfHom f) le_rfl)) ht.2⟩
        simp [ht, hpt, hqs]
      · simp [ht]
    · simp [val_eq_zero hs x]

/-- Comparison components preserve the coefficient exactly on the target support. -/
theorem comparison_app_val (ε : ℝ≥0) (p q : ℝ × WithTop ℝ)
    (hb : q.1 ≤ p.1 + (ε : ℝ))
    (hd : q.2 ≤ p.2 + ((ε : ℝ) : WithTop ℝ)) (t : ℝ)
    (x : fiber (k := k) p t) :
    ((show fiber (k := k) q (t + (ε : ℝ)) from ((comparison ε p q hb hd).app t).hom x) : k) =
      if alive q (t + (ε : ℝ)) then (x : k) else 0 :=
  comparisonLinear_val p q t _ x

private theorem middle_alive (ε : ℝ≥0) (p q : ℝ × WithTop ℝ)
    (hb : q.1 ≤ p.1 + (ε : ℝ))
    (hd : p.2 ≤ q.2 + ((ε : ℝ) : WithTop ℝ)) (t : ℝ)
    (hs : alive p t) (ht : alive p (t + ((ε + ε : ℝ≥0) : ℝ))) :
    alive q (t + (ε : ℝ)) := by
  refine ⟨hb.trans (add_le_add hs.1 le_rfl), ?_⟩
  apply cancel_shift_lt ε (e := p.2) _ hd
  simpa only [NNReal.coe_add, add_assoc] using ht.2

/-- Numeric endpoint bounds construct both interleaving maps, without a nonzero-map
assumption. Death comparisons use `∞ + ε = ∞` for essential intervals. -/
noncomputable def interleavingOfBounds (ε : ℝ≥0) (p q : ℝ × WithTop ℝ)
    (hpq : q.1 ≤ p.1 + (ε : ℝ)) (hqp : p.1 ≤ q.1 + (ε : ℝ))
    (hdpq : q.2 ≤ p.2 + ((ε : ℝ) : WithTop ℝ))
    (hdqp : p.2 ≤ q.2 + ((ε : ℝ) : WithTop ℝ)) :
    RealInterleaving ε (intervalModule (k := k) p) (intervalModule q) := by
  have comp (p q : ℝ × WithTop ℝ)
      (hb : q.1 ≤ p.1 + (ε : ℝ)) (hb' : p.1 ≤ q.1 + (ε : ℝ))
      (hd : q.2 ≤ p.2 + ((ε : ℝ) : WithTop ℝ))
      (hd' : p.2 ≤ q.2 + ((ε : ℝ) : WithTop ℝ)) (t : ℝ) :
      (comparison ε p q hb hd).app t ≫
        (comparison ε q p hb' hd').app (t + (ε : ℝ)) ≫
          (compIso ε ε (intervalModule (k := k) p)).hom.app t =
            (transition (ε + ε) (intervalModule p)).app t := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((show fiber (k := k) p (t + ((ε + ε : ℝ≥0) : ℝ)) from
      ((intervalModule p).map (eqToHom (show (t + (ε : ℝ)) + (ε : ℝ) =
        t + ((ε + ε : ℝ≥0) : ℝ) by simp [NNReal.coe_add, add_assoc]))).hom
        (((comparison ε q p hb' hd').app (t + (ε : ℝ))).hom
          (((comparison ε p q hb hd).app t).hom x))) : k) =
      ((show fiber (k := k) p (t + ((ε + ε : ℝ≥0) : ℝ)) from
        ((intervalModule p).map (homOfLE (le_add_of_nonneg_right
          (NNReal.coe_nonneg (ε + ε))))).hom x) : k)
    erw [map_val, map_val, comparison_app_val, comparison_app_val]
    have heq : t + (ε : ℝ) + (ε : ℝ) = t + ((ε + ε : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_add, add_assoc]
    rw [heq]
    by_cases hs : alive p t
    · by_cases ht : alive p (t + ((ε + ε : ℝ≥0) : ℝ))
      · simp only [if_pos ht, if_pos (middle_alive ε p q hb hd' t hs ht)]
      · simp only [if_neg ht]
    · simp [val_eq_zero hs x]
  exact RealInterleaving.ofApp (comparison ε p q hpq hdpq) (comparison ε q p hqp hdqp)
    (comp p q hpq hqp hdpq hdqp) (comp q p hqp hpq hdqp hdpq)

/-- A finite half-open interval has zero double-shift map exactly at the closed
length bound. No positive-lifetime hypothesis is needed for this criterion. -/
theorem transition_eq_zero_iff (ε : ℝ≥0) (b d : ℝ) :
    transition (ε + ε) (intervalModule (k := k) (b, (d : WithTop ℝ))) = 0 ↔
      d - b ≤ 2 * (ε : ℝ) := by
  constructor
  · intro hz
    by_contra h
    have hlt : b + ((ε + ε : ℝ≥0) : ℝ) < d := by
      simp only [NNReal.coe_add]; linarith [lt_of_not_ge h]
    have hb : alive (b, (d : WithTop ℝ)) b :=
      ⟨le_rfl, WithTop.coe_lt_coe.mpr (lt_of_le_of_lt
        (le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε))) hlt)⟩
    have ht : alive (b, (d : WithTop ℝ)) (b + ((ε + ε : ℝ≥0) : ℝ)) :=
      ⟨le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε)), WithTop.coe_lt_coe.mpr hlt⟩
    let x : fiber (k := k) (b, (d : WithTop ℝ)) b := ⟨1, by simp [fiber, hb]⟩
    have hx : ((transition (ε + ε) (intervalModule (k := k) (b, (d : WithTop ℝ)))).app b).hom x = 0 := by
      rw [hz]; rfl
    have hv := congrArg (fun y : fiber (k := k) (b, (d : WithTop ℝ))
      (b + ((ε + ε : ℝ≥0) : ℝ)) => (y : k)) hx
    change ((show fiber (k := k) (b, (d : WithTop ℝ))
      (b + ((ε + ε : ℝ≥0) : ℝ)) from
        ((intervalModule (b, (d : WithTop ℝ))).map
          (homOfLE (le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε))))).hom x) : k) = 0 at hv
    erw [map_val] at hv
    exact one_ne_zero (by simpa only [if_pos ht, x] using hv)
  · intro h
    apply NatTrans.ext
    funext t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((show fiber (k := k) (b, (d : WithTop ℝ))
      (t + ((ε + ε : ℝ≥0) : ℝ)) from
        ((intervalModule (b, (d : WithTop ℝ))).map
          (homOfLE (le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε))))).hom x) : k) = 0
    erw [map_val]
    by_cases hs : alive (b, (d : WithTop ℝ)) t
    · have ht : ¬ alive (b, (d : WithTop ℝ)) (t + ((ε + ε : ℝ≥0) : ℝ)) := by
        intro ht
        have hdeath := WithTop.coe_lt_coe.mp ht.2
        have hbirth := hs.1
        simp only [NNReal.coe_add] at hdeath
        linarith
      simp only [if_neg ht]
    · simp [val_eq_zero hs x]

/-- Exact finite-interval criterion for interleaving with zero, including length `2ε`. -/
theorem interleaved_zero_iff (ε : ℝ≥0) (b d : ℝ) :
    Nonempty (RealInterleaving ε (intervalModule (k := k) (b, (d : WithTop ℝ))) 0) ↔
      d - b ≤ 2 * (ε : ℝ) :=
  (RealInterleaving.nonempty_zero_iff _ _).trans (transition_eq_zero_iff ε b d)

/-- When the shifted target dies at or before the source birth, the normalized
comparison is zero. Equality is excluded by the half-open support. -/
theorem comparison_eq_zero_of_death_le (ε : ℝ≥0) (p q : ℝ × WithTop ℝ)
    (hb : q.1 ≤ p.1 + (ε : ℝ))
    (hd : q.2 ≤ p.2 + ((ε : ℝ) : WithTop ℝ))
    (htouch : q.2 ≤ ((p.1 + (ε : ℝ) : ℝ) : WithTop ℝ)) :
    comparison (k := k) ε p q hb hd = 0 := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((show fiber (k := k) q (t + (ε : ℝ)) from
    ((comparison ε p q hb hd).app t).hom x) : k) = 0
  erw [comparison_app_val]
  by_cases hs : alive p t
  · have ht : ¬ alive q (t + (ε : ℝ)) := by
      intro h
      exact (not_lt_of_ge (htouch.trans (WithTop.coe_le_coe.mpr
        (add_le_add hs.1 le_rfl)))) h.2
    simp only [if_neg ht]
  · simp [val_eq_zero hs x]

/-- For a positive source and the stated endpoint bounds, the normalized comparison
is nonzero exactly when the shifted source birth lies strictly before target death. -/
theorem comparison_ne_zero_iff (ε : ℝ≥0) (p q : ℝ × WithTop ℝ)
    (hp : (p.1 : WithTop ℝ) < p.2)
    (hb : q.1 ≤ p.1 + (ε : ℝ))
    (hd : q.2 ≤ p.2 + ((ε : ℝ) : WithTop ℝ)) :
    comparison (k := k) ε p q hb hd ≠ 0 ↔
      ((p.1 + (ε : ℝ) : ℝ) : WithTop ℝ) < q.2 := by
  constructor
  · intro hn
    by_contra ht
    exact hn (comparison_eq_zero_of_death_le ε p q hb hd (le_of_not_gt ht))
  · intro ht hz
    have hs : alive p p.1 := ⟨le_rfl, hp⟩
    have hq : alive q (p.1 + (ε : ℝ)) := ⟨hb, ht⟩
    let x : fiber (k := k) p p.1 := ⟨1, by simp [fiber, hs]⟩
    have hx : ((comparison (k := k) ε p q hb hd).app p.1).hom x = 0 := by
      rw [hz]; rfl
    have hv := congrArg (fun y : fiber (k := k) q (p.1 + (ε : ℝ)) => (y : k)) hx
    erw [comparison_app_val] at hv
    change (if alive q (p.1 + (ε : ℝ)) then (1 : k) else 0) = 0 at hv
    exact one_ne_zero (by simpa only [if_pos hq] using hv)

/-- An essential interval cannot be deleted by a finite shift over a field. -/
theorem essential_not_interleaved_zero (ε : ℝ≥0) (b : ℝ) :
    ¬ Nonempty (RealInterleaving ε (intervalModule (k := k) (b, ⊤)) 0) := by
  intro hi
  have hz := (RealInterleaving.nonempty_zero_iff _ _).mp hi
  have hb : alive (b, ⊤) b := ⟨le_rfl, WithTop.coe_lt_top b⟩
  have ht : alive (b, ⊤) (b + ((ε + ε : ℝ≥0) : ℝ)) :=
    ⟨le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε)), WithTop.coe_lt_top _⟩
  let x : fiber (k := k) (b, ⊤) b := ⟨1, by simp [fiber, hb]⟩
  have hx : ((transition (ε + ε) (intervalModule (k := k) (b, ⊤))).app b).hom x = 0 := by
    rw [hz]; rfl
  have hv := congrArg (fun y : fiber (k := k) (b, ⊤)
    (b + ((ε + ε : ℝ≥0) : ℝ)) => (y : k)) hx
  change ((show fiber (k := k) (b, ⊤) (b + ((ε + ε : ℝ≥0) : ℝ)) from
    ((intervalModule (b, ⊤)).map
      (homOfLE (le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε))))).hom x) : k) = 0 at hv
  erw [map_val] at hv
  exact one_ne_zero (by simpa only [if_pos ht, x] using hv)

end TDA.Persistence.RealBarcode
