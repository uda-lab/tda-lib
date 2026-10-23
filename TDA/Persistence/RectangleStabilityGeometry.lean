import TDA.Persistence.Rectangle
import TDA.Persistence.CoordinateInterleaving
import Mathlib.Tactic.Linarith

/-!
# Decorated rectangle geometry for the stability argument

The `α` order is the sum of both endpoints of every coordinate, with a
secondary count of plus-decorated endpoints. It is the order used in
Bjerkevik's rectangle stability proof, §4.1, Lemma 4.7. For a bounded
interval, the lower endpoint is plus-decorated when excluded, and the upper
endpoint is plus-decorated when included.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CoordinateShift
open scoped TDA.Persistence NNReal Classical

namespace RectangleStabilityGeometry

/-- An endpoint of one coordinate: `false` is lower and `true` is upper. -/
def endpoint {n : ℕ} (R : Rectangle n) (j : Fin n × Bool) : ℝ :=
  if j.2 then (R j.1).upper else (R j.1).lower

/-- The paper's plus decoration of each endpoint. -/
def plus {n : ℕ} (R : Rectangle n) (j : Fin n × Bool) : Bool :=
  if j.2 then (R j.1).upperClosed else !(R j.1).lowerClosed

/-- Sum of the real values of all lower and upper endpoints. -/
def alphaValue {n : ℕ} (R : Rectangle n) : ℝ :=
  ∑ j : Fin n × Bool, endpoint R j

/-- Number of plus-decorated endpoints. -/
def alphaPlus {n : ℕ} (R : Rectangle n) : ℕ :=
  ∑ j : Fin n × Bool, (plus R j).toNat

/-- The lexicographic α preorder, including endpoint decorations. -/
def alphaLE {n : ℕ} (R S : Rectangle n) : Prop :=
  alphaValue R < alphaValue S ∨
    (alphaValue R = alphaValue S ∧ alphaPlus R ≤ alphaPlus S)

/-- If `R ≤α T`, then a middle rectangle lies on the forward side of at
least one of the two adjacent pairs. -/
theorem alphaLE_chain_split {n : ℕ} (R S T : Rectangle n)
    (hRT : alphaLE R T) : alphaLE R S ∨ alphaLE S T := by
  by_cases hRS : alphaLE R S
  · exact Or.inl hRS
  right
  have hSR : alphaValue S < alphaValue R ∨
      (alphaValue S = alphaValue R ∧ alphaPlus S < alphaPlus R) := by
    unfold alphaLE at hRS
    rcases lt_trichotomy (alphaValue S) (alphaValue R) with h | h | h
    · exact Or.inl h
    · have hn : ¬ alphaPlus R ≤ alphaPlus S := by
        intro hp
        exact hRS (Or.inr ⟨h.symm, hp⟩)
      exact Or.inr ⟨h, Nat.lt_of_not_ge hn⟩
    · exact False.elim (hRS (Or.inl h))
  unfold alphaLE at hRT ⊢
  rcases hSR with h | ⟨h, hp⟩
  · exact Or.inl (h.trans_le (hRT.elim le_of_lt (fun x => x.1.le)))
  · rcases hRT with hRT | ⟨he, hpRT⟩
    · exact Or.inl (h ▸ hRT)
    · exact Or.inr ⟨h.trans he, hp.le.trans hpRT⟩

/-- Order on real endpoints with a minus sign below a plus sign. -/
def decoratedLE (a b : ℝ) (p q : Bool) : Prop :=
  a < b ∨ (a = b ∧ p ≤ q)

theorem decoratedLE_refl (a : ℝ) (p : Bool) : decoratedLE a a p p :=
  Or.inr ⟨rfl, le_rfl⟩

theorem decoratedLE_value {a b : ℝ} {p q : Bool}
    (h : decoratedLE a b p q) : a ≤ b :=
  h.elim le_of_lt (fun x => x.1.le)

theorem decoratedLE_of_lt {a b : ℝ} (h : a < b) (p q : Bool) :
    decoratedLE a b p q := Or.inl h

theorem decoratedLE_add_mono {a b δ ρ : ℝ} {p q : Bool}
    (h : decoratedLE a (b + δ) p q) (hδρ : δ ≤ ρ) :
    decoratedLE a (b + ρ) p q := by
  rcases h with h | ⟨h, hp⟩
  · exact Or.inl (by linarith)
  · rcases lt_or_eq_of_le hδρ with hlt | he
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by simpa [← he] using h, hp⟩

private theorem interval_lower_le_mem (I : BoundedInterval) {p : ℝ}
    (hp : p ∈ I.support) : I.lower ≤ p :=
  hp.1.elim le_of_lt (fun h => h.1.le)

private theorem interval_mem_le_upper (I : BoundedInterval) {p : ℝ}
    (hp : p ∈ I.support) : p ≤ I.upper :=
  hp.2.elim le_of_lt (fun h => h.1.le)

private theorem interval_exists_mem_lt (I : BoundedInterval) {p t : ℝ}
    (hp : p ∈ I.support) (ht : I.lower < t) :
    ∃ x, x ∈ I.support ∧ x ≤ p ∧ x < t := by
  by_cases he : I.lower = p
  · exact ⟨p, hp, le_rfl, he ▸ ht⟩
  have hpl : I.lower < p := lt_of_le_of_ne (interval_lower_le_mem I hp) he
  let x := min p ((I.lower + t) / 2)
  have hxlow : I.lower < x := lt_min hpl (by linarith)
  have hxp : x ≤ p := min_le_left _ _
  have hxt : x < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨x, ⟨Or.inl hxlow, ?_⟩, hxp, hxt⟩
  by_cases hxp' : x = p
  · simpa [hxp'] using hp.2
  · exact Or.inl ((lt_of_le_of_ne hxp hxp').trans_le (interval_mem_le_upper I hp))

private theorem interval_exists_mem_gt (I : BoundedInterval) {p t : ℝ}
    (hp : p ∈ I.support) (ht : t < I.upper) :
    ∃ x, x ∈ I.support ∧ p ≤ x ∧ t < x := by
  by_cases he : I.upper = p
  · exact ⟨p, hp, le_rfl, he ▸ ht⟩
  have hpu : p < I.upper := lt_of_le_of_ne (interval_mem_le_upper I hp) (Ne.symm he)
  let x := max p ((I.upper + t) / 2)
  have hxup : x < I.upper := max_lt hpu (by linarith)
  have hpx : p ≤ x := le_max_left _ _
  have htx : t < x := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨x, ⟨?_, Or.inl hxup⟩, hpx, htx⟩
  by_cases hpx' : x = p
  · simpa [hpx'] using hp.1
  · exact Or.inl ((interval_lower_le_mem I hp).trans_lt
      (lt_of_le_of_ne hpx (Ne.symm hpx')))

private theorem interval_lower_mem_of_closed (I : BoundedInterval) {p : ℝ}
    (hp : p ∈ I.support) (hc : I.lowerClosed = true) :
    I.lower ∈ I.support := by
  refine ⟨Or.inr ⟨rfl, hc⟩, ?_⟩
  by_cases hlt : I.lower < I.upper
  · exact Or.inl hlt
  have heq : I.lower = I.upper := by
    have := interval_lower_le_mem I hp
    have := interval_mem_le_upper I hp
    linarith
  have hpe : p = I.upper := by
    have := interval_lower_le_mem I hp
    have := interval_mem_le_upper I hp
    linarith
  rcases hp.2 with h | ⟨_, h⟩
  · exfalso; linarith
  · exact Or.inr ⟨heq, h⟩

private theorem interval_upper_mem_of_closed (I : BoundedInterval) {p : ℝ}
    (hp : p ∈ I.support) (hc : I.upperClosed = true) :
    I.upper ∈ I.support := by
  refine ⟨?_, Or.inr ⟨rfl, hc⟩⟩
  by_cases hlt : I.lower < I.upper
  · exact Or.inl hlt
  have heq : I.lower = I.upper := by
    have := interval_lower_le_mem I hp
    have := interval_mem_le_upper I hp
    linarith
  have hpe : p = I.lower := by
    have := interval_lower_le_mem I hp
    have := interval_mem_le_upper I hp
    linarith
  rcases hp.1 with h | ⟨_, h⟩
  · exfalso; linarith
  · exact Or.inr ⟨heq, h⟩

private theorem lower_bound_of_backward (A B : BoundedInterval)
    (ε p : ℝ) (hp : p ∈ A.support)
    (h : ∀ x, x ∈ A.support → x ≤ p → x + ε ∈ B.support) :
    decoratedLE B.lower (A.lower + ε) (!B.lowerClosed) (!A.lowerClosed) := by
  have hval : B.lower ≤ A.lower + ε := by
    by_contra hn
    have hlt : A.lower < B.lower - ε := by linarith
    obtain ⟨x, hx, hxp, hxt⟩ := interval_exists_mem_lt A hp hlt
    have hb := interval_lower_le_mem B (h x hx hxp)
    linarith
  rcases lt_or_eq_of_le hval with hlt | he
  · exact Or.inl hlt
  refine Or.inr ⟨he, ?_⟩
  cases hc : A.lowerClosed
  · simp
  · have hB : B.lowerClosed = true := by
      have hA := interval_lower_mem_of_closed A hp hc
      have hm := (h A.lower hA (interval_lower_le_mem A hp)).1
      rcases hm with hh | ⟨_, hh⟩
      · exfalso; linarith
      · exact hh
    simp [hB]

private theorem upper_bound_of_forward (A B : BoundedInterval)
    (ε p : ℝ) (hp : p + ε ∈ B.support)
    (h : ∀ y, y ∈ B.support → p + ε ≤ y → y - ε ∈ A.support) :
    decoratedLE B.upper (A.upper + ε) B.upperClosed A.upperClosed := by
  have hval : B.upper ≤ A.upper + ε := by
    by_contra hn
    have hlt : A.upper + ε < B.upper := by linarith
    obtain ⟨y, hy, hpy, hty⟩ := interval_exists_mem_gt B hp hlt
    have ha := interval_mem_le_upper A (h y hy hpy)
    linarith
  rcases lt_or_eq_of_le hval with hlt | he
  · exact Or.inl hlt
  refine Or.inr ⟨he, ?_⟩
  cases hc : B.upperClosed
  · simp
  · have hA : A.upperClosed = true := by
      have hB := interval_upper_mem_of_closed B hp hc
      have hm := (h B.upper hB (interval_mem_le_upper B hp)).2
      rcases hm with hh | ⟨_, hh⟩
      · exfalso; linarith
      · exact hh
    simp [hA]

private theorem lower_mem_of_bound (A B : BoundedInterval) (ρ : ℝ)
    (h : decoratedLE B.lower (A.lower + ρ)
      (!B.lowerClosed) (!A.lowerClosed))
    {x : ℝ} (hx : x ∈ A.support) :
    B.lower < x + ρ ∨ (B.lower = x + ρ ∧ B.lowerClosed = true) := by
  rcases h with h | ⟨he, hp⟩
  · exact Or.inl (by have := interval_lower_le_mem A hx; linarith)
  rcases hx.1 with hax | ⟨hax, hc⟩
  · exact Or.inl (by linarith)
  · right
    refine ⟨by linarith, ?_⟩
    cases hB : B.lowerClosed
    · have : False := by
        simp only [hB, hc, Bool.not_false, Bool.not_true] at hp
        have hh := Bool.toNat_le_toNat hp
        norm_num at hh
      exact this.elim
    · rfl

private theorem upper_mem_of_bound (A B : BoundedInterval) (ρ : ℝ)
    (h : decoratedLE B.upper (A.upper + ρ) B.upperClosed A.upperClosed)
    {y : ℝ} (hy : y ∈ B.support) :
    y - ρ < A.upper ∨ (y - ρ = A.upper ∧ A.upperClosed = true) := by
  rcases h with h | ⟨he, hp⟩
  · exact Or.inl (by have hyu := interval_mem_le_upper B hy; linarith)
  rcases hy.2 with hyu | ⟨hyu, hc⟩
  · exact Or.inl (by linarith)
  · right
    refine ⟨by linarith, ?_⟩
    cases hA : A.upperClosed
    · have : False := by
        simp only [hA, hc] at hp
        have hh := Bool.toNat_le_toNat hp
        norm_num at hh
      exact this.elim
    · rfl

/-- Forward decorated endpoint bounds make the normalized overlap comparison
natural: an earlier source point and a later shifted-target point force both
intermediate fibers to be present. -/
theorem compatible_of_endpoint_bounds {n : ℕ} (R S : Rectangle n) (ρ : ℝ≥0)
    (h : ∀ j, decoratedLE (endpoint S j)
      (endpoint R j + (ρ : ℝ)) (plus S j) (plus R j))
    {p q : Fin n → ℝ} (hpq : p ≤ q)
    (hpR : p ∈ R.support) (hqS : translation ρ q ∈ S.support) :
    q ∈ R.support ∧ translation ρ p ∈ S.support := by
  constructor
  · intro i
    have hlo := (hpR i).1
    have hu := upper_mem_of_bound (R i) (S i) (ρ : ℝ)
      (h (i, true)) (hqS i)
    constructor
    · rcases hlo with hlo | ⟨hlo, hc⟩
      · exact Or.inl (hlo.trans_le (hpq i))
      · by_cases he : p i = q i
        · exact Or.inr ⟨hlo.trans he, hc⟩
        · exact Or.inl (lt_of_le_of_ne (hlo.le.trans (hpq i))
            (by intro hh; exact he (by linarith)))
    · simpa [translation_apply] using hu
  · intro i
    have hl := lower_mem_of_bound (R i) (S i) (ρ : ℝ)
      (h (i, false)) (hpR i)
    have hu := (hqS i).2
    constructor
    · simpa [translation_apply] using hl
    · rcases hu with hu | ⟨hu, hc⟩
      · exact Or.inl ((show (translation ρ p) i ≤ (translation ρ q) i from
          (translation ρ).monotone' hpq i).trans_lt hu)
      · by_cases he : p i = q i
        · exact Or.inr ⟨by simpa [translation_apply, he] using hu, hc⟩
        · exact Or.inl (by
            have hpqlt := lt_of_le_of_ne (hpq i) he
            change q i + (ρ : ℝ) = (S i).upper at hu
            change p i + (ρ : ℝ) < (S i).upper
            linarith)

private noncomputable def comparisonLinear {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ρ : ℝ≥0) (p : Fin n → ℝ) :
    SupportInterval.fiber (k := k) R.support p →ₗ[k]
      SupportInterval.fiber (k := k) S.support (translation ρ p) := by
  classical
  exact if h : translation ρ p ∈ S.support then
    Submodule.inclusion (show SupportInterval.fiber (k := k) R.support p ≤
      SupportInterval.fiber S.support (translation ρ p) by
      simp [SupportInterval.fiber, h]) else 0

private theorem comparisonLinear_val {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ρ : ℝ≥0) (p : Fin n → ℝ)
    (x : SupportInterval.fiber (k := k) R.support p) :
    ((comparisonLinear R S ρ p x) : k) =
      if translation ρ p ∈ S.support then (x : k) else 0 := by
  classical
  by_cases h : translation ρ p ∈ S.support <;>
    simp [comparisonLinear, h]

/-- The normalized coefficient-one comparison associated to the forward
decorated endpoint bounds. Its components are identity on overlap and zero
otherwise. -/
noncomputable def comparison {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ρ : ℝ≥0)
    (h : ∀ j, decoratedLE (endpoint S j)
      (endpoint R j + (ρ : ℝ)) (plus S j) (plus R j)) :
    R.module (k := k) ⟶ (shift ρ).obj S.module where
  app p := ModuleCat.ofHom (comparisonLinear R S ρ p)
  naturality {p q} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (comparisonLinear R S ρ q
      (structureMapLinear R.module (leOfHom f) x) : k) =
      (structureMapLinear S.module
        ((translation ρ).monotone' (leOfHom f))
        (comparisonLinear R S ρ p x) : k)
    rw [comparisonLinear_val, SupportInterval.structureMap_val,
      SupportInterval.structureMap_val, comparisonLinear_val]
    by_cases hpR : p ∈ R.support
    · by_cases hqS : translation ρ q ∈ S.support
      · obtain ⟨hqR, hpS⟩ := compatible_of_endpoint_bounds R S ρ h
          (leOfHom f) hpR hqS
        simp [hqR, hpS, hqS]
      · simp [hqS]
    · simp [SupportInterval.val_eq_zero R.support hpR x]

/-- A comparison keeps the coefficient at each shifted-target point. -/
theorem comparison_app_val {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ρ : ℝ≥0)
    (h : ∀ j, decoratedLE (endpoint S j)
      (endpoint R j + (ρ : ℝ)) (plus S j) (plus R j))
    (p : Fin n → ℝ) (x : SupportInterval.fiber (k := k) R.support p) :
    ((show SupportInterval.fiber S.support (translation ρ p) from
      ((comparison R S ρ h).app p).hom x) : k) =
      if translation ρ p ∈ S.support then (x : k) else 0 :=
  comparisonLinear_val R S ρ p x

private theorem sum_erase_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r s : ι → ℝ) (δ : ℝ)
    (hf : ∀ i, s i ≤ r i + δ) (j : ι) :
    (∑ i ∈ Finset.univ.erase j, (s i - r i)) ≤
      ((Fintype.card ι : ℝ) - 1) * δ := by
  let t : Finset ι := Finset.univ.erase j
  have ht : t.card = Fintype.card ι - 1 := by
    simp [t, Finset.card_erase_of_mem]
  calc
    (∑ i ∈ t, (s i - r i)) ≤ ∑ _i ∈ t, δ := by
      apply Finset.sum_le_sum
      intro i hi
      linarith [hf i]
    _ = ((Fintype.card ι : ℝ) - 1) * δ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ht]
      have hc : 1 ≤ Fintype.card ι := by
        exact Fintype.card_pos_iff.mpr ⟨j⟩
      rw [Nat.cast_sub hc]
      norm_num

private theorem sum_reverse_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r s : ι → ℝ) (δ : ℝ)
    (hf : ∀ i, s i ≤ r i + δ)
    (ha : ∑ i, r i ≤ ∑ i, s i) (j : ι) :
    r j ≤ s j + ((Fintype.card ι : ℝ) - 1) * δ := by
  let t : Finset ι := Finset.univ.erase j
  have hrest := sum_erase_bound r s δ hf j
  have htotal : 0 ≤ ∑ i, (s i - r i) := by
    rw [Finset.sum_sub_distrib]
    exact sub_nonneg.mpr ha
  have hsplit : (∑ i, (s i - r i)) =
      (∑ i ∈ t, (s i - r i)) + (s j - r j) := by
    exact (Finset.sum_erase_add Finset.univ (fun i => s i - r i)
      (Finset.mem_univ j)).symm
  linarith

private theorem sum_reverse_decorated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r s : ι → ℝ) (pr ps : ι → Bool) (δ : ℝ)
    (hf : ∀ i, decoratedLE (s i) (r i + δ) (ps i) (pr i))
    (ha : (∑ i, r i) < (∑ i, s i) ∨
      ((∑ i, r i) = (∑ i, s i) ∧
        (∑ i, (pr i).toNat) ≤ (∑ i, (ps i).toNat))) (j : ι) :
    decoratedLE (r j) (s j + ((Fintype.card ι : ℝ) - 1) * δ)
      (pr j) (ps j) := by
  have hfvalue (i : ι) : s i ≤ r i + δ := decoratedLE_value (hf i)
  have havalue : (∑ i, r i) ≤ (∑ i, s i) :=
    ha.elim le_of_lt (fun h => h.1.le)
  have hv := sum_reverse_bound r s δ hfvalue havalue j
  rcases lt_or_eq_of_le hv with hlt | he
  · exact Or.inl hlt
  right
  refine ⟨he, ?_⟩
  let t : Finset ι := Finset.univ.erase j
  have hrest := sum_erase_bound r s δ hfvalue j
  have hsplit : (∑ i, (s i - r i)) =
      (∑ i ∈ t, (s i - r i)) + (s j - r j) := by
    exact (Finset.sum_erase_add Finset.univ (fun i => s i - r i)
      (Finset.mem_univ j)).symm
  have htotal : 0 ≤ ∑ i, (s i - r i) := by
    rw [Finset.sum_sub_distrib]
    exact sub_nonneg.mpr havalue
  have htotal0 : (∑ i, (s i - r i)) = 0 := by linarith
  have hrestEq : (∑ i ∈ t, (s i - r i)) = ∑ _i ∈ t, δ := by
    have ht : t.card = Fintype.card ι - 1 := by
      simp [t, Finset.card_erase_of_mem]
    have hc : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
    have hconst : (∑ _i ∈ t, δ) =
        ((Fintype.card ι : ℝ) - 1) * δ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ht, Nat.cast_sub hc]
      norm_num
    rw [hconst]
    linarith
  have hsat (i : ι) (hi : i ∈ t) : s i = r i + δ := by
    have heq := (Finset.sum_eq_sum_iff_of_le
      (fun i (_hi : i ∈ t) => show s i - r i ≤ δ by linarith [hfvalue i])).mp hrestEq i hi
    linarith
  have hplusRest : (∑ i ∈ t, (ps i).toNat) ≤
      ∑ i ∈ t, (pr i).toNat := by
    apply Finset.sum_le_sum
    intro i hi
    have hb := (hf i).resolve_left (by linarith [hsat i hi])
    rcases hb with ⟨_, hp⟩
    exact Bool.toNat_le_toNat hp
  have haplus : (∑ i, (pr i).toNat) ≤ (∑ i, (ps i).toNat) := by
    rcases ha with hlt | ⟨heq, hp⟩
    · have : (∑ i, r i) = (∑ i, s i) := by
        rw [Finset.sum_sub_distrib] at htotal0
        linarith [htotal0]
      exact False.elim ((ne_of_lt hlt) this)
    · exact hp
  have hsplitPr : (∑ i, (pr i).toNat) =
      (∑ i ∈ t, (pr i).toNat) + (pr j).toNat := by
    exact (Finset.sum_erase_add Finset.univ (fun i => (pr i).toNat)
      (Finset.mem_univ j)).symm
  have hsplitPs : (∑ i, (ps i).toNat) =
      (∑ i ∈ t, (ps i).toNat) + (ps j).toNat := by
    exact (Finset.sum_erase_add Finset.univ (fun i => (ps i).toNat)
      (Finset.mem_univ j)).symm
  cases hpr : pr j <;> cases hps : ps j <;> simp_all; omega

/-- Numeric part of the α argument: among `2n` endpoints, one can lag by at
most `(2n−1)δ` if every other endpoint advances by at most `δ`. -/
theorem reverse_value_of_alphaLE {n : ℕ} (R S : Rectangle n) (δ : ℝ)
    (hf : ∀ j, endpoint S j ≤ endpoint R j + δ)
    (ha : alphaLE R S) (j : Fin n × Bool) :
    endpoint R j ≤ endpoint S j + ((2 * n : ℝ) - 1) * δ := by
  have hh : alphaValue R ≤ alphaValue S :=
    ha.elim le_of_lt (fun h => h.1.le)
  have h := sum_reverse_bound (endpoint R) (endpoint S) δ hf hh j
  simpa [alphaValue, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_mul, mul_comm] using h

/-- Full decorated α bound, including the equality case for open and closed
endpoints. This is the finite-sum step in Bjerkevik's Lemma 4.7. -/
theorem reverse_endpoint_bounds_of_alphaLE {n : ℕ}
    (R S : Rectangle n) (δ : ℝ)
    (hf : ∀ j, decoratedLE (endpoint S j) (endpoint R j + δ)
      (plus S j) (plus R j))
    (ha : alphaLE R S) (j : Fin n × Bool) :
    decoratedLE (endpoint R j)
      (endpoint S j + ((2 * n : ℝ) - 1) * δ)
      (plus R j) (plus S j) := by
  have h := sum_reverse_decorated (endpoint R) (endpoint S)
    (plus R) (plus S) δ hf ha j
  simpa [alphaValue, alphaPlus, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_mul, mul_comm] using h

/-- A nonzero shifted morphism has a nonzero scalar component at a point
belonging to the source and to the translated target. -/
theorem exists_nonzero_shifted_component {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module) (hf : f ≠ 0) :
    ∃ (p : Fin n → ℝ) (hpR : p ∈ R.support)
      (_hpS : translation ε p ∈ S.support),
      (f.app p).hom (SupportInterval.one (k := k) R.support hpR) ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply hf
  ext p x
  by_cases hpR : p ∈ R.support
  · have hx : x = (x : k) • SupportInterval.one (k := k) R.support hpR := by
      apply Subtype.ext
      simp [SupportInterval.one]
    rw [hx, map_smul]
    by_cases hpS : translation ε p ∈ S.support
    · have hz := hn p hpR hpS
      change (x : k) • (f.app p).hom (SupportInterval.one R.support hpR) = 0
      rw [hz]
      exact smul_zero (x : k)
    · apply Subtype.ext
      exact SupportInterval.val_eq_zero S.support hpS _
  · have hx : x = 0 := Subtype.ext (SupportInterval.val_eq_zero R.support hpR x)
    rw [hx]
    change (f.app p).hom 0 = 0
    exact map_zero _

/-- Naturality propagates a nonzero shifted component back through source
structure maps. -/
theorem mem_shifted_target_of_le {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    {p q : Fin n → ℝ} (hpR : p ∈ R.support)
    (hne : (f.app p).hom (SupportInterval.one (k := k) R.support hpR) ≠ 0)
    (hqp : q ≤ p) (hqR : q ∈ R.support) :
    translation ε q ∈ S.support := by
  by_contra hqS
  have hzero : (f.app q).hom (SupportInterval.one (k := k) R.support hqR) = 0 := by
    apply Subtype.ext
    exact SupportInterval.val_eq_zero S.support hqS _
  have hsource : structureMapLinear (R.module (k := k)) hqp
      (SupportInterval.one R.support hqR) = SupportInterval.one R.support hpR := by
    apply Subtype.ext
    rw [SupportInterval.structureMap_val]
    simp [hpR, SupportInterval.one]
  have hnat := congrArg
    (fun F => F.hom (SupportInterval.one (k := k) R.support hqR))
    (f.naturality (homOfLE hqp))
  change (f.app p).hom (structureMapLinear R.module hqp
      (SupportInterval.one R.support hqR)) =
    structureMapLinear ((shift ε).obj S.module) hqp
      ((f.app q).hom (SupportInterval.one R.support hqR)) at hnat
  rw [hsource, hzero, map_zero] at hnat
  exact hne hnat

/-- Naturality propagates a nonzero shifted component forward through target
structure maps. -/
theorem mem_source_of_le_shifted {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module)
    {p q : Fin n → ℝ} (hpR : p ∈ R.support)
    (_hpS : translation ε p ∈ S.support)
    (hne : (f.app p).hom (SupportInterval.one (k := k) R.support hpR) ≠ 0)
    (hpq : p ≤ q) (hqS : translation ε q ∈ S.support) :
    q ∈ R.support := by
  by_contra hqR
  have hsource : structureMapLinear (R.module (k := k)) hpq
      (SupportInterval.one R.support hpR) = 0 := by
    apply Subtype.ext
    exact SupportInterval.val_eq_zero R.support hqR _
  have hnat := congrArg
    (fun F => F.hom (SupportInterval.one (k := k) R.support hpR))
    (f.naturality (homOfLE hpq))
  change (f.app q).hom (structureMapLinear R.module hpq
      (SupportInterval.one R.support hpR)) =
    structureMapLinear ((shift ε).obj S.module) hpq
      ((f.app p).hom (SupportInterval.one R.support hpR)) at hnat
  rw [hsource, map_zero] at hnat
  classical
  let z : SupportInterval.fiber S.support (translation ε p) :=
    (f.app p).hom (SupportInterval.one R.support hpR)
  change (0 : SupportInterval.fiber S.support (translation ε q)) =
    structureMapLinear S.module ((translation ε).monotone' hpq) z at hnat
  have hv := congrArg (fun y : SupportInterval.fiber S.support (translation ε q) =>
    (y : k)) hnat
  rw [SupportInterval.structureMap_val] at hv
  change (0 : k) = if translation ε q ∈ S.support then (z : k) else 0 at hv
  rw [if_pos hqS] at hv
  apply hne
  apply Subtype.ext
  exact hv.symm

private def withCoord {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    Fin n → ℝ := fun j => if j = i then x else p j

private theorem withCoord_self {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    withCoord p i x i = x := by simp [withCoord]

private theorem withCoord_le {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (x : ℝ)
    (h : x ≤ p i) : withCoord p i x ≤ p := by
  intro j
  by_cases hji : j = i <;> simp [withCoord, hji, h]

private theorem le_withCoord {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (x : ℝ)
    (h : p i ≤ x) : p ≤ withCoord p i x := by
  intro j
  by_cases hji : j = i <;> simp [withCoord, hji, h]

private theorem withCoord_mem {n : ℕ} (R : Rectangle n) (p : Fin n → ℝ)
    (hp : p ∈ R.support) (i : Fin n) (x : ℝ) (hx : x ∈ (R i).support) :
    withCoord p i x ∈ R.support := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [withCoord] using hx
  · simpa [withCoord, hji] using hp j

private theorem translation_withCoord_mem {n : ℕ} (S : Rectangle n) (ε : ℝ≥0)
    (p : Fin n → ℝ) (hp : translation ε p ∈ S.support)
    (i : Fin n) (y : ℝ) (hy : y ∈ (S i).support) :
    translation ε (withCoord p i (y - (ε : ℝ))) ∈ S.support := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [withCoord, translation_apply] using hy
  · simpa [withCoord, hji, translation_apply] using hp j

/-- The shifted version of the necessary half of the decorated rectangle Hom
criterion: nonzero natural transformations force both lower and upper endpoint
bounds in the direction target ≤ source + shift. -/
theorem shifted_hom_endpoint_bounds {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ε : ℝ≥0)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module) (hf : f ≠ 0)
    (j : Fin n × Bool) :
    decoratedLE (endpoint S j) (endpoint R j + (ε : ℝ))
      (plus S j) (plus R j) := by
  obtain ⟨p, hpR, hpS, hne⟩ := exists_nonzero_shifted_component R S ε f hf
  rcases j with ⟨i, b⟩
  cases b
  · change decoratedLE (S i).lower ((R i).lower + (ε : ℝ))
        (!(S i).lowerClosed) (!(R i).lowerClosed)
    apply lower_bound_of_backward (R i) (S i) (ε : ℝ) (p i) (hpR i)
    intro x hx hxp
    let q := withCoord p i x
    have hqR : q ∈ R.support := withCoord_mem R p hpR i x hx
    have hqp : q ≤ p := withCoord_le p i x hxp
    have hqS := mem_shifted_target_of_le R S ε f hpR hne hqp hqR
    simpa [q, withCoord, translation_apply] using hqS i
  · change decoratedLE (S i).upper ((R i).upper + (ε : ℝ))
        (S i).upperClosed (R i).upperClosed
    apply upper_bound_of_forward (R i) (S i) (ε : ℝ) (p i) (hpS i)
    intro y hy hpy
    let q := withCoord p i (y - (ε : ℝ))
    have hpq : p ≤ q := le_withCoord p i (y - (ε : ℝ)) (by linarith)
    have hqS : translation ε q ∈ S.support :=
      translation_withCoord_mem S ε p hpS i y hy
    have hqR := mem_source_of_le_shifted R S ε f hpR hpS hne hpq hqS
    simpa [q, withCoord] using hqR i

/-- A pair is geometrically close when both decorated endpoints of each
coordinate differ by at most the stated diagonal shift in both directions. -/
def endpointClose {n : ℕ} (ρ : ℝ) (R S : Rectangle n) : Prop :=
  ∀ j : Fin n × Bool,
    decoratedLE (endpoint R j) (endpoint S j + ρ) (plus R j) (plus S j) ∧
    decoratedLE (endpoint S j) (endpoint R j + ρ) (plus S j) (plus R j)

/-- Every point surviving a double shift through R crosses S at the
intermediate shifted grade when all decorated endpoint bounds hold. -/
theorem middle_mem_of_endpointClose {n : ℕ} (R S : Rectangle n)
    (ρ : ℝ≥0)
    (h : endpointClose (ρ : ℝ) R S) (p : Fin n → ℝ)
    (hp : p ∈ R.support)
    (h2 : translation (ρ + ρ) p ∈ R.support) :
    translation ρ p ∈ S.support := by
  intro i
  have hl := lower_mem_of_bound (R i) (S i) (ρ : ℝ)
    (h (i, false)).2 (hp i)
  have hu := upper_mem_of_bound (S i) (R i) (ρ : ℝ)
    (h (i, true)).1 (h2 i)
  constructor
  · simpa [translation_apply] using hl
  · have he : (translation (ρ + ρ) p) i - (ρ : ℝ) =
        (translation ρ p) i := by
      simp [translation_apply, NNReal.coe_add]
      ring
    rw [he] at hu
    exact hu

/-- The normalized comparisons compose to the original double-shift
transition. Endpoint closeness supplies the intermediate support point. -/
theorem comparison_composite {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ρ : ℝ≥0)
    (h : endpointClose (ρ : ℝ) R S) :
    comparison R S ρ (fun j => (h j).2) ≫
      (shift ρ).map (comparison S R ρ (fun j => (h j).1)) ≫
        (compIso ρ ρ (R.module (k := k))).hom =
          transition (ρ + ρ) (R.module (k := k)) := by
  classical
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hcomp : translation ρ (translation ρ p) ≤ translation (ρ + ρ) p :=
    le_of_eq (by funext i; simp [translation_apply, NNReal.coe_add, add_assoc])
  have hstep : p ≤ translation (ρ + ρ) p := by
    intro i
    change p i ≤ p i + ((ρ + ρ : ℝ≥0) : ℝ)
    exact le_add_of_nonneg_right (ρ + ρ).coe_nonneg
  change ((structureMapLinear R.module hcomp
    (comparisonLinear S R ρ (translation ρ p)
      (comparisonLinear R S ρ p x))) : k) =
    ((structureMapLinear R.module hstep x) : k)
  rw [SupportInterval.structureMap_val, SupportInterval.structureMap_val,
    comparisonLinear_val, comparisonLinear_val]
  have heq : translation ρ (translation ρ p) = translation (ρ + ρ) p := by
    funext i
    simp [translation_apply, NNReal.coe_add, add_assoc]
  rw [heq]
  by_cases hp : p ∈ R.support
  · by_cases h2 : translation (ρ + ρ) p ∈ R.support
    · have hm := middle_mem_of_endpointClose R S ρ h p hp h2
      simp [h2, hm]
    · simp [h2]
  · have hx := SupportInterval.val_eq_zero R.support hp x
    simp [hx]

/-- Decorated endpoint closeness constructs an actual diagonal interleaving
of rectangle modules, including open and closed equality cases. -/
noncomputable def interleavingOfEndpointClose {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (ρ : ℝ≥0)
    (h : endpointClose (ρ : ℝ) R S) :
    CoordinateInterleaving ρ (R.module (k := k)) S.module :=
  ⟨comparison R S ρ (fun j => (h j).2),
    comparison S R ρ (fun j => (h j).1),
    comparison_composite R S ρ h,
    comparison_composite S R ρ (fun j => ⟨(h j).2, (h j).1⟩)⟩

private theorem epsilon_le_stability_radius {n : ℕ} (hn : 0 < n) (ε : ℝ≥0) :
    (ε : ℝ) ≤ ((2 * n : ℝ) - 1) * (ε : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 0 ≤ ((2 * n : ℝ) - 2) * (ε : ℝ) :=
    mul_nonneg (by linarith) ε.coe_nonneg
  nlinarith

/-- The decisive geometric half of Bjerkevik's Lemma 4.7. The morphisms
are directed `R → S[ε]` and `S → T[ε]`; if `R ≤α T`, then S is within
`(2n−1)ε` of one adjacent rectangle at every decorated endpoint. -/
theorem nonzero_path_endpointClose {n : ℕ} (hn : 0 < n)
    {k : Type u} [Field k] (R S T : Rectangle n) (ε : ℝ≥0)
    (hRT : alphaLE R T)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module) (hf : f ≠ 0)
    (g : S.module (k := k) ⟶ (shift ε).obj T.module) (hg : g ≠ 0) :
    endpointClose (((2 * n : ℝ) - 1) * (ε : ℝ)) R S ∨
      endpointClose (((2 * n : ℝ) - 1) * (ε : ℝ)) S T := by
  have hε := epsilon_le_stability_radius hn ε
  rcases alphaLE_chain_split R S T hRT with hRS | hST
  · left
    intro j
    exact ⟨reverse_endpoint_bounds_of_alphaLE R S (ε : ℝ)
      (shifted_hom_endpoint_bounds R S ε f hf) hRS j,
      decoratedLE_add_mono (shifted_hom_endpoint_bounds R S ε f hf j) hε⟩
  · right
    intro j
    exact ⟨reverse_endpoint_bounds_of_alphaLE S T (ε : ℝ)
      (shifted_hom_endpoint_bounds S T ε g hg) hST j,
      decoratedLE_add_mono (shifted_hom_endpoint_bounds S T ε g hg j) hε⟩

/-- The sharp nonnegative parameter for the rectangle stability edge. -/
def stabilityRadius (n : ℕ) (ε : ℝ≥0) : ℝ≥0 :=
  ((2 * n - 1 : ℕ) : ℝ≥0) * ε

example (ε : ℝ≥0) : stabilityRadius 1 ε = ε := by
  simp [stabilityRadius]

example (n : ℕ) : stabilityRadius n 0 = 0 := by
  simp [stabilityRadius]

private theorem stabilityRadius_coe {n : ℕ} (hn : 0 < n) (ε : ℝ≥0) :
    (stabilityRadius n ε : ℝ) = ((2 * n : ℝ) - 1) * (ε : ℝ) := by
  have hnat : 1 ≤ 2 * n := by omega
  simp only [stabilityRadius, NNReal.coe_mul, NNReal.coe_natCast]
  rw [Nat.cast_sub hnat]
  norm_num

/-- Bjerkevik's rectangle geometry edge (published Lemma 4.7), specialized
to nonempty bounded rectangles with arbitrary open/closed decorations. Two
nonzero shifted natural transformations along `R → S → T` and `R ≤α T`
produce an actual `(2n−1)ε` interleaving of S with R or T. -/
theorem nonzero_path_interleaving {n : ℕ} (hn : 0 < n)
    {k : Type u} [Field k] (R S T : Rectangle n) (ε : ℝ≥0)
    (hRT : alphaLE R T)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module) (hf : f ≠ 0)
    (g : S.module (k := k) ⟶ (shift ε).obj T.module) (hg : g ≠ 0) :
    Nonempty (CoordinateInterleaving (stabilityRadius n ε)
      (R.module (k := k)) S.module) ∨
      Nonempty (CoordinateInterleaving (stabilityRadius n ε)
        (S.module (k := k)) T.module) := by
  rcases nonzero_path_endpointClose hn R S T ε hRT f hf g hg with h | h
  · left
    exact ⟨interleavingOfEndpointClose R S (stabilityRadius n ε)
      (by simpa only [stabilityRadius_coe hn ε] using h)⟩
  · right
    exact ⟨interleavingOfEndpointClose S T (stabilityRadius n ε)
      (by simpa only [stabilityRadius_coe hn ε] using h)⟩

private theorem alphaValue_eq_sum {n : ℕ} (R : Rectangle n) :
    alphaValue R = ∑ i, ((R i).lower + (R i).upper) := by
  simp [alphaValue, endpoint, Fintype.sum_prod_type, add_comm]

private theorem cross_coordinate_bound {n : ℕ} (R T : Rectangle n)
    (δ : ℝ) (hα : alphaValue R ≤ alphaValue T)
    (hl : ∀ i, (T i).lower ≤ (R i).lower + 2 * δ)
    (hu : ∀ i, (T i).upper ≤ (R i).upper + 2 * δ) (j : Fin n) :
    ((R j).upper - (R j).lower) + ((T j).upper - (T j).lower) ≤
      4 * ((n : ℝ) - 1) * δ + 2 * ((T j).upper - (R j).lower) := by
  have hb := sum_erase_bound
    (fun i => (R i).lower + (R i).upper)
    (fun i => (T i).lower + (T i).upper) (4 * δ)
    (fun i => by linarith [hl i, hu i]) j
  have hs : (∑ i, (((T i).lower + (T i).upper) -
      ((R i).lower + (R i).upper))) = alphaValue T - alphaValue R := by
    rw [Finset.sum_sub_distrib, alphaValue_eq_sum, alphaValue_eq_sum]
  have he := Finset.sum_erase_add (s := Finset.univ)
    (fun i => ((T i).lower + (T i).upper) - ((R i).lower + (R i).upper))
    (Finset.mem_univ j)
  rw [hs] at he
  simp only [Fintype.card_fin] at hb
  linarith

/-- Long α-ordered endpoints of a nonzero two-step path have a common
source, middle and twice-shifted target grade. This is the specialization of
Bjerkevik's Lemma 4.8 at the significance threshold required by the finite
Hall inequality. -/
theorem nonzero_path_support {n : ℕ} (hn : 0 < n)
    {k : Type u} [Field k] (R S T : Rectangle n) (ε : ℝ≥0)
    (hRT : alphaLE R T)
    (hR : ∃ p, p ∈ R.support ∧
      translation (stabilityRadius n ε + stabilityRadius n ε) p ∈ R.support)
    (hT : ∃ p, p ∈ T.support ∧
      translation (stabilityRadius n ε + stabilityRadius n ε) p ∈ T.support)
    (f : R.module (k := k) ⟶ (shift ε).obj S.module) (hf : f ≠ 0)
    (g : S.module (k := k) ⟶ (shift ε).obj T.module) (hg : g ≠ 0) :
    ∃ p, p ∈ R.support ∧ translation ε p ∈ S.support ∧
      translation (ε + ε) p ∈ T.support := by
  classical
  obtain ⟨pR, hpR, hpR'⟩ := hR
  obtain ⟨pT, hpT, hpT'⟩ := hT
  let w : ℝ := 2 * (stabilityRadius n ε : ℝ)
  have hw : 2 * (ε : ℝ) ≤ w := by
    dsimp [w]
    rw [stabilityRadius_coe hn ε]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [ε.coe_nonneg]
  have hstepR (j : Fin n) := (R j).exists_mem_add_iff w (by
    dsimp [w]; positivity)
  have hstepT (j : Fin n) := (T j).exists_mem_add_iff w (by
    dsimp [w]; positivity)
  have hwidthR (j : Fin n) := (hstepR j).mp
    ⟨pR j, hpR j, by simpa [translation_apply, w, NNReal.coe_add, two_mul] using hpR' j⟩
  have hwidthT (j : Fin n) := (hstepT j).mp
    ⟨pT j, hpT j, by simpa [translation_apply, w, NNReal.coe_add, two_mul] using hpT' j⟩
  have hRf (j : Fin n × Bool) := shifted_hom_endpoint_bounds R S ε f hf j
  have hSg (j : Fin n × Bool) := shifted_hom_endpoint_bounds S T ε g hg j
  have hl (j : Fin n) : (T j).lower ≤ (R j).lower + 2 * (ε : ℝ) := by
    have h₁ := decoratedLE_value (hRf (j, false))
    have h₂ := decoratedLE_value (hSg (j, false))
    simp only [endpoint, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
    linarith
  have hu (j : Fin n) : (T j).upper ≤ (R j).upper + 2 * (ε : ℝ) := by
    have h₁ := decoratedLE_value (hRf (j, true))
    have h₂ := decoratedLE_value (hSg (j, true))
    simp only [endpoint, ↓reduceIte] at h₁ h₂
    linarith
  have hex (j : Fin n) : ∃ x, x ∈ (R j).support ∧
      x + 2 * (ε : ℝ) ∈ (T j).support := by
    have hr : w ≤ (R j).upper - (R j).lower :=
      (hwidthR j).elim le_of_lt (fun h => h.1.le)
    have ht : w ≤ (T j).upper - (T j).lower :=
      (hwidthT j).elim le_of_lt (fun h => h.1.le)
    have hb := cross_coordinate_bound R T (ε : ℝ)
      (hRT.elim le_of_lt (fun h => h.1.le)) hl hu j
    have hw' : w = (4 * (n : ℝ) - 2) * (ε : ℝ) := by
      dsimp [w]; rw [stabilityRadius_coe hn ε]; ring
    have hc : (R j).lower + 2 * (ε : ℝ) ≤ (T j).upper := by
      nlinarith [hw]
    rcases lt_or_eq_of_le hc with hc | hc
    · let x := ((R j).lower + (T j).upper - 2 * (ε : ℝ)) / 2
      refine ⟨x, ⟨Or.inl ?_, Or.inl ?_⟩, ⟨Or.inl ?_, Or.inl ?_⟩⟩ <;>
        dsimp [x] <;> linarith [hl j, hu j]
    · have hwr : w = (R j).upper - (R j).lower := by nlinarith
      have hwt : w = (T j).upper - (T j).lower := by nlinarith
      have hrclosed : (R j).lowerClosed = true := by
        rcases hwidthR j with h | h
        · exact False.elim (by linarith)
        · exact h.2.1
      have htclosed : (T j).upperClosed = true := by
        rcases hwidthT j with h | h
        · exact False.elim (by linarith)
        · exact h.2.2
      exact ⟨(R j).lower, interval_lower_mem_of_closed (R j) (hpR j) hrclosed,
        hc ▸ interval_upper_mem_of_closed (T j) (hpT j) htclosed⟩
  choose p hpR₀ hpT₀ using hex
  refine ⟨p, hpR₀, ?_, ?_⟩
  · intro j
    have hlo := lower_mem_of_bound (R j) (S j) (ε : ℝ) (hRf (j, false)) (hpR₀ j)
    have hup := upper_mem_of_bound (S j) (T j) (ε : ℝ) (hSg (j, true)) (hpT₀ j)
    constructor
    · simpa [translation_apply] using hlo
    · have he : p j + 2 * (ε : ℝ) - (ε : ℝ) = (translation ε p) j := by
        simp only [translation_apply]
        ring
      rw [he] at hup
      exact hup
  · intro j
    simpa [translation_apply, NNReal.coe_add, two_mul] using hpT₀ j

end RectangleStabilityGeometry
end TDA.Persistence
