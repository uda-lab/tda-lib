import TDA.Persistence.SupportInterval
import TDA.Persistence.RealCoordinates
import Mathlib.Tactic.Linarith

/-!
# Bounded rectangles with included or excluded endpoints

Each coordinate interval records both endpoint inclusion choices. A nonempty
interval may be a closed singleton. A rectangle is a family of such intervals;
its persistence module has one coefficient on the rectangle and zero elsewhere.
The transition criterion below detects the endpoint-sensitive equality case:
a coordinate survives a translation equal to its length precisely when both
endpoints are included.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

/-- A bounded nonempty real interval, with independently included endpoints. -/
structure BoundedInterval where
  lower : ℝ
  upper : ℝ
  lowerClosed : Bool
  upperClosed : Bool
  nonempty : lower < upper ∨
    (lower = upper ∧ lowerClosed = true ∧ upperClosed = true)

namespace BoundedInterval

/-- Membership retains both endpoint inclusion choices. -/
def support (I : BoundedInterval) : Set ℝ :=
  {x | (I.lower < x ∨ (I.lower = x ∧ I.lowerClosed = true)) ∧
    (x < I.upper ∨ (x = I.upper ∧ I.upperClosed = true))}

/-- Every bounded interval is order-convex. -/
theorem ordConnected (I : BoundedInterval) : I.support.OrdConnected := by
  constructor
  intro x hx y hy z hz
  rcases hx with ⟨hx, _⟩
  rcases hy with ⟨_, hy⟩
  constructor
  · rcases hx with hx | ⟨hx, hc⟩
    · exact Or.inl (hx.trans_le hz.1)
    · by_cases h : x = z
      · exact Or.inr ⟨hx.trans h, hc⟩
      · exact Or.inl (hx ▸ lt_of_le_of_ne hz.1 h)
  · rcases hy with hy | ⟨hy, hc⟩
    · exact Or.inl (hz.2.trans_lt hy)
    · by_cases h : z = y
      · exact Or.inr ⟨h.trans hy, hc⟩
      · exact Or.inl (hy ▸ lt_of_le_of_ne hz.2 h)

/-- A nonnegative translation fits inside an interval exactly at the strict
length bound, or at equality with both endpoints included. -/
theorem exists_mem_add_iff (I : BoundedInterval) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∃ x, x ∈ I.support ∧ x + δ ∈ I.support) ↔
      δ < I.upper - I.lower ∨
        (δ = I.upper - I.lower ∧ I.lowerClosed = true ∧ I.upperClosed = true) := by
  constructor
  · rintro ⟨x, hx, hy⟩
    have hl : I.lower ≤ x := hx.1.elim le_of_lt (fun h => h.1.le)
    have hu : x + δ ≤ I.upper := hy.2.elim le_of_lt (fun h => h.1.le)
    by_cases h : δ < I.upper - I.lower
    · exact Or.inl h
    · have he : δ = I.upper - I.lower := by linarith
      have hx' : x = I.lower := by linarith
      have hy' : x + δ = I.upper := by linarith
      refine Or.inr ⟨he, ?_, ?_⟩
      · rcases hx.1 with hh | hh
        · exact False.elim (by linarith)
        · exact hh.2
      · rcases hy.2 with hh | hh
        · exact False.elim (by linarith)
        · exact hh.2
  · rintro (h | ⟨h, hl, hu⟩)
    · refine ⟨(I.lower + I.upper - δ) / 2, ?_, ?_⟩
      · exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩
      · exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩
    · refine ⟨I.lower, ⟨Or.inr ⟨rfl, hl⟩, ?_⟩, ?_⟩
      · have hle : I.lower ≤ I.upper := by linarith
        rcases lt_or_eq_of_le hle with hh | hh
        · exact Or.inl hh
        · exact Or.inr ⟨hh, hu⟩
      · constructor
        · by_cases hd : δ = 0
          · exact Or.inr ⟨by simp [hd], hl⟩
          · have hdpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hd)
            exact Or.inl (by linarith)
        · exact Or.inr ⟨by linarith, hu⟩

/-- The endpoint validity condition ensures that the support is nonempty. -/
theorem support_nonempty (I : BoundedInterval) : I.support.Nonempty := by
  have h : (0 : ℝ) < I.upper - I.lower ∨
      (0 = I.upper - I.lower ∧ I.lowerClosed = true ∧ I.upperClosed = true) := by
    rcases I.nonempty with h | ⟨h, hl, hu⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hl, hu⟩
  obtain ⟨x, hx, _⟩ := (I.exists_mem_add_iff 0 le_rfl).mpr h
  exact ⟨x, hx⟩

end BoundedInterval

/-- One bounded interval for each coordinate. Families of rectangles can be
indexed by occurrences, so equal rectangles need not be identified. -/
abbrev Rectangle (n : ℕ) := Fin n → BoundedInterval

namespace Rectangle

open scoped TDA.Persistence

/-- The cartesian product support of a rectangle. -/
def support {n : ℕ} (R : Rectangle n) : Set (Fin n → ℝ) :=
  {p | ∀ i, p i ∈ (R i).support}

/-- The support of a rectangle is order-convex for the coordinatewise order. -/
theorem ordConnected {n : ℕ} (R : Rectangle n) : R.support.OrdConnected := by
  constructor
  intro p hp q hq r hr i
  exact (R i).ordConnected.out (hp i) (hq i) ⟨hr.1 i, hr.2 i⟩

/-- Every rectangle has a point, including products with singleton coordinates. -/
theorem support_nonempty {n : ℕ} (R : Rectangle n) : R.support.Nonempty := by
  classical
  choose p hp using fun i => (R i).support_nonempty
  exact ⟨p, hp⟩

/-- Coordinatewise minima stay in a rectangle, for every endpoint convention. -/
theorem inf_mem {n : ℕ} (R : Rectangle n) {p q : Fin n → ℝ}
    (hp : p ∈ R.support) (hq : q ∈ R.support) : p ⊓ q ∈ R.support := by
  intro i
  change min (p i) (q i) ∈ (R i).support
  rw [min_def]
  split_ifs
  · exact hp i
  · exact hq i

/-- The interval module of a bounded rectangle. -/
@[reducible]
noncomputable def module {n : ℕ} {k : Type u} [Field k] (R : Rectangle n) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  SupportInterval.module R.support R.ordConnected

/-- A morphism between rectangle modules has the same scalar coefficient at
every point of the overlap. Coordinatewise minima connect any two points.
This is the rectangle case of Bjerkevik's scalar-constancy argument. -/
theorem hom_coefficient_eq {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (α : R.module (k := k) ⟶ S.module)
    {p q : Fin n → ℝ} (hpR : p ∈ R.support) (hpS : p ∈ S.support)
    (hqR : q ∈ R.support) (hqS : q ∈ S.support) :
    (((α.app p).hom (SupportInterval.one (k := k) R.support hpR)) : k) =
      (((α.app q).hom (SupportInterval.one (k := k) R.support hqR)) : k) := by
  have hmR := R.inf_mem hpR hqR
  have hmp := SupportInterval.coefficient_eq_of_le R.support S.support
    R.ordConnected S.ordConnected α inf_le_left hmR hpR hpS
  have hmq := SupportInterval.coefficient_eq_of_le R.support S.support
    R.ordConnected S.ordConnected α inf_le_right hmR hqR hqS
  exact hmp.symm.trans hmq

/-- On a nonempty overlap, a single scalar coefficient determines the entire
morphism between rectangle modules. -/
theorem hom_ext {n : ℕ} {k : Type u} [Field k]
    (R S : Rectangle n) (α β : R.module (k := k) ⟶ S.module)
    {p : Fin n → ℝ} (hpR : p ∈ R.support) (hpS : p ∈ S.support)
    (h : (((α.app p).hom (SupportInterval.one (k := k) R.support hpR)) : k) =
      (((β.app p).hom (SupportInterval.one (k := k) R.support hpR)) : k)) : α = β := by
  ext q x
  by_cases hqR : q ∈ R.support
  · by_cases hqS : q ∈ S.support
    · rw [SupportInterval.app_val_eq_mul R.support S.support R.ordConnected
        S.ordConnected α hqR x,
        SupportInterval.app_val_eq_mul R.support S.support R.ordConnected
        S.ordConnected β hqR x,
        ← hom_coefficient_eq R S α hpR hpS hqR hqS,
        ← hom_coefficient_eq R S β hpR hpS hqR hqS, h]
    · rw [SupportInterval.val_eq_zero S.support hqS,
        SupportInterval.val_eq_zero S.support hqS]
  · have hx : x = 0 := Subtype.ext (SupportInterval.val_eq_zero R.support hqR x)
    simp [hx]

/-- A diagonal translation preserves a point of the support exactly when it
fits in every coordinate interval, including the equality endpoint case. -/
theorem exists_mem_add_iff {n : ℕ} (R : Rectangle n) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∃ p, p ∈ R.support ∧ (fun i => p i + δ) ∈ R.support) ↔
      ∀ i, δ < (R i).upper - (R i).lower ∨
        (δ = (R i).upper - (R i).lower ∧
          (R i).lowerClosed = true ∧ (R i).upperClosed = true) := by
  constructor
  · rintro ⟨p, hp, hq⟩ i
    exact ((R i).exists_mem_add_iff δ hδ).mp ⟨p i, hp i, hq i⟩
  · intro h
    classical
    choose p hp hq using fun i => ((R i).exists_mem_add_iff δ hδ).mpr (h i)
    exact ⟨p, hp, hq⟩

/-- All diagonal structure maps vanish exactly when one coordinate fails the
length test. At equality, including both endpoints prevents vanishing. -/
theorem diagonal_maps_eq_zero_iff {n : ℕ} {k : Type u} [Field k]
    (R : Rectangle n) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ p : Fin n → ℝ,
      structureMapLinear (R.module (k := k))
        (show p ≤ (fun i => p i + δ) from fun _i => le_add_of_nonneg_right hδ) = 0) ↔
      ∃ i, (R i).upper - (R i).lower < δ ∨
        ((R i).upper - (R i).lower = δ ∧
          ((R i).lowerClosed = false ∨ (R i).upperClosed = false)) := by
  classical
  have hmap :
      (∀ p : Fin n → ℝ,
        structureMapLinear (R.module (k := k))
          (show p ≤ (fun i => p i + δ) from fun i => le_add_of_nonneg_right hδ) = 0) ↔
        ¬ ∃ p, p ∈ R.support ∧ (fun i => p i + δ) ∈ R.support := by
    constructor
    · intro h ⟨p, hp, hq⟩
      exact ((SupportInterval.structureMap_eq_zero_iff R.support R.ordConnected
        (show p ≤ (fun i => p i + δ) from fun i => le_add_of_nonneg_right hδ)).mp
        (h p)) ⟨hp, hq⟩
    · intro h p
      apply (SupportInterval.structureMap_eq_zero_iff R.support R.ordConnected
        (show p ≤ (fun i => p i + δ) from fun i => le_add_of_nonneg_right hδ)).mpr
      exact fun hp => h ⟨p, hp⟩
  rw [hmap, exists_mem_add_iff R δ hδ]
  push Not
  apply exists_congr
  intro i
  constructor
  · rintro ⟨hle, hn⟩
    by_cases hlt : (R i).upper - (R i).lower < δ
    · exact Or.inl hlt
    · have he : (R i).upper - (R i).lower = δ := by linarith
      right
      refine ⟨he, ?_⟩
      cases hcl : (R i).lowerClosed <;> cases hcu : (R i).upperClosed <;>
        simp_all
  · rintro (hlt | ⟨he, hc⟩)
    · exact ⟨hlt.le, fun h => False.elim (by linarith)⟩
    · refine ⟨he.le, ?_⟩
      intro _ hcl
      rcases hc with hc | hc
      · simp [hcl] at hc
      · simp [hc]

private def halfOpenUnit : Rectangle 1 := fun _ =>
  { lower := 0, upper := 1, lowerClosed := true, upperClosed := false
    nonempty := Or.inl (by norm_num) }

private def closedPoint : Rectangle 1 := fun _ =>
  { lower := 0, upper := 0, lowerClosed := true, upperClosed := true
    nonempty := Or.inr ⟨rfl, rfl, rfl⟩ }

-- Translation by exactly the width kills a half-open interval.
example : ∀ p : Fin 1 → ℝ,
    structureMapLinear (halfOpenUnit.module (k := ℚ))
      (show p ≤ (fun i => p i + 1) from fun _ => by norm_num) = 0 := by
  apply (diagonal_maps_eq_zero_iff halfOpenUnit 1 (by norm_num)).mpr
  refine ⟨0, Or.inr ⟨?_, Or.inr ?_⟩⟩
  · norm_num [halfOpenUnit]
  · rfl

-- A closed singleton still has a nonzero structure map at zero translation.
example : ¬ ∀ p : Fin 1 → ℝ,
    structureMapLinear (closedPoint.module (k := ℚ))
      (show p ≤ (fun i => p i + 0) from fun _ => by norm_num) = 0 := by
  intro h
  obtain ⟨i, hi⟩ := (diagonal_maps_eq_zero_iff closedPoint 0 le_rfl).mp h
  fin_cases i
  simp [closedPoint] at hi

-- Every positive translation kills a closed singleton.
example : ∀ p : Fin 1 → ℝ,
    structureMapLinear (closedPoint.module (k := ℚ))
      (show p ≤ (fun i => p i + 1) from fun _ => by norm_num) = 0 := by
  apply (diagonal_maps_eq_zero_iff closedPoint 1 (by norm_num)).mpr
  refine ⟨0, Or.inl ?_⟩
  norm_num [closedPoint]

end Rectangle
end TDA.Persistence
