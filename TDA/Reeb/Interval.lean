import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Convex.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.NatIso
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Sets.Opens

/-!
# Real open intervals and thickening

`OpenInterval` is the type of open order-convex subsets of `ℝ`: de Silva–Munch–Patel's open
intervals together with `∅` (`⊥`), the open rays (`ioi`, `iio`) and `ℝ` itself (`⊤`). Bounded
intervals are `ioo a b`, which is `⊥` when `b ≤ a`. Morphisms are inclusions: the order is
`SetLike` inclusion and the category is mathlib's thin category of a preorder. Intersection is
the meet (`SemilatticeInf`); there is no join, since a union of order-convex sets need not be
order-convex. Every object is recovered from its `EReal` endpoints (`ofEReal_lower_upper`).
`toOpens` includes the interval category into `TopologicalSpace.Opens ℝ`; the inclusion is fully
faithful because both categories are thin and `toOpens_le_iff` holds (no `FullyFaithful` instance
is packaged). It preserves binary intersections and the union equation of a cover.

For `ε : ℝ≥0`, `thicken ε I = I + [-ε, ε]`. It is again open and order-convex, `thicken 0` is
the identity, it fixes `⊥` and `⊤`, is monotone in `I` and `ε`, contains `I`, and satisfies
`thicken ε (thicken δ I) = thicken (ε + δ) I`. On bounded intervals with `a < b` it moves the
endpoints outward by `ε`; the hypothesis `a < b` is needed because every `ioo a b` with
`b ≤ a` is empty. For `0 < ε` it agrees with `Metric.thickening`, which is empty at `ε = 0`.
`thickenFunctor` packages thickening as an endofunctor with unit, enlargement maps and the
identity and composition isomorphisms. See `docs/math/reeb-intervals.md`.
-/

open Set CategoryTheory
open scoped NNReal Pointwise

namespace TDA.Reeb

/-- An open order-convex subset of `ℝ` (DMP's "open interval", including `∅`, rays, `ℝ`). -/
structure OpenInterval where
  carrier : Set ℝ
  isOpen' : IsOpen carrier
  ordConnected' : carrier.OrdConnected

namespace OpenInterval

instance : SetLike OpenInterval ℝ :=
  ⟨OpenInterval.carrier, fun p q h => by cases p; cases q; congr⟩

instance : PartialOrder OpenInterval := .ofSetLike OpenInterval ℝ

@[ext] theorem ext {I J : OpenInterval} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J := SetLike.ext h

@[simp] theorem mem_mk {s : Set ℝ} {h₁ h₂} {x : ℝ} :
    x ∈ (⟨s, h₁, h₂⟩ : OpenInterval) ↔ x ∈ s := Iff.rfl

@[simp] theorem coe_mk {s : Set ℝ} {h₁ h₂} : ((⟨s, h₁, h₂⟩ : OpenInterval) : Set ℝ) = s := rfl

theorem isOpen (I : OpenInterval) : IsOpen (I : Set ℝ) := I.isOpen'

theorem ordConnected (I : OpenInterval) : (I : Set ℝ).OrdConnected := I.ordConnected'

theorem le_iff_subset {I J : OpenInterval} : I ≤ J ↔ (I : Set ℝ) ⊆ J :=
  SetLike.coe_subset_coe.symm

/-! ### Distinguished objects -/

instance : Bot OpenInterval := ⟨⟨∅, isOpen_empty, ordConnected_empty⟩⟩
instance : Top OpenInterval := ⟨⟨univ, isOpen_univ, ordConnected_univ⟩⟩

@[simp] theorem coe_bot : ((⊥ : OpenInterval) : Set ℝ) = ∅ := rfl
@[simp] theorem coe_top : ((⊤ : OpenInterval) : Set ℝ) = univ := rfl

instance : OrderBot OpenInterval where
  bot_le _ := le_iff_subset.2 (empty_subset _)

instance : OrderTop OpenInterval where
  le_top _ := le_iff_subset.2 (subset_univ _)

/-- Bounded open interval `(a, b)` (empty when `b ≤ a`). -/
def ioo (a b : ℝ) : OpenInterval := ⟨Ioo a b, isOpen_Ioo, ordConnected_Ioo⟩
/-- Open upper ray `(a, ∞)`. -/
def ioi (a : ℝ) : OpenInterval := ⟨Ioi a, isOpen_Ioi, ordConnected_Ioi⟩
/-- Open lower ray `(-∞, b)`. -/
def iio (b : ℝ) : OpenInterval := ⟨Iio b, isOpen_Iio, ordConnected_Iio⟩

@[simp] theorem coe_ioo (a b : ℝ) : (ioo a b : Set ℝ) = Ioo a b := rfl
@[simp] theorem coe_ioi (a : ℝ) : (ioi a : Set ℝ) = Ioi a := rfl
@[simp] theorem coe_iio (b : ℝ) : (iio b : Set ℝ) = Iio b := rfl

/-- Binary intersection is the meet of the inclusion order. The join is not provided:
a union of order-convex sets need not be order-convex. -/
instance : SemilatticeInf OpenInterval where
  inf I J := ⟨(I : Set ℝ) ∩ (J : Set ℝ), I.isOpen.inter J.isOpen,
    I.ordConnected.inter J.ordConnected⟩
  inf_le_left _ _ := le_iff_subset.2 inter_subset_left
  inf_le_right _ _ := le_iff_subset.2 inter_subset_right
  le_inf _ _ _ h₁ h₂ := le_iff_subset.2 (subset_inter (le_iff_subset.1 h₁) (le_iff_subset.1 h₂))

@[simp] theorem coe_inf (I J : OpenInterval) : ((I ⊓ J : OpenInterval) : Set ℝ) = (I : Set ℝ) ∩ (J : Set ℝ) := rfl

/-! ### Endpoint encoding over `EReal` -/

/-- The set `{x : ℝ | a < x < b}` for extended-real endpoints. -/
def ofEReal (a b : EReal) : OpenInterval where
  carrier := {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}
  isOpen' := isOpen_Ioo.preimage continuous_coe_real_ereal
  ordConnected' := (ordConnected_Ioo (a := a) (b := b)).preimage_mono EReal.coe_strictMono.monotone

@[simp] theorem mem_ofEReal {a b : EReal} {x : ℝ} :
    x ∈ ofEReal a b ↔ a < (x : EReal) ∧ (x : EReal) < b := Iff.rfl

/-- Lower endpoint in `EReal` (`⊤` for the empty set). -/
noncomputable def lower (I : OpenInterval) : EReal := sInf ((↑) '' (I : Set ℝ))
/-- Upper endpoint in `EReal` (`⊥` for the empty set). -/
noncomputable def upper (I : OpenInterval) : EReal := sSup ((↑) '' (I : Set ℝ))

/-- Every object is recovered from its `EReal` endpoints (including `∅`, rays and `ℝ`). -/
theorem ofEReal_lower_upper (I : OpenInterval) : ofEReal I.lower I.upper = I := by
  ext x
  simp only [mem_ofEReal, lower, upper]
  constructor
  · rintro ⟨hl, hu⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := sInf_lt_iff.1 hl
    obtain ⟨_, ⟨z, hz, rfl⟩, hxz⟩ := lt_sSup_iff.1 hu
    exact I.ordConnected.out hy hz
      ⟨(EReal.coe_lt_coe_iff.1 hyx).le, (EReal.coe_lt_coe_iff.1 hxz).le⟩
  · intro hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 I.isOpen x hx
    have h₁ : x - δ / 2 ∈ (I : Set ℝ) := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    have h₂ : x + δ / 2 ∈ (I : Set ℝ) := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    refine ⟨lt_of_le_of_lt (sInf_le ⟨_, h₁, rfl⟩) ?_, lt_of_lt_of_le ?_ (le_sSup ⟨_, h₂, rfl⟩)⟩
    · exact EReal.coe_lt_coe_iff.2 (by linarith)
    · exact EReal.coe_lt_coe_iff.2 (by linarith)

theorem exists_eq_ofEReal (I : OpenInterval) : ∃ a b : EReal, I = ofEReal a b :=
  ⟨_, _, (ofEReal_lower_upper I).symm⟩

/-! ### Inclusion into `Opens ℝ` -/

/-- The underlying open set. -/
def toOpens (I : OpenInterval) : TopologicalSpace.Opens ℝ := ⟨I, I.isOpen⟩

@[simp] theorem coe_toOpens (I : OpenInterval) : ((toOpens I : Set ℝ)) = I := rfl

theorem toOpens_monotone : Monotone toOpens := fun _ _ h => le_iff_subset.1 h

theorem toOpens_le_iff {I J : OpenInterval} : toOpens I ≤ toOpens J ↔ I ≤ J := by
  rw [le_iff_subset, ← SetLike.coe_subset_coe]; rfl

theorem toOpens_inf (I J : OpenInterval) : toOpens (I ⊓ J) = toOpens I ⊓ toOpens J := by
  ext x; simp [toOpens]

/-- The union equation of an interval cover transfers to `Opens ℝ`. -/
theorem iSup_toOpens_eq {ι : Sort*} (I : ι → OpenInterval) (U : OpenInterval)
    (hU : ⋃ i, (I i : Set ℝ) = U) : ⨆ i, toOpens (I i) = toOpens U := by
  ext x; simp [toOpens, ← hU]

/-- The (fully faithful) inclusion functor of the interval category into `Opens ℝ`. -/
def toOpensFunctor : OpenInterval ⥤ TopologicalSpace.Opens ℝ := toOpens_monotone.functor

/-! ### Thickening -/

/-- `T_ε s = s + [-ε, ε]` on sets. -/
def thickenSet (ε : ℝ≥0) (s : Set ℝ) : Set ℝ := s + Icc (-(ε : ℝ)) ε

theorem mem_thickenSet {ε : ℝ≥0} {s : Set ℝ} {x : ℝ} :
    x ∈ thickenSet ε s ↔ ∃ y ∈ s, |x - y| ≤ ε := by
  simp only [thickenSet, mem_add, mem_Icc, abs_le]
  constructor
  · rintro ⟨y, hy, t, ⟨ht₁, ht₂⟩, rfl⟩
    exact ⟨y, hy, by linarith, by linarith⟩
  · rintro ⟨y, hy, h₁, h₂⟩
    exact ⟨y, hy, x - y, ⟨h₁, h₂⟩, by ring⟩

theorem isOpen_thickenSet {s : Set ℝ} (hs : IsOpen s) (ε : ℝ≥0) : IsOpen (thickenSet ε s) :=
  hs.add_right

theorem ordConnected_thickenSet {s : Set ℝ} (hs : s.OrdConnected) (ε : ℝ≥0) :
    (thickenSet ε s).OrdConnected :=
  convex_iff_ordConnected.1 ((convex_iff_ordConnected.2 hs).add (convex_Icc _ _))

/-- Thickening of an object of the interval category. -/
def thicken (ε : ℝ≥0) (I : OpenInterval) : OpenInterval :=
  ⟨thickenSet ε I, isOpen_thickenSet I.isOpen ε, ordConnected_thickenSet I.ordConnected ε⟩

@[simp] theorem coe_thicken (ε : ℝ≥0) (I : OpenInterval) :
    (thicken ε I : Set ℝ) = (I : Set ℝ) + Icc (-(ε : ℝ)) ε := rfl

theorem mem_thicken {ε : ℝ≥0} {I : OpenInterval} {x : ℝ} :
    x ∈ thicken ε I ↔ ∃ y ∈ I, |x - y| ≤ ε := mem_thickenSet

@[simp] theorem thicken_zero (I : OpenInterval) : thicken 0 I = I := by
  ext x; simp [mem_thicken, sub_eq_zero]

@[simp] theorem thicken_bot (ε : ℝ≥0) : thicken ε ⊥ = ⊥ := by
  ext x
  rw [mem_thicken]
  constructor
  · rintro ⟨y, hy, -⟩; exact (notMem_empty y hy).elim
  · intro h; exact (notMem_empty x h).elim

@[simp] theorem thicken_top (ε : ℝ≥0) : thicken ε ⊤ = ⊤ := by
  ext x; simp only [mem_thicken]; exact ⟨fun _ => trivial, fun _ => ⟨x, trivial, by simp⟩⟩

theorem le_thicken (ε : ℝ≥0) (I : OpenInterval) : I ≤ thicken ε I := fun x hx =>
  mem_thicken.2 ⟨x, hx, by simp⟩

theorem thicken_mono {ε : ℝ≥0} {I J : OpenInterval} (h : I ≤ J) : thicken ε I ≤ thicken ε J :=
  fun x hx => by
    obtain ⟨y, hy, hxy⟩ := mem_thicken.1 hx
    exact mem_thicken.2 ⟨y, h hy, hxy⟩

theorem thicken_monotone (ε : ℝ≥0) : Monotone (thicken ε) := fun _ _ h => thicken_mono h

theorem thicken_le_thicken_of_le {ε δ : ℝ≥0} (h : ε ≤ δ) (I : OpenInterval) :
    thicken ε I ≤ thicken δ I := fun x hx => by
  obtain ⟨y, hy, hxy⟩ := mem_thicken.1 hx
  exact mem_thicken.2 ⟨y, hy, hxy.trans (by exact_mod_cast h)⟩

/-- Semigroup law: `T_ε (T_δ I) = T_(ε+δ) I`. -/
theorem thicken_thicken (ε δ : ℝ≥0) (I : OpenInterval) :
    thicken ε (thicken δ I) = thicken (ε + δ) I := by
  apply SetLike.coe_injective
  simp only [coe_thicken, add_assoc,
    Set.Icc_add_Icc (by simp : -(δ : ℝ) ≤ δ) (by simp : -(ε : ℝ) ≤ ε)]
  congr 2 <;> push_cast <;> ring

/-- The other composition order. -/
theorem thicken_thicken' (ε δ : ℝ≥0) (I : OpenInterval) :
    thicken δ (thicken ε I) = thicken (ε + δ) I := by
  rw [thicken_thicken, add_comm]

theorem thicken_comm (ε δ : ℝ≥0) (I : OpenInterval) :
    thicken ε (thicken δ I) = thicken δ (thicken ε I) := by
  rw [thicken_thicken, thicken_thicken, add_comm]

/-! ### Endpoint formulas -/

theorem thicken_ioo {a b : ℝ} (hab : a < b) (ε : ℝ≥0) :
    thicken ε (ioo a b) = ioo (a - ε) (b + ε) := by
  ext x
  simp only [mem_thicken, abs_le]
  change (∃ y ∈ Ioo a b, _) ↔ x ∈ Ioo (a - ε) (b + ε)
  simp only [mem_Ioo]
  constructor
  · rintro ⟨y, ⟨hay, hyb⟩, h₁, h₂⟩; constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    by_cases hxa : x ≤ a
    · refine ⟨min (x + ε) ((a + b) / 2), ⟨lt_min (by linarith) (by linarith),
        (min_le_right _ _).trans_lt (by linarith)⟩, ?_, ?_⟩
      · linarith [min_le_left (x + (ε : ℝ)) ((a + b) / 2)]
      · rcases min_cases (x + (ε : ℝ)) ((a + b) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
          linarith [ε.coe_nonneg]
    by_cases hxb : b ≤ x
    · refine ⟨max (x - ε) ((a + b) / 2), ⟨(by linarith : a < (a + b) / 2).trans_le
        (le_max_right _ _), max_lt (by linarith) (by linarith)⟩, ?_, ?_⟩
      · rcases max_cases (x - (ε : ℝ)) ((a + b) / 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
          linarith [ε.coe_nonneg]
      · linarith [le_max_left (x - (ε : ℝ)) ((a + b) / 2)]
    · rw [not_le] at hxa hxb
      exact ⟨x, ⟨hxa, hxb⟩, by linarith [ε.coe_nonneg], by linarith [ε.coe_nonneg]⟩

theorem thicken_ioi (a : ℝ) (ε : ℝ≥0) : thicken ε (ioi a) = ioi (a - ε) := by
  ext x
  rw [mem_thicken]
  change (∃ y ∈ Ioi a, |x - y| ≤ ε) ↔ x ∈ Ioi (a - ε)
  simp only [mem_Ioi, abs_le]
  constructor
  · rintro ⟨y, hy, h₁, h₂⟩; linarith
  · intro hx
    by_cases hxa : a < x
    · exact ⟨x, hxa, by linarith [ε.coe_nonneg], by linarith [ε.coe_nonneg]⟩
    · exact ⟨x + ε, by linarith, by linarith, by linarith [ε.coe_nonneg]⟩

theorem thicken_iio (b : ℝ) (ε : ℝ≥0) : thicken ε (iio b) = iio (b + ε) := by
  ext x
  rw [mem_thicken]
  change (∃ y ∈ Iio b, |x - y| ≤ ε) ↔ x ∈ Iio (b + ε)
  simp only [mem_Iio, abs_le]
  constructor
  · rintro ⟨y, hy, h₁, h₂⟩; linarith
  · intro hx
    by_cases hxb : x < b
    · exact ⟨x, hxb, by linarith [ε.coe_nonneg], by linarith [ε.coe_nonneg]⟩
    · exact ⟨x - ε, by linarith, by linarith [ε.coe_nonneg], by linarith⟩

/-! ### Comparison with `Metric.thickening` -/

/-- For open `s` and `ε > 0`, `s + [-ε, ε]` is mathlib's open thickening. Fails at `ε = 0`
(`Metric.thickening 0 s = ∅`), so `thickenSet` is not definitionally `Metric.thickening`. -/
theorem thickenSet_eq_thickening {s : Set ℝ} (hs : IsOpen s) {ε : ℝ≥0} (hε : 0 < ε) :
    thickenSet ε s = Metric.thickening ε s := by
  have hε' : (0 : ℝ) < ε := hε
  apply Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickenSet.1 hx
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hs y hy
    -- move `y` towards `x` by the fraction `k` of the offset
    set k : ℝ := min (η / 2) ε / (2 * ε) with hk
    have hk0 : 0 < k := div_pos (lt_min (by linarith) hε') (by linarith)
    have hk1 : k ≤ 1 / 2 := by
      rw [hk, div_le_iff₀ (by linarith)]; linarith [min_le_right (η / 2) (ε : ℝ)]
    have hkη : k * ε < η := by
      rw [hk, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith [min_le_left (η / 2) (ε : ℝ)]
    refine Metric.mem_thickening_iff.2 ⟨y + k * (x - y), hball ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, show y + k * (x - y) - y = k * (x - y) by ring,
        abs_mul, abs_of_pos hk0]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxy hk0.le) hkη
    · rw [Real.dist_eq, show x - (y + k * (x - y)) = (1 - k) * (x - y) by ring, abs_mul,
        abs_of_pos (by linarith)]
      calc (1 - k) * |x - y| ≤ (1 - k) * ε := mul_le_mul_of_nonneg_left hxy (by linarith)
        _ < ε := by nlinarith
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.1 hx
    rw [Real.dist_eq] at hxy
    exact mem_thickenSet.2 ⟨y, hy, hxy.le⟩

theorem coe_thicken_eq_thickening (I : OpenInterval) {ε : ℝ≥0} (hε : 0 < ε) :
    (thicken ε I : Set ℝ) = Metric.thickening ε I :=
  thickenSet_eq_thickening I.isOpen hε

/-! ### Categorical packaging -/

/-- Thickening as an endofunctor of the interval category. -/
def thickenFunctor (ε : ℝ≥0) : OpenInterval ⥤ OpenInterval := (thicken_monotone ε).functor

@[simp] theorem thickenFunctor_obj (ε : ℝ≥0) (I : OpenInterval) :
    (thickenFunctor ε).obj I = thicken ε I := rfl

/-- The unit `I ⟶ T_ε I`. -/
def thickenUnit (ε : ℝ≥0) : 𝟭 OpenInterval ⟶ thickenFunctor ε where
  app I := homOfLE (le_thicken ε I)

/-- Enlargement `T_ε ⟶ T_δ` for `ε ≤ δ`. -/
def thickenMap {ε δ : ℝ≥0} (h : ε ≤ δ) : thickenFunctor ε ⟶ thickenFunctor δ where
  app I := homOfLE (thicken_le_thicken_of_le h I)

/-- `T₀ ≅ 𝟭`. -/
def thickenZeroIso : thickenFunctor 0 ≅ 𝟭 OpenInterval :=
  NatIso.ofComponents (fun I => eqToIso (thicken_zero I))

/-- `T_ε ⋙ T_δ ≅ T_(ε+δ)` (apply `T_ε` first), so that `S_ε (S_δ F) = (T_ε ⋙ T_δ) ⋙ F`. -/
def thickenCompIso (ε δ : ℝ≥0) :
    thickenFunctor ε ⋙ thickenFunctor δ ≅ thickenFunctor (ε + δ) :=
  NatIso.ofComponents (fun I => eqToIso (thicken_thicken' ε δ I))

/-- Coherence is automatic in the thin category: e.g. the unit of `ε + δ` factors. -/
theorem thickenUnit_comp (ε δ : ℝ≥0) (I : OpenInterval) :
    (thickenUnit ε).app I ≫ (thickenUnit δ).app (thicken ε I) ≫
      ((thickenCompIso ε δ).hom.app I) = (thickenUnit (ε + δ)).app I :=
  Subsingleton.elim _ _

end OpenInterval

end TDA.Reeb
