import TDA.Persistence.CoordinateGrid
import TDA.Persistence.FiniteInjectiveRankDimension
import TDA.Persistence.FiniteRankProjectiveEndAlgebra
import TDA.Persistence.PrincipalDownsetRankResolution
import Mathlib.Data.Fintype.WithTopBot

/-!
# Cardinalities of minimal complements in finite lattices

This file counts the minimal elements outside principal downsets in finite
products, after adjoining a new top, and in the interval-pair subtype used by
the incidence algebra model.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteLatticeComplementCardinality

open PrincipalDownsetRankResolution
open TDA.Persistence.FiniteInjectiveRankDimension
open TDA.Persistence.FiniteRankProjectiveEndAlgebra

noncomputable section

variable {ι : Type} [Fintype ι] {T : ι → Type}
  [∀ i, LinearOrder (T i)] [∀ i, Finite (T i)] [∀ i, Nonempty (T i)]

private noncomputable instance (i : ι) : Fintype (T i) := Fintype.ofFinite (T i)

private instance (i : ι) : OrderBot (T i) := by
  exact Fintype.toOrderBot (T i)

private instance (i : ι) : OrderTop (T i) := by
  exact Fintype.toOrderTop (T i)

private noncomputable instance piFintype : Fintype (∀ i, T i) := by
  classical
  letI : ∀ i, Fintype (T i) := fun i => Fintype.ofFinite (T i)
  exact Pi.instFintype

/-- A minimal complement in a finite product has a unique active coordinate;
all other coordinates are bottom, and the active value is a minimal
complement in that factor. -/
theorem mem_minimalComplement_pi_iff (p x : ∀ i, T i) :
    x ∈ minimalComplement p ↔
      ∃ i, x i ∈ minimalComplement (p i) ∧ ∀ j, j ≠ i → x j = ⊥ := by
  classical
  constructor
  · intro hx
    change Minimal (fun z : (∀ j, T j) => ¬ z ≤ p) x at hx
    have houtside : ¬ x ≤ p := hx.prop
    have hactive : ∃ i, ¬ x i ≤ p i := by
      change ¬ (∀ i, x i ≤ p i) at houtside
      by_contra h
      push Not at h
      exact houtside h
    obtain ⟨i, hi⟩ := hactive
    let y : (∀ j, T j) := Function.update (fun _ => ⊥) i (x i)
    have hyx : y ≤ x := by
      intro j
      by_cases hji : j = i
      · subst j
        simp [y]
      · simp [y, Function.update_of_ne hji]
    have hyoutside : ¬ y ≤ p := by
      intro h
      exact hi (by simpa [y] using h i)
    have hxy : y = x := hx.eq_of_le hyoutside hyx
    refine ⟨i, ?_, ?_⟩
    · change Minimal (fun a : T i => ¬ a ≤ p i) (x i)
      refine ⟨hi, ?_⟩
      intro a ha hax
      let z : (∀ j, T j) := Function.update x i a
      have hzoutside : ¬ z ≤ p := by
        intro hz
        exact ha (by simpa [z] using hz i)
      have hzx : z ≤ x := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa [z] using hax
        · simp [z, Function.update_of_ne hji]
      have hzx' : z = x := hx.eq_of_le hzoutside hzx
      have haz : a = x i := by
        simpa [z] using congrFun hzx' i
      rw [← haz]
    · intro j hji
      have hj : y j = x j := congrFun hxy j
      simpa [y, Function.update_of_ne hji] using hj.symm
  · rintro ⟨i, hi, hbottom⟩
    change Minimal (fun z : (∀ j, T j) => ¬ z ≤ p) x
    change Minimal (fun a : T i => ¬ a ≤ p i) (x i) at hi
    refine ⟨?_, ?_⟩
    · intro hle
      exact hi.prop (hle i)
    · intro y hy hyx
      have hyi : ¬ y i ≤ p i := by
        by_contra hle
        apply hy
        intro j
        by_cases hji : j = i
        · subst j
          exact hle
        · have hybot : y j = ⊥ :=
            le_antisymm (by simpa [hbottom j hji] using hyx j) bot_le
          rw [hybot]
          exact bot_le
      have hiy : y i = x i := hi.eq_of_le hyi (hyx i)
      intro j
      by_cases hji : j = i
      · subst j
        exact hiy.symm.le
      · rw [hbottom j hji]
        exact bot_le

/-- The active coordinate of a minimal complement in a finite product. -/
noncomputable def minimalComplement_pi_active (p : ∀ i, T i) :
    minimalComplement p → ι :=
  fun x => Classical.choose (mem_minimalComplement_pi_iff p x.1 |>.mp x.2)

private theorem minimalComplement_pi_active_injective (p : ∀ i, T i) :
    Function.Injective (minimalComplement_pi_active p) := by
  classical
  intro x y hxy
  apply Subtype.ext
  let i := minimalComplement_pi_active p x
  let hx := Classical.choose_spec
    (mem_minimalComplement_pi_iff p x.1 |>.mp x.2)
  let hy := Classical.choose_spec
    (mem_minimalComplement_pi_iff p y.1 |>.mp y.2)
  have hxmin : Minimal (fun a : T i => ¬ a ≤ p i) (x.1 i) := hx.1
  have hactive : i = minimalComplement_pi_active p y := by
    simpa [i] using hxy
  have hymin : Minimal (fun a : T i => ¬ a ≤ p i) (y.1 i) := by
    rw [hactive]
    exact hy.1
  have hcoord : x.1 i = y.1 i :=
    le_antisymm (hxmin.le hymin.prop) (hymin.le hxmin.prop)
  funext j
  by_cases hj : j = i
  · subst j
    exact hcoord
  · have hxi : x.1 j = ⊥ := hx.2 j hj
    have hyi : y.1 j = ⊥ := by
      apply hy.2 j
      intro h
      exact hj (h.trans hactive.symm)
    rw [hxi, hyi]

/-- The minimal-complement cardinality of a finite product is bounded by the
number of factors. -/
theorem complementCard_pi_le_card (p : ∀ i, T i) :
    complementCard p ≤ Fintype.card ι := by
  unfold complementCard
  exact Fintype.card_le_of_injective (minimalComplement_pi_active p)
    (minimalComplement_pi_active_injective p)

/-- The maximum minimal-complement cardinality in a finite product is bounded
by its number of factors. -/
theorem maxComplementCard_pi_le_card :
    maxComplementCard (S := ∀ i, T i) ≤ Fintype.card ι := by
  unfold maxComplementCard
  apply Finset.sup_le
  intro p hp
  exact complementCard_pi_le_card p

section WithTop

variable {S : Type} [Lattice S] [Finite S] [OrderBot S] [OrderTop S]

local instance : Fintype S := Fintype.ofFinite S

/-- The new top is the unique minimal complement of the old top in `WithTop`. -/
theorem minimalComplement_withTop_oldTop :
    minimalComplement ((⊤ : S) : WithTop S) = {⊤} := by
  classical
  ext x
  constructor
  · intro hx
    change Minimal (fun y : WithTop S => ¬ y ≤ ((⊤ : S) : WithTop S)) x at hx
    have hxout : ¬ x ≤ ((⊤ : S) : WithTop S) := hx.prop
    have hxtop : x = ⊤ := by
      cases x with
      | top => rfl
      | coe a => exact (hxout (WithTop.coe_le_coe.mpr le_top)).elim
    simp [hxtop]
  · intro hx
    have hxtop : x = (⊤ : WithTop S) := by simpa using hx
    subst x
    change Minimal (fun y : WithTop S => ¬ y ≤ ((⊤ : S) : WithTop S)) ⊤
    refine ⟨?_, ?_⟩
    · exact not_le_of_gt (WithTop.coe_lt_top (⊤ : S))
    · intro y hy hyle
      cases y with
      | top => rfl
      | coe a => exact (hy (WithTop.coe_le_coe.mpr le_top)).elim

/-- Minimal complements at a non-top old element are exactly the old minimal
complements, coerced into `WithTop`. -/
theorem mem_minimalComplement_withTop_coe_iff (p a : S) (hp : p ≠ ⊤) :
    (a : WithTop S) ∈ minimalComplement (p : WithTop S) ↔
      a ∈ minimalComplement p := by
  classical
  constructor
  · intro ha
    change Minimal (fun x : WithTop S => ¬ x ≤ (p : WithTop S)) (a : WithTop S) at ha
    change Minimal (fun x : S => ¬ x ≤ p) a
    refine ⟨?_, ?_⟩
    · simpa only [WithTop.coe_le_coe] using ha.prop
    · intro b hb hba
      have hb' : ¬ (b : WithTop S) ≤ (p : WithTop S) := by
        simpa only [WithTop.coe_le_coe] using hb
      have hba' : (b : WithTop S) ≤ (a : WithTop S) := WithTop.coe_le_coe.mpr hba
      have heq := ha.eq_of_le hb' hba'
      exact (WithTop.coe_injective heq).symm.le
  · intro ha
    change Minimal (fun x : WithTop S => ¬ x ≤ (p : WithTop S)) (a : WithTop S)
    change Minimal (fun x : S => ¬ x ≤ p) a at ha
    refine ⟨?_, ?_⟩
    · simpa only [WithTop.coe_le_coe] using ha.prop
    · intro b hb hba
      cases b with
      | top => exact (not_le_of_gt (WithTop.coe_lt_top a) hba).elim
      | coe b =>
        have hb' : ¬ b ≤ p := by simpa only [WithTop.coe_le_coe] using hb
        have hba' : b ≤ a := WithTop.coe_le_coe.mp hba
        have heq := ha.eq_of_le hb' hba'
        exact WithTop.coe_le_coe.mpr heq.symm.le

/-- Coercing old minimal complements below the old top preserves their
cardinality. -/
private theorem minimalComplement_withTop_coe_ne_top (p : S) (hp : p ≠ ⊤)
    (x : minimalComplement (p : WithTop S)) : x.1 ≠ ⊤ := by
  intro hx
  have hxmem : x.1 ∈ minimalComplement (p : WithTop S) := x.2
  change Minimal (fun y : WithTop S => ¬ y ≤ (p : WithTop S)) x.1 at hxmem
  have htopmem : ¬ ((⊤ : S) : WithTop S) ≤ (p : WithTop S) := by
    intro h
    apply hp
    exact ((WithTop.coe_le_coe.mp h).antisymm le_top).symm
  have hcoetop : ((⊤ : S) : WithTop S) ≤ x.1 := by
    rw [hx]
    exact le_top
  have heq := hxmem.eq_of_le htopmem hcoetop
  have hcoene : ((⊤ : S) : WithTop S) ≠ (⊤ : WithTop S) := by simp
  exact hcoene (by simpa [hx] using heq)

private noncomputable def minimalComplement_withTop_coe_val (p : S) (hp : p ≠ ⊤)
    (x : minimalComplement (p : WithTop S)) : S :=
  x.1.untop (minimalComplement_withTop_coe_ne_top (S := S) p hp x)

private theorem minimalComplement_withTop_coe_val_spec (p : S) (hp : p ≠ ⊤)
    (x : minimalComplement (p : WithTop S)) :
    (minimalComplement_withTop_coe_val (S := S) p hp x : WithTop S) = x.1 :=
  WithTop.coe_untop x.1 (minimalComplement_withTop_coe_ne_top (S := S) p hp x)

/-- Coercion identifies minimal complements below the old top with the
original minimal complements. -/
noncomputable def minimalComplement_withTop_coe_equiv (p : S) (hp : p ≠ ⊤) :
    minimalComplement (p : WithTop S) ≃ minimalComplement p where
  toFun x := by
    have hcoe := minimalComplement_withTop_coe_val_spec (S := S) p hp x
    have hxcoe :
        (minimalComplement_withTop_coe_val (S := S) p hp x : WithTop S) ∈
          minimalComplement (p : WithTop S) := by
      rw [hcoe]
      exact x.2
    exact ⟨minimalComplement_withTop_coe_val (S := S) p hp x,
      (mem_minimalComplement_withTop_coe_iff (S := S) p _ hp).mp hxcoe⟩
  invFun x := ⟨(x.1 : WithTop S),
    (mem_minimalComplement_withTop_coe_iff (S := S) p x.1 hp).mpr x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact minimalComplement_withTop_coe_val_spec (S := S) p hp x
  right_inv x := by
    apply Subtype.ext
    apply WithTop.coe_injective
    have h := minimalComplement_withTop_coe_val_spec (S := S) p hp
      (⟨(x.1 : WithTop S),
        (mem_minimalComplement_withTop_coe_iff (S := S) p x.1 hp).mpr x.2⟩)
    simpa using h

/-- Adjoining a genuinely new top increases the maximum complement count by
at most the singleton old-top case. -/
theorem maxComplementCard_withTop_le :
    maxComplementCard (S := WithTop S) ≤ max 1 (maxComplementCard (S := S)) := by
  classical
  letI : Fintype (WithTop S) := Fintype.ofFinite (WithTop S)
  unfold maxComplementCard
  apply Finset.sup_le
  intro p hp
  cases p with
  | top =>
      have hzero : complementCard (S := WithTop S) (⊤ : WithTop S) = 0 :=
        (complementCard_eq_zero_iff (S := WithTop S) _).2 rfl
      rw [hzero]
      exact Nat.zero_le _
  | coe p =>
      by_cases hptop : p = (⊤ : S)
      · subst p
        have hone :
            complementCard (S := WithTop S) ((⊤ : S) : WithTop S) = 1 := by
          simp [complementCard, minimalComplement_withTop_oldTop (S := S)]
        rw [hone]
        exact Nat.le_max_left _ _
      · have hcard :
            complementCard (S := WithTop S) (p : WithTop S) = complementCard (S := S) p := by
          unfold complementCard
          exact Fintype.card_congr
            (minimalComplement_withTop_coe_equiv (S := S) p hptop)
        rw [hcard]
        exact (complementCard_le_maxComplementCard (S := S) p).trans
          (Nat.le_max_right _ _)

end WithTop

section PairPoset

variable {S : Type} [Lattice S] [Finite S] [OrderBot S] [OrderTop S]

local instance : Fintype S := Fintype.ofFinite S
local instance : Fintype (WithTop S) := Fintype.ofFinite (WithTop S)

/-- The coordinatewise lattice structure on the existing comparable-pair
subtype. -/
@[instance_reducible]
def pairPosetLattice : Lattice (PairPoset S) :=
  Subtype.lattice (fun {_ _} ha hb => sup_le_sup ha hb)
    (fun {_ _} ha hb => inf_le_inf ha hb)

/-- The diagonal endpoints give the existing comparable-pair subtype its
bounded-order structure. -/
@[instance_reducible]
def pairPosetBoundedOrder : BoundedOrder (PairPoset S) :=
  Subtype.boundedOrder (by simp) (by simp)

local instance : Lattice (PairPoset S) := pairPosetLattice (S := S)
local instance : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
local instance : Fintype (PairPoset S) := Fintype.ofFinite (PairPoset S)

/-- The diagonal interval pair associated to an element of `WithTop S`. -/
def diagonalPair (a : WithTop S) : PairPoset S := ⟨(a, a), le_rfl⟩

/-- The interval pair with bottom first coordinate. -/
def bottomPair (b : WithTop S) : PairPoset S := ⟨(⊥, b), bot_le⟩

/-- The diagonal part of the minimal complement at an interval pair, with the
admissibility condition that its coordinate is below the interval's upper
endpoint. -/
def diagonalPairComplement (p : PairPoset S) :=
  {a : minimalComplement p.val.1 // (a.1 : WithTop S) ≤ p.val.2}

/-- The finite enumeration on the restricted diagonal complement family. -/
noncomputable def diagonalPairComplementFintype (p : PairPoset S) :
    Fintype (diagonalPairComplement p) :=
  by
    classical
    exact Fintype.subtype
      (Finset.univ.filter fun a : minimalComplement p.val.1 => a.1 ≤ p.val.2)
      (by intro a; simp)

local instance (p : PairPoset S) : Fintype (diagonalPairComplement p) :=
  diagonalPairComplementFintype (S := S) p

/-- Minimal complements in the actual interval-pair subtype are exactly the
restricted diagonal family and the bottom-first-coordinate family. -/
theorem mem_minimalComplement_pair_iff (p x : PairPoset S) :
    x ∈ minimalComplement p ↔
      (∃ a : minimalComplement p.val.1,
        (a.1 : WithTop S) ≤ p.val.2 ∧ x.val.1 = a.1 ∧ x.val.2 = a.1) ∨
      (∃ b : minimalComplement p.val.2, x.val.1 = ⊥ ∧ x.val.2 = b.1) := by
  classical
  constructor
  · intro hx
    change Minimal (fun z : PairPoset S => ¬ z ≤ p) x at hx
    let a := x.val.1
    let b := x.val.2
    let j := p.val.1
    let k := p.val.2
    have hnot : ¬ (a ≤ j ∧ b ≤ k) := by
      intro hab
      apply hx.prop
      change x.val ≤ p.val
      exact Prod.mk_le_mk.mpr (by simpa [a, b, j, k] using hab)
    by_cases haj : a ≤ j
    · have hbk : ¬ b ≤ k := by
        intro hbk
        exact hnot ⟨haj, hbk⟩
      let q := bottomPair (S := S) b
      have hqout : ¬ q ≤ p := by
        intro hq
        change q.val ≤ p.val at hq
        exact hbk (Prod.mk_le_mk.mp hq).2
      have hqx : q ≤ x := by
        change q.val ≤ x.val
        exact Prod.mk_le_mk.mpr ⟨bot_le, le_rfl⟩
      have hqx' : q = x := hx.eq_of_le hqout hqx
      have hbmin : b ∈ minimalComplement k := by
        change Minimal (fun c : WithTop S => ¬ c ≤ k) b
        refine ⟨hbk, ?_⟩
        intro c hc hcb
        let qc := bottomPair (S := S) c
        have hqcout : ¬ qc ≤ p := by
          intro hqc
          change qc.val ≤ p.val at hqc
          exact hc (Prod.mk_le_mk.mp hqc).2
        have hqcx : qc ≤ x := by
          apply le_trans (show qc ≤ q from ?_) hqx
          change qc.val ≤ q.val
          exact Prod.mk_le_mk.mpr ⟨bot_le, hcb⟩
        have heq : qc = x := hx.eq_of_le hqcout hqcx
        have hc_x := congrArg (fun r : PairPoset S => r.val.2) heq
        have hb_x := congrArg (fun r : PairPoset S => r.val.2) hqx'
        exact (hc_x.trans hb_x.symm).symm.le
      have hfirst := congrArg (fun r : PairPoset S => r.val.1) hqx'
      have hsecond := congrArg (fun r : PairPoset S => r.val.2) hqx'
      exact Or.inr ⟨⟨b, hbmin⟩, hfirst.symm, hsecond.symm⟩
    · have hdiagout : ¬ diagonalPair (S := S) a ≤ p := by
        intro hdiag
        change (a, a) ≤ p.val at hdiag
        exact haj (Prod.mk_le_mk.mp hdiag).1
      have hdiagx : diagonalPair (S := S) a ≤ x := by
        change (a, a) ≤ x.val
        exact Prod.mk_le_mk.mpr ⟨le_rfl, x.property⟩
      have hdiag_eq : diagonalPair (S := S) a = x := hx.eq_of_le hdiagout hdiagx
      have hak : a ≤ k := by
        by_contra hak
        let q := bottomPair (S := S) a
        have hqout : ¬ q ≤ p := by
          intro hq
          change q.val ≤ p.val at hq
          exact hak (Prod.mk_le_mk.mp hq).2
        have hqx : q ≤ x := by
          change q.val ≤ x.val
          exact Prod.mk_le_mk.mpr ⟨bot_le, x.property⟩
        have hq_eq : q = x := hx.eq_of_le hqout hqx
        have hfirst := congrArg (fun r : PairPoset S => r.val.1) hq_eq
        have haeq : (⊥ : WithTop S) = a := by simpa [q, bottomPair] using hfirst
        exact haj (haeq ▸ (bot_le : (⊥ : WithTop S) ≤ j))
      have hamin : a ∈ minimalComplement j := by
        change Minimal (fun c : WithTop S => ¬ c ≤ j) a
        refine ⟨haj, ?_⟩
        intro c hc hca
        let qc := diagonalPair (S := S) c
        have hqcout : ¬ qc ≤ p := by
          intro hqc
          change qc.val ≤ p.val at hqc
          exact hc (Prod.mk_le_mk.mp hqc).1
        have hqcx : qc ≤ x := by
          change qc.val ≤ x.val
          exact Prod.mk_le_mk.mpr ⟨hca, hca.trans x.property⟩
        have heq : qc = x := hx.eq_of_le hqcout hqcx
        have hc_a := congrArg (fun r : PairPoset S => r.val.1) heq
        exact hc_a.symm.le
      have hfirst := congrArg (fun r : PairPoset S => r.val.1) hdiag_eq.symm
      have hsecond := congrArg (fun r : PairPoset S => r.val.2) hdiag_eq.symm
      exact Or.inl ⟨⟨a, hamin⟩, hak, hfirst, hsecond⟩
  · rintro (⟨a, hak, hfirst, hsecond⟩ | ⟨b, hfirst, hsecond⟩)
    · have hx : x = diagonalPair (S := S) a.1 := by
        apply Subtype.ext
        exact Prod.ext hfirst hsecond
      subst x
      change Minimal (fun z : PairPoset S => ¬ z ≤ p) (diagonalPair (S := S) a.1)
      have hamin : Minimal (fun c : WithTop S => ¬ c ≤ p.val.1) a.1 := by
        change Minimal (fun c : WithTop S => ¬ c ≤ p.val.1) a.1
        exact a.2
      refine ⟨?_, ?_⟩
      · intro hle
        exact hamin.prop ((Prod.mk_le_mk.mp (show (a.1, a.1) ≤ p.val from hle)).1)
      · intro q hq hqa
        have hqa' := hqa
        change q.val ≤ (a.1, a.1) at hqa'
        have hqle := Prod.mk_le_mk.mp hqa'
        have hqsecond : q.val.2 ≤ p.val.2 := hqle.2.trans hak
        have hqfirst : ¬ q.val.1 ≤ p.val.1 := by
          intro hqj
          exact hq (Prod.mk_le_mk.mpr ⟨hqj, hqsecond⟩)
        have hfirst : q.val.1 = a.1 := hamin.eq_of_le hqfirst hqle.1
        have hsecond : q.val.2 = a.1 := by
          apply le_antisymm hqle.2
          exact hfirst.symm.le.trans q.property
        have hqeq : q = diagonalPair (S := S) a.1 := by
          apply Subtype.ext
          exact Prod.ext hfirst hsecond
        exact hqeq.symm.le
    · have hx : x = bottomPair (S := S) b.1 := by
        apply Subtype.ext
        exact Prod.ext hfirst hsecond
      subst x
      change Minimal (fun z : PairPoset S => ¬ z ≤ p) (bottomPair (S := S) b.1)
      have hbmin : Minimal (fun c : WithTop S => ¬ c ≤ p.val.2) b.1 := by
        change Minimal (fun c : WithTop S => ¬ c ≤ p.val.2) b.1
        exact b.2
      refine ⟨?_, ?_⟩
      · intro hle
        exact hbmin.prop ((Prod.mk_le_mk.mp (show (⊥, b.1) ≤ p.val from hle)).2)
      · intro q hq hqb
        have hqb' := hqb
        change q.val ≤ (⊥, b.1) at hqb'
        have hqle := Prod.mk_le_mk.mp hqb'
        have hfirst : q.val.1 = ⊥ := le_antisymm hqle.1 bot_le
        have hqsecond : ¬ q.val.2 ≤ p.val.2 := by
          intro hqk
          exact hq (Prod.mk_le_mk.mpr ⟨by simpa [hfirst] using (bot_le : (⊥ : WithTop S) ≤ p.val.1), hqk⟩)
        have hsecond : q.val.2 = b.1 := hbmin.eq_of_le hqsecond hqle.2
        have hqeq : q = bottomPair (S := S) b.1 := by
          apply Subtype.ext
          exact Prod.ext hfirst hsecond
        exact hqeq.symm.le

private theorem pair_bottom_witness (p : PairPoset S)
    (x : minimalComplement p) (h : x.1.val.1 ≤ p.val.1) :
    ∃ b : minimalComplement p.val.2, x.1 = bottomPair (S := S) b.1 := by
  rcases (mem_minimalComplement_pair_iff p x.1).mp x.2 with hdiag | hbottom
  · rcases hdiag with ⟨a, hrest⟩
    have hfirst := hrest.2.1
    have hle : a.1 ≤ p.val.1 := hfirst ▸ h
    have hamin : Minimal (fun c : WithTop S => ¬ c ≤ p.val.1) a.1 := a.2
    exact (hamin.prop hle).elim
  · rcases hbottom with ⟨b, hrest⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    exact Prod.ext hrest.1 hrest.2

private theorem pair_diagonal_witness (p : PairPoset S)
    (x : minimalComplement p) (h : ¬ x.1.val.1 ≤ p.val.1) :
    ∃ a : diagonalPairComplement p, x.1 = diagonalPair (S := S) a.1.1 := by
  rcases (mem_minimalComplement_pair_iff p x.1).mp x.2 with hdiag | hbottom
  · rcases hdiag with ⟨a, hrest⟩
    have hak := hrest.1
    have hfirst := hrest.2.1
    have hsecond := hrest.2.2
    refine ⟨⟨a, hak⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext hfirst hsecond
  · rcases hbottom with ⟨b, hrest⟩
    have hfirst := hrest.1
    have hle : x.1.val.1 ≤ p.val.1 := hfirst ▸ (bot_le : (⊥ : WithTop S) ≤ p.val.1)
    exact (h hle).elim

private noncomputable def pairBottomWitness (p : PairPoset S)
    (x : minimalComplement p) (h : x.1.val.1 ≤ p.val.1) :
    minimalComplement p.val.2 := Classical.choose (pair_bottom_witness p x h)

private theorem pairBottomWitness_spec (p : PairPoset S)
    (x : minimalComplement p) (h : x.1.val.1 ≤ p.val.1) :
    x.1 = bottomPair (S := S) (pairBottomWitness p x h).1 :=
  Classical.choose_spec (pair_bottom_witness p x h)

private noncomputable def pairDiagonalWitness (p : PairPoset S)
    (x : minimalComplement p) (h : ¬ x.1.val.1 ≤ p.val.1) :
    diagonalPairComplement p := Classical.choose (pair_diagonal_witness p x h)

private theorem pairDiagonalWitness_spec (p : PairPoset S)
    (x : minimalComplement p) (h : ¬ x.1.val.1 ≤ p.val.1) :
    x.1 = diagonalPair (S := S) (pairDiagonalWitness p x h).1.1 :=
  Classical.choose_spec (pair_diagonal_witness p x h)

/-- Encode a pair-poset minimal complement by its unique diagonal or
bottom-first-coordinate family. -/
noncomputable def pairComplementEncode (p : PairPoset S) :
    minimalComplement p → diagonalPairComplement p ⊕ minimalComplement p.val.2 := by
  classical
  exact fun x => if h : x.1.val.1 ≤ p.val.1 then
    Sum.inr (pairBottomWitness p x h)
  else Sum.inl (pairDiagonalWitness p x h)

/-- Decode a restricted diagonal or bottom-first-coordinate complement. -/
noncomputable def pairComplementDecode (p : PairPoset S) :
    diagonalPairComplement p ⊕ minimalComplement p.val.2 → minimalComplement p
  | .inl a =>
      ⟨diagonalPair (S := S) a.1.1,
        (mem_minimalComplement_pair_iff p _).2 (Or.inl ⟨a.1, a.2, rfl, rfl⟩)⟩
  | .inr b =>
      ⟨bottomPair (S := S) b.1,
        (mem_minimalComplement_pair_iff p _).2 (Or.inr ⟨b, rfl, rfl⟩)⟩

/-- Exact equivalence between pair-poset complements and the two admissible
families. -/
noncomputable def minimalComplement_pair_equiv (p : PairPoset S) :
    minimalComplement p ≃ diagonalPairComplement p ⊕ minimalComplement p.val.2 where
  toFun := pairComplementEncode p
  invFun := pairComplementDecode p
  left_inv x := by
    classical
    change pairComplementDecode p (pairComplementEncode p x) = x
    simp only [pairComplementEncode]
    split_ifs with h
    · apply Subtype.ext
      simp only [pairComplementDecode]
      exact (pairBottomWitness_spec p x h).symm
    · apply Subtype.ext
      simp only [pairComplementDecode]
      exact (pairDiagonalWitness_spec p x h).symm
  right_inv x := by
    cases x with
    | inl a =>
        classical
        let q := pairComplementDecode p (Sum.inl a)
        have hamin : Minimal (fun c : WithTop S => ¬ c ≤ p.val.1) a.1.1 := a.1.2
        have hnot : ¬ q.1.val.1 ≤ p.val.1 := by
          simpa [q, pairComplementDecode, diagonalPair] using hamin.prop
        have hs := pairDiagonalWitness_spec p q hnot
        have hdiag : pairDiagonalWitness p q hnot = a := by
          apply Subtype.ext
          apply Subtype.ext
          have hfirst := congrArg (fun r : PairPoset S => r.val.1) hs
          simpa [q, pairComplementDecode, diagonalPair] using hfirst.symm
        change pairComplementEncode p q = Sum.inl a
        unfold pairComplementEncode
        rw [dif_neg hnot]
        exact congrArg Sum.inl hdiag
    | inr b =>
        classical
        let q := pairComplementDecode p (Sum.inr b)
        have hbot : q.1.val.1 ≤ p.val.1 := by
          simp [q, pairComplementDecode, bottomPair]
        have hs := pairBottomWitness_spec p q hbot
        have hbottom : pairBottomWitness p q hbot = b := by
          apply Subtype.ext
          have hsecond := congrArg (fun r : PairPoset S => r.val.2) hs
          simpa [q, pairComplementDecode, bottomPair] using hsecond.symm
        change pairComplementEncode p q = Sum.inr b
        unfold pairComplementEncode
        rw [dif_pos hbot]
        exact congrArg Sum.inr hbottom

/-- The exact pair-poset complement count is the sum of the restricted
diagonal family and the bottom-first-coordinate family. -/
theorem complementCard_pair_eq (p : PairPoset S) :
    complementCard (S := PairPoset S) p =
      Fintype.card (diagonalPairComplement p) +
        complementCard (S := WithTop S) p.val.2 := by
  unfold complementCard
  rw [Fintype.card_congr (minimalComplement_pair_equiv (S := S) p)]
  simp [Fintype.card_sum, complementCard]

/-- The restricted diagonal family is bounded by the full first-coordinate
minimal complement. -/
theorem diagonalPairComplement_card_le (p : PairPoset S) :
    Fintype.card (diagonalPairComplement p) ≤ complementCard (S := WithTop S) p.val.1 := by
  unfold complementCard
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- Pointwise, the pair-poset complement count is bounded by the sum of the
two coordinate counts. -/
theorem complementCard_pair_le_add (p : PairPoset S) :
    complementCard (S := PairPoset S) p ≤
      complementCard (S := WithTop S) p.val.1 +
        complementCard (S := WithTop S) p.val.2 := by
  rw [complementCard_pair_eq]
  exact Nat.add_le_add_right (diagonalPairComplement_card_le p) _

/-- The pair-poset maximum is at most twice the corrected WithTop maximum. -/
theorem maxComplementCard_pair_le :
    maxComplementCard (S := PairPoset S) ≤
      2 * max 1 (maxComplementCard (S := S)) := by
  unfold maxComplementCard
  apply Finset.sup_le
  intro p hp
  have hfirst : complementCard (S := WithTop S) p.val.1 ≤
      max 1 (maxComplementCard (S := S)) := by
    exact (complementCard_le_maxComplementCard (S := WithTop S) p.val.1).trans
      (maxComplementCard_withTop_le (S := S))
  have hsecond : complementCard (S := WithTop S) p.val.2 ≤
      max 1 (maxComplementCard (S := S)) := by
    exact (complementCard_le_maxComplementCard (S := WithTop S) p.val.2).trans
      (maxComplementCard_withTop_le (S := S))
  calc
    complementCard p ≤
        complementCard (S := WithTop S) p.val.1 +
          complementCard (S := WithTop S) p.val.2 := complementCard_pair_le_add p
    _ ≤ max 1 (maxComplementCard (S := S)) +
          max 1 (maxComplementCard (S := S)) := Nat.add_le_add hfirst hsecond
    _ = 2 * max 1 (maxComplementCard (S := S)) := by omega

end PairPoset

section CoordinateGrid

variable {n : ℕ} (G : CoordinateGrid n)

/-- The chosen finite endpoints on a nonempty-factor coordinate grid. -/
@[instance_reducible]
noncomputable def coordinateGridBoundedOrder
    (hG : ∀ i : Fin n, (G i).Nonempty) : BoundedOrder G.Point := by
  classical
  letI : Nonempty G.Point := ⟨fun i =>
    ⟨Classical.choose (hG i), (Classical.choose_spec (hG i))⟩⟩
  exact Fintype.toBoundedOrder G.Point

/-- The finite product of nonempty coordinate sets has at most one minimal
complement generator per coordinate. -/
theorem maxComplementCard_coordinateGrid_le
    (hG : ∀ i : Fin n, (G i).Nonempty) :
    letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
    maxComplementCard (S := G.Point) ≤ n := by
  classical
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  letI (i : Fin n) : Fintype {x : ℝ // x ∈ G i} := Fintype.ofFinite _
  letI (i : Fin n) : Nonempty {x : ℝ // x ∈ G i} := by
    obtain ⟨x, hx⟩ := hG i
    exact ⟨⟨x, hx⟩⟩
  letI (i : Fin n) : OrderBot {x : ℝ // x ∈ G i} := Fintype.toOrderBot _
  letI (i : Fin n) : OrderTop {x : ℝ // x ∈ G i} := Fintype.toOrderTop _
  simpa [CoordinateGrid.Point] using
    (maxComplementCard_pi_le_card (ι := Fin n)
      (T := fun i => {x : ℝ // x ∈ G i}))

/-- For a nonempty-factor coordinate grid, adjoining the new top has at most
`n` complement generators when `n` is positive. -/
theorem maxComplementCard_withTop_coordinateGrid_le (hn : 1 ≤ n)
    (hG : ∀ i : Fin n, (G i).Nonempty) :
    letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
    maxComplementCard (S := WithTop G.Point) ≤ n := by
  classical
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  letI (i : Fin n) : Fintype {x : ℝ // x ∈ G i} := Fintype.ofFinite _
  letI (i : Fin n) : Nonempty {x : ℝ // x ∈ G i} := by
    obtain ⟨x, hx⟩ := hG i
    exact ⟨⟨x, hx⟩⟩
  letI (i : Fin n) : OrderBot {x : ℝ // x ∈ G i} := Fintype.toOrderBot _
  letI (i : Fin n) : OrderTop {x : ℝ // x ∈ G i} := Fintype.toOrderTop _
  have hgrid := maxComplementCard_coordinateGrid_le G hG
  exact (maxComplementCard_withTop_le (S := G.Point)).trans
    (max_le_iff.mpr ⟨hn, hgrid⟩)

/-- For a nonempty-factor coordinate grid, its actual interval-pair poset has
at most `2*n` complement generators when `n` is positive. -/
theorem maxComplementCard_pair_coordinateGrid_le (hn : 1 ≤ n)
    (hG : ∀ i : Fin n, (G i).Nonempty) :
    letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
    letI : Lattice (PairPoset G.Point) := pairPosetLattice (S := G.Point)
    letI : BoundedOrder (PairPoset G.Point) :=
      pairPosetBoundedOrder (S := G.Point)
    maxComplementCard (S := PairPoset G.Point) ≤ 2 * n := by
  classical
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  letI (i : Fin n) : Fintype {x : ℝ // x ∈ G i} := Fintype.ofFinite _
  letI (i : Fin n) : Nonempty {x : ℝ // x ∈ G i} := by
    obtain ⟨x, hx⟩ := hG i
    exact ⟨⟨x, hx⟩⟩
  letI (i : Fin n) : OrderBot {x : ℝ // x ∈ G i} := Fintype.toOrderBot _
  letI (i : Fin n) : OrderTop {x : ℝ // x ∈ G i} := Fintype.toOrderTop _
  letI : Lattice (PairPoset G.Point) := pairPosetLattice (S := G.Point)
  letI : BoundedOrder (PairPoset G.Point) := pairPosetBoundedOrder (S := G.Point)
  have hgrid := maxComplementCard_coordinateGrid_le G hG
  exact (maxComplementCard_pair_le (S := G.Point)).trans
    (Nat.mul_le_mul_left 2 (max_le_iff.mpr ⟨hn, hgrid⟩))

end CoordinateGrid


end

end TDA.Persistence.FiniteLatticeComplementCardinality
