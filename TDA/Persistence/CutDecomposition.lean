import TDA.Persistence.CutSubspaces
import Mathlib.LinearAlgebra.DFinsupp
import TDA.Persistence.AlgebraicFamily

/-!
# Internal decomposition by real cut intervals

For an arbitrary pointwise finite-dimensional real-indexed persistence module,
all chosen interval complements span each fiber and have independent finite
relations. The resulting algebraic direct sum is naturally isomorphic to the
original module. The interval index may be uncountable and includes singletons.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.CutDecomposition

open TDA.Persistence
open TDA.Persistence.Cut

variable {k : Type u} [Field k] {α : Type v} [LinearOrder α]
  (M : PModule.{u,v,w} k α)

/-- Turn a downward-closed predicate into a cut. -/
private def ofInitial (P : α → Prop)
    (hP : ∀ ⦃a b⦄, a ≤ b → P b → P a) : Cut α where
  lower := {a | P a}
  upper := {a | ¬ P a}
  mem_lower_or_upper a := em (P a)
  lower_lt_upper := by
    intro a b ha hb
    exact lt_of_le_of_ne (le_total a b |>.resolve_right
      (fun hba => hb (hP hba ha))) (fun hab => hb (hab ▸ ha))

/-- The maximal birth cut allowed by a candidate proper subspace. -/
private def birthCut (t : α) (W : Submodule k (M.obj t)) : Cut α :=
  ofInitial (fun s => ∃ h : s ≤ t, LinearMap.range (structureMapLinear M h) ≤ W) (by
    intro a b hab ⟨hbt, hW⟩
    refine ⟨hab.trans hbt, ?_⟩
    intro x hx
    obtain ⟨y, hy⟩ := hx
    apply hW
    refine ⟨structureMapLinear M hab y, ?_⟩
    rw [← hy]
    exact (LinearMap.congr_fun (structureMapLinear_comp M hab hbt) y).symm)

private theorem birthCut_upper_at (t : α) (W : Submodule k (M.obj t))
    (hW : W ≠ ⊤) : t ∈ (birthCut M t W).upper := by
  change ¬ ∃ h : t ≤ t, LinearMap.range (structureMapLinear M h) ≤ W
  rintro ⟨h, hh⟩
  have hr : LinearMap.range (structureMapLinear M h) = ⊤ := by
    rw [structureMapLinear_self M h, LinearMap.range_id]
  exact hW (top_le_iff.mp (hr ▸ hh))

private theorem birth_imageMinus_le (t : α) (W : Submodule k (M.obj t)) :
    imageMinus M (birthCut M t W) t ≤ W := by
  apply iSup_le
  intro s
  obtain ⟨h, hh⟩ := s.property.1
  exact hh

private theorem birth_imagePlus_not_le (t : α) [FiniteDimensional k (M.obj t)]
    (W : Submodule k (M.obj t)) (hW : W ≠ ⊤) :
    ¬ imagePlus M (birthCut M t W) t ≤ W := by
  obtain ⟨s, hs⟩ := imagePlus_eq_range M (birthCut M t W) (birthCut_upper_at M t W hW)
  intro h
  have hsW : LinearMap.range (structureMapLinear M s.property.2) ≤ W := hs ▸ h
  exact s.property.1 ⟨s.property.2, hsW⟩

/-- The maximal death cut whose lower kernels do not escape `W` after intersecting `B`. -/
private def deathCut (t : α) (B W : Submodule k (M.obj t)) : Cut α :=
  ofInitial (fun r => r < t ∨
    ∃ h : t ≤ r, B ⊓ LinearMap.ker (structureMapLinear M h) ≤ W) (by
    intro a b hab hb
    rcases hb with hbt | ⟨htb, hW⟩
    · exact Or.inl (lt_of_le_of_lt hab hbt)
    · rcases lt_or_ge a t with hat | hta
      · exact Or.inl hat
      · right
        refine ⟨hta, ?_⟩
        have hker : LinearMap.ker (structureMapLinear M hta) ≤
            LinearMap.ker (structureMapLinear M htb) := by
          intro x hx
          change structureMapLinear M htb x = 0
          rw [show htb = hta.trans hab from Subsingleton.elim _ _,
            structureMapLinear_comp M hta hab, LinearMap.comp_apply,
            LinearMap.mem_ker.mp hx, map_zero]
        exact (inf_le_inf_left B hker).trans hW)

private theorem deathCut_lower_at (t : α) (B W : Submodule k (M.obj t)) :
    t ∈ (deathCut M t B W).lower := by
  change t < t ∨ ∃ h : t ≤ t, B ⊓ LinearMap.ker (structureMapLinear M h) ≤ W
  right
  refine ⟨le_rfl, ?_⟩
  rw [structureMapLinear_self M (le_refl t), LinearMap.ker_id]
  exact (inf_le_right : B ⊓ ⊥ ≤ ⊥).trans bot_le

private theorem death_kernelMinus_le (t : α) (B W : Submodule k (M.obj t)) :
    B ⊓ kernelMinus M (deathCut M t B W) t ≤ W := by
  intro x hx
  obtain ⟨r, hr⟩ := (mem_kernelMinus_iff M (deathCut M t B W)
    (deathCut_lower_at M t B W)).mp hx.2
  have hgood : ∃ h : t ≤ r.val,
      B ⊓ LinearMap.ker (structureMapLinear M h) ≤ W := by
    rcases r.property.1 with hrt | hgood
    · exact False.elim ((not_lt_of_ge r.property.2) hrt)
    · exact hgood
  obtain ⟨h, hW⟩ := hgood
  have : h = r.property.2 := Subsingleton.elim _ _
  subst h
  exact hW ⟨hx.1, hr⟩

private theorem death_kernelPlus_not_le (t : α) [FiniteDimensional k (M.obj t)]
    (B W : Submodule k (M.obj t)) (hB : ¬ B ≤ W) :
    ¬ B ⊓ kernelPlus M (deathCut M t B W) t ≤ W := by
  intro h
  by_cases hne : ∃ r ∈ (deathCut M t B W).upper, t ≤ r
  · obtain ⟨r, hr⟩ := kernelPlus_eq_kernel M (deathCut M t B W) hne
    have hgood : ∃ htr : t ≤ r.val,
        B ⊓ LinearMap.ker (structureMapLinear M htr) ≤ W :=
      ⟨r.property.2, hr ▸ h⟩
    exact r.property.1 (Or.inr hgood)
  · have hk : kernelPlus M (deathCut M t B W) t = ⊤ := by
      apply top_unique
      intro x hx
      change x ∈ ⨅ r : {r // r ∈ (deathCut M t B W).upper ∧ t ≤ r},
        LinearMap.ker (structureMapLinear M r.property.2)
      rw [Submodule.mem_iInf]
      intro r
      exact False.elim (hne ⟨r.val, r.property.1, r.property.2⟩)
    exact hB (by simpa [hk] using h)

/-- Every proper fiber subspace misses one interval quotient. -/
theorem exists_interval_escapes (t : α) [FiniteDimensional k (M.obj t)]
    (W : Submodule k (M.obj t)) (hW : W ≠ ⊤) :
    ∃ l r : Cut α, t ∈ support l r ∧
      intervalMinus M l r t ≤ W ∧ ¬ intervalPlus M l r t ≤ W := by
  let l := birthCut M t W
  let B := imagePlus M l t
  let r := deathCut M t B W
  refine ⟨l, r, ⟨birthCut_upper_at M t W hW,
    deathCut_lower_at M t B W⟩, ?_, ?_⟩
  · change (imageMinus M l t ⊓ kernelPlus M r t) ⊔
      (imagePlus M l t ⊓ kernelMinus M r t) ≤ W
    exact sup_le (inf_le_left.trans (birth_imageMinus_le M t W))
      (death_kernelMinus_le M t B W)
  · exact death_kernelPlus_not_le M t B W (birth_imagePlus_not_le M t W hW)

/-- A local complement escapes every subspace containing the interval-minus
space but not the interval-plus space. -/
private theorem complement_escapes (l r : Cut α) (t : α)
    (D : Submodule k (intervalPlus M l r t))
    (hD : IsCompl (intervalMinusInPlus M l r t) D)
    (W : Submodule k (M.obj t))
    (hminus : intervalMinus M l r t ≤ W)
    (hplus : ¬ intervalPlus M l r t ≤ W) :
    ¬ D.map (intervalPlus M l r t).subtype ≤ W := by
  intro hDW
  apply hplus
  intro x hx
  have hmem : (⟨x, hx⟩ : intervalPlus M l r t) ∈
      intervalMinusInPlus M l r t ⊔ D := by
    rw [hD.codisjoint.eq_top]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  have haW : (a : M.obj t) ∈ W := hminus ha
  have hbW : (b : M.obj t) ∈ W := hDW ⟨b, hb, rfl⟩
  have hab' := congrArg Subtype.val hab
  change (a : M.obj t) + b = x at hab'
  exact hab' ▸ W.add_mem haW hbW

/-- Index each nonempty cut interval once, including singleton supports. -/
abbrev IntervalIndex : Type :=
  { p : Cut ℝ × Cut ℝ // (support p.1 p.2).Nonempty }

noncomputable def anchor (i : IntervalIndex) :
    support i.val.1 i.val.2 :=
  ⟨Classical.choose i.property, Classical.choose_spec i.property⟩

noncomputable def chosenFiber (M : PModule.{u,0,w} k ℝ)
    (t : ℝ) (i : IntervalIndex) : Submodule k (M.obj t) :=
  sectionComplementFiber M i.val.1 i.val.2 (anchor i) t

private theorem chosenFiber_escapes_real
    (M : PModule.{u,0,w} k ℝ) [∀ t, FiniteDimensional k (M.obj t)]
    (t : ℝ) (W : Submodule k (M.obj t)) (hW : W ≠ ⊤) :
    ∃ i : IntervalIndex, ¬ chosenFiber M t i ≤ W := by
  obtain ⟨l, r, ht, hminus, hplus⟩ := exists_interval_escapes M t W hW
  let i : IntervalIndex := ⟨(l, r), ⟨t, ht⟩⟩
  refine ⟨i, ?_⟩
  have h := complement_escapes M l r t
    (sectionComplementAt M l r (anchor i) ⟨t, ht⟩)
    (isCompl_sectionComplementAt_real M l r (anchor i) ⟨t, ht⟩)
    W hminus hplus
  change ¬ sectionComplementFiber M l r (anchor i) t ≤ W
  simpa only [sectionComplementFiber, dif_pos ht] using h

theorem chosenFiber_iSup_eq_top_real
    (M : PModule.{u,0,w} k ℝ) [∀ t, FiniteDimensional k (M.obj t)]
    (t : ℝ) : (⨆ i : IntervalIndex, chosenFiber M t i) = ⊤ := by
  by_contra hne
  obtain ⟨i, hi⟩ := chosenFiber_escapes_real M t
    (⨆ i : IntervalIndex, chosenFiber M t i) hne
  exact hi (le_iSup (chosenFiber M t) i)

/-- A strictly earlier birth image is already in the later birth's minus space. -/
private theorem imagePlus_le_imageMinus_of_birth_lt (l₁ l₂ : Cut α) (t : α)
    (h : l₁.lower ⊂ l₂.lower) (ht : t ∈ l₂.upper) :
    imagePlus M l₁ t ≤ imageMinus M l₂ t := by
  obtain ⟨s, hs₂, hs₁⟩ := Set.exists_of_ssubset h
  have hs₁' : s ∈ l₁.upper := (l₁.mem_lower_or_upper s).resolve_left hs₁
  have hst : s ≤ t := (l₂.lower_lt_upper hs₂ ht).le
  exact (iInf_le (fun s : {s // s ∈ l₁.upper ∧ s ≤ t} =>
      LinearMap.range (structureMapLinear M s.property.2)) ⟨s, hs₁', hst⟩).trans
    (le_iSup (fun s : {s // s ∈ l₂.lower ∧ s ≤ t} =>
      LinearMap.range (structureMapLinear M s.property.2)) ⟨s, hs₂, hst⟩)

/-- A strictly earlier death kernel is already in the later death's minus space. -/
private theorem kernelPlus_le_kernelMinus_of_death_lt (r₁ r₂ : Cut α) (t : α)
    (h : r₁.lower ⊂ r₂.lower) (ht : t ∈ r₁.lower) :
    kernelPlus M r₁ t ≤ kernelMinus M r₂ t := by
  obtain ⟨s, hs₂, hs₁⟩ := Set.exists_of_ssubset h
  have hs₁' : s ∈ r₁.upper := (r₁.mem_lower_or_upper s).resolve_left hs₁
  have hts : t ≤ s := (r₁.lower_lt_upper ht hs₁').le
  exact (iInf_le (fun s : {s // s ∈ r₁.upper ∧ t ≤ s} =>
      LinearMap.ker (structureMapLinear M s.property.2)) ⟨s, hs₁', hts⟩).trans
    (le_iSup (fun s : {s // s ∈ r₂.lower ∧ t ≤ s} =>
      LinearMap.ker (structureMapLinear M s.property.2)) ⟨s, hs₂, hts⟩)

/-- Lower parts of cuts on a linear order are totally ordered by inclusion. -/
private theorem lower_subset_total (c d : Cut α) :
    c.lower ⊆ d.lower ∨ d.lower ⊆ c.lower := by
  by_cases h : c.lower ⊆ d.lower
  · exact Or.inl h
  · right
    obtain ⟨a, hac, had⟩ := Set.not_subset.mp h
    have hau : a ∈ d.upper := (d.mem_lower_or_upper a).resolve_left had
    intro b hbd
    by_contra hbc
    have hbu : b ∈ c.upper := (c.mem_lower_or_upper b).resolve_left hbc
    exact (lt_asymm (c.lower_lt_upper hac hbu) (d.lower_lt_upper hbd hau))

private theorem eq_of_lower_eq (c d : Cut α) (h : c.lower = d.lower) : c = d := by
  have hu : c.upper = d.upper := by
    ext x
    constructor
    · intro hx
      rcases d.mem_lower_or_upper x with hd | hd
      · exact False.elim ((not_mem_upper (h.symm ▸ hd)) hx)
      · exact hd
    · intro hx
      rcases c.mem_lower_or_upper x with hc | hc
      · exact False.elim ((not_mem_upper (h ▸ hc)) hx)
      · exact hc
  cases c
  cases d
  cases h
  cases hu
  rfl

/-- The chosen complement meets interval-minus only at zero. -/
private theorem complement_map_inter_minus_zero (l r : Cut α) (t : α)
    (D : Submodule k (intervalPlus M l r t))
    (hD : IsCompl (intervalMinusInPlus M l r t) D)
    (x : M.obj t) (hxD : x ∈ D.map (intervalPlus M l r t).subtype)
    (hxMinus : x ∈ intervalMinus M l r t) : x = 0 := by
  obtain ⟨y, hyD, rfl⟩ := hxD
  have hyMinus : y ∈ intervalMinusInPlus M l r t := hxMinus
  have hy0 := Submodule.disjoint_def.mp hD.disjoint y hyMinus hyD
  exact congrArg Subtype.val hy0

/-- The algebraic elimination step in a finite relation: `y` collects earlier
births and `z` collects equal-birth, earlier-death terms. -/
private theorem selected_zero_of_relation (l r : Cut α) (t : α)
    (D : Submodule k (intervalPlus M l r t))
    (hD : IsCompl (intervalMinusInPlus M l r t) D)
    (x y z : M.obj t)
    (hxD : x ∈ D.map (intervalPlus M l r t).subtype)
    (hy : y ∈ imageMinus M l t)
    (hzImage : z ∈ imagePlus M l t)
    (hzKernel : z ∈ kernelMinus M r t)
    (hsum : x + y + z = 0) : x = 0 := by
  have hxPlus : x ∈ intervalPlus M l r t := by
    obtain ⟨v, hv, rfl⟩ := hxD
    exact v.property
  have hzPlus : z ∈ kernelPlus M r t :=
    kernelMinus_le_kernelPlus M r t hzKernel
  have hyPlus : y ∈ kernelPlus M r t := by
    have hxyz : y + (x + z) = 0 := by simpa [add_comm, add_left_comm, add_assoc] using hsum
    have heq : y = -(x + z) := eq_neg_of_add_eq_zero_left hxyz
    rw [heq]
    exact (kernelPlus M r t).neg_mem
      ((kernelPlus M r t).add_mem hxPlus.2 hzPlus)
  have hxMinus : x ∈ intervalMinus M l r t := by
    have hyz : y + z ∈ intervalMinus M l r t :=
      (intervalMinus M l r t).add_mem
        (show y ∈ intervalMinus M l r t from
          (le_sup_left : imageMinus M l t ⊓ kernelPlus M r t ≤ intervalMinus M l r t)
            ⟨hy, hyPlus⟩)
        (show z ∈ intervalMinus M l r t from
          (le_sup_right : imagePlus M l t ⊓ kernelMinus M r t ≤ intervalMinus M l r t)
            ⟨hzImage, hzKernel⟩)
    have heq : x = -(y + z) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_assoc] using hsum
    rw [heq]
    exact (intervalMinus M l r t).neg_mem hyz
  exact complement_map_inter_minus_zero M l r t D hD x hxD hxMinus

private theorem chosenFiber_le_intervalPlus_real
    (M : PModule.{u,0,w} k ℝ) (t : ℝ) (i : IntervalIndex) :
    chosenFiber M t i ≤ intervalPlus M i.val.1 i.val.2 t := by
  classical
  intro x hx
  unfold chosenFiber sectionComplementFiber at hx
  split_ifs at hx with hs
  · obtain ⟨y, hy, rfl⟩ := hx
    exact y.property
  · exact (show x = 0 from hx) ▸ (intervalPlus M i.val.1 i.val.2 t).zero_mem

private theorem chosenFiber_nonzero_support_real
    (M : PModule.{u,0,w} k ℝ) (t : ℝ) (i : IntervalIndex)
    (x : M.obj t) (hx : x ∈ chosenFiber M t i) (hne : x ≠ 0) :
    t ∈ support i.val.1 i.val.2 := by
  by_contra ht
  have hz : chosenFiber M t i = ⊥ :=
    sectionComplementFiber_eq_bot M i.val.1 i.val.2 (anchor i) ht
  exact hne (by simpa [hz] using hx)

/-- If an index is maximal first in birth and then among equal births in death,
its coefficient in a finite zero relation vanishes. -/
private theorem maximal_term_zero_real
    (M : PModule.{u,0,w} k ℝ) [∀ t, FiniteDimensional k (M.obj t)]
    (t : ℝ) (s : Finset IntervalIndex) (v : IntervalIndex → M.obj t)
    (hv : ∀ j ∈ s, v j ∈ chosenFiber M t j)
    (hsum : ∑ j ∈ s, v j = 0)
    (i : IntervalIndex) (hi : i ∈ s)
    (hbirth : ∀ j ∈ s, v j ≠ 0 → j.val.1.lower ⊆ i.val.1.lower)
    (hdeath : ∀ j ∈ s, v j ≠ 0 → j.val.1 = i.val.1 →
      j.val.2.lower ⊆ i.val.2.lower) : v i = 0 := by
  classical
  by_contra hvi
  have hti := chosenFiber_nonzero_support_real M t i (v i) (hv i hi) hvi
  let E := (s.erase i).filter (fun j => j.val.1.lower ≠ i.val.1.lower)
  let Z := (s.erase i).filter (fun j => j.val.1.lower = i.val.1.lower)
  have hE : ∑ j ∈ E, v j ∈ imageMinus M i.val.1 t := by
    apply Submodule.sum_mem
    intro j hj
    have hjs : j ∈ s := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).2
    by_cases hj0 : v j = 0
    · rw [hj0]; exact Submodule.zero_mem _
    · have hlt : j.val.1.lower ⊂ i.val.1.lower :=
        lt_of_le_of_ne (hbirth j hjs hj0) (Finset.mem_filter.mp hj).2
      exact imagePlus_le_imageMinus_of_birth_lt M j.val.1 i.val.1 t hlt hti.1
        ((chosenFiber_le_intervalPlus_real M t j) (hv j hjs)).1
  have hZI : ∑ j ∈ Z, v j ∈ imagePlus M i.val.1 t := by
    apply Submodule.sum_mem
    intro j hj
    have hjs : j ∈ s := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).2
    have hbirthEq := eq_of_lower_eq j.val.1 i.val.1 (Finset.mem_filter.mp hj).2
    exact hbirthEq ▸ ((chosenFiber_le_intervalPlus_real M t j) (hv j hjs)).1
  have hZK : ∑ j ∈ Z, v j ∈ kernelMinus M i.val.2 t := by
    apply Submodule.sum_mem
    intro j hj
    have hjs : j ∈ s := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).2
    by_cases hj0 : v j = 0
    · rw [hj0]; exact Submodule.zero_mem _
    · have hbirthEq := eq_of_lower_eq j.val.1 i.val.1 (Finset.mem_filter.mp hj).2
      have hdeathLe := hdeath j hjs hj0 hbirthEq
      have hjne : j ≠ i := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
      have hdeathNe : j.val.2.lower ≠ i.val.2.lower := by
        intro heq
        apply hjne
        apply Subtype.ext
        exact Prod.ext hbirthEq (eq_of_lower_eq j.val.2 i.val.2 heq)
      have hlt : j.val.2.lower ⊂ i.val.2.lower :=
        lt_of_le_of_ne hdeathLe hdeathNe
      have htj := chosenFiber_nonzero_support_real M t j (v j) (hv j hjs) hj0
      exact kernelPlus_le_kernelMinus_of_death_lt M j.val.2 i.val.2 t hlt htj.2
        ((chosenFiber_le_intervalPlus_real M t j) (hv j hjs)).2
  have hsplit : (∑ j ∈ E, v j) + (∑ j ∈ Z, v j) =
      ∑ j ∈ s.erase i, v j := by
    simpa only [E, Z, not_not] using
      (Finset.sum_filter_add_sum_filter_not (s.erase i)
        (fun j : IntervalIndex => j.val.1.lower ≠ i.val.1.lower) v)
  have hsel : v i + (∑ j ∈ E, v j) + (∑ j ∈ Z, v j) = 0 := by
    calc
      _ = v i + ((∑ j ∈ E, v j) + (∑ j ∈ Z, v j)) := by abel
      _ = v i + ∑ j ∈ s.erase i, v j := congrArg (v i + ·) hsplit
      _ = ∑ j ∈ s, v j := Finset.add_sum_erase s v hi
      _ = 0 := hsum
  have hD := isCompl_sectionComplementAt_real M i.val.1 i.val.2 (anchor i) ⟨t, hti⟩
  have hselected := selected_zero_of_relation M i.val.1 i.val.2 t
    (sectionComplementAt M i.val.1 i.val.2 (anchor i) ⟨t, hti⟩)
    hD (v i) (∑ j ∈ E, v j) (∑ j ∈ Z, v j) ?_ hE hZI hZK hsel
  · exact hvi hselected
  · simpa only [chosenFiber, sectionComplementFiber, dif_pos hti] using hv i hi

/-- Distinct chosen cut-interval complements form an internal direct sum at each
fiber. The family may be uncountable. -/
theorem chosenFiber_iSupIndep_real
    (M : PModule.{u,0,w} k ℝ) [∀ t, FiniteDimensional k (M.obj t)]
    (t : ℝ) : iSupIndep (chosenFiber M t) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  by_contra hvi
  let nz := s.filter (fun j => v j ≠ 0)
  have hnz : nz.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hvi⟩⟩
  obtain ⟨b, hb, hbmax⟩ :=
    Finset.exists_maximalFor (fun j : IntervalIndex => j.val.1.lower) nz hnz
  let same := nz.filter (fun j => j.val.1.lower = b.val.1.lower)
  have hsame : same.Nonempty :=
    ⟨b, Finset.mem_filter.mpr ⟨hb, rfl⟩⟩
  obtain ⟨c, hc, hcmax⟩ :=
    Finset.exists_maximalFor (fun j : IntervalIndex => j.val.2.lower) same hsame
  have hcb : c.val.1.lower = b.val.1.lower := (Finset.mem_filter.mp hc).2
  have hcnz : c ∈ nz := (Finset.mem_filter.mp hc).1
  have hbirth : ∀ j ∈ s, v j ≠ 0 → j.val.1.lower ⊆ c.val.1.lower := by
    intro j hj hjne
    have hjnz : j ∈ nz := Finset.mem_filter.mpr ⟨hj, hjne⟩
    rw [hcb]
    rcases lower_subset_total j.val.1 b.val.1 with h | h
    · exact h
    · exact hbmax hjnz h
  have hdeath : ∀ j ∈ s, v j ≠ 0 → j.val.1 = c.val.1 →
      j.val.2.lower ⊆ c.val.2.lower := by
    intro j hj hjne hjbirth
    have hjnz : j ∈ nz := Finset.mem_filter.mpr ⟨hj, hjne⟩
    have hjsame : j ∈ same := Finset.mem_filter.mpr ⟨hjnz, by rw [hjbirth]; exact hcb⟩
    rcases lower_subset_total j.val.2 c.val.2 with h | h
    · exact h
    · exact hcmax hjsame h
  have hcs : c ∈ s := (Finset.mem_filter.mp hcnz).1
  have hc0 := maximal_term_zero_real M t s v hv hsum c hcs hbirth hdeath
  exact (Finset.mem_filter.mp hcnz).2 hc0

open CategoryTheory

private noncomputable instance : DecidableEq IntervalIndex := Classical.decEq _

variable {k : Type u} [Field k]
    (M : PModule.{u,0,u} k ℝ) [∀ t, FiniteDimensional k (M.obj t)]

/-- The interval-supported subfunctor for a chosen nonempty pair of cuts. -/
noncomputable def intervalFamily (i : IntervalIndex) : PModule.{u,0,u} k ℝ :=
  sectionComplementModule M i.val.1 i.val.2 (anchor i)

/-- Assemble the natural inclusions of all chosen interval subfunctors. -/
noncomputable def sumToM :
    AlgebraicFamily.familyModule (intervalFamily M) ⟶ M :=
  AlgebraicFamily.desc (intervalFamily M)
    (fun i => sectionComplementInclusion M i.val.1 i.val.2 (anchor i))

omit [∀ t, FiniteDimensional k (M.obj t)] in
/-- The assembled map is exactly the canonical map from an internal sum of
the chosen fiber subspaces. -/
theorem sumToM_app (t : ℝ) :
    ((sumToM M).app t).hom = DirectSum.coeLinearMap (chosenFiber M t) := by
  classical
  rfl

theorem sumToM_bijective (t : ℝ) :
    Function.Bijective (((sumToM M).app t).hom) := by
  classical
  rw [sumToM_app]
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
    (chosenFiber M t)).mpr
    ⟨chosenFiber_iSupIndep_real M t, chosenFiber_iSup_eq_top_real M t⟩

/-- A genuine natural isomorphism from the algebraic direct sum of cut interval
subfunctors to the original pointwise finite-dimensional module. -/
noncomputable def sumIso :
    AlgebraicFamily.familyModule (intervalFamily M) ≅ M :=
  NatIso.ofComponents
    (fun t => (LinearEquiv.ofBijective (((sumToM M).app t).hom)
      (sumToM_bijective M t)).toModuleIso)
    (fun {_ _} f => (sumToM M).naturality f)

theorem sumIso_hom : (sumIso M).hom = sumToM M := rfl

/-- Each parameter sees only finitely many nonzero interval subfunctors. -/
theorem finite_active (t : ℝ) :
    Set.Finite {i : IntervalIndex | Nontrivial ((intervalFamily M i).obj t)} := by
  exact AlgebraicFamily.finite_nontrivial_of_iso (intervalFamily M) (sumIso M).symm
    (fun s => inferInstance) t

/-- A finite observation list detects only finitely many occurrences. -/
theorem finite_observed {N : ℕ} (c : Fin N → ℝ) :
    Set.Finite {i : IntervalIndex | ∃ n, Nontrivial ((intervalFamily M i).obj (c n))} := by
  exact AlgebraicFamily.finite_observed_nontrivial (intervalFamily M)
    (finite_active M) c

end TDA.Persistence.CutDecomposition
