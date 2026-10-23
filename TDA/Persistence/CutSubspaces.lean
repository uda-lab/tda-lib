import TDA.Persistence.Basic
import TDA.Persistence.CompatibleSections
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Cut subspaces of a persistence module

A cut partitions a linear order into an initial part and a final part. Images from the
initial part and intersections of images from the final part describe birth conditions;
kernels toward the two parts describe death conditions. Finite-dimensional fibers make
the nonempty intersections of nested subspaces attained. In particular, transition maps
between the plus spaces of an interval are surjective.
-/

universe u v w

namespace TDA.Persistence

/-- A partition of a linear order with every lower point strictly below every upper point.
Either part may be empty. -/
structure Cut (α : Type v) [LinearOrder α] where
  lower : Set α
  upper : Set α
  mem_lower_or_upper : ∀ t, t ∈ lower ∨ t ∈ upper
  lower_lt_upper : ∀ {s t}, s ∈ lower → t ∈ upper → s < t

namespace Cut

open CategoryTheory

variable {α : Type v} [LinearOrder α]

/-- A cut has disjoint parts. -/
theorem not_mem_upper {c : Cut α} {t : α} (ht : t ∈ c.lower) : t ∉ c.upper :=
  fun hu => lt_irrefl t (c.lower_lt_upper ht hu)

/-- The lower part is closed downward. -/
theorem lower_of_le {c : Cut α} {s t : α} (hst : s ≤ t)
    (ht : t ∈ c.lower) : s ∈ c.lower := by
  rcases c.mem_lower_or_upper s with hs | hs
  · exact hs
  · exact False.elim ((not_lt_of_ge hst) (c.lower_lt_upper ht hs))

/-- The upper part is closed upward. -/
theorem upper_of_le {c : Cut α} {s t : α} (hst : s ≤ t)
    (hs : s ∈ c.upper) : t ∈ c.upper := by
  rcases c.mem_lower_or_upper t with ht | ht
  · exact False.elim ((not_lt_of_ge hst) (c.lower_lt_upper ht hs))
  · exact ht

variable {k : Type u} [Field k] (M : PModule.{u,v,w} k α)

/-- Images arriving from the lower part of a cut. -/
def imageMinus (c : Cut α) (t : α) : Submodule k (M.obj t) :=
  ⨆ s : {s // s ∈ c.lower ∧ s ≤ t}, LinearMap.range (structureMapLinear M s.property.2)

/-- Images arriving from every upper point at or before `t`. -/
def imagePlus (c : Cut α) (t : α) : Submodule k (M.obj t) :=
  ⨅ s : {s // s ∈ c.upper ∧ s ≤ t}, LinearMap.range (structureMapLinear M s.property.2)

/-- Kernels of maps to the lower part of a cut. -/
def kernelMinus (c : Cut α) (t : α) : Submodule k (M.obj t) :=
  ⨆ r : {r // r ∈ c.lower ∧ t ≤ r}, LinearMap.ker (structureMapLinear M r.property.2)

/-- Kernels of maps to every upper point at or after `t`. -/
def kernelPlus (c : Cut α) (t : α) : Submodule k (M.obj t) :=
  ⨅ r : {r // r ∈ c.upper ∧ t ≤ r}, LinearMap.ker (structureMapLinear M r.property.2)

/-- The upper subspace associated with the interval between two cuts. -/
def intervalPlus (l r : Cut α) (t : α) : Submodule k (M.obj t) :=
  imagePlus M l t ⊓ kernelPlus M r t

/-- The lower subspace associated with the interval between two cuts. -/
def intervalMinus (l r : Cut α) (t : α) : Submodule k (M.obj t) :=
  (imageMinus M l t ⊓ kernelPlus M r t) ⊔
    (imagePlus M l t ⊓ kernelMinus M r t)

/-- A nonempty downward directed family of subspaces of a finite-dimensional space has
an attained intersection. No finiteness of the underlying field or carrier is needed. -/
theorem exists_eq_iInf_of_directed {V : Type w} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {ι : Type*} [Nonempty ι] (S : ι → Submodule k V)
    (hS : Directed (· ≥ ·) S) : ∃ i, S i = ⨅ j, S j := by
  classical
  have hex : ∃ n : ℕ, ∃ i, Module.finrank k (S i) = n := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨_, i, rfl⟩
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  have hmin (j : ι) : Module.finrank k (S i) ≤ Module.finrank k (S j) := by
    rw [hi]
    exact Nat.find_min' hex ⟨j, rfl⟩
  refine ⟨i, le_antisymm (le_iInf fun j => ?_) (iInf_le _ i)⟩
  obtain ⟨a, hai, haj⟩ := hS i j
  have heq : S a = S i := Submodule.eq_of_le_of_finrank_eq hai
    (le_antisymm (Submodule.finrank_mono hai) (hmin a))
  exact heq ▸ haj

private theorem range_le_range {a b t : α} (hab : a ≤ b) (hbt : b ≤ t) :
    LinearMap.range (structureMapLinear M (hab.trans hbt)) ≤
      LinearMap.range (structureMapLinear M hbt) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨structureMapLinear M hab x,
    (LinearMap.congr_fun (structureMapLinear_comp M hab hbt) x).symm⟩

/-- At an upper point, image-plus is the image from a single upper point. -/
theorem imagePlus_eq_range (c : Cut α) {t : α} [FiniteDimensional k (M.obj t)]
    (ht : t ∈ c.upper) :
    ∃ s : {s // s ∈ c.upper ∧ s ≤ t},
      imagePlus M c t = LinearMap.range (structureMapLinear M s.property.2) := by
  have : Nonempty {s // s ∈ c.upper ∧ s ≤ t} := ⟨⟨t, ht, le_rfl⟩⟩
  obtain ⟨s, hs⟩ := exists_eq_iInf_of_directed
    (fun s : {s // s ∈ c.upper ∧ s ≤ t} =>
      LinearMap.range (structureMapLinear M s.property.2)) (by
    intro a b
    rcases le_total a.val b.val with hab | hba
    · exact ⟨a, le_rfl, range_le_range M hab b.property.2⟩
    · exact ⟨b, range_le_range M hba a.property.2, le_rfl⟩)
  exact ⟨s, hs.symm⟩

/-- Structure maps preserve image-plus. -/
theorem imagePlus_map_mem (c : Cut α) {p q : α} (hpq : p ≤ q)
    {x : M.obj p} (hx : x ∈ imagePlus M c p) :
    structureMapLinear M hpq x ∈ imagePlus M c q := by
  simp only [imagePlus, Submodule.mem_iInf] at hx ⊢
  intro s
  rcases le_total s.val p with hsp | hps
  · obtain ⟨z, hz⟩ := hx ⟨s, s.property.1, hsp⟩
    refine ⟨z, ?_⟩
    rw [structureMapLinear_comp M hsp hpq, LinearMap.comp_apply, hz]
  · refine ⟨structureMapLinear M hps x, ?_⟩
    exact (LinearMap.congr_fun (structureMapLinear_comp M hps s.property.2) x).symm

/-- Finite dimension turns image-plus transport into a surjection. -/
theorem imagePlus_map_surjective (c : Cut α) {p q : α}
    [FiniteDimensional k (M.obj p)] (hpq : p ≤ q) (hp : p ∈ c.upper)
    {y : M.obj q} (hy : y ∈ imagePlus M c q) :
    ∃ x ∈ imagePlus M c p, structureMapLinear M hpq x = y := by
  obtain ⟨s, hs⟩ := imagePlus_eq_range M c hp
  have hys := ((Submodule.mem_iInf _).mp hy) ⟨s, s.property.1, s.property.2.trans hpq⟩
  obtain ⟨z, hz⟩ := hys
  refine ⟨structureMapLinear M s.property.2 z, ?_, ?_⟩
  · rw [hs]
    exact ⟨z, rfl⟩
  · rw [structureMapLinear_comp M s.property.2 hpq, LinearMap.comp_apply] at hz
    exact hz

/-- At two points in the lower part, kernel-plus pulls back along the structure map. -/
theorem kernelPlus_map_mem_iff (c : Cut α) {p q : α} (hpq : p ≤ q)
    (hq : q ∈ c.lower) (x : M.obj p) :
    structureMapLinear M hpq x ∈ kernelPlus M c q ↔ x ∈ kernelPlus M c p := by
  simp only [kernelPlus, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hx r
    have hqr : q ≤ r := (c.lower_lt_upper hq r.property.1).le
    have he := hx ⟨r, r.property.1, hqr⟩
    rw [← LinearMap.comp_apply, ← structureMapLinear_comp M hpq hqr] at he
    exact he
  · intro hx r
    have he := hx ⟨r, r.property.1, hpq.trans r.property.2⟩
    rw [structureMapLinear_comp M hpq r.property.2, LinearMap.comp_apply] at he
    exact he

/-- Structure maps preserve interval-plus on the interval between its cuts. -/
theorem intervalPlus_map_mem (l r : Cut α) {p q : α} (hpq : p ≤ q)
    (hq : q ∈ r.lower) {x : M.obj p} (hx : x ∈ intervalPlus M l r p) :
    structureMapLinear M hpq x ∈ intervalPlus M l r q :=
  ⟨imagePlus_map_mem M l hpq hx.1,
    (kernelPlus_map_mem_iff M r hpq hq x).mpr hx.2⟩

/-- The transition maps of interval-plus are surjective. The only dimension assumption
is at the source fiber; no compatible lifts or stabilization witnesses are assumed. -/
theorem intervalPlus_map_surjective (l r : Cut α) {p q : α}
    [FiniteDimensional k (M.obj p)] (hpq : p ≤ q)
    (hp : p ∈ l.upper) (hq : q ∈ r.lower)
    {y : M.obj q} (hy : y ∈ intervalPlus M l r q) :
    ∃ x ∈ intervalPlus M l r p, structureMapLinear M hpq x = y := by
  obtain ⟨x, hx, hxy⟩ := imagePlus_map_surjective M l hpq hp hy.1
  refine ⟨x, ⟨hx, ?_⟩, hxy⟩
  apply (kernelPlus_map_mem_iff M r hpq hq x).mp
  rw [hxy]
  exact hy.2

private theorem kernel_le_kernel {t a b : α} (hta : t ≤ a) (hab : a ≤ b) :
    LinearMap.ker (structureMapLinear M hta) ≤
      LinearMap.ker (structureMapLinear M (hta.trans hab)) := by
  intro x hx
  change structureMapLinear M (hta.trans hab) x = 0
  rw [structureMapLinear_comp M hta hab, LinearMap.comp_apply,
    LinearMap.mem_ker.mp hx, map_zero]

/-- A nonempty kernel-plus intersection is attained at one upper point. -/
theorem kernelPlus_eq_kernel (c : Cut α) {t : α} [FiniteDimensional k (M.obj t)]
    (hne : ∃ r ∈ c.upper, t ≤ r) :
    ∃ r : {r // r ∈ c.upper ∧ t ≤ r},
      kernelPlus M c t = LinearMap.ker (structureMapLinear M r.property.2) := by
  have : Nonempty {r // r ∈ c.upper ∧ t ≤ r} := by
    obtain ⟨r, hr, htr⟩ := hne
    exact ⟨⟨r, hr, htr⟩⟩
  obtain ⟨r, hr⟩ := exists_eq_iInf_of_directed
    (fun r : {r // r ∈ c.upper ∧ t ≤ r} =>
      LinearMap.ker (structureMapLinear M r.property.2)) (by
    intro a b
    rcases le_total a.val b.val with hab | hba
    · exact ⟨a, le_rfl, kernel_le_kernel M a.property.2 hab⟩
    · exact ⟨b, kernel_le_kernel M b.property.2 hba, le_rfl⟩)
  exact ⟨r, hr.symm⟩

/-- Every lower image satisfies all upper image conditions. -/
theorem imageMinus_le_imagePlus (c : Cut α) (t : α) :
    imageMinus M c t ≤ imagePlus M c t := by
  apply iSup_le
  intro s
  apply le_iInf
  intro r
  exact range_le_range M (c.lower_lt_upper s.property.1 r.property.1).le r.property.2

/-- Every lower kernel satisfies all upper kernel conditions. -/
theorem kernelMinus_le_kernelPlus (c : Cut α) (t : α) :
    kernelMinus M c t ≤ kernelPlus M c t := by
  apply iSup_le
  intro s
  apply le_iInf
  intro r
  exact kernel_le_kernel M s.property.2 (c.lower_lt_upper s.property.1 r.property.1).le

/-- Interval-minus is a subspace of interval-plus. -/
theorem intervalMinus_le_intervalPlus (l r : Cut α) (t : α) :
    intervalMinus M l r t ≤ intervalPlus M l r t :=
  sup_le (inf_le_inf_right _ (imageMinus_le_imagePlus M l t))
    (inf_le_inf_left _ (kernelMinus_le_kernelPlus M r t))

/-- Image-minus transports exactly once the source lies in the upper part. -/
theorem imageMinus_map_eq (c : Cut α) {p q : α} (hpq : p ≤ q)
    (hp : p ∈ c.upper) :
    (imageMinus M c p).map (structureMapLinear M hpq) = imageMinus M c q := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply iSup_le
    intro s x hx
    obtain ⟨z, hz⟩ := hx
    apply (le_iSup (fun s : {s // s ∈ c.lower ∧ s ≤ q} =>
      LinearMap.range (structureMapLinear M s.property.2))
      ⟨s, s.property.1, s.property.2.trans hpq⟩)
    refine ⟨z, ?_⟩
    rw [structureMapLinear_comp M s.property.2 hpq, LinearMap.comp_apply, hz]
  · apply iSup_le
    intro s x hx
    obtain ⟨z, hz⟩ := hx
    have hsp : s.val ≤ p := (c.lower_lt_upper s.property.1 hp).le
    refine ⟨structureMapLinear M hsp z, ?_, ?_⟩
    · exact (le_iSup (fun s : {s // s ∈ c.lower ∧ s ≤ p} =>
        LinearMap.range (structureMapLinear M s.property.2))
        ⟨s, s.property.1, hsp⟩) ⟨z, rfl⟩
    · rw [structureMapLinear_comp M hsp hpq, LinearMap.comp_apply] at hz
      exact hz

/-- Structure maps preserve lower kernel conditions, including when the killing point
is passed by the structure map. -/
theorem kernelMinus_map_mem (c : Cut α) {p q : α} (hpq : p ≤ q)
    {x : M.obj p} (hx : x ∈ kernelMinus M c p) :
    structureMapLinear M hpq x ∈ kernelMinus M c q := by
  have hle : kernelMinus M c p ≤
      (kernelMinus M c q).comap (structureMapLinear M hpq) := by
    apply iSup_le
    intro s z hz
    rcases le_total q s.val with hqs | hsq
    · apply (le_iSup (fun r : {r // r ∈ c.lower ∧ q ≤ r} =>
        LinearMap.ker (structureMapLinear M r.property.2)) ⟨s, s.property.1, hqs⟩)
      change structureMapLinear M hqs (structureMapLinear M hpq z) = 0
      rw [← LinearMap.comp_apply, ← structureMapLinear_comp M hpq hqs]
      exact hz
    · have he : structureMapLinear M hpq z = 0 := by
        rw [structureMapLinear_comp M s.property.2 hsq, LinearMap.comp_apply,
          LinearMap.mem_ker.mp hz, map_zero]
      change structureMapLinear M hpq z ∈ kernelMinus M c q
      rw [he]
      exact Submodule.zero_mem _
  exact hle hx

/-- A map to a lower point is killed inside kernel-minus at its source. -/
theorem ker_le_kernelMinus (c : Cut α) {p q : α} (hpq : p ≤ q)
    (hq : q ∈ c.lower) :
    LinearMap.ker (structureMapLinear M hpq) ≤ kernelMinus M c p :=
  le_iSup (fun r : {r // r ∈ c.lower ∧ p ≤ r} =>
    LinearMap.ker (structureMapLinear M r.property.2)) ⟨q, hq, hpq⟩

/-- The image-plus subspace has exactly the expected image under transport. -/
theorem imagePlus_map_eq (c : Cut α) {p q : α} [FiniteDimensional k (M.obj p)]
    (hpq : p ≤ q) (hp : p ∈ c.upper) :
    (imagePlus M c p).map (structureMapLinear M hpq) = imagePlus M c q := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact imagePlus_map_mem M c hpq hx
  · intro y hy
    exact imagePlus_map_surjective M c hpq hp hy

/-- Kernel-plus is the pullback of kernel-plus at a later lower point. -/
theorem kernelPlus_comap_eq (c : Cut α) {p q : α} (hpq : p ≤ q)
    (hq : q ∈ c.lower) :
    (kernelPlus M c q).comap (structureMapLinear M hpq) = kernelPlus M c p := by
  ext x
  exact kernelPlus_map_mem_iff M c hpq hq x

/-- At a lower point, membership in kernel-minus is witnessed by one later lower point. -/
theorem mem_kernelMinus_iff (c : Cut α) {t : α} (ht : t ∈ c.lower) {x : M.obj t} :
    x ∈ kernelMinus M c t ↔
      ∃ r : {r // r ∈ c.lower ∧ t ≤ r}, structureMapLinear M r.property.2 x = 0 := by
  have : Nonempty {r // r ∈ c.lower ∧ t ≤ r} := ⟨⟨t, ht, le_rfl⟩⟩
  apply Submodule.mem_iSup_of_directed
  intro a b
  rcases le_total a.val b.val with hab | hba
  · exact ⟨b, kernel_le_kernel M a.property.2 hab, le_rfl⟩
  · exact ⟨a, le_rfl, kernel_le_kernel M b.property.2 hba⟩

/-- Kernel-minus also pulls back exactly between lower points. -/
theorem kernelMinus_map_mem_iff (c : Cut α) {p q : α} (hpq : p ≤ q)
    (hq : q ∈ c.lower) (x : M.obj p) :
    structureMapLinear M hpq x ∈ kernelMinus M c q ↔ x ∈ kernelMinus M c p := by
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := (mem_kernelMinus_iff M c hq).mp hx
    apply (le_iSup (fun r : {r // r ∈ c.lower ∧ p ≤ r} =>
      LinearMap.ker (structureMapLinear M r.property.2))
      ⟨r, r.property.1, hpq.trans r.property.2⟩)
    change structureMapLinear M (hpq.trans r.property.2) x = 0
    rw [structureMapLinear_comp M hpq r.property.2, LinearMap.comp_apply]
    exact hr
  · exact kernelMinus_map_mem M c hpq

/-- Kernel-minus is the pullback of kernel-minus at a later lower point. -/
theorem kernelMinus_comap_eq (c : Cut α) {p q : α} (hpq : p ≤ q)
    (hq : q ∈ c.lower) :
    (kernelMinus M c q).comap (structureMapLinear M hpq) = kernelMinus M c p := by
  ext x
  exact kernelMinus_map_mem_iff M c hpq hq x

/-- Interval-minus transports exactly between points of the interval. -/
theorem intervalMinus_map_eq (l r : Cut α) {p q : α} [FiniteDimensional k (M.obj p)]
    (hpq : p ≤ q) (hp : p ∈ l.upper) (hq : q ∈ r.lower) :
    (intervalMinus M l r p).map (structureMapLinear M hpq) = intervalMinus M l r q := by
  have hbirth : (imageMinus M l p ⊓ kernelPlus M r p).map (structureMapLinear M hpq) =
      imageMinus M l q ⊓ kernelPlus M r q := by
    rw [← kernelPlus_comap_eq M r hpq hq,
      ← Submodule.map_inf_eq_map_inf_comap, imageMinus_map_eq M l hpq hp]
  have hdeath : (imagePlus M l p ⊓ kernelMinus M r p).map (structureMapLinear M hpq) =
      imagePlus M l q ⊓ kernelMinus M r q := by
    rw [← kernelMinus_comap_eq M r hpq hq,
      ← Submodule.map_inf_eq_map_inf_comap, imagePlus_map_eq M l hpq hp]
  simpa only [intervalMinus, Submodule.map_sup] using congrArg₂ (· ⊔ ·) hbirth hdeath

/-- The actual linear transition map between interval-plus subspaces. -/
def intervalPlusMap (l r : Cut α) {p q : α} (hpq : p ≤ q) (hq : q ∈ r.lower) :
    intervalPlus M l r p →ₗ[k] intervalPlus M l r q where
  toFun x := ⟨structureMapLinear M hpq x, intervalPlus_map_mem M l r hpq hq x.property⟩
  map_add' x y := Subtype.ext (map_add (structureMapLinear M hpq) x.val y.val)
  map_smul' a x := Subtype.ext (map_smul (structureMapLinear M hpq) a x.val)

/-- The interval-plus transition map evaluates to the original structure map. -/
@[simp]
theorem intervalPlusMap_apply (l r : Cut α) {p q : α} (hpq : p ≤ q)
    (hq : q ∈ r.lower) (x : intervalPlus M l r p) :
    (intervalPlusMap M l r hpq hq x : M.obj q) = structureMapLinear M hpq x := rfl

/-- Interval-plus transition maps are surjective as maps of subspace carriers. -/
theorem intervalPlusMap_surjective (l r : Cut α) {p q : α}
    [FiniteDimensional k (M.obj p)] (hpq : p ≤ q) (hp : p ∈ l.upper)
    (hq : q ∈ r.lower) : Function.Surjective (intervalPlusMap M l r hpq hq) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := intervalPlus_map_surjective M l r hpq hp hq y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Interval-minus regarded as a subspace of interval-plus. -/
def intervalMinusInPlus (l r : Cut α) (t : α) : Submodule k (intervalPlus M l r t) :=
  (intervalMinus M l r t).comap (intervalPlus M l r t).subtype

/-- The interval-local quotient of the upper space by the lower space. -/
abbrev intervalQuotient (l r : Cut α) (t : α) :=
  intervalPlus M l r t ⧸ intervalMinusInPlus M l r t

/-- On interval-plus, the pullback of interval-minus is exactly interval-minus. -/
theorem intervalMinusInPlus_comap_eq (l r : Cut α) {p q : α}
    [FiniteDimensional k (M.obj p)] (hpq : p ≤ q) (hp : p ∈ l.upper)
    (hq : q ∈ r.lower) :
    (intervalMinusInPlus M l r q).comap (intervalPlusMap M l r hpq hq) =
      intervalMinusInPlus M l r p := by
  ext x
  change structureMapLinear M hpq x.val ∈ intervalMinus M l r q ↔
    x.val ∈ intervalMinus M l r p
  have hmap := intervalMinus_map_eq M l r hpq hp hq
  constructor
  · intro hx
    rw [← hmap] at hx
    obtain ⟨z, hz, he⟩ := hx
    have hd : x.val - z ∈ intervalMinus M l r p := by
      apply (le_sup_right : imagePlus M l p ⊓ kernelMinus M r p ≤ intervalMinus M l r p)
      refine ⟨Submodule.sub_mem _ x.property.1
        ((intervalMinus_le_intervalPlus M l r p hz).1), ?_⟩
      apply ker_le_kernelMinus M r hpq hq
      change structureMapLinear M hpq (x.val - z) = 0
      rw [map_sub, he, sub_self]
    simpa only [sub_add_cancel] using Submodule.add_mem (intervalMinus M l r p) hd hz
  · intro hx
    rw [← hmap]
    exact ⟨x.val, hx, rfl⟩

/-- The quotient transition map is induced by the original structure map. -/
def intervalQuotientMap (l r : Cut α) {p q : α} [FiniteDimensional k (M.obj p)]
    (hpq : p ≤ q) (hp : p ∈ l.upper) (hq : q ∈ r.lower) :
    intervalQuotient M l r p →ₗ[k] intervalQuotient M l r q :=
  (intervalMinusInPlus M l r p).mapQ (intervalMinusInPlus M l r q)
    (intervalPlusMap M l r hpq hq)
    (le_of_eq (intervalMinusInPlus_comap_eq M l r hpq hp hq).symm)

/-- Quotient transport is injective because the lower space is the exact pullback. -/
theorem intervalQuotientMap_injective (l r : Cut α) {p q : α}
    [FiniteDimensional k (M.obj p)] (hpq : p ≤ q) (hp : p ∈ l.upper)
    (hq : q ∈ r.lower) : Function.Injective (intervalQuotientMap M l r hpq hp hq) := by
  apply LinearMap.ker_eq_bot.mp
  rw [intervalQuotientMap, Submodule.ker_mapQ,
    intervalMinusInPlus_comap_eq M l r hpq hp hq, Submodule.mkQ_map_self]

/-- Quotient transport is surjective because interval-plus transport is surjective. -/
theorem intervalQuotientMap_surjective (l r : Cut α) {p q : α}
    [FiniteDimensional k (M.obj p)] (hpq : p ≤ q) (hp : p ∈ l.upper)
    (hq : q ∈ r.lower) : Function.Surjective (intervalQuotientMap M l r hpq hp hq) := by
  intro y
  obtain ⟨y, rfl⟩ := (intervalMinusInPlus M l r q).mkQ_surjective y
  obtain ⟨x, rfl⟩ := intervalPlusMap_surjective M l r hpq hp hq y
  exact ⟨(intervalMinusInPlus M l r p).mkQ x, rfl⟩

/-- Interval-local quotients are linearly isomorphic along every interval transition. -/
noncomputable def intervalQuotientEquiv (l r : Cut α) {p q : α}
    [FiniteDimensional k (M.obj p)] (hpq : p ≤ q) (hp : p ∈ l.upper)
    (hq : q ∈ r.lower) : intervalQuotient M l r p ≃ₗ[k] intervalQuotient M l r q :=
  LinearEquiv.ofBijective (intervalQuotientMap M l r hpq hp hq)
    ⟨intervalQuotientMap_injective M l r hpq hp hq,
      intervalQuotientMap_surjective M l r hpq hp hq⟩

/-- Quotient transport sends the class of a vector to the class of its structure-map image. -/
@[simp]
theorem intervalQuotientEquiv_mkQ (l r : Cut α) {p q : α}
    [FiniteDimensional k (M.obj p)] (hpq : p ≤ q) (hp : p ∈ l.upper)
    (hq : q ∈ r.lower) (x : intervalPlus M l r p) :
    intervalQuotientEquiv M l r hpq hp hq ((intervalMinusInPlus M l r p).mkQ x) =
      (intervalMinusInPlus M l r q).mkQ (intervalPlusMap M l r hpq hq x) := rfl

/-- The interval determined by a lower and an upper cut. It may be empty. -/
def support (l r : Cut α) : Set α := l.upper ∩ r.lower

/-- Interval-plus spaces and their restricted structure maps form a persistence module
on the interval support. -/
def intervalPlusModule (l r : Cut α) : PModule.{u,v,w} k (support l r) :=
  CompatibleSections.subspaceModule M (support l r)
    (fun t => intervalPlus M l r t.val)
    (fun _ t h _ hx => intervalPlus_map_mem M l r h t.property.2 hx)

/-- The interval-plus module's structure maps are the restricted original maps. -/
@[simp]
theorem structureMapLinear_intervalPlusModule (l r : Cut α) {s t : support l r}
    (h : s ≤ t) :
    structureMapLinear (intervalPlusModule M l r) h =
      intervalPlusMap M l r h t.property.2 := rfl

/-- Evaluation of compatible interval-plus sections is surjective for pointwise
finite-dimensional real persistence modules. -/
theorem intervalPlus_evaluation_surjective_real (M : PModule.{u,0,w} k ℝ)
    [∀ t, FiniteDimensional k (M.obj t)] (l r : Cut ℝ) (t : support l r) :
    Function.Surjective (CompatibleSections.evaluation (intervalPlusModule M l r) t) := by
  apply CompatibleSections.evaluation_surjective_real
  intro s t h
  rw [structureMapLinear_intervalPlusModule]
  exact intervalPlusMap_surjective M l r h s.property.1 t.property.2

/-- Every vector in interval-plus extends to a compatible family on the whole real
interval, including open endpoints, singletons and unbounded intervals. -/
theorem exists_intervalPlus_compatible_lift_real (M : PModule.{u,0,w} k ℝ)
    [∀ t, FiniteDimensional k (M.obj t)] (l r : Cut ℝ) (t : support l r)
    (y : M.obj t.val) (hy : y ∈ intervalPlus M l r t.val) :
    ∃ x : ∀ s : support l r, M.obj s.val,
      x t = y ∧ (∀ s, x s ∈ intervalPlus M l r s.val) ∧
      ∀ s t : support l r, ∀ h : s ≤ t, structureMapLinear M h (x s) = x t := by
  apply CompatibleSections.exists_compatible_lift_real M (support l r)
    (fun s => intervalPlus M l r s.val)
    (fun _ t h _ hx => intervalPlus_map_mem M l r h t.property.2 hx)
    (fun s t h _ hy => intervalPlus_map_surjective M l r h s.property.1 t.property.2 hy)
    t y hy

/-- Evaluation in the concrete interval-plus subspace. -/
def intervalPlusEvaluation (l r : Cut α) (t : support l r) :
    CompatibleSections.sections (intervalPlusModule M l r) →ₗ[k] intervalPlus M l r t.val where
  toFun x := x.val t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of a compatible interval-plus section in its interval-local quotient. -/
def intervalQuotientEvaluation (l r : Cut α) (t : support l r) :
    CompatibleSections.sections (intervalPlusModule M l r) →ₗ[k]
      intervalQuotient M l r t.val :=
  (intervalMinusInPlus M l r t.val).mkQ.comp (intervalPlusEvaluation M l r t)

/-- The kernel consists exactly of sections whose value lies in interval-minus. -/
theorem mem_ker_intervalQuotientEvaluation (l r : Cut α) (t : support l r)
    (x : CompatibleSections.sections (intervalPlusModule M l r)) :
    x ∈ (intervalQuotientEvaluation M l r t).ker ↔
      (x.val t).val ∈ intervalMinus M l r t.val := by
  change (Submodule.Quotient.mk (x.val t) : intervalQuotient M l r t.val) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero (p := intervalMinusInPlus M l r t.val)

/-- Compatible interval-plus sections surject onto every interval-local quotient. -/
theorem intervalQuotientEvaluation_surjective_real (M : PModule.{u,0,w} k ℝ)
    [∀ t, FiniteDimensional k (M.obj t)] (l r : Cut ℝ) (t : support l r) :
    Function.Surjective (intervalQuotientEvaluation M l r t) := by
  intro y
  obtain ⟨z, rfl⟩ := (intervalMinusInPlus M l r t.val).mkQ_surjective y
  obtain ⟨x, hx⟩ := intervalPlus_evaluation_surjective_real M l r t z
  change x.val t = z at hx
  exact ⟨x, congrArg (intervalMinusInPlus M l r t.val).mkQ hx⟩

/-- Quotient evaluation commutes with every forward interval transition. -/
theorem intervalQuotientEvaluation_naturality (l r : Cut α) {s t : support l r}
    [FiniteDimensional k (M.obj s.val)] (h : s ≤ t)
    (x : CompatibleSections.sections (intervalPlusModule M l r)) :
    intervalQuotientMap M l r h s.property.1 t.property.2
      (intervalQuotientEvaluation M l r s x) = intervalQuotientEvaluation M l r t x := by
  change (intervalMinusInPlus M l r t.val).mkQ
    (intervalPlusMap M l r h t.property.2 (x.val s)) =
      (intervalMinusInPlus M l r t.val).mkQ (x.val t)
  congr 1
  rw [← structureMapLinear_intervalPlusModule]
  exact CompatibleSections.compatible (intervalPlusModule M l r) x h

/-- The kernel of global quotient evaluation is independent of the interval point.
This supplies the common subspace used when choosing a global complement. -/
theorem ker_intervalQuotientEvaluation_eq [∀ t, FiniteDimensional k (M.obj t)]
    (l r : Cut α) (s t : support l r) :
    (intervalQuotientEvaluation M l r s).ker = (intervalQuotientEvaluation M l r t).ker := by
  have hforward (a b : support l r) (h : a ≤ b)
      (x : CompatibleSections.sections (intervalPlusModule M l r)) :
      intervalQuotientEvaluation M l r a x = 0 ↔
        intervalQuotientEvaluation M l r b x = 0 := by
    have he := intervalQuotientEvaluation_naturality M l r h x
    constructor
    · intro hx
      rw [← he, hx, map_zero]
    · intro hx
      apply intervalQuotientMap_injective M l r h a.property.1 b.property.2
      rw [he, hx, map_zero]
  ext x
  rcases le_total s t with h | h
  · exact hforward s t h x
  · exact (hforward t s h x).symm

/-- One complement is chosen in the global section space, at a specified interval point. -/
noncomputable def sectionComplement (l r : Cut α) (t : support l r) :
    Submodule k (CompatibleSections.sections (intervalPlusModule M l r)) :=
  ((intervalQuotientEvaluation M l r t).ker.exists_isCompl).choose

/-- The chosen section space complements the quotient-evaluation kernel. -/
theorem isCompl_sectionComplement (l r : Cut α) (t : support l r) :
    IsCompl (intervalQuotientEvaluation M l r t).ker (sectionComplement M l r t) :=
  ((intervalQuotientEvaluation M l r t).ker.exists_isCompl).choose_spec

/-- The same chosen section complement works at every interval point. -/
theorem isCompl_sectionComplement_at [∀ t, FiniteDimensional k (M.obj t)]
    (l r : Cut α) (t s : support l r) :
    IsCompl (intervalQuotientEvaluation M l r s).ker (sectionComplement M l r t) := by
  rw [← ker_intervalQuotientEvaluation_eq M l r t s]
  exact isCompl_sectionComplement M l r t

/-- The restriction of quotient evaluation to the chosen global complement is bijective. -/
theorem sectionComplement_quotientEvaluation_bijective_real (M : PModule.{u,0,w} k ℝ)
    [∀ t, FiniteDimensional k (M.obj t)] (l r : Cut ℝ) (t s : support l r) :
    Function.Bijective ((intervalQuotientEvaluation M l r s).comp
      (sectionComplement M l r t).subtype) := by
  have hc := isCompl_sectionComplement_at M l r t s
  constructor
  · intro x y hxy
    apply Subtype.ext
    change intervalQuotientEvaluation M l r s x.val =
      intervalQuotientEvaluation M l r s y.val at hxy
    have hk : x.val - y.val ∈ (intervalQuotientEvaluation M l r s).ker := by
      change intervalQuotientEvaluation M l r s (x.val - y.val) = 0
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hc.disjoint (x.val - y.val) hk
      ((sectionComplement M l r t).sub_mem x.property y.property))
  · intro y
    obtain ⟨x, hx⟩ := intervalQuotientEvaluation_surjective_real M l r s y
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp
      (show x ∈ (intervalQuotientEvaluation M l r s).ker ⊔ sectionComplement M l r t by
        rw [hc.sup_eq_top]; trivial)
    refine ⟨⟨w, hw⟩, ?_⟩
    change intervalQuotientEvaluation M l r s w = y
    calc
      intervalQuotientEvaluation M l r s w = intervalQuotientEvaluation M l r s (z + w) := by
        rw [map_add, LinearMap.mem_ker.mp hz, zero_add]
      _ = intervalQuotientEvaluation M l r s x := congrArg _ hzw
      _ = y := hx

/-- A chosen global complement is linearly isomorphic to every interval-local quotient. -/
noncomputable def sectionComplementQuotientEquiv_real (M : PModule.{u,0,w} k ℝ)
    [∀ t, FiniteDimensional k (M.obj t)] (l r : Cut ℝ) (t s : support l r) :
    sectionComplement M l r t ≃ₗ[k] intervalQuotient M l r s.val :=
  LinearEquiv.ofBijective ((intervalQuotientEvaluation M l r s).comp
    (sectionComplement M l r t).subtype)
    (sectionComplement_quotientEvaluation_bijective_real M l r t s)

/-- Evaluation transports the one global complement into each interval-plus fiber. -/
noncomputable def sectionComplementAt (l r : Cut α) (t s : support l r) :
    Submodule k (intervalPlus M l r s.val) :=
  (sectionComplement M l r t).map (intervalPlusEvaluation M l r s)

/-- The transported global complement is a genuine local complement of interval-minus. -/
theorem isCompl_sectionComplementAt_real (M : PModule.{u,0,w} k ℝ)
    [∀ t, FiniteDimensional k (M.obj t)] (l r : Cut ℝ) (t s : support l r) :
    IsCompl (intervalMinusInPlus M l r s.val) (sectionComplementAt M l r t s) := by
  have hc := isCompl_sectionComplement_at M l r t s
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr (top_unique ?_)⟩
  · intro x hx hxW
    obtain ⟨w, hw, rfl⟩ := hxW
    have hw0 : w = 0 := Submodule.disjoint_def.mp hc.disjoint w
      ((mem_ker_intervalQuotientEvaluation M l r s w).mpr hx) hw
    rw [hw0]
    exact map_zero (intervalPlusEvaluation M l r s)
  · intro x _
    obtain ⟨w, hw⟩ := (sectionComplement_quotientEvaluation_bijective_real M l r t s).surjective
      ((intervalMinusInPlus M l r s.val).mkQ x)
    let z : intervalPlus M l r s.val := intervalPlusEvaluation M l r s w.val
    have hz : z ∈ sectionComplementAt M l r t s := ⟨w.val, w.property, rfl⟩
    have hdiff : x - z ∈ intervalMinusInPlus M l r s.val := by
      apply (Submodule.Quotient.mk_eq_zero (p := intervalMinusInPlus M l r s.val)).mp
      change (intervalMinusInPlus M l r s.val).mkQ (x - z) = 0
      rw [map_sub]
      change (intervalMinusInPlus M l r s.val).mkQ x -
        intervalQuotientEvaluation M l r s w.val = 0
      rw [show intervalQuotientEvaluation M l r s w.val =
        (intervalMinusInPlus M l r s.val).mkQ x from hw, sub_self]
    exact Submodule.mem_sup.mpr ⟨x - z, hdiff, z, hz, sub_add_cancel x z⟩

/-- Transition maps carry each transported complement exactly onto the next one. -/
theorem sectionComplementAt_map_eq (l r : Cut α) (t : support l r)
    {s q : support l r} (h : s ≤ q) :
    (sectionComplementAt M l r t s).map (intervalPlusMap M l r h q.property.2) =
      sectionComplementAt M l r t q := by
  rw [sectionComplementAt, ← Submodule.map_comp]
  congr 1
  ext x
  exact congrArg Subtype.val (CompatibleSections.compatible (intervalPlusModule M l r) x h)

/-- The transported complement, extended by zero outside the interval support. -/
noncomputable def sectionComplementFiber (l r : Cut α) (t : support l r) (s : α) :
    Submodule k (M.obj s) := by
  classical
  exact if hs : s ∈ support l r then
    (sectionComplementAt M l r t ⟨s, hs⟩).map (intervalPlus M l r s).subtype else ⊥

/-- The zero extension is preserved by every structure map, including transitions
that cross the right end of the interval. -/
theorem sectionComplementFiber_map_mem (l r : Cut α) (t : support l r)
    {s q : α} (h : s ≤ q) {x : M.obj s} (hx : x ∈ sectionComplementFiber M l r t s) :
    structureMapLinear M h x ∈ sectionComplementFiber M l r t q := by
  classical
  by_cases hs : s ∈ support l r
  · rw [sectionComplementFiber, dif_pos hs] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hu
    by_cases hq : q ∈ support l r
    · rw [sectionComplementFiber, dif_pos hq]
      refine ⟨w.val ⟨q, hq⟩, ⟨w, hw, rfl⟩, ?_⟩
      exact (congrArg Subtype.val
        (CompatibleSections.compatible (intervalPlusModule M l r) w
          (show (⟨s, hs⟩ : support l r) ≤ ⟨q, hq⟩ from h))).symm
    · rw [sectionComplementFiber, dif_neg hq, Submodule.mem_bot]
      have hqu : q ∈ r.upper := by
        rcases r.mem_lower_or_upper q with hql | hqu
        · exact False.elim (hq ⟨upper_of_le h hs.1, hql⟩)
        · exact hqu
      exact ((Submodule.mem_iInf _).mp (w.val ⟨s, hs⟩).property.2) ⟨q, hqu, h⟩
  · simp only [sectionComplementFiber, dif_neg hs, Submodule.mem_bot] at hx
    subst x
    simpa only [map_zero] using Submodule.zero_mem (sectionComplementFiber M l r t q)

/-- The chosen compatible complement gives an interval-supported persistence submodule. -/
noncomputable def sectionComplementModule (l r : Cut α) (t : support l r) :
    PModule.{u,v,w} k α where
  obj s := ModuleCat.of k (sectionComplementFiber M l r t s)
  map f := ModuleCat.ofHom {
    toFun x := ⟨structureMapLinear M (CategoryTheory.leOfHom f) x.val,
      sectionComplementFiber_map_mem M l r t (CategoryTheory.leOfHom f) x.property⟩
    map_add' _ _ := Subtype.ext (map_add _ _ _)
    map_smul' _ _ := Subtype.ext (map_smul _ _ _) }
  map_id s := by
    ext x
    exact LinearMap.congr_fun (structureMapLinear_self M (le_refl s)) x.val
  map_comp f g := by
    ext x
    exact LinearMap.congr_fun
      (structureMapLinear_comp M (CategoryTheory.leOfHom f) (CategoryTheory.leOfHom g)) x.val

/-- The interval-supported module embeds naturally into the original module. -/
noncomputable def sectionComplementInclusion (l r : Cut α) (t : support l r) :
    sectionComplementModule M l r t ⟶ M where
  app s := ModuleCat.ofHom (sectionComplementFiber M l r t s).subtype
  naturality _ _ f := by ext x; rfl

/-- The chosen submodule vanishes at every point outside its interval. -/
theorem sectionComplementFiber_eq_bot (l r : Cut α) (t : support l r) {s : α}
    (hs : s ∉ support l r) : sectionComplementFiber M l r t s = ⊥ := by
  classical
  simp only [sectionComplementFiber, dif_neg hs]

end Cut

end TDA.Persistence
