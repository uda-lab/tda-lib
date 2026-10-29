import TDA.Persistence.SupportInterval
import TDA.Persistence.RankBarcodeIso
import TDA.Persistence.AlgebraicFamily

/-!
# Finite observations of arbitrary interval decompositions

Strict real observation lists restrict convex supports to finite intervals.
Only finitely many occurrences are visible in a pointwise finite-dimensional
algebraic decomposition. Finite rank uniqueness identifies their multiset, with
multiplicities, with the existing rank barcode.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace TDA.Persistence.FiniteObservation

open CategoryTheory
open scoped Classical

variable {k : Type*} [Field k] {N : ℕ}

noncomputable def active (c : Fin N ↪o ℝ) (S : Set ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => c i ∈ S)

private theorem mem_active (c : Fin N ↪o ℝ) (S : Set ℝ) (i : Fin N) :
    i ∈ active c S ↔ c i ∈ S := by simp [active]

noncomputable def sampledInterval (c : Fin N ↪o ℝ) (S : Set ℝ)
    (hne : (active c S).Nonempty) : FiniteInterval N := by
  let a := (active c S).min' hne
  let b := (active c S).max' hne
  have hab : a ≤ b :=
    Finset.min'_le (active c S) b (Finset.max'_mem (active c S) hne)
  exact ⟨a.val, b.val + 1, by omega, by omega⟩

/-- The finite interval records exactly the observed points in the support. -/
theorem sampledInterval_alive_iff (c : Fin N ↪o ℝ) (S : Set ℝ)
    (hS : S.OrdConnected) (hne : (active c S).Nonempty) (i : Fin N) :
    (sampledInterval c S hne).alive i ↔ c i ∈ S := by
  let a := (active c S).min' hne
  let b := (active c S).max' hne
  have ha : c a ∈ S := (mem_active c S a).mp (Finset.min'_mem _ _)
  have hb : c b ∈ S := (mem_active c S b).mp (Finset.max'_mem _ _)
  have hmin : ∀ j : Fin N, c j ∈ S → a ≤ j := by
    intro j hj
    exact Finset.min'_le _ j ((mem_active c S j).mpr hj)
  have hmax : ∀ j : Fin N, c j ∈ S → j ≤ b := by
    intro j hj
    exact Finset.le_max' _ j ((mem_active c S j).mpr hj)
  constructor
  · intro hi
    change a.val ≤ i.val ∧ i.val < b.val + 1 at hi
    have hai : a ≤ i := by
      exact Fin.le_iff_val_le_val.mpr hi.1
    have hib : i ≤ b := by
      apply Fin.le_iff_val_le_val.mpr
      omega
    exact hS.out ha hb ⟨c.monotone hai, c.monotone hib⟩
  · intro hi
    change a.val ≤ i.val ∧ i.val < b.val + 1
    exact ⟨Fin.le_iff_val_le_val.mp (hmin i hi), by
      have h := Fin.le_iff_val_le_val.mp (hmax i hi)
      omega⟩

private instance sampled_finiteDimensional (c : Fin N ↪o ℝ) (S : Set ℝ)
    (hS : S.OrdConnected) (i : Fin N) :
    FiniteDimensional k ((reindex c.toOrderHom (SupportInterval.module (k := k) S hS)).obj i) := by
  change FiniteDimensional k (SupportInterval.fiber (k := k) S (c i))
  infer_instance

private theorem sampled_structureMapRank (c : Fin N ↪o ℝ) (S : Set ℝ)
    (hS : S.OrdConnected) (i j : Fin N) (hij : i ≤ j) :
    structureMapRank (reindex c.toOrderHom (SupportInterval.module (k := k) S hS)) i j hij =
      if c i ∈ S ∧ c j ∈ S then 1 else 0 := by
  classical
  unfold structureMapRank
  rw [structureMapLinear_reindex]
  let hc : c i ≤ c j := c.monotone hij
  change Module.finrank k (LinearMap.range
    (structureMapLinear (SupportInterval.module (k := k) S hS) hc)) = _
  by_cases h : c i ∈ S ∧ c j ∈ S
  · rw [if_pos h]
    have hinj : Function.Injective
        (structureMapLinear (SupportInterval.module (k := k) S hS)
          (c.monotone hij)) := by
      intro x y hxy
      apply Subtype.ext
      have hv := congrArg (fun z : SupportInterval.fiber (k := k) S (c j) => (z : k)) hxy
      rw [SupportInterval.structureMap_val S hS hc x,
        SupportInterval.structureMap_val S hS hc y] at hv
      simpa [h.2] using hv
    rw [LinearMap.finrank_range_of_inj hinj]
    change Module.finrank k (SupportInterval.fiber (k := k) S (c i)) = 1
    rw [show SupportInterval.fiber (k := k) S (c i) = ⊤ by simp [SupportInterval.fiber, h.1]]
    simp
  · rw [if_neg h]
    have hz := (SupportInterval.structureMap_eq_zero_iff (k := k) S hS
      (c.monotone hij)).mpr h
    rw [hz]
    simp [LinearMap.range_zero]

/-- Every observed transition of a convex support has the same rank as its
native finite interval restriction, including zero and singleton samples. -/
theorem sampled_structureMapRank_eq_interval (c : Fin N ↪o ℝ) (S : Set ℝ)
    (hS : S.OrdConnected) (hne : (active c S).Nonempty)
    (i j : Fin N) (hij : i ≤ j) :
    structureMapRank (reindex c.toOrderHom (SupportInterval.module (k := k) S hS)) i j hij =
      structureMapRank (intervalModule (k := k) (sampledInterval c S hne)) i j hij := by
  rw [sampled_structureMapRank]
  change _ = Module.finrank k (LinearMap.range
    (intervalMap (k := k) (sampledInterval c S hne) hij))
  rw [intervalMap_finrank_range]
  simp only [sampledInterval_alive_iff c S hS hne]

/-- Finite barcode uniqueness identifies a sampled convex support with one
native interval, without assuming a finite decomposition of the real module. -/
theorem sampled_rankBarcode_single (c : Fin N ↪o ℝ) (S : Set ℝ)
    (hS : S.OrdConnected) (hne : (active c S).Nonempty) :
    rankBarcode (reindex c.toOrderHom (SupportInterval.module (k := k) S hS)) =
      {(sampledInterval c S hne)} := by
  classical
  have hrank : ∀ (i j : Fin N) (hij : i ≤ j),
      structureMapRank (reindex c.toOrderHom (SupportInterval.module (k := k) S hS)) i j hij =
        structureMapRank (barcodeModule (k := k) ({sampledInterval c S hne} :
          Multiset (FiniteInterval N))) i j hij := by
    intro i j hij
    rw [sampled_structureMapRank, rank_barcodeMap]
    change (if c i ∈ S ∧ c j ∈ S then 1 else 0) =
      Multiset.countP (fun I : FiniteInterval N => I.birth ≤ i.val ∧ j.val < I.death)
        ((sampledInterval c S hne) ::ₘ 0)
    simp only [Multiset.countP_cons, Multiset.countP_zero, zero_add]
    simp only [← interval_alive_endpoints_iff (sampledInterval c S hne) hij,
      sampledInterval_alive_iff c S hS hne]
  exact ((rankBarcode_eq_iff _ _).2 hrank).trans
    (rankBarcode_barcodeModule ({sampledInterval c S hne} : Multiset (FiniteInterval N)))

/-- A support invisible to every observation has the empty finite barcode. -/
theorem sampled_rankBarcode_empty (c : Fin N ↪o ℝ) (S : Set ℝ)
    (hS : S.OrdConnected) (hempty : active c S = ∅) :
    rankBarcode (reindex c.toOrderHom (SupportInterval.module (k := k) S hS)) = 0 := by
  classical
  have hno (i : Fin N) : c i ∉ S := by
    intro hi
    have hm := (mem_active c S i).mpr hi
    simp [hempty] at hm
  have hrank : ∀ (i j : Fin N) (hij : i ≤ j),
      structureMapRank (reindex c.toOrderHom (SupportInterval.module (k := k) S hS)) i j hij =
        structureMapRank (barcodeModule (k := k) (0 : Multiset (FiniteInterval N))) i j hij := by
    intro i j hij
    rw [sampled_structureMapRank, rank_barcodeMap]
    simp [hno i]
  exact ((rankBarcode_eq_iff _ _).2 hrank).trans
    (rankBarcode_barcodeModule (0 : Multiset (FiniteInterval N)))

/-- Local finiteness at each sampled fiber makes the family of visible
occurrences finite, with no finiteness assumption on the full index type. -/
theorem finite_visible_occurrences {J : Type*} (c : Fin N ↪o ℝ) (S : J → Set ℝ)
    (hlocal : ∀ i : Fin N, {j : J | c i ∈ S j}.Finite) :
    {j : J | ∃ i : Fin N, c i ∈ S j}.Finite := by
  have hf : (⋃ i : Fin N, {j : J | c i ∈ S j}).Finite :=
    Set.finite_iUnion hlocal
  convert hf using 1
  ext j
  simp

private noncomputable def rangePiEquiv {J : Type*} {A B : J → Type*}
    [∀ j, AddCommGroup (A j)] [∀ j, Module k (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module k (B j)]
    (f : ∀ j, A j →ₗ[k] B j) :
    LinearMap.range (LinearMap.piMap f) ≃ₗ[k] ∀ j, LinearMap.range (f j) := by
  classical
  let g : LinearMap.range (LinearMap.piMap f) →ₗ[k]
      ∀ j, LinearMap.range (f j) := {
    toFun := fun y j => ⟨y.1 j, by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x j, by simpa [LinearMap.piMap] using congrFun hx j⟩⟩
    map_add' := by
      intro x y
      funext j
      apply Subtype.ext
      rfl
    map_smul' := by
      intro a x
      funext j
      apply Subtype.ext
      rfl }
  refine LinearEquiv.ofBijective g ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun hxy j)
  · intro y
    let x : ∀ j, A j := fun j => Classical.choose (LinearMap.mem_range.mp (y j).2)
    have hx (j : J) : f j (x j) = (y j).1 :=
      Classical.choose_spec (LinearMap.mem_range.mp (y j).2)
    refine ⟨⟨LinearMap.piMap f x, ⟨x, rfl⟩⟩, ?_⟩
    funext j
    apply Subtype.ext
    change f j (x j) = (y j).1
    exact hx j

private theorem finrank_range_piMap {J : Type*} [Fintype J] {A B : J → Type*}
    [∀ j, AddCommGroup (A j)] [∀ j, Module k (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module k (B j)]
    [∀ j, FiniteDimensional k (A j)] (f : ∀ j, A j →ₗ[k] B j) :
    Module.finrank k (LinearMap.range (LinearMap.piMap f)) =
      ∑ j, Module.finrank k (LinearMap.range (f j)) := by
  classical
  rw [(rangePiEquiv (k := k) f).finrank_eq, Module.finrank_pi_fintype]

/-- A finite family of arbitrary convex supports contributes one rank unit
for each summand alive at both observations. -/
private instance finite_family_finiteDimensional {J : Type} [Fintype J]
    (S : J → Set ℝ) (hS : ∀ j, (S j).OrdConnected) (t : ℝ) :
    FiniteDimensional k ((AlgebraicFamily.familyModule
      (fun a => SupportInterval.module (k := k) (S a) (hS a))).obj t) := by
  change FiniteDimensional k (DirectSum J
    (fun a => SupportInterval.fiber (k := k) (S a) t))
  infer_instance

private instance finite_sampled_family_finiteDimensional {J : Type} [Fintype J]
    (c : Fin N ↪o ℝ) (S : J → Set ℝ) (hS : ∀ j, (S j).OrdConnected)
    (i : Fin N) : FiniteDimensional k
      ((reindex c.toOrderHom (AlgebraicFamily.familyModule
        (fun a => SupportInterval.module (k := k) (S a) (hS a)))).obj i) :=
  finite_family_finiteDimensional S hS (c i)

theorem finite_family_sampled_rank {k : Type*} [Field k] {J : Type} [Fintype J]
    (c : Fin N ↪o ℝ) (S : J → Set ℝ) (hS : ∀ j, (S j).OrdConnected)
    (i j : Fin N) (hij : i ≤ j) :
    structureMapRank
      (reindex c.toOrderHom (AlgebraicFamily.familyModule
        (fun a => SupportInterval.module (k := k) (S a) (hS a)))) i j hij =
      ∑ a : J, if c i ∈ S a ∧ c j ∈ S a then 1 else 0 := by
  classical
  let F : J → PModule.{_,0,_} k ℝ :=
    fun a => SupportInterval.module (k := k) (S a) (hS a)
  letI : ∀ t : Fin N, FiniteDimensional k
      ((c.toOrderHom.toFunctor ⋙ AlgebraicFamily.familyModule F).obj t) :=
    fun t => finite_sampled_family_finiteDimensional c S hS t
  letI : ∀ t : Fin N, FiniteDimensional k
      ((c.toOrderHom.toFunctor ⋙ RealBarcode.familyModule F).obj t) := by
    intro t
    change FiniteDimensional k (∀ a : J, (F a).obj (c t))
    infer_instance
  letI : FiniteDimensional k
      ((reindex c.toOrderHom (AlgebraicFamily.familyModule F)).obj i) :=
    finite_sampled_family_finiteDimensional c S hS i
  letI : FiniteDimensional k
      ((reindex c.toOrderHom (RealBarcode.familyModule F)).obj i) := by
    change FiniteDimensional k (∀ a : J, (F a).obj (c i))
    infer_instance
  let e := Functor.isoWhiskerLeft c.toOrderHom.toFunctor
    (AlgebraicFamily.finiteProductIso F)
  calc
    _ = structureMapRank (reindex c.toOrderHom (RealBarcode.familyModule F)) i j hij :=
      structureMapRank_eq_of_iso e i j hij
    _ = ∑ a : J, if c i ∈ S a ∧ c j ∈ S a then 1 else 0 := by
      change Module.finrank k (LinearMap.range
        (LinearMap.piMap (fun a : J =>
          structureMapLinear (F a) (c.monotone hij)))) = _
      rw [finrank_range_piMap]
      apply Finset.sum_congr rfl
      intro a ha
      have hr := sampled_structureMapRank (k := k) c (S a) (hS a) i j hij
      change Module.finrank k (LinearMap.range
        (structureMapLinear (SupportInterval.module (k := k) (S a) (hS a))
          (c.monotone hij))) = _ at hr
      exact hr

/-- One finite bar for each visible occurrence, retaining repeated supports. -/
noncomputable def finiteFamilyBarcode {J : Type} [Fintype J]
    (c : Fin N ↪o ℝ) (S : J → Set ℝ) : Multiset (FiniteInterval N) := by
  classical
  exact ∑ a : J, if h : (active c (S a)).Nonempty then
    {(sampledInterval c (S a) h)} else 0

private theorem countP_finset_sum {J A : Type*} (s : Finset J)
    (f : J → Multiset A) (p : A → Prop) [DecidablePred p] :
    (∑ a ∈ s, f a).countP p = ∑ a ∈ s, (f a).countP p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, Multiset.countP_add, ih]

/-- Finite barcodes of a finite family are exactly the multiset of its
nonempty observed intersections, without assuming barcode equality. -/
theorem finite_family_rankBarcode {k : Type*} [Field k] {J : Type} [Fintype J]
    (c : Fin N ↪o ℝ) (S : J → Set ℝ) (hS : ∀ a, (S a).OrdConnected) :
    rankBarcode (reindex c.toOrderHom (AlgebraicFamily.familyModule
      (fun a => SupportInterval.module (k := k) (S a) (hS a)))) =
      finiteFamilyBarcode c S := by
  classical
  let B := finiteFamilyBarcode c S
  have hrank : ∀ (i j : Fin N) (hij : i ≤ j),
      structureMapRank (reindex c.toOrderHom (AlgebraicFamily.familyModule
        (fun a => SupportInterval.module (k := k) (S a) (hS a)))) i j hij =
        structureMapRank (barcodeModule (k := k) B) i j hij := by
    intro i j hij
    rw [finite_family_sampled_rank, rank_barcodeMap]
    change (∑ a : J, if c i ∈ S a ∧ c j ∈ S a then 1 else 0) =
      (∑ a : J, if h : (active c (S a)).Nonempty then
        ({(sampledInterval c (S a) h)} : Multiset (FiniteInterval N)) else 0).countP
          (fun I => I.birth ≤ i.val ∧ j.val < I.death)
    rw [countP_finset_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : (active c (S a)).Nonempty
    · simp only [dif_pos h]
      change (if c i ∈ S a ∧ c j ∈ S a then 1 else 0) =
        Multiset.countP (fun I : FiniteInterval N => I.birth ≤ i.val ∧ j.val < I.death)
          ((sampledInterval c (S a) h) ::ₘ 0)
      simp only [Multiset.countP_cons, Multiset.countP_zero, zero_add]
      simp only [← interval_alive_endpoints_iff (sampledInterval c (S a) h) hij,
        sampledInterval_alive_iff c (S a) (hS a) h]
    · simp only [dif_neg h, Multiset.countP_zero]
      have hi : c i ∉ S a := by
        intro hci
        exact h ⟨i, (mem_active c (S a) i).mpr hci⟩
      simp [hi]
  exact ((rankBarcode_eq_iff _ _).2 hrank).trans (rankBarcode_barcodeModule B)

private noncomputable def toVisibleLinear {k : Type*} [Field k] {J : Type}
    (F : J → PModule.{_,0,_} k ℝ) (V : Set J) (t : ℝ) :
    DirectSum J (fun a => (F a).obj t) →ₗ[k]
      DirectSum V (fun a => (F a.val).obj t) := by
  classical
  exact DirectSum.toModule k J _ (fun a =>
    if h : a ∈ V then DirectSum.lof k V (fun b => (F b.val).obj t) ⟨a, h⟩ else 0)

private noncomputable def fromVisibleLinear {k : Type*} [Field k] {J : Type}
    (F : J → PModule.{_,0,_} k ℝ) (V : Set J) (t : ℝ) :
    DirectSum V (fun a => (F a.val).obj t) →ₗ[k]
      DirectSum J (fun a => (F a).obj t) :=
  DirectSum.toModule k V _ (fun a => DirectSum.lof k J (fun b => (F b).obj t) a.val)

private theorem toVisible_fromVisible {k : Type*} [Field k] {J : Type}
    (F : J → PModule.{_,0,_} k ℝ) (V : Set J) (t : ℝ) :
    (toVisibleLinear F V t).comp (fromVisibleLinear F V t) = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro a
  apply LinearMap.ext
  intro x
  simp [toVisibleLinear, fromVisibleLinear]

private theorem fromVisible_toVisible {k : Type*} [Field k] {J : Type}
    (F : J → PModule.{_,0,_} k ℝ) (V : Set J) (t : ℝ)
    (hout : ∀ a : J, a ∉ V → Subsingleton ((F a).obj t)) :
    (fromVisibleLinear F V t).comp (toVisibleLinear F V t) = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro a
  apply LinearMap.ext
  intro x
  by_cases ha : a ∈ V
  · simp [toVisibleLinear, fromVisibleLinear, ha]
  · have hx : x = 0 := @Subsingleton.elim ((F a).obj t) (hout a ha) x 0
    subst x
    simp

/-- At the sampled indices, coordinates whose support misses every sample
vanish. The algebraic family therefore restricts naturally to visible indices. -/
noncomputable def visibleFamilyIso {k : Type*} [Field k] {J : Type}
    (c : Fin N ↪o ℝ) (S : J → Set ℝ) (hS : ∀ a, (S a).OrdConnected)
    (V : Set J) (hcover : ∀ a : J, (∃ i : Fin N, c i ∈ S a) → a ∈ V) :
    reindex c.toOrderHom (AlgebraicFamily.familyModule
      (fun a => SupportInterval.module (k := k) (S a) (hS a))) ≅
      reindex c.toOrderHom (AlgebraicFamily.familyModule
        (fun a : V => SupportInterval.module (k := k) (S a.val) (hS a.val))) := by
  classical
  let F : J → PModule.{_,0,_} k ℝ :=
    fun a => SupportInterval.module (k := k) (S a) (hS a)
  have hout (t : Fin N) (a : J) (ha : a ∉ V) :
      Subsingleton ((F a).obj (c t)) := by
    have hs : c t ∉ S a := fun h => ha (hcover a ⟨t, h⟩)
    change Subsingleton (SupportInterval.fiber (k := k) (S a) (c t))
    exact ⟨fun x y => by
      apply Subtype.ext
      rw [SupportInterval.val_eq_zero (k := k) (S a) hs x,
        SupportInterval.val_eq_zero (k := k) (S a) hs y]⟩
  refine NatIso.ofComponents (fun t => ?_) ?_
  · let g := toVisibleLinear F V (c t)
    have hbij : Function.Bijective g := by
      constructor
      · intro x y hxy
        have he := congrArg (fromVisibleLinear F V (c t)) hxy
        change ((fromVisibleLinear F V (c t)).comp g) x =
          ((fromVisibleLinear F V (c t)).comp g) y at he
        rw [fromVisible_toVisible F V (c t) (hout t)] at he
        simpa using he
      · intro y
        refine ⟨fromVisibleLinear F V (c t) y, ?_⟩
        have he := congrArg (fun L : _ →ₗ[k] _ => L y)
          (toVisible_fromVisible F V (c t))
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using he
    exact (LinearEquiv.ofBijective g hbij).toModuleIso
  · intro s t f
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro a
    apply LinearMap.ext
    intro x
    change (F a).obj (c s) at x
    let hs : c s ≤ c t := c.monotone (leOfHom f)
    change toVisibleLinear F V (c t)
        (DirectSum.lmap (fun b : J => structureMapLinear (F b) hs)
          (DirectSum.lof k J (fun b => (F b).obj (c s)) a x)) =
      DirectSum.lmap (fun b : V => structureMapLinear (F b.val) hs)
        (toVisibleLinear F V (c s)
          (DirectSum.lof k J (fun b => (F b).obj (c s)) a x))
    by_cases ha : a ∈ V
    · simp only [DirectSum.lmap_lof, toVisibleLinear, DirectSum.toModule_lof,
        dif_pos ha, DirectSum.lmap_lof]
    · have hx : x = 0 := @Subsingleton.elim ((F a).obj (c s)) (hout s a ha) x 0
      subst x
      simp only [map_zero]

private instance reindexed_finiteDimensional {k : Type*} [Field k]
    (M : PModule.{_,0,_} k ℝ) [∀ t : ℝ, FiniteDimensional k (M.obj t)]
    (c : Fin N ↪o ℝ) : ∀ i : Fin N,
      FiniteDimensional k ((reindex c.toOrderHom M).obj i) :=
  fun i => inferInstanceAs (FiniteDimensional k (M.obj (c i)))

private theorem support_nontrivial_iff {k : Type*} [Field k]
    (S : Set ℝ) (t : ℝ) :
    Nontrivial (SupportInterval.fiber (k := k) S t) ↔ t ∈ S := by
  classical
  by_cases ht : t ∈ S
  · rw [show SupportInterval.fiber (k := k) S t = ⊤ by
      simp [SupportInterval.fiber, ht]]
    constructor
    · intro _
      exact ht
    · intro _
      exact ⟨⟨0, trivial⟩, ⟨1, trivial⟩, by
        intro h
        exact zero_ne_one (congrArg Subtype.val h)⟩
  · constructor
    · intro hn
      have hs : Subsingleton (SupportInterval.fiber (k := k) S t) :=
        ⟨fun x y => Subtype.ext <| by
          rw [SupportInterval.val_eq_zero (k := k) S ht x,
            SupportInterval.val_eq_zero (k := k) S ht y]⟩
      exact False.elim ((not_nontrivial_iff_subsingleton.mpr hs) hn)
    · exact False.elim ∘ ht

/-- Pointwise finite dimensionality of a represented real module implies
only finitely many interval occurrences hit a finite observation list. -/
theorem finite_visible_of_decomposition {k : Type*} [Field k] {J : Type}
    (M : PModule.{_,0,_} k ℝ) [∀ t : ℝ, FiniteDimensional k (M.obj t)]
    (c : Fin N ↪o ℝ) (S : J → Set ℝ) (hS : ∀ a, (S a).OrdConnected)
    (e : M ≅ AlgebraicFamily.familyModule
      (fun a => SupportInterval.module (k := k) (S a) (hS a))) :
    {a : J | ∃ i : Fin N, c i ∈ S a}.Finite := by
  let F : J → PModule.{_,0,_} k ℝ :=
    fun a => SupportInterval.module (k := k) (S a) (hS a)
  have hf := AlgebraicFamily.finite_observed_nontrivial_of_iso F e
    (fun t => inferInstanceAs (FiniteDimensional k (M.obj t))) (fun i => c i)
  convert hf using 1
  ext a
  simp only [Set.mem_ofPred_eq]
  exact exists_congr (fun i => (support_nontrivial_iff (k := k) (S a) (c i)).symm)

/-- Given an algebraic real interval decomposition, finite observation
recovers exactly the multiset of nonempty sampled intersections. The finite
visible subtype is derived from local activity, so `J` may be uncountable. -/
theorem rankBarcode_of_decomposition {k : Type*} [Field k] {J : Type}
    (M : PModule.{_,0,_} k ℝ) [∀ t : ℝ, FiniteDimensional k (M.obj t)]
    (c : Fin N ↪o ℝ) (S : J → Set ℝ) (hS : ∀ a, (S a).OrdConnected)
    (e : M ≅ AlgebraicFamily.familyModule
      (fun a => SupportInterval.module (k := k) (S a) (hS a)))
    (hvisible : {a : J | ∃ i : Fin N, c i ∈ S a}.Finite) :
    rankBarcode (reindex c.toOrderHom M) =
      letI : Fintype {a : J | ∃ i : Fin N, c i ∈ S a} := hvisible.fintype
      finiteFamilyBarcode c (fun a : {a : J | ∃ i : Fin N, c i ∈ S a} => S a.val) := by
  classical
  let V : Set J := {a | ∃ i : Fin N, c i ∈ S a}
  letI : Fintype V := hvisible.fintype
  letI : ∀ t : Fin N, FiniteDimensional k ((reindex c.toOrderHom M).obj t) :=
    fun t => inferInstanceAs (FiniteDimensional k (M.obj (c t)))
  letI : ∀ t : Fin N, FiniteDimensional k
      ((reindex c.toOrderHom (AlgebraicFamily.familyModule
        (fun a => SupportInterval.module (k := k) (S a) (hS a)))).obj t) := by
    intro t
    exact Module.Finite.equiv ((e.app (c t)).toLinearEquiv)
  letI : ∀ t : Fin N, FiniteDimensional k
      ((reindex c.toOrderHom (AlgebraicFamily.familyModule
        (fun a : V => SupportInterval.module (k := k) (S a.val) (hS a.val)))).obj t) :=
    fun t => finite_sampled_family_finiteDimensional c
      (fun a : V => S a.val) (fun a => hS a.val) t
  let eSample := Functor.isoWhiskerLeft c.toOrderHom.toFunctor e
  let eVisible := visibleFamilyIso (k := k) c S hS V (fun a h => h)
  calc
    rankBarcode (reindex c.toOrderHom M) =
        rankBarcode (reindex c.toOrderHom (AlgebraicFamily.familyModule
          (fun a => SupportInterval.module (k := k) (S a) (hS a)))) :=
      rankBarcode_eq_of_iso eSample
    _ = rankBarcode (reindex c.toOrderHom (AlgebraicFamily.familyModule
          (fun a : V => SupportInterval.module (k := k) (S a.val) (hS a.val)))) :=
      rankBarcode_eq_of_iso eVisible
    _ = finiteFamilyBarcode c (fun a : V => S a.val) :=
      finite_family_rankBarcode c (fun a : V => S a.val) (fun a => hS a.val)

/-- The finite-observation barcode follows from a genuine real algebraic
interval decomposition and pointwise finite dimensionality alone. -/
theorem rankBarcode_of_pfd_decomposition {k : Type*} [Field k] {J : Type}
    (M : PModule.{_,0,_} k ℝ) [∀ t : ℝ, FiniteDimensional k (M.obj t)]
    (c : Fin N ↪o ℝ) (S : J → Set ℝ) (hS : ∀ a, (S a).OrdConnected)
    (e : M ≅ AlgebraicFamily.familyModule
      (fun a => SupportInterval.module (k := k) (S a) (hS a))) :
    rankBarcode (reindex c.toOrderHom M) =
      let hvisible : {a : J | ∃ i : Fin N, c i ∈ S a}.Finite :=
        finite_visible_of_decomposition M c S hS e
      letI : Fintype {a : J | ∃ i : Fin N, c i ∈ S a} := hvisible.fintype
      finiteFamilyBarcode c (fun a : {a : J | ∃ i : Fin N, c i ∈ S a} => S a.val) :=
  rankBarcode_of_decomposition M c S hS e
    (finite_visible_of_decomposition M c S hS e)

end TDA.Persistence.FiniteObservation
