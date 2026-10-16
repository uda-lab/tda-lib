import TDA.Persistence.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Real.Basic

/-!
# Finite-stratum reconstruction of real persistence modules

For strictly increasing real critical values, `cellIndex` counts the values at or below a
parameter. Its zero cell is the left tail; its positive cells are left-closed and right-open,
with an unbounded final cell. `sample` adds a zero stage before the critical-value samples.
The reconstruction uses actual structure-map isomorphisms within cells, over any ring and
without a finite-dimensionality hypothesis.

This is a library construction using functor semantics as in Bauer--Lesnick, arXiv:1311.3681v4,
§2.1. It supplies neither an interleaving distance nor the isometry theorem of that paper.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.FiniteConstructible

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {n : ℕ}

/-- Count critical values at or below `t`, including a zero cell before the first value. -/
noncomputable def cellIndex (c : Fin n ↪o ℝ) : ℝ →o Fin (n + 1) where
  toFun t := ⟨(Finset.univ.filter fun i => c i ≤ t).card,
    Nat.lt_succ_of_le (by simpa using
      (Finset.card_filter_le Finset.univ (fun i : Fin n => c i ≤ t)))⟩
  monotone' s t h := Finset.card_le_card (by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans h)

/-- A critical value has been counted precisely when its index is below the cell count. -/
theorem lt_cellIndex_iff (c : Fin n ↪o ℝ) (i : Fin n) (t : ℝ) :
    i.val < (cellIndex c t).val ↔ c i ≤ t := by
  classical
  constructor
  · intro h
    by_contra hi
    have hsub : (Finset.univ.filter fun j => c j ≤ t) ⊆ Finset.Iio i := by
      intro j hj
      have hjt : c j ≤ t := (Finset.mem_filter.mp hj).2
      exact Finset.mem_Iio.mpr (c.lt_iff_lt.mp (hjt.trans_lt (lt_of_not_ge hi)))
    have hcard := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at hcard
    change i.val < (Finset.univ.filter fun j => c j ≤ t).card at h
    omega
  · intro hi
    have hsub : Finset.Iic i ⊆ (Finset.univ.filter fun j => c j ≤ t) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (c.monotone (Finset.mem_Iic.mp hj)).trans hi⟩
    have hcard := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at hcard
    exact hcard

/-- The zero cell consists exactly of parameters below every critical value. -/
theorem cellIndex_eq_zero_iff (c : Fin n ↪o ℝ) (t : ℝ) :
    cellIndex c t = 0 ↔ ∀ i, t < c i := by
  constructor
  · intro h i
    by_contra hi
    have := (lt_cellIndex_iff c i t).mpr (le_of_not_gt hi)
    simp [h] at this
  · intro h
    apply Fin.ext
    by_contra hz
    have hpos : 0 < (cellIndex c t).val := Nat.pos_of_ne_zero hz
    have h0 : 0 < n := by
      by_contra hn
      have : n = 0 := by omega
      have := (cellIndex c t).isLt
      omega
    have hi := (lt_cellIndex_iff c ⟨0, h0⟩ t).mp hpos
    exact (not_lt_of_ge hi) (h _)

/-- Positive cell `i+1` starts at `c i` and ends before every later critical value. -/
theorem cellIndex_eq_succ_iff (c : Fin n ↪o ℝ) (i : Fin n) (t : ℝ) :
    cellIndex c t = i.succ ↔ c i ≤ t ∧ ∀ j, i < j → t < c j := by
  constructor
  · intro h
    refine ⟨(lt_cellIndex_iff c i t).mp (by simp [h]), ?_⟩
    intro j hij
    by_contra hj
    have := (lt_cellIndex_iff c j t).mpr (le_of_not_gt hj)
    rw [h] at this
    have : i.val < j.val := hij
    simp only [Fin.val_succ] at *
    omega
  · rintro ⟨hi, hgap⟩
    apply Fin.ext
    have hlo := (lt_cellIndex_iff c i t).mpr hi
    have hhi : (cellIndex c t).val ≤ i.val + 1 := by
      by_contra h
      have hjn : i.val + 1 < n := by have := (cellIndex c t).isLt; omega
      let j : Fin n := ⟨i.val + 1, hjn⟩
      have hj := (lt_cellIndex_iff c j t).mp (by dsimp [j]; omega)
      exact (not_lt_of_ge hj) (hgap j (by change i.val < i.val + 1; omega))
    simpa only [Fin.val_succ] using Nat.le_antisymm hhi hlo

/-- A critical value belongs to its new cell, not the preceding cell. -/
@[simp] theorem cellIndex_critical (c : Fin n ↪o ℝ) (i : Fin n) :
    cellIndex c (c i) = i.succ :=
  (cellIndex_eq_succ_iff c i (c i)).mpr ⟨le_rfl, fun _ h => c.strictMono h⟩

/-- Adjacent critical values bound the half-open cell. -/
theorem cellIndex_of_adjacent (c : Fin n ↪o ℝ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (t : ℝ) (hlo : c i ≤ t) (hhi : t < c j) :
    cellIndex c t = i.succ := by
  apply (cellIndex_eq_succ_iff c i t).mpr
  refine ⟨hlo, fun k hik => hhi.trans_le (c.monotone ?_)⟩
  change j.val ≤ k.val
  have : i.val < k.val := hik
  omega

/-- The final cell extends through the whole right tail. -/
theorem cellIndex_of_last_le (c : Fin (n + 1) ↪o ℝ) (t : ℝ)
    (h : c (Fin.last n) ≤ t) : cellIndex c t = Fin.last (n + 1) := by
  apply (cellIndex_eq_succ_iff c (Fin.last n) t).mpr
  exact ⟨h, fun j hj => (not_lt_of_ge (Fin.le_last j) hj).elim⟩

/-- With no critical values every real parameter is in the zero cell. -/
@[simp] theorem cellIndex_empty (c : Fin 0 ↪o ℝ) (t : ℝ) : cellIndex c t = 0 :=
  (cellIndex_eq_zero_iff c t).mpr (fun i => Fin.elim0 i)

variable {R : Type u} [Ring R]

private noncomputable def sampleObj (c : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ)
    (i : Fin (n + 1)) : ModuleCat.{w} R :=
  Fin.cases 0 (fun j => M.obj (c j)) i

private noncomputable def sampleMap (c : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ)
    {i j : Fin (n + 1)} (h : i ≤ j) : sampleObj c M i ⟶ sampleObj c M j := by
  cases i using Fin.cases with
  | zero => exact 0
  | succ i =>
    cases j using Fin.cases with
    | zero => exact 0
    | succ j => exact structureMap M (c.monotone (Fin.succ_le_succ_iff.mp h))

/-- The critical samples, preceded by an actual zero module. -/
noncomputable def sample (c : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ) :
    PModule.{u,0,w} R (Fin (n + 1)) where
  obj := sampleObj c M
  map f := sampleMap c M (leOfHom f)
  map_id i := by
    cases i using Fin.cases with
    | zero => exact (isZero_zero (ModuleCat R)).eq_of_src _ _
    | succ i => exact structureMap_self M _
  map_comp {i j k} f g := by
    cases i using Fin.cases with
    | zero => exact (isZero_zero (ModuleCat R)).eq_of_src _ _
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (by have := leOfHom f; simp at this)
      | succ j =>
        cases k using Fin.cases with
        | zero => exact (by have := leOfHom g; simp at this)
        | succ k => exact (structureMap_comp M _ _).symm

/-- The initial sample is the zero object, rather than a sentinel real grade. -/
@[simp] theorem sample_obj_zero (c : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ) :
    (sample c M).obj 0 = 0 := rfl

/-- Positive samples are values at actual critical parameters. -/
@[simp] theorem sample_obj_succ (c : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ)
    (i : Fin n) : (sample c M).obj i.succ = M.obj (c i) := rfl

/-- Structure maps between positive samples are the original structure maps. -/
@[simp] theorem sample_structureMap_succ (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) {i j : Fin n} (h : i ≤ j) :
    structureMap (sample c M) (Fin.succ_le_succ_iff.mpr h) =
      structureMap M (c.monotone h) := rfl

/-- Right-continuous finite constructibility with an explicit zero left tail.
Only the actual within-cell structure maps are required to be isomorphisms. -/
structure IsConstructible (c : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ) : Prop where
  zero_left : ∀ t, (∀ i, t < c i) → IsZero (M.obj t)
  isIso_map : ∀ (s t : ℝ) (h : s ≤ t), cellIndex c s = cellIndex c t →
    IsIso (structureMap M h)

/-- In the empty-critical-set case, constructibility is exactly pointwise zero. -/
theorem isConstructible_empty_iff (c : Fin 0 ↪o ℝ) (M : PModule.{u,0,w} R ℝ) :
    IsConstructible c M ↔ ∀ t, IsZero (M.obj t) := by
  constructor
  · intro h t
    exact h.zero_left t (fun i => Fin.elim0 i)
  · intro h
    exact ⟨fun t _ => h t, fun s t _ _ => (h s).isIso (h t) _⟩

/-- Any finite chain with zero initial fiber gives a module satisfying these strata.
This also exhibits constructible modules without assuming a factorization in the predicate. -/
theorem isConstructible_reindex (c : Fin n ↪o ℝ)
    (A : PModule.{u,0,w} R (Fin (n + 1))) (hA : IsZero (A.obj 0)) :
    IsConstructible c (reindex (cellIndex c) A) where
  zero_left t ht := by
    change IsZero (A.obj (cellIndex c t))
    rw [(cellIndex_eq_zero_iff c t).mpr ht]
    exact hA
  isIso_map s t h heq := by
    change IsIso (A.map (homOfLE ((cellIndex c).monotone h)))
    have := homOfLE_isIso_of_eq ((cellIndex c).monotone h) heq
    infer_instance

private noncomputable def comparisonMap (c : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ)
    (i : Fin (n + 1)) (t : ℝ) (h : ∀ j : Fin n, j.val < i.val → c j ≤ t) :
    (sample c M).obj i ⟶ M.obj t := by
  cases i using Fin.cases with
  | zero => exact 0
  | succ i => exact structureMap M (h i (Nat.lt_succ_self _))

-- Prove the commuting square before substituting the cell counts. Its positive case is
-- just the two factorizations of the same original structure map `M(c i → t)`.
private theorem comparisonMap_naturality (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) {i j : Fin (n + 1)} (hij : i ≤ j)
    {s t : ℝ} (hst : s ≤ t)
    (hs : ∀ k : Fin n, k.val < i.val → c k ≤ s)
    (ht : ∀ k : Fin n, k.val < j.val → c k ≤ t) :
    structureMap (sample c M) hij ≫ comparisonMap c M j t ht =
      comparisonMap c M i s hs ≫ structureMap M hst := by
  cases i using Fin.cases with
  | zero => exact (isZero_zero (ModuleCat R)).eq_of_src _ _
  | succ i =>
    cases j using Fin.cases with
    | zero => have := hij; simp at this
    | succ j =>
      change structureMap M _ ≫ structureMap M _ =
        structureMap M _ ≫ structureMap M _
      rw [structureMap_comp, structureMap_comp]

/-- The forward reconstruction map exists for every module, using the actual critical
sample-to-parameter structure maps on positive cells and the zero map on the left cell. -/
noncomputable def toOriginal (c : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ) :
    reindex (cellIndex c) (sample c M) ⟶ M where
  app t := comparisonMap c M (cellIndex c t) t
    (fun i h => (lt_cellIndex_iff c i t).mp h)
  naturality {_s _t} f := comparisonMap_naturality c M
    ((cellIndex c).monotone (leOfHom f)) (leOfHom f) _ _

private theorem isIso_comparisonMap (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) (hM : IsConstructible c M)
    (i : Fin (n + 1)) (t : ℝ) (hb : ∀ j : Fin n, j.val < i.val → c j ≤ t)
    (hq : cellIndex c t = i) : IsIso (comparisonMap c M i t hb) := by
  cases i using Fin.cases with
  | zero =>
    exact (isZero_zero (ModuleCat R)).isIso
      (hM.zero_left t ((cellIndex_eq_zero_iff c t).mp hq)) _
  | succ i =>
    apply hM.isIso_map (c i) t
    exact (cellIndex_critical c i).trans hq.symm

/-- Constructibility makes the actual forward comparison an isomorphism at every parameter. -/
theorem isIso_toOriginal_app (c : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ)
    (hM : IsConstructible c M) (t : ℝ) : IsIso ((toOriginal c M).app t) :=
  isIso_comparisonMap c M hM (cellIndex c t) t _ rfl

/-- Reconstruct a module by a natural isomorphism from its finite critical samples.
The inverse is obtained from the proven component isomorphisms, not supplied as a hypothesis. -/
noncomputable def reconstructionIso (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) (hM : IsConstructible c M) :
    reindex (cellIndex c) (sample c M) ≅ M := by
  letI (t : ℝ) : IsIso ((toOriginal c M).app t) := isIso_toOriginal_app c M hM t
  exact NatIso.ofComponents (fun t => asIso ((toOriginal c M).app t))
    (fun f => (toOriginal c M).naturality f)

/-- The reconstruction isomorphism uses the previously constructed forward map. -/
@[simp] theorem reconstructionIso_hom (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) (hM : IsConstructible c M) :
    (reconstructionIso c M hM).hom = toOriginal c M := by
  ext t
  rfl

/-- Forward reconstruction commutes with every real structure map. -/
theorem reconstructionIso_hom_naturality (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) (hM : IsConstructible c M) {s t : ℝ} (h : s ≤ t) :
    structureMap (reindex (cellIndex c) (sample c M)) h ≫
      (reconstructionIso c M hM).hom.app t =
    (reconstructionIso c M hM).hom.app s ≫ structureMap M h :=
  (reconstructionIso c M hM).hom.naturality (homOfLE h)

/-- Inverse reconstruction also commutes with every real structure map. -/
theorem reconstructionIso_inv_naturality (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) (hM : IsConstructible c M) {s t : ℝ} (h : s ≤ t) :
    structureMap M h ≫ (reconstructionIso c M hM).inv.app t =
      (reconstructionIso c M hM).inv.app s ≫
        structureMap (reindex (cellIndex c) (sample c M)) h :=
  (reconstructionIso c M hM).inv.naturality (homOfLE h)

/-- Forward then inverse reconstruction is the identity on the reconstructed module. -/
@[simp] theorem reconstructionIso_hom_inv_id (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) (hM : IsConstructible c M) :
    (reconstructionIso c M hM).hom ≫ (reconstructionIso c M hM).inv = 𝟙 _ :=
  (reconstructionIso c M hM).hom_inv_id

/-- Inverse then forward reconstruction is the identity on the original module. -/
@[simp] theorem reconstructionIso_inv_hom_id (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) (hM : IsConstructible c M) :
    (reconstructionIso c M hM).inv ≫ (reconstructionIso c M hM).hom = 𝟙 M :=
  (reconstructionIso c M hM).inv_hom_id

end TDA.Persistence.FiniteConstructible
