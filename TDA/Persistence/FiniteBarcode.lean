import TDA.Persistence.Interval
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite barcodes and rank recovery

A finite barcode is a multiset. Its pointwise module is a product indexed by the occurrences in
`B.toList`, so repeated intervals occupy separate coordinates. No interval decomposition theorem
is used in this file.
-/

universe u v

namespace TDA.Persistence

open CategoryTheory

/-- The finite set of occurrences in the chosen list representative of a barcode. -/
abbrev BarcodeOccurrence (N : ℕ) (B : Multiset (FiniteInterval N)) := Fin B.toList.length

/-- The pointwise finite direct sum associated to one list enumeration of a barcode. -/
noncomputable def barcodeModuleOfList {N : ℕ} {k : Type u} [Field k]
    (xs : List (FiniteInterval N)) : PModule.{u,0,u} k (Fin N) where
  obj i := ModuleCat.of k
    (∀ t : Fin xs.length, (intervalModule (k := k) (xs.get t)).obj i)
  map {i j} f := ModuleCat.ofHom <|
    LinearMap.piMap (fun t : Fin xs.length =>
      structureMapLinear (intervalModule (k := k) (xs.get t)) (leOfHom f))
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    simp [LinearMap.piMap]
  map_comp {i j ℓ} f g := by
    apply ModuleCat.hom_ext
    have hfg : leOfHom (f ≫ g) = (leOfHom f).trans (leOfHom g) := rfl
    change LinearMap.piMap (fun t : Fin xs.length =>
        structureMapLinear (intervalModule (k := k) (xs.get t)) (leOfHom (f ≫ g))) =
      (LinearMap.piMap (fun t : Fin xs.length =>
        structureMapLinear (intervalModule (k := k) (xs.get t)) (leOfHom g))).comp
      (LinearMap.piMap (fun t : Fin xs.length =>
        structureMapLinear (intervalModule (k := k) (xs.get t)) (leOfHom f))
      )
    apply LinearMap.ext
    intro x
    funext t
    change structureMapLinear (intervalModule (k := k) (xs.get t))
        (leOfHom (f ≫ g)) (x t) =
      structureMapLinear (intervalModule (k := k) (xs.get t)) (leOfHom g)
        (structureMapLinear (intervalModule (k := k) (xs.get t)) (leOfHom f) (x t))
    rw [hfg]
    simpa only [LinearMap.comp_apply] using congrArg
      (fun L : _ →ₗ[k] _ => L (x t))
      (structureMapLinear_comp (intervalModule (k := k) (xs.get t))
        (leOfHom f) (leOfHom g))

/-- Each fiber of a list-enumerated barcode is finite-dimensional. -/
instance barcodeModuleOfList_finiteDimensional {N : ℕ} {k : Type u} [Field k]
    (xs : List (FiniteInterval N)) (i : Fin N) :
    FiniteDimensional k ((barcodeModuleOfList (k := k) xs).obj i) := by
  classical
  letI : ∀ t : Fin xs.length,
      FiniteDimensional k ((intervalModule (k := k) (xs.get t)).obj i) :=
    fun t => intervalModule_finiteDimensional (k := k) (xs.get t) i
  dsimp [barcodeModuleOfList]
  apply FiniteDimensional.finiteDimensional_pi'

/-- The pointwise finite direct sum of the intervals in a multiset barcode. -/
noncomputable def barcodeModule {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) : PModule.{u,0,u} k (Fin N) :=
  barcodeModuleOfList (k := k) B.toList

/-- Each finite barcode fiber is finite-dimensional, with one coordinate per occurrence. -/
instance barcodeModule_finiteDimensional {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (i : Fin N) :
    FiniteDimensional k ((barcodeModule (k := k) B).obj i) := by
  unfold barcodeModule
  infer_instance

private noncomputable def barcodeEnumerationIndexEquiv {N : ℕ}
    {xs ys : List (FiniteInterval N)} (hperm : xs.Perm ys) :
    Fin xs.length ≃ Fin ys.length := by
  classical
  letI : BEq (FiniteInterval N) := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq (FiniteInterval N) := inferInstance
  exact
    { toFun := hperm.idxBij
      invFun := hperm.symm.idxBij
      left_inv := hperm.idxBij_symm_leftInverse_idxBij
      right_inv := hperm.idxBij_symm_rightInverse_idxBij }

private theorem barcodeEnumerationIndexEquiv_apply {N : ℕ}
    {xs ys : List (FiniteInterval N)} (hperm : xs.Perm ys) (t : Fin xs.length) :
    barcodeEnumerationIndexEquiv hperm t = hperm.idxBij t := rfl

private noncomputable def intervalFiberLinearEquiv {N : ℕ} {k : Type u} [Field k]
    {I J : FiniteInterval N} (h : I = J) (i : Fin N) :
    (intervalModule (k := k) I).obj i ≃ₗ[k] (intervalModule (k := k) J).obj i := by
  change (FiniteInterval.fiber (k := k) I i) ≃ₗ[k]
    (FiniteInterval.fiber (k := k) J i)
  have hsub : FiniteInterval.fiber (k := k) J i = FiniteInterval.fiber (k := k) I i :=
    congrArg (fun K => FiniteInterval.fiber (k := k) K i) h.symm
  exact (LinearEquiv.ofEq _ _ hsub).symm

private theorem intervalFiberLinearEquiv_apply {N : ℕ} {k : Type u} [Field k]
    {I J : FiniteInterval N} (h : I = J) (i : Fin N)
    (x : (intervalModule (k := k) I).obj i) :
    intervalFiberLinearEquiv (k := k) h i x = h ▸ x := by
  cases h
  rfl

private theorem intervalFiberLinearEquiv_natural {N : ℕ} {k : Type u} [Field k]
    {I J : FiniteInterval N} (h : I = J) {i j : Fin N} (hij : i ≤ j)
    (x : (intervalModule (k := k) I).obj i) :
    intervalFiberLinearEquiv (k := k) h j
        (structureMapLinear (intervalModule (k := k) I) hij x) =
      structureMapLinear (intervalModule (k := k) J) hij
        (intervalFiberLinearEquiv (k := k) h i x) := by
  cases h
  change structureMapLinear (intervalModule (k := k) I) hij x =
    structureMapLinear (intervalModule (k := k) I) hij x
  rfl

private noncomputable def barcodeEnumerationLinearEquiv {N : ℕ} {k : Type u} [Field k]
    {xs ys : List (FiniteInterval N)} (hperm : xs.Perm ys) (i : Fin N) :
    (∀ t : Fin xs.length, (intervalModule (k := k) (xs.get t)).obj i) ≃ₗ[k]
      (∀ t : Fin ys.length, (intervalModule (k := k) (ys.get t)).obj i) := by
  classical
  let e := barcodeEnumerationIndexEquiv hperm
  have hget (t : Fin xs.length) : ys.get (hperm.idxBij t) = xs.get t := by
    change ys[(hperm.idxBij t : ℕ)] = xs[t]
    exact hperm.getElem_idxBij_eq_getElem t
  have hgetE (t : Fin xs.length) : ys.get (e t) = xs.get t := by
    change ys.get (hperm.idxBij t) = xs.get t
    exact hget t
  have hvalue (s : Fin ys.length) : ys.get s = xs.get (e.symm s) := by
    have h := hgetE (e.symm s)
    simpa only [Equiv.apply_symm_apply] using h
  exact (LinearEquiv.piCongrLeft' k
      (fun t => (intervalModule (k := k) (xs.get t)).obj i) e).trans
    (LinearEquiv.piCongrRight (fun s =>
      intervalFiberLinearEquiv (k := k) (hvalue s).symm i))

private theorem barcodeEnumerationLinearEquiv_apply {N : ℕ} {k : Type u} [Field k]
    {xs ys : List (FiniteInterval N)} (hperm : xs.Perm ys) (i : Fin N)
    (x : ∀ t : Fin xs.length, (intervalModule (k := k) (xs.get t)).obj i)
    (hvalues : ∀ s : Fin ys.length,
      ys.get s = xs.get ((barcodeEnumerationIndexEquiv hperm).symm s))
    (s : Fin ys.length) :
    barcodeEnumerationLinearEquiv (k := k) hperm i x s =
      intervalFiberLinearEquiv (k := k) (hvalues s).symm i
        (x ((barcodeEnumerationIndexEquiv hperm).symm s)) := by
  classical
  let e := barcodeEnumerationIndexEquiv hperm
  change (LinearEquiv.piCongrLeft' k
      (fun t => (intervalModule (k := k) (xs.get t)).obj i) e).trans
    (LinearEquiv.piCongrRight (fun s =>
      intervalFiberLinearEquiv (k := k) (hvalues s).symm i)) x s =
    intervalFiberLinearEquiv (k := k) (hvalues s).symm i (x (e.symm s))
  rw [LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
    LinearEquiv.piCongrLeft'_apply]

/-- Reordering a finite barcode enumeration gives an isomorphism of persistence modules.

The component at each index reindexes the finite product along `List.Perm.idxBij`; its naturality
is the coordinatewise naturality of the interval structure maps. -/
noncomputable def barcodeEnumerationNatIso {N : ℕ} {k : Type u} [Field k]
    {xs ys : List (FiniteInterval N)} (hperm : xs.Perm ys) :
    barcodeModuleOfList (k := k) xs ≅ barcodeModuleOfList (k := k) ys := by
  classical
  refine NatIso.ofComponents
    (fun i => by
      dsimp [barcodeModuleOfList]
      exact (barcodeEnumerationLinearEquiv (k := k) hperm i).toModuleIso) ?_
  intro i j f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  dsimp [barcodeModuleOfList]
  letI : BEq (FiniteInterval N) := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq (FiniteInterval N) := inferInstance
  let e := barcodeEnumerationIndexEquiv hperm
  have hget (t : Fin xs.length) : ys.get (hperm.idxBij t) = xs.get t := by
    change ys[(hperm.idxBij t : ℕ)] = xs[t]
    exact hperm.getElem_idxBij_eq_getElem t
  have hgetE (t : Fin xs.length) : ys.get (e t) = xs.get t := by
    change ys.get (hperm.idxBij t) = xs.get t
    exact hget t
  have hvalues (s : Fin ys.length) : ys.get s = xs.get (e.symm s) := by
    have h := hgetE (e.symm s)
    simpa only [Equiv.apply_symm_apply] using h
  change barcodeEnumerationLinearEquiv (k := k) hperm j
      (fun t => structureMapLinear (intervalModule (k := k) (xs.get t)) (leOfHom f) (x t)) s =
    structureMapLinear (intervalModule (k := k) (ys.get s)) (leOfHom f)
      (barcodeEnumerationLinearEquiv (k := k) hperm i x s)
  rw [barcodeEnumerationLinearEquiv_apply (k := k) (hperm := hperm) (i := j)
      (x := fun t => structureMapLinear (intervalModule (k := k) (xs.get t))
        (leOfHom f) (x t)) (hvalues := hvalues) (s := s),
    barcodeEnumerationLinearEquiv_apply (k := k) (hperm := hperm) (i := i)
      (x := x) (hvalues := hvalues) (s := s)]
  exact intervalFiberLinearEquiv_natural (k := k) (hvalues s).symm (leOfHom f)
    (x (e.symm s))

private noncomputable def rangePiMapToPiRange {ι : Type*} {k : Type*} [Field k]
    {A B : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
    (f : ∀ i, A i →ₗ[k] B i) (x : LinearMap.range (LinearMap.piMap f)) :
    ∀ i, LinearMap.range (f i) := by
  classical
  exact fun i => by
    let x₀ := Classical.choose (LinearMap.mem_range.mp x.property)
    have hx₀ : LinearMap.piMap f x₀ = x.1 :=
      Classical.choose_spec (LinearMap.mem_range.mp x.property)
    refine ⟨x.1 i, ?_⟩
    refine ⟨x₀ i, ?_⟩
    simpa [LinearMap.piMap] using congrFun hx₀ i

private noncomputable def piRangeToRangePiMap {ι : Type*} {k : Type*} [Field k]
    {A B : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
    (f : ∀ i, A i →ₗ[k] B i) (y : ∀ i, LinearMap.range (f i)) :
    LinearMap.range (LinearMap.piMap f) := by
  classical
  refine ⟨LinearMap.piMap f (fun i => Classical.choose (LinearMap.mem_range.mp (y i).property)), ?_⟩
  exact LinearMap.mem_range.mpr ⟨_, rfl⟩

private theorem piRangeToRangePiMap_val {ι : Type*} {k : Type*} [Field k]
    {A B : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
    (f : ∀ i, A i →ₗ[k] B i) (y : ∀ i, LinearMap.range (f i)) :
    (piRangeToRangePiMap f y).val = fun i => (y i).val := by
  classical
  funext i
  simp [piRangeToRangePiMap, LinearMap.piMap,
    Classical.choose_spec (LinearMap.mem_range.mp (y i).property)]

private noncomputable def rangePiMapEquiv {ι : Type*} {k : Type*} [Field k]
    {A B : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
    (f : ∀ i, A i →ₗ[k] B i) :
    LinearMap.range (LinearMap.piMap f) ≃ₗ[k]
      (∀ i, LinearMap.range (f i)) where
  toFun := rangePiMapToPiRange f
  invFun := piRangeToRangePiMap f
  left_inv x := by
    apply Subtype.ext
    ext i
    simp [piRangeToRangePiMap_val, rangePiMapToPiRange]
  right_inv y := by
    funext i
    apply Subtype.ext
    simp [piRangeToRangePiMap_val, rangePiMapToPiRange]
  map_add' x y := by
    funext i
    apply Subtype.ext
    simp [rangePiMapToPiRange]
  map_smul' c x := by
    funext i
    apply Subtype.ext
    simp [rangePiMapToPiRange]

private theorem finrank_range_piMap {ι : Type*} [Fintype ι] {k : Type*} [Field k]
    {A B : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
    [∀ i, FiniteDimensional k (A i)]
    (f : ∀ i, A i →ₗ[k] B i) :
    Module.finrank k (LinearMap.range (LinearMap.piMap f)) =
      ∑ i, Module.finrank k (LinearMap.range (f i)) := by
  classical
  rw [(rangePiMapEquiv f).finrank_eq, Module.finrank_pi_fintype]

private theorem list_get_sum_countP {α : Type*} (xs : List α) (p : α → Prop)
    [DecidablePred p] :
    (∑ t : Fin xs.length, if p (xs.get t) then 1 else 0) =
      (xs : Multiset α).countP p := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      change (∑ t : Fin (xs.length + 1),
        if p ((a :: xs).get t) then 1 else 0) = (↑(a :: xs) : Multiset α).countP p
      rw [Fin.sum_univ_succ]
      change (if p a then 1 else 0) +
        (∑ t : Fin xs.length, if p (xs.get t) then 1 else 0) =
          (↑(a :: xs) : Multiset α).countP p
      simp only [Multiset.coe_countP, List.countP_cons]
      simp only [Multiset.coe_countP] at ih
      rw [ih]
      simp [add_comm]

/-- The rank of the barcode structure map is the number of active interval summands.

Rank is computed from the range of the actual structure map, then its finite-product range is
identified with the product of coordinate ranges. -/
theorem rank_barcodeMap {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (i j : Fin N) (hij : i ≤ j) :
    structureMapRank (barcodeModule (k := k) B) i j hij =
      B.countP (fun I => I.birth ≤ i.val ∧ j.val < I.death) := by
  classical
  let f : ∀ t : BarcodeOccurrence N B,
      ((intervalModule (k := k) (B.toList.get t)).obj i) →ₗ[k]
        ((intervalModule (k := k) (B.toList.get t)).obj j) :=
    fun t => structureMapLinear (intervalModule (k := k) (B.toList.get t)) hij
  change Module.finrank k (LinearMap.range (LinearMap.piMap f)) = _
  rw [finrank_range_piMap f]
  calc
    (∑ t : BarcodeOccurrence N B, Module.finrank k (LinearMap.range (f t))) =
        ∑ t : BarcodeOccurrence N B,
          if (B.toList.get t).birth ≤ i.val ∧ j.val < (B.toList.get t).death then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      change Module.finrank k (LinearMap.range
        (structureMapLinear (intervalModule (k := k) (B.toList.get t)) hij)) = _
      change Module.finrank k (LinearMap.range
        (intervalMap (k := k) (B.toList.get t) hij)) = _
      simpa only [interval_alive_endpoints_iff (B.toList.get t) hij] using
        (intervalMap_finrank_range (k := k) (B.toList.get t) hij)
    _ = B.countP (fun I => I.birth ≤ i.val ∧ j.val < I.death) := by
      simpa only [Multiset.coe_toList] using
        (list_get_sum_countP B.toList (fun I => I.birth ≤ i.val ∧ j.val < I.death))

/-- The integer rank table, extended by zero outside valid ordered index pairs. -/
noncomputable def barcodeRankInteger {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (i j : ℤ) : ℤ := by
  classical
  exact if h : 0 ≤ i ∧ i ≤ j ∧ j < (N : ℤ) then
    let hi : (i.toNat : ℤ) = i := Int.toNat_of_nonneg h.1
    let hj : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (h.1.trans h.2.1)
    let fi : Fin N := ⟨i.toNat, by
      have hlt : i < (N : ℤ) := h.2.1.trans_lt h.2.2
      have hlt' : (i.toNat : ℤ) < (N : ℤ) := by rw [hi]; exact hlt
      exact_mod_cast hlt'⟩
    let fj : Fin N := ⟨j.toNat, by
      have hlt' : (j.toNat : ℤ) < (N : ℤ) := by rw [hj]; exact h.2.2
      exact_mod_cast hlt'⟩
    let hFin : fi ≤ fj := Fin.le_iff_val_le_val.mpr (by
      have hle : (i.toNat : ℤ) ≤ (j.toNat : ℤ) := by rw [hi, hj]; exact h.2.1
      exact_mod_cast hle)
    (structureMapRank (barcodeModule (k := k) B) fi fj hFin : ℤ)
  else 0

/-- At natural valid indices, the integer extension is the cast of the actual range rank. -/
theorem barcodeRankInteger_nat {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (i j : ℕ) (hij : i ≤ j) (hj : j < N) :
    barcodeRankInteger (k := k) B (i : ℤ) (j : ℤ) =
      (B.countP (fun I => I.birth ≤ i ∧ j < I.death) : ℤ) := by
  classical
  have h : 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) < (N : ℤ) := by omega
  simp [barcodeRankInteger, h, rank_barcodeMap]

/-- Negative indices are the explicit left boundary sentinel. -/
@[simp] theorem barcodeRankInteger_neg_one {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (j : ℤ) :
    barcodeRankInteger (k := k) B (-1) j = 0 := by
  classical
  simp [barcodeRankInteger]

/-- The index `N` is the explicit right boundary sentinel. -/
@[simp] theorem barcodeRankInteger_at_size {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (i : ℤ) :
    barcodeRankInteger (k := k) B i (N : ℤ) = 0 := by
  classical
  simp [barcodeRankInteger]

/-- Multiplicity is the count of occurrences with the specified endpoints. -/
def barcodeMultiplicity {N : ℕ} (B : Multiset (FiniteInterval N)) (b d : ℕ) : ℕ :=
  B.countP (fun I => I.birth = b ∧ I.death = d)

private theorem interval_indicator_difference {N : ℕ} (I : FiniteInterval N)
    (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    (if I.birth ≤ b ∧ d - 1 < I.death then (1 : ℤ) else 0) -
      (if 0 < b ∧ I.birth ≤ b - 1 ∧ d - 1 < I.death then 1 else 0) -
      (if d < N ∧ I.birth ≤ b ∧ d < I.death then 1 else 0) +
      (if 0 < b ∧ d < N ∧ I.birth ≤ b - 1 ∧ d < I.death then 1 else 0) =
        if I.birth = b ∧ I.death = d then 1 else 0 := by
  classical
  have hI : I.birth < I.death := I.birth_lt_death
  have hIN : I.death ≤ N := I.death_le_size
  by_cases hb : 0 < b
  by_cases hdN : d < N
  by_cases hbirth : I.birth ≤ b
  by_cases hbirthPrev : I.birth ≤ b - 1
  by_cases hdeathPrev : d - 1 < I.death
  by_cases hdeath : d < I.death
  all_goals
    simp_all
    omega

private theorem multiset_four_difference {N : ℕ}
    (B : Multiset (FiniteInterval N)) (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    (B.countP (fun I => I.birth ≤ b ∧ d - 1 < I.death) : ℤ) -
      (B.countP (fun I => 0 < b ∧ I.birth ≤ b - 1 ∧ d - 1 < I.death) : ℤ) -
      (B.countP (fun I => d < N ∧ I.birth ≤ b ∧ d < I.death) : ℤ) +
      (B.countP (fun I => 0 < b ∧ d < N ∧ I.birth ≤ b - 1 ∧ d < I.death) : ℤ) =
        (barcodeMultiplicity B b d : ℤ) := by
  classical
  induction B using Multiset.induction_on with
  | empty => simp [barcodeMultiplicity]
  | cons I B ih =>
      simp only [Multiset.countP_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        barcodeMultiplicity]
      simp only [barcodeMultiplicity] at ih
      have hsingle := interval_indicator_difference I b d hbd hd
      omega

private theorem barcodeRankInteger_birth_deathPrev {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    barcodeRankInteger (k := k) B (b : ℤ) ((d : ℤ) - 1) =
      (B.countP (fun I => I.birth ≤ b ∧ d - 1 < I.death) : ℤ) := by
  have hdpos : 0 < d := by omega
  have hbd' : b ≤ d - 1 := by omega
  have hd' : d - 1 < N := by omega
  have hcast : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [← hcast]
  exact barcodeRankInteger_nat B b (d - 1) hbd' hd'

private theorem barcodeRankInteger_birthPrev_deathPrev {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    barcodeRankInteger (k := k) B ((b : ℤ) - 1) ((d : ℤ) - 1) =
      (B.countP (fun I => 0 < b ∧ I.birth ≤ b - 1 ∧ d - 1 < I.death) : ℤ) := by
  by_cases hb : b = 0
  · have hcast : (b : ℤ) - 1 = -1 := by omega
    rw [hcast, barcodeRankInteger_neg_one]
    simp [hb]
  · have hbpos : 0 < b := by omega
    have hdpos : 0 < d := by omega
    have hbcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
    have hdcast : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
    rw [← hbcast, ← hdcast]
    simpa only [hbpos, true_and] using
      (barcodeRankInteger_nat (k := k) B (b - 1) (d - 1) (by omega) (by omega))

private theorem barcodeRankInteger_birth_death {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    barcodeRankInteger (k := k) B (b : ℤ) (d : ℤ) =
      (B.countP (fun I => d < N ∧ I.birth ≤ b ∧ d < I.death) : ℤ) := by
  by_cases hdN : d = N
  · have hcast : (d : ℤ) = (N : ℤ) := by exact_mod_cast hdN
    rw [hcast, barcodeRankInteger_at_size]
    simp [hdN]
  · have hdlt : d < N := by omega
    simpa only [hdlt, true_and] using
      (barcodeRankInteger_nat (k := k) B b d (by omega) hdlt)

private theorem barcodeRankInteger_birthPrev_death {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    barcodeRankInteger (k := k) B ((b : ℤ) - 1) (d : ℤ) =
      (B.countP (fun I => 0 < b ∧ d < N ∧ I.birth ≤ b - 1 ∧ d < I.death) : ℤ) := by
  by_cases hb : b = 0
  · have hcast : (b : ℤ) - 1 = -1 := by omega
    rw [hcast, barcodeRankInteger_neg_one]
    simp [hb]
  · have hbpos : 0 < b := by omega
    by_cases hdN : d = N
    · have hcast : (d : ℤ) = (N : ℤ) := by exact_mod_cast hdN
      rw [hcast, barcodeRankInteger_at_size]
      simp [hdN]
    · have hdlt : d < N := by omega
      have hbcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      rw [← hbcast]
      simpa only [hbpos, hdlt, true_and] using
        (barcodeRankInteger_nat (k := k) B (b - 1) d (by omega) hdlt)

/-- The four integer rank differences recover every endpoint multiplicity.

The predecessor is taken in `ℤ`, so `b = 0` produces the explicit `-1` sentinel rather than
truncated natural subtraction. -/
theorem multiplicity_eq_rank_difference {N : ℕ} {k : Type u} [Field k]
    (B : Multiset (FiniteInterval N)) (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    (barcodeMultiplicity B b d : ℤ) =
      barcodeRankInteger (k := k) B (b : ℤ) ((d : ℤ) - 1) -
        barcodeRankInteger (k := k) B ((b : ℤ) - 1) ((d : ℤ) - 1) -
        barcodeRankInteger (k := k) B (b : ℤ) (d : ℤ) +
        barcodeRankInteger (k := k) B ((b : ℤ) - 1) (d : ℤ) := by
  rw [barcodeRankInteger_birth_deathPrev B b d hbd hd,
    barcodeRankInteger_birthPrev_deathPrev B b d hbd hd,
    barcodeRankInteger_birth_death B b d hbd hd,
    barcodeRankInteger_birthPrev_death B b d hbd hd]
  exact (multiset_four_difference B b d hbd hd).symm

/-- Equal integer rank tables determine the finite barcode multiset uniquely.

The proof recovers the count of each valid endpoint pair from the four-rank formula, then uses
extensionality of finite multisets. This concerns only the explicitly constructed realizations
`barcodeModule B`; it makes no assertion that an arbitrary persistence module decomposes. -/
theorem barcodeRankInteger_injective {N : ℕ} {k : Type u} [Field k]
    {B C : Multiset (FiniteInterval N)}
    (h : ∀ i j : ℤ, barcodeRankInteger (k := k) B i j =
      barcodeRankInteger (k := k) C i j) : B = C := by
  classical
  have hm (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
      barcodeMultiplicity B b d = barcodeMultiplicity C b d := by
    have hB := multiplicity_eq_rank_difference (k := k) B b d hbd hd
    have hC := multiplicity_eq_rank_difference (k := k) C b d hbd hd
    have hcast : (barcodeMultiplicity B b d : ℤ) = barcodeMultiplicity C b d := by
      rw [hB, hC, h (b : ℤ) ((d : ℤ) - 1), h ((b : ℤ) - 1) ((d : ℤ) - 1),
        h (b : ℤ) (d : ℤ), h ((b : ℤ) - 1) (d : ℤ)]
    exact_mod_cast hcast
  apply Multiset.ext'
  intro I
  have hpred (J : FiniteInterval N) :
      (J.birth = I.birth ∧ J.death = I.death) ↔ J = I := by
    constructor
    · rintro ⟨hb, hd⟩
      cases J with
      | mk jb jd hjb hjd =>
        cases I with
        | mk ib id hib hid =>
          simp_all
    · intro h
      subst J
      exact ⟨rfl, rfl⟩
  have hB := hm I.birth I.death I.birth_lt_death I.death_le_size
  have hBcount : B.count I = barcodeMultiplicity B I.birth I.death := by
    simpa [barcodeMultiplicity, Multiset.count, eq_comm] using
      (Multiset.countP_congr (s := B) (s' := B) rfl
        (fun J _ => propext (hpred J)))
  have hCcount : C.count I = barcodeMultiplicity C I.birth I.death := by
    simpa [barcodeMultiplicity, Multiset.count, eq_comm] using
      (Multiset.countP_congr (s := C) (s' := C) rfl
        (fun J _ => propext (hpred J)))
  rw [hBcount, hCcount, hB]

/-- With no observed stages, the empty barcode has the zero integer rank table. -/
@[simp] theorem emptyBarcode_rank_N0 {k : Type u} [Field k] (i j : ℤ) :
    barcodeRankInteger (k := k) (N := 0) (0 : Multiset (FiniteInterval 0)) i j = 0 := by
  classical
  unfold barcodeRankInteger
  split
  · rename_i h
    omega
  · rfl

/-- The bar `[0,1)` has rank one on the only observed structure map. -/
theorem rank_single_fullInterval_N1 {k : Type u} [Field k] :
    let I : FiniteInterval 1 := ⟨0, 1, by omega, by omega⟩
    structureMapRank (barcodeModule (k := k) ({I} : Multiset (FiniteInterval 1)))
      (0 : Fin 1) 0 (by omega) = 1 := by
  classical
  dsimp
  rw [rank_barcodeMap]
  change Multiset.countP (fun x : FiniteInterval 1 => x.birth = 0 ∧ 0 < x.death)
    ((⟨0, 1, by omega, by omega⟩ : FiniteInterval 1) ::ₘ 0) = 1
  rw [Multiset.countP_cons_of_pos (s := 0) (by simp)]
  simp

/-- A bar spanning `[0,N)` has rank one from the first to the last observed stage. -/
theorem rank_fullObservedInterval {N : ℕ} {k : Type u} [Field k] (hN : 0 < N) :
    let I : FiniteInterval N := ⟨0, N, by omega, by omega⟩
    structureMapRank (barcodeModule (k := k) ({I} : Multiset (FiniteInterval N)))
      ⟨0, by omega⟩ ⟨N - 1, by omega⟩ (by
        apply Fin.le_iff_val_le_val.mpr
        change (0 : ℕ) ≤ N - 1
        omega) = 1 := by
  classical
  dsimp
  rw [rank_barcodeMap]
  change Multiset.countP (fun I : FiniteInterval N => I.birth ≤ 0 ∧ N - 1 < I.death)
    ((⟨0, N, by omega, by omega⟩ : FiniteInterval N) ::ₘ 0) = 1
  rw [Multiset.countP_cons_of_pos (s := 0) (by simp; omega)]
  simp

/-- Two copies of `[0,1)` remain two distinct barcode occurrences and contribute rank two. -/
theorem rank_duplicate_fullInterval_N1 {k : Type u} [Field k] :
    let I : FiniteInterval 1 := ⟨0, 1, by omega, by omega⟩
    structureMapRank (barcodeModule (k := k)
      (({I} : Multiset (FiniteInterval 1)) + {I})) (0 : Fin 1) 0 (by omega) = 2 := by
  classical
  dsimp
  rw [rank_barcodeMap]
  change Multiset.countP (fun x : FiniteInterval 1 => x.birth ≤ 0 ∧ 0 < x.death)
    ((⟨0, 1, by omega, by omega⟩ : FiniteInterval 1) ::ₘ
      ((⟨0, 1, by omega, by omega⟩ : FiniteInterval 1) ::ₘ 0)) = 2
  rw [Multiset.countP_cons_of_pos (s := _ ::ₘ 0) (by norm_num),
    Multiset.countP_cons_of_pos (s := 0) (by norm_num)]
  simp

/-- For the full observed interval `[0,N)`, the multiplicity four-difference applies at both
boundary conventions: birth zero uses `-1`, and death `N` uses the right sentinel. -/
theorem fullInterval_boundary_difference {N : ℕ} {k : Type u} [Field k] (hN : 0 < N) :
    let I : FiniteInterval N := ⟨0, N, by omega, by omega⟩
    let B : Multiset (FiniteInterval N) := {I}
    (barcodeMultiplicity B 0 N : ℤ) =
      barcodeRankInteger (k := k) B (0 : ℤ) ((N : ℤ) - 1) -
        barcodeRankInteger (k := k) B (-1) ((N : ℤ) - 1) -
        barcodeRankInteger (k := k) B (0 : ℤ) (N : ℤ) +
        barcodeRankInteger (k := k) B (-1) (N : ℤ) := by
  dsimp
  exact multiplicity_eq_rank_difference (k := k) _ 0 N (by omega) (by omega)

/-- The four integer rank terms at birth zero and death `N` evaluate to one for the full bar. -/
theorem fullInterval_boundary_rank_sum_one {N : ℕ} {k : Type u} [Field k]
    (hN : 0 < N) :
    let I : FiniteInterval N := ⟨0, N, by omega, by omega⟩
    let B : Multiset (FiniteInterval N) := {I}
    barcodeRankInteger (k := k) B (0 : ℤ) ((N : ℤ) - 1) -
      barcodeRankInteger (k := k) B (-1) ((N : ℤ) - 1) -
      barcodeRankInteger (k := k) B (0 : ℤ) (N : ℤ) +
      barcodeRankInteger (k := k) B (-1) (N : ℤ) = 1 := by
  classical
  dsimp
  have hfirst : barcodeRankInteger (k := k)
      (({(⟨0, N, by omega, by omega⟩ : FiniteInterval N)} : Multiset _))
      (0 : ℤ) ((N : ℤ) - 1) = 1 := by
    have hnat := barcodeRankInteger_nat (k := k)
      (({(⟨0, N, by omega, by omega⟩ : FiniteInterval N)} : Multiset _))
      0 (N - 1) (by omega) (by omega)
    have hcast : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    rw [← hcast]
    change barcodeRankInteger (k := k)
      (({(⟨0, N, by omega, by omega⟩ : FiniteInterval N)} : Multiset _))
      ((0 : ℕ) : ℤ) ((N - 1 : ℕ) : ℤ) = 1
    rw [hnat]
    change (Multiset.countP
      (fun I : FiniteInterval N => I.birth ≤ 0 ∧ N - 1 < I.death)
      ((⟨0, N, by omega, by omega⟩ : FiniteInterval N) ::ₘ 0) : ℤ) = 1
    rw [Multiset.countP_cons_of_pos (s := 0) (by simp; omega)]
    simp
  rw [hfirst, barcodeRankInteger_neg_one, barcodeRankInteger_at_size,
    barcodeRankInteger_neg_one]
  norm_num

private instance identityTransitionDiagram_finiteDimensional {k : Type u} [Field k]
    (i : Fin 2) : FiniteDimensional k ((identityTransitionDiagram k).obj i) := by
  unfold identityTransitionDiagram
  dsimp
  infer_instance

private instance zeroTransitionDiagram_finiteDimensional {k : Type u} [Field k]
    (i : Fin 2) : FiniteDimensional k ((zeroTransitionDiagram k).obj i) := by
  unfold zeroTransitionDiagram
  dsimp
  infer_instance

/-- Equal-dimensional two-stage modules can have different actual structure-map ranks. -/
theorem equal_dimensions_different_structureMapRanks {k : Type u} [Field k] :
    (∀ i : Fin 2,
      Module.finrank k ((identityTransitionDiagram k).obj i) =
        Module.finrank k ((zeroTransitionDiagram k).obj i)) ∧
      structureMapRank (identityTransitionDiagram k) (0 : Fin 2) 1 (by omega) = 1 ∧
      structureMapRank (zeroTransitionDiagram k) (0 : Fin 2) 1 (by omega) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change Module.finrank k k = Module.finrank k k
    rfl
  · change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = 1
    rw [LinearMap.range_id]
    rw [finrank_top]
    exact Module.finrank_self k
  · change Module.finrank k (LinearMap.range (0 : k →ₗ[k] k)) = 0
    rw [LinearMap.range_zero]
    simp

end TDA.Persistence
