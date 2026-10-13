import TDA.Persistence.FiniteDecompositionSupport
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Finset.Max

/-!
# Extracting an interval summand

A vector born at the earliest nonzero stage generates an interval. A functional at its last
nonzero image gives a natural retraction; the earliest-stage condition handles the birth boundary.
-/

universe u

namespace TDA.Persistence

open CategoryTheory

variable {N : ℕ} {k : Type u} [Field k]

private def extractionInterval (b t : Fin N) (hbt : b ≤ t) : FiniteInterval N :=
  ⟨b.val, t.val + 1, by have := hbt; omega, by omega⟩

private theorem extractionInterval_alive (b t : Fin N) (hbt : b ≤ t) (i : Fin N) :
    (extractionInterval b t hbt).alive i ↔ b ≤ i ∧ i ≤ t := by
  simp only [FiniteInterval.alive, extractionInterval, Fin.le_iff_val_le_val]
  omega

private theorem intervalFiber_eq_zero (I : FiniteInterval N) (i : Fin N)
    (hi : ¬ I.alive i) (x : I.fiber (k := k) i) : x.val = 0 := by
  simpa [FiniteInterval.fiber, hi] using x.property

private noncomputable def extractionInclusionLinear
    (M : PModule.{u,0,u} k (Fin N)) (I : FiniteInterval N)
    (w : ∀ i, M.obj i) (i : Fin N) :
    I.fiber (k := k) i →ₗ[k] M.obj i :=
  (LinearMap.toSpanSingleton k (M.obj i) (w i)).comp (I.fiber i).subtype

private theorem extractionInclusionLinear_apply
    (M : PModule.{u,0,u} k (Fin N)) (I : FiniteInterval N)
    (w : ∀ i, M.obj i) (i : Fin N) (x : I.fiber (k := k) i) :
    extractionInclusionLinear M I w i x = x.val • w i := rfl

private noncomputable def extractionInclusion
    (M : PModule.{u,0,u} k (Fin N)) (b t : Fin N) (hbt : b ≤ t)
    (w : ∀ i, M.obj i)
    (hw : ∀ (i j : Fin N) (_hbi : b ≤ i) (hij : i ≤ j),
      structureMapLinear M hij (w i) = w j)
    (hzero : ∀ i, t < i → w i = 0) :
    intervalModule (k := k) (extractionInterval b t hbt) ⟶ M where
  app i := ModuleCat.ofHom (extractionInclusionLinear M _ w i)
  naturality {i j} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (extractionInterval b t hbt).fiber (k := k) i at x
    change extractionInclusionLinear M _ w j
        (intervalMap _ (leOfHom f) x) =
      structureMapLinear M (leOfHom f) (extractionInclusionLinear M _ w i x)
    rw [extractionInclusionLinear_apply, extractionInclusionLinear_apply, map_smul]
    by_cases hi : (extractionInterval b t hbt).alive i
    · by_cases hj : (extractionInterval b t hbt).alive j
      · rw [hw i j ((extractionInterval_alive b t hbt i).mp hi).1 (leOfHom f)]
        simp [intervalMap, hi, hj]
      · have htj : t < j := by
          have hbi := ((extractionInterval_alive b t hbt i).mp hi).1
          have hij := leOfHom f
          rw [extractionInterval_alive] at hj
          omega
        rw [hw i j ((extractionInterval_alive b t hbt i).mp hi).1 (leOfHom f), hzero j htj]
        simp [intervalMap, hj]
    · have hx := intervalFiber_eq_zero (k := k) _ i hi x
      simp [intervalMap, hi, hx]

private noncomputable def extractionRetractionLinear
    (M : PModule.{u,0,u} k (Fin N)) (b t : Fin N) (hbt : b ≤ t)
    (ell : Module.Dual k (M.obj t)) (i : Fin N) :
    M.obj i →ₗ[k] (extractionInterval b t hbt).fiber (k := k) i := by
  classical
  exact if hi : (extractionInterval b t hbt).alive i then
    (ell.comp (structureMapLinear M ((extractionInterval_alive b t hbt i).mp hi).2)).codRestrict
      _ (fun _ => by simp [FiniteInterval.fiber, hi])
  else 0

private theorem extractionRetractionLinear_active
    (M : PModule.{u,0,u} k (Fin N)) (b t : Fin N) (hbt : b ≤ t)
    (ell : Module.Dual k (M.obj t)) (i : Fin N)
    (hi : (extractionInterval b t hbt).alive i) (x : M.obj i) :
    (extractionRetractionLinear M b t hbt ell i x).val =
      ell (structureMapLinear M ((extractionInterval_alive b t hbt i).mp hi).2 x) := by
  simp [extractionRetractionLinear, hi]

private noncomputable def extractionRetraction
    (M : PModule.{u,0,u} k (Fin N)) (b t : Fin N) (hbt : b ≤ t)
    (hbefore : ∀ i, i < b → ∀ x : M.obj i, x = 0)
    (ell : Module.Dual k (M.obj t)) :
    M ⟶ intervalModule (k := k) (extractionInterval b t hbt) where
  app i := ModuleCat.ofHom (extractionRetractionLinear M b t hbt ell i)
  naturality {i j} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (extractionRetractionLinear M b t hbt ell j
        (structureMapLinear M (leOfHom f) x)).val =
      (intervalMap _ (leOfHom f) (extractionRetractionLinear M b t hbt ell i x)).val
    by_cases hj : (extractionInterval b t hbt).alive j
    · by_cases hi : (extractionInterval b t hbt).alive i
      · rw [extractionRetractionLinear_active M b t hbt ell j hj]
        have hcomp := structureMapLinear_comp M (leOfHom f)
          ((extractionInterval_alive b t hbt j).mp hj).2
        simp only [intervalMap, hi, hj, and_self, ↓reduceDIte,
          Submodule.coe_inclusion]
        rw [extractionRetractionLinear_active M b t hbt ell i hi]
        rw [hcomp]
        rfl
      · have hib : i < b := by
          have hjt := ((extractionInterval_alive b t hbt j).mp hj).2
          have hij := leOfHom f
          rw [extractionInterval_alive] at hi
          omega
        rw [hbefore i hib x]
        simp
    · simp [extractionRetractionLinear, intervalMap, hj]

private theorem extraction_split_identity
    (M : PModule.{u,0,u} k (Fin N)) (b t : Fin N) (hbt : b ≤ t)
    (w : ∀ i, M.obj i)
    (hw : ∀ (i j : Fin N) (_hbi : b ≤ i) (hij : i ≤ j),
      structureMapLinear M hij (w i) = w j)
    (hzero : ∀ i, t < i → w i = 0)
    (hbefore : ∀ i, i < b → ∀ x : M.obj i, x = 0)
    (ell : Module.Dual k (M.obj t)) (hell : ell (w t) = 1) :
    extractionInclusion M b t hbt w hw hzero ≫ extractionRetraction M b t hbt hbefore ell =
      𝟙 (intervalModule (k := k) (extractionInterval b t hbt)) := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (extractionInterval b t hbt).fiber (k := k) i at x
  apply Subtype.ext
  change (extractionRetractionLinear M b t hbt ell i
    (extractionInclusionLinear M _ w i x)).val = x.val
  by_cases hi : (extractionInterval b t hbt).alive i
  · rw [extractionRetractionLinear_active M b t hbt ell i hi,
      extractionInclusionLinear_apply, map_smul, hw i t
        ((extractionInterval_alive b t hbt i).mp hi).1
        ((extractionInterval_alive b t hbt i).mp hi).2, map_smul, hell]
    simp
  · rw [intervalFiber_eq_zero (k := k) _ i hi x]
    simp [extractionRetractionLinear, hi]

/-- A nonzero module on a finite chain contains an interval with a natural retraction.
The inclusion and retraction are constructed from a vector at the earliest nonzero stage and
a dual functional at its last surviving image. -/
theorem exists_interval_retract (M : PModule.{u,0,u} k (Fin N))
    (hne : ∃ i, ∃ v : M.obj i, v ≠ 0) :
    ∃ (I : FiniteInterval N) (ι : intervalModule (k := k) I ⟶ M)
      (π : M ⟶ intervalModule (k := k) I), ι ≫ π = 𝟙 _ := by
  classical
  let births : Finset (Fin N) := Finset.univ.filter (fun i => ∃ v : M.obj i, v ≠ 0)
  have hbirths : births.Nonempty := by
    obtain ⟨i, v, hv⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv⟩⟩
  obtain ⟨b, hb, hbmin⟩ := births.exists_min_image (fun i => i) hbirths
  obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hb).2
  have hbefore (i : Fin N) (hi : i < b) (x : M.obj i) : x = 0 := by
    by_contra hx
    have hbi := hbmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx⟩)
    exact (not_le_of_gt hi) hbi
  let w : ∀ i, M.obj i := fun i => if hi : b ≤ i then structureMapLinear M hi v else 0
  have hwb : w b = v := by simp [w]
  have hw (i j : Fin N) (hbi : b ≤ i) (hij : i ≤ j) :
      structureMapLinear M hij (w i) = w j := by
    dsimp [w]
    rw [dif_pos hbi, dif_pos (hbi.trans hij), structureMapLinear_comp M hbi hij]
    rfl
  let surviving : Finset (Fin N) := Finset.univ.filter (fun i => w i ≠ 0)
  have hsurv : surviving.Nonempty := by
    refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rwa [hwb]
  obtain ⟨t, ht, htmax⟩ := surviving.exists_max_image (fun i => i) hsurv
  have hwt : w t ≠ 0 := (Finset.mem_filter.mp ht).2
  have hbt : b ≤ t := by
    by_contra h
    exact hwt (by simp [w, h])
  have hzero (i : Fin N) (hi : t < i) : w i = 0 := by
    by_contra hwi
    exact (not_le_of_gt hi) (htmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwi⟩))
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one k hwt
  exact ⟨extractionInterval b t hbt, extractionInclusion M b t hbt w hw hzero,
    extractionRetraction M b t hbt hbefore ell,
    extraction_split_identity M b t hbt w hw hzero hbefore ell hell⟩

/-- A nonempty finite interval has strictly positive total stage dimension. -/
theorem totalDimension_intervalModule_pos (I : FiniteInterval N) :
    0 < totalDimension (intervalModule (k := k) I) := by
  classical
  let b : Fin N := ⟨I.birth, I.birth_lt_death.trans_le I.death_le_size⟩
  have hb : I.alive b := ⟨le_rfl, I.birth_lt_death⟩
  have hdim : Module.finrank k ((intervalModule (k := k) I).obj b) = 1 := by
    change Module.finrank k (I.fiber (k := k) b) = 1
    have hf : I.fiber (k := k) b = ⊤ := by simp [FiniteInterval.fiber, hb]
    rw [hf]
    simp
  have hle := Finset.single_le_sum (f := fun i : Fin N =>
    Module.finrank k ((intervalModule (k := k) I).obj i))
    (fun i _ => Nat.zero_le _) (Finset.mem_univ b)
  change Module.finrank k ((intervalModule (k := k) I).obj b) ≤
    totalDimension (intervalModule (k := k) I) at hle
  omega

/-- Extract an interval summand and a pointwise finite-dimensional kernel complement.
The complementary module has strictly smaller total stage dimension. -/
theorem exists_interval_summand (M : PModule.{u,0,u} k (Fin N))
    [∀ i, FiniteDimensional k (M.obj i)] (h : 0 < totalDimension M) :
    ∃ (I : FiniteInterval N) (C : PModule.{u,0,u} k (Fin N)),
      (∀ i, FiniteDimensional k (C.obj i)) ∧
      Nonempty (M ≅ pointwiseProd (intervalModule (k := k) I) C) ∧
      totalDimension C < totalDimension M := by
  have hne : ∃ i, ∃ v : M.obj i, v ≠ 0 := by
    obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp h
    exact ⟨i, Module.finrank_pos_iff_exists_ne_zero.mp hi⟩
  obtain ⟨I, inc, ret, hsplit⟩ := exists_interval_retract M hne
  refine ⟨I, splitComplement ret, fun i => inferInstance, ⟨splitIso inc ret hsplit⟩, ?_⟩
  have hdim := totalDimension_split inc ret hsplit
  have hpos := totalDimension_intervalModule_pos (k := k) I
  omega

end TDA.Persistence
