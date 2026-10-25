import TDA.Persistence.FinitePresentationRankProjectiveClassification
import TDA.Persistence.FinitePresentationHookKernel
import Mathlib.Tactic

/-!
# Consumers of the finitely-presented real rank-projective classification

The examples exercise finite-death and infinite-death hooks, repeated
occurrences, the empty sum, and equality of multiplicities after reordering a
mixed ambient sum. The classification examples come from actual finite
coordinate grids, so their hypotheses match the public theorem.
-/

set_option autoImplicit false

namespace TDA.Persistence.FinitePresentationRankProjectiveClassification.Examples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.GradedFree
open TDA.Persistence.FiniteRankProjectiveClassification
open scoped TDA.Persistence ZeroObject

abbrev P := Fin 1 → ℝ

private noncomputable abbrev grid : CoordinateGrid 1 := fun _ => {0, 1}

private noncomputable def gridOrigin : grid.Point := fun i =>
  ⟨0, by norm_num [grid]⟩

private noncomputable def gridTop : grid.Point := fun i =>
  ⟨1, by norm_num [grid]⟩

private theorem gridOrigin_lt_top : gridOrigin < gridTop := by
  apply lt_of_le_of_ne
  · intro i
    fin_cases i
    change (0 : ℝ) ≤ 1
    norm_num
  · intro h
    have h0 := congrArg (fun p : grid.Point => (p 0).val) h
    norm_num [gridOrigin, gridTop] at h0

private noncomputable abbrev birth : P := grid.embedding gridOrigin

private noncomputable abbrev death : P := grid.embedding gridTop

private theorem birth_lt_death : birth < death :=
  grid.embedding.strictMono gridOrigin_lt_top

private theorem finiteHook_finitelyPresented :
    FinitelyPresented (R := ℚ) (P := P) (Hook.module (k := ℚ) birth death) := by
  let A : PModule ℚ grid.Point := Hook.module (k := ℚ) gridOrigin gridTop
  have hA : FinitelyPresented (R := ℚ) (P := grid.Point) A :=
    GradedFree.pfd_finitelyPresented_of_finite_poset A (by
      intro p
      infer_instance)
  have hLan : FinitelyPresented (R := ℚ) (P := P) (grid.lan.obj A) :=
    GradedFree.finitelyPresented_lan_of_finiteGrid grid hA
  exact GradedFree.finitelyPresented_of_iso hLan (grid.hookLanIso gridOrigin gridTop)

private theorem infinityHook_finitelyPresented :
    FinitelyPresented (R := ℚ) (P := P) (HookInfinity.module (R := ℚ) birth) := by
  let A : PModule ℚ grid.Point := HookInfinity.module (R := ℚ) gridOrigin
  have hA : FinitelyPresented (R := ℚ) (P := grid.Point) A :=
    GradedFree.pfd_finitelyPresented_of_finite_poset A (by
      intro p
      infer_instance)
  have hLan : FinitelyPresented (R := ℚ) (P := P) (grid.lan.obj A) :=
    GradedFree.finitelyPresented_lan_of_finiteGrid grid hA
  exact GradedFree.finitelyPresented_of_iso hLan (grid.infinityLanIso gridOrigin)

/-- The theorem classifies a concrete nonzero finite-death hook. -/
theorem nonzero_finite_hook_classifies :
    (∃ x : (Hook.module (k := ℚ) birth death).obj birth, x ≠ 0) ∧
      ∃ m : ℕ, ∃ t : Fin m → RankProjectiveHookTag P,
        Nonempty (Hook.module (k := ℚ) birth death ≅
          ⨁ fun i => rankProjectiveHookModule (k := ℚ) (t i)) := by
  constructor
  · refine ⟨SupportInterval.one (Hook.support birth death)
      (Hook.birth_mem birth_lt_death), ?_⟩
    intro h
    have hv := congrArg Subtype.val h
    simp [SupportInterval.one] at hv
  · exact (GradedFree.finitelyPresented_rankProjective_iff_exists_hook_sum
      (k := ℚ) (n := 1) (M := Hook.module (k := ℚ) birth death)
      (by norm_num) finiteHook_finitelyPresented).mp
        (Hook.isRankProjective birth_lt_death)

/-- The principal upset has a nonzero fiber above every grade, and the theorem
classifies it using the infinite-death tag. -/
theorem unbounded_principal_upset_classifies :
    (∀ r : P, ∃ a : P, r ≤ a ∧
      ∃ x : (HookInfinity.module (R := ℚ) birth).obj a, x ≠ 0) ∧
      ∃ m : ℕ, ∃ t : Fin m → RankProjectiveHookTag P,
        Nonempty (HookInfinity.module (R := ℚ) birth ≅
          ⨁ fun i => rankProjectiveHookModule (k := ℚ) (t i)) := by
  constructor
  · intro r
    let a : P := fun i => max (birth i) (r i)
    have hba : birth ≤ a := by
      intro i
      exact le_max_left _ _
    have hra : r ≤ a := by
      intro i
      exact le_max_right _ _
    let e := HookInfinity.fiberEquivOfLe (R := ℚ) hba
    refine ⟨a, hra, e.symm 1, ?_⟩
    intro hx
    have hone := congrArg e hx
    exact (one_ne_zero : (1 : ℚ) ≠ 0) (by simpa using hone)
  · exact (GradedFree.finitelyPresented_rankProjective_iff_exists_hook_sum
      (k := ℚ) (n := 1) (M := HookInfinity.module (R := ℚ) birth)
      (by norm_num) infinityHook_finitelyPresented).mp
        (HookInfinity.isRankProjective birth)

private noncomputable def finiteTag : RankProjectiveHookTag P :=
  .inl ⟨(birth, death), birth_lt_death⟩

private noncomputable def infiniteTag : RankProjectiveHookTag P := .inr birth

private noncomputable def mixedHookTags : Fin 3 → RankProjectiveHookTag P := fun i =>
  if i.val = 1 then infiniteTag else finiteTag

/-- Reordering a mixed sum with repeated finite hooks preserves every
finite-death and infinite-death occurrence count. -/
theorem reordered_mixed_hook_sum_preserves_every_multiplicity
    (c : RankProjectiveHookTag P) :
    Fintype.card {i : Fin 3 // mixedHookTags i = c} =
      Fintype.card {i : Fin 3 // mixedHookTags (Equiv.swap (0 : Fin 3) 1 i) = c} := by
  classical
  let σ : Fin 3 ≃ Fin 3 := Equiv.swap (0 : Fin 3) 1
  let reordered : Fin 3 → RankProjectiveHookTag P := fun i => mixedHookTags (σ i)
  have hReordered : (fun i : Fin 3 =>
      rankProjectiveHookModule (k := ℚ) (reordered i)) =
      (fun i : Fin 3 => rankProjectiveHookModule (k := ℚ) (mixedHookTags i)) ∘ σ := by
    funext i
    rfl
  have e : (⨁ fun i : Fin 3 =>
      rankProjectiveHookModule (k := ℚ) (mixedHookTags i)) ≅
      ⨁ fun i : Fin 3 => rankProjectiveHookModule (k := ℚ) (reordered i) := by
    simpa only [hReordered] using
      (biproduct.reindex σ
        (fun i : Fin 3 => rankProjectiveHookModule (k := ℚ) (mixedHookTags i))).symm
  simpa [σ, reordered] using
    GradedFree.rankProjectiveHookSum_multiplicity_unique_of_iso
      (k := ℚ) (n := 1) mixedHookTags reordered ⟨e⟩ c

/-- Empty occurrence families have equal multiplicity for every real tag. -/
theorem empty_hook_sums_have_equal_every_multiplicity
    (c : RankProjectiveHookTag P) :
    Fintype.card {i : Fin 0 // (Fin.elim0 i : RankProjectiveHookTag P) = c} =
      Fintype.card {i : Fin 0 // (Fin.elim0 i : RankProjectiveHookTag P) = c} := by
  exact GradedFree.rankProjectiveHookSum_multiplicity_unique_of_iso
    (k := ℚ) (n := 1) Fin.elim0 Fin.elim0 ⟨Iso.refl
      (⨁ fun i : Fin 0 => rankProjectiveHookModule (k := ℚ)
        (Fin.elim0 i : RankProjectiveHookTag P))⟩ c

private theorem repeatedFiniteHook_finitelyPresented :
    FinitelyPresented (R := ℚ) (P := P)
      (⨁ fun _ : Fin 2 => rankProjectiveHookModule (k := ℚ) finiteTag) := by
  let A : Fin 2 → PModule ℚ grid.Point := fun _ =>
    Hook.module (k := ℚ) gridOrigin gridTop
  have hA : FinitelyPresented (R := ℚ) (P := grid.Point) (⨁ A) :=
    GradedFree.pfd_finitelyPresented_of_finite_poset (⨁ A) (by
      intro p
      letI : ∀ i, FiniteDimensional ℚ ((A i).obj p) := by
        intro i
        dsimp [A]
        infer_instance
      letI : FiniteDimensional ℚ (∀ i, (A i).obj p) := by
        infer_instance
      exact (FiniteBiproduct.fiberIsoPi A p).symm.toLinearEquiv.finiteDimensional)
  have hLan : FinitelyPresented (R := ℚ) (P := P) (grid.lan.obj (⨁ A)) :=
    GradedFree.finitelyPresented_lan_of_finiteGrid grid hA
  have e : grid.lan.obj (⨁ A) ≅
      ⨁ fun _ : Fin 2 => rankProjectiveHookModule (k := ℚ) finiteTag := by
    simpa [A, finiteTag, rankProjectiveHookModule, birth, death] using
      (grid.lanBiproductIso A).trans
        (biproduct.mapIso (fun _ : Fin 2 => grid.hookLanIso gridOrigin gridTop))
  exact GradedFree.finitelyPresented_of_iso hLan e

/-- Two repeated nonzero hooks remain two occurrences in the classified sum. -/
theorem repeated_finite_hook_classifies :
    IsRankProjective (⨁ fun _ : Fin 2 => rankProjectiveHookModule (k := ℚ) finiteTag) ∧
      ∃ m : ℕ, ∃ t : Fin m → RankProjectiveHookTag P,
        Nonempty ((⨁ fun _ : Fin 2 => rankProjectiveHookModule (k := ℚ) finiteTag) ≅
          ⨁ fun i => rankProjectiveHookModule (k := ℚ) (t i)) := by
  classical
  let M : PModule ℚ P :=
    ⨁ fun _ : Fin 2 => rankProjectiveHookModule (k := ℚ) finiteTag
  let C := GradedFree.finitelyPresented_rankProjective_iff_exists_hook_sum
    (k := ℚ) (n := 1) (M := M) (by norm_num) repeatedFiniteHook_finitelyPresented
  have hRP := C.mpr ⟨2, fun _ : Fin 2 => finiteTag, ⟨Iso.refl M⟩⟩
  exact ⟨hRP, C.mp hRP⟩

private theorem zero_finitelyPresented :
    FinitelyPresented.{0,0,0} (R := ℚ) (P := P) (0 : PModule.{0,0,0} ℚ P) := by
  let W : GradedGenerators.{0,0} P := ⟨Empty, Empty.elim⟩
  letI : Finite W.Carrier := inferInstanceAs (Finite Empty)
  have hz : IsZero (GradedFree.module (R := ℚ) W : PModule.{0,0,0} ℚ P) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply GradedFree.hom_ext_birth W
    intro g
    exact g.elim
  have hfree : FinitelyPresented.{0,0,0} (R := ℚ) (P := P)
      (GradedFree.module (R := ℚ) W) := GradedFree.free_finitelyPresented W
  exact GradedFree.finitelyPresented_of_iso hfree hz.isoZero

private theorem emptyTaggedSum_isZero (t : Fin 0 → RankProjectiveHookTag P) :
    IsZero (⨁ fun i : Fin 0 => rankProjectiveHookModule (k := ℚ) (t i)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext'
  intro i
  exact Fin.elim0 i

/-- The public iff accepts the zero module as the empty tagged sum. -/
theorem zero_empty_tagged_sum_classifies :
    IsRankProjective (0 : PModule ℚ P) ∧
      ∃ t : Fin 0 → RankProjectiveHookTag P,
        Nonempty ((0 : PModule ℚ P) ≅
          ⨁ fun i => rankProjectiveHookModule (k := ℚ) (t i)) := by
  classical
  have ezero : IsZero (0 : PModule ℚ P) := isZero_zero _
  let t : Fin 0 → RankProjectiveHookTag P := Fin.elim0
  let e : (0 : PModule ℚ P) ≅
      ⨁ fun i : Fin 0 => rankProjectiveHookModule (k := ℚ) (t i) :=
    ezero.isoZero ≪≫ (emptyTaggedSum_isZero t).isoZero.symm
  have hRP := (GradedFree.finitelyPresented_rankProjective_iff_exists_hook_sum
    (k := ℚ) (n := 1) (M := (0 : PModule ℚ P)) (by norm_num)
    zero_finitelyPresented).mpr ⟨0, Fin.elim0, ⟨e⟩⟩
  exact ⟨hRP, t, ⟨e⟩⟩

end TDA.Persistence.FinitePresentationRankProjectiveClassification.Examples
