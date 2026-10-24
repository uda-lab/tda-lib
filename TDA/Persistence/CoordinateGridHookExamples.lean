import TDA.Persistence.FinitePresentationHookCover
import TDA.Persistence.CoordinateGridKanExamples
import TDA.Persistence.FinitePresentationKanExamples
import TDA.Persistence.FiniteHookDeflationExamples
import Mathlib.Tactic

/-!
# Actual coordinate-grid hook comparisons and covers

These fixtures use the actual Kan comparison maps, the existing occurrence
indices and the finite-presentation capstone. They include an unbounded planar
arm, repeated and mixed hook occurrences, characteristic two and the
zero-coordinate boundary.
-/

set_option autoImplicit false

namespace TDA.Persistence.CoordinateGridHook.Examples

open CategoryTheory CategoryTheory.Limits GradedFree
open scoped TDA.Persistence ZeroObject

private noncomputable abbrev grid := CoordinateGridKan.Examples.planarGrid
private noncomputable abbrev birth := CoordinateGridKan.Examples.planarLower
private noncomputable abbrev death := CoordinateGridKan.Examples.planarUpper

private noncomputable def realBirth : Fin 2 → ℝ := grid.embedding birth
private noncomputable def realDeath : Fin 2 → ℝ := grid.embedding death

private def armGrade : Fin 2 → ℝ := fun i => if i = 0 then 10 else 1
private def afterArmGrade : Fin 2 → ℝ := fun i => if i = 0 then 10 else 3

private theorem armGrade_le_afterArmGrade : armGrade ≤ afterArmGrade := by
  intro i
  fin_cases i <;> norm_num [armGrade, afterArmGrade]

private theorem armGrade_support :
    armGrade ∈ Hook.support realBirth realDeath := by
  change realBirth ≤ armGrade ∧ ¬ realDeath ≤ armGrade
  constructor
  · intro i
    fin_cases i <;> norm_num [realBirth, CoordinateGrid.embedding_apply,
      birth, CoordinateGridKan.Examples.planarLower, armGrade]
  · intro h
    have h1 := h 1
    norm_num [realDeath, CoordinateGrid.embedding_apply,
      death, CoordinateGridKan.Examples.planarUpper, armGrade] at h1

private theorem afterArmGrade_not_support :
    afterArmGrade ∉ Hook.support realBirth realDeath := by
  change ¬ (realBirth ≤ afterArmGrade ∧ ¬ realDeath ≤ afterArmGrade)
  intro h
  apply h.2
  intro i
  fin_cases i <;> norm_num [realDeath, CoordinateGrid.embedding_apply,
    death, CoordinateGridKan.Examples.planarUpper, afterArmGrade]

private noncomputable def realArmUnit (k : Type) [Field k] :
    (Hook.module (k := k) realBirth realDeath).obj armGrade :=
  SupportInterval.one (Hook.support realBirth realDeath) armGrade_support

/-- The actual Lan comparison transports the unit hook vector to the real
grade `(10,1)`, which lies on an unbounded planar arm. -/
noncomputable def armVector (k : Type) [Field k] :
    (grid.lan.obj (Hook.module (k := k) birth death)).obj armGrade :=
  ((grid.hookLanIso birth death).inv.app armGrade).hom (realArmUnit k)

/-- The canonical comparison sends the actual Lan vector to coefficient one. -/
theorem armVector_coefficient (k : Type) [Field k] :
    (((grid.hookLanIso birth death).hom.app armGrade).hom (armVector k) :
      SupportInterval.fiber (k := k) (Hook.support realBirth realDeath) armGrade) =
      (((grid.appIso (Hook.module (k := k) birth death) armGrade
        (show grid.HasLowerPoint armGrade from ⟨birth, by
          intro i
          fin_cases i <;> norm_num [armGrade, CoordinateGrid.embedding_apply, birth,
            CoordinateGridKan.Examples.planarLower]⟩)).hom.hom (armVector k) :
        SupportInterval.fiber (k := k) (Hook.support birth death)
          (grid.floor armGrade (show grid.HasLowerPoint armGrade from ⟨birth, by
            intro i
            fin_cases i <;> norm_num [armGrade, CoordinateGrid.embedding_apply, birth,
              CoordinateGridKan.Examples.planarLower]⟩))) : k) := by
  exact grid.hookLanIso_apply_coefficient birth death
    (show grid.HasLowerPoint armGrade from ⟨birth, by
      intro i
      fin_cases i <;> norm_num [armGrade, CoordinateGrid.embedding_apply, birth,
        CoordinateGridKan.Examples.planarLower]⟩)
    armGrade_support (armVector k)

/-- The arm vector is genuinely nonzero in the actual Lan fiber. -/
theorem armVector_ne_zero (k : Type) [Field k] : armVector k ≠ 0 := by
  let e : grid.lan.obj (Hook.module (k := k) birth death) ≅
      Hook.module (k := k) realBirth realDeath := grid.hookLanIso birth death
  intro h
  have hcancel :
      (e.hom.app armGrade).hom (armVector k) =
        realArmUnit k := by
    dsimp [armVector]
    have hh := congrArg (fun f => f.hom (realArmUnit k)) (e.inv_hom_id_app armGrade)
    change ((e.inv.app armGrade ≫ e.hom.app armGrade).hom (realArmUnit k)) = _ at hh
    exact hh
  rw [h, map_zero] at hcancel
  have hzero : realArmUnit k = 0 := hcancel.symm
  have hval := congrArg Subtype.val hzero
  exact (one_ne_zero : (1 : k) ≠ 0) hval

private theorem realArmUnit_dies (k : Type) [Field k] :
    structureMapLinear (Hook.module (k := k) realBirth realDeath)
      armGrade_le_afterArmGrade (realArmUnit k) = 0 := by
  apply Subtype.ext
  have h := SupportInterval.structureMap_val (Hook.support realBirth realDeath)
    (Hook.support_ordConnected realBirth realDeath) armGrade_le_afterArmGrade
    (realArmUnit k)
  rw [if_neg afterArmGrade_not_support] at h
  exact h

/-- The actual real transition from `(10,1)` to `(10,3)` kills the arm vector. -/
theorem armVector_dies_across_real_transition (k : Type) [Field k] :
    structureMapLinear (grid.lan.obj (Hook.module (k := k) birth death))
      armGrade_le_afterArmGrade (armVector k) = 0 := by
  let e : grid.lan.obj (Hook.module (k := k) birth death) ≅
      Hook.module (k := k) realBirth realDeath := grid.hookLanIso birth death
  have hn := congrArg (fun f => f.hom (armVector k))
    (e.hom.naturality (homOfLE armGrade_le_afterArmGrade))
  change (e.hom.app afterArmGrade).hom
      (structureMapLinear (grid.lan.obj (Hook.module (k := k) birth death))
        armGrade_le_afterArmGrade (armVector k)) =
    structureMapLinear (Hook.module (k := k) realBirth realDeath)
      armGrade_le_afterArmGrade ((e.hom.app armGrade).hom (armVector k)) at hn
  have hcoeff : (e.hom.app armGrade).hom (armVector k) = realArmUnit k := by
    dsimp [armVector]
    have hh := congrArg (fun f => f.hom (realArmUnit k)) (e.inv_hom_id_app armGrade)
    change ((e.inv.app armGrade ≫ e.hom.app armGrade).hom (realArmUnit k)) = _ at hh
    exact hh
  rw [hcoeff, realArmUnit_dies] at hn
  have hinj : Function.Injective (e.hom.app afterArmGrade).hom :=
    (ModuleCat.mono_iff_injective (e.hom.app afterArmGrade)).mp inferInstance
  exact hinj (by simpa using hn)

/-- The existing unbounded-tail fixture also supplies a nonzero actual Lan
fiber for the principal-upset comparison. -/
theorem principal_upset_actual_tail :
    ∃ x : (grid.lan.obj (HookInfinity.module (R := ℚ) birth)).obj
      (fun _ => 10), x ≠ 0 :=
  CoordinateGridKan.Examples.principal_upset_unbounded_tail (fun _ => 10)
    (by intro i; norm_num)

/-- The principal-upset coefficient law is usable on the same actual tail. -/
theorem principal_upset_tail_coefficient
    (x : (grid.lan.obj (HookInfinity.module (R := ℚ) birth)).obj (fun _ => 10)) :
    HookInfinity.fiberEquivOfLe (R := ℚ)
        (show grid.embedding birth ≤ (fun _ => 10) from by
          intro i
          norm_num [CoordinateGrid.embedding_apply, birth,
            CoordinateGridKan.Examples.planarLower])
        (((grid.infinityLanIso birth).hom.app (fun _ => 10)).hom x) =
      HookInfinity.fiberEquivOfLe (R := ℚ)
        ((grid.le_floor_iff (fun _ => 10)
          (show grid.HasLowerPoint (fun _ => 10) from ⟨death, by
            intro i
            norm_num [CoordinateGrid.embedding_apply, death,
              CoordinateGridKan.Examples.planarUpper]⟩) birth).mp
            (show grid.embedding birth ≤ (fun _ => 10) from by
              intro i
              norm_num [CoordinateGrid.embedding_apply, birth,
                CoordinateGridKan.Examples.planarLower]))
        ((grid.appIso (HookInfinity.module (R := ℚ) birth) (fun _ => 10)
          (⟨death, by intro i; norm_num [CoordinateGrid.embedding_apply, death,
            CoordinateGridKan.Examples.planarUpper]⟩)).hom.hom x) := by
  exact grid.infinityLanIso_apply_coefficient birth
    (⟨death, by intro i; norm_num [CoordinateGrid.embedding_apply, death,
      CoordinateGridKan.Examples.planarUpper]⟩)
    (by intro i; norm_num [CoordinateGrid.embedding_apply, birth,
      CoordinateGridKan.Examples.planarLower]) x

noncomputable abbrev zeroGrid := CoordinateGridKan.Examples.zeroGrid
noncomputable abbrev zeroGridPoint := CoordinateGridKan.Examples.zeroGridPoint
noncomputable abbrev zeroGridGrade := CoordinateGridKan.Examples.zeroGridGrade

private theorem degenerateHookFiber_subsingleton {P : Type} [PartialOrder P]
    (k : Type) [Field k] (p : P) :
    Subsingleton ((Hook.module (k := k) p p).obj p) := by
  change Subsingleton
    (SupportInterval.fiber (k := k) (Hook.support p p) p)
  constructor
  intro x y
  have hp : p ∉ Hook.support p p := by simp [Hook.support]
  apply Subtype.ext
  rw [SupportInterval.val_eq_zero (Hook.support p p) hp x,
    SupportInterval.val_eq_zero (Hook.support p p) hp y]

/-- A finite hook with equal birth and death is zero at its only n=0 grade. -/
theorem zero_dim_degenerate_hook_fiber_isZero :
    IsZero ((Hook.module (k := ℚ) zeroGridPoint zeroGridPoint).obj zeroGridPoint) := by
  letI : Subsingleton
      ((Hook.module (k := ℚ) zeroGridPoint zeroGridPoint).obj zeroGridPoint) :=
    degenerateHookFiber_subsingleton ℚ zeroGridPoint
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual finite-hook comparison remains available in dimension zero,
where the equal-endpoint finite hook vanishes. -/
noncomputable def zero_dim_degenerate_hook_lanIso :
    zeroGrid.lan.obj (Hook.module (k := ℚ) zeroGridPoint zeroGridPoint) ≅
      Hook.module (k := ℚ) (zeroGrid.embedding zeroGridPoint)
        (zeroGrid.embedding zeroGridPoint) :=
  zeroGrid.hookLanIso zeroGridPoint zeroGridPoint

/-- The principal-upset summand survives at the unique n=0 real grade. -/
theorem zero_dim_infinite_hook_lan_nonzero :
    ∃ x : (zeroGrid.lan.obj
      (HookInfinity.module (R := ℚ) zeroGridPoint)).obj zeroGridGrade, x ≠ 0 :=
  CoordinateGridKan.Examples.zero_dim_principal_upset_lan_nonzero

/-- An empty family has its actual canonical finite-biproduct comparison. -/
noncomputable def emptyFamily : Fin 0 → PModule ℚ zeroGrid.Point := Fin.elim0

noncomputable def emptyFamilyLanIso :
    zeroGrid.lan.obj (⨁ emptyFamily) ≅ ⨁ fun i : Fin 0 =>
      zeroGrid.lan.obj (emptyFamily i) :=
  zeroGrid.lanBiproductIso emptyFamily

private noncomputable abbrev doubleModule : PModule ℚ zeroGrid.Point :=
  (Functor.const zeroGrid.Point).obj (ModuleCat.of ℚ (ℚ × ℚ))

private instance doubleModule_finiteDimensional (p : zeroGrid.Point) :
    FiniteDimensional ℚ (doubleModule.obj p) :=
  inferInstanceAs (FiniteDimensional ℚ (ℚ × ℚ))

private noncomputable def repeatedOccurrence0 :
    FiniteHookDeflation.Index doubleModule :=
  .inr ⟨zeroGridPoint, ⟨0, by simp [doubleModule, Module.finrank_prod]⟩⟩

private noncomputable def repeatedOccurrence1 :
    FiniteHookDeflation.Index doubleModule :=
  .inr ⟨zeroGridPoint, ⟨1, by simp [doubleModule, Module.finrank_prod]⟩⟩

/-- Equal endpoints at n=0 still occur twice as distinct basis occurrences. -/
theorem repeated_cover_occurrences_distinct :
    repeatedOccurrence0 ≠ repeatedOccurrence1 := by
  intro h
  have h' := congrArg
    (fun t : FiniteHookDeflation.Index doubleModule =>
      t.elim (fun _ => 2) (fun s => s.2.val)) h
  norm_num [repeatedOccurrence0, repeatedOccurrence1] at h'

/-- Both distinct occurrences retain the same actual principal-upset summand. -/
theorem repeated_cover_occurrences_same_hook :
    zeroGrid.embeddedCoverFamily doubleModule repeatedOccurrence0 =
        HookInfinity.module (R := ℚ) (zeroGrid.embedding zeroGridPoint) ∧
      zeroGrid.embeddedCoverFamily doubleModule repeatedOccurrence1 =
        HookInfinity.module (R := ℚ) (zeroGrid.embedding zeroGridPoint) :=
  ⟨rfl, rfl⟩

/-- The actual comparison preserves the first repeated occurrence's projection. -/
theorem repeated_cover_first_projection_law :
    (zeroGrid.finiteHookDeflationLanIso doubleModule).hom ≫
        biproduct.π (zeroGrid.embeddedCoverFamily doubleModule) repeatedOccurrence0 =
      zeroGrid.lan.map
          (biproduct.π (FiniteHookDeflation.family doubleModule) repeatedOccurrence0) ≫
        (zeroGrid.infinityLanIso zeroGridPoint).hom :=
  zeroGrid.finiteHookDeflationLanIso_hom_π doubleModule repeatedOccurrence0

/-- The second occurrence has its own actual inclusion law despite its equal endpoint. -/
theorem repeated_cover_second_inclusion_law :
    biproduct.ι (zeroGrid.embeddedCoverFamily doubleModule) repeatedOccurrence1 ≫
        (zeroGrid.finiteHookDeflationLanIso doubleModule).inv =
      (zeroGrid.infinityLanIso zeroGridPoint).inv ≫
        zeroGrid.lan.map
          (biproduct.ι (FiniteHookDeflation.family doubleModule) repeatedOccurrence1) :=
  zeroGrid.finiteHookDeflationLanIso_inv_ι doubleModule repeatedOccurrence1

private theorem gridBirth_lt_death : birth < death := by
  apply lt_of_le_of_ne
  · intro i
    fin_cases i <;> change (0 : ℝ) ≤ 2 <;> norm_num
  · intro h
    have h0 := congrArg (fun p : grid.Point => (p 0).val) h
    norm_num [birth, death, CoordinateGridKan.Examples.planarLower,
      CoordinateGridKan.Examples.planarUpper] at h0

private noncomputable abbrev gridHook : PModule ℚ grid.Point :=
  Hook.module birth death

private noncomputable def gridHookBirthUnit : gridHook.obj birth :=
  SupportInterval.one (Hook.support birth death) (Hook.birth_mem gridBirth_lt_death)

private theorem gridHookBirthUnit_ne_zero : gridHookBirthUnit ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  exact (one_ne_zero : (1 : ℚ) ≠ 0) hv

private theorem gridHook_dies :
    structureMapLinear gridHook gridBirth_lt_death.le gridHookBirthUnit = 0 :=
  Hook.generator_dies gridBirth_lt_death (𝟙 gridHook)

private theorem gridHook_birth_finrank_pos :
    0 < Module.finrank ℚ (gridHook.obj birth) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  exact ⟨gridHookBirthUnit, gridHookBirthUnit_ne_zero⟩

private theorem gridHook_kernel_finrank_pos :
    0 < Module.finrank ℚ
      (LinearMap.ker (structureMapLinear gridHook gridBirth_lt_death.le)) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨gridHookBirthUnit, gridHook_dies⟩, ?_⟩
  intro h
  exact gridHookBirthUnit_ne_zero (congrArg Subtype.val h)

private noncomputable def mixedFiniteOccurrence :
    FiniteHookDeflation.Index gridHook :=
  .inl ⟨⟨(birth, death), gridBirth_lt_death⟩,
    ⟨0, gridHook_kernel_finrank_pos⟩⟩

private noncomputable def mixedInfiniteOccurrence :
    FiniteHookDeflation.Index gridHook :=
  .inr ⟨birth, ⟨0, gridHook_birth_finrank_pos⟩⟩

/-- The actual occurrence family contains both finite death and infinite
death hooks, and keeps their different occurrence indices. -/
theorem mixed_cover_family_endpoints_and_multiplicity :
    mixedFiniteOccurrence ≠ mixedInfiniteOccurrence ∧
      grid.embeddedCoverFamily gridHook mixedFiniteOccurrence =
        Hook.module (k := ℚ) (grid.embedding birth) (grid.embedding death) ∧
      grid.embeddedCoverFamily gridHook mixedInfiniteOccurrence =
        HookInfinity.module (R := ℚ) (grid.embedding birth) := by
  refine ⟨by simp [mixedFiniteOccurrence, mixedInfiniteOccurrence], rfl, rfl⟩

/-- The finite-death summand's projection is transported through its actual
hook comparison in the occurrence-indexed cover. -/
theorem mixed_cover_finite_projection_law :
    (grid.finiteHookDeflationLanIso gridHook).hom ≫
        biproduct.π (grid.embeddedCoverFamily gridHook) mixedFiniteOccurrence =
      grid.lan.map
          (biproduct.π (FiniteHookDeflation.family gridHook) mixedFiniteOccurrence) ≫
        (grid.hookLanIso birth death).hom :=
  grid.finiteHookDeflationLanIso_hom_π gridHook mixedFiniteOccurrence

/-- The infinite-death summand's inclusion has the corresponding actual law. -/
theorem mixed_cover_infinite_inclusion_law :
    biproduct.ι (grid.embeddedCoverFamily gridHook) mixedInfiniteOccurrence ≫
        (grid.finiteHookDeflationLanIso gridHook).inv =
      (grid.infinityLanIso birth).inv ≫
        grid.lan.map
          (biproduct.ι (FiniteHookDeflation.family gridHook) mixedInfiniteOccurrence) :=
  grid.finiteHookDeflationLanIso_inv_ι gridHook mixedInfiniteOccurrence

/-- Relative projectivity supplies an actual lift of the identity through the
left Kan image of the finite-hook deflation. -/
theorem lan_hook_deflation_lifts_identity :
    ∃ s : grid.lan.obj gridHook ⟶
        grid.lan.obj (FiniteHookDeflation.module gridHook),
      s ≫ grid.lan.map (FiniteHookDeflation.π gridHook) = 𝟙 (grid.lan.obj gridHook) := by
  letI : ∀ p, FiniteDimensional ℚ (gridHook.obj p) := by
    intro p
    change FiniteDimensional ℚ
      (SupportInterval.fiber (k := ℚ) (Hook.support birth death) p)
    infer_instance
  have hprojective : IsRankProjective (grid.lan.obj gridHook) :=
    grid.lan_isRankProjective gridHook (Hook.isRankProjective gridBirth_lt_death)
  have hsequence :
      IsRankExact
        (grid.lan.map (kernel.ι (FiniteHookDeflation.π gridHook)))
        (grid.lan.map (FiniteHookDeflation.π gridHook)) :=
    grid.lan_isRankExact (FiniteHookDeflation.rankExact gridHook)
  exact hprojective _ _ _ _ _ hsequence (𝟙 (grid.lan.obj gridHook))

private noncomputable abbrev repeatedFiniteGridFamily :
    Fin 2 → PModule ℚ grid.Point := fun _ => Hook.module birth death

private noncomputable abbrev repeatedFiniteRealFamily :
    Fin 2 → PModule ℚ (Fin 2 → ℝ) := fun _ =>
      Hook.module (grid.embedding birth) (grid.embedding death)

/-- The two finite occurrences share endpoints but remain separately indexed. -/
theorem repeated_finite_occurrences_distinct_and_equal_endpoints :
    repeatedFiniteGridFamily 0 = repeatedFiniteGridFamily 1 ∧
      (0 : Fin 2) ≠ 1 :=
  ⟨rfl, Fin.zero_ne_one⟩

/-- The actual Lan-sum comparison is the canonical Lan biproduct isomorphism
followed by the two actual finite-hook comparisons. -/
noncomputable def repeatedFiniteHookLanIso :
    grid.lan.obj (⨁ repeatedFiniteGridFamily) ≅ ⨁ repeatedFiniteRealFamily :=
  (grid.lanBiproductIso repeatedFiniteGridFamily).trans
    (biproduct.mapIso (fun _ => grid.hookLanIso birth death))

/-- The first repeated finite-hook projection is the image of its own grid
projection followed by the actual hook comparison. -/
theorem repeated_finite_first_projection_law :
    repeatedFiniteHookLanIso.hom ≫ biproduct.π repeatedFiniteRealFamily 0 =
      grid.lan.map (biproduct.π repeatedFiniteGridFamily 0) ≫
        (grid.hookLanIso birth death).hom := by
  change (grid.lanBiproductIso repeatedFiniteGridFamily).hom ≫
      biproduct.map (fun _ => (grid.hookLanIso birth death).hom) ≫
        biproduct.π repeatedFiniteRealFamily 0 = _
  calc
    _ = (grid.lanBiproductIso repeatedFiniteGridFamily).hom ≫
        (biproduct.π (fun i => grid.lan.obj (repeatedFiniteGridFamily i)) 0 ≫
          (grid.hookLanIso birth death).hom) := by rw [biproduct.map_π]
    _ = ((grid.lanBiproductIso repeatedFiniteGridFamily).hom ≫
        biproduct.π (fun i => grid.lan.obj (repeatedFiniteGridFamily i)) 0) ≫
          (grid.hookLanIso birth death).hom := by rw [← Category.assoc]
    _ = _ := by rw [grid.lanBiproductIso_hom_π]

/-- The second repeated finite-hook inclusion retains its own index through
the inverse comparison. -/
theorem repeated_finite_second_inclusion_law :
    biproduct.ι repeatedFiniteRealFamily 1 ≫ repeatedFiniteHookLanIso.inv =
      (grid.hookLanIso birth death).inv ≫
        grid.lan.map (biproduct.ι repeatedFiniteGridFamily 1) := by
  change biproduct.ι repeatedFiniteRealFamily 1 ≫
      biproduct.map (fun _ => (grid.hookLanIso birth death).inv) ≫
        (grid.lanBiproductIso repeatedFiniteGridFamily).inv = _
  calc
    _ = (biproduct.ι repeatedFiniteRealFamily 1 ≫
        biproduct.map (fun _ => (grid.hookLanIso birth death).inv)) ≫
          (grid.lanBiproductIso repeatedFiniteGridFamily).inv := by
          rw [← Category.assoc]
    _ = ((grid.hookLanIso birth death).inv ≫
        biproduct.ι (fun i => grid.lan.obj (repeatedFiniteGridFamily i)) 1) ≫
          (grid.lanBiproductIso repeatedFiniteGridFamily).inv := by
          rw [biproduct.ι_map]
    _ = (grid.hookLanIso birth death).inv ≫
        biproduct.ι (fun i => grid.lan.obj (repeatedFiniteGridFamily i)) 1 ≫
          (grid.lanBiproductIso repeatedFiniteGridFamily).inv := by
          rw [← Category.assoc]
    _ = _ := by rw [grid.lanBiproductIso_inv_ι]

/-- The two repeated real summands are still distinguished by their
off-diagonal projection/inclusion map. -/
theorem repeated_finite_offDiagonal_zero :
    biproduct.ι repeatedFiniteRealFamily 0 ≫
      biproduct.π repeatedFiniteRealFamily 1 = 0 :=
  biproduct.ι_π_ne repeatedFiniteRealFamily (by decide)

/-- The arm-vector construction also works over the field of two elements. -/
theorem characteristic_two_arm_vector_survives_and_dies :
    armVector (ZMod 2) ≠ 0 ∧
      structureMapLinear
        (grid.lan.obj (Hook.module (k := ZMod 2) birth death))
        armGrade_le_afterArmGrade (armVector (ZMod 2)) = 0 :=
  ⟨armVector_ne_zero (ZMod 2), armVector_dies_across_real_transition (ZMod 2)⟩

/-- The original rational finite presentation receives the constructed actual
finite-hook rank-exact cover. -/
theorem rational_presentation_actual_hook_cover :
    ∃ (G : CoordinateGrid 2) (A : PModule ℚ G.Point)
      (hA : ∀ p, FiniteDimensional ℚ (A.obj p))
      (e : G.lan.obj A ≅ (FinitePresentationKanExamples.presentation ℚ 2).presented),
      IsRankExact
        (G.lan.map (kernel.ι (FiniteHookDeflation.π A)) ≫
          (G.finiteHookDeflationLanIso A).hom)
        ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom) ∧
      IsRankProjective (⨁ fun t => G.embeddedCoverFamily A t) ∧
      (∀ a : Fin 2 → ℝ,
        FiniteDimensional ℚ
          ((G.lan.obj (kernel (FiniteHookDeflation.π A))).obj a)) := by
  exact GradedFree.finitelyPresented_exists_finiteHookRankExactCover
    ((FinitePresentationKanExamples.presentation ℚ 2).finitelyPresented
      (FinitePresentationKanExamples.presentation_finite ℚ 2))

/-- The same original-presentation consumer works in characteristic two. -/
theorem characteristic_two_presentation_actual_hook_cover :
    ∃ (G : CoordinateGrid 2) (A : PModule (ZMod 2) G.Point)
      (hA : ∀ p, FiniteDimensional (ZMod 2) (A.obj p))
      (e : G.lan.obj A ≅ (FinitePresentationKanExamples.presentation (ZMod 2) 2).presented),
      IsRankExact
        (G.lan.map (kernel.ι (FiniteHookDeflation.π A)) ≫
          (G.finiteHookDeflationLanIso A).hom)
        ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom) ∧
      IsRankProjective (⨁ fun t => G.embeddedCoverFamily A t) ∧
      (∀ a : Fin 2 → ℝ,
        FiniteDimensional (ZMod 2)
          ((G.lan.obj (kernel (FiniteHookDeflation.π A))).obj a)) := by
  exact GradedFree.finitelyPresented_exists_finiteHookRankExactCover
    ((FinitePresentationKanExamples.presentation (ZMod 2) 2).finitelyPresented
      (FinitePresentationKanExamples.presentation_finite (ZMod 2) 2))

end TDA.Persistence.CoordinateGridHook.Examples
