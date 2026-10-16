import TDA.Persistence.ConstructibleSampling
import TDA.Persistence.RealIntervalInterleaving

/-!
# Nonzero defects, rounded translations and the terminal observation

Zero comparison maps on a length-two interval give actual nonzero defects whose
critical samples are two-short but fail the shorter bound. Irregular grids and
an essential tail distinguish rounding from truncation.
-/

set_option autoImplicit false

namespace TDA.Persistence.ConstructibleDefectExamples

open CategoryTheory CategoryTheory.Limits FiniteConstructible RealShift
open scoped NNReal ZeroObject

private def coarse : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i => if i = 0 then (0 : ℝ) else 2)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private theorem coarse_apply (i : Fin 2) : coarse i = if i = 0 then (0 : ℝ) else 2 := rfl
private def bar : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩

private noncomputable def input : PModule.{0,0,0} ℚ ℝ :=
  reindex (cellIndex coarse) (intervalModule (k := ℚ) bar)

private theorem input_constructible : IsConstructible coarse input := by
  apply isConstructible_reindex
  have : Subsingleton ((intervalModule (k := ℚ) bar).obj 0) := by
    change Subsingleton (FiniteInterval.fiber (k := ℚ) bar 0)
    have hn : ¬ bar.alive 0 := by norm_num [FiniteInterval.alive, bar]
    simp only [FiniteInterval.fiber, if_neg hn]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

private noncomputable def threshold : PModule.{0,0,0} ℚ ℝ :=
  RealBarcode.intervalModule (0, (2 : WithTop ℝ))

private noncomputable def intervalIso : input ≅ threshold := by
  have hp : RealBarcode.endpoints coarse (RealBarcode.dropZero bar (by decide)) =
      ((0 : ℝ), (2 : WithTop ℝ)) := by
    norm_num [RealBarcode.endpoints, RealBarcode.dropZero, bar, coarse_apply]
  exact (RealBarcode.intervalPullbackIso coarse bar (by decide)).trans (eqToIso (by rw [hp]; rfl))

private noncomputable def realWitness : RealInterleaving 1 threshold threshold where
  φ := 0
  ψ := 0
  φ_ψ := by rw [zero_comp]; exact (RealBarcode.transition_eq_zero_iff 1 0 2).mpr (by norm_num) |>.symm
  ψ_φ := by rw [zero_comp]; exact (RealBarcode.transition_eq_zero_iff 1 0 2).mpr (by norm_num) |>.symm

private noncomputable def witness : RealInterleaving 1 input input :=
  realWitness.congr intervalIso.symm intervalIso.symm

private theorem witness_φ_zero : witness.φ = 0 := by
  simp [witness, RealInterleaving.congr, realWitness]

private theorem threshold_fiber_nonzero (t : ℝ) (ht : RealBarcode.alive (0, (2 : WithTop ℝ)) t) :
    ¬ IsZero (threshold.obj t) := by
  intro hz
  let x : RealBarcode.fiber (k := ℚ) (0, (2 : WithTop ℝ)) t :=
    ⟨1, by simp [RealBarcode.fiber, ht]⟩
  have h := congrArg (fun f : threshold.obj t ⟶ threshold.obj t =>
    (show RealBarcode.fiber (k := ℚ) (0, (2 : WithTop ℝ)) t from f.hom x).val)
    (hz.eq_zero_of_src (𝟙 _))
  exact (one_ne_zero : (1 : ℚ) ≠ 0) h

private theorem input_nonzero : ¬ IsZero input := by
  intro h
  exact threshold_fiber_nonzero 0 (by norm_num [RealBarcode.alive])
    ((h.of_iso intervalIso.symm).obj 0)

private theorem shifted_input_nonzero : ¬ IsZero ((shift 1).obj input) := by
  intro h
  have hz := h.obj (-1 : ℝ)
  change IsZero (input.obj ((-1 : ℝ) + 1)) at hz
  norm_num at hz
  exact threshold_fiber_nonzero 0 (by norm_num [RealBarcode.alive])
    (hz.of_iso (intervalIso.app 0).symm)

/-- The actual comparison is neither mono nor epi, and both actual defects are nonzero. -/
theorem actual_nonzero_defects :
    ¬ Mono witness.φ ∧ ¬ Epi witness.φ ∧
      ¬ IsZero (kernel witness.φ) ∧ ¬ IsZero (cokernel witness.φ) := by
  refine ⟨fun h => input_nonzero (IsZero.of_mono_eq_zero witness.φ witness_φ_zero),
    fun h => shifted_input_nonzero (IsZero.of_epi_eq_zero witness.φ witness_φ_zero), ?_, ?_⟩
  · rw [witness_φ_zero]
    intro h
    exact input_nonzero (h.of_iso kernelZeroIsoSource.symm)
  · rw [witness_φ_zero]
    intro h
    exact shifted_input_nonzero (h.of_iso cokernelZeroIsoTarget.symm)

/-- The constructed common grid gives both actual constructible defects and
both finite shortness conclusions without an assumed shortness certificate. -/
theorem actual_common_defects :
    let e := commonGrid coarse (shiftGrid 1 coarse)
    IsConstructible e (kernel witness.φ) ∧ IsConstructible e (cokernel witness.φ) ∧
      TranslationTrivial (sampleTranslation e (1 + 1)) (le_sampleTranslation e (1 + 1))
        (finiteKernel (reindexNatTrans e.toOrderHom witness.φ)) ∧
      TranslationTrivial (sampleTranslation e (1 + 1)) (le_sampleTranslation e (1 + 1))
        (finiteCokernel (reindexNatTrans e.toOrderHom witness.φ)) :=
  interleaving_critical_defects input_constructible input_constructible witness

private def fine : Fin 4 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (![(-1 : ℝ), 0, 1, 2])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private theorem fine_theta_one : sampleTranslation fine 1 (1 : Fin 4) = 2 := by
  apply Fin.succ_injective 4
  rw [sampleTranslation_succ]
  apply (cellIndex_eq_succ_iff fine (2 : Fin 4) _).mpr
  refine ⟨?_, ?_⟩
  · change (1 : ℝ) ≤ 0 + 1
    norm_num
  intro j hj
  have hj3 : j = 3 := by
    apply Fin.ext
    have hjn := j.isLt
    change 2 < j.val at hj
    omega
  subst j
  change (0 : ℝ) + 1 < 2
  norm_num

private theorem threshold_sample_map_nonzero :
    structureMap (reindex fine.toOrderHom threshold)
      (le_sampleTranslation fine 1 (1 : Fin 4)) ≠ 0 := by
  have hs : RealBarcode.alive (0, (2 : WithTop ℝ)) (fine (1 : Fin 4)) := by
    change RealBarcode.alive (0, (2 : WithTop ℝ)) 0
    norm_num [RealBarcode.alive]
  have ht : RealBarcode.alive (0, (2 : WithTop ℝ))
      (fine (sampleTranslation fine 1 (1 : Fin 4))) := by
    rw [fine_theta_one]
    change RealBarcode.alive (0, (2 : WithTop ℝ)) 1
    norm_num [RealBarcode.alive]
  let x : RealBarcode.fiber (k := ℚ) (0, (2 : WithTop ℝ)) (fine (1 : Fin 4)) :=
    ⟨1, by simp [RealBarcode.fiber, hs]⟩
  intro hz
  have hx := congrArg (fun f : threshold.obj (fine (1 : Fin 4)) ⟶
      threshold.obj (fine (sampleTranslation fine 1 (1 : Fin 4))) =>
    (show RealBarcode.fiber (k := ℚ) (0, (2 : WithTop ℝ)) _ from f.hom x).val) hz
  change (show RealBarcode.fiber (k := ℚ) (0, (2 : WithTop ℝ)) _ from
    ((RealBarcode.intervalModule (0, (2 : WithTop ℝ))).map
      (homOfLE (fine.monotone (le_sampleTranslation fine 1 (1 : Fin 4))))).hom x).val = 0 at hx
  rw [RealBarcode.map_val] at hx
  exact (one_ne_zero : (1 : ℚ) ≠ 0) (by simpa only [if_pos ht, x] using hx)

/-- The actual sampled kernel is not one-short: its map from real 0 to 1 survives. -/
theorem shorter_parameter_rejected :
    ¬ TranslationTrivial (sampleTranslation fine 1) (le_sampleTranslation fine 1)
      (finiteKernel (reindexNatTrans fine.toOrderHom witness.φ)) := by
  intro h
  have hf : reindexNatTrans fine.toOrderHom witness.φ = 0 := by
    rw [witness_φ_zero]
    rfl
  change TranslationTrivial _ _ (kernel _) at h
  rw [hf] at h
  have hi := translationTrivial_of_iso _ _ kernelZeroIsoSource h
  have hr := translationTrivial_of_iso _ _
    (Functor.isoWhiskerLeft fine.toOrderHom.toFunctor intervalIso) hi
  exact threshold_sample_map_nonzero (hr (1 : Fin 4))

/-- The constructed common grid contains the actual negative shifted critical value. -/
theorem common_grid_negative :
    (-1 : ℝ) ∈ Set.range (commonGrid coarse (shiftGrid 1 coarse)) := by
  rw [range_commonGrid]
  exact Or.inr ⟨0, by norm_num [shiftGrid_apply, coarse_apply]⟩

/-- Sampling comparisons retain the actual inclusion and projection of this nonzero example. -/
theorem sampling_inclusion_projection :
    (criticalKernelIso fine witness.φ).inv ≫ reindexNatTrans fine.toOrderHom (kernel.ι witness.φ) =
      kernel.ι (reindexNatTrans fine.toOrderHom witness.φ) ∧
    reindexNatTrans fine.toOrderHom (cokernel.π witness.φ) ≫ (criticalCokernelIso fine witness.φ).hom =
      cokernel.π (reindexNatTrans fine.toOrderHom witness.φ) :=
  ⟨criticalKernelIso_inv_ι _ _, criticalCokernelIso_π_hom _ _⟩

private def irregular : Fin 3 ↪o ℝ :=
  OrderEmbedding.ofStrictMono
    (fun i => if i = 0 then (-3 : ℝ) else if i = 1 then 0 else 10)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private theorem irregular_apply (i : Fin 3) :
    irregular i = if i = 0 then (-3 : ℝ) else if i = 1 then 0 else 10 := rfl

private theorem small_first : sampleTranslation irregular 1 (0 : Fin 3) = 0 := by
  apply Fin.succ_injective 3
  rw [sampleTranslation_succ]
  apply (cellIndex_eq_succ_iff irregular (0 : Fin 3) _).mpr
  refine ⟨by norm_num [irregular_apply], ?_⟩
  intro j hj
  have hjv : (0 : ℕ) < j.val := hj
  fin_cases j <;> norm_num [irregular_apply] at *

private theorem small_middle : sampleTranslation irregular 1 (1 : Fin 3) = 1 := by
  apply Fin.succ_injective 3
  rw [sampleTranslation_succ]
  apply (cellIndex_eq_succ_iff irregular (1 : Fin 3) _).mpr
  refine ⟨by norm_num [irregular_apply], ?_⟩
  intro j hj
  have hj2 : j = 2 := by
    apply Fin.ext
    have hjn := j.isLt
    change 1 < j.val at hj
    omega
  subst j
  change (0 : ℝ) + 1 < 10
  norm_num

private theorem exact_boundary : sampleTranslation irregular 3 (0 : Fin 3) = 1 := by
  apply Fin.succ_injective 3
  rw [sampleTranslation_succ]
  apply (cellIndex_eq_succ_iff irregular (1 : Fin 3) _).mpr
  refine ⟨by norm_num [irregular_apply], ?_⟩
  intro j hj
  have hj2 : j = 2 := by
    apply Fin.ext
    have hjn := j.isLt
    change 1 < j.val at hj
    omega
  subst j
  change (-3 : ℝ) + 3 < 10
  norm_num

/-- A positive translation may round strictly down and fix an interior index;
an exact critical boundary advances, while the last observation remains fixed. -/
theorem rounding_and_boundaries (δ : ℝ≥0) :
    sampleTranslation irregular 1 (0 : Fin 3) = 0 ∧
    sampleTranslation irregular 1 (1 : Fin 3) = 1 ∧
    sampleTranslation irregular 3 (0 : Fin 3) = 1 ∧
    irregular (sampleTranslation irregular 1 (1 : Fin 3)) < irregular 1 + 1 ∧
    sampleTranslation irregular δ (Fin.last 2) = Fin.last 2 := by
  refine ⟨small_first, small_middle, exact_boundary, ?_, sampleTranslation_last _ _⟩
  rw [small_middle]
  norm_num [irregular_apply]

private def oneGrid : Fin 1 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun _ => (0 : ℝ))
    (by intro i j hij; fin_cases i; fin_cases j; simp at hij)

private theorem oneGrid_apply (i : Fin 1) : oneGrid i = (0 : ℝ) := rfl
private def essentialBar : FiniteInterval 2 := ⟨1, 2, by decide, by decide⟩
private noncomputable def essentialInput : PModule.{0,0,0} ℚ ℝ :=
  reindex (cellIndex oneGrid) (intervalModule (k := ℚ) essentialBar)

private theorem essential_constructible : IsConstructible oneGrid essentialInput := by
  apply isConstructible_reindex
  have : Subsingleton ((intervalModule (k := ℚ) essentialBar).obj 0) := by
    change Subsingleton (FiniteInterval.fiber (k := ℚ) essentialBar 0)
    have hn : ¬ essentialBar.alive 0 := by norm_num [FiniteInterval.alive, essentialBar]
    simp only [FiniteInterval.fiber, if_neg hn]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

private noncomputable def essentialIso :
    essentialInput ≅ RealBarcode.intervalModule (k := ℚ) (0, ⊤) := by
  have hp : RealBarcode.endpoints oneGrid (RealBarcode.dropZero essentialBar (by decide)) =
      ((0 : ℝ), (⊤ : WithTop ℝ)) := by
    norm_num [RealBarcode.endpoints, RealBarcode.dropZero, essentialBar, oneGrid_apply]
  exact (RealBarcode.intervalPullbackIso oneGrid essentialBar (by decide)).trans
    (eqToIso (by rw [hp]))

private theorem essential_last_nonzero : ¬ IsZero (essentialInput.obj 10) := by
  intro hz
  have hr := hz.of_iso (essentialIso.app 10).symm
  have ha : RealBarcode.alive ((0 : ℝ), (⊤ : WithTop ℝ)) 10 :=
    ⟨by norm_num, WithTop.coe_lt_top 10⟩
  let x : RealBarcode.fiber (k := ℚ) (0, ⊤) 10 :=
    ⟨1, by simp [RealBarcode.fiber, ha]⟩
  have h := congrArg (fun f : (RealBarcode.intervalModule (k := ℚ) (0, ⊤)).obj 10 ⟶
      (RealBarcode.intervalModule (k := ℚ) (0, ⊤)).obj 10 =>
    (show RealBarcode.fiber (k := ℚ) (0, ⊤) 10 from f.hom x).val)
    (hr.eq_zero_of_src (𝟙 _))
  exact (one_ne_zero : (1 : ℚ) ≠ 0) h

/-- A genuine constructible essential tail rejects every finite sampled shortness
bound, because the final observed self-map remains nonzero. -/
theorem essential_tail_rejected : IsConstructible irregular essentialInput ∧
    ∀ δ : ℝ≥0, ¬ TranslationTrivial (sampleTranslation irregular δ)
      (le_sampleTranslation irregular δ) (reindex irregular.toOrderHom essentialInput) := by
  have hr : Refines oneGrid irregular := by
    rintro x ⟨i, rfl⟩
    exact ⟨1, by norm_num [oneGrid_apply, irregular_apply]⟩
  refine ⟨essential_constructible.refine hr, ?_⟩
  intro δ h
  have hz := h (Fin.last 2)
  have : IsIso (homOfLE (le_sampleTranslation irregular δ (Fin.last 2))) :=
    homOfLE_isIso_of_eq _ (sampleTranslation_last irregular δ).symm
  have : IsIso (structureMap (reindex irregular.toOrderHom essentialInput)
      (le_sampleTranslation irregular δ (Fin.last 2))) := by
    unfold structureMap
    infer_instance
  apply essential_last_nonzero
  change IsZero ((reindex irregular.toOrderHom essentialInput).obj (Fin.last 2))
  exact IsZero.of_mono_eq_zero _ hz

private noncomputable def zeroWitness : RealInterleaving 0 input input :=
  RealInterleaving.ofIso (Iso.refl _)

private theorem zero_of_zero_double_transition {A : PModule.{0,0,0} ℚ ℝ}
    (h : transition (0 + 0) A = 0) : IsZero A := by
  apply (IsZero.iff_id_eq_zero A).mpr
  have hz : transition 0 A = 0 := by
    rw [← transition_congr (show (0 : ℝ≥0) + 0 = 0 from zero_add 0) A, h, zero_comp]
  have ht := transition_zero A
  rw [hz, zero_comp] at ht
  exact ht.symm

/-- Zero parameter gives actual zero defects and identity-translation shortness
for a module that itself is nonzero. -/
theorem zero_parameter : ¬ IsZero input ∧ IsZero (kernel zeroWitness.φ) ∧
    IsZero (cokernel zeroWitness.φ) ∧
    sampleTranslation coarse 0 = OrderHom.id ∧
    TranslationTrivial (sampleTranslation coarse 0) (le_sampleTranslation coarse 0)
      (finiteKernel (reindexNatTrans coarse.toOrderHom zeroWitness.φ)) ∧
    TranslationTrivial (sampleTranslation coarse 0) (le_sampleTranslation coarse 0)
      (finiteCokernel (reindexNatTrans coarse.toOrderHom zeroWitness.φ)) := by
  have ht : IsConstructible coarse ((shift 0).obj input) := by
    simpa only [shiftGrid_zero] using input_constructible.shift 0
  have hk := zero_of_zero_double_transition zeroWitness.kernel_transition_eq_zero
  have hc := zero_of_zero_double_transition zeroWitness.cokernel_transition_eq_zero
  exact ⟨input_nonzero, hk, hc, sampleTranslation_zero _,
    criticalKernel_translationTrivial input_constructible ht _ 0
      (hk.eq_zero_of_src _),
    criticalCokernel_translationTrivial input_constructible ht _ 0
      (hc.eq_zero_of_src _)⟩

private def empty : Fin 0 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
private noncomputable def zeroInput : PModule.{0,0,0} ℚ ℝ := 0
private theorem empty_constructible : IsConstructible empty zeroInput :=
  (isConstructible_empty_iff _ _).mpr (fun t => Functor.zero_obj t)

/-- Empty critical sampling has no stages; its actual constructible real module is zero. -/
theorem empty_grid (δ : ℝ≥0) : sampleTranslation empty δ = OrderHom.id ∧
    (∀ t, IsZero (zeroInput.obj t)) ∧
    TranslationTrivial (sampleTranslation empty δ) (le_sampleTranslation empty δ)
      (finiteKernel (reindexNatTrans empty.toOrderHom (𝟙 zeroInput))) ∧
    TranslationTrivial (sampleTranslation empty δ) (le_sampleTranslation empty δ)
      (finiteCokernel (reindexNatTrans empty.toOrderHom (𝟙 zeroInput))) := by
  refine ⟨?_, (isConstructible_empty_iff _ _).mp empty_constructible,
    fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  apply DFunLike.ext
  intro i
  exact Fin.elim0 i

end TDA.Persistence.ConstructibleDefectExamples
