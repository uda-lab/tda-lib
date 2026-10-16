import TDA.Persistence.RealBarcode
import TDA.Persistence.FiniteDecomposition

/-!
# Finite-constructible real barcode decomposition

Finite-dimensionality is required only at the critical fibers. The initial sampled zero
module then supplies the remaining finite-dimensional fiber. Its zero rank excludes every
birth-zero occurrence before the real endpoints are formed.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteConstructible

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {n : ℕ} {k : Type u} [Field k]

/-- Only the critical fibers need a finite-dimensionality hypothesis for the finite sample. -/
theorem finiteDimensional_sample (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) (j : Fin (n + 1)) :
    FiniteDimensional k ((sample c M).obj j) := by
  cases j using Fin.cases with
  | zero =>
    have : Subsingleton ((sample c M).obj 0) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero (ModuleCat k))
    infer_instance
  | succ i => exact hfd i

/-- A zero initial fiber excludes every birth-zero occurrence from the canonical barcode. -/
theorem rankBarcode_birth_pos (A : PModule.{u,0,u} k (Fin (n + 1)))
    [∀ j, FiniteDimensional k (A.obj j)] (hzero : IsZero (A.obj 0))
    (I : FiniteInterval (n + 1)) (hI : I ∈ rankBarcode A) : 0 < I.birth := by
  classical
  have : Subsingleton (A.obj 0) := ModuleCat.isZero_iff_subsingleton.mp hzero
  have hr : structureMapRank A 0 0 le_rfl = 0 := by
    change Module.finrank k (LinearMap.range
      (structureMapLinear A (show (0 : Fin (n + 1)) ≤ 0 from le_rfl))) = 0
    exact Module.finrank_zero_of_subsingleton
  have hc := (structureMapRank_rankBarcode (M := A) 0 0 le_rfl).trans hr
  rw [rank_barcodeMap] at hc
  change (rankBarcode A).countP (fun J => J.birth ≤ 0 ∧ 0 < J.death) = 0 at hc
  have hn := (Multiset.countP_eq_zero.mp hc) I hI
  have := I.birth_lt_death
  omega

/-- The canonical barcode of the padded sample, with only critical-fiber finiteness as input. -/
noncomputable def sampleBarcode (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) : Multiset (FiniteInterval (n + 1)) := by
  letI : ∀ j, FiniteDimensional k ((sample c M).obj j) := finiteDimensional_sample c M hfd
  exact rankBarcode (sample c M)

/-- Every occurrence in the sampled barcode has a genuine critical birth. -/
theorem sampleBarcode_birth_pos (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i)))
    (I : FiniteInterval (n + 1)) (hI : I ∈ sampleBarcode c M hfd) : 0 < I.birth := by
  have hSampleFD : ∀ j, FiniteDimensional k ((sample c M).obj j) :=
    finiteDimensional_sample c M hfd
  exact rankBarcode_birth_pos (sample c M) (isZero_zero (ModuleCat k)) I hI

/-- When there are no critical values the padded sample has no barcode occurrences. -/
theorem sampleBarcode_empty_grid (c : Fin 0 ↪o ℝ) (M : PModule.{u,0,u} k ℝ) :
    sampleBarcode c M (fun i => Fin.elim0 i) = 0 := by
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro I hI
  have hb := sampleBarcode_birth_pos c M (fun i => Fin.elim0 i) I hI
  have := I.birth_lt_death
  have := I.death_le_size
  omega

/-- The real endpoint diagram comes from the unpadded critical module.
No real value is assigned to the padded zero stage. -/
noncomputable def moduleDiagram (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) : Diagram ℝ := by
  letI : ∀ i, FiniteDimensional k ((reindex c.toOrderHom M).obj i) := hfd
  exact ofIndexBars c c.strictMono (rankBarcode (reindex c.toOrderHom M))

/-- The padded sample's barcode gives the same diagram after actual `Fin.succ` sampling. -/
theorem moduleDiagram_eq_reindex_sample (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) :
    moduleDiagram c M hfd = ofIndexBars c c.strictMono
      (reindexBarcode (Fin.succOrderEmb n).toOrderHom (sampleBarcode c M hfd)) := by
  have hSampleFD : ∀ j, FiniteDimensional k ((sample c M).obj j) :=
    finiteDimensional_sample c M hfd
  have hCriticalFD : ∀ i, FiniteDimensional k ((reindex c.toOrderHom M).obj i) := hfd
  unfold moduleDiagram sampleBarcode
  rw [← rankBarcode_reindex]
  rfl

/-- The resulting diagram has positive bars, including essential tails. -/
theorem moduleDiagram_isPositive (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) : (moduleDiagram c M hfd).IsPositive := by
  rw [moduleDiagram_eq_reindex_sample]
  exact ofIndexBars_isPositive _ _ _

/-- No critical values produce an empty endpoint diagram. -/
theorem moduleDiagram_empty_grid (c : Fin 0 ↪o ℝ) (M : PModule.{u,0,u} k ℝ) :
    (moduleDiagram c M (fun i => Fin.elim0 i)).points = 0 := by
  rw [moduleDiagram_eq_reindex_sample, sampleBarcode_empty_grid]
  simp [reindexBarcode, ofIndexBars]

/-- A finite-constructible real module is naturally isomorphic to its half-open barcode
realization. Only the critical fibers require finite-dimensionality.

The finite decomposition isomorphism is actually whiskered along `cellIndex c`; the final
isomorphism transports every occurrence to the existing real endpoint diagram. -/
noncomputable def barcodeRealizationIso (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hM : IsConstructible c M) (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) :
    M ≅ RealBarcode.realize (k := k) (moduleDiagram c M hfd) := by
  letI : ∀ j, FiniteDimensional k ((sample c M).obj j) := finiteDimensional_sample c M hfd
  exact (reconstructionIso c M hM).symm ≪≫
    Functor.isoWhiskerLeft (cellIndex c).toFunctor (rankBarcodeIso (sample c M)) ≪≫
    RealBarcode.barcodePullbackIso c (sampleBarcode c M hfd) (sampleBarcode_birth_pos c M hfd) ≪≫
    eqToIso (congrArg (RealBarcode.realize (k := k)) (moduleDiagram_eq_reindex_sample c M hfd).symm)

end TDA.Persistence.FiniteConstructible
