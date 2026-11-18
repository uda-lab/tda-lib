import TDA.Persistence.LocallyFiniteDiagramBottleneckLaws
import TDA.Persistence.RealInterleavingDistance
import TDA.Persistence.PersistenceMeasureEssentialContent
import TDA.Persistence.PersistenceMeasureDiagram
import TDA.Persistence.PersistenceMeasureEssentialDiagram
import Mathlib.Tactic.Linarith

/-!
# A whole-line obstruction to unrestricted finite-birth isometry

The actual constant scalar persistence module and the actual zero module have the same
canonical finite-birth decorated diagram: neither has a finite birth. Their real
interleaving distance is infinite. Thus the established one-sided bottleneck bound
does not reverse for arbitrary q-tame modules. The constant module fails every finite
zero-left bound, so this example does not contradict a left-bounded isometry target.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.WholeLineObstructionExamples

open CategoryTheory CategoryTheory.Limits RectangleMeasure
open scoped NNReal ENNReal Classical ZeroObject

variable (k : Type u) [Field k]

/-- The scalar module on the entire real line, with identity transition maps. -/
noncomputable def constant : PModule.{u,0,u} k ℝ :=
  (Functor.const ℝ).obj (ModuleCat.of k k)

/-- Every actual transition of the whole-line scalar module is the identity. -/
theorem constant_structureMapLinear {s t : ℝ} (hst : s ≤ t) :
    structureMapLinear (constant k) hst = LinearMap.id := by
  rfl

private theorem zero_structureMapLinear {s t : ℝ} (hst : s ≤ t) :
    structureMapLinear (0 : PModule.{u,0,u} k ℝ) hst = 0 := by
  change (structureMap (0 : PModule.{u,0,u} k ℝ) hst).hom = 0
  rw [(Functor.zero_obj s).eq_of_src (structureMap (0 : PModule.{u,0,u} k ℝ) hst) 0]
  rfl

/-- The actual constant scalar module is q-tame over any field. -/
theorem constant_qTame : (constant k).QTame :=
  PModule.qTame_of_finiteDimensional _ (fun _ => by
    change FiniteDimensional k k
    infer_instance)

/-- The actual zero module is q-tame over any field. -/
theorem zero_qTame : (0 : PModule.{u,0,u} k ℝ).QTame := by
  intro a b hab
  rw [zero_structureMapLinear k hab.le, LinearMap.range_zero]
  infer_instance

private theorem constant_image_top {s t : ℝ} (hst : s ≤ t) :
    persistenceImage (constant k) hst = ⊤ := by
  rw [persistenceImage, constant_structureMapLinear k hst]
  exact LinearMap.range_id

private theorem zero_image_bot {s t : ℝ} (hst : s ≤ t) :
    persistenceImage (0 : PModule.{u,0,u} k ℝ) hst = ⊥ := by
  simp [persistenceImage, zero_structureMapLinear k hst]

private theorem constant_rectangle_zero {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    persistenceMeasureValue (constant k) hab hbc hcd = 0 := by
  have hi : FiniteDimensional k (persistenceImage (constant k) hbc) := by
    change FiniteDimensional k
      (LinearMap.range (structureMapLinear (constant k) hbc))
    haveI : FiniteDimensional k ((constant k).obj b) := by
      change FiniteDimensional k k
      infer_instance
    exact LinearMap.finiteDimensional_range _
  letI := hi
  have h := persistenceMeasureValue_four_rank (constant k) hab hbc hcd
  rw [constant_image_top k hbc, constant_image_top k (hab.trans hbc),
    constant_image_top k (hbc.trans hcd),
    constant_image_top k ((hab.trans hbc).trans hcd)] at h
  omega

private theorem zero_rectangle_zero {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    persistenceMeasureValue (0 : PModule.{u,0,u} k ℝ) hab hbc hcd = 0 :=
  persistenceMeasureValue_eq_zero_of_crossing_eq_zero _ _ _ _
    (zero_structureMapLinear k hbc)

private theorem constant_tail_zero {a b c : ℝ}
    (hab : a ≤ b) (hbc : b < c) :
    persistenceTailMeasureValue (constant k) hab hbc.le = 0 := by
  have hi : FiniteDimensional k (persistenceImage (constant k) hbc.le) :=
    constant_qTame k b c hbc
  letI := hi
  have h := persistenceTailMeasureValue_add_image (constant k) hab hbc.le
  rw [constant_image_top k hbc.le, constant_image_top k (hab.trans hbc.le)] at h
  omega

private theorem zero_tail_zero {a b c : ℝ}
    (hab : a ≤ b) (hbc : b < c) :
    persistenceTailMeasureValue (0 : PModule.{u,0,u} k ℝ) hab hbc.le = 0 := by
  have hi : FiniteDimensional k
      (persistenceImage (0 : PModule.{u,0,u} k ℝ) hbc.le) :=
    zero_qTame k b c hbc
  letI := hi
  have h := persistenceTailMeasureValue_add_image
    (0 : PModule.{u,0,u} k ℝ) hab hbc.le
  rw [zero_image_bot k hbc.le, zero_image_bot k (hab.trans hbc.le)] at h
  omega

private theorem constant_essential_zero {a b : ℝ} (hab : a ≤ b) :
    essentialMeasureValue (constant k) hab = 0 := by
  have hbc : b < b + 1 := lt_add_one b
  have h := essentialMeasureValue_le_tail (constant k) hab hbc
  rw [constant_tail_zero k hab hbc] at h
  omega

private theorem zero_essential_zero {a b : ℝ} (hab : a ≤ b) :
    essentialMeasureValue (0 : PModule.{u,0,u} k ℝ) hab = 0 := by
  have hbc : b < b + 1 := lt_add_one b
  have h := essentialMeasureValue_le_tail
    (0 : PModule.{u,0,u} k ℝ) hab hbc
  rw [zero_tail_zero k hab hbc] at h
  omega

private theorem constant_essentialMultiplicity_zero (birth : Cut ℝ) :
    moduleEssentialMultiplicity (constant k) (constant_qTame k) birth = 0 := by
  by_contra hn
  have hp := Nat.pos_of_ne_zero hn
  obtain ⟨U, hU, hbU⟩ :=
    moduleEssentialMultiplicity_visible_of_pos (constant k) (constant_qTame k) hp
  obtain ⟨a, b, hab, rfl⟩ := hU
  have hle := moduleEssentialMultiplicity_le_content (constant k) (constant_qTame k)
    (cutCell_mem_cutCells a b) hbU
  rw [essentialCutContent_apply (constant k) (constant_qTame k) hab,
    constant_essential_zero k hab] at hle
  omega

private theorem zero_essentialMultiplicity_zero (birth : Cut ℝ) :
    moduleEssentialMultiplicity (0 : PModule.{u,0,u} k ℝ) (zero_qTame k) birth = 0 := by
  by_contra hn
  have hp := Nat.pos_of_ne_zero hn
  obtain ⟨U, hU, hbU⟩ :=
    moduleEssentialMultiplicity_visible_of_pos
      (0 : PModule.{u,0,u} k ℝ) (zero_qTame k) hp
  obtain ⟨a, b, hab, rfl⟩ := hU
  have hle := moduleEssentialMultiplicity_le_content
    (0 : PModule.{u,0,u} k ℝ) (zero_qTame k)
    (cutCell_mem_cutCells a b) hbU
  rw [essentialCutContent_apply (0 : PModule.{u,0,u} k ℝ) (zero_qTame k) hab,
    zero_essential_zero k hab] at hle
  omega

/-- The actual constant scalar module has no extracted finite-birth occurrence,
including on the death-at-infinity boundary. -/
theorem constant_multiplicity_zero (p : Cut ℝ × Cut ℝ) :
    moduleExtendedDiagramMultiplicity (constant k) (constant_qTame k) p = 0 := by
  by_cases h : p.2 = infinityCut
  · simp [moduleExtendedDiagramMultiplicity, h, constant_essentialMultiplicity_zero k]
  · simp only [moduleExtendedDiagramMultiplicity, if_neg h]
    apply moduleDiagramMultiplicity_eq_zero_of_rectangle_zero
    intro a b c d hab hbc hcd
    exact constant_rectangle_zero k hab.le hbc.le hcd.le

/-- The actual zero module also has zero multiplicity at every decorated cut pair. -/
theorem zero_multiplicity_zero (p : Cut ℝ × Cut ℝ) :
    moduleExtendedDiagramMultiplicity (0 : PModule.{u,0,u} k ℝ) (zero_qTame k) p = 0 := by
  by_cases h : p.2 = infinityCut
  · simp [moduleExtendedDiagramMultiplicity, h, zero_essentialMultiplicity_zero k]
  · simp only [moduleExtendedDiagramMultiplicity, if_neg h]
    apply moduleDiagramMultiplicity_eq_zero_of_rectangle_zero
    intro a b c d hab hbc hcd
    exact zero_rectangle_zero k hab.le hbc.le hcd.le

/-- The canonical finite-birth diagrams of the actual constant and zero modules coincide. -/
theorem canonical_diagrams_eq :
    LocallyFiniteDecoratedDiagram.ofQModule (constant_qTame k) =
      LocallyFiniteDecoratedDiagram.ofQModule (zero_qTame k) := by
  apply LocallyFiniteDecoratedDiagram.ext
  funext p
  exact (constant_multiplicity_zero k p).trans (zero_multiplicity_zero k p).symm

/-- Their canonical finite-birth diagram bottleneck distance is zero. -/
theorem canonical_bottleneck_zero :
    LocallyFiniteDecoratedDiagram.bottleneck
      (LocallyFiniteDecoratedDiagram.ofQModule (constant_qTame k))
      (LocallyFiniteDecoratedDiagram.ofQModule (zero_qTame k)) = 0 := by
  rw [canonical_diagrams_eq k]
  exact LocallyFiniteDecoratedDiagram.bottleneck_self _

/-- No finite radius interleaves the actual constant scalar module with zero. -/
theorem constant_not_interleaved_zero (ε : ℝ≥0) :
    ¬ Nonempty (RealInterleaving ε (constant k) 0) := by
  intro hi
  have htrans := (RealInterleaving.nonempty_zero_iff ε (constant k)).mp hi
  have happ := congrArg (fun z => z.app (0 : ℝ)) htrans
  have hzero : (𝟙 (ModuleCat.of k k) : _ ⟶ _) = 0 := by
    change structureMap (constant k)
      (show (0 : ℝ) ≤ 0 + ((ε + ε : ℝ≥0) : ℝ) from by positivity) = 0 at happ
    change (𝟙 (ModuleCat.of k k) : _ ⟶ _) = 0 at happ
    exact happ
  have hs : Subsingleton k := ModuleCat.isZero_iff_subsingleton.mp
    ((IsZero.iff_id_eq_zero _).mpr hzero)
  exact (zero_ne_one : (0 : k) ≠ 1) (hs.elim _ _)

/-- The actual real interleaving distance is infinite. -/
theorem constant_distance_top :
    realInterleavingDistance (constant k) 0 = ⊤ :=
  realInterleavingDistance_eq_top_iff.mpr fun ε =>
    not_nonempty_iff.mp (constant_not_interleaved_zero k ε)

/-- No finite threshold bounds the constant module's nonzero left tail. -/
theorem constant_no_zero_left_bound :
    ∀ a : ℝ, ∃ t : ℝ, t < a ∧ ¬ IsZero ((constant k).obj t) := by
  intro a
  refine ⟨a - 1, by linarith, ?_⟩
  change ¬ IsZero (ModuleCat.of k k)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact not_subsingleton k

/-- Canonical finite-birth bottleneck zero does not imply finite module distance
without a left-bound condition. Both distances use the actual modules and extractor. -/
theorem canonical_zero_but_module_distance_top :
    LocallyFiniteDecoratedDiagram.ofQModule (constant_qTame k) =
        LocallyFiniteDecoratedDiagram.ofQModule (zero_qTame k) ∧
      LocallyFiniteDecoratedDiagram.bottleneck
        (LocallyFiniteDecoratedDiagram.ofQModule (constant_qTame k))
        (LocallyFiniteDecoratedDiagram.ofQModule (zero_qTame k)) = 0 ∧
      realInterleavingDistance (constant k) 0 = ⊤ :=
  ⟨canonical_diagrams_eq k, canonical_bottleneck_zero k, constant_distance_top k⟩

end TDA.Persistence.WholeLineObstructionExamples
