import TDA.Persistence.ModuleScaling
import TDA.Persistence.ConstructibleScaleBarcode
import TDA.Persistence.SublevelScaling
import TDA.Persistence.DiagramBottleneckScalingExamples
import TDA.Persistence.RealInterleavingExamples
import TDA.Persistence.SublevelConstructibleExamples
import TDA.Persistence.FiniteFilterStabilitySingletonExamples
import TDA.Filtration.FilterFunctionMapExamples
import TDA.Filtration.CechExamples

/-!
# Fixtures for positive scaling of real persistence modules

These fixtures instantiate the module scaling, sublevel bridge, finite-constructible isometry,
infinite-distance, boundary, and logarithmic-shift statements on the concrete examples already
used by the persistence library.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.ModuleScalingExamples

open CategoryTheory CategoryTheory.Limits
open TDA.Filtration TDA.Simplicial
open TDA.Filtration.Cech.Examples
open TDA.Persistence.FiniteConstructible
open TDA.Persistence.ScalingExamples
open TDA.Persistence.SublevelConstructibleExamples
open TDA.Persistence.StabilityExamples
open scoped Classical ENNReal NNReal ZeroObject

variable {R : Type u} [Ring R]

/-! ### Generic scaling at one -/

private theorem twoPoints_value_le_two (σ : TotalFace (Rips.fullComplex (Fin 2))) :
    (Rips.filter TwoPoints.metric).value σ ≤ 2 := by
  rw [Rips.filter_value]
  have hsub : σ.val ⊆ ({0, 1} : Finset (Fin 2)) := by
    intro v hv
    fin_cases v <;> simp
  calc
    Rips.diameter TwoPoints.metric σ.val ≤ Rips.diameter TwoPoints.metric {0, 1} :=
      Rips.diameter_mono _ hsub
    _ = 2 := by rw [Rips.diameter_pair, TwoPoints.metric_dist, TwoPoints.dist_pts]

private theorem twoPoints_scaled_value_difference_le
    (σ : TotalFace (Rips.fullComplex (Fin 2))) :
    |(Rips.filter TwoPoints.metric).value σ -
        ((Rips.filter TwoPoints.metric).scale 2 two_pos).value σ| ≤ 2 := by
  let v := (Rips.filter TwoPoints.metric).value σ
  have hv0 : 0 ≤ v := by
    dsimp [v]
    exact Rips.diameter_nonneg _ _
  have hv2 : v ≤ 2 := twoPoints_value_le_two σ
  rw [FilterFunction.scale_value]
  change |v - 2 * v| ≤ 2
  rw [show v - 2 * v = -v by ring, abs_neg, abs_of_nonneg hv0]
  exact hv2

/-- The distance law at factor one, proved directly from the generic scaling theorem. -/
theorem scaleOne_distance (M N : PModule.{u,0,w} R ℝ) :
    realInterleavingDistance (PModule.scale 1 one_pos M) (PModule.scale 1 one_pos N) =
      realInterleavingDistance M N := by
  rw [realInterleavingDistance_scale 1 one_pos, ENNReal.ofReal_one, one_mul]

/-- The distance at factor one also follows from the two scaling-unit isomorphisms. -/
theorem scaleOne_distance_of_iso (M N : PModule.{u,0,w} R ℝ) :
    realInterleavingDistance (PModule.scale 1 one_pos M) (PModule.scale 1 one_pos N) =
      realInterleavingDistance M N :=
  realInterleavingDistance_congr (PModule.scaleOneIso M) (PModule.scaleOneIso N)

/-- At factor one, the module-diagram formula reduces to `Diagram.scale_one`. -/
theorem scaleOne_moduleDiagram {n : ℕ} {k : Type u} [Field k]
    (g : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (g i))) :
    moduleDiagram (FiniteConstructible.scaleGrid 1 one_pos g)
        (PModule.scale 1 one_pos M)
        (FiniteConstructible.finiteDimensional_scaledCritical hfd 1 one_pos) =
      moduleDiagram g M hfd := by
  rw [FiniteConstructible.moduleDiagram_scale, Diagram.scale_one]

/-! ### Two points and the sublevel bridge -/

/-- Scaling the two-point Rips sublevel module agrees with the module-level scaling law. -/
theorem twoPoints_sublevelModule_scale (n : ℕ) :
    sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n =
      PModule.scale 2 two_pos (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) n) :=
  sublevelModule_scale (ZMod 2) n (Rips.filter TwoPoints.metric) 2 two_pos

private theorem twoPoints_scale_sublevel_four :
    ((Rips.filter TwoPoints.metric).scale 2 two_pos).sublevel 4 =
      (Rips.filter TwoPoints.metric).sublevel 2 := by
  rw [FilterFunction.scale_sublevel]
  norm_num

private theorem twoPoints_scale_sublevel_two :
    ((Rips.filter TwoPoints.metric).scale 2 two_pos).sublevel 2 =
      (Rips.filter TwoPoints.metric).sublevel 1 := by
  rw [FilterFunction.scale_sublevel]
  norm_num

/-- The scaled two-point module at `4` is the homology of the original sublevel at `2`. -/
theorem twoPoints_scale_four_homology (n : ℕ) :
    (sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n).obj 4 =
      simplicialHomology ((Rips.filter TwoPoints.metric).sublevel 2) (ZMod 2) n := by
  rw [simplicialHomologyPModule_obj]
  change simplicialHomology
      (((Rips.filter TwoPoints.metric).scale 2 two_pos).sublevel 4) (ZMod 2) n = _
  rw [twoPoints_scale_sublevel_four]

/-- The edge belongs to the original two-point sublevel at the scaled threshold `4`. -/
theorem twoPoints_scale_four_edge_mem :
    TwoPoints.edge ∈ (Rips.filter TwoPoints.metric).sublevel 2 :=
  TwoPoints.edge_mem_rips_two

/-- The scaled two-point module at `2` is the homology of the original sublevel at `1`. -/
theorem twoPoints_scale_two_homology (n : ℕ) :
    (sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n).obj 2 =
      simplicialHomology ((Rips.filter TwoPoints.metric).sublevel 1) (ZMod 2) n := by
  rw [simplicialHomologyPModule_obj]
  change simplicialHomology
      (((Rips.filter TwoPoints.metric).scale 2 two_pos).sublevel 2) (ZMod 2) n = _
  rw [twoPoints_scale_sublevel_two]

/-- The edge is absent from the original two-point sublevel at the scaled threshold `2`. -/
theorem twoPoints_scale_two_edge_not_mem :
    TwoPoints.edge ∉ (Rips.filter TwoPoints.metric).sublevel 1 :=
  TwoPoints.edge_not_mem_rips_one

/-- The scaled two-point Rips module diagram is the scaled original diagram in every degree. -/
theorem twoPoints_moduleDiagram_scale (n : ℕ) :
    moduleDiagram (FiniteConstructible.scaleGrid 2 two_pos
        (Rips.filter TwoPoints.metric).criticalValue)
        (sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n)
        (sublevelModule_scale_finiteDimensional (k := ZMod 2) (n := n)
          (Rips.filter TwoPoints.metric) 2 two_pos) =
      (dgm (ZMod 2) (Rips.filter TwoPoints.metric) n).scale 2 two_pos := by
  calc
    _ = dgm (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n :=
      moduleDiagram_sublevelModule_scale (k := ZMod 2) n
        (Rips.filter TwoPoints.metric) 2 two_pos
    _ = (dgm (ZMod 2) (Rips.filter TwoPoints.metric) n).scale 2 two_pos :=
      dgm_scale (ZMod 2) (Rips.filter TwoPoints.metric) n two_pos

/-- The two-point Rips diagram scaling fixture in degree zero. -/
theorem twoPoints_moduleDiagram_scale_zero :
    moduleDiagram (FiniteConstructible.scaleGrid 2 two_pos
        (Rips.filter TwoPoints.metric).criticalValue)
        (sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) 0)
        (sublevelModule_scale_finiteDimensional (k := ZMod 2) (n := 0)
          (Rips.filter TwoPoints.metric) 2 two_pos) =
      (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).scale 2 two_pos :=
  twoPoints_moduleDiagram_scale 0

/-- The two-point Rips diagram scaling fixture in degree one. -/
theorem twoPoints_moduleDiagram_scale_one :
    moduleDiagram (FiniteConstructible.scaleGrid 2 two_pos
        (Rips.filter TwoPoints.metric).criticalValue)
        (sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) 1)
        (sublevelModule_scale_finiteDimensional (k := ZMod 2) (n := 1)
          (Rips.filter TwoPoints.metric) 2 two_pos) =
      (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 1).scale 2 two_pos :=
  twoPoints_moduleDiagram_scale 1

/-- The two-point Rips modules at factors one and two are at distance at most `2`. -/
theorem twoPoints_distance_scale_le (n : ℕ) :
    realInterleavingDistance (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) n)
        (sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n) ≤
      2 := by
  apply realInterleavingDistance_sublevel_le (ZMod 2) n
  intro σ
  exact twoPoints_scaled_value_difference_le σ

/-! ### Scaled Čech--Rips comparisons -/

/-- Scaling the two-point Čech--Rips sublevel distance multiplies it by `2`. -/
theorem twoPoints_cech_rips_distance_scale (n : ℕ) :
    realInterleavingDistance
        (sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n)
        (sublevelModule (ZMod 2) ((Cech.filter TwoPoints.pts).scale 2 two_pos) n) =
      ENNReal.ofReal 2 * realInterleavingDistance
        (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) n)
        (sublevelModule (ZMod 2) (Cech.filter TwoPoints.pts) n) :=
  realInterleavingDistance_sublevelModule_scale (ZMod 2) n
    (Rips.filter TwoPoints.metric) (Cech.filter TwoPoints.pts) 2 two_pos

/-- The scaled Čech--Rips module distance is the bottleneck of the scaled actual diagrams. -/
theorem twoPoints_cech_rips_scale_isometry (n : ℕ) :
    realInterleavingDistance
        (sublevelModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n)
        (sublevelModule (ZMod 2) ((Cech.filter TwoPoints.pts).scale 2 two_pos) n) =
      bottleneck (dgm (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n)
        (dgm (ZMod 2) ((Cech.filter TwoPoints.pts).scale 2 two_pos) n) := by
  exact (bottleneck_dgm_eq_realInterleavingDistance (ZMod 2) n
    ((Rips.filter TwoPoints.metric).scale 2 two_pos)
    ((Cech.filter TwoPoints.pts).scale 2 two_pos)).symm

/-- The scaled Čech--Rips bottleneck agrees with the diagram scaling law. -/
theorem twoPoints_cech_rips_bottleneck_scale (n : ℕ) :
    bottleneck (dgm (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) n)
        (dgm (ZMod 2) ((Cech.filter TwoPoints.pts).scale 2 two_pos) n) =
      ENNReal.ofReal 2 * bottleneck (dgm (ZMod 2) (Rips.filter TwoPoints.metric) n)
        (dgm (ZMod 2) (Cech.filter TwoPoints.pts) n) :=
  bottleneck_dgm_scale (ZMod 2) (Rips.filter TwoPoints.metric)
    (Cech.filter TwoPoints.pts) n two_pos

/-! ### Infinite distances -/

/-- The essential interval has infinite distance from the zero module. -/
theorem essential_distance_top :
    realInterleavingDistance
        (RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))) 0 = ⊤ :=
  by
    apply realInterleavingDistance_eq_top_iff.mpr
    intro ε
    exact not_nonempty_iff.mp
      (RealInterleavingExamples.essential_interval_not_interleaved (k := ℚ) ε)

/-- Positive scaling preserves the infinite distance of the essential interval. -/
theorem essential_scale_distance_top {c : ℝ} (hc : 0 < c) :
    realInterleavingDistance
        (PModule.scale c hc (RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))))
        (PModule.scale c hc (0 : PModule.{0,0,0} ℚ ℝ)) = ⊤ := by
  apply (realInterleavingDistance_scale_eq_top_iff c hc _ _).2
  exact essential_distance_top

/-- The filled and hollow degree-one module diagrams have different essential counts. -/
theorem filled_hollow_bottleneck_top :
    bottleneck
        (moduleDiagram filledReal.criticalValue
          (sublevelModule (ZMod 2) filledReal 1)
          (sublevelModule_finiteDimensional (ZMod 2) 1 filledReal))
        (moduleDiagram hollowReal.criticalValue
          (sublevelModule (ZMod 2) hollowReal 1)
          (sublevelModule_finiteDimensional (ZMod 2) 1 hollowReal)) = ⊤ := by
  apply (bottleneck_eq_top_iff _ _).2
  rw [filledReal_moduleDiagram_one, hollowReal_moduleDiagram_one]
  exact fun h => Nat.zero_ne_one h

/-- The filled and hollow degree-one sublevel modules have infinite distance. -/
theorem filled_hollow_distance_top :
    realInterleavingDistance (sublevelModule (ZMod 2) filledReal 1)
        (sublevelModule (ZMod 2) hollowReal 1) = ⊤ := by
  apply (distance_eq_top_iff_essential_card_ne
    (sublevelModule_isConstructible (ZMod 2) 1 filledReal)
    (sublevelModule_isConstructible (ZMod 2) 1 hollowReal)
    (sublevelModule_finiteDimensional (ZMod 2) 1 filledReal)
    (sublevelModule_finiteDimensional (ZMod 2) 1 hollowReal)).2
  rw [filledReal_moduleDiagram_one, hollowReal_moduleDiagram_one]
  exact fun h => Nat.zero_ne_one h

/-- Positive scaling keeps the filled--hollow degree-one distance infinite. -/
theorem filled_hollow_scale_distance_top {c : ℝ} (hc : 0 < c) :
    realInterleavingDistance
        (sublevelModule (ZMod 2) (filledReal.scale c hc) 1)
        (sublevelModule (ZMod 2) (hollowReal.scale c hc) 1) = ⊤ := by
  rw [sublevelModule_scale, sublevelModule_scale]
  exact (realInterleavingDistance_scale_eq_top_iff c hc _ _).2 filled_hollow_distance_top

/-- The bottleneck route also keeps the filled--hollow scaled diagrams at `⊤`. -/
theorem filled_hollow_scale_bottleneck_top {c : ℝ} (hc : 0 < c) :
    bottleneck
        (moduleDiagram (FiniteConstructible.scaleGrid c hc filledReal.criticalValue)
          (PModule.scale c hc (sublevelModule (ZMod 2) filledReal 1))
          (FiniteConstructible.finiteDimensional_scaledCritical
            (sublevelModule_finiteDimensional (ZMod 2) 1 filledReal) c hc))
        (moduleDiagram (FiniteConstructible.scaleGrid c hc hollowReal.criticalValue)
          (PModule.scale c hc (sublevelModule (ZMod 2) hollowReal 1))
          (FiniteConstructible.finiteDimensional_scaledCritical
            (sublevelModule_finiteDimensional (ZMod 2) 1 hollowReal) c hc)) = ⊤ := by
  calc
    _ = ENNReal.ofReal c * realInterleavingDistance
        (sublevelModule (ZMod 2) filledReal 1)
        (sublevelModule (ZMod 2) hollowReal 1) :=
      FiniteConstructible.bottleneck_moduleDiagram_scale
        (sublevelModule_isConstructible (ZMod 2) 1 filledReal)
        (sublevelModule_isConstructible (ZMod 2) 1 hollowReal)
        (sublevelModule_finiteDimensional (ZMod 2) 1 filledReal)
        (sublevelModule_finiteDimensional (ZMod 2) 1 hollowReal) c hc
    _ = ⊤ := by
      rw [filled_hollow_distance_top,
        ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne']

/-! ### The one-vertex value and a short interval -/

/-- The scaled one-vertex module distance is `ofReal (c * |a - b|)`. -/
theorem vertex_scale_distance (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    realInterleavingDistance
        (sublevelModule (ZMod 2) ((vertexFilter a).scale c hc) 0)
        (sublevelModule (ZMod 2) ((vertexFilter b).scale c hc) 0) =
      ENNReal.ofReal (c * |a - b|) := by
  rw [realInterleavingDistance_sublevelModule_scale, vertex_distance_eq]
  rw [← ENNReal.ofReal_mul hc.le]

/-- The same vertex distance follows from scaling the filter values first. -/
theorem vertex_scale_distance_of_filter (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    realInterleavingDistance
        (sublevelModule (ZMod 2) ((vertexFilter a).scale c hc) 0)
        (sublevelModule (ZMod 2) ((vertexFilter b).scale c hc) 0) =
      ENNReal.ofReal (c * |a - b|) := by
  rw [vertexFilter_scale a hc, vertexFilter_scale b hc, vertex_distance_eq]
  rw [← mul_sub, abs_mul, abs_of_pos hc]

/-- Scaling the one-interleaved interval by `2` gives a distance at most `2`. -/
theorem short_interval_scale_le :
    realInterleavingDistance
        (PModule.scale 2 two_pos
          (RealBarcode.intervalModule (k := ℚ) (0, (2 : WithTop ℝ))))
        (PModule.scale 2 two_pos (0 : PModule.{0,0,0} ℚ ℝ)) ≤ 2 := by
  obtain ⟨i⟩ := RealInterleavingExamples.short_interval_one_interleaved (k := ℚ)
  simpa using (RealInterleaving.distance_le (i.scale 2 two_pos))

/-! ### The negative and zero boundary controls -/

/-- A negative factor cannot define the monotone reindexing used by scaling. -/
theorem neg_factor_not_monotone {c : ℝ} (hc : c < 0) :
    ¬ Monotone (fun t : ℝ => c⁻¹ * t) := by
  intro hmono
  have h := hmono (show (-1 : ℝ) ≤ 1 by norm_num)
  have hinv : c⁻¹ < 0 := inv_neg''.2 hc
  nlinarith

private noncomputable def constReindexIso (M : PModule.{0,0,0} ℚ ℝ) :
    reindex (OrderHom.const ℝ (0 : ℝ)) M ≅ (Functor.const ℝ).obj (M.obj 0) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros X Y f
    change M.map (𝟙 (0 : ℝ)) ≫ 𝟙 (M.obj 0) = 𝟙 (M.obj 0) ≫ 𝟙 (M.obj 0)
    rw [M.map_id])

private noncomputable def constZeroReindexIso :
    reindex (OrderHom.const ℝ (0 : ℝ)) (0 : PModule.{0,0,0} ℚ ℝ) ≅
      (0 : PModule.{0,0,0} ℚ ℝ) :=
  NatIso.ofComponents
    (fun x =>
      (Functor.zero_obj ((OrderHom.const ℝ (0 : ℝ)) x)).iso
        (Functor.zero_obj x))
    (by
      intros X Y f
      exact (Functor.zero_obj ((OrderHom.const ℝ (0 : ℝ)) X)).eq_of_src _ _)

private theorem essential_interval_obj_not_isZero :
    ¬ IsZero ((RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))).obj 0) := by
  intro hzero
  have hs : Subsingleton (RealBarcode.fiber (k := ℚ) (0, (⊤ : WithTop ℝ)) 0) :=
    ModuleCat.isZero_iff_subsingleton.mp hzero
  let one : RealBarcode.fiber (k := ℚ) (0, (⊤ : WithTop ℝ)) 0 :=
    ⟨1, by simp [RealBarcode.fiber, RealBarcode.alive]⟩
  have heq := hs.elim (0 : RealBarcode.fiber (k := ℚ) (0, (⊤ : WithTop ℝ)) 0) one
  exact (zero_ne_one : (0 : ℚ) ≠ 1) (congrArg Subtype.val heq)

private theorem const_essential_distance_top :
    realInterleavingDistance
        ((Functor.const ℝ).obj
          ((RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))).obj 0))
        (0 : PModule.{0,0,0} ℚ ℝ) = ⊤ := by
  apply realInterleavingDistance_eq_top_iff.mpr
  intro ε
  apply not_nonempty_iff.mp
  intro hi
  have htrans := (RealInterleaving.nonempty_zero_iff ε
    ((Functor.const ℝ).obj
      ((RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))).obj 0))).mp hi
  have happ := congrArg (fun z => z.app (0 : ℝ)) htrans
  have hzero : (𝟙 (((Functor.const ℝ).obj
      ((RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))).obj 0)).obj 0) :
      _ ⟶ _) = 0 := by
    change structureMap ((Functor.const ℝ).obj
      ((RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))).obj 0))
        (show (0 : ℝ) ≤ 0 + ((ε + ε : ℝ≥0) : ℝ) from by positivity) = 0 at happ
    change ((Functor.const ℝ).obj
      ((RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))).obj 0)).map _ = 0 at happ
    change (𝟙 ((RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))).obj 0) :
      _ ⟶ _) = 0 at happ
    exact happ
  exact essential_interval_obj_not_isZero
    ((IsZero.iff_id_eq_zero _).mpr hzero)

/-- Reindexing both modules by the zero order hom still leaves the essential module at distance `⊤`. -/
theorem zero_factor_distance_top :
    realInterleavingDistance
        (reindex (OrderHom.const ℝ (0 : ℝ))
          (RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))))
        (reindex (OrderHom.const ℝ (0 : ℝ)) (0 : PModule.{0,0,0} ℚ ℝ)) = ⊤ := by
  calc
    _ = realInterleavingDistance
        ((Functor.const ℝ).obj
          ((RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))).obj 0))
        (0 : PModule.{0,0,0} ℚ ℝ) :=
      realInterleavingDistance_congr (constReindexIso _) (constZeroReindexIso)
    _ = ⊤ := const_essential_distance_top

/-- The zero-factor analogue of the positive scaling law fails on the essential interval. -/
theorem zero_factor_law_fails :
    realInterleavingDistance
        (reindex (OrderHom.const ℝ (0 : ℝ))
          (RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))))
        (reindex (OrderHom.const ℝ (0 : ℝ)) (0 : PModule.{0,0,0} ℚ ℝ)) = ⊤ ∧
      ENNReal.ofReal 0 * realInterleavingDistance
        (RealBarcode.intervalModule (k := ℚ) (0, (⊤ : WithTop ℝ))) 0 = 0 := by
  refine ⟨zero_factor_distance_top, ?_⟩
  simp

/-! ### Logarithmic scaling -/

private theorem twoPoints_logModule_scale_shiftIso_source_obj (t : ℝ) :
    ((RealShift.shift (logParam 2)).obj
        (logModule (ZMod 2) ((Rips.filter TwoPoints.metric).scale 2 two_pos) 1)).obj t =
      (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) 1).obj
        ((2 : ℝ)⁻¹ * Real.exp (t + (logParam 2 : ℝ))) := by
  rw [RealShift.shift_obj, logModule_eq_reindex, sublevelModule_scale]
  rfl

private theorem twoPoints_logModule_scale_shiftIso_target_obj (t : ℝ) :
    (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) 1).obj (Real.exp t) =
      (logModule (ZMod 2) (Rips.filter TwoPoints.metric) 1).obj t := by
  rw [logModule_eq_reindex]
  rfl

private theorem twoPoints_logModule_scale_shiftIso_index (t : ℝ) :
    (2 : ℝ)⁻¹ * Real.exp (t + (logParam 2 : ℝ)) = Real.exp t := by
  rw [exp_add_logParam (by norm_num : (1 : ℝ) ≤ 2) t]
  exact inv_mul_cancel_left₀ (by norm_num) _

/-- The two-point degree-one log-scale comparison has the explicit transport at every time. -/
theorem twoPoints_logModule_scale_shiftIso_hom_app (t : ℝ) :
    (logModule_scale_shiftIso (ZMod 2) 1 (Rips.filter TwoPoints.metric)
        two_pos (by norm_num : (1 : ℝ) ≤ 2)).hom.app t =
      eqToHom (twoPoints_logModule_scale_shiftIso_source_obj t) ≫
        (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) 1).map
          (eqToHom (twoPoints_logModule_scale_shiftIso_index t)) ≫
        eqToHom (twoPoints_logModule_scale_shiftIso_target_obj t) := by
  exact logModule_scale_shiftIso_hom_app (ZMod 2) 1
    (Rips.filter TwoPoints.metric) two_pos (by norm_num : (1 : ℝ) ≤ 2) t

end TDA.Persistence.ModuleScalingExamples
