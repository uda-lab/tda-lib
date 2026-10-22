import TDA.Persistence.CechRipsInterleaving
import TDA.Filtration.CechExamples
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Rat

set_option autoImplicit false

/-!
# Fixtures for the log-scale Čech–Rips interleaving

The log-scale interleaving is instantiated on two points of the line over `ZMod 2` and `ℚ`
and on an acute Euclidean triangle. On two points, the parameter `log 2` is forced by the
inclusions, and every vertex is present at every log time, so the log-scale module has no
zero left tail. At radius level, the Rips doubling factors through Čech, both at a positive
radius, where it is a structure map, and at a negative radius, between empty complexes.
-/

namespace TDA.Persistence.Cech.RipsInterleavingExamples

open CategoryTheory TDA.Simplicial TDA.Filtration TDA.Persistence
open TDA.Filtration.Cech.Examples
open scoped NNReal ENNReal

/-! ### Two points, log scale -/

/-- The log-scale two-point Rips and Čech modules are `log 2`-interleaved in every degree. -/
noncomputable def twoPointsInterleaving (R : Type) [Ring R] (n : ℕ) :
    RealInterleaving (logParam 2) (logModule R (Rips.filter TwoPoints.metric) n)
      (logModule R (Cech.filter TwoPoints.pts) n) :=
  ripsCechLogInterleaving R n TwoPoints.metric TwoPoints.pts TwoPoints.metric_dist

noncomputable def twoPointsInterleaving_zmod (n : ℕ) :
    RealInterleaving (logParam 2) (logModule (ZMod 2) (Rips.filter TwoPoints.metric) n)
      (logModule (ZMod 2) (Cech.filter TwoPoints.pts) n) :=
  twoPointsInterleaving (ZMod 2) n

noncomputable def twoPointsInterleaving_rat (n : ℕ) :
    RealInterleaving (logParam 2) (logModule ℚ (Rips.filter TwoPoints.metric) n)
      (logModule ℚ (Cech.filter TwoPoints.pts) n) :=
  twoPointsInterleaving ℚ n

theorem twoPoints_distance_le_zmod (n : ℕ) :
    realInterleavingDistance (logModule (ZMod 2) (Rips.filter TwoPoints.metric) n)
      (logModule (ZMod 2) (Cech.filter TwoPoints.pts) n) ≤ ENNReal.ofReal (Real.log 2) :=
  realInterleavingDistance_rips_cech_log_le (ZMod 2) n TwoPoints.metric TwoPoints.pts
    TwoPoints.metric_dist

theorem twoPoints_distance_le_rat (n : ℕ) :
    realInterleavingDistance (logModule ℚ (Rips.filter TwoPoints.metric) n)
      (logModule ℚ (Cech.filter TwoPoints.pts) n) ≤ ENNReal.ofReal (Real.log 2) :=
  realInterleavingDistance_rips_cech_log_le ℚ n TwoPoints.metric TwoPoints.pts
    TwoPoints.metric_dist

/-! ### The constant `log 2` is forced by the inclusions -/

theorem twoPoints_edge_mem_cech_exp_zero :
    TwoPoints.edge ∈ (Cech.filter TwoPoints.pts).sublevel (Real.exp 0) := by
  rw [Real.exp_zero]
  exact (FilterFunction.mem_sublevel_iff_of_mem _ _ TwoPoints.edgeFace).2
    TwoPoints.cech_value.le

/-- Below `log 2`, the edge of the log-scale Čech sublevel at `t = 0` is missing from the
shifted log-scale Rips sublevel. -/
theorem twoPoints_edge_not_mem_rips {ε : ℝ≥0} (hε : (ε : ℝ) < Real.log 2) :
    TwoPoints.edge ∉ (Rips.filter TwoPoints.metric).sublevel (Real.exp (0 + ε)) := by
  intro h
  have hv := (FilterFunction.mem_sublevel_iff_of_mem _ _ TwoPoints.edgeFace).1 h
  rw [TwoPoints.rips_value, zero_add] at hv
  have := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).1 hε
  linarith

/-- Below `log 2`, the hypothesis `hGF` of the inclusion interleaving fails at `t = 0` for
the two-point log-scale filtrations. -/
theorem twoPoints_not_hGF {ε : ℝ≥0} (hε : (ε : ℝ) < Real.log 2) :
    ¬ ∀ t, Filtration.reindex expHom (Cech.filter TwoPoints.pts).sublevelFiltration t ≤
      Filtration.reindex expHom (Rips.filter TwoPoints.metric).sublevelFiltration (t + ε) :=
  fun h => twoPoints_edge_not_mem_rips hε (h 0 twoPoints_edge_mem_cech_exp_zero)

/-- At `log 2`, the edge enters the shifted log-scale Rips sublevel. -/
theorem twoPoints_edge_mem_rips_logParam :
    TwoPoints.edge ∈ (Rips.filter TwoPoints.metric).sublevel (Real.exp (0 + logParam 2)) := by
  rw [exp_add_logParam one_le_two, Real.exp_zero, mul_one]
  exact TwoPoints.edge_mem_rips_two

/-! ### No zero left tail at log scale -/

theorem twoPoints_vertex_mem_rips (t : ℝ) :
    ({0} : Finset (Fin 2)) ∈ (Rips.filter TwoPoints.metric).sublevel (Real.exp t) := by
  refine (FilterFunction.mem_sublevel_iff _ _ _).2 ⟨Finset.singleton_nonempty 0, ?_⟩
  rw [Rips.filter_value, Rips.diameter_singleton]
  exact (Real.exp_pos t).le

theorem twoPoints_vertex_mem_cech (t : ℝ) :
    ({0} : Finset (Fin 2)) ∈ (Cech.filter TwoPoints.pts).sublevel (Real.exp t) :=
  sublevel_le_sublevel_of_le
    (Cech.filter_value_le_rips TwoPoints.metric TwoPoints.pts TwoPoints.metric_dist) _
    (twoPoints_vertex_mem_rips t)

/-- In contrast, the radius-level Rips sublevel at a negative radius is empty. -/
theorem twoPoints_rips_sublevel_neg :
    (Rips.filter TwoPoints.metric).sublevel (-1) = ⊥ :=
  Rips.sublevel_eq_bot_of_neg _ (by norm_num)

/-! ### Euclidean triangle -/

/-- The log-scale Rips and Čech modules of the acute triangle are `log 2`-interleaved in
every degree. -/
noncomputable def triangleInterleaving (R : Type) [Ring R] (n : ℕ) :
    RealInterleaving (logParam 2) (logModule R (Rips.filter Triangle.metric) n)
      (logModule R (Cech.filter Triangle.pts) n) :=
  ripsCechLogInterleaving R n Triangle.metric Triangle.pts Triangle.metric_dist

noncomputable def triangleInterleaving_zero :
    RealInterleaving (logParam 2) (logModule (ZMod 2) (Rips.filter Triangle.metric) 0)
      (logModule (ZMod 2) (Cech.filter Triangle.pts) 0) :=
  triangleInterleaving (ZMod 2) 0

noncomputable def triangleInterleaving_one :
    RealInterleaving (logParam 2) (logModule (ZMod 2) (Rips.filter Triangle.metric) 1)
      (logModule (ZMod 2) (Cech.filter Triangle.pts) 1) :=
  triangleInterleaving (ZMod 2) 1

theorem triangle_distance_le (n : ℕ) :
    realInterleavingDistance (logModule (ZMod 2) (Rips.filter Triangle.metric) n)
      (logModule (ZMod 2) (Cech.filter Triangle.pts) n) ≤ ENNReal.ofReal (Real.log 2) :=
  realInterleavingDistance_rips_cech_log_le (ZMod 2) n Triangle.metric Triangle.pts
    Triangle.metric_dist

/-! ### Radius-level factorization -/

/-- At radius `1`, the composite `Rips_1 ⊆ Čech_1 ⊆ Rips_2` is the structure map. -/
theorem twoPoints_factor_one :
    (ripsToCech (ZMod 2) 0 TwoPoints.metric TwoPoints.pts TwoPoints.metric_dist ≫
        cechToRips (ZMod 2) 0 TwoPoints.metric TwoPoints.pts TwoPoints.metric_dist).app 1 =
      structureMap (sublevelModule (ZMod 2) (Rips.filter TwoPoints.metric) 0)
        (by norm_num : (1 : ℝ) ≤ 2 * 1) := by
  rw [ripsToCech_comp_cechToRips]
  exact ripsDouble_app_of_nonneg (ZMod 2) 0 TwoPoints.metric zero_le_one

theorem twoPoints_rips_sublevel_two_mul_neg :
    (Rips.filter TwoPoints.metric).sublevel (2 * -1) = ⊥ :=
  Rips.sublevel_eq_bot_of_neg _ (by norm_num)

/-- At radius `-1`, the composite is still the inclusion component, between the empty
complexes `Rips_{-1}` and `Rips_{-2}`. -/
theorem twoPoints_factor_neg_one :
    (ripsToCech (ZMod 2) 0 TwoPoints.metric TwoPoints.pts TwoPoints.metric_dist ≫
        cechToRips (ZMod 2) 0 TwoPoints.metric TwoPoints.pts TwoPoints.metric_dist).app (-1) =
      simplicialHomologyIncl (ZMod 2)
        (K := (Rips.filter TwoPoints.metric).sublevel (-1))
        (L := (Rips.filter TwoPoints.metric).sublevel (2 * -1))
        (by rw [twoPoints_rips_sublevel_neg]; exact bot_le) 0 := by
  rw [ripsToCech_comp_cechToRips]
  rfl

end TDA.Persistence.Cech.RipsInterleavingExamples
