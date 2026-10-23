import TDA.Persistence.SupportInterval
import TDA.Persistence.AlgebraicFamily
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Real interval examples

Whole-line, left-tail and singleton supports exhibit the endpoint conventions.
A disjoint infinite interval family accumulates at zero and has at most one
active occurrence at each parameter.
-/

set_option autoImplicit false

namespace TDA.Persistence.RealIntervalExamples

open CategoryTheory
open Filter Topology

/-- The whole-line interval module retains every coefficient along every map. -/
noncomputable abbrev wholeLine : PModule ℚ ℝ :=
  SupportInterval.module (k := ℚ) (Set.univ : Set ℝ) Set.ordConnected_univ

theorem wholeLine_map_preserves_coefficients {s t : ℝ} (h : s ≤ t)
    (x : SupportInterval.fiber (k := ℚ) (Set.univ : Set ℝ) s) :
    ((structureMapLinear wholeLine h x :
      SupportInterval.fiber (k := ℚ) (Set.univ : Set ℝ) t) : ℚ) = (x : ℚ) := by
  simpa [wholeLine] using
    (SupportInterval.structureMap_val (k := ℚ) (Set.univ : Set ℝ)
      Set.ordConnected_univ h x)

noncomputable abbrev leftClosedRay (a : ℝ) : PModule ℚ ℝ :=
  SupportInterval.module (k := ℚ) (Set.Iic a) inferInstance

noncomputable abbrev leftOpenRay (a : ℝ) : PModule ℚ ℝ :=
  SupportInterval.module (k := ℚ) (Set.Iio a) inferInstance

/-- Every point strictly below the endpoint still carries a nonzero open-tail fiber. -/
theorem leftOpen_fiber_nonzero_below (a p : ℝ) (h : p < a) :
    ∃ x : SupportInterval.fiber (k := ℚ) (Set.Iio a) p, (x : ℚ) = 1 := by
  refine ⟨SupportInterval.one (k := ℚ) (Set.Iio a) (p := p)
    (Set.mem_Iio.mpr h), ?_⟩
  simp [SupportInterval.one]

/-- A closed left tail includes its finite endpoint and carries a nonzero fiber there. -/
theorem leftClosed_endpoint_nonzero (a : ℝ) :
    ∃ x : SupportInterval.fiber (k := ℚ) (Set.Iic a) a, (x : ℚ) = 1 := by
  refine ⟨SupportInterval.one (k := ℚ) (Set.Iic a) (p := a)
    (Set.mem_Iic.mpr le_rfl), ?_⟩
  simp [SupportInterval.one]

/-- The closed tail's map to the endpoint preserves the unit coefficient. -/
theorem leftClosed_map_to_endpoint (a p : ℝ) (h : p ≤ a) :
    structureMapLinear (leftClosedRay a) h
      (SupportInterval.one (k := ℚ) (Set.Iic a) (p := p) (Set.mem_Iic.mpr h)) =
    SupportInterval.one (k := ℚ) (Set.Iic a) (p := a) (Set.mem_Iic.mpr le_rfl) := by
  apply Subtype.ext
  rw [SupportInterval.structureMap_val]
  simp [SupportInterval.one]

/-- The open tail omits its finite endpoint, even though it is nonempty arbitrarily near it. -/
theorem leftOpen_endpoint_is_zero (a : ℝ) :
    Subsingleton ((leftOpenRay a).obj a) := by
  change Subsingleton (SupportInterval.fiber (k := ℚ) (Set.Iio a) a)
  constructor
  intro x y
  apply Subtype.ext
  have hx := SupportInterval.val_eq_zero (k := ℚ) (Set.Iio a)
    (show a ∉ Set.Iio a by simp) x
  have hy := SupportInterval.val_eq_zero (k := ℚ) (Set.Iio a)
    (show a ∉ Set.Iio a by simp) y
  exact hx.trans hy.symm

/-- Its transition into the omitted endpoint is the zero map. -/
theorem leftOpen_map_to_endpoint_is_zero (a p : ℝ) (h : p < a) :
    structureMapLinear (leftOpenRay a) (le_of_lt h) = 0 := by
  apply (SupportInterval.structureMap_eq_zero_iff (k := ℚ) (Set.Iio a)
    (inferInstance : (Set.Iio a).OrdConnected) (le_of_lt h)).2
  rintro ⟨_, ha⟩
  simp only [Set.mem_Iio] at ha
  exact (lt_irrefl a) ha

noncomputable abbrev singletonInterval (a : ℝ) : PModule ℚ ℝ :=
  SupportInterval.module (k := ℚ) ({a} : Set ℝ) inferInstance

/-- A singleton interval remains visible as a nonzero fiber. -/
theorem singleton_fiber_nonzero (a : ℝ) :
    ∃ x : SupportInterval.fiber (k := ℚ) ({a} : Set ℝ) a, (x : ℚ) = 1 := by
  refine ⟨SupportInterval.one (k := ℚ) ({a} : Set ℝ) (p := a) (by simp), ?_⟩
  simp [SupportInterval.one]

/-- Every strict map in a singleton-supported module vanishes. -/
theorem singleton_strict_map_zero {s t a : ℝ} (h : s < t) :
    structureMapLinear (singletonInterval a) (le_of_lt h) = 0 := by
  apply (SupportInterval.structureMap_eq_zero_iff (k := ℚ) ({a} : Set ℝ)
    (inferInstance : ({a} : Set ℝ).OrdConnected) (le_of_lt h)).2
  rintro ⟨hs, ht⟩
  simp only [Set.mem_singleton_iff] at hs ht
  subst s
  subst t
  exact (lt_irrefl a) h

/-- An empty indexing type gives an actually zero algebraic family at each parameter. -/
noncomputable def emptyFamily : Empty → PModule ℚ ℝ := fun e => Empty.elim e

theorem empty_family_fiber_is_subsingleton (t : ℝ) :
    Subsingleton ((AlgebraicFamily.familyModule emptyFamily).obj t) := by
  change Subsingleton (DirectSum Empty (fun e => (emptyFamily e).obj t))
  infer_instance

/-- Reciprocal endpoints decrease strictly to zero. -/
noncomputable def endpoint (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem endpoint_pos (n : ℕ) : 0 < endpoint n := by
  simpa [endpoint] using (Nat.one_div_pos_of_nat (α := ℝ) (n := n))

theorem endpoint_strict_antitone (n : ℕ) : endpoint (n + 1) < endpoint n := by
  simpa [endpoint] using
    (Nat.one_div_lt_one_div (α := ℝ) (Nat.lt_succ_self n))

theorem endpoint_antitone {m n : ℕ} (h : m ≤ n) : endpoint n ≤ endpoint m := by
  simpa [endpoint] using (Nat.one_div_le_one_div (α := ℝ) h)

/-- Pairwise disjoint positive intervals with endpoints converging to zero. -/
def accumulatingInterval (n : ℕ) : Set ℝ := Set.Ioc (endpoint (n + 1)) (endpoint n)

theorem accumulatingInterval_nonempty (n : ℕ) : (accumulatingInterval n).Nonempty := by
  refine ⟨endpoint n, ?_⟩
  exact ⟨endpoint_strict_antitone n, le_rfl⟩

theorem accumulatingInterval_disjoint_of_lt {i j : ℕ} (hij : i < j) :
    Disjoint (accumulatingInterval i) (accumulatingInterval j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hj : endpoint j ≤ endpoint (i + 1) := endpoint_antitone (Nat.succ_le_of_lt hij)
  exact (not_lt_of_ge (hy.2.trans hj)) hx.1

theorem accumulatingInterval_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (accumulatingInterval i) (accumulatingInterval j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact accumulatingInterval_disjoint_of_lt h
  · exact (accumulatingInterval_disjoint_of_lt h).symm

def activeIndices (x : ℝ) : Set ℕ := {n | x ∈ accumulatingInterval n}

/-- Each parameter belongs to at most one interval in the family. -/
theorem activeIndices_subsingleton (x : ℝ) : Set.Subsingleton (activeIndices x) := by
  intro i hi j hj
  by_contra hij
  exact (Set.disjoint_left.mp (accumulatingInterval_disjoint hij)) hi hj

/-- Thus the family satisfies pointwise finite activity. -/
theorem activeIndices_finite (x : ℝ) : (activeIndices x).Finite := by
  classical
  by_cases hne : (activeIndices x).Nonempty
  · rcases hne with ⟨n, hn⟩
    refine Set.Finite.subset (Set.finite_singleton n) ?_
    intro m hm
    have hmn : m = n := activeIndices_subsingleton x hm hn
    simp [hmn]
  · have hempty : activeIndices x = ∅ := by
      ext n
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hn => hne ⟨n, hn⟩
    simp [hempty]

/-- Every index is a nonempty occurrence, so infinitely many distinct intervals occur. -/
theorem infinitely_many_nonempty_occurrences :
    Set.Infinite {n : ℕ | (accumulatingInterval n).Nonempty} := by
  have hset : {n : ℕ | (accumulatingInterval n).Nonempty} = Set.univ := by
    ext n
    simp [accumulatingInterval_nonempty]
  rw [hset]
  exact Set.infinite_univ

/-- The chosen point from each occurrence converges to the accumulation parameter zero. -/
theorem occurrence_points_accumulate_at_zero :
    Tendsto endpoint atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem occurrence_point_lies_in_interval (n : ℕ) : endpoint n ∈ accumulatingInterval n :=
  ⟨endpoint_strict_antitone n, le_rfl⟩

end TDA.Persistence.RealIntervalExamples
