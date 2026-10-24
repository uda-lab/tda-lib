import TDA.Persistence.RipsQTameInfiniteMetricStability
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A finite-sample limit with an infinite compact target

The reciprocal sequence together with its limit is a compact infinite metric
space. Its initial finite sets converge in Hausdorff distance, so their q-tame
Rips diagrams converge to the target diagram itself.
-/

namespace TDA.Persistence.Rips.InfiniteMetricStabilityExamples

open Filter Metric Set
open scoped Topology

noncomputable section

/-- The compact limit set consisting of zero and the positive reciprocal sequence. -/
def reciprocalTargetSet : Set ℝ :=
  insert 0 (Set.range fun n : ℕ => (1 : ℝ) / (n + 1))

/-- The reciprocal target as a metric space. -/
abbrev ReciprocalTarget := {x : ℝ // x ∈ reciprocalTargetSet}

/-- Finite initial samples of the reciprocal target, including the limit point. -/
def reciprocalSampleMap (N : ℕ) : Option (Fin (N + 1)) → ℝ
  | none => 0
  | some i => (1 : ℝ) / (i.val + 1)

private theorem reciprocalSampleMap_injective (N : ℕ) :
    Function.Injective (reciprocalSampleMap N) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j =>
          have hj : 0 < (1 : ℝ) / (j.val + 1) := by positivity
          simp [reciprocalSampleMap] at hij
          linarith
  | some i =>
      cases j with
      | none =>
          have hi : 0 < (1 : ℝ) / (i.val + 1) := by positivity
          simp [reciprocalSampleMap] at hij
          linarith
      | some j =>
          have hrecip : (1 : ℝ) / (i.val + 1) = 1 / (j.val + 1) := by
            simpa [reciprocalSampleMap] using hij
          have hden : (i.val : ℝ) + 1 = (j.val : ℝ) + 1 := by
            field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i.val),
              Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j.val)] at hrecip
            linarith
          have hval : (i.val : ℝ) = (j.val : ℝ) := by linarith
          exact congrArg some (Fin.ext (by exact_mod_cast hval))

private theorem reciprocalTargetSet_isCompact : IsCompact reciprocalTargetSet := by
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa [reciprocalTargetSet] using hlim.isCompact_insert_range

/-- The reciprocal target has infinitely many distinct points. -/
theorem reciprocalTarget_infinite : Infinite ReciprocalTarget := by
  apply Infinite.of_injective (fun n : ℕ =>
    (⟨(1 : ℝ) / (n + 1), Set.mem_insert_of_mem _ (Set.mem_range_self n)⟩ :
      ReciprocalTarget))
  intro m n h
  have h' := congrArg (fun x : ReciprocalTarget => (x : ℝ)) h
  have hden : (m : ℝ) + 1 = (n : ℝ) + 1 := by
    change (1 : ℝ) / (m + 1) = 1 / (n + 1) at h'
    field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m),
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)] at h'
    linarith
  have hmn : (m : ℝ) = n := by linarith
  exact_mod_cast hmn

private theorem reciprocalTarget_compactSpace : CompactSpace ReciprocalTarget :=
  isCompact_iff_compactSpace.mp reciprocalTargetSet_isCompact

@[instance_reducible] private def reciprocalSampleMetric
    (N : ℕ) : MetricSpace (Option (Fin (N + 1))) :=
  @MetricSpace.induced _ ℝ (reciprocalSampleMap N)
    (reciprocalSampleMap_injective N) inferInstance

private instance reciprocalSampleLinearOrder (N : ℕ) :
    LinearOrder (Option (Fin (N + 1))) :=
  LinearOrder.lift' (reciprocalSampleMap N) (reciprocalSampleMap_injective N)

private instance reciprocalSampleMetricSpace (N : ℕ) :
    MetricSpace (Option (Fin (N + 1))) := reciprocalSampleMetric N

private instance reciprocalTarget_nonempty : Nonempty ReciprocalTarget :=
  ⟨⟨0, Set.mem_insert _ _⟩⟩

private theorem reciprocalTarget_totallyBounded :
    TotallyBounded (Set.univ : Set ReciprocalTarget) := by
  letI : CompactSpace ReciprocalTarget := reciprocalTarget_compactSpace
  exact isCompact_univ.totallyBounded

/-- Finite samples of the infinite compact target converge to its complete q-tame
Rips diagram in the locally finite bottleneck distance, with sample cardinality
increasing along the sequence.
-/
theorem tendsto_reciprocalSample_qTameDiagram_bottleneck
    (k : Type*) [Field k] (n : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (qTameLocallyFiniteDiagram (X := Option (Fin (N + 1))) k
          (Set.finite_univ.totallyBounded :
            TotallyBounded (Set.univ : Set (Option (Fin (N + 1))))) n).bottleneck
          (qTameLocallyFiniteDiagram (X := ReciprocalTarget) k
            reciprocalTarget_totallyBounded n))
      atTop (𝓝 0) := by
  letI : CompactSpace ReciprocalTarget := reciprocalTarget_compactSpace
  let g : ReciprocalTarget → ℝ := Subtype.val
  have hg : Isometry g := isometry_subtype_coe
  have hY : TotallyBounded (Set.univ : Set ReciprocalTarget) :=
    isCompact_univ.totallyBounded
  let f : ∀ N, Option (Fin (N + 1)) → ℝ := reciprocalSampleMap
  have hf : ∀ N, Isometry (f N) := by
    intro N
    exact MetricSpace.isometry_induced _ (reciprocalSampleMap_injective N)
  have hhaus : ∀ N,
      hausdorffDist (Set.range (f N)) (Set.range g) ≤ (1 : ℝ) / (N + 1) := by
    intro N
    apply hausdorffDist_le_of_mem_dist (by positivity)
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      cases i with
      | none =>
          refine ⟨0, ?_, ?_⟩
          · exact ⟨⟨0, Set.mem_insert _ _⟩, rfl⟩
          · simp only [f, reciprocalSampleMap, dist_self]
            positivity
      | some i =>
          refine ⟨f N (some i), ?_, ?_⟩
          · exact ⟨⟨f N (some i), Set.mem_insert_of_mem _
              (Set.mem_range_self i.val)⟩, rfl⟩
          · simp only [dist_self]
            positivity
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      have hy : (y : ℝ) = 0 ∨ ∃ m : ℕ, (1 : ℝ) / (m + 1) = (y : ℝ) := by
        simpa [reciprocalTargetSet, Set.mem_insert_iff] using y.property
      rcases hy with hy | ⟨m, hy⟩
      · refine ⟨0, ?_, ?_⟩
        · exact ⟨none, rfl⟩
        · simpa [g, hy] using
            (show (0 : ℝ) ≤ (1 : ℝ) / (N + 1) by positivity)
      · by_cases hm : m ≤ N
        · let i : Fin (N + 1) := ⟨m, by omega⟩
          refine ⟨f N (some i), ⟨some i, rfl⟩, ?_⟩
          simp [g, f, reciprocalSampleMap, i, hy]
          positivity
        · let i : Fin (N + 1) := Fin.last N
          have hrecip : (1 : ℝ) / (m + 1) ≤ 1 / (N + 1) := by
            have hm_lt : N < m := Nat.lt_of_not_ge hm
            have hmNat : N + 1 ≤ m + 1 := by omega
            have hm' : (N : ℝ) + 1 ≤ (m : ℝ) + 1 := by
              exact_mod_cast hmNat
            exact one_div_le_one_div_of_le (by positivity) hm'
          refine ⟨f N (some i), ⟨some i, rfl⟩, ?_⟩
          simp only [g, f, reciprocalSampleMap]
          rw [← hy]
          have hlast : (i.val : ℝ) = N := by simp [i]
          rw [hlast, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hrecip)]
          have hN : 0 ≤ (1 : ℝ) / (N + 1) := by positivity
          have hm_nonneg : 0 ≤ (1 : ℝ) / (m + 1) := by positivity
          linarith
  have hhausTendsto :
      Filter.Tendsto (fun N : ℕ => hausdorffDist (Set.range (f N)) (Set.range g))
        atTop (𝓝 0) := by
    have hr : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
      (fun _ => hausdorffDist_nonneg) hhaus
  exact tendsto_qTameLocallyFiniteDiagram_bottleneck_of_hausdorffDist_tendsto_zero
    (k := k) (X := fun N => Option (Fin (N + 1))) ReciprocalTarget
    (f := f) (g := g) hf hg hY hhausTendsto n

end
end TDA.Persistence.Rips.InfiniteMetricStabilityExamples
