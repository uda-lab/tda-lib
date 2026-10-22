import TDA.Filtration.CechExamples
import TDA.Persistence.Reduction.TriangleSublevelDiagrams
import TDA.Persistence.SublevelDiagramMonotone
import TDA.Persistence.LogScaleDiagramComparison
import TDA.Persistence.LogScaleDiagramExamples
import TDA.Persistence.SublevelConstructibleExamples
import TDA.Persistence.DiagramBottleneckLaws

set_option autoImplicit false

/-!
# Explicit Čech and Rips values for the library triangle

This module records the exact face values of the library triangle with vertices `(0,0)`,
`(2,0)` and `(1,2)`, whose circumradius is `5/4`.  The radius-scale fixtures below are
read from the certified filled-triangle pivot computation after transporting the filter
between equal complexes.  The right-triangle control and the later log-scale and bottleneck
fixtures are extensions of the library definitions, not translations of a source theorem.
-/

namespace TDA.Persistence.TriangleCechRipsExamples

universe u w

open TDA.Filtration TDA.Simplicial TDA.Persistence
open TDA.Filtration.Cech.Examples
open TDA.Persistence.Reduction TDA.Persistence.Reduction.Examples
open Real
open scoped ENNReal

/-! ### The two triangle filters -/

/-- The Čech filter on the library's acute Euclidean triangle. -/
noncomputable abbrev cechT : FilterFunction (Rips.fullComplex (Fin 3)) ℝ :=
  Cech.filter Triangle.pts

/-- The Rips filter on the induced metric of the library's acute Euclidean triangle. -/
noncomputable abbrev ripsT : FilterFunction (Rips.fullComplex (Fin 3)) ℝ :=
  Rips.filter Triangle.metric

/-! ### Distances and face values -/

/-- The base edge of the library triangle has length `2`. -/
theorem triangle_dist01 : dist (Triangle.pts 0) (Triangle.pts 1) = 2 := by
  calc
    dist (Triangle.pts 0) (Triangle.pts 1) =
        √(dist (Triangle.pts 0) (Triangle.pts 1) ^ 2) :=
      (Real.sqrt_sq dist_nonneg).symm
    _ = 2 := by
      rw [Triangle.dist_sq]
      norm_num [Triangle.pts_zero, Triangle.pts_one]

/-- The two equal sloping edges of the library triangle have length `√5`. -/
theorem triangle_dist02 : dist (Triangle.pts 0) (Triangle.pts 2) = √5 := by
  calc
    dist (Triangle.pts 0) (Triangle.pts 2) =
        √(dist (Triangle.pts 0) (Triangle.pts 2) ^ 2) :=
      (Real.sqrt_sq dist_nonneg).symm
    _ = √5 := by
      rw [Triangle.dist_sq]
      norm_num [Triangle.pts_zero, Triangle.pts_two]

/-- The two equal sloping edges of the library triangle have length `√5`. -/
theorem triangle_dist12 : dist (Triangle.pts 1) (Triangle.pts 2) = √5 := by
  calc
    dist (Triangle.pts 1) (Triangle.pts 2) =
        √(dist (Triangle.pts 1) (Triangle.pts 2) ^ 2) :=
      (Real.sqrt_sq dist_nonneg).symm
    _ = √5 := by
      rw [Triangle.dist_sq]
      norm_num [Triangle.pts_one, Triangle.pts_two]

/-! ### Rips values and the elementary ordering bounds -/

/-- The Rips value of the base edge is `2`. -/
theorem triangle_rips_value_edge01 :
    ripsT.value ⟨Triangle.edge01, by simp [Triangle.edge01]⟩ = 2 := by
  change Rips.diameter Triangle.metric ({0, 1} : Finset (Fin 3)) = 2
  rw [Rips.diameter_pair, Triangle.metric_dist, triangle_dist01]

/-- The Rips value of the edge from vertex `0` to vertex `2` is `√5`. -/
theorem triangle_rips_value_edge02 :
    ripsT.value ⟨Triangle.edge02, by simp [Triangle.edge02]⟩ = √5 := by
  change Rips.diameter Triangle.metric ({0, 2} : Finset (Fin 3)) = √5
  rw [Rips.diameter_pair, Triangle.metric_dist, triangle_dist02]

/-- The Rips value of the edge from vertex `1` to vertex `2` is `√5`. -/
theorem triangle_rips_value_edge12 :
    ripsT.value ⟨Triangle.edge12, by simp [Triangle.edge12]⟩ = √5 := by
  change Rips.diameter Triangle.metric ({1, 2} : Finset (Fin 3)) = √5
  rw [Rips.diameter_pair, Triangle.metric_dist, triangle_dist12]

/-- The Rips value of the filled triangle is its diameter `√5`. -/
theorem triangle_rips_value_tri :
    ripsT.value ⟨Triangle.tri, by simp [Triangle.tri]⟩ = √5 := by
  change Rips.diameter Triangle.metric Triangle.tri = √5
  apply le_antisymm
  · refine (Rips.diameter_le_iff Triangle.metric Triangle.tri √5).2
      ⟨by positivity, ?_⟩
    intro v hv w hw
    rw [Triangle.metric_dist]
    simp only [Triangle.tri, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [Triangle.pts_zero, Triangle.pts_one, Triangle.pts_two] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)])
  · have h := Rips.diameter_mono Triangle.metric (s := Triangle.edge02)
      (t := Triangle.tri) (by decide)
    calc
      √5 = Rips.diameter Triangle.metric ({0, 2} : Finset (Fin 3)) := by
        rw [Rips.diameter_pair, Triangle.metric_dist, triangle_dist02]
      _ ≤ Rips.diameter Triangle.metric Triangle.tri := h

/-- A singleton has Čech value zero, for every pseudometric ambient space. -/
theorem cech_value_singleton {V X : Type*} [PseudoMetricSpace X] (p : V → X) (v : V) :
    (Cech.filter p).value ⟨{v}, Finset.singleton_nonempty v⟩ = 0 := by
  apply le_antisymm
  · refine (Cech.filter_value_le_radiusAt p ⟨{v}, Finset.singleton_nonempty v⟩ (p v)).trans ?_
    exact (Cech.radiusAt_le_iff p (p v) {v} 0).2 ⟨le_rfl, by simp⟩
  · exact Cech.filter_value_nonneg p ⟨{v}, Finset.singleton_nonempty v⟩

/-- The Čech value of the base edge is its midpoint radius `1`. -/
theorem triangle_cech_value_edge01 :
    cechT.value ⟨Triangle.edge01, by simp [Triangle.edge01]⟩ = 1 := by
  apply le_antisymm
  · refine (Cech.filter_value_le_radiusAt Triangle.pts _ !₂[1, 0]).trans ?_
    refine (Cech.radiusAt_le_iff Triangle.pts !₂[1, 0] Triangle.edge01 1).2
      ⟨by norm_num, ?_⟩
    intro v hv
    simp only [Triangle.edge01, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [Triangle.pts_zero])
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [Triangle.pts_one])
  · have h := Cech.rips_le_two_mul_filter_value Triangle.metric Triangle.pts
      Triangle.metric_dist ⟨Triangle.edge01, by simp [Triangle.edge01]⟩
    rw [triangle_rips_value_edge01] at h
    linarith

/-- The Čech value of the edge from vertex `0` to vertex `2` is `√5/2`. -/
theorem triangle_cech_value_edge02 :
    cechT.value ⟨Triangle.edge02, by simp [Triangle.edge02]⟩ = √5 / 2 := by
  apply le_antisymm
  · refine (Cech.filter_value_le_radiusAt Triangle.pts _ !₂[1 / 2, 1]).trans ?_
    refine (Cech.radiusAt_le_iff Triangle.pts !₂[1 / 2, 1] Triangle.edge02 (√5 / 2)).2
      ⟨by positivity, ?_⟩
    intro v hv
    simp only [Triangle.edge02, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [Triangle.pts_zero] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)])
    · exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [Triangle.pts_two] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)])
  · have h := Cech.rips_le_two_mul_filter_value Triangle.metric Triangle.pts
      Triangle.metric_dist ⟨Triangle.edge02, by simp [Triangle.edge02]⟩
    rw [triangle_rips_value_edge02] at h
    linarith

/-- The Čech value of the edge from vertex `1` to vertex `2` is `√5/2`. -/
theorem triangle_cech_value_edge12 :
    cechT.value ⟨Triangle.edge12, by simp [Triangle.edge12]⟩ = √5 / 2 := by
  apply le_antisymm
  · refine (Cech.filter_value_le_radiusAt Triangle.pts _ !₂[3 / 2, 1]).trans ?_
    refine (Cech.radiusAt_le_iff Triangle.pts !₂[3 / 2, 1] Triangle.edge12 (√5 / 2)).2
      ⟨by positivity, ?_⟩
    intro v hv
    simp only [Triangle.edge12, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [Triangle.pts_one] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)])
    · exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [Triangle.pts_two] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)])
  · have h := Cech.rips_le_two_mul_filter_value Triangle.metric Triangle.pts
      Triangle.metric_dist ⟨Triangle.edge12, by simp [Triangle.edge12]⟩
    rw [triangle_rips_value_edge12] at h
    linarith

/-- The Čech value of the filled library triangle is its circumradius `5/4`. -/
theorem triangle_cech_value_tri :
    cechT.value ⟨Triangle.tri, by simp [Triangle.tri]⟩ = 5 / 4 := by
  apply le_antisymm
  · refine (Cech.filter_value_le_radiusAt Triangle.pts _ !₂[1, 3 / 4]).trans ?_
    refine (Cech.radiusAt_le_iff Triangle.pts !₂[1, 3 / 4] Triangle.tri (5 / 4)).2
      ⟨by norm_num, ?_⟩
    intro v hv
    simp only [Triangle.tri, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [Triangle.pts_zero])
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [Triangle.pts_one])
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [Triangle.pts_two])
  · refine le_ciInf ?_
    intro x
    by_contra h
    have hlt : Cech.radiusAt Triangle.pts x Triangle.tri < 5 / 4 := lt_of_not_ge h
    have h0d : dist x (Triangle.pts 0) < 5 / 4 :=
      (Cech.dist_le_radiusAt Triangle.pts x (s := Triangle.tri) (v := 0)
        (by simp [Triangle.tri])).trans_lt hlt
    have h1d : dist x (Triangle.pts 1) < 5 / 4 :=
      (Cech.dist_le_radiusAt Triangle.pts x (s := Triangle.tri) (v := 1)
        (by simp [Triangle.tri])).trans_lt hlt
    have h2d : dist x (Triangle.pts 2) < 5 / 4 :=
      (Cech.dist_le_radiusAt Triangle.pts x (s := Triangle.tri) (v := 2)
        (by simp [Triangle.tri])).trans_lt hlt
    have h0sq : dist x (Triangle.pts 0) ^ 2 < (5 / 4 : ℝ) ^ 2 := by
      have hn : 0 ≤ dist x (Triangle.pts 0) := dist_nonneg
      exact (sq_lt_sq₀ hn (by norm_num)).2 h0d
    have h1sq : dist x (Triangle.pts 1) ^ 2 < (5 / 4 : ℝ) ^ 2 := by
      have hn : 0 ≤ dist x (Triangle.pts 1) := dist_nonneg
      exact (sq_lt_sq₀ hn (by norm_num)).2 h1d
    have h2sq : dist x (Triangle.pts 2) ^ 2 < (5 / 4 : ℝ) ^ 2 := by
      have hn : 0 ≤ dist x (Triangle.pts 2) := dist_nonneg
      exact (sq_lt_sq₀ hn (by norm_num)).2 h2d
    rw [Triangle.dist_sq] at h0sq h1sq h2sq
    norm_num [Triangle.pts_zero, Triangle.pts_one, Triangle.pts_two] at h0sq h1sq h2sq
    nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 3 / 4)]

/-- The three scale comparisons needed by the order and diagonal fixtures. -/
theorem sqrt_five_bounds : 1 < √5 / 2 ∧ √5 / 2 < 5 / 4 ∧ 2 < √5 := by
  constructor
  · have h := (Real.lt_sqrt (show (0 : ℝ) ≤ 2 by norm_num)).2
      (show (2 : ℝ) ^ 2 < 5 by norm_num)
    nlinarith
  constructor
  · have h := (Real.sqrt_lt' (show (0 : ℝ) < 5 / 2 by norm_num)).2
      (show (5 : ℝ) < (5 / 2) ^ 2 by norm_num)
    nlinarith
  · exact (Real.lt_sqrt (show (0 : ℝ) ≤ 2 by norm_num)).2
      (show (2 : ℝ) ^ 2 < 5 by norm_num)

/-! ### Transport to the certified filled triangle -/

/-- The certified filled triangle and the full three-vertex complex are equal. -/
theorem filledTriangle_toPre_eq :
    FilledTriangle.C.toPre = Rips.fullComplex (Fin 3) := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  change s ∈ FilledTriangle.C.faces ↔ s.Nonempty
  revert s
  decide +kernel

/-- Pull a real-valued filter on the full three-vertex complex back to the certified complex. -/
noncomputable def pullTriangle
    (g : FilterFunction (Rips.fullComplex (Fin 3)) ℝ) :
    FilterFunction FilledTriangle.C.toPre ℝ where
  value s := g.value ⟨s.val, by
    rw [← filledTriangle_toPre_eq]
    exact s.property⟩
  mono := by
    intro s t hst
    exact g.mono hst

/-- The pulled-back filter has the defining value of the original filter. -/
@[simp] theorem pullTriangle_value
    (g : FilterFunction (Rips.fullComplex (Fin 3)) ℝ)
    (s : TotalFace FilledTriangle.C.toPre) :
    (pullTriangle g).value s = g.value ⟨s.val, by
      rw [← filledTriangle_toPre_eq]
      exact s.property⟩ := rfl

private theorem dgm_eq_of_complex_eq
    {V : Type u} [LinearOrder V] {α : Type w} [LinearOrder α]
    (k : Type u) [Field k] {K L : PreAbstractSimplicialComplex V}
    [iK : Fintype (TotalFace K)] [iL : Fintype (TotalFace L)]
    (h : K = L) (f : FilterFunction L α) (g : FilterFunction K α)
    (hfg : ∀ s, g.value s = f.value ⟨s.val, h ▸ s.property⟩) (n : ℕ) :
    @dgm V _ k _ α _ K iK g n = @dgm V _ k _ α _ L iL f n := by
  subst L
  have hgf : g = f := by
    apply FilterFunction.ext
    intro s
    simpa using hfg s
  subst f
  have hi : iK = iL := Subsingleton.elim _ _
  cases hi
  rfl

/-- Pulling a filter across the equal-complex identification preserves its diagram. -/
theorem dgm_pullTriangle (k : Type) [Field k]
    (g : FilterFunction (Rips.fullComplex (Fin 3)) ℝ) (n : ℕ) :
    dgm k (pullTriangle g) n = dgm k g n := by
  exact dgm_eq_of_complex_eq k filledTriangle_toPre_eq g (pullTriangle g)
    (fun s => by simp [pullTriangle]) n

private noncomputable def cechVals (n : ℕ) : ℝ :=
  if n < 3 then 0 else if n = 3 then 1 else if n < 6 then √5 / 2 else 5 / 4

private noncomputable def ripsVals (n : ℕ) : ℝ :=
  if n < 3 then 0 else if n = 3 then 2 else √5

private theorem cech_enum_values (i : Fin (faceCount FilledTriangle.C.toPre)) :
    (pullTriangle cechT).value (FilledTriangle.e.enum i) =
      cechVals i.val := by
  fin_cases i
  · show cechT.value ⟨{0}, by simp⟩ = cechVals 0
    rw [cech_value_singleton]
    norm_num [cechVals]
  · show cechT.value ⟨{1}, by simp⟩ = cechVals 1
    rw [cech_value_singleton]
    norm_num [cechVals]
  · show cechT.value ⟨{2}, by simp⟩ = cechVals 2
    rw [cech_value_singleton]
    norm_num [cechVals]
  · show cechT.value ⟨Triangle.edge01, by simp [Triangle.edge01]⟩ = cechVals 3
    rw [triangle_cech_value_edge01]
    norm_num [cechVals]
  · show cechT.value ⟨Triangle.edge12, by simp [Triangle.edge12]⟩ = cechVals 4
    rw [triangle_cech_value_edge12]
    norm_num [cechVals]
  · show cechT.value ⟨Triangle.edge02, by simp [Triangle.edge02]⟩ = cechVals 5
    rw [triangle_cech_value_edge02]
    norm_num [cechVals]
  · show cechT.value ⟨Triangle.tri, by simp [Triangle.tri]⟩ = cechVals 6
    rw [triangle_cech_value_tri]
    norm_num [cechVals]

private theorem rips_enum_values (i : Fin (faceCount FilledTriangle.C.toPre)) :
    (pullTriangle ripsT).value (FilledTriangle.e.enum i) =
      ripsVals i.val := by
  fin_cases i
  · show ripsT.value ⟨{0}, by simp⟩ = ripsVals 0
    rw [Rips.filter_value]
    calc
      Rips.diameter Triangle.metric ({0} : Finset (Fin 3)) = 0 :=
        Rips.diameter_singleton _ _
      _ = ripsVals 0 := by norm_num [ripsVals]
  · show ripsT.value ⟨{1}, by simp⟩ = ripsVals 1
    rw [Rips.filter_value]
    calc
      Rips.diameter Triangle.metric ({1} : Finset (Fin 3)) = 0 :=
        Rips.diameter_singleton _ _
      _ = ripsVals 1 := by norm_num [ripsVals]
  · show ripsT.value ⟨{2}, by simp⟩ = ripsVals 2
    rw [Rips.filter_value]
    calc
      Rips.diameter Triangle.metric ({2} : Finset (Fin 3)) = 0 :=
        Rips.diameter_singleton _ _
      _ = ripsVals 2 := by norm_num [ripsVals]
  · show ripsT.value ⟨Triangle.edge01, by simp [Triangle.edge01]⟩ = ripsVals 3
    rw [triangle_rips_value_edge01]
    norm_num [ripsVals]
  · show ripsT.value ⟨Triangle.edge12, by simp [Triangle.edge12]⟩ = ripsVals 4
    rw [triangle_rips_value_edge12]
    norm_num [ripsVals]
  · show ripsT.value ⟨Triangle.edge02, by simp [Triangle.edge02]⟩ = ripsVals 5
    rw [triangle_rips_value_edge02]
    norm_num [ripsVals]
  · show ripsT.value ⟨Triangle.tri, by simp [Triangle.tri]⟩ = ripsVals 6
    rw [triangle_rips_value_tri]
    norm_num [ripsVals]

/-- The Čech values are monotone along the certified filled-triangle order. -/
theorem cech_monotone_enum :
    Monotone ((pullTriangle cechT).value ∘ FilledTriangle.e.enum) := by
  intro i j hij
  simp only [Function.comp_apply]
  rw [cech_enum_values i, cech_enum_values j]
  rcases sqrt_five_bounds with ⟨h₁, h₂, h₃⟩
  fin_cases i <;> fin_cases j <;>
    first
    | (simp only [Fin.mk_le_mk, Fin.le_def, Fin.val_mk] at hij; omega)
    | (norm_num [cechVals]; done)
    | (norm_num [cechVals]; nlinarith)

/-- The Rips values are monotone along the certified filled-triangle order. -/
theorem rips_monotone_enum :
    Monotone ((pullTriangle ripsT).value ∘ FilledTriangle.e.enum) := by
  intro i j hij
  simp only [Function.comp_apply]
  rw [rips_enum_values i, rips_enum_values j]
  rcases sqrt_five_bounds with ⟨h₁, h₂, h₃⟩
  fin_cases i <;> fin_cases j <;>
    first
    | (simp only [Fin.mk_le_mk, Fin.le_def, Fin.val_mk] at hij; omega)
    | (norm_num [ripsVals]; done)
    | (norm_num [ripsVals]; nlinarith)

/-- The unfiltered Rips degree-one pivot pair is diagonal: both faces have value `√5`. -/
theorem triangle_rips_pair_diagonal :
    (pullTriangle ripsT).value (FilledTriangle.e.enum ⟨5, by decide⟩) =
      (pullTriangle ripsT).value (FilledTriangle.e.enum ⟨6, by decide⟩) := by
  rw [rips_enum_values ⟨5, by decide⟩, rips_enum_values ⟨6, by decide⟩]
  norm_num [ripsVals]

/-! ### Radius-scale diagrams -/

/-- The degree-zero Čech diagram of the library triangle. -/
theorem triangle_cech_dgm_zero :
    (dgm (ZMod 2) cechT 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), (0, ((1 : ℝ) : WithTop ℝ)),
        (0, ((√5 / 2 : ℝ) : WithTop ℝ))} := by
  have h01 : (0 : ℝ) ≠ 1 := by norm_num
  have h0s : (0 : ℝ) ≠ √5 / 2 := by
    nlinarith [sqrt_five_bounds.1]
  rw [← dgm_pullTriangle,
    ← evaluatePivotTemplate_eq_dgm (ZMod 2) FilledTriangle.e _ cech_monotone_enum 0]
  simp only [evaluatePivotTemplate]
  rw [FilledTriangle.exact_pairs_zero, FilledTriangle.exact_essential_zero]
  simp [Multiset.filter_singleton, pairValues, birthValue, -pullTriangle_value,
    cech_enum_values, cechVals, h01, h0s]
  simp only [← Multiset.cons_zero]
  simp only [Multiset.cons_swap]

/-- The degree-one Čech diagram of the library triangle. -/
theorem triangle_cech_dgm_one :
    (dgm (ZMod 2) cechT 1).points =
      {((√5 / 2 : ℝ), ((5 / 4 : ℝ) : WithTop ℝ))} := by
  have hne : √5 / 2 ≠ (5 / 4 : ℝ) := ne_of_lt sqrt_five_bounds.2.1
  rw [← dgm_pullTriangle,
    ← evaluatePivotTemplate_eq_dgm (ZMod 2) FilledTriangle.e _ cech_monotone_enum 1]
  simp only [evaluatePivotTemplate]
  rw [FilledTriangle.exact_pairs_one, FilledTriangle.exact_essential_one]
  simp [Multiset.filter_singleton, pairValues, birthValue, -pullTriangle_value,
    cech_enum_values, cechVals, hne]

/-- The degree-zero Rips diagram of the library triangle. -/
theorem triangle_rips_dgm_zero :
    (dgm (ZMod 2) ripsT 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), (0, ((2 : ℝ) : WithTop ℝ)),
        (0, ((√5 : ℝ) : WithTop ℝ))} := by
  have h02 : (0 : ℝ) ≠ 2 := by norm_num
  have h0s : (0 : ℝ) ≠ √5 := by
    nlinarith [sqrt_five_bounds.2.2]
  rw [← dgm_pullTriangle,
    ← evaluatePivotTemplate_eq_dgm (ZMod 2) FilledTriangle.e _ rips_monotone_enum 0]
  simp only [evaluatePivotTemplate]
  rw [FilledTriangle.exact_pairs_zero, FilledTriangle.exact_essential_zero]
  simp [Multiset.filter_singleton, pairValues, birthValue, -pullTriangle_value,
    rips_enum_values, ripsVals, h02, h0s]
  rw [← Multiset.cons_zero, ← Multiset.cons_zero, Multiset.cons_swap _ (_, ⊤),
    Multiset.cons_swap _ (_, ⊤)]

/-- The degree-one Rips diagram is empty after diagonal filtering. -/
theorem triangle_rips_dgm_one :
    (dgm (ZMod 2) ripsT 1).points = 0 := by
  rw [← dgm_pullTriangle,
    ← evaluatePivotTemplate_eq_dgm (ZMod 2) FilledTriangle.e _ rips_monotone_enum 1]
  simp only [evaluatePivotTemplate]
  rw [FilledTriangle.exact_pairs_one, FilledTriangle.exact_essential_one]
  simp [Multiset.filter_singleton, pairValues, birthValue, -pullTriangle_value,
    rips_enum_values, ripsVals]

/-! ### Log-scale diagrams -/

/-- The logarithm of the two equal Čech edge radii. -/
theorem log_sqrt_five_div_two :
    Real.log (√5 / 2) = Real.log (5 / 4) / 2 := by
  calc
    Real.log (√5 / 2) = Real.log (√(5 / 4)) := by
      rw [Real.sqrt_div' 5 (show (0 : ℝ) ≤ 4 by norm_num)]
      norm_num
    _ = Real.log (5 / 4) / 2 := by
      rw [Real.log_sqrt (show (0 : ℝ) ≤ 5 / 4 by norm_num)]

/-- The degree-one Čech diagram after logarithmic rescaling. -/
theorem triangle_cech_logDgm_one :
    (logDgm (ZMod 2) cechT 1).points =
      {((Real.log (5 / 4) / 2 : ℝ), ((Real.log (5 / 4) : ℝ) : WithTop ℝ))} := by
  rw [logDgm_points_eq_map_log (ZMod 2) le_rfl
      TDA.Persistence.LogScaleDiagramExamples.triangle_cech_positive,
    triangle_cech_dgm_one]
  simp [log_sqrt_five_div_two]

/-- The degree-one Rips diagram remains empty after logarithmic rescaling. -/
theorem triangle_rips_logDgm_one :
    (logDgm (ZMod 2) ripsT 1).points = 0 := by
  rw [logDgm_points_eq_map_log (ZMod 2) le_rfl
      TDA.Persistence.LogScaleDiagramExamples.triangle_rips_positive,
    triangle_rips_dgm_one, Multiset.map_zero]

/-! ### Exact bottleneck values -/

/-- The radius-scale degree-zero Rips-to-Čech bottleneck value. -/
theorem triangle_bottleneck_zero :
    bottleneck (dgm (ZMod 2) ripsT 0) (dgm (ZMod 2) cechT 0) =
      ENNReal.ofReal (√5 / 2) := by
  classical
  let x : Fin 2 → ℝ × ℝ := ![(0, 2), (0, √5)]
  let y : Fin 2 → ℝ × ℝ := ![(0, 1), (0, √5 / 2)]
  let b : Fin 1 → ℝ := fun _ => 0
  let c : Fin 1 → ℝ := fun _ => 0
  have hx : (Finset.univ : Finset (Fin 2)).val.map x =
      finitePart (dgm (ZMod 2) ripsT 0).points := by
    simp [finitePart, x, triangle_rips_dgm_zero] <;> rfl
  have hy : (Finset.univ : Finset (Fin 2)).val.map y =
      finitePart (dgm (ZMod 2) cechT 0).points := by
    simp [finitePart, y, triangle_cech_dgm_zero] <;> rfl
  have hb : (Finset.univ : Finset (Fin 1)).val.map b =
      essentialPart (dgm (ZMod 2) ripsT 0).points := by
    simp [essentialPart, b, triangle_rips_dgm_zero] <;> rfl
  have hc : (Finset.univ : Finset (Fin 1)).val.map c =
      essentialPart (dgm (ZMod 2) cechT 0).points := by
    simp [essentialPart, c, triangle_cech_dgm_zero] <;> rfl
  rw [bottleneck_eq_presentation _ _ x y b c hx hy hb hc]
  apply le_antisymm
  · let M : OccurrenceMatching (Fin 2) (Fin 2) (Fin 1) (Fin 1) :=
      ⟨fun i => some i, by
        intro i i' j hi hi'
        exact Option.some.inj (hi.trans hi'.symm), Equiv.refl _⟩
    have hs : |√5 - √5 / 2| = √5 / 2 := by
      rw [abs_of_nonneg]
      · ring
      · nlinarith [Real.sqrt_nonneg (5 : ℝ)]
    have hcost : M.cost x y b c = ENNReal.ofReal (√5 / 2) := by
      rcases sqrt_five_bounds with ⟨h₁, h₂, h₃⟩
      have hsmall : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (√5 / 2) := by
        simpa using ENNReal.ofReal_le_ofReal (le_of_lt h₁)
      have hbase : |(2 : ℝ) - 1| = 1 := by
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 - 1)]
        norm_num
      simp [OccurrenceMatching.cost, M, x, y, b, c, finitePairCost, diagonalCost,
        essentialPairCost, Fin.univ_succ, Finset.sup_insert, Finset.sup_singleton,
        hbase, hs, max_eq_right (le_of_lt h₁), max_eq_right hsmall]
    exact (presentationBottleneck_le_cost x y b c M).trans_eq hcost
  · unfold presentationBottleneck
    apply le_iInf
    intro M
    have hsource := M.source_le_cost x y b c 1
    cases h : M.finite 1 with
    | none =>
        calc
          ENNReal.ofReal (√5 / 2) = diagonalCost (x 1) := by
            simp [x, diagonalCost, abs_of_nonneg (Real.sqrt_nonneg 5)]
          _ ≤ M.cost x y b c := by simpa [h] using hsource
    | some j =>
        fin_cases j
        · have hsminus : 0 ≤ √5 - 1 := by
            nlinarith [sqrt_five_bounds.2.2]
          calc
            ENNReal.ofReal (√5 / 2) ≤ ENNReal.ofReal (√5 - 1) :=
              ENNReal.ofReal_le_ofReal (by nlinarith [sqrt_five_bounds.2.2])
            _ = finitePairCost (x 1) (y 0) := by
              simp [x, y, finitePairCost, hsminus, abs_of_nonneg hsminus]
            _ ≤ M.cost x y b c := by simpa [h] using hsource
        · have hs : |√5 - √5 / 2| = √5 / 2 := by
            rw [abs_of_nonneg]
            · ring
            · nlinarith [Real.sqrt_nonneg (5 : ℝ)]
          calc
            ENNReal.ofReal (√5 / 2) = finitePairCost (x 1) (y 1) := by
              simp [x, y, finitePairCost, hs]
            _ ≤ M.cost x y b c := by simpa [h] using hsource

/-- The radius-scale degree-one Rips-to-Čech bottleneck value. -/
theorem triangle_bottleneck_one :
    bottleneck (dgm (ZMod 2) ripsT 1) (dgm (ZMod 2) cechT 1) =
      ENNReal.ofReal ((5 / 4 - √5 / 2) / 2) := by
  classical
  rw [bottleneck_comm]
  let x : Fin 1 → ℝ × ℝ := fun _ => (√5 / 2, 5 / 4)
  let y : Fin 0 → ℝ × ℝ := Fin.elim0
  let b : Fin 0 → ℝ := Fin.elim0
  let c : Fin 0 → ℝ := Fin.elim0
  have hx : (Finset.univ : Finset (Fin 1)).val.map x =
      finitePart (dgm (ZMod 2) cechT 1).points := by
    simp [finitePart, x, triangle_cech_dgm_one] <;> rfl
  have hy : (Finset.univ : Finset (Fin 0)).val.map y =
      finitePart (dgm (ZMod 2) ripsT 1).points := by
    simp [finitePart, y, triangle_rips_dgm_one] <;> rfl
  have hb : (Finset.univ : Finset (Fin 0)).val.map b =
      essentialPart (dgm (ZMod 2) cechT 1).points := by
    simp [essentialPart, b, triangle_cech_dgm_one] <;> rfl
  have hc : (Finset.univ : Finset (Fin 0)).val.map c =
      essentialPart (dgm (ZMod 2) ripsT 1).points := by
    simp [essentialPart, c, triangle_rips_dgm_one] <;> rfl
  rw [bottleneck_eq_presentation _ _ x y b c hx hy hb hc]
  change presentationBottleneck (fun _ : Fin 1 => ((√5 / 2 : ℝ), (5 / 4 : ℝ)))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) = _
  rw [presentationBottleneck_singleton_empty]
  have hpos : 0 < (5 / 4 : ℝ) - √5 / 2 := by
    nlinarith [sqrt_five_bounds.2.1]
  unfold diagonalCost
  rw [abs_of_pos hpos]

/-- The log-scale degree-one Rips-to-Čech bottleneck value. -/
theorem triangle_logBottleneck_one :
    bottleneck (logDgm (ZMod 2) ripsT 1) (logDgm (ZMod 2) cechT 1) =
      ENNReal.ofReal (Real.log (5 / 4) / 4) := by
  classical
  rw [bottleneck_comm]
  let x : Fin 1 → ℝ × ℝ :=
    fun _ => (Real.log (5 / 4) / 2, Real.log (5 / 4))
  let y : Fin 0 → ℝ × ℝ := Fin.elim0
  let b : Fin 0 → ℝ := Fin.elim0
  let c : Fin 0 → ℝ := Fin.elim0
  have hx : (Finset.univ : Finset (Fin 1)).val.map x =
      finitePart (logDgm (ZMod 2) cechT 1).points := by
    simp [finitePart, x, triangle_cech_logDgm_one] <;> rfl
  have hy : (Finset.univ : Finset (Fin 0)).val.map y =
      finitePart (logDgm (ZMod 2) ripsT 1).points := by
    simp [finitePart, y, triangle_rips_logDgm_one]
  have hb : (Finset.univ : Finset (Fin 0)).val.map b =
      essentialPart (logDgm (ZMod 2) cechT 1).points := by
    simp [essentialPart, b, triangle_cech_logDgm_one] <;> rfl
  have hc : (Finset.univ : Finset (Fin 0)).val.map c =
      essentialPart (logDgm (ZMod 2) ripsT 1).points := by
    simp [essentialPart, c, triangle_rips_logDgm_one]
  rw [bottleneck_eq_presentation _ _ x y b c hx hy hb hc]
  change presentationBottleneck
      (fun _ : Fin 1 => ((Real.log (5 / 4) / 2 : ℝ), (Real.log (5 / 4) : ℝ)))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) = _
  rw [presentationBottleneck_singleton_empty]
  have hlog : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hpos : 0 < Real.log (5 / 4) - Real.log (5 / 4) / 2 := by
    linarith
  unfold diagonalCost
  rw [abs_of_pos hpos]
  congr 1
  ring

/-- The log-scale degree-one interleaving distance equals the exact bottleneck value. -/
theorem triangle_logInterleaving_one :
    realInterleavingDistance (logModule (ZMod 2) ripsT 1)
        (logModule (ZMod 2) cechT 1) = ENNReal.ofReal (Real.log (5 / 4) / 4) := by
  rw [← bottleneck_logDgm_eq_realInterleavingDistance (ZMod 2) le_rfl
    TDA.Persistence.LogScaleDiagramExamples.triangle_rips_positive
    TDA.Persistence.LogScaleDiagramExamples.triangle_cech_positive,
    triangle_logBottleneck_one]

/-- The exact log-scale value is strictly below the general `log 2` bound. -/
theorem triangle_logBottleneck_one_lt_log_two :
    bottleneck (logDgm (ZMod 2) ripsT 1) (logDgm (ZMod 2) cechT 1) <
      ENNReal.ofReal (Real.log 2) := by
  rw [triangle_logBottleneck_one]
  apply (ENNReal.ofReal_lt_ofReal_iff (Real.log_pos (by norm_num))).2
  have hlog : Real.log (5 / 4) < Real.log 2 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hpos : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  nlinarith [hpos, hlog]

/-! ### Required cross-check fixtures -/

/-- The Čech degree-one homology at radius `6/5` has rank one. -/
theorem triangle_cech_finrank_one :
    Module.finrank (ZMod 2)
        (simplicialHomology (cechT.sublevel (6 / 5)) (ZMod 2) 1) = 1 := by
  rw [finrank_sublevelHomology_eq_countP (ZMod 2) cechT 1 (6 / 5),
    triangle_cech_dgm_one]
  have hs : √5 ≤ (12 / 5 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg (5 : ℝ)]
  have hbirth : √5 / 2 ≤ (6 / 5 : ℝ) := by
    nlinarith
  have hdeath : (6 / 5 : ℝ) < 5 / 4 := by norm_num
  rw [← Multiset.cons_zero,
    Multiset.countP_cons_of_pos (s := 0)
      ⟨hbirth, WithTop.coe_lt_coe.2 hdeath⟩,
    Multiset.countP_zero]

/-- The Čech degree-zero diagram has one essential point. -/
theorem triangle_cech_essential_card_zero :
    (essentialPart (dgm (ZMod 2) cechT 0).points).card = 1 := by
  rw [triangle_cech_dgm_zero]
  simp [essentialPart]
  rfl

/-- The Rips degree-zero diagram has one essential point. -/
theorem triangle_rips_essential_card_zero :
    (essentialPart (dgm (ZMod 2) ripsT 0).points).card = 1 := by
  rw [triangle_rips_dgm_zero]
  simp [essentialPart]
  rfl

/-- The radius-scale and log-scale degree-one bottleneck values differ. -/
theorem triangle_radius_ne_log_one :
    (5 / 4 - √5 / 2) / 2 ≠ Real.log (5 / 4) / 4 := by
  intro h
  have hlog : Real.log (5 / 4) / 4 ≤ (1 / 16 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    nlinarith
  have hsqrt : √5 < (9 / 4 : ℝ) := by
    exact (Real.sqrt_lt' (show (0 : ℝ) < 9 / 4 by norm_num)).2
      (show (5 : ℝ) < (9 / 4) ^ 2 by norm_num)
  have hradius : (1 / 16 : ℝ) < (5 / 4 - √5 / 2) / 2 := by
    nlinarith
  nlinarith

/-- The exact log-scale degree-one bottleneck is nonzero. -/
theorem triangle_logBottleneck_one_ne_zero :
    bottleneck (logDgm (ZMod 2) ripsT 1) (logDgm (ZMod 2) cechT 1) ≠ 0 := by
  rw [triangle_logBottleneck_one]
  intro h
  have hlog : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hpos : 0 < Real.log (5 / 4) / 4 := by linarith
  have hz : Real.log (5 / 4) / 4 ≤ 0 := ENNReal.ofReal_eq_zero.mp h
  linarith

/-! ### Right-triangle negative control -/

namespace RightTriangle

/-- The vertices `(0,0)`, `(2,0)` and `(2,2)` of the right-triangle control. -/
noncomputable def pts : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0], !₂[2, 0], !₂[2, 2]]

/-- The first vertex of the right-triangle control. -/
@[simp] theorem pts_zero : pts 0 = !₂[0, 0] := rfl

/-- The second vertex of the right-triangle control. -/
@[simp] theorem pts_one : pts 1 = !₂[2, 0] := rfl

/-- The third vertex of the right-triangle control. -/
@[simp] theorem pts_two : pts 2 = !₂[2, 2] := rfl

/-- The right-triangle vertex labels are injective. -/
theorem pts_injective : Function.Injective pts := by
  intro i j h
  have hx : pts i 0 = pts j 0 :=
    congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
  have hy : pts i 1 = pts j 1 :=
    congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h
  have hx' : ∀ k : Fin 3, pts k 0 = ![0, 2, 2] k := by
    intro k
    fin_cases k <;> rfl
  have hy' : ∀ k : Fin 3, pts k 1 = ![0, 0, 2] k := by
    intro k
    fin_cases k <;> rfl
  rw [hx', hx'] at hx
  rw [hy', hy'] at hy
  fin_cases i <;> fin_cases j <;>
    first | rfl | (norm_num at hx; done) | (norm_num at hy; done)

/-- The label metric induced by the right-triangle vertices. -/
noncomputable abbrev metric : MetricSpace (Fin 3) :=
  MetricSpace.induced pts pts_injective inferInstance

/-- The induced label distance is the ambient Euclidean distance. -/
theorem metric_dist (v w : Fin 3) : metric.dist v w = dist (pts v) (pts w) := rfl

/-- The two edges incident to the right angle and the hypotenuse. -/
def edge01 : Finset (Fin 3) := {0, 1}

/-- The hypotenuse of the right-triangle control. -/
def edge02 : Finset (Fin 3) := {0, 2}

/-- The second edge incident to the right angle. -/
def edge12 : Finset (Fin 3) := {1, 2}

/-- The filled right-triangle face. -/
def tri : Finset (Fin 3) := {0, 1, 2}

private theorem dist01 : dist (pts 0) (pts 1) = 2 := by
  calc
    dist (pts 0) (pts 1) = √(dist (pts 0) (pts 1) ^ 2) :=
      (Real.sqrt_sq dist_nonneg).symm
    _ = 2 := by
      rw [Triangle.dist_sq]
      norm_num [pts_zero, pts_one]

private theorem dist12 : dist (pts 1) (pts 2) = 2 := by
  calc
    dist (pts 1) (pts 2) = √(dist (pts 1) (pts 2) ^ 2) :=
      (Real.sqrt_sq dist_nonneg).symm
    _ = 2 := by
      rw [Triangle.dist_sq]
      norm_num [pts_one, pts_two]

private theorem dist02 : dist (pts 0) (pts 2) = 2 * √2 := by
  calc
    dist (pts 0) (pts 2) = √(dist (pts 0) (pts 2) ^ 2) :=
      (Real.sqrt_sq dist_nonneg).symm
    _ = 2 * √2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
      rw [Triangle.dist_sq]
      norm_num [pts_zero, pts_two] <;>
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The Rips value of the first right-triangle edge is `2`. -/
theorem rightTriangle_rips_value_edge01 :
    (Rips.filter metric).value ⟨edge01, by simp [edge01]⟩ = 2 := by
  change Rips.diameter metric ({0, 1} : Finset (Fin 3)) = 2
  rw [Rips.diameter_pair, metric_dist, dist01]

/-- The Rips value of the second right-triangle edge is `2`. -/
theorem rightTriangle_rips_value_edge12 :
    (Rips.filter metric).value ⟨edge12, by simp [edge12]⟩ = 2 := by
  change Rips.diameter metric ({1, 2} : Finset (Fin 3)) = 2
  rw [Rips.diameter_pair, metric_dist, dist12]

/-- The Rips value of the right-triangle hypotenuse is `2 * √2`. -/
theorem rightTriangle_rips_value_edge02 :
    (Rips.filter metric).value ⟨edge02, by simp [edge02]⟩ = 2 * √2 := by
  change Rips.diameter metric ({0, 2} : Finset (Fin 3)) = 2 * √2
  rw [Rips.diameter_pair, metric_dist, dist02]

/-- The Rips value of the filled right triangle is its hypotenuse length `2 * √2`. -/
theorem rightTriangle_rips_value_tri :
    (Rips.filter metric).value ⟨tri, by simp [tri]⟩ = 2 * √2 := by
  change Rips.diameter metric tri = 2 * √2
  apply le_antisymm
  · refine (Rips.diameter_le_iff metric tri (2 * √2)).2
      ⟨by positivity, ?_⟩
    intro v hv w hw
    rw [metric_dist]
    simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [pts_zero, pts_one, pts_two] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
  · have h := Rips.diameter_mono metric (s := edge02) (t := tri) (by decide)
    calc
      2 * √2 = Rips.diameter metric ({0, 2} : Finset (Fin 3)) := by
        rw [Rips.diameter_pair, metric_dist, dist02]
      _ ≤ Rips.diameter metric tri := h

/-- The Čech value of the first right-triangle edge is `1`. -/
theorem rightTriangle_cech_value_edge01 :
    (Cech.filter pts).value ⟨edge01, by simp [edge01]⟩ = 1 := by
  apply le_antisymm
  · refine (Cech.filter_value_le_radiusAt pts _ !₂[1, 0]).trans ?_
    refine (Cech.radiusAt_le_iff pts !₂[1, 0] edge01 1).2
      ⟨by norm_num, ?_⟩
    intro v hv
    simp only [edge01, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [pts_zero])
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [pts_one])
  · have h := Cech.rips_le_two_mul_filter_value metric pts metric_dist
      ⟨edge01, by simp [edge01]⟩
    rw [rightTriangle_rips_value_edge01] at h
    linarith

/-- The Čech value of the second right-triangle edge is `1`. -/
theorem rightTriangle_cech_value_edge12 :
    (Cech.filter pts).value ⟨edge12, by simp [edge12]⟩ = 1 := by
  apply le_antisymm
  · refine (Cech.filter_value_le_radiusAt pts _ !₂[2, 1]).trans ?_
    refine (Cech.radiusAt_le_iff pts !₂[2, 1] edge12 1).2
      ⟨by norm_num, ?_⟩
    intro v hv
    simp only [edge12, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [pts_one])
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [pts_two])
  · have h := Cech.rips_le_two_mul_filter_value metric pts metric_dist
      ⟨edge12, by simp [edge12]⟩
    rw [rightTriangle_rips_value_edge12] at h
    linarith

/-- The Čech value of the right-triangle hypotenuse is `√2`. -/
theorem rightTriangle_cech_value_edge02 :
    (Cech.filter pts).value ⟨edge02, by simp [edge02]⟩ = √2 := by
  apply le_antisymm
  · refine (Cech.filter_value_le_radiusAt pts _ !₂[1, 1]).trans ?_
    refine (Cech.radiusAt_le_iff pts !₂[1, 1] edge02 √2).2
      ⟨by positivity, ?_⟩
    intro v hv
    simp only [edge02, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [pts_zero] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
    · exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [pts_two] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
  · have h := Cech.rips_le_two_mul_filter_value metric pts metric_dist
      ⟨edge02, by simp [edge02]⟩
    rw [rightTriangle_rips_value_edge02] at h
    linarith

/-- The Čech value of the filled right triangle is `√2`. -/
theorem rightTriangle_cech_value_tri :
    (Cech.filter pts).value ⟨tri, by simp [tri]⟩ = √2 := by
  apply le_antisymm
  · refine (Cech.filter_value_le_radiusAt pts _ !₂[1, 1]).trans ?_
    refine (Cech.radiusAt_le_iff pts !₂[1, 1] tri √2).2
      ⟨by positivity, ?_⟩
    intro v hv
    simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [pts_zero] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
    · exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [pts_one] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
    · exact Triangle.dist_le_of_sq_le (by positivity) (by
        norm_num [pts_two] <;>
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
  · have h : (Cech.filter pts).value ⟨edge02, by simp [edge02]⟩ ≤
        (Cech.filter pts).value ⟨tri, by simp [tri]⟩ :=
      (Cech.filter pts).mono (by decide)
    rw [rightTriangle_cech_value_edge02] at h
    exact h

/-- The right-triangle Čech 2-face enters at the same value as its hypotenuse. -/
theorem rightTriangle_cech_value_tri_eq_edge02 :
    (Cech.filter pts).value ⟨tri, by simp [tri]⟩ =
      (Cech.filter pts).value ⟨edge02, by simp [edge02]⟩ := by
  rw [rightTriangle_cech_value_tri, rightTriangle_cech_value_edge02]

private noncomputable def cechVals (n : ℕ) : ℝ :=
  if n < 3 then 0 else if n < 5 then 1 else √2

private noncomputable def ripsVals (n : ℕ) : ℝ :=
  if n < 3 then 0 else if n < 5 then 2 else 2 * √2

private theorem cech_enum_values (i : Fin (faceCount FilledTriangle.C.toPre)) :
    (pullTriangle (Cech.filter pts)).value (FilledTriangle.e.enum i) = cechVals i.val := by
  fin_cases i
  · show (Cech.filter pts).value ⟨{0}, by simp⟩ = cechVals 0
    rw [cech_value_singleton]
    norm_num [cechVals]
  · show (Cech.filter pts).value ⟨{1}, by simp⟩ = cechVals 1
    rw [cech_value_singleton]
    norm_num [cechVals]
  · show (Cech.filter pts).value ⟨{2}, by simp⟩ = cechVals 2
    rw [cech_value_singleton]
    norm_num [cechVals]
  · show (Cech.filter pts).value ⟨edge01, by simp [edge01]⟩ = cechVals 3
    rw [rightTriangle_cech_value_edge01]
    norm_num [cechVals]
  · show (Cech.filter pts).value ⟨edge12, by simp [edge12]⟩ = cechVals 4
    rw [rightTriangle_cech_value_edge12]
    norm_num [cechVals]
  · show (Cech.filter pts).value ⟨edge02, by simp [edge02]⟩ = cechVals 5
    rw [rightTriangle_cech_value_edge02]
    norm_num [cechVals]
  · show (Cech.filter pts).value ⟨tri, by simp [tri]⟩ = cechVals 6
    rw [rightTriangle_cech_value_tri]
    norm_num [cechVals]

private theorem rips_enum_values (i : Fin (faceCount FilledTriangle.C.toPre)) :
    (pullTriangle (Rips.filter metric)).value (FilledTriangle.e.enum i) = ripsVals i.val := by
  fin_cases i
  · show (Rips.filter metric).value ⟨{0}, by simp⟩ = ripsVals 0
    rw [Rips.filter_value]
    calc
      Rips.diameter metric ({0} : Finset (Fin 3)) = 0 :=
        Rips.diameter_singleton _ _
      _ = ripsVals 0 := by norm_num [ripsVals]
  · show (Rips.filter metric).value ⟨{1}, by simp⟩ = ripsVals 1
    rw [Rips.filter_value]
    calc
      Rips.diameter metric ({1} : Finset (Fin 3)) = 0 :=
        Rips.diameter_singleton _ _
      _ = ripsVals 1 := by norm_num [ripsVals]
  · show (Rips.filter metric).value ⟨{2}, by simp⟩ = ripsVals 2
    rw [Rips.filter_value]
    calc
      Rips.diameter metric ({2} : Finset (Fin 3)) = 0 :=
        Rips.diameter_singleton _ _
      _ = ripsVals 2 := by norm_num [ripsVals]
  · show (Rips.filter metric).value ⟨edge01, by simp [edge01]⟩ = ripsVals 3
    rw [rightTriangle_rips_value_edge01]
    norm_num [ripsVals]
  · show (Rips.filter metric).value ⟨edge12, by simp [edge12]⟩ = ripsVals 4
    rw [rightTriangle_rips_value_edge12]
    norm_num [ripsVals]
  · show (Rips.filter metric).value ⟨edge02, by simp [edge02]⟩ = ripsVals 5
    rw [rightTriangle_rips_value_edge02]
    norm_num [ripsVals]
  · show (Rips.filter metric).value ⟨tri, by simp [tri]⟩ = ripsVals 6
    rw [rightTriangle_rips_value_tri]
    norm_num [ripsVals]

private theorem cech_monotone_enum :
    Monotone ((pullTriangle (Cech.filter pts)).value ∘ FilledTriangle.e.enum) := by
  intro i j hij
  simp only [Function.comp_apply]
  rw [cech_enum_values i, cech_enum_values j]
  have hs : (1 : ℝ) < √2 := Real.one_lt_sqrt_two
  fin_cases i <;> fin_cases j <;>
    first
    | (simp only [Fin.mk_le_mk, Fin.le_def, Fin.val_mk] at hij; omega)
    | (norm_num [cechVals]; done)
    | (norm_num [cechVals]; nlinarith)

private theorem rips_monotone_enum :
    Monotone ((pullTriangle (Rips.filter metric)).value ∘ FilledTriangle.e.enum) := by
  intro i j hij
  simp only [Function.comp_apply]
  rw [rips_enum_values i, rips_enum_values j]
  have hs : (1 : ℝ) < √2 := Real.one_lt_sqrt_two
  fin_cases i <;> fin_cases j <;>
    first
    | (simp only [Fin.mk_le_mk, Fin.le_def, Fin.val_mk] at hij; omega)
    | (norm_num [ripsVals]; done)
    | (norm_num [ripsVals]; nlinarith)

/-- The right-triangle Čech degree-one diagram is empty. -/
theorem rightTriangle_cech_dgm_one :
    (dgm (ZMod 2) (Cech.filter pts) 1).points = 0 := by
  rw [← dgm_pullTriangle,
    ← evaluatePivotTemplate_eq_dgm (ZMod 2) FilledTriangle.e _ cech_monotone_enum 1]
  simp only [evaluatePivotTemplate]
  rw [FilledTriangle.exact_pairs_one, FilledTriangle.exact_essential_one]
  simp [Multiset.filter_singleton, pairValues, birthValue, -pullTriangle_value,
    cech_enum_values, cechVals]

/-- The right-triangle Rips degree-one diagram is empty. -/
theorem rightTriangle_rips_dgm_one :
    (dgm (ZMod 2) (Rips.filter metric) 1).points = 0 := by
  rw [← dgm_pullTriangle,
    ← evaluatePivotTemplate_eq_dgm (ZMod 2) FilledTriangle.e _ rips_monotone_enum 1]
  simp only [evaluatePivotTemplate]
  rw [FilledTriangle.exact_pairs_one, FilledTriangle.exact_essential_one]
  simp [Multiset.filter_singleton, pairValues, birthValue, -pullTriangle_value,
    rips_enum_values, ripsVals]

private theorem rips_positive : PositiveOnEdges (Rips.filter metric) :=
  positiveOnEdges_rips _

private theorem cech_positive : PositiveOnEdges (Cech.filter pts) :=
  Cech.positiveOnEdges_cech metric pts metric_dist

/-- The right-triangle degree-one log-scale Rips and Čech bottleneck is zero. -/
theorem rightTriangle_logBottleneck_one :
    bottleneck (logDgm (ZMod 2) (Rips.filter metric) 1)
        (logDgm (ZMod 2) (Cech.filter pts) 1) = 0 := by
  have hD : logDgm (ZMod 2) (Rips.filter metric) 1 =
      logDgm (ZMod 2) (Cech.filter pts) 1 := by
    apply Diagram.ext
    rw [logDgm_points_eq_map_log (ZMod 2) le_rfl rips_positive,
      rightTriangle_rips_dgm_one, Multiset.map_zero,
      logDgm_points_eq_map_log (ZMod 2) le_rfl cech_positive,
      rightTriangle_cech_dgm_one, Multiset.map_zero]
  rw [hD]
  exact bottleneck_self _

end RightTriangle

end TDA.Persistence.TriangleCechRipsExamples
