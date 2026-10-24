import TDA.Filtration.SparseRips.LogDiagramStability
import TDA.Simplicial.VertexChainMap
import Mathlib.Data.ZMod.Basic

/-!
# A four-point sparse Rips cycle

Four vertices carry the shortest-path metric of a four-cycle: adjacent vertices
have distance one and opposite vertices distance two. At scale one the sparse
complex is the four-edge cycle, before any greedy deletion. Its degree-one
homology is nonzero, so the sparse-to-relaxed comparison exercises a genuine
positive-degree class.
-/

namespace TDA.Filtration.SparseRips.H1Examples

open TDA.Filtration TDA.Filtration.SparseRips TDA.Simplicial
open GreedyNet
open CategoryTheory

noncomputable section

private def adjacent (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
  (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
  (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
  (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3)

private instance (i j : Fin 4) : Decidable (adjacent i j) := by
  unfold adjacent
  infer_instance

private def cycleDist (i j : Fin 4) : ℝ :=
  if i = j then 0 else if adjacent i j then 1 else 2

private theorem adjacent_symm (i j : Fin 4) : adjacent i j ↔ adjacent j i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem cycleDist_comm (i j : Fin 4) : cycleDist i j = cycleDist j i := by
  by_cases h : i = j
  · subst j; rfl
  · simp only [cycleDist, if_neg h, if_neg (Ne.symm h)]
    by_cases ha : adjacent i j
    · simp [ha, (adjacent_symm i j).mp ha]
    · have hb : ¬ adjacent j i := fun hb => ha ((adjacent_symm i j).mpr hb)
      simp [ha, hb]

private theorem cycleDist_ge_one {i j : Fin 4} (h : i ≠ j) :
    1 ≤ cycleDist i j := by
  unfold cycleDist
  simp only [if_neg h]
  split_ifs <;> norm_num

private theorem cycleDist_le_two (i j : Fin 4) : cycleDist i j ≤ 2 := by
  unfold cycleDist
  split_ifs <;> norm_num

private instance : MetricSpace (Fin 4) where
  dist := cycleDist
  dist_self := by intro i; simp [cycleDist]
  dist_comm := cycleDist_comm
  dist_triangle := by
    intro i j k
    by_cases hij : i = j
    · subst j
      simp [cycleDist]
    · by_cases hjk : j = k
      · subst k
        simp [cycleDist]
      · have hleft := cycleDist_le_two i k
        have hright1 := cycleDist_ge_one hij
        have hright2 := cycleDist_ge_one hjk
        linarith
  eq_of_dist_eq_zero := by
    intro i j h
    by_contra hij
    have hlow := cycleDist_ge_one hij
    linarith

private theorem dist_ge_one_of_ne {i j : Fin 4} (hij : i ≠ j) : 1 ≤ dist i j := by
  exact cycleDist_ge_one hij

private theorem dist_le_one_iff (i j : Fin 4) :
    dist i j ≤ 1 ↔ i = j ∨ adjacent i j := by
  change cycleDist i j ≤ 1 ↔ _
  unfold cycleDist
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, false_or]
    by_cases ha : adjacent i j <;> simp [ha]

private def cycleK : PreAbstractSimplicialComplex (Fin 4) where
  faces := {s | s.Nonempty ∧ ∀ i ∈ s, ∀ j ∈ s, i = j ∨ adjacent i j}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht =>
      ⟨ht, fun i hi j hj => hs.2 i (hts hi) j (hts hj)⟩⟩

private theorem rips_one_eq_cycleK :
    (Rips.filter inferInstance).sublevel 1 = cycleK := by
  ext σ
  change σ ∈ (Rips.filter inferInstance).sublevel 1 ↔ σ ∈ cycleK
  rw [Rips.mem_sublevel_iff]
  change (σ.Nonempty ∧ ∀ i ∈ σ, ∀ j ∈ σ, dist i j ≤ 1) ↔
    (σ.Nonempty ∧ ∀ i ∈ σ, ∀ j ∈ σ, i = j ∨ adjacent i j)
  simp only [dist_le_one_iff]

private instance : IsEmpty (Face cycleK 2) := ⟨fun s => by
  have h : ∀ t : Finset (Fin 4),
      (t.Nonempty ∧ ∀ i ∈ t, ∀ j ∈ t, i = j ∨ adjacent i j) →
      t.card ≠ 3 := by decide
  exact (h s.1 s.2.1) s.2.2⟩

private def vertexFace (i : Fin 4) : Face cycleK 0 :=
  ⟨{i}, by
    change ({i} : Finset (Fin 4)).Nonempty ∧
      ∀ a ∈ ({i} : Finset (Fin 4)), ∀ b ∈ ({i} : Finset (Fin 4)),
        a = b ∨ adjacent a b
    simp, by simp⟩

private def edge01 : Face cycleK 1 :=
  ⟨{0, 1}, by
    change ({0, 1} : Finset (Fin 4)).Nonempty ∧
      ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∀ j ∈ ({0, 1} : Finset (Fin 4)),
        i = j ∨ adjacent i j
    decide, by decide⟩
private def edge12 : Face cycleK 1 :=
  ⟨{1, 2}, by
    change ({1, 2} : Finset (Fin 4)).Nonempty ∧
      ∀ i ∈ ({1, 2} : Finset (Fin 4)), ∀ j ∈ ({1, 2} : Finset (Fin 4)),
        i = j ∨ adjacent i j
    decide, by decide⟩
private def edge23 : Face cycleK 1 :=
  ⟨{2, 3}, by
    change ({2, 3} : Finset (Fin 4)).Nonempty ∧
      ∀ i ∈ ({2, 3} : Finset (Fin 4)), ∀ j ∈ ({2, 3} : Finset (Fin 4)),
        i = j ∨ adjacent i j
    decide, by decide⟩
private def edge03 : Face cycleK 1 :=
  ⟨{0, 3}, by
    change ({0, 3} : Finset (Fin 4)).Nonempty ∧
      ∀ i ∈ ({0, 3} : Finset (Fin 4)), ∀ j ∈ ({0, 3} : Finset (Fin 4)),
        i = j ∨ adjacent i j
    decide, by decide⟩

private def pairEmb (a b : Fin 4) (hab : a < b) : Fin 2 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono ![a, b] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all)

private theorem pair_orderEmb (e : Face cycleK 1) {a b : Fin 4}
    (hab : a < b) (he : e.1 = {a, b}) :
    e.1.orderEmbOfFin e.2.2 = pairEmb a b hab := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  change ![a, b] i ∈ e.1
  rw [he]
  fin_cases i <;> simp

private theorem edge01_deleted_zero : deletedFace cycleK 0 edge01 0 = vertexFace 1 := by
  apply Subtype.ext
  change edge01.1.erase (edge01.1.orderEmbOfFin edge01.2.2 0) = {1}
  rw [pair_orderEmb edge01 (show (0 : Fin 4) < 1 by decide) rfl]
  decide
private theorem edge01_deleted_one : deletedFace cycleK 0 edge01 1 = vertexFace 0 := by
  apply Subtype.ext
  change edge01.1.erase (edge01.1.orderEmbOfFin edge01.2.2 1) = {0}
  rw [pair_orderEmb edge01 (show (0 : Fin 4) < 1 by decide) rfl]
  decide
private theorem edge12_deleted_zero : deletedFace cycleK 0 edge12 0 = vertexFace 2 := by
  apply Subtype.ext
  change edge12.1.erase (edge12.1.orderEmbOfFin edge12.2.2 0) = {2}
  rw [pair_orderEmb edge12 (show (1 : Fin 4) < 2 by decide) rfl]
  decide
private theorem edge12_deleted_one : deletedFace cycleK 0 edge12 1 = vertexFace 1 := by
  apply Subtype.ext
  change edge12.1.erase (edge12.1.orderEmbOfFin edge12.2.2 1) = {1}
  rw [pair_orderEmb edge12 (show (1 : Fin 4) < 2 by decide) rfl]
  decide
private theorem edge23_deleted_zero : deletedFace cycleK 0 edge23 0 = vertexFace 3 := by
  apply Subtype.ext
  change edge23.1.erase (edge23.1.orderEmbOfFin edge23.2.2 0) = {3}
  rw [pair_orderEmb edge23 (show (2 : Fin 4) < 3 by decide) rfl]
  decide
private theorem edge23_deleted_one : deletedFace cycleK 0 edge23 1 = vertexFace 2 := by
  apply Subtype.ext
  change edge23.1.erase (edge23.1.orderEmbOfFin edge23.2.2 1) = {2}
  rw [pair_orderEmb edge23 (show (2 : Fin 4) < 3 by decide) rfl]
  decide
private theorem edge03_deleted_zero : deletedFace cycleK 0 edge03 0 = vertexFace 3 := by
  apply Subtype.ext
  change edge03.1.erase (edge03.1.orderEmbOfFin edge03.2.2 0) = {3}
  rw [pair_orderEmb edge03 (show (0 : Fin 4) < 3 by decide) rfl]
  decide
private theorem edge03_deleted_one : deletedFace cycleK 0 edge03 1 = vertexFace 0 := by
  apply Subtype.ext
  change edge03.1.erase (edge03.1.orderEmbOfFin edge03.2.2 1) = {0}
  rw [pair_orderEmb edge03 (show (0 : Fin 4) < 3 by decide) rfl]
  decide

private theorem edge01_boundary :
    boundary cycleK ℚ 0 (Finsupp.single edge01 1) =
      Finsupp.single (vertexFace 1) 1 - Finsupp.single (vertexFace 0) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ,
    edge01_deleted_zero, edge01_deleted_one]
  all_goals simp only [sub_eq_add_neg]
private theorem edge12_boundary :
    boundary cycleK ℚ 0 (Finsupp.single edge12 1) =
      Finsupp.single (vertexFace 2) 1 - Finsupp.single (vertexFace 1) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ,
    edge12_deleted_zero, edge12_deleted_one]
  all_goals simp only [sub_eq_add_neg]
private theorem edge23_boundary :
    boundary cycleK ℚ 0 (Finsupp.single edge23 1) =
      Finsupp.single (vertexFace 3) 1 - Finsupp.single (vertexFace 2) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ,
    edge23_deleted_zero, edge23_deleted_one]
  all_goals simp only [sub_eq_add_neg]
private theorem edge03_boundary :
    boundary cycleK ℚ 0 (Finsupp.single edge03 1) =
      Finsupp.single (vertexFace 3) 1 - Finsupp.single (vertexFace 0) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ,
    edge03_deleted_zero, edge03_deleted_one]
  all_goals simp only [sub_eq_add_neg]

private noncomputable def cycleChain : Chain cycleK ℚ 1 :=
  Finsupp.single edge01 1 + Finsupp.single edge12 1 +
    Finsupp.single edge23 1 - Finsupp.single edge03 1

private theorem cycleChain_boundary : boundary cycleK ℚ 0 cycleChain = 0 := by
  simp only [cycleChain, map_add, map_sub, edge01_boundary,
    edge12_boundary, edge23_boundary, edge03_boundary]
  module

private theorem cycleChain_coeff : cycleChain edge01 = 1 := by
  have h12 : edge12 ≠ edge01 := by decide
  have h23 : edge23 ≠ edge01 := by decide
  have h03 : edge03 ≠ edge01 := by decide
  simp [cycleChain, h12, h23, h03]

private theorem cycleChain_ne_zero : cycleChain ≠ 0 := by
  intro hz
  have h := congrArg (fun c : Chain cycleK ℚ 1 => c edge01) hz
  rw [cycleChain_coeff] at h
  norm_num at h

private noncomputable def cycleHomologyCycle : simplicialCycles cycleK ℚ 1 :=
  ⟨cycleChain, by
    rw [simplicialCycles_succ]
    exact cycleChain_boundary⟩

private theorem cycleHomologyCycle_not_boundary :
    cycleHomologyCycle ∉ simplicialBoundaries cycleK ℚ 1 := by
  intro hb
  obtain ⟨c, hc⟩ := (mem_simplicialBoundaries_iff ℚ cycleK 1 _).mp hb
  have hc0 : c = 0 := by
    ext σ
    exact isEmptyElim σ
  rw [hc0, map_zero] at hc
  exact cycleChain_ne_zero hc.symm

set_option backward.isDefEq.respectTransparency false in
private theorem cycleHomologyClass_ne_zero :
    simplicialHomologyClass ℚ cycleK 1 cycleHomologyCycle ≠ 0 := by
  intro hz
  have hq := congrArg
    (homologyKernelQuotient ℚ (simplicialChainComplex cycleK ℚ) 1).hom.hom hz
  rw [simplicialHomologyClass_quotient, map_zero] at hq
  exact cycleHomologyCycle_not_boundary ((Submodule.Quotient.mk_eq_zero _).mp hq)

private theorem nearestDistance_ge_one {s : Finset (Fin 4)} (hs : s.Nonempty)
    {x : Fin 4} (hx : x ∉ s) : 1 ≤ nearestDistance s x := by
  obtain ⟨y, hy, heq⟩ := exists_nearest hs x
  rw [← heq]
  exact dist_ge_one_of_ne (fun h => hx (h ▸ hy))

private theorem insertionRadius_ge_one {x : Fin 4} (hx : x ≠ 0) :
    1 ≤ radius (0 : Fin 4) (insertionIndex 0 x - 1) := by
  letI : DecidableEq (Fin 4) := Classical.decEq _
  have hi : 0 < insertionIndex (0 : Fin 4) x := by
    have := (insertionIndex_eq_zero_iff (0 : Fin 4) x).not.mpr hx
    omega
  have hnot := not_mem_before_insertionIndex (0 : Fin 4) x
    (show insertionIndex (0 : Fin 4) x - 1 < insertionIndex 0 x by omega)
  have hmem := mem_insertionIndex (0 : Fin 4) x
  have heq : insertionIndex (0 : Fin 4) x = (insertionIndex 0 x - 1) + 1 := by omega
  rw [heq, prefix_succ, Finset.mem_insert] at hmem
  have hxnext : x = next (0 : Fin 4) (greedyPrefix 0 (insertionIndex 0 x - 1)) :=
    hmem.resolve_right hnot
  unfold radius
  rw [← hxnext]
  exact nearestDistance_ge_one (prefix_nonempty 0 _) hnot

private theorem deletionTime_ge_nine (x : Fin 4) :
    ∀ t ∈ deletionTime (0 : Fin 4) (1 / 3) x, 9 ≤ t := by
  intro t ht
  by_cases hx : x = 0
  · simp [hx] at ht
  · rw [deletionTime_of_ne 0 (1 / 3) hx] at ht
    have heq : t = radius (0 : Fin 4) (insertionIndex 0 x - 1) /
      ((1 / 3 : ℝ) * (1 - 2 * (1 / 3 : ℝ))) := by
      simpa [eq_comm] using ht
    rw [heq]
    have hr := insertionRadius_ge_one hx
    norm_num at hr ⊢
    linarith

private theorem weight_one_eq_zero (x : Fin 4) :
    weight (1 / 3) (deletionTime (0 : Fin 4) (1 / 3) x) 1 = 0 := by
  cases htx : deletionTime (0 : Fin 4) (1 / 3) x with
  | none => simp [weight]
  | some t =>
      have ht : 9 ≤ t := deletionTime_ge_nine x t (by
        simpa only [Option.mem_def, one_div] using htx)
      simpa only [weight_some] using (finiteWeight_of_le (by nlinarith :
        (1 : ℝ) ≤ (1 - 2 * (1 / 3 : ℝ)) * t))

private theorem closedActive_one (x : Fin 4) :
    ClosedActive (deletionTime (0 : Fin 4) (1 / 3) x) 1 := by
  cases htx : deletionTime (0 : Fin 4) (1 / 3) x with
  | none => trivial
  | some t =>
      have ht : 9 ≤ t := deletionTime_ge_nine x t (by
        simpa only [Option.mem_def, one_div] using htx)
      simpa [ClosedActive] using (show (1 : ℝ) ≤ t by linarith)

/-- At scale one the sparse complex is exactly the unweighted four-cycle Rips complex. -/
theorem sparse_eq_rips_one :
    sparseComplex (0 : Fin 4) (1 / 3) 1 =
      (Rips.filter inferInstance).sublevel 1 := by
  apply le_antisymm
  · intro σ hσ
    have hr := sparseComplex_le_relaxedComplex (0 : Fin 4)
      (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1 / 3) 1 hσ
    apply (Rips.mem_sublevel_iff _ _ _).mpr
    refine ⟨hr.1, ?_⟩
    intro x hx y hy
    have hxy := hr.2.2 x hx y hy
    simp only [relaxedDistance, weight_one_eq_zero, add_zero] at hxy
    exact hxy
  · intro σ hσ
    apply closedActiveComplex_le_sparseComplex (0 : Fin 4) (1 / 3) (by norm_num)
    refine ⟨?_, ?_⟩
    · obtain ⟨hne, hdist⟩ := (Rips.mem_sublevel_iff _ _ _).mp hσ
      refine ⟨hne, by norm_num, ?_⟩
      intro x hx y hy
      simpa only [relaxedDistance, ← one_div, weight_one_eq_zero, add_zero]
        using hdist x hx y hy
    · intro x hx
      exact closedActive_one x

/-- The actual sparse filter has a nonzero rational degree-one class at scale one.
All four cycle edges are present and there are no filling triangles. -/
theorem sparseFilter_h1_nonzero :
    ∃ z : simplicialHomology ((sparseFilter (0 : Fin 4) (1 / 3)).sublevel 1) ℚ 1,
      z ≠ 0 := by
  rw [sparseFilter_sublevel_eq (0 : Fin 4) (by norm_num) (by norm_num) 1,
    sparse_eq_rips_one, rips_one_eq_cycleK]
  exact ⟨simplicialHomologyClass ℚ cycleK 1 cycleHomologyCycle,
    cycleHomologyClass_ne_zero⟩

/-- The sparse-to-relaxed degree-one comparison acts on a nonzero class here. -/
theorem sparse_relaxed_h1_nonzero :
    ∃ z : simplicialHomology (sparseComplex (0 : Fin 4) (1 / 3) 1) ℚ 1,
      (simplicialHomologyIncl ℚ
        (sparseComplex_le_relaxedComplex (0 : Fin 4)
          (by norm_num : (0 : ℝ) < 1 / 3)
          (by norm_num : (1 / 3 : ℝ) ≤ 1 / 3) 1) 1).hom z ≠ 0 := by
  have hsparse :
      ∃ z : simplicialHomology (sparseComplex (0 : Fin 4) (1 / 3) 1) ℚ 1,
        z ≠ 0 := by
    rw [sparse_eq_rips_one, rips_one_eq_cycleK]
    exact ⟨simplicialHomologyClass ℚ cycleK 1 cycleHomologyCycle,
      cycleHomologyClass_ne_zero⟩
  obtain ⟨z, hz⟩ := hsparse
  let f := simplicialHomologyIncl ℚ
      (sparseComplex_le_relaxedComplex (0 : Fin 4)
        (by norm_num : (0 : ℝ) < 1 / 3)
        (by norm_num : (1 / 3 : ℝ) ≤ 1 / 3) 1) 1
  have hIso : IsIso f :=
    isIso_sparse_relaxed_all ℚ (0 : Fin 4)
      (show (0 : ℝ) < 1 / 3 by norm_num)
      (show (1 / 3 : ℝ) ≤ 1 / 3 by norm_num) 1 1
  refine ⟨z, ?_⟩
  intro hzero
  haveI : IsIso f := hIso
  have hinj : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).mp inferInstance
  exact hz (hinj (by simpa [f] using hzero))

end

end TDA.Filtration.SparseRips.H1Examples
