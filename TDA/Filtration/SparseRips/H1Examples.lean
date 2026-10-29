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

/-! A short pendant at the seed can be deleted while the four-cycle survives. -/

private abbrev PendantCycle := Option (Fin 4)

private instance : LinearOrder PendantCycle :=
  LinearOrder.lift'
    (fun x => match x with
      | none => (0 : ℕ)
      | some i => i.val + 1)
    (by
      intro x y h
      cases x with
      | none =>
          cases y with
          | none => rfl
          | some j => simp at h
      | some i =>
          cases y with
          | none => simp at h
          | some j =>
              apply congrArg some
              change i.val + 1 = j.val + 1 at h
              exact Fin.ext (by omega))

private def anchor : PendantCycle → Fin 4
  | none => 0
  | some i => i

private def leafPenalty : PendantCycle → ℝ
  | none => 1 / 20
  | some _ => 0

private theorem leafPenalty_nonneg (x : PendantCycle) : 0 ≤ leafPenalty x := by
  cases x <;> norm_num [leafPenalty]

private def leafDist (x y : PendantCycle) : ℝ :=
  if x = y then 0 else dist (anchor x) (anchor y) + leafPenalty x + leafPenalty y

private theorem leafDist_nonneg (x y : PendantCycle) : 0 ≤ leafDist x y := by
  unfold leafDist
  split_ifs
  · norm_num
  · have hx := leafPenalty_nonneg x
    have hy := leafPenalty_nonneg y
    linarith [dist_nonneg (x := anchor x) (y := anchor y)]

private theorem leafDist_pos_of_ne {x y : PendantCycle} (hxy : x ≠ y) :
    0 < leafDist x y := by
  cases x with
  | none =>
      cases y with
      | none => exact False.elim (hxy rfl)
      | some j =>
          have hd := dist_nonneg (x := (0 : Fin 4)) (y := j)
          simp only [leafDist, reduceCtorEq, if_false, anchor, leafPenalty]
          linarith
  | some i =>
      cases y with
      | none =>
          have hd := dist_nonneg (x := i) (y := (0 : Fin 4))
          simp only [leafDist, reduceCtorEq, if_false, anchor, leafPenalty]
          linarith
      | some j =>
          have hij : i ≠ j := fun h => hxy (congrArg some h)
          have hd : 0 < dist i j := dist_pos.mpr hij
          simpa [leafDist, anchor, leafPenalty, hij] using hd

private instance : MetricSpace PendantCycle where
  dist := leafDist
  dist_self := by intro x; simp [leafDist]
  dist_comm := by
    intro x y
    by_cases hxy : x = y
    · subst y; rfl
    · simp only [leafDist, if_neg hxy, if_neg (Ne.symm hxy)]
      rw [dist_comm]
      ring
  dist_triangle := by
    intro x y z
    by_cases hxy : x = y
    · subst y; simp [leafDist]
    · by_cases hyz : y = z
      · subst z; simp [leafDist]
      · by_cases hxz : x = z
        · subst z
          have h₁ := leafDist_nonneg x y
          have h₂ := leafDist_nonneg y x
          simpa [leafDist] using (add_nonneg h₁ h₂)
        · simp only [leafDist, if_neg hxy, if_neg hyz, if_neg hxz]
          have ht := dist_triangle (anchor x) (anchor y) (anchor z)
          have hp := leafPenalty_nonneg y
          linarith
  eq_of_dist_eq_zero := by
    intro x y h
    by_contra hxy
    exact (ne_of_gt (leafDist_pos_of_ne hxy)) h

private theorem pendantRadius_eq_nearest {x : PendantCycle} (hx : x ≠ some (0 : Fin 4)) :
    radius (some (0 : Fin 4)) (insertionIndex (some (0 : Fin 4)) x - 1) =
      nearestDistance (greedyPrefix (some (0 : Fin 4)) (insertionIndex (some (0 : Fin 4)) x - 1)) x := by
  letI : DecidableEq PendantCycle := Classical.decEq _
  have hi : 0 < insertionIndex (some (0 : Fin 4)) x := by
    have := (insertionIndex_eq_zero_iff (some (0 : Fin 4)) x).not.mpr hx
    omega
  have hnot := not_mem_before_insertionIndex (some (0 : Fin 4)) x
    (show insertionIndex (some (0 : Fin 4)) x - 1 < insertionIndex (some (0 : Fin 4)) x by omega)
  have hmem := mem_insertionIndex (some (0 : Fin 4)) x
  have heq : insertionIndex (some (0 : Fin 4)) x =
      (insertionIndex (some (0 : Fin 4)) x - 1) + 1 := by omega
  rw [heq, prefix_succ, Finset.mem_insert] at hmem
  have hxnext : x = next (some (0 : Fin 4))
      (greedyPrefix (some (0 : Fin 4)) (insertionIndex (some (0 : Fin 4)) x - 1)) :=
    hmem.resolve_right hnot
  unfold radius
  exact congrArg (nearestDistance
    (greedyPrefix (some (0 : Fin 4)) (insertionIndex (some (0 : Fin 4)) x - 1)))
    hxnext.symm

private theorem coreDist_ge_one {i : Fin 4} (hi : i ≠ 0)
    {y : PendantCycle} (hy : y ≠ some i) : 1 ≤ dist (some i) y := by
  cases y with
  | none =>
      have hd := dist_ge_one_of_ne hi
      change 1 ≤ dist i (0 : Fin 4) + 0 + 1 / 20
      linarith
  | some j =>
      have hij : i ≠ j := fun h => hy (congrArg some h.symm)
      change 1 ≤ leafDist (some i) (some j)
      simpa [leafDist, anchor, leafPenalty, hij] using
        (dist_ge_one_of_ne hij)

private theorem coreRadius_ge_one {i : Fin 4} (hi : i ≠ 0) :
    1 ≤ radius (some (0 : Fin 4))
      (insertionIndex (some (0 : Fin 4)) (some i) - 1) := by
  have hx : (some i : PendantCycle) ≠ some (0 : Fin 4) := by simp [hi]
  rw [pendantRadius_eq_nearest hx]
  let s := greedyPrefix (some (0 : Fin 4))
    (insertionIndex (some (0 : Fin 4)) (some i) - 1)
  have hs : s.Nonempty := prefix_nonempty (some (0 : Fin 4)) _
  have hnot : (some i : PendantCycle) ∉ s :=
    not_mem_before_insertionIndex (some (0 : Fin 4)) (some i)
      (by have := (insertionIndex_eq_zero_iff (some (0 : Fin 4)) (some i)).not.mpr hx
          omega)
  obtain ⟨y, hy, heq⟩ := exists_nearest hs (some i)
  rw [← heq]
  exact coreDist_ge_one hi (fun h => hnot (h ▸ hy))

private theorem pendantRadius_le :
    radius (some (0 : Fin 4))
      (insertionIndex (some (0 : Fin 4)) (none : PendantCycle) - 1) ≤ 1 / 20 := by
  rw [pendantRadius_eq_nearest (by simp)]
  have hseed : (some (0 : Fin 4)) ∈
      greedyPrefix (some (0 : Fin 4)) (insertionIndex (some (0 : Fin 4)) (none : PendantCycle) - 1) :=
    seed_mem_prefix (some (0 : Fin 4)) _
  have hle := nearestDistance_le (x := (none : PendantCycle)) hseed
  have hd : dist (none : PendantCycle) (some (0 : Fin 4)) = (1 / 20 : ℝ) := by
    change leafDist none (some (0 : Fin 4)) = _
    simp [leafDist, anchor, leafPenalty]
  simpa [hd] using hle

/-- The pendant point has a finite deletion time strictly before the scale-one cycle. -/
theorem pendant_deleted_before_one :
    ∃ t, deletionTime (some (0 : Fin 4)) (1 / 3) (none : PendantCycle) = some t ∧
      t < 1 := by
  let t := radius (some (0 : Fin 4))
      (insertionIndex (some (0 : Fin 4)) (none : PendantCycle) - 1) /
        ((1 / 3 : ℝ) * (1 - 2 * (1 / 3 : ℝ)))
  refine ⟨t, deletionTime_of_ne (some (0 : Fin 4)) (1 / 3) (by simp), ?_⟩
  have hr := pendantRadius_le
  dsimp [t]
  norm_num at hr ⊢
  linarith

/-- At scale one the pendant vertex has passed its deletion time. -/
theorem pendant_inactive_one :
    ¬ ClosedActive
      (deletionTime (some (0 : Fin 4)) (1 / 3) (none : Option (Fin 4))) 1 := by
  obtain ⟨t, ht, hlt⟩ := pendant_deleted_before_one
  rw [ht]
  exact not_le_of_gt hlt

private theorem core_closedActive_one (i : Fin 4) :
    ClosedActive (deletionTime (some (0 : Fin 4)) (1 / 3) (some i)) 1 := by
  by_cases hi : i = 0
  · subst i; simp [ClosedActive]
  · rw [deletionTime_of_ne (some (0 : Fin 4)) (1 / 3) (by simp [hi])]
    have hr := coreRadius_ge_one hi
    norm_num [ClosedActive] at hr ⊢
    linarith

private theorem core_weight_one_eq_zero (i : Fin 4) :
    weight (1 / 3) (deletionTime (some (0 : Fin 4)) (1 / 3) (some i)) 1 = 0 := by
  by_cases hi : i = 0
  · subst i; simp [weight]
  · rw [deletionTime_of_ne (some (0 : Fin 4)) (1 / 3) (by simp [hi]), weight_some]
    have hr := coreRadius_ge_one hi
    apply finiteWeight_of_le
    norm_num at hr ⊢
    linarith

private theorem core_distance_eq (i j : Fin 4) :
    dist (some i : PendantCycle) (some j) = dist i j := by
  change leafDist (some i) (some j) = dist i j
  by_cases hij : i = j
  · subst j; simp [leafDist, anchor, leafPenalty]
  · simp [leafDist, anchor, leafPenalty, hij]

private theorem anchor_distance_le (x y : PendantCycle) :
    dist (anchor x) (anchor y) ≤ dist x y := by
  change dist (anchor x) (anchor y) ≤ leafDist x y
  unfold leafDist
  split_ifs with h
  · subst y; simp
  · have hx := leafPenalty_nonneg x
    have hy := leafPenalty_nonneg y
    linarith

private abbrev coreSparse : PreAbstractSimplicialComplex (Fin 4) :=
  sparseComplex (0 : Fin 4) (1 / 3) 1

private abbrev pendantSparse : PreAbstractSimplicialComplex PendantCycle :=
  sparseComplex (some (0 : Fin 4)) (1 / 3) 1

private def coreSection : VertexMap coreSparse pendantSparse where
  toFun := some
  map_face := by
    classical
    letI : DecidableEq PendantCycle := Classical.decEq _
    intro σ hσ
    have hrips : σ ∈ (Rips.filter inferInstance).sublevel 1 := by
      rw [← sparse_eq_rips_one]
      exact hσ
    obtain ⟨hne, hdist⟩ := (Rips.mem_sublevel_iff _ _ _).mp hrips
    apply closedActiveComplex_le_sparseComplex (some (0 : Fin 4)) (1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1)
    refine ⟨⟨hne.image some, by norm_num, ?_⟩, ?_⟩
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hxy := hdist i hi j hj
      simpa only [relaxedDistance, core_weight_one_eq_zero, core_distance_eq,
        add_zero] using hxy
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact core_closedActive_one i

private def pendantCollapse : VertexMap pendantSparse coreSparse where
  toFun := anchor
  map_face := by
    classical
    letI : DecidableEq (Fin 4) := Classical.decEq _
    intro σ hσ
    have hrelaxed := sparseComplex_le_relaxedComplex (some (0 : Fin 4))
      (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num : (1 / 3 : ℝ) ≤ 1 / 3) 1 hσ
    have hrips := relaxedComplex_le_rips (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (deletionTime (some (0 : Fin 4)) (1 / 3)) hrelaxed
    dsimp only [coreSparse]
    rw [sparse_eq_rips_one]
    apply (Rips.mem_sublevel_iff _ _ _).mpr
    obtain ⟨hne, hdist⟩ := (Rips.mem_sublevel_iff _ _ _).mp hrips
    refine ⟨hne.image anchor, ?_⟩
    intro i hi j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
    exact (anchor_distance_le x y).trans (hdist x hx y hy)

private theorem coreSection_collapse :
    VertexMap.comp coreSection pendantCollapse = VertexMap.id coreSparse := by
  apply VertexMap.ext
  intro i
  rfl

/-- A pendant vertex is actually deleted before scale one, while the surviving four-cycle
has a nonzero rational `H₁` class in the sparse complex. The sparse-to-relaxed comparison
also sends this class to a nonzero class. -/
theorem deleted_pendant_h1_nonzero :
    (∃ t : ℝ, deletionTime (some (0 : Fin 4)) (1 / 3) (none : Option (Fin 4)) = some t ∧
      t < 1) ∧
    ∃ z : simplicialHomology
        (sparseComplex (some (0 : Fin 4)) (1 / 3) 1) ℚ 1,
      z ≠ 0 ∧
      (simplicialHomologyIncl ℚ
        (sparseComplex_le_relaxedComplex (some (0 : Fin 4))
          (by norm_num : (0 : ℝ) < 1 / 3)
          (by norm_num : (1 / 3 : ℝ) ≤ 1 / 3) 1) 1).hom z ≠ 0 := by
  constructor
  · exact pendant_deleted_before_one
  have hcore : ∃ z : simplicialHomology coreSparse ℚ 1, z ≠ 0 := by
    change ∃ z : simplicialHomology (sparseComplex (0 : Fin 4) (1 / 3) 1) ℚ 1,
      z ≠ 0
    rw [sparse_eq_rips_one, rips_one_eq_cycleK]
    exact ⟨simplicialHomologyClass ℚ cycleK 1 cycleHomologyCycle,
      cycleHomologyClass_ne_zero⟩
  obtain ⟨z, hz⟩ := hcore
  let f := simplicialHomologyMap ℚ coreSection 1
  let g := simplicialHomologyMap ℚ pendantCollapse 1
  have hfg : f ≫ g = 𝟙 (simplicialHomology coreSparse ℚ 1) := by
    dsimp only [f, g]
    rw [← simplicialHomologyMap_comp, coreSection_collapse]
    exact simplicialHomologyMap_id ℚ coreSparse 1
  have hcomp : g.hom (f.hom z) = z := by
    have h := congrArg
      (fun q : simplicialHomology coreSparse ℚ 1 ⟶
          simplicialHomology coreSparse ℚ 1 => q.hom z) hfg
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h
  have hnonzero : f.hom z ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hcomp
    exact hz hcomp.symm
  let h := simplicialHomologyIncl ℚ
    (sparseComplex_le_relaxedComplex (some (0 : Fin 4))
      (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num : (1 / 3 : ℝ) ≤ 1 / 3) 1) 1
  have hIso : IsIso h :=
    isIso_sparse_relaxed_all ℚ (some (0 : Fin 4))
      (show (0 : ℝ) < 1 / 3 by norm_num)
      (show (1 / 3 : ℝ) ≤ 1 / 3 by norm_num) 1 1
  refine ⟨f.hom z, hnonzero, ?_⟩
  intro hzero
  haveI : IsIso h := hIso
  have hinj : Function.Injective h.hom := (ModuleCat.mono_iff_injective h).mp inferInstance
  exact hnonzero (hinj (by simpa [h] using hzero))

end

end TDA.Filtration.SparseRips.H1Examples
