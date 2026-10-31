import TDA.Persistence.RankResolutionDegreeTwo
import TDA.Persistence.FiniteSimplicialPresentation
import Mathlib.Tactic

/-!
# A finite simplicial realization of the degree-two witness

The fourteen proper nonempty faces of a tetrahedron carry the literal two-coordinate
face grading below. Over any field, actual edge-boundary equations give a three-cycle
normal form. Explicit available triangle chains identify the kernel of the common-edge
coefficient at all nine grid stages. The resulting cycle/boundary quotient equivalences
commute with all inclusions and yield `finiteIso` for actual degree-one homology.

The coefficient functional is set to zero outside the three supported stages. Every
certificate uses only addition and subtraction, so the construction includes characteristic
two. The final grid theorem identifies the actual face-coordinate grid exactly.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open TDA.Simplicial TDA.Filtration

/-- The boundary tetrahedron has all fourteen nonempty proper faces on `Fin 4`. -/
def boundaryTetrahedron : FiniteComplex 4 where
  faces := Finset.univ.filter (fun s : Finset (Fin 4) => s.Nonempty ∧ s.card ≤ 3)
  nonempty := by
    intro s hs
    have hs' : s.Nonempty ∧ s.card ≤ 3 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hs
    exact hs'.1
  downClosed := by
    intro s t hs ht hts
    have hs' : s.Nonempty ∧ s.card ≤ 3 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ht, (Finset.card_le_card hts).trans hs'.2⟩

private def faceGradeX (s : Finset (Fin 4)) : ℕ :=
  if ({0, 1, 3} : Finset (Fin 4)) ⊆ s then 2
  else if ({0, 3} : Finset (Fin 4)) ⊆ s ∨
      ({1, 3} : Finset (Fin 4)) ⊆ s ∨ ({2, 3} : Finset (Fin 4)) ⊆ s then 1
  else 0

private def faceGradeY (s : Finset (Fin 4)) : ℕ :=
  if ({0, 1, 2} : Finset (Fin 4)) ⊆ s then 2
  else if ({0, 2} : Finset (Fin 4)) ⊆ s ∨
      ({1, 2} : Finset (Fin 4)) ⊆ s ∨ ({2, 3} : Finset (Fin 4)) ⊆ s then 1
  else 0

private def faceGradeNat (s : TotalFace boundaryTetrahedron.toPre) : Fin 2 → ℕ :=
  fun i => if i = 0 then faceGradeX s.val else faceGradeY s.val

private theorem faceGradeNat_mono {s t : TotalFace boundaryTetrahedron.toPre}
    (hst : s.val ⊆ t.val) : faceGradeNat s ≤ faceGradeNat t := by
  classical
  intro i
  fin_cases i
  · simp only [faceGradeNat]
    unfold faceGradeX
    by_cases hs : ({0, 1, 3} : Finset (Fin 4)) ⊆ s.val
    · have ht : ({0, 1, 3} : Finset (Fin 4)) ⊆ t.val := hs.trans hst
      simp [hs, ht]
    · by_cases hp : ({0, 3} : Finset (Fin 4)) ⊆ s.val ∨
        ({1, 3} : Finset (Fin 4)) ⊆ s.val ∨ ({2, 3} : Finset (Fin 4)) ⊆ s.val
      · have hpt : ({0, 3} : Finset (Fin 4)) ⊆ t.val ∨
          ({1, 3} : Finset (Fin 4)) ⊆ t.val ∨ ({2, 3} : Finset (Fin 4)) ⊆ t.val := by
          rcases hp with h | h | h
          · exact Or.inl (h.trans hst)
          · exact Or.inr (Or.inl (h.trans hst))
          · exact Or.inr (Or.inr (h.trans hst))
        by_cases ht : ({0, 1, 3} : Finset (Fin 4)) ⊆ t.val <;>
          simp [hs, hp, hpt, ht]
      · simp [hs, hp]
  · simp only [faceGradeNat]
    unfold faceGradeY
    by_cases hs : ({0, 1, 2} : Finset (Fin 4)) ⊆ s.val
    · have ht : ({0, 1, 2} : Finset (Fin 4)) ⊆ t.val := hs.trans hst
      simp [hs, ht]
    · by_cases hp : ({0, 2} : Finset (Fin 4)) ⊆ s.val ∨
        ({1, 2} : Finset (Fin 4)) ⊆ s.val ∨ ({2, 3} : Finset (Fin 4)) ⊆ s.val
      · have hpt : ({0, 2} : Finset (Fin 4)) ⊆ t.val ∨
          ({1, 2} : Finset (Fin 4)) ⊆ t.val ∨ ({2, 3} : Finset (Fin 4)) ⊆ t.val := by
          rcases hp with h | h | h
          · exact Or.inl (h.trans hst)
          · exact Or.inr (Or.inl (h.trans hst))
          · exact Or.inr (Or.inr (h.trans hst))
        by_cases ht : ({0, 1, 2} : Finset (Fin 4)) ⊆ t.val <;>
          simp [hs, hp, hpt, ht]
      · simp [hs, hp]

/-- The literal coordinate grades on the boundary tetrahedron.

Vertices and edge `01` have grade `(0,0)`; edges `02,12` have `(0,1)`;
edges `03,13` have `(1,0)`; edge `23` and triangles `023,123` have `(1,1)`;
triangles `012` and `013` have `(0,2)` and `(2,0)`, respectively. -/
def boundaryTetrahedronGrading : FiniteGraded boundaryTetrahedron 2 where
  grade s i := (faceGradeNat s i : ℝ)
  mono := by
    intro s t h i
    change (faceGradeNat s i : ℝ) ≤ (faceGradeNat t i : ℝ)
    exact_mod_cast faceGradeNat_mono h i

theorem boundaryTetrahedron_card : boundaryTetrahedron.faces.card = 14 := by
  decide

private def vertex (i : Fin 4) : Face boundaryTetrahedron.toPre 0 :=
  ⟨{i}, by change {i} ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by simp⟩

private def edge01 : Face boundaryTetrahedron.toPre 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def edge02 : Face boundaryTetrahedron.toPre 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def edge03 : Face boundaryTetrahedron.toPre 1 :=
  ⟨{0, 3}, by change ({0, 3} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def edge12 : Face boundaryTetrahedron.toPre 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def edge13 : Face boundaryTetrahedron.toPre 1 :=
  ⟨{1, 3}, by change ({1, 3} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def edge23 : Face boundaryTetrahedron.toPre 1 :=
  ⟨{2, 3}, by change ({2, 3} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def triangle012 : Face boundaryTetrahedron.toPre 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def triangle013 : Face boundaryTetrahedron.toPre 2 :=
  ⟨{0, 1, 3}, by change ({0, 1, 3} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def triangle023 : Face boundaryTetrahedron.toPre 2 :=
  ⟨{0, 2, 3}, by change ({0, 2, 3} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def triangle123 : Face boundaryTetrahedron.toPre 2 :=
  ⟨{1, 2, 3}, by change ({1, 2, 3} : Finset (Fin 4)) ∈ boundaryTetrahedron.faces; simp [boundaryTetrahedron], by decide⟩

private def pairOrderEmb (a b : Fin 4) (hab : a < b) : Fin 2 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (fun i => if i = 0 then a else b) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all)

private def tripleOrderEmb (a b c : Fin 4) (hab : a < b) (hbc : b < c) : Fin 3 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (fun i => if i = 0 then a else if i = 1 then b else c) (by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact hab.trans hbc | simp_all)

private theorem edge01_orderEmb :
    edge01.1.orderEmbOfFin edge01.2.2 = pairOrderEmb 0 1 (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [pairOrderEmb, edge01]

private theorem edge02_orderEmb :
    edge02.1.orderEmbOfFin edge02.2.2 = pairOrderEmb 0 2 (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [pairOrderEmb, edge02]

private theorem edge03_orderEmb :
    edge03.1.orderEmbOfFin edge03.2.2 = pairOrderEmb 0 3 (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [pairOrderEmb, edge03]

private theorem edge12_orderEmb :
    edge12.1.orderEmbOfFin edge12.2.2 = pairOrderEmb 1 2 (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [pairOrderEmb, edge12]

private theorem edge13_orderEmb :
    edge13.1.orderEmbOfFin edge13.2.2 = pairOrderEmb 1 3 (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [pairOrderEmb, edge13]

private theorem edge23_orderEmb :
    edge23.1.orderEmbOfFin edge23.2.2 = pairOrderEmb 2 3 (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [pairOrderEmb, edge23]

private theorem triangle012_orderEmb :
    triangle012.1.orderEmbOfFin triangle012.2.2 = tripleOrderEmb 0 1 2 (by decide) (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [tripleOrderEmb, triangle012]

private theorem triangle013_orderEmb :
    triangle013.1.orderEmbOfFin triangle013.2.2 = tripleOrderEmb 0 1 3 (by decide) (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [tripleOrderEmb, triangle013]

private theorem triangle023_orderEmb :
    triangle023.1.orderEmbOfFin triangle023.2.2 = tripleOrderEmb 0 2 3 (by decide) (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [tripleOrderEmb, triangle023]

private theorem triangle123_orderEmb :
    triangle123.1.orderEmbOfFin triangle123.2.2 = tripleOrderEmb 1 2 3 (by decide) (by decide) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [tripleOrderEmb, triangle123]

private theorem edge01_del0 : deletedFace boundaryTetrahedron.toPre 0 edge01 0 = vertex 1 := by
  apply Subtype.ext
  change edge01.1.erase (edge01.1.orderEmbOfFin edge01.2.2 0) = (vertex 1).1
  rw [edge01_orderEmb]
  decide

private theorem edge01_del1 : deletedFace boundaryTetrahedron.toPre 0 edge01 1 = vertex 0 := by
  apply Subtype.ext
  change edge01.1.erase (edge01.1.orderEmbOfFin edge01.2.2 1) = (vertex 0).1
  rw [edge01_orderEmb]
  decide

private theorem edge02_del0 : deletedFace boundaryTetrahedron.toPre 0 edge02 0 = vertex 2 := by
  apply Subtype.ext
  change edge02.1.erase (edge02.1.orderEmbOfFin edge02.2.2 0) = (vertex 2).1
  rw [edge02_orderEmb]
  decide

private theorem edge02_del1 : deletedFace boundaryTetrahedron.toPre 0 edge02 1 = vertex 0 := by
  apply Subtype.ext
  change edge02.1.erase (edge02.1.orderEmbOfFin edge02.2.2 1) = (vertex 0).1
  rw [edge02_orderEmb]
  decide

private theorem edge03_del0 : deletedFace boundaryTetrahedron.toPre 0 edge03 0 = vertex 3 := by
  apply Subtype.ext
  change edge03.1.erase (edge03.1.orderEmbOfFin edge03.2.2 0) = (vertex 3).1
  rw [edge03_orderEmb]
  decide

private theorem edge03_del1 : deletedFace boundaryTetrahedron.toPre 0 edge03 1 = vertex 0 := by
  apply Subtype.ext
  change edge03.1.erase (edge03.1.orderEmbOfFin edge03.2.2 1) = (vertex 0).1
  rw [edge03_orderEmb]
  decide

private theorem edge12_del0 : deletedFace boundaryTetrahedron.toPre 0 edge12 0 = vertex 2 := by
  apply Subtype.ext
  change edge12.1.erase (edge12.1.orderEmbOfFin edge12.2.2 0) = (vertex 2).1
  rw [edge12_orderEmb]
  decide

private theorem edge12_del1 : deletedFace boundaryTetrahedron.toPre 0 edge12 1 = vertex 1 := by
  apply Subtype.ext
  change edge12.1.erase (edge12.1.orderEmbOfFin edge12.2.2 1) = (vertex 1).1
  rw [edge12_orderEmb]
  decide

private theorem edge13_del0 : deletedFace boundaryTetrahedron.toPre 0 edge13 0 = vertex 3 := by
  apply Subtype.ext
  change edge13.1.erase (edge13.1.orderEmbOfFin edge13.2.2 0) = (vertex 3).1
  rw [edge13_orderEmb]
  decide

private theorem edge13_del1 : deletedFace boundaryTetrahedron.toPre 0 edge13 1 = vertex 1 := by
  apply Subtype.ext
  change edge13.1.erase (edge13.1.orderEmbOfFin edge13.2.2 1) = (vertex 1).1
  rw [edge13_orderEmb]
  decide

private theorem edge23_del0 : deletedFace boundaryTetrahedron.toPre 0 edge23 0 = vertex 3 := by
  apply Subtype.ext
  change edge23.1.erase (edge23.1.orderEmbOfFin edge23.2.2 0) = (vertex 3).1
  rw [edge23_orderEmb]
  decide

private theorem edge23_del1 : deletedFace boundaryTetrahedron.toPre 0 edge23 1 = vertex 2 := by
  apply Subtype.ext
  change edge23.1.erase (edge23.1.orderEmbOfFin edge23.2.2 1) = (vertex 2).1
  rw [edge23_orderEmb]
  decide

private theorem triangle012_del0 : deletedFace boundaryTetrahedron.toPre 1 triangle012 0 = edge12 := by
  apply Subtype.ext
  change triangle012.1.erase (triangle012.1.orderEmbOfFin triangle012.2.2 0) = edge12.1
  rw [triangle012_orderEmb]
  decide

private theorem triangle012_del1 : deletedFace boundaryTetrahedron.toPre 1 triangle012 1 = edge02 := by
  apply Subtype.ext
  change triangle012.1.erase (triangle012.1.orderEmbOfFin triangle012.2.2 1) = edge02.1
  rw [triangle012_orderEmb]
  decide

private theorem triangle012_del2 : deletedFace boundaryTetrahedron.toPre 1 triangle012 2 = edge01 := by
  apply Subtype.ext
  change triangle012.1.erase (triangle012.1.orderEmbOfFin triangle012.2.2 2) = edge01.1
  rw [triangle012_orderEmb]
  decide

private theorem triangle013_del0 : deletedFace boundaryTetrahedron.toPre 1 triangle013 0 = edge13 := by
  apply Subtype.ext
  change triangle013.1.erase (triangle013.1.orderEmbOfFin triangle013.2.2 0) = edge13.1
  rw [triangle013_orderEmb]
  decide

private theorem triangle013_del1 : deletedFace boundaryTetrahedron.toPre 1 triangle013 1 = edge03 := by
  apply Subtype.ext
  change triangle013.1.erase (triangle013.1.orderEmbOfFin triangle013.2.2 1) = edge03.1
  rw [triangle013_orderEmb]
  decide

private theorem triangle013_del2 : deletedFace boundaryTetrahedron.toPre 1 triangle013 2 = edge01 := by
  apply Subtype.ext
  change triangle013.1.erase (triangle013.1.orderEmbOfFin triangle013.2.2 2) = edge01.1
  rw [triangle013_orderEmb]
  decide

private theorem triangle023_del0 : deletedFace boundaryTetrahedron.toPre 1 triangle023 0 = edge23 := by
  apply Subtype.ext
  change triangle023.1.erase (triangle023.1.orderEmbOfFin triangle023.2.2 0) = edge23.1
  rw [triangle023_orderEmb]
  decide

private theorem triangle023_del1 : deletedFace boundaryTetrahedron.toPre 1 triangle023 1 = edge03 := by
  apply Subtype.ext
  change triangle023.1.erase (triangle023.1.orderEmbOfFin triangle023.2.2 1) = edge03.1
  rw [triangle023_orderEmb]
  decide

private theorem triangle023_del2 : deletedFace boundaryTetrahedron.toPre 1 triangle023 2 = edge02 := by
  apply Subtype.ext
  change triangle023.1.erase (triangle023.1.orderEmbOfFin triangle023.2.2 2) = edge02.1
  rw [triangle023_orderEmb]
  decide

private theorem triangle123_del0 : deletedFace boundaryTetrahedron.toPre 1 triangle123 0 = edge23 := by
  apply Subtype.ext
  change triangle123.1.erase (triangle123.1.orderEmbOfFin triangle123.2.2 0) = edge23.1
  rw [triangle123_orderEmb]
  decide

private theorem triangle123_del1 : deletedFace boundaryTetrahedron.toPre 1 triangle123 1 = edge13 := by
  apply Subtype.ext
  change triangle123.1.erase (triangle123.1.orderEmbOfFin triangle123.2.2 1) = edge13.1
  rw [triangle123_orderEmb]
  decide

private theorem triangle123_del2 : deletedFace boundaryTetrahedron.toPre 1 triangle123 2 = edge12 := by
  apply Subtype.ext
  change triangle123.1.erase (triangle123.1.orderEmbOfFin triangle123.2.2 2) = edge12.1
  rw [triangle123_orderEmb]
  decide

private theorem boundary_edge01 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge01 1) =
      Finsupp.single (vertex 1) 1 - Finsupp.single (vertex 0) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, edge01_del0, edge01_del1]
  abel

private theorem boundary_edge02 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge02 1) =
      Finsupp.single (vertex 2) 1 - Finsupp.single (vertex 0) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, edge02_del0, edge02_del1]
  abel

private theorem boundary_edge03 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge03 1) =
      Finsupp.single (vertex 3) 1 - Finsupp.single (vertex 0) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, edge03_del0, edge03_del1]
  abel

private theorem boundary_edge12 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge12 1) =
      Finsupp.single (vertex 2) 1 - Finsupp.single (vertex 1) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, edge12_del0, edge12_del1]
  abel

private theorem boundary_edge13 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge13 1) =
      Finsupp.single (vertex 3) 1 - Finsupp.single (vertex 1) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, edge13_del0, edge13_del1]
  abel

private theorem boundary_edge23 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge23 1) =
      Finsupp.single (vertex 3) 1 - Finsupp.single (vertex 2) 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, edge23_del0, edge23_del1]
  abel

private theorem boundary_triangle012 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 1 (Finsupp.single triangle012 1) =
      Finsupp.single edge01 1 - Finsupp.single edge02 1 + Finsupp.single edge12 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, triangle012_del0, triangle012_del1, triangle012_del2]
  abel

private theorem boundary_triangle013 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 1 (Finsupp.single triangle013 1) =
      Finsupp.single edge01 1 - Finsupp.single edge03 1 + Finsupp.single edge13 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, triangle013_del0, triangle013_del1, triangle013_del2]
  abel

private theorem boundary_triangle023 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 1 (Finsupp.single triangle023 1) =
      Finsupp.single edge02 1 - Finsupp.single edge03 1 + Finsupp.single edge23 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, triangle023_del0, triangle023_del1, triangle023_del2]
  abel

private theorem boundary_triangle123 (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 1 (Finsupp.single triangle123 1) =
      Finsupp.single edge12 1 - Finsupp.single edge13 1 + Finsupp.single edge23 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, triangle123_del0, triangle123_del1, triangle123_del2]
  abel

private noncomputable def chainCoeff (k : Type u) [Field k]
    (n : ℕ) (e : Face boundaryTetrahedron.toPre n) :
    Chain boundaryTetrahedron.toPre k n →ₗ[k] k where
  toFun z := z e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem edge_cases (e : Face boundaryTetrahedron.toPre 1) :
    e = edge01 ∨ e = edge02 ∨ e = edge03 ∨
      e = edge12 ∨ e = edge13 ∨ e = edge23 := by
  classical
  obtain ⟨i, j, hij, hset⟩ := Finset.card_eq_two.mp e.2.2
  have hval : e.val = {i, j} := hset
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact Or.inl (Subtype.ext (by rw [hval]; decide))
    | exact Or.inr (Or.inl (Subtype.ext (by rw [hval]; decide)))
    | exact Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [hval]; decide))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [hval]; decide)))) )
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [hval]; decide))))) )
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext (by rw [hval]; decide))))) )
    | simp_all

private theorem boundary_single_scale (k : Type u) [Field k]
    (e : Face boundaryTetrahedron.toPre 1) (a : k) :
    boundary boundaryTetrahedron.toPre k 0 (Finsupp.single e a) =
      a • boundary boundaryTetrahedron.toPre k 0 (Finsupp.single e 1) := by
  rw [boundary_single, boundary_single]
  simp

private theorem boundaryCoeff_vertex1 (k : Type u) [Field k] :
    (chainCoeff k 0 (vertex 1)).comp (boundary boundaryTetrahedron.toPre k 0) =
      chainCoeff k 1 edge01 - chainCoeff k 1 edge12 - chainCoeff k 1 edge13 := by
  apply Finsupp.lhom_ext
  intro e a
  rcases edge_cases e with h | h | h | h | h | h
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge01 a)) (vertex 1) = _
    rw [boundary_single_scale, boundary_edge01]
    simp [chainCoeff, vertex, edge01, edge12, edge13, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge02 a)) (vertex 1) = _
    rw [boundary_single_scale, boundary_edge02]
    simp [chainCoeff, vertex, edge01, edge02, edge12, edge13, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge03 a)) (vertex 1) = _
    rw [boundary_single_scale, boundary_edge03]
    simp [chainCoeff, vertex, edge01, edge03, edge12, edge13, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge12 a)) (vertex 1) = _
    rw [boundary_single_scale, boundary_edge12]
    simp [chainCoeff, vertex, edge01, edge12, edge13, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge13 a)) (vertex 1) = _
    rw [boundary_single_scale, boundary_edge13]
    simp [chainCoeff, vertex, edge01, edge12, edge13, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge23 a)) (vertex 1) = _
    rw [boundary_single_scale, boundary_edge23]
    simp [chainCoeff, vertex, edge01, edge12, edge13, edge23, Finset.ext_iff, Fin.forall_fin_succ]

private theorem boundaryCoeff_vertex2 (k : Type u) [Field k] :
    (chainCoeff k 0 (vertex 2)).comp (boundary boundaryTetrahedron.toPre k 0) =
      chainCoeff k 1 edge02 + chainCoeff k 1 edge12 - chainCoeff k 1 edge23 := by
  apply Finsupp.lhom_ext
  intro e a
  rcases edge_cases e with h | h | h | h | h | h
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge01 a)) (vertex 2) = _
    rw [boundary_single_scale, boundary_edge01]
    simp [chainCoeff, vertex, edge01, edge02, edge12, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge02 a)) (vertex 2) = _
    rw [boundary_single_scale, boundary_edge02]
    simp [chainCoeff, vertex, edge02, edge12, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge03 a)) (vertex 2) = _
    rw [boundary_single_scale, boundary_edge03]
    simp [chainCoeff, vertex, edge02, edge03, edge12, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge12 a)) (vertex 2) = _
    rw [boundary_single_scale, boundary_edge12]
    simp [chainCoeff, vertex, edge02, edge12, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge13 a)) (vertex 2) = _
    rw [boundary_single_scale, boundary_edge13]
    simp [chainCoeff, vertex, edge02, edge12, edge13, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge23 a)) (vertex 2) = _
    rw [boundary_single_scale, boundary_edge23]
    simp [chainCoeff, vertex, edge02, edge12, edge23, Finset.ext_iff, Fin.forall_fin_succ]

private theorem boundaryCoeff_vertex3 (k : Type u) [Field k] :
    (chainCoeff k 0 (vertex 3)).comp (boundary boundaryTetrahedron.toPre k 0) =
      chainCoeff k 1 edge03 + chainCoeff k 1 edge13 + chainCoeff k 1 edge23 := by
  apply Finsupp.lhom_ext
  intro e a
  rcases edge_cases e with h | h | h | h | h | h
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge01 a)) (vertex 3) = _
    rw [boundary_single_scale, boundary_edge01]
    simp [chainCoeff, vertex, edge01, edge03, edge13, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge02 a)) (vertex 3) = _
    rw [boundary_single_scale, boundary_edge02]
    simp [chainCoeff, vertex, edge02, edge03, edge13, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge03 a)) (vertex 3) = _
    rw [boundary_single_scale, boundary_edge03]
    simp [chainCoeff, vertex, edge03, edge13, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge12 a)) (vertex 3) = _
    rw [boundary_single_scale, boundary_edge12]
    simp [chainCoeff, vertex, edge03, edge12, edge13, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge13 a)) (vertex 3) = _
    rw [boundary_single_scale, boundary_edge13]
    simp [chainCoeff, vertex, edge03, edge13, edge23, Finset.ext_iff, Fin.forall_fin_succ]
  · subst e
    change (boundary boundaryTetrahedron.toPre k 0 (Finsupp.single edge23 a)) (vertex 3) = _
    rw [boundary_single_scale, boundary_edge23]
    simp [chainCoeff, vertex, edge03, edge13, edge23, Finset.ext_iff, Fin.forall_fin_succ]

private noncomputable def alpha (k : Type u) [Field k] : Chain boundaryTetrahedron.toPre k 1 :=
  Finsupp.single edge01 1 - Finsupp.single edge02 1 + Finsupp.single edge12 1

private noncomputable def beta (k : Type u) [Field k] : Chain boundaryTetrahedron.toPre k 1 :=
  Finsupp.single edge01 1 - Finsupp.single edge03 1 + Finsupp.single edge13 1

private noncomputable def gamma (k : Type u) [Field k] : Chain boundaryTetrahedron.toPre k 1 :=
  Finsupp.single edge02 1 - Finsupp.single edge03 1 + Finsupp.single edge23 1

private noncomputable def delta (k : Type u) [Field k] : Chain boundaryTetrahedron.toPre k 1 :=
  Finsupp.single edge12 1 - Finsupp.single edge13 1 + Finsupp.single edge23 1

private theorem boundary_alpha (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (alpha k) = 0 := by
  simp only [alpha, map_sub, map_add]
  rw [boundary_edge01, boundary_edge02, boundary_edge12]
  abel

private theorem boundary_beta (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (beta k) = 0 := by
  simp only [beta, map_sub, map_add]
  rw [boundary_edge01, boundary_edge03, boundary_edge13]
  abel

private theorem boundary_gamma (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (gamma k) = 0 := by
  simp only [gamma, map_sub, map_add]
  rw [boundary_edge02, boundary_edge03, boundary_edge23]
  abel

private theorem boundary_delta (k : Type u) [Field k] :
    boundary boundaryTetrahedron.toPre k 0 (delta k) = 0 := by
  simp only [delta, map_sub, map_add]
  rw [boundary_edge12, boundary_edge13, boundary_edge23]
  abel


private theorem ambient_cycle_normalForm (k : Type u) [Field k]
    (z : Chain boundaryTetrahedron.toPre k 1)
    (hz : boundary boundaryTetrahedron.toPre k 0 z = 0) :
    z = z edge12 • alpha k + z edge13 • beta k + z edge23 • gamma k := by
  have h1 : z edge01 - z edge12 - z edge13 = 0 := by
    have he := congrArg (fun f => f z) (boundaryCoeff_vertex1 k)
    simpa [chainCoeff, hz] using he.symm
  have h2 : z edge02 + z edge12 - z edge23 = 0 := by
    have he := congrArg (fun f => f z) (boundaryCoeff_vertex2 k)
    simpa [chainCoeff, hz] using he.symm
  have h3 : z edge03 + z edge13 + z edge23 = 0 := by
    have he := congrArg (fun f => f z) (boundaryCoeff_vertex3 k)
    simpa [chainCoeff, hz] using he.symm
  simp only [edge01, edge02, edge03, edge12, edge13, edge23] at h1 h2 h3
  ext e
  rcases edge_cases e with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [alpha, beta, gamma, edge01, edge02, edge03, edge12, edge13, edge23,
      Finset.ext_iff, Fin.forall_fin_succ]
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3

private theorem ambient_cycle_coeff01 (k : Type u) [Field k]
    (z : Chain boundaryTetrahedron.toPre k 1)
    (hz : boundary boundaryTetrahedron.toPre k 0 z = 0) :
    z edge01 = z edge12 + z edge13 := by
  have he := congrArg (fun f => f z) (boundaryCoeff_vertex1 k)
  have hh : z edge01 - z edge12 - z edge13 = 0 := by
    simpa [chainCoeff, hz] using he.symm
  linear_combination hh

open RankResolutionDegreeTwo
open CategoryTheory Module
open scoped Classical

private noncomputable abbrev stage (p : grid.Point) :=
  boundaryTetrahedronGrading.sublevel (grid.embedding p)

private theorem stage_le (p : grid.Point) : stage p ≤ boundaryTetrahedron.toPre :=
  boundaryTetrahedronGrading.sublevel_le _

private theorem faceIncl_inj {K L : PreAbstractSimplicialComplex (Fin 4)}
    (h : K ≤ L) (n : ℕ) : Function.Injective (faceIncl h n) := by
  intro s t he
  exact Subtype.ext (congrArg (fun x : Face L n => x.val) he)

private theorem chainIncl_inj (k : Type u) [Field k]
    {K L : PreAbstractSimplicialComplex (Fin 4)} (h : K ≤ L) (n : ℕ) :
    Function.Injective (chainIncl k h n) :=
  Finsupp.mapDomain_injective (faceIncl_inj h n)

private noncomputable def ambientCycle (k : Type u) [Field k] (p : grid.Point)
    (z : simplicialCycles (stage p) k 1) : Chain boundaryTetrahedron.toPre k 1 :=
  chainIncl k (stage_le p) 1 z

private theorem ambientCycle_boundary (k : Type u) [Field k] (p : grid.Point)
    (z : simplicialCycles (stage p) k 1) :
    boundary boundaryTetrahedron.toPre k 0 (ambientCycle k p z) = 0 := by
  have hz : boundary (stage p) k 0 (z : Chain (stage p) k 1) = 0 := by
    simpa only [simplicialCycles_succ, LinearMap.mem_ker] using z.property
  have he := congrArg (fun f => f (z : Chain (stage p) k 1))
    (boundary_chainIncl k (stage_le p) 0)
  simpa [ambientCycle, hz] using he

private theorem ambientCycle_missing (k : Type u) [Field k] (p : grid.Point)
    (z : simplicialCycles (stage p) k 1) (e : Face boundaryTetrahedron.toPre 1)
    (he : e.val ∉ stage p) : ambientCycle k p z e = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨s, hs⟩
  apply he
  exact hs ▸ s.property.1

private noncomputable def stageSingle (k : Type u) [Field k] (p : grid.Point)
    (n : ℕ) (e : Face boundaryTetrahedron.toPre n) (v : k) : Chain (stage p) k n :=
  if he : e.val ∈ stage p then Finsupp.single ⟨e.val, he, e.property.2⟩ v else 0

private theorem stageSingle_incl (k : Type u) [Field k] (p : grid.Point)
    (n : ℕ) (e : Face boundaryTetrahedron.toPre n) (v : k)
    (hv : e.val ∉ stage p → v = 0) :
    chainIncl k (stage_le p) n (stageSingle k p n e v) = Finsupp.single e v := by
  unfold stageSingle
  split_ifs with he
  · rw [chainIncl_single]
    rfl
  · simp [hv he]

private theorem stage_boundary_of_ambient (k : Type u) [Field k] (p : grid.Point)
    (z : simplicialCycles (stage p) k 1) (w : Chain (stage p) k 2)
    (hw : boundary boundaryTetrahedron.toPre k 1
      (chainIncl k (stage_le p) 2 w) = ambientCycle k p z) :
    z ∈ simplicialBoundaries (stage p) k 1 := by
  apply (mem_simplicialBoundaries_iff k (stage p) 1 z).mpr
  refine ⟨w, chainIncl_inj k (stage_le p) 1 ?_⟩
  have he := congrArg (fun f => f w) (boundary_chainIncl k (stage_le p) 1)
  exact he.symm.trans hw


private theorem coord_cases (p : grid.Point) (i : Fin 2) :
    (p i).val = 0 ∨ (p i).val = 1 ∨ (p i).val = 2 := by
  simpa only [grid, gridValues, Finset.mem_insert, Finset.mem_singleton] using (p i).property

private theorem coord_nonneg (p : grid.Point) (i : Fin 2) : 0 ≤ (p i).val := by
  rcases coord_cases p i with hh | hh | hh <;> rw [hh] <;> norm_num

private theorem stage_face_iff (p : grid.Point) (n : ℕ)
    (s : Face boundaryTetrahedron.toPre n) :
    s.val ∈ stage p ↔
      (faceGradeNat ⟨s.val, s.property.1⟩ 0 : ℝ) ≤ (p 0).val ∧
      (faceGradeNat ⟨s.val, s.property.1⟩ 1 : ℝ) ≤ (p 1).val := by
  change (∃ hs : s.val ∈ boundaryTetrahedron.toPre,
    boundaryTetrahedronGrading.grade ⟨s.val, hs⟩ ≤ grid.embedding p) ↔ _
  simp [boundaryTetrahedronGrading, CoordinateGrid.embedding_apply,
    Pi.le_def, Fin.forall_fin_succ, s.property.1]

private theorem stage_edge01 (p : grid.Point) : edge01.val ∈ stage p := by
  rw [stage_face_iff]
  simpa [faceGradeNat, faceGradeX, faceGradeY, edge01, Finset.subset_iff,
    Fin.forall_fin_succ] using And.intro (coord_nonneg p 0) (coord_nonneg p 1)

private theorem stage_edge02 (p : grid.Point) : edge02.val ∈ stage p ↔ 1 ≤ (p 1).val := by
  rw [stage_face_iff]
  simp [faceGradeNat, faceGradeX, faceGradeY, edge02, Finset.subset_iff, coord_nonneg]

private theorem stage_edge12 (p : grid.Point) : edge12.val ∈ stage p ↔ 1 ≤ (p 1).val := by
  rw [stage_face_iff]
  simp [faceGradeNat, faceGradeX, faceGradeY, edge12, Finset.subset_iff, coord_nonneg]

private theorem stage_edge03 (p : grid.Point) : edge03.val ∈ stage p ↔ 1 ≤ (p 0).val := by
  rw [stage_face_iff]
  simp [faceGradeNat, faceGradeX, faceGradeY, edge03, Finset.subset_iff, coord_nonneg]

private theorem stage_edge13 (p : grid.Point) : edge13.val ∈ stage p ↔ 1 ≤ (p 0).val := by
  rw [stage_face_iff]
  simp [faceGradeNat, faceGradeX, faceGradeY, edge13, Finset.subset_iff, coord_nonneg]

private theorem stage_edge23 (p : grid.Point) : edge23.val ∈ stage p ↔
    1 ≤ (p 0).val ∧ 1 ≤ (p 1).val := by
  rw [stage_face_iff]
  simp [faceGradeNat, faceGradeX, faceGradeY, edge23, Finset.subset_iff]

private theorem stage_triangle012 (p : grid.Point) : triangle012.val ∈ stage p ↔
    2 ≤ (p 1).val := by
  rw [stage_face_iff]
  simp [faceGradeNat, faceGradeX, faceGradeY, triangle012, Finset.subset_iff, coord_nonneg]

private theorem stage_triangle013 (p : grid.Point) : triangle013.val ∈ stage p ↔
    2 ≤ (p 0).val := by
  rw [stage_face_iff]
  simp [faceGradeNat, faceGradeX, faceGradeY, triangle013, Finset.subset_iff, coord_nonneg]

private theorem stage_triangle023 (p : grid.Point) : triangle023.val ∈ stage p ↔
    1 ≤ (p 0).val ∧ 1 ≤ (p 1).val := by
  rw [stage_face_iff]
  simp [faceGradeNat, faceGradeX, faceGradeY, triangle023, Finset.subset_iff]

private theorem stage_triangle123 (p : grid.Point) : triangle123.val ∈ stage p ↔
    1 ≤ (p 0).val ∧ 1 ≤ (p 1).val := by
  rw [stage_face_iff]
  simp [faceGradeNat, faceGradeX, faceGradeY, triangle123, Finset.subset_iff]

private theorem fill_boundary (k : Type u) [Field k] (p : grid.Point)
    (z : simplicialCycles (stage p) k 1) (A B C D : k)
    (hA : triangle012.val ∉ stage p → A = 0)
    (hB : triangle013.val ∉ stage p → B = 0)
    (hC : triangle023.val ∉ stage p → C = 0)
    (hD : triangle123.val ∉ stage p → D = 0)
    (hz : ambientCycle k p z =
      A • alpha k + B • beta k + C • gamma k + D • delta k) :
    z ∈ simplicialBoundaries (stage p) k 1 := by
  apply stage_boundary_of_ambient k p z
    (stageSingle k p 2 triangle012 A + stageSingle k p 2 triangle013 B +
      stageSingle k p 2 triangle023 C + stageSingle k p 2 triangle123 D)
  simp only [map_add, stageSingle_incl k p 2 triangle012 A hA,
    stageSingle_incl k p 2 triangle013 B hB,
    stageSingle_incl k p 2 triangle023 C hC,
    stageSingle_incl k p 2 triangle123 D hD]
  have hs (e : Face boundaryTetrahedron.toPre 2) (v : k) :
      Finsupp.single e v = v • Finsupp.single e (1 : k) := by simp
  rw [hs triangle012, hs triangle013, hs triangle023, hs triangle123]
  simp only [map_smul, boundary_triangle012, boundary_triangle013,
    boundary_triangle023, boundary_triangle123]
  exact hz.symm


private def stagePoint (i j : Fin 3) : grid.Point := fun t =>
  if h : t.val = 0 then ⟨(i.val : ℝ), by fin_cases i <;> norm_num [grid, gridValues]⟩
  else ⟨(j.val : ℝ), by fin_cases j <;> norm_num [grid, gridValues]⟩

private theorem support_bounds (p : grid.Point) : p ∈ RankResolutionDegreeTwo.support ↔
    (1 ≤ (p 1).val ∨ 1 ≤ (p 0).val) ∧ (p 0).val ≤ 1 ∧ (p 1).val ≤ 1 := by
  have ha : a ≤ p ↔ 1 ≤ (p 1).val := by
    change stagePoint 0 1 ≤ p ↔ _
    simp [Pi.le_def, Fin.forall_fin_succ, stagePoint]
    change (0 ≤ (p 0).val ∧ 1 ≤ (p 1).val) ↔ _
    simp [coord_nonneg]
  have hb : b ≤ p ↔ 1 ≤ (p 0).val := by
    change stagePoint 1 0 ≤ p ↔ _
    simp [Pi.le_def, Fin.forall_fin_succ, stagePoint]
    change (1 ≤ (p 0).val ∧ 0 ≤ (p 1).val) ↔ _
    simp [coord_nonneg]
  have hc : p ≤ c ↔ (p 0).val ≤ 1 ∧ (p 1).val ≤ 1 := by
    change p ≤ stagePoint 1 1 ↔ _
    simp [Pi.le_def, Fin.forall_fin_succ, stagePoint]
    rfl
  change ((a ≤ p ∨ b ≤ p) ∧ p ≤ c) ↔ _
  rw [ha, hb, hc]

private noncomputable def cycleCoefficient (k : Type u) [Field k] (p : grid.Point) :
    simplicialCycles (stage p) k 1 →ₗ[k] SupportInterval.fiber (k := k) RankResolutionDegreeTwo.support p where
  toFun z := ⟨if p ∈ RankResolutionDegreeTwo.support then ambientCycle k p z edge01 else 0, by
    by_cases hp : p ∈ RankResolutionDegreeTwo.support
    · simp only [SupportInterval.fiber, if_pos hp, Submodule.mem_top]
    · simp only [SupportInterval.fiber, if_neg hp, Submodule.mem_bot]⟩
  map_add' z w := by
    apply Subtype.ext
    by_cases hp : p ∈ RankResolutionDegreeTwo.support <;> simp [hp, ambientCycle]
  map_smul' v z := by
    apply Subtype.ext
    by_cases hp : p ∈ RankResolutionDegreeTwo.support <;> simp [hp, ambientCycle]

private theorem cycleCoefficient_val (k : Type u) [Field k] (p : grid.Point)
    (z : simplicialCycles (stage p) k 1) :
    (cycleCoefficient k p z : k) =
      if p ∈ RankResolutionDegreeTwo.support then ambientCycle k p z edge01 else 0 := rfl

private theorem ambientChain_missing (k : Type u) [Field k] (p : grid.Point)
    (n : ℕ) (z : Chain (stage p) k n) (e : Face boundaryTetrahedron.toPre n)
    (he : e.val ∉ stage p) : chainIncl k (stage_le p) n z e = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨s, hs⟩
  apply he
  exact hs ▸ s.property.1

private theorem triangle_cases (s : Face boundaryTetrahedron.toPre 2) :
    s = triangle012 ∨ s = triangle013 ∨ s = triangle023 ∨ s = triangle123 := by
  obtain ⟨i, j, l, hij, hil, hjl, hval⟩ := Finset.card_eq_three.mp s.property.2
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals
    first
    | exact Or.inl (Subtype.ext (by rw [hval]; decide))
    | exact Or.inr (Or.inl (Subtype.ext (by rw [hval]; decide)))
    | exact Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [hval]; decide))))
    | exact Or.inr (Or.inr (Or.inr (Subtype.ext (by rw [hval]; decide))))
    | simp_all

private theorem boundaryCoeff_edge01 (k : Type u) [Field k] :
    (chainCoeff k 1 edge01).comp (boundary boundaryTetrahedron.toPre k 1) =
      chainCoeff k 2 triangle012 + chainCoeff k 2 triangle013 := by
  apply Finsupp.lhom_ext
  intro s v
  have hs (e : Face boundaryTetrahedron.toPre 2) :
      Finsupp.single e v = v • Finsupp.single e (1 : k) := by simp
  rcases triangle_cases s with rfl | rfl | rfl | rfl
  all_goals
    change (boundary boundaryTetrahedron.toPre k 1 _) edge01 = _
    rw [hs, map_smul]
    first | rw [boundary_triangle012] | rw [boundary_triangle013]
          | rw [boundary_triangle023] | rw [boundary_triangle123]
    simp [chainCoeff, edge01, edge02, edge03, edge12, edge13,
      edge23, triangle012, triangle013, triangle023, triangle123,
      Finset.ext_iff, Fin.forall_fin_succ]

private theorem boundaries_le_coefficient_ker (k : Type u) [Field k] (p : grid.Point) :
    simplicialBoundaries (stage p) k 1 ≤ LinearMap.ker (cycleCoefficient k p) := by
  intro z hz
  obtain ⟨w, hw⟩ := (mem_simplicialBoundaries_iff k (stage p) 1 z).mp hz
  apply Subtype.ext
  change (if p ∈ RankResolutionDegreeTwo.support then ambientCycle k p z edge01 else 0) = 0
  by_cases hp : p ∈ RankResolutionDegreeTwo.support
  · rw [if_pos hp]
    have hp' := (support_bounds p).mp hp
    have h012 : triangle012.val ∉ stage p := by
      rw [stage_triangle012]
      linarith [hp'.2.2]
    have h013 : triangle013.val ∉ stage p := by
      rw [stage_triangle013]
      linarith [hp'.2.1]
    have he := congrArg (fun f => f w) (boundary_chainIncl k (stage_le p) 1)
    simp only [LinearMap.comp_apply] at he
    rw [hw] at he
    change _ = ambientCycle k p z at he
    rw [← he]
    change (chainCoeff k 1 edge01)
      (boundary boundaryTetrahedron.toPre k 1 (chainIncl k (stage_le p) 2 w)) = 0
    rw [← LinearMap.comp_apply, boundaryCoeff_edge01]
    change chainIncl k (stage_le p) 2 w triangle012 +
      chainIncl k (stage_le p) 2 w triangle013 = 0
    rw [ambientChain_missing k p 2 w triangle012 h012,
      ambientChain_missing k p 2 w triangle013 h013, add_zero]
  · simp [hp]


private theorem coefficient_ker_le_boundaries (k : Type u) [Field k] (p : grid.Point) :
    LinearMap.ker (cycleCoefficient k p) ≤ simplicialBoundaries (stage p) k 1 := by
  intro z hz
  let r : k := ambientCycle k p z edge12
  let s : k := ambientCycle k p z edge13
  let t : k := ambientCycle k p z edge23
  have hn : ambientCycle k p z = r • alpha k + s • beta k + t • gamma k :=
    ambient_cycle_normalForm k _ (ambientCycle_boundary k p z)
  have hd : delta k = alpha k - beta k + gamma k := by
    unfold delta alpha beta gamma
    abel
  have hr : (p 1).val = 0 → r = 0 := by
    intro hy
    apply ambientCycle_missing k p z edge12
    simp [stage_edge12, hy]
  have hs : (p 0).val = 0 → s = 0 := by
    intro hx
    apply ambientCycle_missing k p z edge13
    simp [stage_edge13, hx]
  have ht : (p 0).val = 0 ∨ (p 1).val = 0 → t = 0 := by
    intro hh
    apply ambientCycle_missing k p z edge23
    rcases hh with hh | hh <;> simp [stage_edge23, hh]
  have hsum : p ∈ RankResolutionDegreeTwo.support → r + s = 0 := by
    intro hp
    have hv := congrArg (fun x : SupportInterval.fiber (k := k)
      RankResolutionDegreeTwo.support p => (x : k)) hz
    change (if p ∈ RankResolutionDegreeTwo.support then ambientCycle k p z edge01 else 0) = 0 at hv
    rw [if_pos hp] at hv
    exact (ambient_cycle_coeff01 k _ (ambientCycle_boundary k p z)).symm.trans hv
  rcases coord_cases p 0 with hx | hx | hx <;>
    rcases coord_cases p 1 with hy | hy | hy
  -- o = (0,0): no cycles.
  · have hr0 := hr hy
    have hs0 := hs hx
    have ht0 := ht (Or.inl hx)
    apply fill_boundary k p z (0) (0) (0) (0)
    all_goals try { intro hh; simp_all [stage_triangle012, stage_triangle013, stage_triangle023, stage_triangle123] }
    rw [hn, hd]
    simp only [hr0, hs0, ht0]
    module
  -- a = (0,1): coefficient evaluation is injective.
  · have hs0 := hs hx
    have ht0 := ht (Or.inl hx)
    have hsum0 := hsum (by rw [support_bounds]; norm_num [hx, hy])
    have hr0 : r = 0 := by simpa [hs0] using hsum0
    apply fill_boundary k p z (0) (0) (0) (0)
    all_goals try { intro hh; simp_all [stage_triangle012, stage_triangle013, stage_triangle023, stage_triangle123] }
    rw [hn, hd]
    simp only [hr0, hs0, ht0]
    module
  -- d = (0,2): the 012 cap fills the sole cycle.
  · have hs0 := hs hx
    have ht0 := ht (Or.inl hx)
    apply fill_boundary k p z (r) (0) (0) (0)
    all_goals try { intro hh; simp_all [stage_triangle012, stage_triangle013, stage_triangle023, stage_triangle123] }
    rw [hn, hd]
    simp only [hs0, ht0]
    module
  -- b = (1,0): coefficient evaluation is injective.
  · have hr0 := hr hy
    have ht0 := ht (Or.inr hy)
    have hsum0 := hsum (by rw [support_bounds]; norm_num [hx, hy])
    have hs0 : s = 0 := by simpa [hr0] using hsum0
    apply fill_boundary k p z (0) (0) (0) (0)
    all_goals try { intro hh; simp_all [stage_triangle012, stage_triangle013, stage_triangle023, stage_triangle123] }
    rw [hn, hd]
    simp only [hr0, hs0, ht0]
    module
  -- c = (1,1): r[123] + (t-r)[023] fills the coefficient kernel.
  · have hsum0 := hsum (by rw [support_bounds]; norm_num [hx, hy])
    have hs0 : s = -r := by linear_combination hsum0
    apply fill_boundary k p z (0) (0) (t - r) (r)
    all_goals try { intro hh; simp_all [stage_triangle012, stage_triangle013, stage_triangle023, stage_triangle123] }
    rw [hn, hd]
    simp only [hs0]
    module
  -- f = (1,2): (r+s)[012] - s[123] + (t+s)[023] fills every cycle.
  · apply fill_boundary k p z (r + s) (0) (t + s) (-s)
    all_goals try { intro hh; simp_all [stage_triangle012, stage_triangle013, stage_triangle023, stage_triangle123] }
    rw [hn, hd]
    module
  -- e = (2,0): the 013 cap fills the sole cycle.
  · have hr0 := hr hy
    have ht0 := ht (Or.inr hy)
    apply fill_boundary k p z (0) (s) (0) (0)
    all_goals try { intro hh; simp_all [stage_triangle012, stage_triangle013, stage_triangle023, stage_triangle123] }
    rw [hn, hd]
    simp only [hr0, ht0]
    module
  -- g = (2,1): (r+s)[013] + r[123] + (t-r)[023] fills every cycle.
  · apply fill_boundary k p z (0) (r + s) (t - r) (r)
    all_goals try { intro hh; simp_all [stage_triangle012, stage_triangle013, stage_triangle023, stage_triangle123] }
    rw [hn, hd]
    module
  -- h = (2,2): the same filling as at f is available.
  · apply fill_boundary k p z (r + s) (0) (t + s) (-s)
    all_goals try { intro hh; simp_all [stage_triangle012, stage_triangle013, stage_triangle023, stage_triangle123] }
    rw [hn, hd]
    module

private theorem boundaries_eq_coefficient_ker (k : Type u) [Field k] (p : grid.Point) :
    simplicialBoundaries (stage p) k 1 = LinearMap.ker (cycleCoefficient k p) :=
  le_antisymm (boundaries_le_coefficient_ker k p) (coefficient_ker_le_boundaries k p)


private noncomputable def alphaChain (k : Type u) [Field k] (p : grid.Point) :
    Chain (stage p) k 1 :=
  stageSingle k p 1 edge01 1 - stageSingle k p 1 edge02 1 + stageSingle k p 1 edge12 1

private theorem alphaChain_incl (k : Type u) [Field k] (p : grid.Point)
    (hy : 1 ≤ (p 1).val) : chainIncl k (stage_le p) 1 (alphaChain k p) = alpha k := by
  have h01 : edge01.val ∉ stage p → (1 : k) = 0 := fun hh => (hh (stage_edge01 p)).elim
  have h02 : edge02.val ∉ stage p → (1 : k) = 0 :=
    fun hh => (hh ((stage_edge02 p).mpr hy)).elim
  have h12 : edge12.val ∉ stage p → (1 : k) = 0 :=
    fun hh => (hh ((stage_edge12 p).mpr hy)).elim
  simp only [alphaChain, map_add, map_sub, stageSingle_incl k p 1 edge01 1 h01,
    stageSingle_incl k p 1 edge02 1 h02, stageSingle_incl k p 1 edge12 1 h12]
  rfl

private noncomputable def betaChain (k : Type u) [Field k] (p : grid.Point) :
    Chain (stage p) k 1 :=
  stageSingle k p 1 edge01 1 - stageSingle k p 1 edge03 1 + stageSingle k p 1 edge13 1

private theorem betaChain_incl (k : Type u) [Field k] (p : grid.Point)
    (hx : 1 ≤ (p 0).val) : chainIncl k (stage_le p) 1 (betaChain k p) = beta k := by
  have h01 : edge01.val ∉ stage p → (1 : k) = 0 := fun hh => (hh (stage_edge01 p)).elim
  have h03 : edge03.val ∉ stage p → (1 : k) = 0 :=
    fun hh => (hh ((stage_edge03 p).mpr hx)).elim
  have h13 : edge13.val ∉ stage p → (1 : k) = 0 :=
    fun hh => (hh ((stage_edge13 p).mpr hx)).elim
  simp only [betaChain, map_add, map_sub, stageSingle_incl k p 1 edge01 1 h01,
    stageSingle_incl k p 1 edge03 1 h03, stageSingle_incl k p 1 edge13 1 h13]
  rfl

private noncomputable def cycleFromAmbient (k : Type u) [Field k] (p : grid.Point)
    (w : Chain (stage p) k 1)
    (hw : boundary boundaryTetrahedron.toPre k 0 (chainIncl k (stage_le p) 1 w) = 0) :
    simplicialCycles (stage p) k 1 :=
  ⟨w, by
    rw [simplicialCycles_succ]
    change boundary (stage p) k 0 w = 0
    apply chainIncl_inj k (stage_le p) 0
    rw [map_zero]
    have he := congrArg (fun f => f w) (boundary_chainIncl k (stage_le p) 0)
    exact he.symm.trans hw⟩

private noncomputable def alphaCycle (k : Type u) [Field k] (p : grid.Point)
    (hy : 1 ≤ (p 1).val) : simplicialCycles (stage p) k 1 :=
  cycleFromAmbient k p (alphaChain k p) (by rw [alphaChain_incl k p hy]; exact boundary_alpha k)

private noncomputable def betaCycle (k : Type u) [Field k] (p : grid.Point)
    (hx : 1 ≤ (p 0).val) : simplicialCycles (stage p) k 1 :=
  cycleFromAmbient k p (betaChain k p) (by rw [betaChain_incl k p hx]; exact boundary_beta k)

private theorem cycleCoefficient_surjective (k : Type u) [Field k] (p : grid.Point) :
    Function.Surjective (cycleCoefficient k p) := by
  intro x
  by_cases hp : p ∈ RankResolutionDegreeTwo.support
  · rcases ((support_bounds p).mp hp).1 with hy | hx
    · refine ⟨(x : k) • alphaCycle k p hy, Subtype.ext ?_⟩
      rw [cycleCoefficient_val, if_pos hp]
      change (chainIncl k (stage_le p) 1 ((x : k) • alphaChain k p)) edge01 = (x : k)
      rw [map_smul, alphaChain_incl k p hy]
      simp [alpha, edge01, edge02, edge12, Finset.ext_iff, Fin.forall_fin_succ]
    · refine ⟨(x : k) • betaCycle k p hx, Subtype.ext ?_⟩
      rw [cycleCoefficient_val, if_pos hp]
      change (chainIncl k (stage_le p) 1 ((x : k) • betaChain k p)) edge01 = (x : k)
      rw [map_smul, betaChain_incl k p hx]
      simp [beta, edge01, edge03, edge13, Finset.ext_iff, Fin.forall_fin_succ]
  · refine ⟨0, Subtype.ext ?_⟩
    rw [SupportInterval.val_eq_zero RankResolutionDegreeTwo.support hp x]
    simp


private theorem stage_mono {p q : grid.Point} (hpq : p ≤ q) : stage p ≤ stage q :=
  boundaryTetrahedronGrading.sublevel_mono (grid.embedding.monotone hpq)

private theorem ambientCycle_incl (k : Type u) [Field k] {p q : grid.Point}
    (hpq : p ≤ q) (z : simplicialCycles (stage p) k 1) :
    ambientCycle k q (simplicialCycleIncl k (stage_mono hpq) 1 z) =
      ambientCycle k p z := by
  unfold ambientCycle
  rw [simplicialCycleIncl_coe]
  exact (congrArg (fun f => f (z : Chain (stage p) k 1))
    (chainIncl_comp k (stage_mono hpq) (stage_le q) 1)).symm

private theorem ambientCycle_origin (k : Type u) [Field k] (p : grid.Point)
    (hx : (p 0).val = 0) (hy : (p 1).val = 0)
    (z : simplicialCycles (stage p) k 1) : ambientCycle k p z = 0 := by
  have hr := ambientCycle_missing k p z edge12 (by simp [stage_edge12, hy])
  have hs := ambientCycle_missing k p z edge13 (by simp [stage_edge13, hx])
  have ht := ambientCycle_missing k p z edge23 (by simp [stage_edge23, hx])
  rw [ambient_cycle_normalForm k _ (ambientCycle_boundary k p z), hr, hs, ht]
  simp

private theorem off_support_before_support {p q : grid.Point} (hpq : p ≤ q)
    (hp : p ∉ RankResolutionDegreeTwo.support) (hq : q ∈ RankResolutionDegreeTwo.support) :
    (p 0).val = 0 ∧ (p 1).val = 0 := by
  have hq' := (support_bounds q).mp hq
  have hx : (p 0).val ≤ 1 := (show (p 0).val ≤ (q 0).val from hpq 0).trans hq'.2.1
  have hy : (p 1).val ≤ 1 := (show (p 1).val ≤ (q 1).val from hpq 1).trans hq'.2.2
  have hn : ¬ (1 ≤ (p 1).val ∨ 1 ≤ (p 0).val) := by
    intro hh
    exact hp ((support_bounds p).mpr ⟨hh, hx, hy⟩)
  constructor
  · rcases coord_cases p 0 with hh | hh | hh
    · exact hh
    · exact (hn (Or.inr (by rw [hh]))).elim
    · linarith
  · rcases coord_cases p 1 with hh | hh | hh
    · exact hh
    · exact (hn (Or.inl (by rw [hh]))).elim
    · linarith

private theorem cycleCoefficient_naturality (k : Type u) [Field k] {p q : grid.Point}
    (hpq : p ≤ q) (z : simplicialCycles (stage p) k 1) :
    cycleCoefficient k q (simplicialCycleIncl k (stage_mono hpq) 1 z) =
      structureMapLinear (finiteModule (k := k)) hpq (cycleCoefficient k p z) := by
  apply Subtype.ext
  rw [cycleCoefficient_val, SupportInterval.structureMap_val, cycleCoefficient_val]
  by_cases hq : q ∈ RankResolutionDegreeTwo.support
  · rw [if_pos hq, if_pos hq, ambientCycle_incl k hpq z]
    by_cases hp : p ∈ RankResolutionDegreeTwo.support
    · rw [if_pos hp]
    · rw [if_neg hp]
      obtain ⟨hx, hy⟩ := off_support_before_support hpq hp hq
      rw [ambientCycle_origin k p hx hy z]
      rfl
  · simp [hq]

private noncomputable local instance cyclesQuotient (k : Type u) [Field k] (p : grid.Point) :
    HasQuotient (simplicialCycles (stage p) k 1)
      (Submodule k (simplicialCycles (stage p) k 1)) :=
  Submodule.hasQuotient (R := k) (M := simplicialCycles (stage p) k 1)

private noncomputable def quotientEquiv (k : Type u) [Field k] (p : grid.Point) :
    (simplicialCycles (stage p) k 1 ⧸ simplicialBoundaries (stage p) k 1) ≃ₗ[k]
      SupportInterval.fiber (k := k) RankResolutionDegreeTwo.support p :=
  (Submodule.quotEquivOfEq _ _ (boundaries_eq_coefficient_ker k p)).trans
    ((cycleCoefficient k p).quotKerEquivOfSurjective (cycleCoefficient_surjective k p))

private theorem quotientEquiv_mk (k : Type u) [Field k] (p : grid.Point)
    (z : simplicialCycles (stage p) k 1) :
    quotientEquiv k p (Submodule.mkQ (R := k) (M := simplicialCycles (stage p) k 1)
      (simplicialBoundaries (stage p) k 1) z) =
      cycleCoefficient k p z := by
  simp only [quotientEquiv, LinearEquiv.trans_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

private noncomputable def homologyEquiv (k : Type u) [Field k] (p : grid.Point) :
    simplicialHomology (stage p) k 1 ≃ₗ[k]
      SupportInterval.fiber (k := k) RankResolutionDegreeTwo.support p :=
  (homologyKernelQuotient.{u,0,u} k (simplicialChainComplex (stage p) k) 1).toLinearEquiv.trans
    (quotientEquiv k p)

private theorem homologyEquiv_naturality (k : Type u) [Field k] {p q : grid.Point}
    (hpq : p ≤ q) (x : simplicialHomology (stage p) k 1) :
    homologyEquiv k q ((simplicialHomologyIncl k (stage_mono hpq) 1).hom x) =
      structureMapLinear (finiteModule (k := k)) hpq (homologyEquiv k p x) := by
  have hn := congrArg (fun f => f.hom x)
    (simplicialHomologyIncl_quotient_naturality k (stage_mono hpq) 1)
  change (homologyKernelQuotient.{u,0,u} k (simplicialChainComplex (stage q) k) 1).hom.hom
      ((simplicialHomologyIncl k (stage_mono hpq) 1).hom x) =
    simplicialQuotientIncl k (stage_mono hpq) 1
      ((homologyKernelQuotient.{u,0,u} k (simplicialChainComplex (stage p) k) 1).hom.hom x) at hn
  change quotientEquiv k q
    ((homologyKernelQuotient.{u,0,u} k (simplicialChainComplex (stage q) k) 1).hom.hom
      ((simplicialHomologyIncl k (stage_mono hpq) 1).hom x)) =
    structureMapLinear (finiteModule (k := k)) hpq (quotientEquiv k p
      ((homologyKernelQuotient.{u,0,u} k (simplicialChainComplex (stage p) k) 1).hom.hom x))
  rw [hn]
  generalize (homologyKernelQuotient.{u,0,u} k (simplicialChainComplex (stage p) k) 1).hom.hom x = w
  induction w using Quotient.inductionOn' with
  | _ z =>
    change quotientEquiv k q (simplicialQuotientIncl k (stage_mono hpq) 1
      (Submodule.mkQ (R := k) (M := simplicialCycles (stage p) k 1)
        (simplicialBoundaries (stage p) k 1) z)) =
      structureMapLinear (finiteModule (k := k)) hpq
        (quotientEquiv k p (Submodule.mkQ (R := k) (M := simplicialCycles (stage p) k 1)
          (simplicialBoundaries (stage p) k 1) z))
    rw [simplicialQuotientIncl_mkQ, quotientEquiv_mk, quotientEquiv_mk]
    exact cycleCoefficient_naturality k hpq z

/-- Actual degree-one simplicial homology on the nine-point grid realizes the
independently defined degree-two witness, over every coefficient field. -/
noncomputable def finiteIso (k : Type u) [Field k] :
    grid.embedding.monotone.functor ⋙
      finiteSimplicialHomology k boundaryTetrahedronGrading 1 ≅ finiteModule (k := k) :=
  NatIso.ofComponents (fun p => (homologyEquiv k p).toModuleIso) (by
    intro p q f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact homologyEquiv_naturality k (leOfHom f) x)


private theorem grade_mem_gridValues (s : TotalFace boundaryTetrahedron.toPre) (i : Fin 2) :
    boundaryTetrahedronGrading.grade s i ∈ gridValues := by
  fin_cases i
  all_goals
    simp only [boundaryTetrahedronGrading, faceGradeNat]
    simp only [faceGradeX, faceGradeY]
    split_ifs <;> norm_num [gridValues]

/-- The actual finite face-coordinate grid is exactly the existing `3 × 3` grid. -/
theorem boundaryTetrahedronGrading_gridCoordinates :
    boundaryTetrahedronGrading.gridCoordinates = grid := by
  classical
  funext i
  apply Finset.ext
  intro x
  change x ∈ insert 0 (Finset.univ.image (fun s : TotalFace boundaryTetrahedron.toPre =>
    boundaryTetrahedronGrading.grade s i)) ↔ x ∈ gridValues
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp [gridValues]
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx
      exact grade_mem_gridValues s i
  · intro hx
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by
      simpa only [gridValues, Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hx' with rfl | rfl | rfl
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨⟨edge23.val, edge23.property.1⟩, Finset.mem_univ _, ?_⟩
      fin_cases i <;> norm_num [boundaryTetrahedronGrading, faceGradeNat,
        faceGradeX, faceGradeY, edge23, Finset.subset_iff] <;> decide
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      fin_cases i
      · refine ⟨⟨triangle013.val, triangle013.property.1⟩, Finset.mem_univ _, ?_⟩
        norm_num [boundaryTetrahedronGrading, faceGradeNat,
          faceGradeX, faceGradeY, triangle013, Finset.subset_iff]
      · refine ⟨⟨triangle012.val, triangle012.property.1⟩, Finset.mem_univ _, ?_⟩
        norm_num [boundaryTetrahedronGrading, faceGradeNat,
          faceGradeX, faceGradeY, triangle012, Finset.subset_iff]

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
