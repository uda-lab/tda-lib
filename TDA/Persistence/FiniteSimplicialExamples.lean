import TDA.Persistence.FiniteSimplicialStability
import TDA.Simplicial.Attachment

/-!
# Finite simplicial stability examples

The edge filtration has two vertices with the same birth grade and a later
joining edge. Its actual H₀ structure map kills one class. A translated grade
assignment supplies a nonzero perturbation. The empty fixtures include zero
ambient vertices and zero grading coordinates. A two-coordinate fixture has
incomparable vertex grades and distinct singleton sublevels.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteSimplicialExamples

open TDA.Simplicial TDA.Filtration CategoryTheory
open scoped TDA.Persistence NNReal ENNReal

private def edge : FiniteComplex 2 where
  faces := {{0}, {1}, {0, 1}}
  nonempty := by decide
  downClosed := by decide

private def vertices : FiniteComplex 2 where
  faces := {{0}, {1}}
  nonempty := by decide
  downClosed := by decide

private def edgeGrades (n : ℕ) : FiniteGraded edge n where
  grade s _ := (s.val.card : ℝ) - 1
  mono := by
    intro s t h i
    exact sub_le_sub_right (Nat.cast_le.mpr (Finset.card_le_card h)) 1

private def translatedEdgeGrades (n : ℕ) : FiniteGraded edge n where
  grade s _ := (s.val.card : ℝ)
  mono := by
    intro s t h i
    exact Nat.cast_le.mpr (Finset.card_le_card h)

private theorem edge_grade_error (n : ℕ) :
    ∀ s i, |(edgeGrades n).grade s i -
      (translatedEdgeGrades n).grade s i| ≤ ((1 : ℝ≥0) : ℝ) := by
  intro s i
  norm_num [edgeGrades, translatedEdgeGrades]

private theorem repeated_vertex_grades (n : ℕ) (i : Fin n) :
    (edgeGrades n).grade ⟨{0}, by decide⟩ i = 0 ∧
    (edgeGrades n).grade ⟨{1}, by decide⟩ i = 0 := by
  norm_num [edgeGrades]

private def incomparableEdgeGrades : FiniteGraded edge 2 where
  grade s i := if (if i = 0 then 1 else 0 : Fin 2) ∈ s.val then 1 else 0
  mono := by
    intro s t h i
    by_cases hs : (if i = 0 then 1 else 0 : Fin 2) ∈ s.val
    · have ht := h hs
      simp [hs, ht]
    · simp only [hs, ↓reduceIte]
      split_ifs <;> norm_num

private theorem incomparable_vertex_grades :
    ¬ incomparableEdgeGrades.grade ⟨{0}, by decide⟩ ≤
      incomparableEdgeGrades.grade ⟨{1}, by decide⟩ ∧
    ¬ incomparableEdgeGrades.grade ⟨{1}, by decide⟩ ≤
      incomparableEdgeGrades.grade ⟨{0}, by decide⟩ := by
  constructor
  · intro h
    have h1 := h 1
    norm_num [incomparableEdgeGrades] at h1
  · intro h
    have h0 := h 0
    norm_num [incomparableEdgeGrades] at h0

private theorem incomparable_sublevel_vertex_zero :
    incomparableEdgeGrades.sublevel (fun i => if i = 0 then 0 else 1) =
      singletonFace (0 : Fin 2) := by
  ext s
  change s ∈ incomparableEdgeGrades.sublevel (fun i => if i = 0 then 0 else 1) ↔
    s ∈ singletonFace (0 : Fin 2)
  rw [FiniteGraded.mem_sublevel_iff, mem_singletonFace_iff]
  constructor
  · rintro ⟨hs, hg⟩
    change s ∈ edge.faces at hs
    simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · rfl
    · have h := hg 0
      norm_num [incomparableEdgeGrades] at h
    · have h := hg 0
      norm_num [incomparableEdgeGrades] at h
  · rintro rfl
    exact ⟨by decide, by intro i; fin_cases i <;> norm_num [incomparableEdgeGrades]⟩

private theorem incomparable_sublevel_vertex_one :
    incomparableEdgeGrades.sublevel (fun i => if i = 0 then 1 else 0) =
      singletonFace (1 : Fin 2) := by
  ext s
  change s ∈ incomparableEdgeGrades.sublevel (fun i => if i = 0 then 1 else 0) ↔
    s ∈ singletonFace (1 : Fin 2)
  rw [FiniteGraded.mem_sublevel_iff, mem_singletonFace_iff]
  constructor
  · rintro ⟨hs, hg⟩
    change s ∈ edge.faces at hs
    simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · have h := hg 1
      norm_num [incomparableEdgeGrades] at h
    · rfl
    · have h := hg 1
      norm_num [incomparableEdgeGrades] at h
  · rintro rfl
    exact ⟨by decide, by intro i; fin_cases i <;> norm_num [incomparableEdgeGrades]⟩

private theorem incomparable_sublevel_full_edge :
    incomparableEdgeGrades.sublevel (fun _ => 1) = edge.toPre := by
  apply FiniteGraded.sublevel_eq_self_of_forall_le
  intro s i
  simp only [incomparableEdgeGrades]
  split_ifs <;> norm_num

private theorem incomparable_sublevels_distinct :
    incomparableEdgeGrades.sublevel (fun i => if i = 0 then 0 else 1) ≠
      incomparableEdgeGrades.sublevel (fun i => if i = 0 then 1 else 0) := by
  rw [incomparable_sublevel_vertex_zero, incomparable_sublevel_vertex_one]
  intro h
  have hm : ({0} : Finset (Fin 2)) ∈ singletonFace (1 : Fin 2) :=
    h ▸ (mem_singletonFace_iff _ _).mpr rfl
  have he := (mem_singletonFace_iff _ _).mp hm
  exact (by decide : ({0} : Finset (Fin 2)) ≠ {1}) he

private theorem edge_sublevel_zero :
    (edgeGrades 1).sublevel (fun _ => 0) = vertices.toPre := by
  ext s
  change s ∈ (edgeGrades 1).sublevel (fun _ => 0) ↔ s ∈ vertices.toPre
  rw [FiniteGraded.mem_sublevel_iff]
  constructor
  · rintro ⟨hs, hg⟩
    change s ∈ edge.faces at hs
    simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · decide
    · decide
    · have h := hg 0
      norm_num [edgeGrades] at h
  · intro hs
    change s ∈ vertices.faces at hs
    simp only [vertices, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨by decide, by intro i; norm_num [edgeGrades]⟩
    · exact ⟨by decide, by intro i; norm_num [edgeGrades]⟩

private theorem edge_sublevel_one :
    (edgeGrades 1).sublevel (fun _ => 1) = edge.toPre := by
  ext s
  change s ∈ (edgeGrades 1).sublevel (fun _ => 1) ↔ s ∈ edge.toPre
  rw [FiniteGraded.mem_sublevel_iff]
  constructor
  · exact fun ⟨hs, _⟩ => hs
  · intro hs
    refine ⟨hs, ?_⟩
    change s ∈ edge.faces at hs
    simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> intro i <;> norm_num [edgeGrades]

private def connectingEdgeOnComplexes : SimplexAttachment vertices.toPre edge.toPre 1 where
  simplex := {0, 1}
  card_simplex := by decide
  not_mem := by decide
  face_iff := by
    change ∀ s : Finset (Fin 2), s ∈ edge.faces ↔
      s ∈ vertices.faces ∨ s = {0, 1}
    decide

private instance : IsEmpty (Face vertices.toPre 1) := ⟨fun s => by
  have hs : s.val ∈ vertices.faces := s.property.1
  simp only [vertices, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | h <;> have hc := s.property.2 <;> simp [h] at hc⟩

private def connectingEdge : SimplexAttachment
    ((edgeGrades 1).sublevel (fun _ => 0))
    ((edgeGrades 1).sublevel (fun _ => 1)) 1 := by
  rw [edge_sublevel_zero, edge_sublevel_one]
  exact connectingEdgeOnComplexes

private instance : IsEmpty (Face ((edgeGrades 1).sublevel (fun _ => 0)) 1) := by
  rw [edge_sublevel_zero]
  infer_instance

private theorem edge_structureMap_kills_one_class (k : Type u) [Field k] :
    Module.finrank k (LinearMap.ker
      (structureMap (finiteSimplicialHomology k (edgeGrades 1) 0)
        (show (fun _ : Fin 1 => (0 : ℝ)) ≤ (fun _ => 1) by
          intro i; norm_num)).hom) = 1 := by
  rw [finiteSimplicialHomology_structureMap]
  exact (connectingEdge.positive_death k
    (connectingEdge.attachingClass_ne_zero_of_no_old_coface k)).2.2.1

private theorem perturbed_edge_stability (k : Type u) [Field k] (q : ℕ) :
    signedHookBottleneckDissimilarity (k := k)
        (finiteSimplicialSignedHookBarcode k (by decide : 1 ≤ 1) (edgeGrades 1) q)
        (finiteSimplicialSignedHookBarcode k (by decide : 1 ≤ 1)
          (translatedEdgeGrades 1) q) ≤ 1 := by
  simpa using finiteSimplicial_signedHookBottleneckDissimilarity_le k
    (by decide : 1 ≤ 1) (edgeGrades 1) (translatedEdgeGrades 1) q
    (edge_grade_error 1)

private theorem perturbation_is_nonzero :
    (edgeGrades 1).grade ⟨{0}, by decide⟩ 0 ≠
      (translatedEdgeGrades 1).grade ⟨{0}, by decide⟩ 0 := by
  norm_num [edgeGrades, translatedEdgeGrades]

private def emptyComplex (m : ℕ) : FiniteComplex m where
  faces := ∅
  nonempty := by simp
  downClosed := by simp

private def emptyGrades (m n : ℕ) : FiniteGraded (emptyComplex m) n where
  grade s := by
    have hs : s.val ∈ (∅ : Finset (Finset (Fin m))) := s.property
    exact False.elim (Finset.notMem_empty s.val hs)
  mono := by
    intro s t h
    have hs : s.val ∈ (∅ : Finset (Finset (Fin m))) := s.property
    exact False.elim (Finset.notMem_empty s.val hs)

private theorem empty_finitelyPresented (k : Type u) [Field k] (m n q : ℕ) :
    GradedFree.FinitelyPresented.{u,0,0}
      (finiteSimplicialHomology k (emptyGrades m n) q) :=
  finiteSimplicialHomology_finitelyPresented k (emptyGrades m n) q

private theorem empty_zero_vertices_zero_coordinates (k : Type u) [Field k] (q : ℕ) :
    GradedFree.FinitelyPresented.{u,0,0}
      (finiteSimplicialHomology k (emptyGrades 0 0) q) :=
  empty_finitelyPresented k 0 0 q

private theorem empty_stability (k : Type u) [Field k] (m q : ℕ) :
    signedHookBottleneckDissimilarity (k := k)
        (finiteSimplicialSignedHookBarcode k (by decide : 1 ≤ 1) (emptyGrades m 1) q)
        (finiteSimplicialSignedHookBarcode k (by decide : 1 ≤ 1) (emptyGrades m 1) q)
      ≤ 0 := by
  simpa using finiteSimplicial_signedHookBottleneckDissimilarity_le k
    (by decide : 1 ≤ 1) (emptyGrades m 1) (emptyGrades m 1) q
    (δ := 0) (by intro s i; simp)

#print axioms edge
#print axioms vertices
#print axioms edgeGrades
#print axioms translatedEdgeGrades
#print axioms edge_grade_error
#print axioms repeated_vertex_grades
#print axioms incomparableEdgeGrades
#print axioms incomparable_vertex_grades
#print axioms incomparable_sublevel_vertex_zero
#print axioms incomparable_sublevel_vertex_one
#print axioms incomparable_sublevel_full_edge
#print axioms incomparable_sublevels_distinct
#print axioms edge_sublevel_zero
#print axioms edge_sublevel_one
#print axioms connectingEdgeOnComplexes
#print axioms connectingEdge
#print axioms edge_structureMap_kills_one_class
#print axioms perturbed_edge_stability
#print axioms perturbation_is_nonzero
#print axioms emptyComplex
#print axioms emptyGrades
#print axioms empty_finitelyPresented
#print axioms empty_zero_vertices_zero_coordinates
#print axioms empty_stability

end TDA.Persistence.FiniteSimplicialExamples
