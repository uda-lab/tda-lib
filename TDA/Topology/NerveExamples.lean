import TDA.Topology.Nerve

/-!
# Concrete ordinary-nerve fixtures

These declarations exercise support-sensitive vertices, duplicate labels,
pairwise-but-not-triple intersections, strict pullback loss, and empty types.
-/

namespace TDA.Topology.NerveExamples

/-- A family with an inhabited index type but an empty member. -/
def emptyMemberFamily : CoverFamily Bool (Fin 1) := fun _ => ∅

/-- An empty member does not create a vertex. -/
theorem emptyMember_has_no_vertex :
    ¬ ({0} : Finset (Fin 1)) ∈ nerve emptyMemberFamily := by
  simp [mem_nerve_iff, emptyMemberFamily]

/-- Two distinct labels carry the same nonempty member. -/
def duplicateFamily : CoverFamily Bool (Fin 2) := fun _ => {true}

/-- Both duplicate labels are vertices of the nerve. -/
theorem duplicateFamily_has_two_vertices :
    ({0} : Finset (Fin 2)) ∈ nerve duplicateFamily ∧
      ({1} : Finset (Fin 2)) ∈ nerve duplicateFamily := by
  simp [mem_nerve_iff, duplicateFamily]

/-- The two duplicate vertices span an edge. -/
theorem duplicateFamily_has_edge :
    ({0, 1} : Finset (Fin 2)) ∈ nerve duplicateFamily := by
  simp [mem_nerve_iff, duplicateFamily]

/-- Three members have all pairwise intersections but no common triple point. -/
def pairwiseFamily : CoverFamily (Fin 3) (Fin 3) := fun i =>
  if i = 0 then {0, 1} else if i = 1 then {1, 2} else {0, 2}

/-- Every edge in the pairwise fixture is a face. -/
theorem pairwiseFamily_has_all_edges :
    ({0, 1} : Finset (Fin 3)) ∈ nerve pairwiseFamily ∧
      ({0, 2} : Finset (Fin 3)) ∈ nerve pairwiseFamily ∧
      ({1, 2} : Finset (Fin 3)) ∈ nerve pairwiseFamily := by
  simp [mem_nerve_iff, pairwiseFamily]

/-- Pairwise intersections do not create the absent triple face. -/
theorem pairwiseFamily_has_no_triangle :
    ¬ ({0, 1, 2} : Finset (Fin 3)) ∈ nerve pairwiseFamily := by
  intro hs
  obtain ⟨_, x, hx⟩ := (mem_nerve_iff pairwiseFamily _).1 hs
  fin_cases x <;> simp [pairwiseFamily] at hx

/-- Two disjoint target members, retained as two labelled vertices. -/
def disjointFamily : CoverFamily Bool (Fin 2) := fun i =>
  if i = 0 then {false} else {true}

/-- A constant map lands in the first target member. -/
def constantMap : Fin 1 → Bool := fun _ => false

/-- The target nerve has both disjoint-family vertices. -/
theorem disjointFamily_has_target_vertices :
    ({0} : Finset (Fin 2)) ∈ nerve disjointFamily ∧
      ({1} : Finset (Fin 2)) ∈ nerve disjointFamily := by
  simp [mem_nerve_iff, disjointFamily]

/-- The constant pullback retains the first target vertex. -/
theorem constantPullback_has_first_vertex :
    ({0} : Finset (Fin 2)) ∈ nerve (pullback constantMap disjointFamily) := by
  simp [mem_nerve_iff, pullback, disjointFamily, constantMap]

/-- The constant pullback loses the second target vertex. -/
theorem constantPullback_has_no_second_vertex :
    ¬ ({1} : Finset (Fin 2)) ∈ nerve (pullback constantMap disjointFamily) := by
  simp [mem_nerve_iff, pullback, disjointFamily, constantMap]

/-- The constant pullback is a proper subcomplex of the disjoint target nerve. -/
theorem constantPullback_is_proper_subcomplex :
    nerve (pullback constantMap disjointFamily) < nerve disjointFamily := by
  refine ⟨nerve_pullback_le constantMap disjointFamily, ?_⟩
  intro h
  exact constantPullback_has_no_second_vertex (h disjointFamily_has_target_vertices.2)

/-- An empty ambient type gives the bottom nerve without an inhabitedness assumption. -/
def emptyAmbientFamily : CoverFamily Empty (Fin 1) := fun _ => ∅

theorem emptyAmbient_nerve_is_bot :
    nerve emptyAmbientFamily = (⊥ : PreAbstractSimplicialComplex (Fin 1)) := by
  exact nerve_eq_bot_of_isEmpty emptyAmbientFamily

/-- An empty index type gives the bottom nerve without an inhabitedness assumption. -/
def emptyIndexFamily : CoverFamily Bool Empty := Empty.elim

theorem emptyIndex_nerve_is_bot :
    nerve emptyIndexFamily = (⊥ : PreAbstractSimplicialComplex Empty) := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  constructor
  · intro hs
    obtain ⟨i, _⟩ := (mem_nerve_iff emptyIndexFamily s).1 hs |>.1
    exact Empty.elim i
  · intro hs
    exact hs.elim

end TDA.Topology.NerveExamples
