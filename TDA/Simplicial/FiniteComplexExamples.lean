import TDA.Simplicial.FiniteComplex
import TDA.Filtration.FilterFunction

set_option autoImplicit false

/-!
# Executable finite-complex regressions

These private fixtures check support preservation, exact face enumeration, malformed
presentation rejection, and use of the merged face-value sublevel API. The explicit `#eval`
commands select the presentation-specific instances so the executable data path stays visible.
-/

namespace TDA.Simplicial.FiniteComplexExamples

open TDA.Simplicial.FiniteComplex

-- The exact public interface is kept visible alongside the fixtures.
#check @FiniteComplex
#check @toPre
#check @instDecidableMemToPre
#check @instFintypeTotalFace
#check @mem_toPre
#check @empty_not_mem_faces
#check @image_univ_totalFace_val
#check @card_totalFace
#check @toPre_injective

private theorem selected_fintype {n : ℕ} (C : FiniteComplex n) :
    (inferInstance : Fintype (TDA.Simplicial.TotalFace C.toPre)) =
      instFintypeTotalFace C := rfl

private theorem selected_decidable {n : ℕ} (C : FiniteComplex n)
    (s : Finset (Fin n)) :
    (inferInstance : Decidable (s ∈ C.toPre)) =
      instDecidableMemToPre C s := rfl

private def empty0 : FiniteComplex 0 where
  faces := ∅
  nonempty := by simp
  downClosed := by simp

private def empty3 : FiniteComplex 3 where
  faces := ∅
  nonempty := by simp
  downClosed := by simp

private theorem fin0_faces_empty (C : FiniteComplex 0) : C.faces = ∅ := by
  ext s
  constructor
  · intro hs
    obtain ⟨v, _⟩ := C.nonempty s hs
    exact Fin.elim0 v
  · simp

private theorem empty0_toPre_bot :
    empty0.toPre = (⊥ : PreAbstractSimplicialComplex (Fin 0)) := by
  ext s
  change s ∈ (∅ : Finset (Finset (Fin 0))) ↔ False
  simp

private theorem empty3_toPre_bot :
    empty3.toPre = (⊥ : PreAbstractSimplicialComplex (Fin 3)) := by
  ext s
  change s ∈ (∅ : Finset (Finset (Fin 3))) ↔ False
  simp

private theorem empty3_no_singletons (v : Fin 3) :
    ({v} : Finset (Fin 3)) ∉ empty3.toPre := by
  simp [mem_toPre, empty3]

private theorem empty0_univ_empty :
    (Finset.univ : Finset (TDA.Simplicial.TotalFace empty0.toPre)) = ∅ := by
  ext s
  have hs : s.val ∈ empty0.faces := s.property
  change s.val ∈ (∅ : Finset (Finset (Fin 0))) at hs
  simp at hs

private theorem empty3_univ_empty :
    (Finset.univ : Finset (TDA.Simplicial.TotalFace empty3.toPre)) = ∅ := by
  ext s
  have hs : s.val ∈ empty3.faces := s.property
  change s.val ∈ (∅ : Finset (Finset (Fin 3))) at hs
  simp at hs

private def singleton3 : FiniteComplex 3 where
  faces := {{0}}
  nonempty := by decide
  downClosed := by decide

private theorem singleton3_no_one :
    ({1} : Finset (Fin 3)) ∉ singleton3.toPre := by decide

private theorem singleton3_empty_absent :
    (∅ : Finset (Fin 3)) ∉ singleton3.toPre :=
  singleton3.empty_not_mem_faces

private theorem singleton3_image_exact :
    (Finset.univ : Finset (TDA.Simplicial.TotalFace singleton3.toPre)).image
      (fun s => s.val) = singleton3.faces :=
  image_univ_totalFace_val singleton3

private theorem singleton3_toPre_singletonFace :
    singleton3.toPre = TDA.Filtration.singletonFace (0 : Fin 3) := by
  ext s
  change s ∈ ({{0}} : Finset (Finset (Fin 3))) ↔ s = {0}
  simp

private theorem singleton3_not_top :
    singleton3.toPre ≠ (⊤ : PreAbstractSimplicialComplex (Fin 3)) := by
  intro h
  have hs : ({1} : Finset (Fin 3)) ∈ singleton3.toPre := by
    rw [h]
    change ({1} : Finset (Fin 3)).Nonempty
    simp
  exact singleton3_no_one hs

private def edge3 : FiniteComplex 3 where
  faces := {{0}, {1}, {0, 1}}
  nonempty := by decide
  downClosed := by decide

private theorem edge3_no_two (s : Finset (Fin 3)) (h : (2 : Fin 3) ∈ s) :
    s ∉ edge3.toPre := by
  intro hs
  change s ∈ edge3.faces at hs
  simp only [edge3, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h0 | h1 | h01
  · rw [h0] at h
    simp at h
  · rw [h1] at h
    simp at h
  · rw [h01] at h
    simp at h

private theorem edge3_no_singleton_two :
    ({2} : Finset (Fin 3)) ∉ edge3.toPre :=
  edge3_no_two {2} (by simp)

private theorem edge3_empty_absent :
    (∅ : Finset (Fin 3)) ∉ edge3.toPre :=
  edge3.empty_not_mem_faces

private theorem edge3_image_exact :
    (Finset.univ : Finset (TDA.Simplicial.TotalFace edge3.toPre)).image
      (fun s => s.val) = edge3.faces :=
  image_univ_totalFace_val edge3

private theorem malformed_empty_face_impossible
    (C : FiniteComplex 3) (h : (∅ : Finset (Fin 3)) ∈ C.faces) : False :=
  C.empty_not_mem_faces h

private theorem malformed_edge_only_impossible
    (h : ∀ {s t : Finset (Fin 3)},
      s ∈ ({{0, 1}} : Finset (Finset (Fin 3))) →
      t.Nonempty → t ⊆ s →
      t ∈ ({{0, 1}} : Finset (Finset (Fin 3)))) : False := by
  have hs : ({0} : Finset (Fin 3)) ∈
      ({{0, 1}} : Finset (Finset (Fin 3))) :=
    h (s := {0, 1}) (t := {0}) (by decide) (by decide) (by decide)
  exact (by decide : ({0} : Finset (Fin 3)) ≠ {0, 1})
    (Finset.mem_singleton.mp hs)

private def triangle3 : FiniteComplex 3 where
  faces := {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}
  nonempty := by decide
  downClosed := by decide

private theorem triangle3_card : triangle3.faces.card = 7 := by decide

private theorem triangle3_image_exact :
    (Finset.univ : Finset (TDA.Simplicial.TotalFace triangle3.toPre)).image
      (fun s => s.val) = triangle3.faces :=
  image_univ_totalFace_val triangle3

private def edge3Filter : TDA.Filtration.FilterFunction edge3.toPre ℤ where
  value := fun _ => 5
  mono := by
    intros
    exact le_rfl

private theorem edge3Filter_sublevel_four : edge3Filter.sublevel 4 = ⊥ := by
  apply edge3Filter.sublevel_eq_bot_of_forall_lt
  intro s
  norm_num [edge3Filter]

private theorem edge3Filter_sublevel_five : edge3Filter.sublevel 5 = edge3.toPre := by
  apply edge3Filter.sublevel_eq_self_of_forall_le
  intro s
  simp [edge3Filter]

private theorem edge3Filter_mem_iff (r : ℤ) (s : Finset (Fin 3)) :
    s ∈ edge3Filter.sublevel r ↔ s ∈ edge3.toPre ∧ (5 : ℤ) ≤ r := by
  rw [TDA.Filtration.FilterFunction.mem_sublevel_iff]
  constructor
  · rintro ⟨hs, hv⟩
    exact ⟨hs, by simpa [edge3Filter] using hv⟩
  · rintro ⟨hs, hr⟩
    exact ⟨hs, by simpa [edge3Filter] using hr⟩

private instance edge3FilterMemDecidable (r : ℤ) (s : Finset (Fin 3)) :
    Decidable (s ∈ edge3Filter.sublevel r) :=
  decidable_of_iff (s ∈ edge3.toPre ∧ (5 : ℤ) ≤ r)
    (edge3Filter_mem_iff r s).symm

private theorem edge3Filter_vertex_two_absent :
    ({2} : Finset (Fin 3)) ∉ edge3Filter.sublevel 5 := by
  rw [edge3Filter_sublevel_five]
  exact edge3_no_singleton_two

-- The named presentation instances are selected explicitly by the executable checks.
#eval (letI := instFintypeTotalFace empty0;
  Fintype.card (TDA.Simplicial.TotalFace empty0.toPre))
#eval (letI := instFintypeTotalFace empty3;
  Fintype.card (TDA.Simplicial.TotalFace empty3.toPre))
#eval (letI := instFintypeTotalFace singleton3;
  Fintype.card (TDA.Simplicial.TotalFace singleton3.toPre))
#eval (letI := instFintypeTotalFace edge3;
  Fintype.card (TDA.Simplicial.TotalFace edge3.toPre))
#eval (letI := instFintypeTotalFace triangle3;
  Fintype.card (TDA.Simplicial.TotalFace triangle3.toPre))

#eval (letI := instDecidableMemToPre singleton3;
  decide (({0} : Finset (Fin 3)) ∈ singleton3.toPre))
#eval (letI := instDecidableMemToPre singleton3;
  decide (({1} : Finset (Fin 3)) ∈ singleton3.toPre))
#eval (letI := instDecidableMemToPre singleton3;
  decide ((∅ : Finset (Fin 3)) ∈ singleton3.toPre))
#eval (letI := instDecidableMemToPre edge3;
  decide (({0, 1} : Finset (Fin 3)) ∈ edge3.toPre))
#eval (letI := instDecidableMemToPre edge3;
  decide (({2} : Finset (Fin 3)) ∈ edge3.toPre))
#eval (letI := instDecidableMemToPre edge3;
  decide ((∅ : Finset (Fin 3)) ∈ edge3.toPre))
#eval (letI := instDecidableMemToPre empty3;
  decide (({0} : Finset (Fin 3)) ∈ empty3.toPre))
#eval (letI := instDecidableMemToPre triangle3;
  decide (({0, 1, 2} : Finset (Fin 3)) ∈ triangle3.toPre))
#eval (letI := instDecidableMemToPre triangle3;
  decide ((∅ : Finset (Fin 3)) ∈ triangle3.toPre))

#eval (letI := instFintypeTotalFace empty3;
  decide (((Finset.univ : Finset (TDA.Simplicial.TotalFace empty3.toPre)).image
    (fun s => s.val)) = empty3.faces))
#eval (letI := instFintypeTotalFace singleton3;
  decide (((Finset.univ : Finset (TDA.Simplicial.TotalFace singleton3.toPre)).image
    (fun s => s.val)) = singleton3.faces))
#eval (letI := instFintypeTotalFace edge3;
  decide (((Finset.univ : Finset (TDA.Simplicial.TotalFace edge3.toPre)).image
    (fun s => s.val)) = edge3.faces))
#eval (letI := instFintypeTotalFace triangle3;
  decide (((Finset.univ : Finset (TDA.Simplicial.TotalFace triangle3.toPre)).image
    (fun s => s.val)) = triangle3.faces))
#eval (letI := instFintypeTotalFace edge3;
  letI := edge3FilterMemDecidable 4 ({0} : Finset (Fin 3));
  decide (({0} : Finset (Fin 3)) ∈ edge3Filter.sublevel 4))
#eval (letI := instFintypeTotalFace edge3;
  letI := edge3FilterMemDecidable 5 ({0, 1} : Finset (Fin 3));
  decide (({0, 1} : Finset (Fin 3)) ∈ edge3Filter.sublevel 5))
#eval (letI := instFintypeTotalFace edge3;
  letI := edge3FilterMemDecidable 5 ({2} : Finset (Fin 3));
  decide (({2} : Finset (Fin 3)) ∈ edge3Filter.sublevel 5))

-- Every declaration in this private fixture is included in the live trust audit.
#print axioms FiniteComplex.mk
#print axioms FiniteComplex.faces
#print axioms FiniteComplex.nonempty
#print axioms FiniteComplex.downClosed
#print axioms toPre
#print axioms instDecidableMemToPre
#print axioms instFintypeTotalFace
#print axioms selected_fintype
#print axioms selected_decidable
#print axioms empty0
#print axioms empty3
#print axioms fin0_faces_empty
#print axioms empty0_toPre_bot
#print axioms empty3_toPre_bot
#print axioms empty3_no_singletons
#print axioms empty0_univ_empty
#print axioms empty3_univ_empty
#print axioms singleton3
#print axioms singleton3_no_one
#print axioms singleton3_empty_absent
#print axioms singleton3_image_exact
#print axioms singleton3_toPre_singletonFace
#print axioms singleton3_not_top
#print axioms edge3
#print axioms edge3_no_two
#print axioms edge3_no_singleton_two
#print axioms edge3_empty_absent
#print axioms edge3_image_exact
#print axioms malformed_empty_face_impossible
#print axioms malformed_edge_only_impossible
#print axioms triangle3
#print axioms triangle3_card
#print axioms triangle3_image_exact
#print axioms edge3Filter
#print axioms edge3Filter_sublevel_four
#print axioms edge3Filter_sublevel_five
#print axioms edge3Filter_mem_iff
#print axioms edge3FilterMemDecidable
#print axioms edge3Filter_vertex_two_absent

end TDA.Simplicial.FiniteComplexExamples
