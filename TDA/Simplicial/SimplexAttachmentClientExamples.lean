import TDA.Simplicial.DeletedFaceValues
import TDA.Simplicial.FiniteComplex

/-!
# Client statements of the attached-simplex face computations

Regression fixtures for #1277, family 10 of the downstream-use audit (#1207). Each statement
is written as a downstream client writes it: the file opens no scope and declares no instance,
and no helper lemma computes a deleted face.

* Joining the two isolated vertices of `Fin 2` by the edge `{0, 1}`: the old deleted faces of the
  edge at positions `0` and `1` are `{1}` and `{0}`, and the attaching class is nonzero over
  every field, through the existing theorem and through the form that takes the two vertices
  directly.
-/

namespace TDA.Simplicial.SimplexAttachmentClientExamples

/-- The edge `{0, 1}` with its two vertices, on `Fin 2`. -/
def edge : TDA.Simplicial.FiniteComplex 2 where
  faces := {{0}, {1}, {0, 1}}
  nonempty := by decide
  downClosed := by decide

/-- The two isolated vertices of `Fin 2`. -/
def twoPoints : TDA.Simplicial.FiniteComplex 2 where
  faces := {{0}, {1}}
  nonempty := by decide
  downClosed := by decide

/-- The edge `{0, 1}` attached to the two vertices. -/
def attach : TDA.Simplicial.SimplexAttachment twoPoints.toPre edge.toPre 1 where
  simplex := {0, 1}
  card_simplex := by decide
  not_mem := by decide
  face_iff := by
    intro s
    change s ∈ edge.faces ↔ s ∈ twoPoints.faces ∨ s = {0, 1}
    simp only [edge, twoPoints, Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- The old deleted face of the attached edge at position `0` is `{1}`. -/
theorem oldDeletedFace_zero : (attach.oldDeletedFace 0).val = {1} :=
  TDA.Simplicial.SimplexAttachment.oldDeletedFace_val_pair_zero attach (a := 0) (b := 1)
    (by decide) rfl

/-- The old deleted face of the attached edge at position `1` is `{0}`. -/
theorem oldDeletedFace_one : (attach.oldDeletedFace 1).val = {0} :=
  TDA.Simplicial.SimplexAttachment.oldDeletedFace_val_pair_one attach (a := 0) (b := 1)
    (by decide) rfl

/-- The attaching class of the edge is nonzero, from the existing theorem. -/
theorem attachingHomologyClass_ne_zero (k : Type) [Field k] :
    attach.attachingHomologyClass k ≠ 0 :=
  TDA.Simplicial.SimplexAttachment.attachingHomologyClass_ne_zero_of_separated_vertices
    twoPoints.toPre k attach (fun v => v.val = {1}) (by decide)
    (by rw [oldDeletedFace_zero]) (by rw [oldDeletedFace_one]; decide)

/-- The attaching class of the edge is nonzero, from the vertex form. -/
theorem attachingHomologyClass_ne_zero_of_vertices (k : Type) [Field k] :
    attach.attachingHomologyClass k ≠ 0 :=
  TDA.Simplicial.SimplexAttachment.attachingHomologyClass_ne_zero_of_separated_edge k attach
    (fun v => v = 1) (by decide) (a := 0) (b := 1) (by decide) rfl (by decide) rfl

end TDA.Simplicial.SimplexAttachmentClientExamples
