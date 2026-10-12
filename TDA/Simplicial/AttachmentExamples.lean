import TDA.Simplicial.Attachment

/-! Concrete additions of actual faces on three ordered vertices. -/

namespace TDA.Simplicial.AttachmentExamples

open TDA.Simplicial
universe v

private def generated (facets : Finset (Finset (Fin 3))) :
    PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ ∃ t ∈ facets, s ⊆ t}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht =>
      ⟨ht, by obtain ⟨u, hu, hsu⟩ := hs.2; exact ⟨u, hu, hts.trans hsu⟩⟩⟩

private def vertex0 := generated {{0}}
private def twoVertices := generated {{0}, {1}}
private def edge01 := generated {{0, 1}}
private def path := generated {{0, 1}, {0, 2}}
private def cycle := generated {{0, 1}, {0, 2}, {1, 2}}
private def triangle := generated {{0, 1, 2}}

private instance (facets : Finset (Finset (Fin 3))) :
    Finite (TotalFace (generated facets)) :=
  Finite.of_injective Subtype.val Subtype.val_injective

private def emptyVertex : SimplexAttachment
    (⊥ : PreAbstractSimplicialComplex (Fin 3)) vertex0 0 where
  simplex := {0}
  card_simplex := by decide
  not_mem := by simp
  face_iff := by
    change ∀ s : Finset (Fin 3), (s.Nonempty ∧ ∃ t ∈ ({{0}} : Finset (Finset (Fin 3))), s ⊆ t) ↔ False ∨ s = {0}
    decide

private def isolatedVertex : SimplexAttachment vertex0 twoVertices 0 where
  simplex := {1}
  card_simplex := by decide
  not_mem := by
    change ¬ (({1} : Finset (Fin 3)).Nonempty ∧ ∃ t ∈ ({{0}} : Finset (Finset (Fin 3))), ({1} : Finset (Fin 3)) ⊆ t)
    decide
  face_iff := by
    change ∀ s : Finset (Fin 3), (s.Nonempty ∧ ∃ t ∈ ({{0}, {1}} : Finset (Finset (Fin 3))), s ⊆ t) ↔ (s.Nonempty ∧ ∃ t ∈ ({{0}} : Finset (Finset (Fin 3))), s ⊆ t) ∨ s = {1}
    decide

private def connectingEdge : SimplexAttachment twoVertices edge01 1 where
  simplex := {0, 1}
  card_simplex := by decide
  not_mem := by
    change ¬ (({0, 1} : Finset (Fin 3)).Nonempty ∧ ∃ t ∈ ({{0}, {1}} : Finset (Finset (Fin 3))), ({0, 1} : Finset (Fin 3)) ⊆ t)
    decide
  face_iff := by
    change ∀ s : Finset (Fin 3), (s.Nonempty ∧ ∃ t ∈ ({{0, 1}} : Finset (Finset (Fin 3))), s ⊆ t) ↔ (s.Nonempty ∧ ∃ t ∈ ({{0}, {1}} : Finset (Finset (Fin 3))), s ⊆ t) ∨ s = {0, 1}
    decide

private def closingEdge : SimplexAttachment path cycle 1 where
  simplex := {1, 2}
  card_simplex := by decide
  not_mem := by
    change ¬ (({1, 2} : Finset (Fin 3)).Nonempty ∧ ∃ t ∈ ({{0, 1}, {0, 2}} : Finset (Finset (Fin 3))), ({1, 2} : Finset (Fin 3)) ⊆ t)
    decide
  face_iff := by
    change ∀ s : Finset (Fin 3), (s.Nonempty ∧ ∃ t ∈ ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))), s ⊆ t) ↔ (s.Nonempty ∧ ∃ t ∈ ({{0, 1}, {0, 2}} : Finset (Finset (Fin 3))), s ⊆ t) ∨ s = {1, 2}
    decide

private def fillingTriangle : SimplexAttachment cycle triangle 2 where
  simplex := {0, 1, 2}
  card_simplex := by decide
  not_mem := by
    change ¬ (({0, 1, 2} : Finset (Fin 3)).Nonempty ∧ ∃ t ∈ ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))), ({0, 1, 2} : Finset (Fin 3)) ⊆ t)
    decide

  face_iff := by
    change ∀ s : Finset (Fin 3), (s.Nonempty ∧ ∃ t ∈ ({{0, 1, 2}} : Finset (Finset (Fin 3))), s ⊆ t) ↔ (s.Nonempty ∧ ∃ t ∈ ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))), s ⊆ t) ∨ s = {0, 1, 2}
    decide

private instance : IsEmpty (Face twoVertices 1) := ⟨fun s => by
  have h : ∀ t : Finset (Fin 3),
      (t.Nonempty ∧ ∃ u ∈ ({{0}, {1}} : Finset (Finset (Fin 3))), t ⊆ u) →
      t.card ≠ 2 := by decide
  have hs : s.1.Nonempty ∧
      ∃ u ∈ ({{0}, {1}} : Finset (Finset (Fin 3))), s.1 ⊆ u := s.2.1
  exact (h s.1 hs) s.2.2⟩

private instance : IsEmpty (Face cycle 2) := ⟨fun s => by
  have h : ∀ t : Finset (Fin 3),
      (t.Nonempty ∧ ∃ u ∈ ({{0, 1}, {0, 2}, {1, 2}} :
        Finset (Finset (Fin 3))), t ⊆ u) → t.card ≠ 3 := by decide
  have hs : s.1.Nonempty ∧
      ∃ u ∈ ({{0, 1}, {0, 2}, {1, 2}} :
        Finset (Finset (Fin 3))), s.1 ⊆ u := s.2.1
  exact (h s.1 hs) s.2.2⟩


private def pathEdge01 : Face path 1 :=
  ⟨{0, 1}, by
    change ({0, 1} : Finset (Fin 3)).Nonempty ∧
      ∃ t ∈ ({{0, 1}, {0, 2}} : Finset (Finset (Fin 3))),
        ({0, 1} : Finset (Fin 3)) ⊆ t
    decide, by decide⟩

private def pathEdge02 : Face path 1 :=
  ⟨{0, 2}, by
    change ({0, 2} : Finset (Fin 3)).Nonempty ∧
      ∃ t ∈ ({{0, 1}, {0, 2}} : Finset (Finset (Fin 3))),
        ({0, 2} : Finset (Fin 3)) ⊆ t
    decide, by decide⟩

private theorem pathEdge01_order :
    pathEdge01.1.orderEmbOfFin pathEdge01.2.2 =
      Fin.succAboveOrderEmb (2 : Fin 3) := by
  have hs : pathEdge01.1 = ({(2 : Fin 3)}ᶜ : Finset (Fin 3)) := by decide
  simp [hs]

private theorem pathEdge02_order :
    pathEdge02.1.orderEmbOfFin pathEdge02.2.2 =
      Fin.succAboveOrderEmb (1 : Fin 3) := by
  have hs : pathEdge02.1 = ({(1 : Fin 3)}ᶜ : Finset (Fin 3)) := by decide
  simp [hs]

private theorem closingEdge_order :
    closingEdge.newFace.1.orderEmbOfFin closingEdge.newFace.2.2 =
      Fin.succAboveOrderEmb (0 : Fin 3) := by
  have hs : closingEdge.newFace.1 =
      ({(0 : Fin 3)}ᶜ : Finset (Fin 3)) := by decide
  simp [hs]

private theorem closingEdge_old_filler (k : Type*) [Field k] :
    boundary path k 0
      (Finsupp.single pathEdge02 1 - Finsupp.single pathEdge01 1) =
        closingEdge.attachingBoundary k := by
  classical
  have h02 : deletedFace path 0 pathEdge02 0 = closingEdge.oldDeletedFace 0 := by
    apply Subtype.ext
    change pathEdge02.1.erase
      (pathEdge02.1.orderEmbOfFin pathEdge02.2.2 0) =
      closingEdge.newFace.1.erase
        (closingEdge.newFace.1.orderEmbOfFin closingEdge.newFace.2.2 0)
    rw [pathEdge02_order, closingEdge_order]
    decide
  have hcommon : deletedFace path 0 pathEdge02 1 =
      deletedFace path 0 pathEdge01 1 := by
    apply Subtype.ext
    change pathEdge02.1.erase
      (pathEdge02.1.orderEmbOfFin pathEdge02.2.2 1) =
      pathEdge01.1.erase
        (pathEdge01.1.orderEmbOfFin pathEdge01.2.2 1)
    rw [pathEdge02_order, pathEdge01_order]
    decide
  have h01 : deletedFace path 0 pathEdge01 0 =
      closingEdge.oldDeletedFace 1 := by
    apply Subtype.ext
    change pathEdge01.1.erase
      (pathEdge01.1.orderEmbOfFin pathEdge01.2.2 0) =
      closingEdge.newFace.1.erase
        (closingEdge.newFace.1.orderEmbOfFin closingEdge.newFace.2.2 1)
    rw [pathEdge01_order, closingEdge_order]
    decide
  rw [map_sub, boundary_single, boundary_single]
  simp only [one_smul, SimplexAttachment.attachingBoundary,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  have hcommon' : deletedFace path 0 pathEdge02 (Fin.succ 0) =
      deletedFace path 0 pathEdge01 (Fin.succ 0) := by simpa using hcommon
  have h01' : deletedFace path 0 pathEdge01 0 =
      closingEdge.oldDeletedFace (Fin.succ 0) := by simpa using h01
  rw [h02, hcommon', h01']
  norm_num
  module

private theorem closingEdge_attachingClass_zero (k : Type v) [Field k] :
    closingEdge.attachingHomologyClass k = 0 := by
  have hb : closingEdge.attachingCycle k ∈ simplicialBoundaries path k 0 :=
    (mem_simplicialBoundaries_iff k path 0 _).2
      ⟨Finsupp.single pathEdge02 1 - Finsupp.single pathEdge01 1,
        closingEdge_old_filler k⟩
  have hq : closingEdge.attachingQuotientClass k = 0 :=
    (closingEdge.attachingClass_zero_iff_boundary k).2 hb
  let e := (homologyKernelQuotient.{v,0,v} k
    (simplicialChainComplex path k) 0).toLinearEquiv
  apply e.injective
  exact (closingEdge.attachingHomologyClass_equiv k).trans
    (hq.trans e.map_zero.symm)

example (k : Type*) [Field k] :
    Function.Injective
      (simplicialHomologyIncl k emptyVertex.inclusion 0).hom :=
  (emptyVertex.isolatedVertex_birth k).1

example (k : Type*) [Field k] :
    Module.finrank k (simplicialHomology twoVertices k 0 ⧸
      LinearMap.range (simplicialHomologyIncl k isolatedVertex.inclusion 0).hom) = 1 :=
  (isolatedVertex.isolatedVertex_birth k).2.1

/-- Joining the two components kills the span of the actual attaching class in H₀. -/
example (k : Type*) [Field k] :
    LinearMap.ker (simplicialHomologyIncl k connectingEdge.inclusion 0).hom =
      k ∙ connectingEdge.attachingHomologyClass k ∧
    Module.finrank k (LinearMap.ker
      (simplicialHomologyIncl k connectingEdge.inclusion 0).hom) = 1 := by
  have h := connectingEdge.positive_death k
    (connectingEdge.attachingClass_ne_zero_of_no_old_coface k)
  exact ⟨h.2.1, h.2.2.1⟩

/-- The last edge of the triangle boundary creates an actual H₁ class. -/
example (k : Type*) [Field k] :
    Function.Injective (simplicialHomologyIncl k closingEdge.inclusion 1).hom ∧
    Module.finrank k (simplicialHomology cycle k 1 ⧸
      LinearMap.range (simplicialHomologyIncl k closingEdge.inclusion 1).hom) = 1 ∧
    Function.Bijective (simplicialHomologyIncl k closingEdge.inclusion 0).hom := by
  have h := closingEdge.positive_birth k (closingEdge_attachingClass_zero k)
  exact ⟨h.1, h.2.1, h.2.2.1 0 (by omega)⟩

example (k : Type*) [Field k] :
    ∃ a : Chain path k 1, boundary path k 0 a = closingEdge.attachingBoundary k ∧
      ∃ z : simplicialCycles cycle k 1,
        (z : Chain cycle k 1) =
          Finsupp.single closingEdge.newFace 1 -
            chainIncl k closingEdge.inclusion 1 a ∧
        k ∙ closingEdge.birthCokernelClass k z = ⊤ :=
  closingEdge.positive_birth_generator k (closingEdge_attachingClass_zero k)

/-- Filling the triangle kills the boundary's actual degree-one class. -/
example (k : Type*) [Field k] :
    LinearMap.ker (simplicialHomologyIncl k fillingTriangle.inclusion 1).hom =
      k ∙ fillingTriangle.attachingHomologyClass k ∧
    Module.finrank k (LinearMap.ker
      (simplicialHomologyIncl k fillingTriangle.inclusion 1).hom) = 1 := by
  have h := fillingTriangle.positive_death k
    (fillingTriangle.attachingClass_ne_zero_of_no_old_coface k)
  exact ⟨h.2.1, h.2.2.1⟩

end TDA.Simplicial.AttachmentExamples
