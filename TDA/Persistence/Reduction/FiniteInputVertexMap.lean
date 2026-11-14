import TDA.Persistence.Reduction.FiniteInputCycleCoordinatesCorrectness

/-! Finite validation and original-face matrices of simplicial vertex functions. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- Every admitted source face has its image admitted in the target. -/
def VertexMapCondition (xs ys : Input) (a b : ℤ) (f : ℕ → ℕ) : Prop :=
  ∀ i : Fin xs.length, (xs.get i).2 ≤ a →
    ∃ j : Fin ys.length, (ys.get j).1 = (xs.get i).1.image f ∧ (ys.get j).2 ≤ b

instance (xs ys : Input) (a b : ℤ) (f : ℕ → ℕ) :
    Decidable (VertexMapCondition xs ys a b f) := by
  unfold VertexMapCondition
  infer_instance

/-- The complete finite input check, in all face degrees. -/
def VertexMapInput (xs ys : Input) (a b : ℤ) (f : ℕ → ℕ) : Prop :=
  Valid xs ∧ Valid ys ∧ VertexMapCondition xs ys a b f

instance (xs ys : Input) (a b : ℤ) (f : ℕ → ℕ) :
    Decidable (VertexMapInput xs ys a b f) := by
  unfold VertexMapInput
  infer_instance

theorem gradeFilter_listFace (xs : Input) (h : Valid xs) (i : Fin xs.length) :
    (gradeFilter xs h).value (listFace xs h i) = (xs.get i).2 := by
  change (xs.get ((listEquiv xs h).symm ((listEquiv xs h) i))).2 = _
  rw [Equiv.symm_apply_apply]

/-- Actual sublevel faces are exactly the admitted list entries. -/
theorem mem_sublevel_iff_list (xs : Input) (h : Valid xs) (a : ℤ) (s : Finset ℕ) :
    s ∈ (gradeFilter xs h).sublevel a ↔
      ∃ i : Fin xs.length, (xs.get i).1 = s ∧ (xs.get i).2 ≤ a := by
  constructor
  · rintro ⟨hs, ha⟩
    let i := (listEquiv xs h).symm ⟨s, hs⟩
    refine ⟨i, ?_, ha⟩
    exact congrArg Subtype.val ((listEquiv xs h).apply_symm_apply ⟨s, hs⟩)
  · rintro ⟨i, rfl, ha⟩
    refine ⟨(listFace xs h i).property, ?_⟩
    exact (gradeFilter_listFace xs h i).trans_le ha

/-- The finite condition is exactly the face-preservation condition of the actual sublevels. -/
theorem vertexMapCondition_iff (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (a b : ℤ) (f : ℕ → ℕ) :
    VertexMapCondition xs ys a b f ↔
      ∀ s, s ∈ (gradeFilter xs hx).sublevel a →
        s.image f ∈ (gradeFilter ys hy).sublevel b := by
  constructor
  · intro h s hs
    obtain ⟨i, hi, ha⟩ := (mem_sublevel_iff_list xs hx a s).mp hs
    obtain ⟨j, hj, hb⟩ := h i ha
    exact (mem_sublevel_iff_list ys hy b (s.image f)).mpr ⟨j, hi ▸ hj, hb⟩
  · intro h i ha
    exact (mem_sublevel_iff_list ys hy b _).mp
      (h _ ((mem_sublevel_iff_list xs hx a _).mpr ⟨i, rfl, ha⟩))

/-- The existing semantic vertex map, supplied by the finite check. -/
def validatedVertexMap (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (a b : ℤ) (f : ℕ → ℕ) (h : VertexMapCondition xs ys a b f) :
    VertexMap ((gradeFilter xs hx).sublevel a) ((gradeFilter ys hy).sublevel b) where
  toFun := f
  map_face := by
    intro s hs
    have he : @Finset.image ℕ ℕ (Classical.decEq ℕ) f s = s.image f := by
      ext x
      simp only [Finset.mem_image]
    rw [he]
    exact (vertexMapCondition_iff xs ys hx hy a b f).mp h s hs

/-- Original-face chain matrix: unselected or collapsed source columns are zero. -/
def vertexMatrix (xs ys : Input) (a : ℤ) (f : ℕ → ℕ) :
    Matrix (Fin ys.length) (Fin xs.length) (ZMod 2) := fun i j =>
  if (xs.get j).2 ≤ a ∧ ((xs.get j).1.image f).card = (xs.get j).1.card ∧
      (ys.get i).1 = (xs.get j).1.image f then 1 else 0

/-- Sum all original source coefficients, including coincident image faces. -/
def vertexVector (xs ys : Input) (a : ℤ) (f : ℕ → ℕ)
    (v : Fin xs.length → ZMod 2) : Fin ys.length → ZMod 2 :=
  (vertexMatrix xs ys a f).mulVec v

theorem vertexMapCondition_id (xs : Input) (a b : ℤ) (hab : a ≤ b) :
    VertexMapCondition xs xs a b id := by
  intro i hi
  exact ⟨i, by simp, hi.trans hab⟩

theorem vertexMapCondition_comp (xs ys zs : Input) (a b c : ℤ) (f g : ℕ → ℕ)
    (hf : VertexMapCondition xs ys a b f) (hg : VertexMapCondition ys zs b c g) :
    VertexMapCondition xs zs a c (g ∘ f) := by
  intro i hi
  obtain ⟨j, hj, hb⟩ := hf i hi
  obtain ⟨k, hk, hc⟩ := hg j hb
  refine ⟨k, ?_, hc⟩
  rw [hk, hj, Finset.image_image]

theorem vertexMatrix_apply (xs ys : Input) (a : ℤ) (f : ℕ → ℕ)
    (i : Fin ys.length) (j : Fin xs.length) :
    vertexMatrix xs ys a f i j =
      if (xs.get j).2 ≤ a ∧ ((xs.get j).1.image f).card = (xs.get j).1.card ∧
          (ys.get i).1 = (xs.get j).1.image f then 1 else 0 := rfl

end TDA.Persistence.Reduction.FiniteInput
