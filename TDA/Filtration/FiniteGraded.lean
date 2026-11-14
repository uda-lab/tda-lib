import TDA.Simplicial.FiniteComplex
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
# Finite simplicial complexes with coordinate grades

A `FiniteGraded C n` assigns a vector in `ℝⁿ` to each nonempty face of the finite
complex `C`. Face inclusion increases grades in the coordinatewise order. Its
sublevels retain exactly the original faces with grade at most the index.
Repeated grades, empty complexes, and zero coordinates require no extra choices.
-/

namespace TDA.Filtration

open TDA.Simplicial

/-- Coordinate grades on the actual faces of a finite complex, monotone under
face inclusion. No homological or presentation data is part of the input. -/
structure FiniteGraded {m : ℕ} (C : FiniteComplex m) (n : ℕ) where
  grade : TotalFace C.toPre → (Fin n → ℝ)
  mono : ∀ {s t : TotalFace C.toPre}, s.val ⊆ t.val → grade s ≤ grade t

namespace FiniteGraded

variable {m n : ℕ} {C : FiniteComplex m}

/-- Equality of the grade assignment determines the graded input. -/
@[ext]
theorem ext {g h : FiniteGraded C n} (he : ∀ s, g.grade s = h.grade s) : g = h := by
  cases g with
  | mk gg gm =>
    cases h with
    | mk hg hm =>
      have heq : gg = hg := funext he
      cases heq
      rfl

/-- The faces present at the coordinate threshold `a`. -/
def sublevel (g : FiniteGraded C n) (a : Fin n → ℝ) :
    PreAbstractSimplicialComplex (Fin m) where
  faces := {s | ∃ hs : s ∈ C.toPre, g.grade ⟨s, hs⟩ ≤ a}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsa⟩
    refine ⟨(C.toPre.isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    have htC : t ∈ C.toPre := (C.toPre.isRelLowerSet_faces hs).2 hts ht
    exact ⟨htC, (g.mono (s := ⟨t, htC⟩) (t := ⟨s, hs⟩) hts).trans hsa⟩

/-- Sublevel membership records both the original face and its grade bound. -/
theorem mem_sublevel_iff (g : FiniteGraded C n) (a : Fin n → ℝ)
    (s : Finset (Fin m)) :
    s ∈ g.sublevel a ↔ ∃ hs : s ∈ C.toPre, g.grade ⟨s, hs⟩ ≤ a := Iff.rfl

/-- For an existing face, membership is exactly the coordinate grade bound. -/
@[simp]
theorem mem_sublevel_iff_of_mem (g : FiniteGraded C n) (a : Fin n → ℝ)
    (s : TotalFace C.toPre) :
    s.val ∈ g.sublevel a ↔ g.grade s ≤ a := by
  constructor
  · rintro ⟨hs, h⟩
    exact h
  · intro h
    exact ⟨s.property, h⟩

/-- A sublevel never inserts faces outside the finite input complex. -/
theorem sublevel_le (g : FiniteGraded C n) (a : Fin n → ℝ) :
    g.sublevel a ≤ C.toPre := by
  rintro s ⟨hs, _⟩
  exact hs

/-- Increasing every coordinate of the threshold can only add faces. -/
theorem sublevel_mono (g : FiniteGraded C n) : Monotone g.sublevel := by
  intro a b hab s hs
  obtain ⟨hsC, hsa⟩ := hs
  exact ⟨hsC, hsa.trans hab⟩

/-- The sublevels as the existing support-aware simplicial filtration. -/
def sublevelFiltration (g : FiniteGraded C n) :
    SimplicialFiltration (Fin n → ℝ) (Fin m) where
  toFun := g.sublevel
  monotone' := g.sublevel_mono

/-- Evaluation of the sublevel filtration is the corresponding subcomplex. -/
@[simp]
theorem sublevelFiltration_apply (g : FiniteGraded C n) (a : Fin n → ℝ) :
    g.sublevelFiltration a = g.sublevel a := rfl

/-- Thresholds yielding the same grade bounds yield the same subcomplex. -/
theorem sublevel_eq_of_forall_le_iff (g : FiniteGraded C n)
    {a b : Fin n → ℝ}
    (h : ∀ s : TotalFace C.toPre, g.grade s ≤ a ↔ g.grade s ≤ b) :
    g.sublevel a = g.sublevel b := by
  apply le_antisymm
  · rintro s ⟨hs, hsa⟩
    exact ⟨hs, (h ⟨s, hs⟩).mp hsa⟩
  · rintro s ⟨hs, hsb⟩
    exact ⟨hs, (h ⟨s, hs⟩).mpr hsb⟩

/-- A sublevel is empty exactly when no input face satisfies its grade bound. -/
theorem sublevel_eq_bot_iff (g : FiniteGraded C n) (a : Fin n → ℝ) :
    g.sublevel a = ⊥ ↔ ∀ s : TotalFace C.toPre, ¬ g.grade s ≤ a := by
  constructor
  · intro he s hs
    have hm := (g.mem_sublevel_iff_of_mem a s).mpr hs
    rw [he] at hm
    exact hm
  · intro h
    apply le_antisymm
    · rintro s ⟨hs, hsa⟩
      exact (h ⟨s, hs⟩ hsa).elim
    · exact bot_le

/-- Once every face has entered, the sublevel is the input complex. -/
theorem sublevel_eq_self_of_forall_le (g : FiniteGraded C n) (a : Fin n → ℝ)
    (h : ∀ s : TotalFace C.toPre, g.grade s ≤ a) :
    g.sublevel a = C.toPre := by
  apply le_antisymm (g.sublevel_le a)
  intro s hs
  exact ⟨hs, h ⟨s, hs⟩⟩

/-- With no coordinates every input face satisfies every threshold. -/
theorem sublevel_zero_coordinates (g : FiniteGraded C 0) (a : Fin 0 → ℝ) :
    g.sublevel a = C.toPre := by
  apply g.sublevel_eq_self_of_forall_le a
  intro s i
  exact Fin.elim0 i

end FiniteGraded
end TDA.Filtration
