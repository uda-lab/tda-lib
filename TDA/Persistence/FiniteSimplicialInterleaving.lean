import TDA.Persistence.SublevelInterleaving
import TDA.Persistence.CoordinateInterleavingDistance
import TDA.Persistence.FiniteSimplicial

/-!
# Coordinate perturbations of finite simplicial filtrations

Shifted inclusions induce coordinate interleavings through the actual
inclusion maps on simplicial homology, in every homological degree.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration CoordinateShift
open scoped NNReal ENNReal

variable {V : Type u} [LinearOrder V] {n : ℕ}
variable (R : Type v) [Ring R] (q : ℕ)

/-- Two coordinate filtrations contained in one another after a diagonal shift
have an inclusion-induced interleaving on homology. -/
noncomputable def coordinateInclusionInterleaving
    {F G : SimplicialFiltration (Fin n → ℝ) V} {δ : ℝ≥0}
    (hFG : ∀ a, F a ≤ G (translation δ a))
    (hGF : ∀ a, G a ≤ F (translation δ a)) :
    CoordinateInterleaving δ (simplicialHomologyPModule R F q)
      (simplicialHomologyPModule R G q) :=
  CoordinateInterleaving.ofStructureMapEquations
    (inclusionHom R q (F := F) (G := Filtration.reindex (translation δ) G) hFG)
    (inclusionHom R q (F := G) (G := Filtration.reindex (translation δ) F) hGF)
    (fun a => by
      change simplicialHomologyIncl R (hFG a) q ≫
          simplicialHomologyIncl R (hGF (translation δ a)) q =
        simplicialHomologyIncl R _ q
      rw [← simplicialHomologyIncl_comp])
    (fun a => by
      change simplicialHomologyIncl R (hGF a) q ≫
          simplicialHomologyIncl R (hFG (translation δ a)) q =
        simplicialHomologyIncl R _ q
      rw [← simplicialHomologyIncl_comp])

/-- The forward component is the homology map of the shifted inclusion. -/
@[simp] theorem coordinateInclusionInterleaving_φ_app
    {F G : SimplicialFiltration (Fin n → ℝ) V} {δ : ℝ≥0}
    (hFG : ∀ a, F a ≤ G (translation δ a))
    (hGF : ∀ a, G a ≤ F (translation δ a)) (a : Fin n → ℝ) :
    (coordinateInclusionInterleaving R q hFG hGF).φ.app a =
      simplicialHomologyIncl R (hFG a) q := rfl

/-- The reverse component is the homology map of the reverse shifted inclusion. -/
@[simp] theorem coordinateInclusionInterleaving_ψ_app
    {F G : SimplicialFiltration (Fin n → ℝ) V} {δ : ℝ≥0}
    (hFG : ∀ a, F a ≤ G (translation δ a))
    (hGF : ∀ a, G a ≤ F (translation δ a)) (a : Fin n → ℝ) :
    (coordinateInclusionInterleaving R q hFG hGF).ψ.app a =
      simplicialHomologyIncl R (hGF a) q := rfl

end TDA.Persistence

namespace TDA.Filtration.FiniteGraded

open TDA.Simplicial TDA.Persistence.CoordinateShift
open scoped NNReal

variable {m n : ℕ} {C : FiniteComplex m}

/-- A one-sided grade bound induces an inclusion into the shifted sublevel. -/
theorem sublevel_le_translation (g h : FiniteGraded C n) {δ : ℝ≥0}
    (hgrade : ∀ s i, h.grade s i ≤ g.grade s i + (δ : ℝ)) (a : Fin n → ℝ) :
    g.sublevel a ≤ h.sublevel (translation δ a) := by
  intro s hs
  obtain ⟨hsC, hsa⟩ := (g.mem_sublevel_iff a s).mp hs
  apply (h.mem_sublevel_iff _ s).mpr
  refine ⟨hsC, ?_⟩
  intro i
  exact (hgrade ⟨s, hsC⟩ i).trans (add_le_add (hsa i) le_rfl)

/-- A coordinatewise absolute grade error gives the shifted sublevel inclusion. -/
theorem sublevel_le_translation_of_error (g h : FiniteGraded C n) {δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) (a : Fin n → ℝ) :
    g.sublevel a ≤ h.sublevel (translation δ a) :=
  sublevel_le_translation g h (fun s i => by
    have hb := (abs_sub_le_iff.mp (herror s i)).2
    linarith) a

/-- The largest absolute coordinate grade error over all faces and coordinates.
The maximum is zero when either index set is empty; repeated grades are allowed. -/
noncomputable def supGradeError (g h : FiniteGraded C n) : ℝ≥0 := by
  classical
  exact Finset.univ.sup (fun p : TotalFace C.toPre × Fin n =>
    Real.toNNReal |g.grade p.1 p.2 - h.grade p.1 p.2|)

/-- The finite maximum bounds exactly the coordinatewise absolute errors. -/
theorem supGradeError_le_iff (g h : FiniteGraded C n) (δ : ℝ≥0) :
    supGradeError g h ≤ δ ↔ ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ) := by
  classical
  simp only [supGradeError, Finset.sup_le_iff, Finset.mem_univ, forall_const,
    Prod.forall, Real.toNNReal_le_iff_le_coe]

/-- Every coordinate error is bounded by the finite maximum. -/
theorem abs_grade_sub_le_supGradeError (g h : FiniteGraded C n)
    (s : TotalFace C.toPre) (i : Fin n) :
    |g.grade s i - h.grade s i| ≤ (supGradeError g h : ℝ) :=
  (supGradeError_le_iff g h _).mp le_rfl s i

/-- Equal grade assignments have zero maximal error. -/
@[simp] theorem supGradeError_self (g : FiniteGraded C n) :
    supGradeError g g = 0 := by
  classical
  simp [supGradeError]

/-- The maximal error is independent of the order of the two assignments. -/
theorem supGradeError_comm (g h : FiniteGraded C n) :
    supGradeError g h = supGradeError h g := by
  classical
  simp only [supGradeError, abs_sub_comm]

/-- An empty face set has zero maximal grade error. -/
@[simp] theorem supGradeError_of_isEmpty (g h : FiniteGraded C n)
    [IsEmpty (TotalFace C.toPre)] : supGradeError g h = 0 := by
  classical
  simp [supGradeError]

/-- There is no coordinate error in dimension zero. -/
@[simp] theorem supGradeError_zero_coordinates (g h : FiniteGraded C 0) :
    supGradeError g h = 0 := by
  classical
  simp [supGradeError]

end TDA.Filtration.FiniteGraded

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration CoordinateShift
open scoped NNReal ENNReal

variable {m n : ℕ} {C : FiniteComplex m}
variable (k : Type u) [Field k]

/-- Coordinatewise grade errors induce an interleaving of the actual simplicial
homology modules, for every degree and coefficient field. -/
noncomputable def finiteSimplicialHomology_interleaving
    (g h : FiniteGraded C n) (q : ℕ) {δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) :
    CoordinateInterleaving δ (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q) :=
  coordinateInclusionInterleaving k q
    (g.sublevel_le_translation_of_error h herror)
    (h.sublevel_le_translation_of_error g (fun s i => by
      simpa only [abs_sub_comm] using herror s i))

/-- The forward interleaving component is induced by the shifted sublevel inclusion. -/
@[simp] theorem finiteSimplicialHomology_interleaving_φ_app
    (g h : FiniteGraded C n) (q : ℕ) {δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) (a : Fin n → ℝ) :
    (finiteSimplicialHomology_interleaving k g h q herror).φ.app a =
      simplicialHomologyIncl k (g.sublevel_le_translation_of_error h herror a) q := rfl

/-- The reverse interleaving component is induced by the reverse shifted inclusion. -/
@[simp] theorem finiteSimplicialHomology_interleaving_ψ_app
    (g h : FiniteGraded C n) (q : ℕ) {δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) (a : Fin n → ℝ) :
    (finiteSimplicialHomology_interleaving k g h q herror).ψ.app a =
      simplicialHomologyIncl k (h.sublevel_le_translation_of_error g (fun s i => by
        simpa only [abs_sub_comm] using herror s i) a) q := rfl

/-- The coordinate interleaving distance is bounded by any coordinatewise grade error. -/
theorem coordinateInterleavingDistance_finiteSimplicialHomology_le
    (g h : FiniteGraded C n) (q : ℕ) {δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) :
    coordinateInterleavingDistance (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q) ≤ δ :=
  (finiteSimplicialHomology_interleaving k g h q herror).distance_le

/-- The actual finite maximal grade error bounds the coordinate interleaving distance. -/
theorem coordinateInterleavingDistance_finiteSimplicialHomology_le_supGradeError
    (g h : FiniteGraded C n) (q : ℕ) :
    coordinateInterleavingDistance (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q) ≤ g.supGradeError h :=
  coordinateInterleavingDistance_finiteSimplicialHomology_le k g h q
    (g.abs_grade_sub_le_supGradeError h)

end TDA.Persistence
