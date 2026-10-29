import TDA.Persistence.RealCoordinates
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max

/-!
# Finite coordinate grids

Each direction has a finite set of real values. Their product includes
into real coordinate space with its coordinatewise preorder category.
-/

set_option autoImplicit false

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence

/-- A finite set of real coordinate values in each direction. -/
abbrev CoordinateGrid (n : ℕ) := Fin n → Finset ℝ

namespace CoordinateGrid

variable {n : ℕ} (G : CoordinateGrid n)

/-- The finite product of the selected coordinate sets, with coordinatewise order. -/
abbrev Point := ∀ i : Fin n, {x : ℝ // x ∈ G i}

noncomputable instance pointFintype : Fintype G.Point := by
  classical
  unfold Point
  infer_instance

/-- The actual inclusion of the product grid into real coordinate space. -/
def embedding : G.Point ↪o (Fin n → ℝ) where
  toFun x i := (x i).val
  inj' := by
    intro x y h
    funext i
    exact Subtype.ext (congrFun h i)
  map_rel_iff' := Iff.rfl

/-- Grid inclusion reads the selected coordinate value. -/
@[simp] theorem embedding_apply (p : G.Point) (i : Fin n) : G.embedding p i = (p i).val := rfl

/-- A real grade has a grid point below it. -/
def HasLowerPoint (a : Fin n → ℝ) : Prop := ∃ p : G.Point, G.embedding p ≤ a

/-- Having a lower grid point is preserved by increasing the real grade. -/
theorem hasLowerPoint_mono {a b : Fin n → ℝ} (hab : a ≤ b) (ha : G.HasLowerPoint a) :
    G.HasLowerPoint b := ha.imp (fun _ hp => hp.trans hab)

private theorem coordinateBelow_nonempty (a : Fin n → ℝ) (ha : G.HasLowerPoint a) (i : Fin n) :
    ((G i).filter (fun x => x ≤ a i)).Nonempty := by
  classical
  obtain ⟨p, hp⟩ := ha
  exact ⟨(p i).val, Finset.mem_filter.mpr ⟨(p i).property, hp i⟩⟩

/-- The coordinatewise greatest grid point below a grade where one exists. -/
noncomputable def floor (a : Fin n → ℝ) (ha : G.HasLowerPoint a) : G.Point := by
  classical
  exact fun i => ⟨((G i).filter (fun x => x ≤ a i)).max' (coordinateBelow_nonempty G a ha i),
    (Finset.mem_filter.mp (Finset.max'_mem _ (coordinateBelow_nonempty G a ha i))).1⟩

/-- The constructed floor actually lies below the original grade. -/
theorem floor_le (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    G.embedding (G.floor a ha) ≤ a := by
  classical
  intro i
  exact (Finset.mem_filter.mp (Finset.max'_mem _ (coordinateBelow_nonempty G a ha i))).2

/-- Every grid point below the grade lies below the constructed floor. -/
theorem le_floor (a : Fin n → ℝ) (ha : G.HasLowerPoint a) {p : G.Point}
    (hp : G.embedding p ≤ a) : p ≤ G.floor a ha := by
  classical
  intro i
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨(p i).property, hp i⟩)

/-- The floor is the greatest grid point below a real grade. -/
theorem le_floor_iff (a : Fin n → ℝ) (ha : G.HasLowerPoint a) (p : G.Point) :
    G.embedding p ≤ a ↔ p ≤ G.floor a ha := by
  constructor
  · exact G.le_floor a ha
  · intro hp
    exact (G.embedding.monotone hp).trans (G.floor_le a ha)

/-- A grid point is the floor exactly when it is greatest among the lower points. -/
theorem floor_eq_iff (a : Fin n → ℝ) (ha : G.HasLowerPoint a) (p : G.Point) :
    G.floor a ha = p ↔ G.embedding p ≤ a ∧ ∀ q : G.Point, G.embedding q ≤ a → q ≤ p := by
  constructor
  · rintro rfl
    exact ⟨G.floor_le a ha, fun _ hq => G.le_floor a ha hq⟩
  · intro h
    exact le_antisymm (h.2 _ (G.floor_le a ha)) (G.le_floor a ha h.1)

/-- Floors are monotone on the region with lower grid points. -/
theorem floor_mono {a b : Fin n → ℝ} (hab : a ≤ b)
    (ha : G.HasLowerPoint a) (hb : G.HasLowerPoint b) : G.floor a ha ≤ G.floor b hb :=
  G.le_floor b hb ((G.floor_le a ha).trans hab)

end CoordinateGrid

/-- Select the coordinatewise preorder category on a finite product grid. -/
scoped instance (priority := 10000) coordinateGridPreorderCategory {n : ℕ}
    (G : CoordinateGrid n) : SmallCategory G.Point := Preorder.smallCategory _

open scoped TDA.Persistence

end TDA.Persistence
