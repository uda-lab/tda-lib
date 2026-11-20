import TDA.Persistence.RankErosionGrid
import TDA.Persistence.Reduction.F2MatrixRank
import Mathlib.Data.Fintype.Pi

/-!
# Executable F₂ matrix representations on rational grids

A `RatGrid` lists finitely many rational values in each coordinate. Its real image is a
`CoordinateGrid`; every point of that grid has a unique rational grade, and the executable
floor of a rational grade is the rational grade of the real floor.

An `F2GridRep` adds a fiber dimension for each rational grade and an F₂ matrix for each pair
of rational grades. Only their values at grid grades, and at comparable pairs of them, are
used. `F2GridRep.Valid` is the decidable statement that the matrices are identities on the
diagonal and compose along comparable triples of grid grades. A valid representation defines
an actual module on the grid, with fibers `Fin (dim a) → ZMod 2` and structure maps the stored
matrices.

`F2GridRep.rankAt x y` is the executable rank of the stored matrix between the floors of two
rational grades, or zero when `x` has no lower grid value. `F2GridRep.rankAt_eq` identifies it
with the rank of the actual Kan extension of the grid module between the real grades of `x`
and `y`.

Validation enumerates the comparable triples of grid grades, and each rank is computed by
enumeration of source vectors; no polynomial bound is claimed.
-/

set_option autoImplicit false

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence
open TDA.Persistence.Reduction

/-- Finitely many rational grid values in each coordinate. A list is used as the finite set of
its elements: order and repetitions do not matter. -/
abbrev RatGrid (n : ℕ) := Fin n → List ℚ

namespace RatGrid

variable {n : ℕ}

/-- The real grade of a rational grade. -/
def realGrade (x : Fin n → ℚ) : Fin n → ℝ := fun i => (x i : ℝ)

@[simp] theorem realGrade_apply (x : Fin n → ℚ) (i : Fin n) : realGrade x i = (x i : ℝ) := rfl

theorem realGrade_le_iff {x y : Fin n → ℚ} : realGrade x ≤ realGrade y ↔ x ≤ y :=
  ⟨fun h i => Rat.cast_le.mp (h i), fun h i => Rat.cast_le.mpr (h i)⟩

theorem realGrade_injective : Function.Injective (realGrade (n := n)) :=
  fun _ _ h => funext fun i => Rat.cast_injective (congrFun h i)

variable (V : RatGrid n)

/-- The rational grades of the grid. -/
def points : Finset (Fin n → ℚ) := Fintype.piFinset fun i => (V i).toFinset

theorem mem_points {a : Fin n → ℚ} : a ∈ V.points ↔ ∀ i, a i ∈ V i := by
  simp [points]

/-- The real coordinate grid of the listed values. -/
noncomputable def grid : CoordinateGrid n :=
  fun i => (V i).toFinset.image (fun x : ℚ => (x : ℝ))

theorem mem_grid {i : Fin n} {c : ℝ} : c ∈ V.grid i ↔ ∃ q ∈ V i, (q : ℝ) = c := by
  simp [grid]

/-- The rational grade of a point of the real grid. -/
noncomputable def ratPoint (p : V.grid.Point) : Fin n → ℚ :=
  fun i => Classical.choose (V.mem_grid.mp (p i).property)

theorem ratPoint_mem (p : V.grid.Point) (i : Fin n) : V.ratPoint p i ∈ V i :=
  (Classical.choose_spec (V.mem_grid.mp (p i).property)).1

theorem ratPoint_cast (p : V.grid.Point) (i : Fin n) :
    ((V.ratPoint p i : ℚ) : ℝ) = (p i).val :=
  (Classical.choose_spec (V.mem_grid.mp (p i).property)).2

theorem realGrade_ratPoint (p : V.grid.Point) :
    realGrade (V.ratPoint p) = V.grid.embedding p :=
  funext fun i => V.ratPoint_cast p i

theorem ratPoint_mem_points (p : V.grid.Point) : V.ratPoint p ∈ V.points :=
  V.mem_points.mpr (V.ratPoint_mem p)

theorem ratPoint_le_iff {p q : V.grid.Point} : V.ratPoint p ≤ V.ratPoint q ↔ p ≤ q := by
  rw [← realGrade_le_iff, V.realGrade_ratPoint, V.realGrade_ratPoint]
  exact V.grid.embedding.le_iff_le

/-- The point of the real grid at a rational grid grade. -/
noncomputable def pointOfRat (a : Fin n → ℚ) (ha : a ∈ V.points) : V.grid.Point :=
  fun i => ⟨(a i : ℝ), V.mem_grid.mpr ⟨a i, V.mem_points.mp ha i, rfl⟩⟩

theorem embedding_pointOfRat (a : Fin n → ℚ) (ha : a ∈ V.points) :
    V.grid.embedding (V.pointOfRat a ha) = realGrade a := rfl

theorem ratPoint_pointOfRat (a : Fin n → ℚ) (ha : a ∈ V.points) :
    V.ratPoint (V.pointOfRat a ha) = a :=
  realGrade_injective ((V.realGrade_ratPoint _).trans (V.embedding_pointOfRat a ha))

theorem pointOfRat_ratPoint (p : V.grid.Point) :
    V.pointOfRat (V.ratPoint p) (V.ratPoint_mem_points p) = p :=
  V.grid.embedding.injective
    ((V.embedding_pointOfRat _ _).trans (V.realGrade_ratPoint p))

/-- Executable: every coordinate has a listed value below the grade. -/
def hasLower (x : Fin n → ℚ) : Bool := decide (∀ i, ∃ g ∈ V i, g ≤ x i)

/-- Executable: the largest listed value below a rational number, or the number itself when
there is none. -/
def floorCoord (l : List ℚ) (x : ℚ) : ℚ := ((l.filter (· ≤ x)).max?).getD x

/-- Executable floor of a rational grade. -/
def floor (x : Fin n → ℚ) : Fin n → ℚ := fun i => floorCoord (V i) (x i)

theorem floorCoord_spec {l : List ℚ} {x : ℚ} (h : ∃ g ∈ l, g ≤ x) :
    floorCoord l x ∈ l ∧ floorCoord l x ≤ x ∧ ∀ g ∈ l, g ≤ x → g ≤ floorCoord l x := by
  obtain ⟨g, hg, hgx⟩ := h
  have hne : l.filter (· ≤ x) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.mpr ⟨hg, by simpa using hgx⟩)
  obtain ⟨m, hm⟩ : ∃ m, (l.filter (· ≤ x)).max? = some m := by
    cases hmax : (l.filter (· ≤ x)).max? with
    | none => exact absurd (List.max?_eq_none_iff.mp hmax) hne
    | some m => exact ⟨m, rfl⟩
  have hmem := List.mem_filter.mp (List.max?_mem hm)
  have hval : floorCoord l x = m := by simp [floorCoord, hm]
  rw [hval]
  refine ⟨hmem.1, by simpa using hmem.2, fun g' hg' hg'x => ?_⟩
  exact (List.max?_le_iff hm).mp le_rfl g' (List.mem_filter.mpr ⟨hg', by simpa using hg'x⟩)

theorem hasLower_iff (x : Fin n → ℚ) : V.hasLower x = true ↔ ∀ i, ∃ g ∈ V i, g ≤ x i := by
  simp [hasLower]

theorem hasLowerPoint_realGrade_iff (x : Fin n → ℚ) :
    V.grid.HasLowerPoint (realGrade x) ↔ V.hasLower x = true := by
  rw [CoordinateGrid.hasLowerPoint_iff, hasLower_iff]
  refine forall_congr' fun i => ⟨?_, ?_⟩
  · rintro ⟨c, hc, hle⟩
    obtain ⟨q, hq, rfl⟩ := V.mem_grid.mp hc
    exact ⟨q, hq, Rat.cast_le.mp hle⟩
  · rintro ⟨q, hq, hle⟩
    exact ⟨(q : ℝ), V.mem_grid.mpr ⟨q, hq, rfl⟩, Rat.cast_le.mpr hle⟩

theorem floor_mem_points {x : Fin n → ℚ} (hx : V.hasLower x = true) : V.floor x ∈ V.points :=
  V.mem_points.mpr fun i => (floorCoord_spec ((V.hasLower_iff x).mp hx i)).1

/-- The executable floor is the rational grade of the real floor. -/
theorem ratPoint_floor (x : Fin n → ℚ) (hx : V.grid.HasLowerPoint (realGrade x)) :
    V.ratPoint (V.grid.floor (realGrade x) hx) = V.floor x := by
  funext i
  have hspec := floorCoord_spec ((V.hasLower_iff x).mp ((V.hasLowerPoint_realGrade_iff x).mp hx) i)
  apply Rat.cast_injective (α := ℝ)
  rw [V.ratPoint_cast]
  apply le_antisymm
  · have hle : (V.grid.floor (realGrade x) hx i).val ≤ (x i : ℝ) :=
      V.grid.floor_le (realGrade x) hx i
    rw [← V.ratPoint_cast] at hle ⊢
    exact Rat.cast_le.mpr (hspec.2.2 _ (V.ratPoint_mem _ i) (Rat.cast_le.mp hle))
  · exact (V.grid.le_floor_apply_iff (realGrade x) hx
      (V.mem_grid.mpr ⟨_, hspec.1, rfl⟩)).mpr (Rat.cast_le.mpr hspec.2.1)

end RatGrid

/-- An executable F₂ representation on a rational coordinate grid: a fiber dimension for each
rational grade and a matrix for each pair of rational grades. Only the values at grid grades
and at comparable pairs of them are used. -/
structure F2GridRep (n : ℕ) where
  /-- The grid values in each coordinate. -/
  values : RatGrid n
  /-- The fiber dimension at a rational grade. -/
  dim : (Fin n → ℚ) → ℕ
  /-- The matrix of the structure map between two rational grades. -/
  map : (a b : Fin n → ℚ) → Matrix (Fin (dim b)) (Fin (dim a)) (ZMod 2)

namespace F2GridRep

open RatGrid

variable {n : ℕ} (R : F2GridRep n)

/-- Identity on the diagonal and composition along comparable triples of grid grades. -/
def Valid : Prop :=
  (∀ a ∈ R.values.points, R.map a a = 1) ∧
    ∀ a ∈ R.values.points, ∀ b ∈ R.values.points, ∀ c ∈ R.values.points, a ≤ b → b ≤ c →
      R.map b c * R.map a b = R.map a c

instance : Decidable R.Valid := by
  unfold Valid
  infer_instance

/-- The real coordinate grid of the representation. -/
noncomputable abbrev grid : CoordinateGrid n := R.values.grid

/-- The actual module on the grid: fibers `Fin (dim a) → ZMod 2`, structure maps the stored
matrices. -/
noncomputable def toModule (h : R.Valid) : PModule.{0,0,0} (ZMod 2) R.grid.Point where
  obj p := ModuleCat.of (ZMod 2) (Fin (R.dim (R.values.ratPoint p)) → ZMod 2)
  map {p q} _ := ModuleCat.ofHom (R.map (R.values.ratPoint p) (R.values.ratPoint q)).mulVecLin
  map_id p := by
    ext1
    simp [h.1 _ (R.values.ratPoint_mem_points p)]
  map_comp {p q r} f g := by
    ext1
    rw [← h.2 _ (R.values.ratPoint_mem_points p) _ (R.values.ratPoint_mem_points q) _
      (R.values.ratPoint_mem_points r) (R.values.ratPoint_le_iff.mpr (leOfHom f))
      (R.values.ratPoint_le_iff.mpr (leOfHom g)), Matrix.mulVecLin_mul]
    rfl

theorem toModule_obj (h : R.Valid) (p : R.grid.Point) :
    (R.toModule h).obj p =
      ModuleCat.of (ZMod 2) (Fin (R.dim (R.values.ratPoint p)) → ZMod 2) := rfl

/-- The structure maps of the grid module are the stored matrices. -/
theorem structureMapLinear_toModule (h : R.Valid) {p q : R.grid.Point} (hpq : p ≤ q) :
    structureMapLinear (R.toModule h) hpq =
      (R.map (R.values.ratPoint p) (R.values.ratPoint q)).mulVecLin := rfl

/-- The fibers of the grid module are finite-dimensional. -/
instance finiteDimensional_toModule_obj (h : R.Valid) (p : R.grid.Point) :
    FiniteDimensional (ZMod 2) ((R.toModule h).obj p) :=
  inferInstanceAs (FiniteDimensional (ZMod 2) (Fin (R.dim (R.values.ratPoint p)) → ZMod 2))

/-- On the grid, the rank of a structure map is the executed rank of its matrix. -/
theorem rankOfStructureMap_toModule (h : R.Valid) {p q : R.grid.Point} (hpq : p ≤ q) :
    rankOfStructureMap (R.toModule h) hpq =
      F2Matrix.rank (R.map (R.values.ratPoint p) (R.values.ratPoint q)) := by
  rw [F2Matrix.rank_eq_finrank_range]
  rfl

/-- Executable rank of the extension between two rational grades: the rank of the stored
matrix between their floors, or zero when the source grade has no lower grid value. -/
def rankAt (x y : Fin n → ℚ) : ℕ :=
  if R.values.hasLower x then F2Matrix.rank (R.map (R.values.floor x) (R.values.floor y)) else 0

private theorem rank_map_congr {a a' b b' : Fin n → ℚ} (ha : a = a') (hb : b = b') :
    F2Matrix.rank (R.map a b) = F2Matrix.rank (R.map a' b') := by
  subst ha
  subst hb
  rfl

/-- The executable rank is the rank of the actual Kan extension of the grid module between
the real grades. -/
theorem rankAt_eq (h : R.Valid) {x y : Fin n → ℚ} (hxy : x ≤ y) :
    R.rankAt x y =
      rankOfStructureMap (R.grid.lan.obj (R.toModule h)) (realGrade_le_iff.mpr hxy) := by
  by_cases hl : R.grid.HasLowerPoint (realGrade x)
  · have hlow : R.values.hasLower x = true := (R.values.hasLowerPoint_realGrade_iff x).mp hl
    have hly := R.grid.hasLowerPoint_mono (realGrade_le_iff.mpr hxy) hl
    rw [CoordinateGrid.rankOfStructureMap_lan _ _ _ hl, rankOfStructureMap_toModule, rankAt]
    simp only [hlow, ↓reduceIte]
    exact (R.rank_map_congr (R.values.ratPoint_floor x hl) (R.values.ratPoint_floor y hly)).symm
  · have hlow : R.values.hasLower x = false :=
      Bool.eq_false_iff.mpr fun hx => hl ((R.values.hasLowerPoint_realGrade_iff x).mpr hx)
    rw [CoordinateGrid.rankOfStructureMap_lan_eq_zero _ _ _ hl, rankAt]
    simp only [hlow, Bool.false_eq_true, ↓reduceIte]

/-- The executable rank read at arbitrary real grades equal to the real grades of two rational
grades. -/
theorem rankAt_eq_of_eq (h : R.Valid) {x y : Fin n → ℚ} {a b : Fin n → ℝ}
    (ha : realGrade x = a) (hb : realGrade y = b) (hab : a ≤ b) :
    R.rankAt x y = rankOfStructureMap (R.grid.lan.obj (R.toModule h)) hab := by
  subst ha
  subst hb
  exact R.rankAt_eq h (realGrade_le_iff.mp hab)

end F2GridRep

end TDA.Persistence
