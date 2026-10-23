import TDA.Mapper.RefinementHomologyDiagram
import TDA.Mapper.RefinementHomologyLowerBound
import TDA.Simplicial.H0Augmentation

/-!
# Tightness of the step-tower bounds

Let `f : C(X, Y)` be continuous, let `c : Fin m ↪o ℝ` be a grid, and let `cover i`, `r`,
component orders and `n` be step data as in `TDA.Mapper.RefinementHomologyDiagram`, with an
empty initial family. The rank obstructions to real interleavings of Mapper homology modules
(`TDA.Mapper.RefinementHomologyLowerBound`) apply to two step modules and, through
`bottleneck_stepMapperDiagram_eq`, bound the bottleneck distance of two step diagrams from
below. They are stated for the stage of the second tower at radius `t + ε`.

The step tower on `shiftGrid ε c` is the step tower on `c` moved earlier by `ε`:
`cellIndex_shiftGrid` identifies the stage at radius `t` of the former with the stage at
`t + ε` of the latter. The selected refinements between the two stage families are cover maps
shifting by `ε` in both directions, so the bottleneck distance of the two step diagrams is at
most `ε`.

If the homology map of the selected refinement from the first nonempty stage to the last stage
is nonzero in degree `n`, the distance is exactly `ε`, both for the diagrams and for the
modules. Over a vertex of the first nonempty stage the degree-`0` map is nonzero, so the
hypothesis holds in degree `0` whenever the first nonempty stage has a vertex. The bottleneck
distance of two step diagrams is infinite exactly when their numbers of essential bars differ.

The hypothesis on the last stage cannot be dropped; the fixtures give a degree-`1` example in
which the translated diagrams are at distance strictly less than the shift. Nothing is claimed
about exact distances for pairs of grids that are not translates, about bar-length lower
bounds, about the bound `≤ η` beyond translations, or about multinerve Mapper.
-/

namespace TDA.Mapper

open CategoryTheory CategoryTheory.Limits
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence
open TDA.Persistence.FiniteConstructible
open scoped NNReal ENNReal

noncomputable section

universe u v w c

/-! ## Lower bounds for the bottleneck distance -/

section LowerBound

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (k : Type u) [Field k] (f : C(X, Y)) (n : ℕ)
variable {m : ℕ} {c : Fin m ↪o ℝ} {Index : Fin (m + 1) → Type u}
  {cover : (i : Fin (m + 1)) → Index i → Set Y}
  [∀ i, LinearOrder (ComponentIndex f (cover i))] [∀ i, Finite (Face (mapper f (cover i)) n)]
  [IsEmpty (Index 0)]
  (r : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j))
variable {m' : ℕ} {d : Fin m' ↪o ℝ} {Index' : Fin (m' + 1) → Type u}
  {cover' : (i : Fin (m' + 1)) → Index' i → Set Y}
  [∀ i, LinearOrder (ComponentIndex f (cover' i))] [∀ i, Finite (Face (mapper f (cover' i)) n)]
  [IsEmpty (Index' 0)]
  (r' : ∀ {i j : Fin (m' + 1)}, i ≤ j → Refinement (cover' i) (cover' j))

/-- If for every finite `ε < ρ` some homology map of a selected refinement of the first tower
from radius `t` to radius `t + 2ε` has rank larger than the dimension of the finite-dimensional
homology of the second tower's stage at `t + ε`, then the bottleneck distance of the two step
diagrams is at least `ρ`. -/
theorem le_bottleneck_stepMapperDiagram_of_finrank_lt {ρ : ℝ≥0∞}
    (hρ : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < ρ → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      FiniteDimensional k
          (simplicialHomology (mapper f (cover' (cellIndex d (t + ε)))) k n) ∧
        Module.finrank k (simplicialHomology (mapper f (cover' (cellIndex d (t + ε)))) k n) <
          Module.finrank k (LinearMap.range
            (mapperHomologyMap k f (r ((cellIndex c).monotone h)) n).hom)) :
    ρ ≤ bottleneck (stepMapperDiagram k f c cover r n) (stepMapperDiagram k f d cover' r' n) := by
  rw [bottleneck_stepMapperDiagram_eq]
  exact le_realInterleavingDistance_mapperHomologyPModule_of_finrank_lt k
    (stepRefinement c cover r) (stepRefinement d cover' r') n hρ

/-- If for every finite `ε < ρ` the stage of the second tower at `t + ε` has no `n`-faces while
the homology map of a selected refinement of the first tower from radius `t` to radius
`t + 2ε` is nonzero, then the bottleneck distance of the two step diagrams is at least `ρ`. -/
theorem le_bottleneck_stepMapperDiagram_of_isEmpty_face {ρ : ℝ≥0∞}
    (hρ : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < ρ → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      IsEmpty (Face (mapper f (cover' (cellIndex d (t + ε)))) n) ∧
        mapperHomologyMap k f (r ((cellIndex c).monotone h)) n ≠ 0) :
    ρ ≤ bottleneck (stepMapperDiagram k f c cover r n) (stepMapperDiagram k f d cover' r' n) := by
  rw [bottleneck_stepMapperDiagram_eq]
  exact le_realInterleavingDistance_mapperHomologyPModule_of_isEmpty_face k
    (stepRefinement c cover r) (stepRefinement d cover' r') n hρ

/-- If for every finite `ε < ρ` the second step module vanishes at some radius `t + ε` while the
first has a nonzero structure map from `t` to `t + 2ε`, then the bottleneck distance of the two
step diagrams is at least `ρ`. -/
theorem le_bottleneck_stepMapperDiagram_of_structureMap_ne_zero {ρ : ℝ≥0∞}
    (hρ : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < ρ → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      Subsingleton ((mapperHomologyPModule k f (stepTower d cover')
        (stepRefinement d cover' r') n).obj (t + ε)) ∧
        structureMap (mapperHomologyPModule k f (stepTower c cover)
          (stepRefinement c cover r) n) h ≠ 0) :
    ρ ≤ bottleneck (stepMapperDiagram k f c cover r n) (stepMapperDiagram k f d cover' r' n) := by
  rw [bottleneck_stepMapperDiagram_eq]
  exact le_realInterleavingDistance_of_structureMap_ne_zero hρ

omit [∀ i, Finite (Face (mapper f (cover i)) n)] [IsEmpty (Index 0)]
  [∀ i, Finite (Face (mapper f (cover' i)) n)] [IsEmpty (Index' 0)] in
/-- If the stage of the second tower at `t + ε` has no `n`-faces and the homology map of the
selected refinement of the first tower from radius `t` to radius `t + 2ε` is nonzero, then the
two step modules are not `ε`-interleaved. -/
theorem isEmpty_realInterleaving_stepTower_of_isEmpty_face {ε : ℝ≥0} (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ))
    [IsEmpty (Face (mapper f (cover' (cellIndex d (t + ε)))) n)]
    (hne : mapperHomologyMap k f (r ((cellIndex c).monotone h)) n ≠ 0) :
    IsEmpty (RealInterleaving ε
      (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n)
      (mapperHomologyPModule k f (stepTower d cover') (stepRefinement d cover' r') n)) :=
  isEmpty_realInterleaving_mapperHomologyPModule_of_isEmpty_face k
    (stepRefinement c cover r) (stepRefinement d cover' r') n t h hne

end LowerBound

/-! ## Translation of the grid -/

section Translation

variable {Y : Type v} {m : ℕ} (c : Fin m ↪o ℝ) {Index : Fin (m + 1) → Type u}
  (cover : (i : Fin (m + 1)) → Index i → Set Y)
  (r : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j)) (ε : ℝ≥0)

/-- The family of the step tower on `shiftGrid ε c` at the radius `t` is the family of the step
tower on `c` at the radius `t + ε`. -/
theorem heq_stepTower_shiftGrid (t : ℝ) :
    HEq (stepTower (shiftGrid ε c) cover t) (stepTower c cover (t + ε)) := by
  unfold stepTower
  rw [cellIndex_shiftGrid]

/-- The selected refinement from the step tower on `c` at the radius `t` to the step tower on
`shiftGrid ε c` at the radius `t + ε`. -/
def stepTowerToShiftGrid (t : ℝ) :
    Refinement (stepTower c cover t) (stepTower (shiftGrid ε c) cover (t + ε)) :=
  r (by
    rw [cellIndex_shiftGrid]
    exact (cellIndex c).monotone (by linarith [ε.coe_nonneg]))

/-- The selected refinement from the step tower on `shiftGrid ε c` at the radius `t` to the
step tower on `c` at the radius `t + ε`: the two stages coincide. -/
def stepTowerOfShiftGrid (t : ℝ) :
    Refinement (stepTower (shiftGrid ε c) cover t) (stepTower c cover (t + ε)) :=
  r (cellIndex_shiftGrid ε c t).le

variable {X : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable (k : Type u) [Field k] (f : C(X, Y)) (n : ℕ)
  [∀ i, LinearOrder (ComponentIndex f (cover i))] [∀ i, Finite (Face (mapper f (cover i)) n)]
  [IsEmpty (Index 0)]

/-- Upper bound for a translated grid: the selected stage refinements are cover maps shifting by
`ε` in both directions. No survival hypothesis is needed; it is the upper half of the exact
distance. -/
theorem bottleneck_stepMapperDiagram_shiftGrid_le :
    bottleneck (stepMapperDiagram k f c cover r n)
        (stepMapperDiagram k f (shiftGrid ε c) cover r n) ≤ ε :=
  bottleneck_stepMapperDiagram_le k f n r r (stepTowerToShiftGrid c cover r ε)
    (stepTowerOfShiftGrid c cover r ε)

end Translation

/-! ## Exact translation distance -/

section Exact

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (k : Type u) [Field k] (f : C(X, Y)) (n : ℕ)
variable {m₀ : ℕ} (c : Fin (m₀ + 1) ↪o ℝ) {Index : Fin (m₀ + 1 + 1) → Type u}
  {cover : (i : Fin (m₀ + 1 + 1)) → Index i → Set Y}
  [∀ i, LinearOrder (ComponentIndex f (cover i))] [∀ i, Finite (Face (mapper f (cover i)) n)]
  [IsEmpty (Index 0)]
  (r : ∀ {i j : Fin (m₀ + 1 + 1)}, i ≤ j → Refinement (cover i) (cover j))

omit [∀ i, Finite (Face (mapper f (cover i)) n)] [IsEmpty (Index 0)] in
/-- Survival: the homology map from the first nonempty stage to the last stage is nonzero. -/
abbrev SurvivesToLast : Prop :=
  mapperHomologyMap k f (r (Fin.le_last (0 : Fin (m₀ + 1)).succ)) n ≠ 0

variable {k f n r}

omit [∀ i, Finite (Face (mapper f (cover i)) n)] [IsEmpty (Index 0)] in
private theorem mapperHomologyMap_ne_zero_of_le {i j l : Fin (m₀ + 1 + 1)} (hij : i ≤ j)
    (hjl : j ≤ l) (hil : i ≤ l) (hne : mapperHomologyMap k f (r hil) n ≠ 0) :
    mapperHomologyMap k f (r hij) n ≠ 0 := fun h0 =>
  hne ((mapperHomologyMap_comp_eq k f (r hij) (r hjl) (r hil) n).symm.trans
    (by rw [h0, zero_comp]))

omit [∀ i, Finite (Face (mapper f (cover i)) n)] in
/-- If the homology map from the first nonempty stage to the last stage is nonzero, then the
real interleaving distance of the step module on `c` and that on `shiftGrid ε c` is at least
`ε`. -/
theorem le_realInterleavingDistance_stepTower_shiftGrid (ε : ℝ≥0) (hsurv : SurvivesToLast k f n r) :
    (ε : ℝ≥0∞) ≤ realInterleavingDistance
      (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n)
      (mapperHomologyPModule k f (stepTower (shiftGrid ε c) cover)
        (stepRefinement (shiftGrid ε c) cover r) n) := by
  rw [realInterleavingDistance_comm]
  refine le_realInterleavingDistance_of_structureMap_ne_zero fun δ hδ => ?_
  have hδε : (δ : ℝ) < ε := by exact_mod_cast ENNReal.coe_lt_coe.1 hδ
  have hδ0 := δ.coe_nonneg
  refine ⟨c 0 - ε, by linarith, ?_, ?_⟩
  · have hz := (isConstructible_stepTower c cover k f r n).zero_left (c 0 - ε + δ)
      (fun i => by linarith [c.monotone (Fin.zero_le i)])
    exact ModuleCat.subsingleton_of_isZero hz
  · have hi : (0 : Fin (m₀ + 1)).succ = cellIndex (shiftGrid ε c) (c 0 - ε) := by
      rw [cellIndex_shiftGrid, sub_add_cancel, cellIndex_critical]
    intro h0
    have key : ∀ i (_ : (0 : Fin (m₀ + 1)).succ = i) (hil : i ≤ Fin.last (m₀ + 1)),
        mapperHomologyMap k f (r hil) n ≠ 0 := by
      rintro i rfl hil
      exact hsurv
    exact mapperHomologyMap_ne_zero_of_le
      ((cellIndex (shiftGrid ε c)).monotone (show c 0 - ε ≤ c 0 - ε + ((δ + δ : ℝ≥0) : ℝ) by
        have := (δ + δ).coe_nonneg
        linarith))
      (Fin.le_last _) (Fin.le_last _) (key _ hi _) h0

/-- If the homology map from the first nonempty stage to the last stage is nonzero, then the
real interleaving distance of the step module on `c` and that on `shiftGrid ε c` is `ε`. -/
theorem realInterleavingDistance_stepTower_shiftGrid_eq (ε : ℝ≥0)
    (hsurv : SurvivesToLast k f n r) :
    realInterleavingDistance
        (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n)
        (mapperHomologyPModule k f (stepTower (shiftGrid ε c) cover)
          (stepRefinement (shiftGrid ε c) cover r) n) = ε := by
  refine le_antisymm ?_ (le_realInterleavingDistance_stepTower_shiftGrid c ε hsurv)
  rw [← bottleneck_stepMapperDiagram_eq]
  exact bottleneck_stepMapperDiagram_shiftGrid_le c cover r ε k f n

/-- If the homology map from the first nonempty stage to the last stage is nonzero, then the
step diagram on `c` and that on `shiftGrid ε c` are at bottleneck distance `ε`. -/
theorem bottleneck_stepMapperDiagram_shiftGrid_eq (ε : ℝ≥0) (hsurv : SurvivesToLast k f n r) :
    bottleneck (stepMapperDiagram k f c cover r n)
        (stepMapperDiagram k f (shiftGrid ε c) cover r n) = ε := by
  rw [bottleneck_stepMapperDiagram_eq]
  exact realInterleavingDistance_stepTower_shiftGrid_eq c ε hsurv

end Exact

/-! ## Degree zero -/

section DegreeZero

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (k : Type u) [Field k] (f : C(X, Y))
variable {m₀ : ℕ} (c : Fin (m₀ + 1) ↪o ℝ) {Index : Fin (m₀ + 1 + 1) → Type u}
  {cover : (i : Fin (m₀ + 1 + 1)) → Index i → Set Y}
  [∀ i, LinearOrder (ComponentIndex f (cover i))] [∀ i, Finite (Face (mapper f (cover i)) 0)]
  [IsEmpty (Index 0)]
  (r : ∀ {i j : Fin (m₀ + 1 + 1)}, i ≤ j → Refinement (cover i) (cover j))

omit [∀ i, Finite (Face (mapper f (cover i)) 0)] [IsEmpty (Index 0)] in
/-- A vertex of the first nonempty stage survives to the last stage in degree `0`. -/
theorem survivesToLast_zero (a : ComponentIndex f (cover (0 : Fin (m₀ + 1)).succ)) :
    SurvivesToLast k f 0 r :=
  mapperHomologyMap_zero_ne_zero k _ a

/-- If the first nonempty stage has a vertex, the degree-`0` step diagrams on `c` and on
`shiftGrid ε c` are at bottleneck distance exactly `ε`. -/
theorem bottleneck_stepMapperDiagram_shiftGrid_eq_zero_degree (ε : ℝ≥0)
    (a : ComponentIndex f (cover (0 : Fin (m₀ + 1)).succ)) :
    bottleneck (stepMapperDiagram k f c cover r 0)
        (stepMapperDiagram k f (shiftGrid ε c) cover r 0) = ε :=
  bottleneck_stepMapperDiagram_shiftGrid_eq c ε (survivesToLast_zero k f r a)

end DegreeZero

/-! ## Infinite distance -/

section Infinite

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (k : Type u) [Field k] (f : C(X, Y)) (n : ℕ)
variable {m : ℕ} {c : Fin m ↪o ℝ} {Index : Fin (m + 1) → Type u}
  {cover : (i : Fin (m + 1)) → Index i → Set Y}
  [∀ i, LinearOrder (ComponentIndex f (cover i))] [∀ i, Finite (Face (mapper f (cover i)) n)]
  [IsEmpty (Index 0)]
  (r : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j))
variable {m' : ℕ} {d : Fin m' ↪o ℝ} {Index' : Fin (m' + 1) → Type u}
  {cover' : (i : Fin (m' + 1)) → Index' i → Set Y}
  [∀ i, LinearOrder (ComponentIndex f (cover' i))] [∀ i, Finite (Face (mapper f (cover' i)) n)]
  [IsEmpty (Index' 0)]
  (r' : ∀ {i j : Fin (m' + 1)}, i ≤ j → Refinement (cover' i) (cover' j))

/-- The bottleneck distance of two step diagrams is infinite exactly when their numbers of
essential bars differ. -/
theorem bottleneck_stepMapperDiagram_eq_top_iff :
    bottleneck (stepMapperDiagram k f c cover r n) (stepMapperDiagram k f d cover' r' n) = ⊤ ↔
      (essentialPart (stepMapperDiagram k f c cover r n).points).card ≠
        (essentialPart (stepMapperDiagram k f d cover' r' n).points).card := by
  rw [bottleneck_stepMapperDiagram_eq]
  exact realInterleavingDistance_stepTower_eq_top_iff k f n r r'

end Infinite

end

end TDA.Mapper
