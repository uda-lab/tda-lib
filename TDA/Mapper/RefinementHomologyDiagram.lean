import TDA.Mapper.RefinementHomologyInterleaving
import TDA.Mapper.RefinementHomologyBarcode
import TDA.Persistence.SublevelConstructible

/-!
# Diagrams of Mapper homology along step towers

Let `f : C(X, Y)` be continuous, let `c : Fin m ↪o ℝ` be a strictly increasing grid of
radii, and let `cover i : Index i → Set Y` be cover families on the finite chain
`Fin (m + 1)` with a selected refinement `r h` for every `h : i ≤ j` and supplied linear
orders on the component-index types. No identity or composition equation is required of the
selectors. The step tower `stepTower c cover` places `cover (cellIndex c t)` at the radius
`t`: stage `0` on the left ray below `c 0`, and stage `i + 1` on `[c i, c (i + 1))`, the last
stage on `[c (m - 1), ∞)`. Its Mapper homology module is definitionally the reindexing of the
finite-chain module along `cellIndex c`.

If the initial family has an empty index type, then its Mapper complex is empty and its
homology vanishes in every degree, so the step module is finite-constructible on the grid
`c`. When moreover every stage has finitely many Mapper faces in degree `n` and the field,
the domain and the index types lie in one universe, `stepMapperDiagram` is the real endpoint
diagram of the degree-`n` module. It is the image under `ofIndexBars c` of the finite Mapper
barcode of the stages `1, …, m`, equivalently of the barcode of all stages restricted along
`Fin.succ`; it has positive bars and does not depend on the selected refinements.

For two step towers on possibly different grids and selected cover maps shifting the radius by
`η` in both directions, the bottleneck distance of the two diagrams is at most `η`; in general
it equals the real interleaving distance of the two modules, interleavings at a parameter exist
exactly when matchings of that cost exist, and the distance is infinite exactly when the
numbers of essential bars differ. Cover maps through an intermediate real tower, shifting by
`η₁` and `η₂`, bound the bottleneck distance of the outer diagrams by `η₁ + η₂`. For the piecewise-linear height of a finite graph and
finitely many open-interval labels at every stage, every finiteness hypothesis is discharged
by instances.

The empty initial stage is the zero left tail of the finite-constructible convention; a tower
that starts nonempty is handled by prepending an empty stage. Towers of open members indexed by
radius, such as the centred tower, are left-open and lie outside this convention. No diagram is
defined for towers that are not step towers or for q-tame modules, and nothing is claimed about
tightness of the bound, independence of the component orders, multinerve Mapper, or executable
extraction.
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

/-! ## Empty families -/

section Empty

variable {X : Type u} {Y : Type v} {I : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- A family without component indices has the empty Mapper complex. -/
theorem mapper_eq_bot_of_isEmpty_componentIndex (f : C(X, Y)) (U : I → Set Y)
    [IsEmpty (ComponentIndex f U)] : mapper f U = ⊥ := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  constructor
  · intro hs
    obtain ⟨a, _⟩ := ((mem_mapper_iff f U s).1 hs).1
    exact isEmptyElim a
  · intro hs
    exact hs.elim

/-- A family with an empty index type has the empty Mapper complex. -/
theorem mapper_eq_bot_of_isEmpty [IsEmpty I] (f : C(X, Y)) (U : I → Set Y) :
    mapper f U = ⊥ :=
  have : IsEmpty (ComponentIndex f U) := ⟨fun a => isEmptyElim a.1⟩
  mapper_eq_bot_of_isEmpty_componentIndex f U

/-- A family with an empty index type has zero Mapper homology in every degree, over every
ring and for every component order. -/
theorem isZero_simplicialHomology_mapper_of_isEmpty [IsEmpty I] (R : Type c) [Ring R]
    (f : C(X, Y)) (U : I → Set Y) [LinearOrder (ComponentIndex f U)] (n : ℕ) :
    IsZero (simplicialHomology (mapper f U) R n) := by
  rw [mapper_eq_bot_of_isEmpty f U]
  exact TDA.Persistence.isZero_simplicialHomology_bot R n

end Empty

/-! ## Step towers -/

section StepTower

variable {Y : Type v} {m : ℕ} (c : Fin m ↪o ℝ) {Index : Fin (m + 1) → Type w}
  (cover : (i : Fin (m + 1)) → Index i → Set Y)

/-- The step tower of finitely many cover families on the grid `c`: the family at radius `t`
is the family of the cell `cellIndex c t` containing `t`. -/
abbrev stepTower (t : ℝ) : Index (cellIndex c t) → Set Y :=
  cover (cellIndex c t)

/-- The refinements of a step tower are the selected refinements between the families of the
cells. -/
def stepRefinement (r : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j))
    {s t : ℝ} (h : s ≤ t) : Refinement (stepTower c cover s) (stepTower c cover t) :=
  r ((cellIndex c).monotone h)

variable {X : Type u} [TopologicalSpace X] [TopologicalSpace Y] (R : Type c) [Ring R]
  (f : C(X, Y)) [∀ i, LinearOrder (ComponentIndex f (cover i))]
  (r : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j)) (n : ℕ)

/-- The Mapper homology module of a step tower is the finite-chain module reindexed along
`cellIndex c`. -/
theorem mapperHomologyPModule_stepTower :
    mapperHomologyPModule R f (stepTower c cover) (stepRefinement c cover r) n =
      reindex (cellIndex c) (mapperHomologyPModule R f cover r n) :=
  rfl

/-- With an empty initial family, the Mapper homology module of a step tower is
finite-constructible on its grid, in every degree and over every ring. -/
theorem isConstructible_stepTower [IsEmpty (Index 0)] :
    IsConstructible c (mapperHomologyPModule R f (stepTower c cover) (stepRefinement c cover r) n) := by
  rw [mapperHomologyPModule_stepTower]
  exact isConstructible_reindex c _ (isZero_simplicialHomology_mapper_of_isEmpty R f (cover 0) n)

end StepTower

/-! ## Diagrams -/

section Diagram

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (k : Type u) [Field k] (f : C(X, Y)) {m : ℕ} (c : Fin m ↪o ℝ)
  {Index : Fin (m + 1) → Type u} (cover : (i : Fin (m + 1)) → Index i → Set Y)
  [∀ i, LinearOrder (ComponentIndex f (cover i))]
  (r : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j)) (n : ℕ)
  [∀ i, Finite (Face (mapper f (cover i)) n)]

/-- Face finiteness makes the step module finite-dimensional at every critical radius. -/
theorem finiteDimensional_stepTower (j : Fin m) :
    FiniteDimensional k
      ((mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n).obj (c j)) :=
  inferInstance

/-- The real endpoint diagram of the degree-`n` Mapper homology module of a step tower. It
describes the module when the initial family is empty (`isConstructible_stepTower`). -/
def stepMapperDiagram : Diagram ℝ :=
  moduleDiagram c (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n)
    (finiteDimensional_stepTower k f c cover r n)

private theorem moduleDiagram_congr {M N : PModule.{u,0,u} k ℝ} (h : M = N)
    (hM : ∀ j, FiniteDimensional k (M.obj (c j))) (hN : ∀ j, FiniteDimensional k (N.obj (c j))) :
    moduleDiagram c M hM = moduleDiagram c N hN := by
  subst h
  rfl

/-- The step diagram does not depend on the selected refinements. -/
theorem stepMapperDiagram_eq
    (r' : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j)) :
    stepMapperDiagram k f c cover r n = stepMapperDiagram k f c cover r' n :=
  moduleDiagram_congr k c
    (mapperHomologyPModule_eq k f (stepTower c cover) (stepRefinement c cover r) n
      (stepRefinement c cover r')) _ _

/-- Every bar of the step diagram is positive, including essential bars. -/
theorem stepMapperDiagram_isPositive : (stepMapperDiagram k f c cover r n).IsPositive :=
  moduleDiagram_isPositive c _ _

private theorem cellIndex_comp_grid :
    (cellIndex c).comp c.toOrderHom = (Fin.succOrderEmb m).toOrderHom := by
  ext j
  exact congrArg Fin.val (cellIndex_critical c j)

/-- The step diagram is the image under `ofIndexBars c` of the finite Mapper barcode of the
stages `1, …, m`. -/
theorem stepMapperDiagram_eq_ofIndexBars_succ :
    stepMapperDiagram k f c cover r n =
      ofIndexBars c c.strictMono (mapperBarcode k f (fun j : Fin m => cover j.succ)
        (fun h => r (Fin.succ_le_succ_iff.mpr h)) n) := by
  have : ∀ j, FiniteDimensional k ((reindex c.toOrderHom
      (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n)).obj j) :=
    finiteDimensional_stepTower k f c cover r n
  change ofIndexBars c c.strictMono (rankBarcode (reindex c.toOrderHom
    (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n))) = _
  congr 1
  exact rankBarcode_eq_of_iso (eqToIso (congrArg
    (fun s : Fin m →o Fin (m + 1) => reindex s (mapperHomologyPModule k f cover r n))
    (cellIndex_comp_grid c)))

/-- The step diagram is the image under `ofIndexBars c` of the finite Mapper barcode of all
stages, restricted along `Fin.succ`. -/
theorem stepMapperDiagram_eq_ofIndexBars :
    stepMapperDiagram k f c cover r n =
      ofIndexBars c c.strictMono
        (reindexBarcode (Fin.succOrderEmb m).toOrderHom (mapperBarcode k f cover r n)) := by
  rw [stepMapperDiagram_eq_ofIndexBars_succ]
  congr 1
  exact rankBarcode_reindex (mapperHomologyPModule k f cover r n) (Fin.succOrderEmb m).toOrderHom

end Diagram

/-! ## Stability and isometry -/

section Stability

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

/-- Cover maps shifting the radius by `η` in both directions between two step towers bound
the bottleneck distance of their degree-`n` Mapper diagrams by `η`. The grids may differ. -/
theorem bottleneck_stepMapperDiagram_le {η : ℝ≥0}
    (ζ : ∀ t, Refinement (stepTower c cover t) (stepTower d cover' (t + η)))
    (ξ : ∀ t, Refinement (stepTower d cover' t) (stepTower c cover (t + η))) :
    bottleneck (stepMapperDiagram k f c cover r n) (stepMapperDiagram k f d cover' r' n) ≤ η :=
  bottleneck_le_of_interleaving (isConstructible_stepTower c cover k f r n)
    (isConstructible_stepTower d cover' k f r' n) _ _
    (mapperHomologyInterleaving k f (stepRefinement c cover r) (stepRefinement d cover' r') ζ ξ n)

/-- The bottleneck distance of two step diagrams is the real interleaving distance of the two
Mapper homology modules. -/
theorem bottleneck_stepMapperDiagram_eq :
    bottleneck (stepMapperDiagram k f c cover r n) (stepMapperDiagram k f d cover' r' n) =
      realInterleavingDistance
        (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n)
        (mapperHomologyPModule k f (stepTower d cover') (stepRefinement d cover' r') n) :=
  bottleneck_eq_distance (isConstructible_stepTower c cover k f r n)
    (isConstructible_stepTower d cover' k f r' n) _ _

/-- At every parameter `ε`, the two step modules are `ε`-interleaved exactly when the two step
diagrams admit an occurrence matching of cost at most `ε`. -/
theorem stepMapperDiagram_interleaving_iff_matching (ε : ℝ≥0) :
    Nonempty (RealInterleaving ε
        (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n)
        (mapperHomologyPModule k f (stepTower d cover') (stepRefinement d cover' r') n)) ↔
      ∃ A : OccurrenceMatching (stepMapperDiagram k f c cover r n).finiteOccurrences
          (stepMapperDiagram k f d cover' r' n).finiteOccurrences
          (stepMapperDiagram k f c cover r n).essentialOccurrences
          (stepMapperDiagram k f d cover' r' n).essentialOccurrences,
        A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤ (ε : ℝ≥0∞) :=
  interleaving_iff_matching (isConstructible_stepTower c cover k f r n)
    (isConstructible_stepTower d cover' k f r' n) _ _ ε

/-- The interleaving distance of two step modules is infinite exactly when their diagrams have
different numbers of essential bars. -/
theorem realInterleavingDistance_stepTower_eq_top_iff :
    realInterleavingDistance
        (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n)
        (mapperHomologyPModule k f (stepTower d cover') (stepRefinement d cover' r') n) = ⊤ ↔
      (essentialPart (stepMapperDiagram k f c cover r n).points).card ≠
        (essentialPart (stepMapperDiagram k f d cover' r' n).points).card :=
  distance_eq_top_iff_essential_card_ne (isConstructible_stepTower c cover k f r n)
    (isConstructible_stepTower d cover' k f r' n) _ _

variable {m'' : ℕ} {e : Fin m'' ↪o ℝ} {Index'' : Fin (m'' + 1) → Type u}
  {cover'' : (i : Fin (m'' + 1)) → Index'' i → Set Y}
  [∀ i, LinearOrder (ComponentIndex f (cover'' i))] [∀ i, Finite (Face (mapper f (cover'' i)) n)]
  [IsEmpty (Index'' 0)]
  (r'' : ∀ {i j : Fin (m'' + 1)}, i ≤ j → Refinement (cover'' i) (cover'' j))

/-- Cover maps shifting by `η₁` between the first two step towers and by `η₂` between the last
two bound the bottleneck distance of the outer diagrams by `η₁ + η₂`; the middle tower need not
have finitely many faces or an empty initial stage. -/
theorem bottleneck_stepMapperDiagram_le_add {IndexV : ℝ → Type u}
    {V : (t : ℝ) → IndexV t → Set Y} [∀ t, LinearOrder (ComponentIndex f (V t))]
    (rV : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t)) {η₁ η₂ : ℝ≥0}
    (ζ₁ : ∀ t, Refinement (stepTower c cover t) (V (t + η₁)))
    (ξ₁ : ∀ t, Refinement (V t) (stepTower c cover (t + η₁)))
    (ζ₂ : ∀ t, Refinement (V t) (stepTower e cover'' (t + η₂)))
    (ξ₂ : ∀ t, Refinement (stepTower e cover'' t) (V (t + η₂))) :
    bottleneck (stepMapperDiagram k f c cover r n) (stepMapperDiagram k f e cover'' r'' n) ≤
      η₁ + η₂ :=
  (bottleneck_le_distance (isConstructible_stepTower c cover k f r n)
    (isConstructible_stepTower e cover'' k f r'' n) _ _).trans
    (realInterleavingDistance_mapperHomologyPModule_le_add k f (stepRefinement c cover r) n rV
      (stepRefinement e cover'' r'') ζ₁ ξ₁ ζ₂ ξ₂)

end Stability

/-! ## Graph-PL step towers -/

-- For a finite graph and finitely many interval labels at every stage, the step diagram of
-- the piecewise-linear height needs no face-finiteness argument.
example {m : ℕ} {V : Type u} [Finite V] (G : SimpleGraph V) (h : V → ℝ) (c : Fin m ↪o ℝ)
    {Index : Fin (m + 1) → Type u} [∀ i, Finite (Index i)] [IsEmpty (Index 0)]
    (cover : (i : Fin (m + 1)) → Index i → TDA.Reeb.OpenInterval)
    [∀ i, LinearOrder (ComponentIndex (TDA.Reeb.GraphPL.plHeight G h)
      (fun j => (cover i j : Set ℝ)))]
    (r : ∀ {i j : Fin (m + 1)}, i ≤ j →
      Refinement (fun l => (cover i l : Set ℝ)) (fun l => (cover j l : Set ℝ)))
    (k : Type u) [Field k] (n : ℕ) :
    (stepMapperDiagram k (TDA.Reeb.GraphPL.plHeight G h) c
      (fun i l => (cover i l : Set ℝ)) r n).IsPositive :=
  stepMapperDiagram_isPositive _ _ _ _ _ _

end

end TDA.Mapper
