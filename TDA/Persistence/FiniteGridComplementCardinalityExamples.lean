import TDA.Persistence.FiniteGridInjectiveRankDimension
import TDA.Persistence.PrincipalDownsetInjective

/-!
# Finite grid complement-count fixtures

These fixtures exercise the zero-coordinate product, a grid with a singleton
factor, a genuine two-coordinate real grid, the old and new tops, both families
in the actual interval-pair subtype, and a nonzero rational injective module.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteLatticeComplementCardinality.Examples

open CategoryTheory CategoryTheory.Limits
open PrincipalDownsetRankResolution
open TDA.Persistence.FiniteLatticeComplementCardinality
open TDA.Persistence.FiniteGridInjectiveRankDimension
open TDA.Persistence.FiniteInjectiveRankDimension
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveHomExact
open TDA.Persistence.FiniteRankProjectiveHomDimension
open TDA.Persistence.PrincipalDownsetInjective

noncomputable section

/-- The coordinate grid with no coordinate directions. -/
def emptyGrid : CoordinateGrid 0 := fun i => Fin.elim0 i

private theorem emptyGrid_nonempty : ∀ i : Fin 0, (emptyGrid i).Nonempty := by
  intro i
  exact Fin.elim0 i

/-- The actual empty-index product has no minimal complement generators. -/
theorem emptyGrid_maxComplementCard_eq_zero :
    letI : BoundedOrder emptyGrid.Point :=
      coordinateGridBoundedOrder emptyGrid emptyGrid_nonempty
    maxComplementCard (S := emptyGrid.Point) = 0 := by
  letI : BoundedOrder emptyGrid.Point :=
    coordinateGridBoundedOrder emptyGrid emptyGrid_nonempty
  have h := maxComplementCard_coordinateGrid_le emptyGrid emptyGrid_nonempty
  omega

/-- A one-direction real grid whose sole factor is a singleton. -/
def singletonGrid : CoordinateGrid 1 := fun _ => {0}

private theorem singletonGrid_nonempty :
    ∀ i : Fin 1, (singletonGrid i).Nonempty := by
  intro i
  simp [singletonGrid]

/-- The singleton-factor real grid satisfies the one-generator bound. -/
theorem singletonGrid_maxComplementCard_le :
    letI : BoundedOrder singletonGrid.Point :=
      coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
    maxComplementCard (S := singletonGrid.Point) ≤ 1 :=
  maxComplementCard_coordinateGrid_le singletonGrid singletonGrid_nonempty

/-- Adjoining the new top to that one-factor grid still satisfies the bound. -/
theorem singletonGrid_withTop_maxComplementCard_le :
    letI : BoundedOrder singletonGrid.Point :=
      coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
    maxComplementCard (S := WithTop singletonGrid.Point) ≤ 1 := by
  exact maxComplementCard_withTop_coordinateGrid_le singletonGrid (by omega)
    singletonGrid_nonempty

/-- A real square grid with two selected values in each direction. -/
def squareGrid : CoordinateGrid 2 := fun _ => {0, 1}

private theorem squareGrid_nonempty :
    ∀ i : Fin 2, (squareGrid i).Nonempty := by
  intro i
  simp [squareGrid]

/-- The actual two-dimensional grid has the expected coordinate-count bound. -/
theorem squareGrid_maxComplementCard_le :
    letI : BoundedOrder squareGrid.Point :=
      coordinateGridBoundedOrder squareGrid squareGrid_nonempty
    maxComplementCard (S := squareGrid.Point) ≤ 2 :=
  maxComplementCard_coordinateGrid_le squareGrid squareGrid_nonempty

/-- Its adjoined-top maximum respects the positive-grid bound. -/
theorem squareGrid_withTop_maxComplementCard_le :
    letI : BoundedOrder squareGrid.Point :=
      coordinateGridBoundedOrder squareGrid squareGrid_nonempty
    maxComplementCard (S := WithTop squareGrid.Point) ≤ 2 := by
  exact maxComplementCard_withTop_coordinateGrid_le squareGrid (by omega)
    squareGrid_nonempty

/-- The actual interval-pair subtype over the square grid has at most `2*n`
complement generators. -/
theorem squareGrid_pair_maxComplementCard_le :
    letI : BoundedOrder squareGrid.Point :=
      coordinateGridBoundedOrder squareGrid squareGrid_nonempty
    letI : Lattice (PairPoset squareGrid.Point) :=
      pairPosetLattice (S := squareGrid.Point)
    letI : BoundedOrder (PairPoset squareGrid.Point) :=
      pairPosetBoundedOrder (S := squareGrid.Point)
    maxComplementCard (S := PairPoset squareGrid.Point) ≤ 4 := by
  exact maxComplementCard_pair_coordinateGrid_le squareGrid (by omega)
    squareGrid_nonempty

/-- At the old top, adjoining a new top creates exactly one minimal
complement generator: the genuinely new top. -/
theorem boolWithTop_oldTop_minimalComplement :
    minimalComplement (S := WithTop Bool) ((⊤ : Bool) : WithTop Bool) =
      {⊤} :=
  minimalComplement_withTop_oldTop (S := Bool)

/-- At the genuinely new top, the complement is empty. -/
theorem boolWithTop_newTop_minimalComplement :
    minimalComplement (S := WithTop Bool) (⊤ : WithTop Bool) = ∅ :=
  (minimalComplement_eq_empty_iff (p := (⊤ : WithTop Bool))).2 rfl

private theorem boolWithTop_false_minimalComplement :
    minimalComplement (S := WithTop Bool) ((false : Bool) : WithTop Bool) =
      {((true : Bool) : WithTop Bool)} := by
  ext x
  constructor
  · intro hx
    change Minimal (fun y : WithTop Bool => ¬ y ≤ ((false : Bool) : WithTop Bool)) x at hx
    cases x with
    | top =>
        have hnot : ¬ ((true : Bool) : WithTop Bool) ≤ ((false : Bool) : WithTop Bool) := by
          norm_num
        have heq : ((true : Bool) : WithTop Bool) = (⊤ : WithTop Bool) :=
          hx.eq_of_le hnot le_top
        simp at heq
    | coe b =>
        cases b with
        | false => exact False.elim (hx.prop le_rfl)
        | true => rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change Minimal (fun y : WithTop Bool => ¬ y ≤ ((false : Bool) : WithTop Bool))
      ((true : Bool) : WithTop Bool)
    refine ⟨?_, ?_⟩
    · norm_num
    · intro y hy hyle
      cases y with
      | top => simp at hyle
      | coe b =>
          cases b with
          | false => simp at hy
          | true => exact le_rfl

/-- The nontrivial comparable pair used to exercise both complement families. -/
def boolIntervalPair : PairPoset Bool :=
  ⟨((false : WithTop Bool), (true : WithTop Bool)), by decide⟩

/-- The pair's restricted diagonal family contains `(true,true)`. -/
theorem boolIntervalPair_diagonalFamily_nonempty :
    letI : Lattice (PairPoset Bool) := pairPosetLattice (S := Bool)
    letI : BoundedOrder (PairPoset Bool) := pairPosetBoundedOrder (S := Bool)
    Nonempty (diagonalPairComplement boolIntervalPair) := by
  letI : Lattice (PairPoset Bool) := pairPosetLattice (S := Bool)
  letI : BoundedOrder (PairPoset Bool) := pairPosetBoundedOrder (S := Bool)
  refine ⟨⟨⟨(true : WithTop Bool), ?_⟩, ?_⟩⟩
  · change (true : WithTop Bool) ∈
      minimalComplement (S := WithTop Bool) ((false : Bool) : WithTop Bool)
    rw [boolWithTop_false_minimalComplement]
    simp
  · exact le_rfl

/-- The same pair's bottom-axis family contains `(bottom,newTop)`. -/
theorem boolIntervalPair_bottomFamily_nonempty :
    Set.Nonempty (minimalComplement (S := WithTop Bool) boolIntervalPair.val.2) := by
  refine ⟨(⊤ : WithTop Bool), ?_⟩
  change (⊤ : WithTop Bool) ∈
    minimalComplement (S := WithTop Bool) ((⊤ : Bool) : WithTop Bool)
  rw [boolWithTop_oldTop_minimalComplement]
  simp

/-- Both disjoint families contribute one element at the selected pair. -/
theorem boolIntervalPair_complementCard_eq_two :
    letI : Lattice (PairPoset Bool) := pairPosetLattice (S := Bool)
    letI : BoundedOrder (PairPoset Bool) := pairPosetBoundedOrder (S := Bool)
    complementCard (S := PairPoset Bool) boolIntervalPair = 2 := by
  letI : Lattice (PairPoset Bool) := pairPosetLattice (S := Bool)
  letI : BoundedOrder (PairPoset Bool) := pairPosetBoundedOrder (S := Bool)
  letI : Fintype (PairPoset Bool) := Fintype.ofFinite _
  letI : Fintype (diagonalPairComplement boolIntervalPair) :=
    diagonalPairComplementFintype boolIntervalPair
  rw [complementCard_pair_eq]
  have hdiag : Fintype.card (diagonalPairComplement boolIntervalPair) = 1 := by
    apply Fintype.card_eq_one_iff_nonempty_unique.mpr
    have hset := boolWithTop_false_minimalComplement
    let hmembership : (true : WithTop Bool) ∈
        minimalComplement ((false : Bool) : WithTop Bool) := by
      rw [hset]
      simp
    let a₀ : diagonalPairComplement boolIntervalPair :=
      ⟨⟨(true : WithTop Bool), hmembership⟩, by rfl⟩
    refine ⟨{ default := a₀, uniq := ?_ }⟩
    intro a
    apply Subtype.ext
    apply Subtype.ext
    have ha : a.1.1 ∈ minimalComplement ((false : Bool) : WithTop Bool) := a.1.2
    rw [hset] at ha
    exact Set.mem_singleton_iff.mp ha
  have hbottom :
      complementCard (S := WithTop Bool) boolIntervalPair.val.2 = 1 := by
    change complementCard (S := WithTop Bool) ((⊤ : Bool) : WithTop Bool) = 1
    unfold complementCard
    let e : minimalComplement (S := WithTop Bool) ((⊤ : Bool) : WithTop Bool) ≃
        {x : WithTop Bool // x = ⊤} :=
      Equiv.subtypeEquivRight (fun x => by
        rw [boolWithTop_oldTop_minimalComplement]
        simp)
    calc
      Fintype.card (minimalComplement (S := WithTop Bool) ((⊤ : Bool) : WithTop Bool)) =
          Fintype.card {x : WithTop Bool // x = ⊤} := Fintype.card_congr e
      _ = 1 := by
        apply Fintype.card_eq_one_iff_nonempty_unique.mpr
        refine ⟨{ default := ⟨⊤, rfl⟩, uniq := ?_ }⟩
        intro x
        apply Subtype.ext
        exact x.property
  rw [hdiag, hbottom]

/-- A singleton real grid and its nonzero rational principal-downset
injective. -/
def rationalSingletonGridPoint : singletonGrid.Point :=
  fun _ => ⟨0, by simp [singletonGrid]⟩

/-- The principal downset at the unique grid point, over `ℚ`. -/
def rationalSingletonInjective :
    PModule.{0,0,0} ℚ singletonGrid.Point :=
  PrincipalDownsetInjective.module (k := ℚ) rationalSingletonGridPoint

/-- The rational injective fixture is genuinely nonzero. -/
theorem rationalSingletonInjective_not_isZero :
    ¬ IsZero rationalSingletonInjective := by
  intro hzero
  let p : singletonGrid.Point := rationalSingletonGridPoint
  letI : Subsingleton (rationalSingletonInjective.obj p) :=
    ModuleCat.subsingleton_of_isZero (hzero.obj p)
  letI : Nontrivial (rationalSingletonInjective.obj p) := by
    change Nontrivial (SupportInterval.fiber (k := ℚ) (Set.Iic p) p)
    exact Function.Injective.nontrivial
      (f := fun x : ℚ =>
        (⟨x, by simp [SupportInterval.fiber]⟩ :
          SupportInterval.fiber (k := ℚ) (Set.Iic p) p))
      (by
        intro x y h
        exact congrArg
          (fun z : SupportInterval.fiber (k := ℚ) (Set.Iic p) p => (z : ℚ)) h)
  exact false_of_nontrivial_of_subsingleton (rationalSingletonInjective.obj p)

/-- Over `ℚ`, the nonzero ordinary injective on the singleton grid has Hom
projective dimension zero. -/
theorem rationalSingletonInjective_hom_dimension_zero :
    HasProjectiveDimensionLE
      ((FiniteRankProjectiveHomExact.homFunctor (k := ℚ)
        (S := singletonGrid.Point)).obj rationalSingletonInjective) 0 := by
  letI : Injective rationalSingletonInjective := by
    simpa [rationalSingletonInjective] using
      (PrincipalDownsetInjective.isInjective (k := ℚ) rationalSingletonGridPoint)
  letI : ∀ q : singletonGrid.Point,
      FiniteDimensional ℚ (rationalSingletonInjective.obj q) := fun q => by
    change FiniteDimensional ℚ
      ((PrincipalDownsetInjective.module (k := ℚ)
        rationalSingletonGridPoint).obj q)
    infer_instance
  simpa using hasProjectiveDimensionLE_of_coordinateGrid
    (k := ℚ) singletonGrid rationalSingletonInjective singletonGrid_nonempty

/-- Every supplied certified minimal rank-projective resolution of that
ordinary injective vanishes in positive degrees. -/
theorem rationalSingletonInjective_resolution_positive_vanishing
    (R : MinimalFiniteRankProjectiveResolution
      (k := ℚ) (M := rationalSingletonInjective))
    (j : ℕ) (hj : 0 < j) : IsZero (R.termAt j) := by
  letI : Injective rationalSingletonInjective := by
    simpa [rationalSingletonInjective] using
      (PrincipalDownsetInjective.isInjective (k := ℚ) rationalSingletonGridPoint)
  letI : ∀ q : singletonGrid.Point,
      FiniteDimensional ℚ (rationalSingletonInjective.obj q) := fun q => by
    change FiniteDimensional ℚ
      ((PrincipalDownsetInjective.module (k := ℚ)
        rationalSingletonGridPoint).obj q)
    infer_instance
  simpa using termAt_isZero_of_coordinateGrid
    (k := ℚ) singletonGrid rationalSingletonInjective singletonGrid_nonempty R j hj

end

end TDA.Persistence.FiniteLatticeComplementCardinality.Examples
