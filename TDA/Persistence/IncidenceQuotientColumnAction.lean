import TDA.Persistence.IncidenceQuotientDerivedOne
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Module.Projective

/-!
# The diagonal-column additive functor

This file records the fixed diagonal-floor columns that control the kernel action on
right incidence modules.  The auxiliary functor takes values in abelian groups: its
objects and the assembly map are not asserted to be incidence modules or module maps.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceQuotientColumnAction

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceQuotientDerivedOne

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : DecidableLE S := Classical.decRel _
local instance : DecidableLT S := Classical.decRel _
local instance : DecidableEq S := Classical.decEq _
local instance : DecidableEq (WithTop S) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset S) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop S × WithTop S => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset S) := Classical.decRel _
local instance : DecidableLT (PairPoset S) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset S) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset S) := Classical.decEq _
local instance : Fintype (ComparablePair S) := Fintype.ofFinite _
local instance diagonalIdealTwoSided :
    (FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := S)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := S)

abbrev R := RightIncidence (k := k) (S := S)
abbrev C := RightQuotient (k := k) (S := S)
abbrev Pair := PairPoset S

/-- The diagonal-floor idempotent acting on the column indexed by `q`. -/
def columnProjector (q : Pair (S := S)) : R (k := k) (S := S) :=
  MulOpposite.op (delta (k := k) (S := S) (diagonalFloor (S := S) q)
    (diagonalFloor (S := S) q) le_rfl)

/-- The matrix unit assembling the diagonal-floor column `q`. -/
def columnAssembler (q : Pair (S := S)) : R (k := k) (S := S) :=
  MulOpposite.op (delta (k := k) (S := S) (diagonalFloor (S := S) q) q
    (diagonalFloor_le (S := S) q))

/-- The additive subgroup fixed by the diagonal-floor idempotent. -/
def fixedColumn (M : ModuleCat (R (k := k) (S := S))) (q : Pair (S := S)) : AddSubgroup M where
  carrier := {m | columnProjector (k := k) (S := S) q • m = m}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change columnProjector (k := k) (S := S) q • (x + y) = x + y
    rw [smul_add, hx, hy]
  neg_mem' := by
    intro x hx
    change columnProjector (k := k) (S := S) q • (-x) = -x
    rw [smul_neg, hx]

@[simp] theorem mem_fixedColumn_iff
    (M : ModuleCat (R (k := k) (S := S))) (q : Pair (S := S)) (m : M) :
    m ∈ fixedColumn (k := k) (S := S) M q ↔
      columnProjector (k := k) (S := S) q • m = m := Iff.rfl

/-- The product of all fixed diagonal-floor columns of a right incidence module. -/
abbrev ColumnObject (M : ModuleCat (R (k := k) (S := S))) :=
  ∀ q : Pair (S := S), fixedColumn (k := k) (S := S) M q

private def columnMapHom {M N : ModuleCat (R (k := k) (S := S))} (f : M ⟶ N) :
    ColumnObject (k := k) (S := S) M →+ ColumnObject (k := k) (S := S) N where
  toFun x q := ⟨f.hom (x q), by
    change columnProjector (k := k) (S := S) q • f.hom (x q) = f.hom (x q)
    rw [← f.hom.map_smul]
    exact congrArg f.hom (x q).property⟩
  map_zero' := by
    ext q
    simp
  map_add' := by
    intro x y
    ext q
    simp

@[simp] private theorem columnMapHom_apply
    {M N : ModuleCat (R (k := k) (S := S))} (f : M ⟶ N)
    (x : ColumnObject (k := k) (S := S) M) (q : Pair (S := S)) :
    columnMapHom (k := k) (S := S) f x q = ⟨f.hom (x q), by
      change columnProjector (k := k) (S := S) q • f.hom (x q) = f.hom (x q)
      rw [← f.hom.map_smul]
      exact congrArg f.hom (x q).property⟩ := rfl

/-- The additive functor of fixed diagonal-floor columns. -/
noncomputable def columnAction :
    ModuleCat (R (k := k) (S := S)) ⥤ AddCommGrpCat where
  obj M := AddCommGrpCat.of (ColumnObject (k := k) (S := S) M)
  map f := AddCommGrpCat.ofHom (columnMapHom (k := k) (S := S) f)
  map_id M := by
    apply AddCommGrpCat.ext
    intro x
    funext q
    exact Subtype.ext rfl
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro x
    funext q
    exact Subtype.ext rfl

instance columnAction_additive :
    Functor.Additive (columnAction (k := k) (S := S)) where
  map_add := by
    intro M N f g
    apply AddCommGrpCat.ext
    intro x
    funext q
    exact Subtype.ext rfl

@[simp] theorem columnAction_map_apply
    {M N : ModuleCat (R (k := k) (S := S))} (f : M ⟶ N)
    (x : ColumnObject (k := k) (S := S) M) (q : Pair (S := S)) :
    ((columnAction (k := k) (S := S)).map f x q : N) = f.hom (x q) := rfl

/-- Assemble a fixed family by acting with its matrix units and summing in the module. -/
def assembleAction (M : ModuleCat (R (k := k) (S := S))) :
    ColumnObject (k := k) (S := S) M →+ M where
  toFun x := ∑ q : Pair (S := S), columnAssembler (k := k) (S := S) q • (x q : M)
  map_zero' := by simp
  map_add' x y := by
    change (∑ q : Pair (S := S), columnAssembler (k := k) (S := S) q •
        ((x + y) q : M)) =
      (∑ q : Pair (S := S), columnAssembler (k := k) (S := S) q • (x q : M)) +
        (∑ q : Pair (S := S), columnAssembler (k := k) (S := S) q • (y q : M))
    simp only [Pi.add_apply, AddSubgroup.coe_add, Finset.sum_add_distrib, smul_add]

@[simp] theorem assembleAction_apply
    (M : ModuleCat (R (k := k) (S := S)))
    (x : ColumnObject (k := k) (S := S) M) :
    assembleAction (k := k) (S := S) M x =
      ∑ q : Pair (S := S), columnAssembler (k := k) (S := S) q • (x q : M) := rfl

theorem assembleAction_natural
    {M N : ModuleCat (R (k := k) (S := S))} (f : M ⟶ N)
    (x : ColumnObject (k := k) (S := S) M) :
    assembleAction (k := k) (S := S) N
      (columnMapHom (k := k) (S := S) f x) =
        f.hom (assembleAction (k := k) (S := S) M x) := by
  change (∑ q : Pair (S := S), columnAssembler (k := k) (S := S) q • f.hom (x q)) =
    f.hom (∑ q : Pair (S := S), columnAssembler (k := k) (S := S) q • (x q : M))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact (f.hom.map_smul (columnAssembler (k := k) (S := S) q) (x q)).symm

private theorem columnProjector_mul_self (q : Pair (S := S)) :
    columnProjector (k := k) (S := S) q * columnProjector (k := k) (S := S) q =
      columnProjector (k := k) (S := S) q := by
  dsimp [columnProjector]
  rw [← MulOpposite.op_mul]
  apply MulOpposite.op_injective
  rw [delta_mul]
  simp

private theorem columnAssembler_mem_kernel (q : Pair (S := S)) :
    columnAssembler (k := k) (S := S) q ∈ J (k := k) (S := S) := by
  have hmem : MulOpposite.unop (columnAssembler (k := k) (S := S) q) ∈
      FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
        (k := k) (S := S) := by
    change delta (k := k) (S := S) (diagonalFloor (S := S) q) q
      (diagonalFloor_le (S := S) q) ∈
        FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
          (k := k) (S := S)
    exact diagonalIdeal_mem_delta_of_cross
      (k := k) (S := S) (diagonalFloor (S := S) q) q
      (diagonalFloor_le (S := S) q)
      (by
        change (diagonalFloor (S := S) q).val.2 ≤ q.val.1
        simp [diagonalFloor])
  exact (mem_kernel_iff_unop_mem (k := k) (S := S)
    (columnAssembler (k := k) (S := S) q)).2 hmem

private theorem columnProjector_mem_kernel (q : Pair (S := S)) :
    columnProjector (k := k) (S := S) q ∈ J (k := k) (S := S) := by
  have hmem : MulOpposite.unop (columnProjector (k := k) (S := S) q) ∈
      FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
        (k := k) (S := S) := by
    change delta (k := k) (S := S) (diagonalFloor (S := S) q)
      (diagonalFloor (S := S) q) le_rfl ∈
        FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
          (k := k) (S := S)
    exact diagonalIdeal_mem_delta_of_cross
      (k := k) (S := S) (diagonalFloor (S := S) q)
      (diagonalFloor (S := S) q) le_rfl
      (by
        change (diagonalFloor (S := S) q).val.2 ≤
          (diagonalFloor (S := S) q).val.1
        simp [diagonalFloor])
  exact (mem_kernel_iff_unop_mem (k := k) (S := S)
    (columnProjector (k := k) (S := S) q)).2 hmem

private def kernelColumnFamily
    (M : ModuleCat (R (k := k) (S := S)))
    (a : R (k := k) (S := S)) (ha : a ∈ J (k := k) (S := S)) (m : M) :
    ColumnObject (k := k) (S := S) M := by
  let u : FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := S) :=
    ⟨MulOpposite.unop a,
      (mem_kernel_iff_unop_mem (k := k) (S := S) a).1 ha⟩
  refine fun q => ⟨MulOpposite.op (includeColumns (k := k) (S := S) u q) • m, ?_⟩
  have hscalar :
      columnProjector (k := k) (S := S) q *
        MulOpposite.op (includeColumns (k := k) (S := S) u q) =
          MulOpposite.op (includeColumns (k := k) (S := S) u q) := by
    dsimp [columnProjector]
    rw [← MulOpposite.op_mul]
    exact congrArg MulOpposite.op
      (includeColumns_mul_diagonalFloorIdempotent (k := k) (S := S) u q)
  calc
    columnProjector (k := k) (S := S) q •
        (MulOpposite.op (includeColumns (k := k) (S := S) u q) • m) =
        (columnProjector (k := k) (S := S) q *
          MulOpposite.op (includeColumns (k := k) (S := S) u q)) • m := by
            rw [smul_smul]
    _ = MulOpposite.op (includeColumns (k := k) (S := S) u q) • m := by
      rw [hscalar]

private theorem kernel_smul_mem_assembleRange
    (M : ModuleCat (R (k := k) (S := S)))
    (a : R (k := k) (S := S)) (ha : a ∈ J (k := k) (S := S)) (m : M) :
    a • m ∈ (assembleAction (k := k) (S := S) M).range := by
  let u : FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := S) :=
    ⟨MulOpposite.unop a,
      (mem_kernel_iff_unop_mem (k := k) (S := S) a).1 ha⟩
  let z := kernelColumnFamily (k := k) (S := S) M a ha m
  have hreassemble :
      assembleColumns (k := k) (S := S) (includeColumns (k := k) (S := S) u) = u := by
    exact LinearMap.congr_fun
      (assembleColumns_comp_includeColumns (k := k) (S := S)) u
  refine ⟨z, ?_⟩
  rw [assembleAction_apply]
  calc
    (∑ q : Pair (S := S), columnAssembler (k := k) (S := S) q • (z q : M)) =
        ∑ q : Pair (S := S),
          MulOpposite.op
            (includeColumns (k := k) (S := S) u q *
              delta (k := k) (S := S) (diagonalFloor (S := S) q) q
                (diagonalFloor_le (S := S) q)) • m := by
          apply Finset.sum_congr rfl
          intro q hq
          change columnAssembler (k := k) (S := S) q •
              (MulOpposite.op (includeColumns (k := k) (S := S) u q) • m) = _
          rw [smul_smul]
          congr 1
    _ = (∑ q : Pair (S := S),
          MulOpposite.op
            (includeColumns (k := k) (S := S) u q *
              delta (k := k) (S := S) (diagonalFloor (S := S) q) q
                (diagonalFloor_le (S := S) q))) • m := by
          rw [← Finset.sum_smul]
    _ = MulOpposite.op
          (∑ q : Pair (S := S),
            includeColumns (k := k) (S := S) u q *
              delta (k := k) (S := S) (diagonalFloor (S := S) q) q
                (diagonalFloor_le (S := S) q)) • m := by
          congr 1
          simp
    _ = MulOpposite.op
          (assembleColumns (k := k) (S := S)
            (includeColumns (k := k) (S := S) u)).1 • m := by
          rw [← assembleColumns_eq_sum_mul_delta (k := k) (S := S)]
    _ = MulOpposite.op u.1 • m := by rw [hreassemble]
    _ = a • m := by simp [u]

/-- The image of the additive assembly map is exactly the underlying additive subgroup
of the existing quotient relation submodule. -/
theorem assembleAction_range_eq_relation
    (M : ModuleCat (R (k := k) (S := S))) :
    (assembleAction (k := k) (S := S) M).range =
      (relation (k := k) (S := S) M).toAddSubgroup := by
  classical
  apply AddSubgroup.ext
  intro m
  change (∃ x, assembleAction (k := k) (S := S) M x = m) ↔
    m ∈ relation (k := k) (S := S) M
  constructor
  · rintro ⟨x, rfl⟩
    rw [relation_eq_kernel_smul_top (k := k) (S := S)]
    change assembleAction (k := k) (S := S) M x ∈
      (J (k := k) (S := S) • (⊤ : Submodule (R (k := k) (S := S)) M))
    rw [assembleAction_apply]
    apply Submodule.sum_mem
    intro q hq
    exact Submodule.smul_mem_smul
      (columnAssembler_mem_kernel (k := k) (S := S) q) Submodule.mem_top
  · intro hm
    change m ∈ Submodule.span (R (k := k) (S := S))
      (Set.range fun z : (J (k := k) (S := S)) × M =>
        (z.1 : R (k := k) (S := S)) • z.2) at hm
    have hspan (x : M) (hx : x ∈ Submodule.span (R (k := k) (S := S))
        (Set.range fun z : (J (k := k) (S := S)) × M =>
          (z.1 : R (k := k) (S := S)) • z.2)) :
        ∀ r : R (k := k) (S := S),
          r • x ∈ (assembleAction (k := k) (S := S) M).range := by
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨z, hz⟩ := hy
        rcases z with ⟨a, y₀⟩
        subst y
        intro r
        rw [smul_smul]
        exact kernel_smul_mem_assembleRange (k := k) (S := S) M (r * a)
          (Ideal.mul_mem_left (J (k := k) (S := S)) r a.property) y₀
      | zero =>
        intro r
        simp
      | add x y hx hy ihx ihy =>
        intro r
        rw [smul_add]
        exact (assembleAction (k := k) (S := S) M).range.add_mem
          (ihx r) (ihy r)
      | smul r x hx ih =>
        intro s
        rw [smul_smul]
        exact ih (s * r)
    simpa using hspan m hm 1

/-- The fixed-column object of a restricted quotient module is zero. -/
theorem columnAction_restrict_isZero
    (N : ModuleCat (C (k := k) (S := S))) :
    IsZero ((columnAction (k := k) (S := S)).obj
      ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)) := by
  classical
  let M : ModuleCat (R (k := k) (S := S)) :=
    (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N
  have hfixedZero (x : ColumnObject (k := k) (S := S) M)
      (q : Pair (S := S)) : (x q : M) = 0 := by
    have hkill : columnProjector (k := k) (S := S) q • (x q : M) = 0 :=
      kernel_smul_restricted (k := k) (S := S) N
        (columnProjector (k := k) (S := S) q)
        (columnProjector_mem_kernel (k := k) (S := S) q) (x q : M)
    calc
      (x q : M) = columnProjector (k := k) (S := S) q • (x q : M) :=
        (x q).property.symm
      _ = 0 := hkill
  letI : Subsingleton (ColumnObject (k := k) (S := S) M) := ⟨by
    intro x y
    funext q
    apply Subtype.ext
    rw [hfixedZero x q, hfixedZero y q]⟩
  change IsZero (AddCommGrpCat.of (ColumnObject (k := k) (S := S) M))
  exact AddCommGrpCat.isZero_of_subsingleton _

private theorem mul_diagonalDelta_apply
    (a : FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S))
    (d p t : Pair (S := S)) :
    (a * delta (k := k) (S := S) d d le_rfl) p t =
      if t = d then a p d else 0 := by
  classical
  by_cases ht : t = d
  · subst t
    by_cases hpd : p ≤ d
    · rw [IncidenceAlgebra.mul_apply]
      have hdmem : d ∈ Finset.Icc p d := Finset.mem_Icc.mpr ⟨hpd, le_rfl⟩
      rw [Finset.sum_eq_single d]
      · simp [delta_apply]
      · intro x hx hxd
        simp [delta_apply, hxd]
      · intro h
        exact (h hdmem).elim
    · rw [IncidenceAlgebra.mul_apply]
      have ha : a p d = 0 := a.eq_zero_of_not_le' hpd
      simp only [if_pos rfl, ha]
      apply Finset.sum_eq_zero
      intro x hx
      have hxd : x ≠ d := by
        intro h
        subst x
        exact hpd (Finset.mem_Icc.mp hx).1
      simp [delta_apply, hxd]
  · rw [IncidenceAlgebra.mul_apply]
    simp only [if_neg ht]
    apply Finset.sum_eq_zero
    intro x hx
    simp [delta_apply, ht]

private abbrev regularColumnModule : ModuleCat (R (k := k) (S := S)) :=
  ModuleCat.of (R (k := k) (S := S)) (R (k := k) (S := S))

private def regularColumns
    (x : ColumnObject (k := k) (S := S)
      (regularColumnModule (k := k) (S := S))) : ColumnModule (k := k) (S := S) :=
  fun q => MulOpposite.unop
    ((x q : regularColumnModule (k := k) (S := S)) : R (k := k) (S := S))

private theorem assembleAction_regular_formula
    (x : ColumnObject (k := k) (S := S)
      (regularColumnModule (k := k) (S := S))) :
    MulOpposite.unop
        (assembleAction (k := k) (S := S)
          (regularColumnModule (k := k) (S := S)) x) =
      (assembleColumns (k := k) (S := S)
        (regularColumns (k := k) (S := S) x)).1 := by
  rw [assembleColumns_eq_sum_mul_delta (k := k) (S := S)]
  change MulOpposite.unop
      (∑ q : Pair (S := S),
        columnAssembler (k := k) (S := S) q • (x q : regularColumnModule (k := k) (S := S))) = _
  change ((MulOpposite.opAddEquiv :
      FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) ≃+
        R (k := k) (S := S)).symm.toAddMonoidHom)
      (∑ q : Pair (S := S),
        columnAssembler (k := k) (S := S) q • (x q : regularColumnModule (k := k) (S := S))) = _
  rw [map_sum]
  simp [columnAssembler, regularColumns, regularColumnModule, MulOpposite.unop_mul]

private theorem assembleAction_regular_eq_zero
    {x : ColumnObject (k := k) (S := S)
      (regularColumnModule (k := k) (S := S))}
    (hx : assembleAction (k := k) (S := S)
      (regularColumnModule (k := k) (S := S)) x = 0) : x = 0 := by
  let g := regularColumns (k := k) (S := S) x
  have hcols : assembleColumns (k := k) (S := S) g = 0 := by
    apply Subtype.ext
    calc
      (assembleColumns (k := k) (S := S) g).1 =
          MulOpposite.unop (assembleAction (k := k) (S := S)
            (regularColumnModule (k := k) (S := S)) x) :=
        (assembleAction_regular_formula (k := k) (S := S) x).symm
      _ = 0 := by
        have h := congrArg MulOpposite.unop hx
        simpa using h
  have hcoeff (q p : Pair (S := S)) : g q p (diagonalFloor (S := S) q) = 0 := by
    have h := congrArg
      (fun a : FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
        (k := k) (S := S) => a.1 p q) hcols
    simpa [g, assembleColumns_apply] using h
  have hfixed (q : Pair (S := S)) :
      g q * delta (k := k) (S := S) (diagonalFloor (S := S) q)
        (diagonalFloor (S := S) q) le_rfl = g q := by
    have hp := (x q).property
    change columnProjector (k := k) (S := S) q *
        ((x q : regularColumnModule (k := k) (S := S)) : R (k := k) (S := S)) =
      ((x q : regularColumnModule (k := k) (S := S)) : R (k := k) (S := S)) at hp
    have hp' := congrArg MulOpposite.unop hp
    change MulOpposite.unop ((x q : regularColumnModule (k := k) (S := S)) :
      R (k := k) (S := S)) *
        delta (k := k) (S := S) (diagonalFloor (S := S) q)
          (diagonalFloor (S := S) q) le_rfl =
      MulOpposite.unop ((x q : regularColumnModule (k := k) (S := S)) :
        R (k := k) (S := S)) at hp'
    change g q * delta (k := k) (S := S) (diagonalFloor (S := S) q)
        (diagonalFloor (S := S) q) le_rfl = g q
    exact hp'
  have hg (q : Pair (S := S)) : g q = 0 := by
    ext p t
    by_cases ht : t = diagonalFloor (S := S) q
    · subst t
      exact hcoeff q p
    · have hpt := congrArg
        (fun a : FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S) => a p t)
        (hfixed q)
      rw [mul_diagonalDelta_apply (g q) (diagonalFloor (S := S) q) p t] at hpt
      simp [ht] at hpt
      exact hpt.symm
  funext q
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change MulOpposite.unop
    ((x q : regularColumnModule (k := k) (S := S)) : R (k := k) (S := S)) = 0
  simpa [g, regularColumns] using hg q

/-- Assembly is injective on the regular right incidence module. -/
theorem assembleAction_regular_injective :
    Function.Injective
      (assembleAction (k := k) (S := S)
        (regularColumnModule (k := k) (S := S))) := by
  intro x y hxy
  have hzero : assembleAction (k := k) (S := S)
      (regularColumnModule (k := k) (S := S)) (x - y) = 0 := by
    rw [map_sub, hxy]
    simp
  have hsub := assembleAction_regular_eq_zero (k := k) (S := S) hzero
  exact sub_eq_zero.mp hsub

private theorem assembleAction_finsupp_eq_zero {ι : Type u}
    {x : ColumnObject (k := k) (S := S)
      (ModuleCat.of (R (k := k) (S := S)) (ι →₀ R (k := k) (S := S)))}
    (hx : assembleAction (k := k) (S := S)
      (ModuleCat.of (R (k := k) (S := S)) (ι →₀ R (k := k) (S := S))) x = 0) :
    x = 0 := by
  funext q
  apply Subtype.ext
  ext i
  let ev : ModuleCat.of (R (k := k) (S := S))
      (ι →₀ R (k := k) (S := S)) ⟶ regularColumnModule (k := k) (S := S) :=
    ModuleCat.ofHom (Finsupp.lapply i)
  have hmap : columnMapHom (k := k) (S := S) ev x = 0 :=
    assembleAction_regular_eq_zero (k := k) (S := S) (by
      calc
        assembleAction (k := k) (S := S)
            (regularColumnModule (k := k) (S := S))
            (columnMapHom (k := k) (S := S) ev x) =
            ev.hom (assembleAction (k := k) (S := S)
              (ModuleCat.of (R (k := k) (S := S)) (ι →₀ R (k := k) (S := S))) x) :=
          assembleAction_natural (k := k) (S := S) ev x
        _ = 0 := by simp [hx])
  have hq := congrArg (fun y : ColumnObject (k := k) (S := S)
      (regularColumnModule (k := k) (S := S)) => (y q : regularColumnModule (k := k) (S := S))) hmap
  change (Finsupp.lapply i) (x q : ι →₀ R (k := k) (S := S)) = 0 at hq
  simpa [Finsupp.lapply_apply] using hq

private theorem assembleAction_projective_eq_zero
    (M : ModuleCat.{u} (R (k := k) (S := S))) [Projective M]
    {x : ColumnObject (k := k) (S := S) M}
    (hx : assembleAction (k := k) (S := S) M x = 0) : x = 0 := by
  letI : Module.Projective (R (k := k) (S := S)) M :=
    ModuleCat.projective_of_module_projective M
  obtain ⟨s, hs⟩ := Module.Projective.out (R := R (k := k) (S := S)) (P := M)
  let sf : M ⟶ ModuleCat.of (R (k := k) (S := S))
      (M →₀ R (k := k) (S := S)) := ModuleCat.ofHom s
  have hfree : columnMapHom (k := k) (S := S) sf x = 0 :=
    assembleAction_finsupp_eq_zero (k := k) (S := S) (by
      calc
        assembleAction (k := k) (S := S)
            (ModuleCat.of (R (k := k) (S := S)) (M →₀ R (k := k) (S := S)))
            (columnMapHom (k := k) (S := S) sf x) =
            sf.hom (assembleAction (k := k) (S := S) M x) :=
          assembleAction_natural (k := k) (S := S) sf x
        _ = 0 := by simp [hx])
  funext q
  apply Subtype.ext
  have hq := congrArg (fun y : ColumnObject (k := k) (S := S)
      (ModuleCat.of (R (k := k) (S := S)) (M →₀ R (k := k) (S := S))) => (y q : M →₀ R (k := k) (S := S))) hfree
  change s (x q : M) = 0 at hq
  have hr := congrArg (Finsupp.linearCombination (R (k := k) (S := S)) id) hq
  change (x q : M) = 0
  simpa only [map_zero, hs (x q : M)] using hr

/-- Assembly is injective on every categorical projective right incidence module. -/
theorem assembleAction_projective_injective
    (M : ModuleCat.{u} (R (k := k) (S := S))) [Projective M] :
    Function.Injective (assembleAction (k := k) (S := S) M) := by
  intro x y hxy
  have hzero : assembleAction (k := k) (S := S) M (x - y) = 0 := by
    rw [map_sub, hxy]
    simp
  have hsub := assembleAction_projective_eq_zero (k := k) (S := S) M hzero
  exact sub_eq_zero.mp hsub

/-- The additive column functor carries every exact module short complex to an exact
short complex of abelian groups. -/
theorem columnAction_map_exact
    (T : ShortComplex (ModuleCat (R (k := k) (S := S)))) (hT : T.Exact) :
    (T.map (columnAction (k := k) (S := S))).Exact := by
  classical
  have hExact := (T.moduleCat_exact_iff).mp hT
  apply (ShortComplex.ab_exact_iff _).2
  intro x hx
  change columnMapHom (k := k) (S := S) T.g x = 0 at hx
  have hzero (q : Pair (S := S)) : T.g.hom (x q : T.X₂) = 0 := by
    have hq := congrArg (fun y : ColumnObject (k := k) (S := S) T.X₃ =>
      (y q : T.X₃)) hx
    change T.g.hom (x q : T.X₂) = 0 at hq
    exact hq
  choose y hy using fun q => hExact (x q) (hzero q)
  have hfixed (q : Pair (S := S)) :
      columnProjector (k := k) (S := S) q •
        (columnProjector (k := k) (S := S) q • y q) =
          columnProjector (k := k) (S := S) q • y q := by
    calc
      columnProjector (k := k) (S := S) q •
          (columnProjector (k := k) (S := S) q • y q) =
          (columnProjector (k := k) (S := S) q *
            columnProjector (k := k) (S := S) q) • y q := by rw [smul_smul]
      _ = columnProjector (k := k) (S := S) q • y q := by
        rw [columnProjector_mul_self]
  let z : ColumnObject (k := k) (S := S) T.X₁ :=
    fun q => ⟨columnProjector (k := k) (S := S) q • y q, hfixed q⟩
  refine ⟨z, ?_⟩
  change columnMapHom (k := k) (S := S) T.f z = x
  funext q
  apply Subtype.ext
  calc
    T.f.hom (columnProjector (k := k) (S := S) q • y q) =
        columnProjector (k := k) (S := S) q • T.f.hom (y q) := by
          rw [T.f.hom.map_smul]
    _ = columnProjector (k := k) (S := S) q • x q := by rw [hy q]
    _ = x q := (x q).property

/-- The additive column functor carries short-exact module rows to short-exact rows.
The endpoint maps remain injective and surjective coordinatewise. -/
theorem columnAction_map_shortExact
    (T : ShortComplex (ModuleCat (R (k := k) (S := S)))) (hT : T.ShortExact) :
    (T.map (columnAction (k := k) (S := S))).ShortExact := by
  classical
  have hExact := columnAction_map_exact (k := k) (S := S) T hT.exact
  have hInjective : Function.Injective T.f := hT.moduleCat_injective_f
  have hMono : Mono ((T.map (columnAction (k := k) (S := S))).f) :=
    (AddCommGrpCat.mono_iff_injective _).2 (by
      intro x y hxy
      funext q
      apply Subtype.ext
      apply hInjective
      have hq := congrArg (fun z => (z q : T.X₂)) hxy
      change T.f.hom (x q) = T.f.hom (y q)
      exact hq)
  have hSurjective : Function.Surjective T.g := hT.moduleCat_surjective_g
  have hEpi : Epi ((T.map (columnAction (k := k) (S := S))).g) :=
    (AddCommGrpCat.epi_iff_surjective _).2 (by
      intro x
      choose y hy using fun q : Pair (S := S) => hSurjective (x q)
      have hfixed (q : Pair (S := S)) :
          columnProjector (k := k) (S := S) q •
            (columnProjector (k := k) (S := S) q • y q) =
              columnProjector (k := k) (S := S) q • y q := by
        calc
          columnProjector (k := k) (S := S) q •
              (columnProjector (k := k) (S := S) q • y q) =
              (columnProjector (k := k) (S := S) q *
                columnProjector (k := k) (S := S) q) • y q := by rw [smul_smul]
          _ = columnProjector (k := k) (S := S) q • y q := by
            rw [columnProjector_mul_self]
      let z : ColumnObject (k := k) (S := S) T.X₂ :=
        fun q => ⟨columnProjector (k := k) (S := S) q • y q, hfixed q⟩
      refine ⟨z, ?_⟩
      change columnMapHom (k := k) (S := S) T.g z = x
      funext q
      apply Subtype.ext
      calc
        T.g.hom (columnProjector (k := k) (S := S) q • y q) =
            columnProjector (k := k) (S := S) q • T.g.hom (y q) := by
              rw [T.g.hom.map_smul]
        _ = columnProjector (k := k) (S := S) q • x q := by rw [hy q]
        _ = x q := (x q).property)
  exact { exact := hExact, mono_f := hMono, epi_g := hEpi }

end

end TDA.Persistence.IncidenceQuotientColumnAction
