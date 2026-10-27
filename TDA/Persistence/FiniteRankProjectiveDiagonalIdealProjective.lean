import TDA.Persistence.FiniteRankProjectiveEndAlgebra
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Projectivity of the diagonal interval-pair ideal

The diagonal ideal in the interval-pair incidence algebra is a projective left
module.  Its columns split from a finite free module: the column indexed by
`q` is supported at the diagonal point `(q.1, q.1)`.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective

open CategoryTheory
open TDA.Persistence.FiniteRankProjectiveEndAlgebra

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

abbrev Incidence := IncidenceAlgebra k (PairPoset S)
abbrev DiagonalIdeal := diagonalIdeal (k := k) (S := S)
abbrev ColumnModule := PairPoset S → Incidence (k := k) (S := S)

/-- The largest diagonal pair lying below a given interval pair. -/
def diagonalFloor (q : PairPoset S) : PairPoset S :=
  ⟨(q.val.1, q.val.1), le_rfl⟩

@[simp] theorem diagonalFloor_fst (q : PairPoset S) :
    (diagonalFloor (S := S) q).val.1 = q.val.1 := rfl

@[simp] theorem diagonalFloor_snd (q : PairPoset S) :
    (diagonalFloor (S := S) q).val.2 = q.val.1 := rfl

theorem diagonalFloor_isDiagonal (q : PairPoset S) :
    IsDiagonal (S := S) (diagonalFloor (S := S) q) := rfl

theorem diagonalFloor_le (q : PairPoset S) : diagonalFloor (S := S) q ≤ q := by
  change q.val.1 ≤ q.val.1 ∧ q.val.1 ≤ q.val.2
  exact ⟨le_rfl, q.property⟩

theorem le_diagonalFloor_iff_crossesDiagonal (p q : PairPoset S) :
    p ≤ diagonalFloor (S := S) q ↔ CrossesDiagonal (S := S) p q := by
  change (p.val.1 ≤ q.val.1 ∧ p.val.2 ≤ q.val.1) ↔ p.val.2 ≤ q.val.1
  constructor
  · exact And.right
  · intro h
    exact ⟨p.property.trans h, h⟩

/-- A coefficient of an ideal element can be nonzero only when its interval
meets the diagonal.  The assertion also covers incomparable pairs, whose
incidence coefficients already vanish by definition. -/
theorem diagonalIdeal_coeff_zero_of_not_crosses
    (f : DiagonalIdeal (k := k) (S := S)) (p q : PairPoset S)
    (h : ¬ CrossesDiagonal (S := S) p q) : f.1 p q = 0 := by
  by_cases hpq : p ≤ q
  · exact crossingDeltaSpan_coeff_zero_of_not_crosses
      (k := k) (S := S) f.1
      ((mem_diagonalIdeal_iff_mem_crossingDeltaSpan
        (k := k) (S := S) f.1).1 f.property) p q h
  · exact f.1.eq_zero_of_not_le' hpq

/-- The diagonal ideal is characterized by its coefficients on crossing
intervals. -/
theorem mem_diagonalIdeal_iff_coeff_zero_of_not_crosses (f : Incidence (k := k) (S := S)) :
    f ∈ DiagonalIdeal (k := k) (S := S) ↔
      ∀ p q : PairPoset S, ¬ CrossesDiagonal (S := S) p q → f p q = 0 := by
  constructor
  · intro hf p q h
    exact diagonalIdeal_coeff_zero_of_not_crosses
      (k := k) (S := S) ⟨f, hf⟩ p q h
  · intro hf
    classical
    rw [incidence_eq_deltaExpansion (k := k) (S := S) f]
    change (∑ c ∈ (Finset.univ : Finset (ComparablePair S)),
      f c.val.1 c.val.2 •
        delta (k := k) (S := S) c.val.1 c.val.2 c.property) ∈
      DiagonalIdeal (k := k) (S := S)
    apply Submodule.sum_mem
    intro c hc
    by_cases hcross : CrossesDiagonal (S := S) c.val.1 c.val.2
    · simpa only [Algebra.algebraMap_eq_smul_one, smul_one_mul] using
        (Ideal.mul_mem_left (DiagonalIdeal (k := k) (S := S))
          (algebraMap k (Incidence (k := k) (S := S)) (f c.val.1 c.val.2))
          (diagonalIdeal_mem_delta_of_cross (k := k) (S := S)
            c.val.1 c.val.2 c.property hcross))
    · rw [hf c.val.1 c.val.2 hcross]
      simp

private theorem mul_apply_truncate_at
    (a f : Incidence (k := k) (S := S)) (p q r : PairPoset S)
    (hrq : r ≤ q) (hz : ∀ x, ¬ x ≤ r → f x q = 0) :
    (a * f) p q = ∑ x ∈ Finset.Icc p r, a p x * f x q := by
  rw [IncidenceAlgebra.mul_apply]
  have hsub : Finset.Icc p r ⊆ Finset.Icc p q := by
    intro x hx
    rcases Finset.mem_Icc.mp hx with ⟨hpx, hxr⟩
    exact Finset.mem_Icc.mpr ⟨hpx, hxr.trans hrq⟩
  exact (Finset.sum_subset hsub (by
    intro x hx hxnot
    have hnot : ¬ x ≤ r := by
      intro hxr
      exact hxnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1, hxr⟩)
    rw [hz x hnot]
    simp)).symm

/-- The column of an ideal element supported at the diagonal floor. -/
private def includeColumn (f : DiagonalIdeal (k := k) (S := S))
    (q : PairPoset S) : Incidence (k := k) (S := S) := by
  classical
  refine ⟨fun p t => if t = diagonalFloor (S := S) q then f.1 p q else 0, ?_⟩
  intro p t hnot
  by_cases ht : t = diagonalFloor (S := S) q
  · subst t
    simp only [if_pos rfl]
    apply diagonalIdeal_coeff_zero_of_not_crosses (k := k) (S := S) f p q
    intro hcross
    exact hnot ((le_diagonalFloor_iff_crossesDiagonal (S := S) p q).2 hcross)
  · simp [ht]

/-- Embed an ideal element into the family of its columns at the diagonal
floor of each terminal vertex. -/
def includeColumns :
    DiagonalIdeal (k := k) (S := S) →ₗ[Incidence (k := k) (S := S)]
      ColumnModule (k := k) (S := S) where
  toFun f q := includeColumn (k := k) (S := S) f q
  map_add' f g := by
    funext q
    ext p t
    by_cases h : t = diagonalFloor (S := S) q <;> simp [includeColumn, h]
  map_smul' a f := by
    funext q
    ext p t
    change (if t = diagonalFloor (S := S) q then (a * f.1) p q else 0) =
      (a * includeColumn (k := k) (S := S) f q) p t
    by_cases ht : t = diagonalFloor (S := S) q
    · subst t
      simp only [if_pos rfl]
      rw [mul_apply_truncate_at (k := k) (S := S) a f.1 p q
        (diagonalFloor (S := S) q) (diagonalFloor_le (S := S) q)]
      · simp only [IncidenceAlgebra.mul_apply]
        apply Finset.sum_congr rfl
        intro x hx
        simp [includeColumn]
      · intro x hxr
        exact diagonalIdeal_coeff_zero_of_not_crosses
          (k := k) (S := S) f x q
          (fun hcross => hxr
            ((le_diagonalFloor_iff_crossesDiagonal (S := S) x q).2 hcross))
    · simp [IncidenceAlgebra.mul_apply, includeColumn, ht]

@[simp] theorem includeColumns_apply
    (f : DiagonalIdeal (k := k) (S := S)) (q p t : PairPoset S) :
    includeColumns (k := k) (S := S) f q p t =
      if t = diagonalFloor (S := S) q then f.1 p q else 0 := rfl

/-- Right multiplication by `δ_{d,q}` places the `d`-column at `q`. -/
theorem mul_delta_right_apply_column
    (a : Incidence (k := k) (S := S)) (d q p t : PairPoset S)
    (hdq : d ≤ q) :
    (a * delta (k := k) (S := S) d q hdq) p t =
      if t = q then a p d else 0 := by
  classical
  by_cases ht : t = q
  · subst t
    by_cases hpd : p ≤ d
    · rw [IncidenceAlgebra.mul_apply]
      have hdmem : d ∈ Finset.Icc p q := Finset.mem_Icc.mpr ⟨hpd, hdq⟩
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

/-- Each included diagonal-floor column is fixed by right multiplication by its
diagonal-floor idempotent. -/
theorem includeColumns_mul_diagonalFloorIdempotent
    (f : DiagonalIdeal (k := k) (S := S)) (q : PairPoset S) :
    includeColumns (k := k) (S := S) f q *
        delta (k := k) (S := S) (diagonalFloor (S := S) q)
          (diagonalFloor (S := S) q) le_rfl =
      includeColumns (k := k) (S := S) f q := by
  classical
  ext p t
  rw [mul_delta_right_apply_column (k := k) (S := S)
    (includeColumns (k := k) (S := S) f q) (diagonalFloor (S := S) q)
    (diagonalFloor (S := S) q) p t le_rfl]
  by_cases ht : t = diagonalFloor (S := S) q
  · subst t
    simp
  · simp [ht]

/-- Reassemble the chosen diagonal-floor coefficients as an incidence
function. -/
private def assembleValue (g : ColumnModule (k := k) (S := S)) :
    Incidence (k := k) (S := S) := by
  refine ⟨fun p q => g q p (diagonalFloor (S := S) q), ?_⟩
  intro p q hnot
  apply (g q).eq_zero_of_not_le'
  intro hp
  exact hnot (hp.trans (diagonalFloor_le (S := S) q))

private theorem assembleValue_mem_diagonalIdeal
    (g : ColumnModule (k := k) (S := S)) :
    assembleValue (k := k) (S := S) g ∈ DiagonalIdeal (k := k) (S := S) := by
  apply (mem_diagonalIdeal_iff_coeff_zero_of_not_crosses
    (k := k) (S := S) (assembleValue (k := k) (S := S) g)).2
  intro p q hcross
  apply (g q).eq_zero_of_not_le'
  intro hp
  exact hcross ((le_diagonalFloor_iff_crossesDiagonal (S := S) p q).1 hp)

/-- Assemble a family of columns by reading its coefficient at the diagonal
floor of each terminal vertex. -/
def assembleColumns :
    ColumnModule (k := k) (S := S) →ₗ[Incidence (k := k) (S := S)]
      DiagonalIdeal (k := k) (S := S) where
  toFun g := ⟨assembleValue (k := k) (S := S) g,
    assembleValue_mem_diagonalIdeal (k := k) (S := S) g⟩
  map_add' g h := by
    apply Subtype.ext
    ext p q
    rfl
  map_smul' a g := by
    let assembled := assembleValue (k := k) (S := S) g
    apply Subtype.ext
    ext p q
    change (a * g q) p (diagonalFloor (S := S) q) =
      (a * assembled) p q
    rw [mul_apply_truncate_at (k := k) (S := S) a
      assembled p q
      (diagonalFloor (S := S) q) (diagonalFloor_le (S := S) q)]
    · simp only [IncidenceAlgebra.mul_apply]
      apply Finset.sum_congr rfl
      intro x hx
      rfl
    · intro x hxr
      change g q x (diagonalFloor (S := S) q) = 0
      exact (g q).eq_zero_of_not_le' hxr

@[simp] theorem assembleColumns_apply
    (g : ColumnModule (k := k) (S := S)) (p q : PairPoset S) :
    (assembleColumns (k := k) (S := S) g).1 p q =
      g q p (diagonalFloor (S := S) q) := rfl

private theorem incidenceFinsetSum_apply_column {ι : Type}
    (s : Finset ι) (g : ι → Incidence (k := k) (S := S))
    (p q : PairPoset S) :
    (∑ i ∈ s, g i) p q = ∑ i ∈ s, g i p q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, IncidenceAlgebra.add_apply, ih]

/-- Reassembly is the sum of the chosen terminal columns multiplied by their
diagonal-floor matrix units. -/
theorem assembleColumns_eq_sum_mul_delta
    (g : ColumnModule (k := k) (S := S)) :
    (assembleColumns (k := k) (S := S) g).1 =
      ∑ q : PairPoset S,
        g q * delta (k := k) (S := S) (diagonalFloor (S := S) q) q
          (diagonalFloor_le (S := S) q) := by
  classical
  ext p t
  rw [assembleColumns_apply, incidenceFinsetSum_apply_column]
  simp_rw [mul_delta_right_apply_column]
  simp

/-- Reassembling the included columns returns the original ideal element. -/
theorem assembleColumns_comp_includeColumns :
    (assembleColumns (k := k) (S := S)).comp
      (includeColumns (k := k) (S := S)) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  ext p q
  simp [includeColumns, assembleColumns, assembleValue, includeColumn]

/-- The actual finite family of incidence columns is free over the incidence
algebra. -/
theorem columnModule_projective :
    Module.Projective (Incidence (k := k) (S := S))
      (ColumnModule (k := k) (S := S)) := by
  exact Module.Projective.of_basis
    (Pi.basisFun (Incidence (k := k) (S := S)) (PairPoset S))

/-- The diagonal ideal is a direct summand of the finite free column module,
and hence projective as a left incidence-algebra module. -/
theorem diagonalIdeal_projective :
    Module.Projective (Incidence (k := k) (S := S))
      (DiagonalIdeal (k := k) (S := S)) := by
  letI := columnModule_projective (k := k) (S := S)
  exact Module.Projective.of_split
    (includeColumns (k := k) (S := S))
    (assembleColumns (k := k) (S := S))
    (assembleColumns_comp_includeColumns (k := k) (S := S))

/-- The diagonal ideal is also projective in the category of left incidence
algebra modules. -/
theorem diagonalIdeal_projective_object :
    CategoryTheory.Projective
      (ModuleCat.of (Incidence (k := k) (S := S))
        (DiagonalIdeal (k := k) (S := S))) := by
  letI := diagonalIdeal_projective (k := k) (S := S)
  exact inferInstance

end

end TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
