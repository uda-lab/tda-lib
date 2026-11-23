import TDA.Persistence.Morse.FilteredHomology
import TDA.Persistence.Reduction.FilteredNormalForm.NormalMatrix

/-!
# A reducer order for filtered based complexes

The column reducer of `TDA.Persistence.Reduction` runs on a square matrix over `Fin m`. Its
normal-form theorem `matrixReductionTrace_normalForm_input` needs a square-zero matrix that is
strictly upper triangular (`StrictBoundary`: a nonzero entry in row `r` and column `c` has
`r < c`) and lowers a degree function by one (`LowersDegree`). A filtered based complex
`(ι, degree, grade, D)` of `TDA.Persistence.Morse.Cancellation` comes with no such order: after
a cancellation the inherited order of the survivors need not be triangular (fixture F4 of
`TDA.Persistence.Morse.UnitCancellationExamples`, and fixtures R1 and R2 of
`TDA.Persistence.Morse.ReducerOrderExamples`).

For a carrier `ι` with a linear order, which serves as the stable identity of the generators,
`key degree grade x` is `(grade x, degree x, x)` in the lexicographic order. It is injective,
and a nonzero entry `D r c` of a filtered differential has `key r < key c`, because
`grade r ≤ grade c` and `degree c = degree r + 1` (`key_lt_of_ne_zero`).

`sortList degree grade L` is the insertion sort of a list by `key`. It is a permutation of `L`,
strictly increasing in `key` when `L` has no duplicates, and depends on `L` only up to
permutation (`sortList_eq_of_perm`). On a finite carrier, `sortedGenerators degree grade` is the
sort of the elements of `Finset.univ`, computed through the quotient, and `reducerEquiv` is the
resulting enumeration `Fin (sortedGenerators degree grade).length ≃ ι`. It is strictly
increasing in `key` (`key_strictMono`), so the grades are monotone along it, and
`i < j ↔ key (reducerEquiv … i) < key (reducerEquiv … j)`.

`reducerMatrix degree grade D` is `D` in this order. For a filtered differential it is again a
filtered differential; over a field it is strictly upper triangular and lowers
`degree ∘ reducerEquiv degree grade` by one, so the reducer's normal-form theorem applies to it
(`reducerMatrix_normalForm_input`). The
original generators are kept: `reducerEquiv` is an equivalence onto `ι`, and
`reducerContraction` is the identity contraction transported along it, whose
`sublevelHomologyIso` is the isomorphism `reducerHomologyIso` of grade-sublevel homology
persistence modules.

This is a library derivation. The module runs no reduction and states nothing about barcodes or
diagrams.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.ReducerOrder

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation

section Key

variable {ι : Type*} [LinearOrder ι] (degree : ι → ℕ) (grade : ι → ℤ)

/-- The reducer key of a generator: its grade, then its degree, then the generator itself, in
the lexicographic order. -/
def key (x : ι) : ℤ ×ₗ ℕ ×ₗ ι :=
  toLex (grade x, toLex (degree x, x))

omit [LinearOrder ι] in
/-- The key determines the generator. -/
theorem key_injective : Function.Injective (key degree grade) := by
  intro x y h
  simpa [key] using congrArg (fun z => (ofLex (ofLex z).2).2) h

variable {degree grade}

/-- A generator of degree one less than another, at grade at most its grade, has the smaller
key. -/
theorem key_lt {x y : ι} (hg : grade x ≤ grade y) (hd : degree y = degree x + 1) :
    key degree grade x < key degree grade y := by
  simp only [key, Prod.Lex.toLex_lt_toLex]
  omega

variable {k : Type*} [CommRing k] [Fintype ι] {D : Matrix ι ι k}

/-- A nonzero entry of a filtered differential has a smaller key in its row than in its
column. -/
theorem key_lt_of_ne_zero (hD : IsFilteredDifferential degree grade D) {r c : ι}
    (h : D r c ≠ 0) : key degree grade r < key degree grade c :=
  key_lt (hD.grade_le r c h) (hD.lowers_degree r c h)

end Key

section Sorting

variable {ι : Type*} [LinearOrder ι] (degree : ι → ℕ) (grade : ι → ℤ)

/-- The insertion sort of a list of generators by `key`. -/
def sortList (L : List ι) : List ι :=
  L.insertionSort fun x y => key degree grade x ≤ key degree grade y

/-- The sorted list is a permutation of the list. -/
theorem sortList_perm (L : List ι) : (sortList degree grade L).Perm L :=
  List.perm_insertionSort _ _

/-- The sorted list is sorted by non-decreasing key. -/
theorem pairwise_sortList_le (L : List ι) :
    (sortList degree grade L).Pairwise fun x y => key degree grade x ≤ key degree grade y := by
  have : Std.Total fun x y : ι => key degree grade x ≤ key degree grade y :=
    ⟨fun _ _ => le_total _ _⟩
  have : IsTrans ι fun x y : ι => key degree grade x ≤ key degree grade y :=
    ⟨fun _ _ _ => le_trans⟩
  exact List.pairwise_insertionSort _ _

/-- A list without duplicates sorts to a list strictly increasing in key. -/
theorem pairwise_sortList {L : List ι} (hL : L.Nodup) :
    (sortList degree grade L).Pairwise fun x y => key degree grade x < key degree grade y :=
  ((pairwise_sortList_le degree grade L).and ((sortList_perm degree grade L).nodup_iff.mpr hL)).imp
    fun h => lt_of_le_of_ne h.1 fun he => h.2 (key_injective degree grade he)

/-- The sorted list depends on the list only up to permutation. -/
theorem sortList_eq_of_perm {L L' : List ι} (h : L.Perm L') :
    sortList degree grade L = sortList degree grade L' :=
  List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => key_injective degree grade (le_antisymm hab hba))
    (pairwise_sortList_le degree grade L) (pairwise_sortList_le degree grade L')
    ((sortList_perm degree grade L).trans (h.trans (sortList_perm degree grade L').symm))

variable [Fintype ι]

/-- The generators of a finite carrier sorted by `key`: the sort of the elements of
`Finset.univ`, computed through the quotient. -/
def sortedGenerators : List ι :=
  Quotient.liftOn (Finset.univ : Finset ι).val (sortList degree grade)
    fun _ _ h => sortList_eq_of_perm degree grade h

/-- For any enumeration of the carrier without duplicates, `sortedGenerators` is its sort. -/
theorem sortedGenerators_eq {L : List ι} (hn : L.Nodup) (hc : ∀ x, x ∈ L) :
    sortedGenerators degree grade = sortList degree grade L := by
  obtain ⟨L', hL'⟩ := Quotient.exists_rep (Finset.univ : Finset ι).val
  have hp : L'.Perm L := by
    have h1 : (L' : Multiset ι) = Finset.univ.val := hL'
    rw [List.perm_iff_count]
    intro a
    have : (Finset.univ.val : Multiset ι).count a = 1 :=
      Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ a)
    rw [← Multiset.coe_count, h1, this, List.count_eq_one_of_mem hn (hc a)]
  unfold sortedGenerators
  rw [← hL']
  exact sortList_eq_of_perm degree grade hp

/-- Every generator occurs in `sortedGenerators`. -/
theorem mem_sortedGenerators (x : ι) : x ∈ sortedGenerators degree grade := by
  rw [sortedGenerators_eq degree grade (Finset.nodup_toList Finset.univ)
    fun y => Finset.mem_toList.mpr (Finset.mem_univ y)]
  exact (sortList_perm degree grade _).mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ x))

/-- `sortedGenerators` is strictly increasing in key. -/
theorem pairwise_sortedGenerators :
    (sortedGenerators degree grade).Pairwise
      fun x y => key degree grade x < key degree grade y := by
  rw [sortedGenerators_eq degree grade (Finset.nodup_toList Finset.univ)
    fun y => Finset.mem_toList.mpr (Finset.mem_univ y)]
  exact pairwise_sortList degree grade (Finset.nodup_toList Finset.univ)

/-- `sortedGenerators` has no duplicates. -/
theorem nodup_sortedGenerators : (sortedGenerators degree grade).Nodup :=
  (pairwise_sortedGenerators degree grade).imp fun h => ne_of_apply_ne _ (ne_of_lt h)

/-- `sortedGenerators` lists every generator once. -/
theorem length_sortedGenerators :
    (sortedGenerators degree grade).length = Fintype.card ι := by
  rw [sortedGenerators_eq degree grade (Finset.nodup_toList Finset.univ)
    fun y => Finset.mem_toList.mpr (Finset.mem_univ y), sortList, List.length_insertionSort,
    Finset.length_toList, Finset.card_univ]

/-- The reducer order: list positions of `sortedGenerators` as an equivalence onto the
carrier. -/
def reducerEquiv : Fin (sortedGenerators degree grade).length ≃ ι :=
  List.Nodup.getEquivOfForallMemList _ (nodup_sortedGenerators degree grade)
    (mem_sortedGenerators degree grade)

/-- The reducer order reads the sorted list. -/
@[simp] theorem reducerEquiv_apply (i : Fin (sortedGenerators degree grade).length) :
    reducerEquiv degree grade i = (sortedGenerators degree grade).get i :=
  rfl

/-- The key is strictly increasing along the reducer order. -/
theorem key_strictMono : StrictMono (key degree grade ∘ reducerEquiv degree grade) := by
  intro i j hij
  exact List.pairwise_iff_getElem.mp (pairwise_sortedGenerators degree grade) i j i.isLt j.isLt hij

/-- Positions in the reducer order compare as their keys. -/
theorem lt_iff_key_lt {i j : Fin (sortedGenerators degree grade).length} :
    i < j ↔ key degree grade (reducerEquiv degree grade i) <
      key degree grade (reducerEquiv degree grade j) :=
  (key_strictMono degree grade).lt_iff_lt.symm

/-- The grades are monotone along the reducer order. -/
theorem monotone_grade : Monotone (grade ∘ reducerEquiv degree grade) := by
  intro i j hij
  have h := (key_strictMono degree grade).monotone hij
  exact Prod.Lex.monotone_fst _ _ h

end Sorting

section Matrix

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {k : Type*} [CommRing k]
  (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k)

/-- The filtered differential in the reducer order. -/
def reducerMatrix :
    Matrix (Fin (sortedGenerators degree grade).length)
      (Fin (sortedGenerators degree grade).length) k :=
  D.submatrix (reducerEquiv degree grade) (reducerEquiv degree grade)

variable {degree grade D}

/-- In the reducer order, a filtered differential still squares to zero. -/
theorem reducerMatrix_sq_zero (hD : IsFilteredDifferential degree grade D) :
    reducerMatrix degree grade D * reducerMatrix degree grade D = 0 := by
  rw [reducerMatrix, Matrix.submatrix_mul_equiv, hD.sq_zero, Matrix.submatrix_zero]
  rfl

/-- In the reducer order, a filtered differential is a filtered differential for the transported
degree and grade. -/
theorem isFilteredDifferential_reducerMatrix (hD : IsFilteredDifferential degree grade D) :
    IsFilteredDifferential (degree ∘ reducerEquiv degree grade)
      (grade ∘ reducerEquiv degree grade) (reducerMatrix degree grade D) :=
  ⟨⟨reducerMatrix_sq_zero hD, fun _ _ h => hD.lowers_degree _ _ h⟩,
    fun _ _ h => hD.grade_le _ _ h⟩

variable (degree grade D)

/-- The identity contraction transported along the reducer order: a filtered contraction of the
complex onto itself in the reducer order. -/
def reducerContraction :
    FilteredContraction degree grade D (degree ∘ reducerEquiv degree grade)
      (grade ∘ reducerEquiv degree grade) (reducerMatrix degree grade D) :=
  ((FilteredContraction.refl degree grade D).reindex (reducerEquiv degree grade).symm).copy
    rfl rfl rfl

/-- The projection of `reducerContraction` is the identity read in the reducer order. -/
theorem reducerContraction_proj :
    (reducerContraction degree grade D).proj =
      (1 : Matrix ι ι k).submatrix (reducerEquiv degree grade) id :=
  rfl

/-- The inclusion of `reducerContraction` is the identity read in the reducer order. -/
theorem reducerContraction_incl :
    (reducerContraction degree grade D).incl =
      (1 : Matrix ι ι k).submatrix id (reducerEquiv degree grade) :=
  rfl

/-- The homotopy of `reducerContraction` is zero. -/
theorem reducerContraction_htpy : (reducerContraction degree grade D).htpy = 0 :=
  rfl

end Matrix

section Reducer

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {k : Type*} [Field k]
  (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k)

/-- A filtered differential in an order along which the key is strictly increasing is strictly
upper triangular. -/
theorem strictBoundary_submatrix {m : ℕ} (e : Fin m ≃ ι)
    (he : StrictMono (key degree grade ∘ e)) (hD : IsFilteredDifferential degree grade D) :
    StrictBoundary (D.submatrix e e) := by
  intro _ _ h
  exact he.lt_iff_lt.mp (key_lt_of_ne_zero hD h)

variable {degree grade D}

/-- In the reducer order, a filtered differential is strictly upper triangular. -/
theorem strictBoundary_reducerMatrix (hD : IsFilteredDifferential degree grade D) :
    StrictBoundary (reducerMatrix degree grade D) :=
  strictBoundary_submatrix degree grade D _ (key_strictMono degree grade) hD

/-- In the reducer order, a filtered differential lowers the transported degree by one. -/
theorem lowersDegree_reducerMatrix (hD : IsFilteredDifferential degree grade D) :
    LowersDegree (degree ∘ reducerEquiv degree grade) (reducerMatrix degree grade D) :=
  fun _ _ h => hD.lowers_degree _ _ h

/-- **The reducer accepts the reducer order.** For a filtered differential in the reducer order,
the chronological reducer supplies all the normal-form inputs of
`matrixReductionTrace_normalForm_input`. -/
theorem reducerMatrix_normalForm_input [DecidableEq k]
    (hD : IsFilteredDifferential degree grade D) :
    let M := reducerMatrix degree grade D
    let ops := matrixReductionTrace M
    let R := replay M ops
    let V := traceChange ops
    let W := traceChangeInv ops
    R = M * V ∧ TraceChangeCertificate (degree ∘ reducerEquiv degree grade) V W ∧
      LowersDegree (degree ∘ reducerEquiv degree grade) R ∧ StrictBoundary R ∧
      DistinctPivots R ∧
      (∀ j i, columnPivot (R.col j) = some i → columnPivot (R.col i) = none) :=
  matrixReductionTrace_normalForm_input _ _ (reducerMatrix_sq_zero hD)
    (strictBoundary_reducerMatrix hD) (lowersDegree_reducerMatrix hD)

end Reducer

section Homology

variable {ι : Type} [LinearOrder ι] [Fintype ι] {k : Type*} [CommRing k]
  (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k)

/-- The grade-sublevel homology persistence modules of a based complex and of its reducer
order are isomorphic in every degree, by `reducerContraction`. -/
noncomputable def reducerHomologyIso (p : ℕ) :
    sublevelHomologyPModule degree grade D p ≅
      sublevelHomologyPModule (degree ∘ reducerEquiv degree grade)
        (grade ∘ reducerEquiv degree grade) (reducerMatrix degree grade D) p :=
  (reducerContraction degree grade D).sublevelHomologyIso p

end Homology

end TDA.Persistence.Morse.ReducerOrder
