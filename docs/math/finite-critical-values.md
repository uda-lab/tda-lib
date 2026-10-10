# Finite critical-value enumeration

## Construction

Let `K` be a preabstract simplicial complex on an arbitrary type `V`, and suppose the actual
face type `TDA.Simplicial.TotalFace K` is equipped with `Fintype`. For a
`FilterFunction K α` with `[LinearOrder α]`, define

```lean
criticalValues f = Finset.univ.image f.value
criticalValue f = f.criticalValues.orderEmbOfFin rfl
gradeFiltration f =
  TDA.Filtration.reindex f.criticalValue.toOrderHom f.sublevelFiltration
```

The finite set contains the distinct values on actual nonempty faces, so its cardinality counts
grades rather than faces. `criticalValue` lists those values in increasing order. The grade
filtration is exactly the existing sublevel filtration reindexed along this embedding.

## Exact threshold recovery

The public laws in `TDA.Filtration.CriticalValues` establish that:

- `mem_criticalValues` identifies membership with attainment on an actual face.
- `criticalValues_eq_empty_iff` characterizes the empty image by `K = ⊥`.
- `criticalValue_mem` and `exists_criticalValue_eq` give the two directions of coverage
  between the enumeration and face values.
- `gradeFiltration_apply` identifies each indexed stage with its corresponding sublevel.
- `sublevel_eq_bot_of_lt_first` handles thresholds below the least grade.
- `sublevel_eq_grade_of_gap` identifies the stage when the threshold lies below every later
  grade; `sublevel_eq_grade_of_adjacent` supplies this hypothesis for adjacent grades.
- `sublevel_eq_self_of_last_le` says a threshold at or above the greatest grade recovers `K`.
- `sublevel_eq_bot_or_grade` recovers every threshold: its sublevel is bottom or equals a
  grade at or below that threshold. Its proof takes the maximum of the finite set of critical
  values at most the threshold when that set is nonempty.

No bottom sentinel is inserted. A nonempty grade set starts at its least attained value, and
tied faces enter together. If `K = ⊥`, then the grade type is `Fin 0`; its filtration has an
empty index type and every ambient threshold still has bottom sublevel. The final-stage law
returns `K`, which can be strictly smaller than the ambient top complex.

## Assumptions and scope

The general API assumes only a linear order on `α`, the existing complex `K` on `V`, and a
supplied `Fintype (TDA.Simplicial.TotalFace K)`. It adds no order, finiteness, decidable
equality, or nonemptiness assumption on `V`, and no inhabitedness or density assumption on
`α`. Empty `V` and empty `α` are allowed where the existing types and instances permit
them. The result is a theory-side finite enumeration from supplied data; it does not construct
that data from a finite presentation.

## Source correspondence

This construction extends the existing face-value sublevel API directly:

- `TDA/Filtration/FilterFunction.lean` (blob
  `bcf4907aaec0a1cb2ce116c661230a115fdf4a65`) defines the actual-face domain, sublevel
  membership, monotonicity, and bottom/self endpoint lemmas.
- `TDA/Filtration/Basic.lean` (blob
  `77a63f98ba6e7c3cbfe6fc92f6a51014643ef32f`) supplies `SimplicialFiltration`,
  `reindex`, and its evaluation law.
- `TDA/Simplicial/Bridge.lean` (blob
  `a811965673ef1d3da54efe0aef768bcbf3ae1d50`) supplies the type of actual nonempty faces.
- `Mathlib.Data.Finset.Sort` at pinned mathlib revision
  `0df444a360eaa60ab8c11dca51a86af692955474` supplies `Finset.orderEmbOfFin` and the
  increasing finite enumeration used here.

The membership, endpoint, plateau, and threshold-recovery proofs are direct consequences of
these definitions and finite ordered-set facts. No external persistence theorem is translated
or claimed. This module does not construct a finite complex presentation, choose a compatible
simplex order, or establish homology, barcode, stability, or Reeb results.
