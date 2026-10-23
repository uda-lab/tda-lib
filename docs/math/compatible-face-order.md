# Canonical grade-compatible face orders

For a finite presentation `C : TDA.Simplicial.FiniteComplex n` and a monotone face-value
function `f`, `TDA.Filtration.CompatibleOrder.ofLex C f` gives a bijection from
`Fin (Fintype.card (TotalFace C.toPre))` to the nonempty faces. Its key orders faces by

1. `f.value s`;
2. `s.val.card`;
3. `Colex s.val`, using the standard order on `Fin n`.

The grade is the primary coordinate. Cardinality ensures every proper face precedes its coface
when their grades tie. Colex makes the full key injective when grades and cardinalities also
tie. Consequently, the returned enumeration has nondecreasing grades and strict key increase.
All faces of the supplied presentation occur once; absent ambient vertices and the empty face
are not added.

The key's lexicographic order is pulled back along its injective map to the face subtype.
The finite order isomorphism from `Fintype.orderIsoFinOfCardEq` then supplies the canonical
sorted enumeration. This local order is used only inside the constructor and its key-order
theorem. The ambient `TotalFace` order remains set inclusion, so unrelated singleton faces
remain incomparable outside the construction.

An empty presentation yields `Fin 0` and its empty equivalence. No face, vertex, grade default,
or inhabitant of the grade type is selected. Concrete lists for empty, tied, nonconstant,
cross-dimensional, and colex-discriminator presentations are evaluated in
[`CompatibleOrderExamples.lean`](../../TDA/Filtration/CompatibleOrderExamples.lean); that file
also exhibits a monotone-grade permutation rejected by proper-face precedence.

The finite presentation supplies executable face data. The constructor evaluates on the
integer-valued examples; an arbitrary value function is not thereby claimed to be runtime
computable. The result is a finite presentation constructor, not a generic noncomputable linear
extension. It establishes no range-order equivalence, initial-segment theorem, sublevel
reconstruction, simplexwise reindexing, topological result, homology, reduction, pairing, or
barcode consequence.

## Source and API notes

- [`FiniteComplex.lean`](../../TDA/Simplicial/FiniteComplex.lean) converts the stored finite
  face collection directly to `TotalFace` and provides its `Fintype`; this constructor reuses
  that instance and its membership proofs.
- [`FilterFunction.lean`](../../TDA/Filtration/FilterFunction.lean) supplies values on faces and weak monotonicity under inclusion. No additional filter assumption is introduced.
- The repository baseline for those modules is develop
  [`fa0cece24f7c00a820981872494092d8a4a3df76`](https://github.com/uda-lab/tda-lib/commit/fa0cece24f7c00a820981872494092d8a4a3df76).
- Mathlib is pinned at `0df444a360eaa60ab8c11dca51a86af692955474`. The implementation reuses
  [`Finset.Sort`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Sort.lean)
  (`Fintype.orderIsoFinOfCardEq`, `Finset.orderIsoOfFin`; the executable path passes through
  `Finset.sort`, `Multiset.sort`, and `List.SortedLT.getIso`),
  [`Order.Basic`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/Basic.lean)
  (`LinearOrder.lift'`),
  [`Prod.Lex`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Prod/Lex.lean),
  [`Colex`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Combinatorics/Colex.lean),
  and [`Order.Lex`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/Lex.lean).
  The colex linear order is on `Colex (Finset (Fin n))`; the nested lex orders and existing
  equivalences are used directly. No sorting algorithm or ordering instance is added to
  Mathlib.
- The primary mathematical source for the API is the finite presentation and monotone filter
  already in this repository. This document does not attribute the constructor or its
  tie-breaker to an external persistence theorem. The broader order-equivalence and
  initial-segment questions remain in parent Issue #42.
