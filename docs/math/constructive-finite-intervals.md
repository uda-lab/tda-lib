# Executing finite interval and list-barcode modules

A finite interval on `Fin N` has natural endpoints `birth < death ≤ N` and
support `birth ≤ i.val < death`. Its module has the coefficient field as its
fiber on the support and the zero submodule elsewhere. A structure map acts as
the identity when both endpoints are alive and as zero otherwise.

`FiniteInterval.decidableAlive` decides support membership by natural-number
arithmetic. `FiniteInterval.fiber`, `intervalMap` and `intervalModule` use these
decisions in their executable data. `barcodeModuleOfList` forms the same
coordinatewise product, with one coordinate for every position in its input
list. These definitions require a field, with no coefficient-equality decision
or supplied basis.

Concrete field operations must themselves be executable. The public consumers
in `ConstructiveIntervalExamples` execute both ℚ and F₂; this does not assert
executability of an arbitrary field instance chosen by a caller.

## Endpoints and zero cases

For an interval `[1,4)` on `Fin 5`, a nonzero value at index 1 maps unchanged to
indices 2 and 3 and to zero at index 4. Index 0 has a zero source fiber. An
interval with `death = N` survives at index `N−1` when `N > 0`. There is no index
`N` in `Fin N`, and this endpoint convention does not mean infinite lifetime.

An empty barcode list has no coordinates at any stage. At `N = 0` the index
category itself is empty; the empty list/module is available without constructing
an impossible finite interval. At `N = 1`, `[0,1)` has its single alive fiber at
index 0.

The examples apply actual public structure maps, including self and composite
maps:

```lean
import TDA.Persistence.ConstructiveIntervalExamples

open TDA.Persistence.ConstructiveIntervalExamples

#eval action A 1 2 (by decide) (7 : ℚ)  -- 7
#eval action A 1 4 (by decide) (7 : ℚ)  -- 0
#eval action B 0 4 (by decide) (7 : ℚ)  -- 7; B.death = 5
```

`intervalMap_apply_val` describes these actions directly in the coefficient
field. The existing rank characteristic theorem retains its explicit
`[decAlive : Decidable (I.alive i ∧ I.alive j)]` argument.

## Reordering lists with repeated intervals

`barcodeEnumerationNatIso hperm` executes the existing occurrence correspondence
for `hperm : xs.Perm ys`. Batteries' `List.Perm.idxBij` matches the nth occurrence
of each equal interval. The forward component at a target position `s` reads
source position `hperm.symm.idxBij s`; the inverse at source position `t` reads
target position `hperm.idxBij t`. The public
`barcodeEnumerationNatIso_hom_apply_val` and
`barcodeEnumerationNatIso_inv_apply_val` state these coefficient formulas.

For `xs = [A,B,A]` and `ys = [A,A,B]`, the source-to-target index map is
`[0,2,1]`. Distinct values in the two A coordinates retain their first and second
occurrences:

```lean
#eval forward reorder 1 sourceCoefficients  -- [2, 7, 5]
#eval inverse reorder 1 targetCoefficients  -- [11, 17, 13]
#eval naturalityLeft                       -- [0, 0, 5]
#eval naturalityRight                      -- [0, 0, 5]
```

Both naturality expressions transport from index 2 to index 4. The A coordinates
die, while B survives. They execute the two orders of reindexing and applying
structure maps. A swap proof of `[A,A].Perm [A,A]` still gives the identity
`idxBij`: a proof written with `Perm.swap` does not swap the equal-valued
occurrences. `equal_swap_actions` checks forward and inverse behavior with
different coefficients in those coordinates.

## Executability and proof boundaries

These constructors and the ordinary clients above compile as data-producing
`def`s. Their runtime operations are finite arithmetic, field operations,
coordinatewise maps and the existing nth-occurrence lookup. There is no new
barcode extraction algorithm or complexity claim.

Execution and proof axioms are separate properties. The permutation isomorphism's
proof closure still includes `Classical.choice`, even though its forward and
inverse data execute; the interval rank theorem also retains classical
dependencies. A successful allowed-axiom audit establishes soundness under the
library's axiom policy, not that every proof is constructive.

The arbitrary-multiset `barcodeModule` retains its `Multiset.toList` convention.
`Module.finrank`, `rankBarcode`, `rankBarcodeIso` and general decomposition are
theory APIs here. The private range-product preimage constructions in
`FiniteBarcode.lean` retain their separate classical choices. None is turned into
an executable extraction procedure by these interval/list constructors.

The statements describe the existing Lean interval and list-realization
semantics. No primary-paper full-text comparison is asserted.
