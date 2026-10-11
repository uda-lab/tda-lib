# Ordered-barcode representation laws

The [finite diagram convention](finite-diagram-ordered-q.md) stores a finite multiset of
`α × WithTop α` points, excluding only finite diagonal points. The coordinate type
`α` has an arbitrary `LinearOrder`; it need not be inhabited. In particular, a
finite pair with death before birth remains a diagram point. Each occurrence of
a repeated pair or essential birth remains a separate multiset occurrence.

`TDA.Persistence.orderedQ_append` states that appending both finite and essential
coordinate tuples adds their point multisets. This is a multiset law, so
collisions across the boundary add multiplicities. It does not introduce an
addition operation on `Diagram`.

`orderedQ_eq_iff` compares diagrams with possibly different finite and essential
dimensions. It compares finite input multisets after deleting precisely pairs
`(b,b)`, and it compares essential birth multisets separately. This is more
general than a fixed-dimension permutation criterion: distinct diagonal tuples
can both represent the empty diagram. The essential comparison still preserves
all occurrences, so it cannot identify different essential multiplicities.

`orderedQ_surjective` gives some finite dimensions and coordinate tuples for
every diagram. The proof separates finite-death and top-death points with
`Multiset.filterMap`, reconstructs the original multiset from those two parts,
and enumerates each part with `Multiset.toList`. This enumeration uses classical
choice within an existential proof. It supplies neither a canonical ordering
nor a computable persistence algorithm, and requires no `Nonempty α` or
`Inhabited α` instance. The all-empty case includes an empty coordinate type.

`orderedQ_zeroLength` deletes a diagonal finite coordinate at any `Fin (m+1)`
position. The private `ofFn_removeNth` enumeration identity expresses the old
finite multiset as the surviving coordinates plus that one occurrence.
Filtering removes the diagonal singleton, while leaving every other finite
and essential occurrence unchanged. The theorem covers first, interior, last,
and singleton positions.

The product fixtures check cross-boundary collisions and reversed points,
cross-dimension equality, three distinct negative equality cases, explicit
non-orbit tuple inequality, an independently constructed mixed diagram with a
concrete witness, first/interior/last deletion, finite-only and essential-only
representations, and differing all-diagonal inputs yielding empty diagrams.
The append diagonal fixture quantifies over every possible diagonal value.
The public laws are pinned in the live axiom audit; private helpers and
fixtures are included in the completed-module declaration inventory.

These laws use the source convention already reviewed for the core diagram
map and the governing [Issue #151](https://github.com/uda-lab/tda-lib/issues/151)
contract. They are elementary consequences of that representation; this unit
does not claim a fresh primary-paper comparison. No law here identifies a
terminal finite observation with infinite death. Value-labelled persistence,
`ofIndexBars`, and the eventual-sublevel argument remain separate work.
