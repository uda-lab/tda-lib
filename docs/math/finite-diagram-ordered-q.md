# Finite diagrams and the ordered-barcode map

Consulted manifestations, attribution and rights: [LOT21-v4](references.md#LOT21-v4).

`TDA.Persistence.Diagram α` stores a finite multiset of pairs in
`α × WithTop α`, with the proof that no stored pair lies on the finite diagonal.
Here `α` has a linear order. Finite deaths may lie on either side of their
births. Only the death coordinate may be `⊤`; an essential point `(b, ⊤)` has
its ordinary finite multiplicity. The diagonal's infinite repetition is
implicit: it has no entries in `points`.

`orderedQ m n` takes `m` finite birth/death pairs and `n` essential births.
It removes precisely the finite pairs `(b, b)`, embeds every other finite pair
unchanged, and appends each essential point. This generalizes the set-level
ordered-barcode map of Leygonie–Oudot–Tillmann, Definition 3.1, from real
coordinates to an arbitrary linearly ordered type. Definition 2.8 and Remark
2.9 allow reversed finite pairs; the map is defined on the full ordered
barcode space. See the [publisher article](https://doi.org/10.1007/s10208-021-09522-y)
and [preprint, pp. 8 and 11](https://arxiv.org/pdf/1910.00960v4).

`Diagram.IsPositive` is a separate predicate. `orderedQ_isPositive_iff` says
that the image is positive exactly when every input finite pair has birth at
most death. Equality is allowed because those diagonal pairs disappear. The
permutation theorem changes only input enumeration; it does not characterize
all equal outputs. For example, `(0, 0)` and `(1, 1)` each map to the empty
diagram, and so does their two-entry list. The count theorems count input
positions, preserving repeated reversed pairs and repeated essential births.

This is a finite multiset construction, not a persistence computation. It
does not map a terminal finite observation to an essential point or identify
an arbitrary terminal death with infinity. Such a value-labelled result needs
an additional eventual-sublevel argument. The order-general definitions here
make no metric, norm, quotient-topology, or smoothness claim.
