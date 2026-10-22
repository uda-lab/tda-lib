# Compatible orders from a finite face type

Let `K` be a preabstract simplicial complex on any vertex type `V`, and let `f : FilterFunction K α` for a linearly ordered grade type `α`. Given a `Fintype (TotalFace K)`, `exists_compatibleOrder f` proves that some enumeration of the faces places every proper face before its coface and has nondecreasing grades. Neither the ambient vertices nor the grades need to be finite or inhabited. In particular, the bottom complex has the empty enumeration even with an `Empty` grade type.

Choose a finite rank equivalence `q : TotalFace K ≃ Fin (card (TotalFace K))` in the proof. Order faces locally by the nested lexicographic key `(f.value s, s.val.card, q s)`. The rank makes the key injective, and `Fintype.orderIsoFinOfCardEq` enumerates its finite linear order. Filter monotonicity makes a proper face's grade no greater than its coface's grade; if the grades tie, strict inclusion makes its cardinality smaller. Thus the key, and hence its enumeration index, increases strictly for proper faces. Projection of the lexicographic key gives grade monotonicity.

The rank is an arbitrary proof-local choice. This theorem asserts existence; it supplies neither a canonical order nor an executable enumeration. For a finite presentation with ordered `Fin n` vertices, `CompatibleOrder.ofLex` remains the executable colex-based constructor. The supplied face `Fintype` is retained, and no global order on faces or vertices is installed.

For any supplied equivalence `e : Fin (card (TotalFace K)) ≃ TotalFace K`, `CompatibleOrder.monotone_enum_iff_reflects_lt f e` says that grades along `e` are monotone exactly when strict grade comparisons reflect strict index comparisons. Equal grades impose no strict index constraint. This characterization concerns grades only: an enumeration can satisfy it while putting a coface before a face.

`CompatibleOrderExistenceExamples.lean` checks empty complexes over `Fin 0` and `ℕ`, an edge with three faces in infinite ambient `ℕ`, tied and nonconstant grades, both directions of the comparison law, a decreasing-grade enumeration, and a grade-monotone enumeration that violates face precedence. The existence witnesses are used only through their compatibility fields.

The proofs use the existing `CompatibleOrder` and `FilterFunction` interfaces and pinned Mathlib finite equivalences, finite-order sorting, lexicographic order, and strict finite-set cardinality. The theorem does not address transfer, prefixes, topology, homology, or the outstanding closed-compatibility assertion in parent Issue #42.
