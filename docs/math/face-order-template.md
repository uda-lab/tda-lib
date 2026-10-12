# Fixed face-order persistence templates

Fix a compatible enumeration of the actual nonempty faces of a finite simplicial complex. Its first `t` faces form a subcomplex for `0 ≤ t ≤ m`. Degree-`p` homology and the actual maps induced by inclusions give an `(m + 1)`-stage persistence module. Its canonical rank barcode depends on the enumeration, coefficient field and degree, with no filter values in this construction.

The stage-zero complex is empty and has zero homology. Thus every barcode occurrence has birth `b > 0`. A finite interval `[b,d)` with `d ≤ m` becomes the face-index pair `(b-1,d-1)`; a terminal interval with `d = m+1` becomes the essential birth index `b-1`. These are multisets: repeated occurrences remain repeated, and no assertion that a face index appears at most once is made here.

For any filter monotone along the fixed enumeration, evaluate each pair at those two face values. A finite pair with equal values contributes no diagram point. An essential index contributes a point with death `∞`. The evaluation equals the actual sublevel homology diagram. The proof identifies each attained sublevel with its face-count prefix **and compares the induced inclusion maps**, then applies finite rank-barcode sampling. This also covers ties and the empty face set. Any compatible witnesses with the same enumeration have equal index multisets, even if their reference filters differ. A different compatible enumeration can change the index multisets while giving the same evaluated diagram.

## Endpoint checks

- Empty complex: `m = 0`; both multisets and the diagram are empty. No face index is chosen.
- One vertex: its degree-zero template has one essential index `0`, giving `(value(vertex), ∞)`. The concrete Lean fixture derives this from actual singleton homology.
- Two vertices `a,b` followed by edge `ab`: in degree zero, an order with `a` first has the finite pair `(1,2)` and essential index `0`. If the edge enters at a later value, that pair evaluates to `(value(b), value(ab))`; if all values tie, it vanishes. The Lean edge fixture checks the actual diagram `(2,∞) + (5,9)` and the all-tied evaluation's absence of finite points.
- Signed triangle order `[a,b,c,ab,bc,ac,abc]`: in degree one the cycle closes on face index `5` and dies on face index `6`, so its interval contributes `(5,6)`. Equal values at `ac` and `abc` remove that evaluated point. Without `abc`, the degree-one endpoint at index `5` is essential. The general theorem applies to these actual prefix homology maps; this note records the endpoint calculation, not a separate Lean computation of the triangle's homology ranks.
- Permuting vertices within a tied block can change the index assignment of finite intervals. Equality of evaluated diagrams follows from both evaluations being the same actual sublevel diagram.

This construction uses rank barcodes, not a barcode-module decomposition. It does not establish the each-face-at-most-once property reserved in #45.
