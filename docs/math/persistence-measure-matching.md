# Local matching from finite box counts

A finite family of persistence points records occurrences, so equal point values
can appear more than once. If distinct source points are sufficiently separated,
two-sided box-count inequalities produce a matching of these occurrences with
controlled cost.

Write `x : I → ℝ × ℝ` and `y : J → ℝ × ℝ`, where `I` and `J` are finite,
and let ε ≥ 0. The function `finiteBoxCount x p r` counts occurrences in the
closed square of radius r about p, using the maximum metric. Assume that both
families satisfy

\[
 \#(x\cap B_r(p))\leq\#(y\cap B_{r+\varepsilon}(p)),
 \qquad
 \#(y\cap B_r(p))\leq\#(x\cap B_{r+\varepsilon}(p))
\]

whenever r > 0 and the expanded square lies strictly above the diagonal:
2(r+ε) < p₂−p₁. These are counting hypotheses, not assumptions that a matching
exists. The theorem `finiteBoxCount_box_le` proves the same inequalities for
r = 0 by finite-support stabilization of a shrinking positive radius.

`exists_matching_of_separated_box_bounds` assumes in addition:

- every source lifetime is greater than 4ε;
- distinct source point values have maximum distance greater than 2ε;
- every target point has birth at most death.

It constructs an `OccurrenceMatching I J PEmpty PEmpty` of cost at most ε,
matching every source occurrence. Repeated points need no separation from their
other copies. Target occurrences outside the matching have lifetime at most 2ε
and hence diagonal cost at most ε.

For a source value p, the radius-zero forward bound and radius-ε reverse bound
show that the target ε-square contains exactly the multiplicity of p. Source
separation makes these squares disjoint. Summing their cardinalities gives
Hall's inequality for every subset of source occurrences, from which mathlib's
finite Hall theorem supplies an injection. Equality of cluster cardinalities
forces that injection to cover every target cluster. Finally, the reverse
radius-zero bound puts every target of lifetime greater than 2ε in a source
cluster. This proves the claimed bound for unmatched targets.

The fixture `duplicated_shift_with_short_target` checks the box inequalities
directly for two copies of (0,10), two target copies of (1,11), and the extra
target (0,1), with ε = 1. It tests multiplicity, nonzero displacement, and an
additional short interval.

This is the finite local step of Chazal–de Silva–Glisse–Oudot,
[*The structure and stability of persistence modules*, arXiv:1207.3674v3](https://arxiv.org/pdf/1207.3674v3),
Theorem 4.25, Part 2(ii), §4.7. Example 4.26 shows why one pair of box
inequalities does not imply a general matching theorem without these local
hypotheses. The one-parameter family used in Theorem 4.25, the passage from
[module rectangle measures](persistence-measure-box.md) to these closed-square
occurrence counts, essential points, and the locally finite extension are not part of
this local theorem. The global result, `qTame_bottleneck_le_of_realInterleaving`, is proved by a
different route through `PersistenceMeasureWindowMatching` and finite saturation (see
[Rips metric stability](rips-metric-stability.md)); this local theorem by itself asserts
neither full algebraic stability nor a Rips bottleneck bound.
