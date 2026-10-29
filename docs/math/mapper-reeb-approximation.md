# Categorical Mapper and Reeb approximation

Let `G` be a finite simple graph, with arbitrary real vertex heights `h`. Its realization
carries the affine height `f = plHeight G h`. Horizontal edges, repeated vertex heights and
disconnected inputs are allowed. Let `U_i = (a_i,b_i)` be a finite family of bounded open
intervals covering the values attained by `f`. Intervals outside that range may be discarded;
intervals meeting only an edge interior are retained.

For every nonempty simplex `σ` of the cover nerve, categorical Mapper stores the path
components of `f⁻¹(U_σ)`, where `U_σ` is the full intersection of the intervals indexed by `σ`.
Its maps are induced by the inclusions belonging to faces. `categoricalMapperData` formalizes
this diagram. `coverIntersectionInterval` presents each intersection as an open
interval, and `finite_graphPL_categoricalMapperData` proves that every graph-PL component
value of this diagram is finite. It preserves distinct components of an intersection, even when ordinary
Mapper records only a single edge over the same pair of component vertices.

For a test interval `I`, select precisely the simplices for which `U_σ ∩ I` is nonempty.
The functor usually denoted `P_K C_K` takes their component diagram's colimit. The chosen
colimit model `categoricalMapperAssembly` is the path-component set of

\[
f^{-1}\left(\bigcup_{U_i\cap I\ne\varnothing}U_i\right).
\]

`categoricalMapperIsColimit` proves its universal property, and
`categoricalMapperCocone_map` identifies its interval maps with the maps induced by inclusion
of selected simplices.

The assembly is an interval cosheaf. For the gluing proof, a fixed cover interval meets an
interval cover in a connected chain; local compatible functions therefore agree on each
original cover component. The endpoints of the bounded cover form a finite critical-value
witness. Finiteness of the graph-PL pullback components then gives a constructible cosheaf.
These facts supply the hypotheses of the existing finite reconstruction equivalence, whose
inverse `D` yields the real graph `graphPLMapperReconstruction`.

## Error and convergence

Define the retained resolution by

\[
\operatorname{res}_f(U)=\max\bigl(\{0\}\cup
 \{b_i-a_i\mid f^{-1}(U_i)\ne\varnothing\}\bigr).
\]

`clippedCoverResolution` separately records the maximum diameter of `U_i ∩ range(f)`.
Each retained interval contributes its full ambient width to the bound above. For constant input, clipping an
interval to the attained singleton would give zero width although the assembled cosheaf has
values away from that height. The clipped-resolution fixture proves zero, while the
constant-input fixture proves strictly positive geometric
error by ruling out a small positive shift through an empty target fiber.
`coverComponentsRetainedIso` proves that discarding exactly the
empty pullbacks preserves the assembly.

`geometricInterleavingDistance_mapperReeb_le_retained` proves

\[
d_{\mathrm{geo}}\bigl(DP_KC_K(f),\mathcal R(f)\bigr)
 \le \operatorname{res}_f(U).
\]

Here `𝓡(f)` is `GraphPL.graphPLReebGraph`, the Reeb quotient equipped with its finite
real-graph property. The proof constructs both natural comparison maps on input
points, verifies their interleaving composites, and transports the result through the
reconstruction and quotient component isomorphisms. The version
`geometricInterleavingDistance_mapperReeb_le` uses all cover members' widths.

`tendsto_geometricInterleavingDistance_mapperReeb` gives convergence to zero when cover
resolutions tend to zero; the `_retained` version needs only retained resolutions to vanish. The finite index type may vary along the family.
`exists_graphPLMapperCover_resolution_le` constructs a finite uniform cover for any
positive prescribed resolution; finite vertex heights provide range bounds.
`exists_graphPLMapperReconstruction_error_le` exports the resulting geometric estimate.
The nonconstant single-edge example exposes a family with vanishing full resolutions, its
geometric error bounds and convergence.

## Two inputs

Let `h, g : V → ℝ` be vertex heights on one finite simple graph `G`, and let `(a, b)` and
`(a', b')` be finite bounded-interval covers of the attained ranges of `plHeight G h` and
`plHeight G g`, with resolutions `res` and `res'`. Write `M_h`, `M_g` for the two
reconstructions and `𝓡(h)`, `𝓡(g)` for the Reeb quotients. At the cosheaf level, for
continuous `f, g : C(X, ℝ)` with `|f x - g x| ≤ ε` and covers whose members have diameters at
most `r` and `r'`, the triangle inequality for the interleaving distance and the one-input bound
give
\[
d(C_{U}f,\ C_{U'}g) \le r + \varepsilon + r',
\]
and `r + ‖f - g‖∞ + r'` with the uniform extended distance
(`interleavingDistance_coverComponents_le_add`, `_edist`).

For graph-PL input, the geometric triangle inequality with
`geometricInterleavingDistance_mapperReeb_le` and the vertex-height bound
`geometricInterleavingDistance_graphPLReebGraph_le_edist` give
\[
d_{\mathrm{geo}}(M_h, M_g) \le \operatorname{res} + \operatorname{edist}(h, g)
 + \operatorname{res}'
\]
(`geometricInterleavingDistance_mapperReeb_le_add_edist`), with forms for a vertex budget `ε`,
for retained resolutions, and for one cover (`2 res + edist h g`). The same triangle inequality
in the other direction gives the two-sided comparison
`d_geo(𝓡(h), 𝓡(g)) ≤ d_geo(M_h, M_g) + res + res'` and
`d_geo(M_h, M_g) ≤ d_geo(𝓡(h), 𝓡(g)) + res + res'`
(`geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add` and
`geometricInterleavingDistance_mapperReeb_le_graphPLReebGraph_add`). With the extremal
lower bounds of the Reeb distance, for nonempty `V`,
`|max h - max g| ≤ d_geo(M_h, M_g) + res + res'`, and the same for `min`.

Along families of covers (`κ t`, `a t`, `b t`) and (`κ' t`, `a' t`, `b' t`) that cover the
attained ranges at every `t` and have both resolutions tending to `0`,
`tendsto_geometricInterleavingDistance_mapperReeb_pair` shows that `d_geo(M_h^t, M_g^t)` tends to
`d_geo(𝓡(h), 𝓡(g))`, by squeezing between `d_geo(𝓡) - (res_t + res'_t)` and
`d_geo(𝓡) + res_t + res'_t` in `ℝ≥0∞`; the retained form needs only retained resolutions to
vanish. `exists_graphPLMapperReconstruction_pair_le` gives, for every `r > 0`, finite covers with
`d_geo(M_h, M_g) ≤ edist h g + 2 r`.

Coverage of each height's attained range is required by the ingredients: the empty cover of a
nonempty graph reconstructs the empty graph, which is at distance `⊤` from the Reeb quotient
although its resolution is `0`. None of the bounds is claimed to be sharp. With equal heights
and one cover the distance is `0` while the bound is `2 res`. Reconstructions
over different graphs or edge sets are not compared. The two-input bounds are compositions of the
one-input approximation with the triangle inequality and are attributed to neither source paper;
the perturbation step is de Silva–Munch–Patel, Theorem 4.6(i).

For vertical translation the distance is exact at every finite cover. Translating the height to
`f + c` and every member to `U i + c` gives an assembled precosheaf naturally isomorphic to
`translatePre c (coverComponents f U)` (`coverComponentsTranslateIso`), so the two assemblies are
at distance at most `|c|`. For a finite bounded-interval cover `(a, b)` with an active member,
that is a member with nonempty inverse image, the distance is exactly `|c|`
(`interleavingDistance_coverComponents_add_const`): for `c > 0` and `ε < c`, the interval
`(a i₀, a i₀ + (c - ε)/2)` at the least left endpoint `a i₀` of an active member has a nonempty
assembled value for `f`, while every original member meeting `translate c (thicken ε I)` has
left endpoint strictly below `a i₀` and is therefore inactive. Hence, for graph-PL input,
\[
d_{\mathrm{geo}}\bigl(M_h(a, b),\ M_{h + c}(a + c, b + c)\bigr) = |c|
\]
(`geometricInterleavingDistance_graphPLMapperReconstruction_add_const`, and `_of_covers` when the
cover covers the attained range of `h` on a nonempty vertex type). No coverage, resolution bound
or boundedness is assumed. The active member cannot be dropped: two graph objects with empty
total spaces are at distance `0` (`RGraph.geometricInterleavingDistance_eq_zero_of_isEmpty`), so
over empty covers of a nonempty graph the reconstructions of `h` and `h + 1` are at distance `0`
while the Reeb quotients are at distance `1` and both resolutions are `0`, so the comparison
`d_geo(𝓡(h), 𝓡(g)) ≤ d_geo(M_h, M_g) + res + res'` also needs coverage. Translation of graph
objects, `RGraph.translateRGraph c`, preserves the geometric interleaving distance and moves every
graph object with nonempty total space by exactly `|c|` (see
[reeb-rgraph-translation.md](reeb-rgraph-translation.md)); the reconstruction of `h + c` over the
translated cover is not identified with the translate of the reconstruction of `h`. Translating
the cover by `c` preserves its resolution (`coverResolution_add_const`). Translating the height
without the cover, or the cover without the height, is covered only by the perturbation bounds
above.

## Scope and computation

The interval-indexed categorical bound follows the objects and conclusion of Munch–Wang,
*Convergence between Categorical Representations of Reeb Space and Mapper*, arXiv v2,
Theorem 4.1, Lemma 7.1 and Corollary 8.1. The formalization begins with finite graph-PL input
in universe zero and uses the library's existing quotient and finite reconstruction.
Its interval arguments use the one-dimensional intersection property of real intervals.
No higher-dimensional Reeb-space theorem or automatic identification with the ordinary
Mapper simple graph is asserted.

The component functors, colimits and reconstructed graph are abstract mathematical objects.
Classical finite-witness selection is permitted. This result provides neither an executable
component enumeration procedure nor a complexity bound. An executable algorithm would
require a separate specification and a correctness bridge to these objects.

The examples cover a horizontal edge, repeated heights on a disconnected graph, a retained
edge-interior hit with no retained vertex, an empty pullback, the constant-input width
boundary, and the four-cycle's two categorical intersection components over one ordinary
Mapper edge. A finer three-member cover has a reconstructed graph with two components
over its central test interval, established through the reconstruction isomorphism. A coarse
assembly may merge those components; the categorical input count alone does not prove that
the reconstructed graph preserves the loop. See the [source register](references.md#MW16-v2) for source and rights scope.
