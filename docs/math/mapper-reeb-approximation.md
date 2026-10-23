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
