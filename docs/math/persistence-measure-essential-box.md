# Interleavings and essential birth strips

Essential intervals contribute no mass to finite-death rectangles. Their
stability therefore needs a comparison on the death-at-infinity boundary.
For q-tame modules M and N,
`RealInterleaving.essentialMeasureValue_box_le_of_qTame` proves that comparison
from an actual ε-interleaving:

\[
 E_M(a,b)\leq E_N(a-\varepsilon,b+\varepsilon).
\]

Here a ≤ b, and E is the essential strip measure constructed from eventual
finite-target image-quotient dimensions in
[persistence rectangle measures](persistence-rectangle-measure.md). The theorem
also gives an inequality between the defined natural-valued `Module.finrank` minima assuming
only N is q-tame. For a source M that is not q-tame, its minimum need not equal
its eventual tail value, so that more general numerical statement is not an
assertion about its genuine essential boundary count. The theorem assumes
neither a vanishing lower tail nor an interval decomposition. Reversing the
interleaving gives the opposite boundary comparison for q-tame M and N.

The finite-target theorem `persistenceTailMeasureValue_box_le` first proves

\[
 \dim\frac{\operatorname{im}(M_b\to M_c)}
                 {\operatorname{im}(M_a\to M_c)}
 \leq
 \dim\frac{\operatorname{im}(N_{b+\varepsilon}\to N_{c-\varepsilon})}
                 {\operatorname{im}(N_{a-\varepsilon}\to N_{c-\varepsilon})}.
\]

It requires b+ε ≤ c−ε and only a finite-dimensional expanded crossing image.
The interleaving factors the source crossing map through that image. Restricting
the reverse interleaving map to the preimage of the source crossing image gives
a surjection. Naturality sends the earlier target image into the earlier source
image, so the surjection descends to a quotient of a subspace of the expanded
tail quotient. Its dimension is bounded by the expanded quotient dimension.

For the essential bound, choose a finite target attaining the minimum defining
E_N. Q-tameness makes its crossing image finite. The finite-target inequality,
together with E_M being a lower bound for every source tail count, proves the
result. No diagram representation is needed in this argument.

The fixture `displaced_essential_interval_box_nonzero` uses the actual
1/4-interleaving of [0,∞) and [1/4,∞). It transports a source essential count
of one into the expanded birth strip [−5/4,1/4], including the shifted birth
on its upper edge.

The source is Chazal–de Silva–Glisse–Oudot,
[*The structure and stability of persistence modules*, arXiv:1207.3674v3](https://arxiv.org/pdf/1207.3674v3),
Proposition 4.23 in §4.6, with measures at infinity defined by minima in §2.6.
For q-tame source and target, the implementation proves the finite-birth,
positive-death boundary case directly through module quotients. It supplies a
box comparison; a matching of
essential occurrences and full algebraic stability require further arguments.
