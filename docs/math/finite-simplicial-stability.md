# Stability of finite graded simplicial homology

Let $C$ be a finite simplicial complex whose faces are nonempty finite sets of
vertices. Assign a vector $g(s)\in\mathbb R^n$ to each face, with

$$
s\subseteq t \quad\Longrightarrow\quad g(s)\le g(t)
$$

in the coordinatewise order. At a parameter $a\in\mathbb R^n$, the sublevel

$$
C_g(a)=\{s\in C:g(s)\le a\}
$$

is a subcomplex. Its homology in degree $q\in\mathbb N$, over an arbitrary
field $k$, forms a persistence module $M_g(a)=H_q(C_g(a);k)$; the structure
maps are induced by inclusions of subcomplexes. These are ordinary simplicial
homology groups, so the empty complex has zero homology in every degree.

`Filtration.FiniteGraded C n` stores exactly the face grades and their
monotonicity, with `C : Simplicial.FiniteComplex m` on vertices `Fin m`.
`finiteSimplicialHomology k g q` constructs this module through the existing
`simplicialHomologyPModule`.

## Finite presentation from the input

The module $M_g$ satisfies the original `GradedFree.FinitelyPresented`
predicate. A finite presentation consists of finitely many graded generators
and relations whose cokernel is naturally isomorphic to $M_g$.
`finiteSimplicialHomology_finitelyPresented` derives this data from $C,g$.

For each coordinate, take the finite set of values occurring among the face
grades, include zero in each coordinate set, and let $G$ be their product
grid. Whenever $a$ has a grid point below it, the coordinatewise greatest
such point $\lfloor a\rfloor_G$ satisfies

$$
g(s)\le a \quad\Longleftrightarrow\quad
g(s)\le\lfloor a\rfloor_G.
$$

Thus the inclusion from the floor sublevel to the original sublevel is an
equality of complexes. When no lower grid point exists, no face can occur:
the grade of any occurring face would itself be a lower grid point.

Restrict $M_g$ to $G$ and take its left Kan extension along the grid
inclusion. The canonical comparison to $M_g$ is an isomorphism at every
parameter: at a floor it is the inclusion-induced homology isomorphism, and
outside the lower-grid region both fibres are zero. Since the comparison is
a natural transformation, it preserves all structure maps. The restricted
module has finite-dimensional fibres on a finite poset. The existing
finite-poset presentation theorem and finite-grid Kan extension theorem
therefore give the required graded-free presentation of $M_g$.

This construction permits repeated grades and empty complexes. In zero
coordinates the grid product is a singleton and every sublevel is $C$;
the same argument gives finite presentation of the resulting constant module.

## Perturbing the grades

For two monotone grade assignments $g,h$ on the same complex, let

$$
\delta=\max_{s\in C,\,i\in\{1,\ldots,n\}}
  |g(s)_i-h(s)_i|,
$$

with value zero when the indexing set is empty. The declaration
`FiniteGraded.supGradeError` uses this finite maximum. More generally, any
nonnegative upper bound $\varepsilon$ for these coordinate errors gives

$$
C_g(a)\subseteq C_h(a+\varepsilon\mathbf1),\qquad
C_h(a)\subseteq C_g(a+\varepsilon\mathbf1).
$$

Functoriality of inclusion-induced homology makes the two composites the
structure maps shifted by $2\varepsilon$. This constructs an actual
coordinate interleaving, `finiteSimplicialHomology_interleaving`, and proves

$$
d_I(M_g,M_h)\le\delta.
$$

For $n\ge1$, the derived finite presentations define the canonical signed
hook barcodes $B_g,B_h$. Applying the existing
[signed hook stability theorem](../api.md#signed-hook-bottleneck-stability)
gives

$$
d_{\mathrm{signed}}(B_g,B_h)\le (2n-1)^2\delta.
$$

`finiteSimplicial_signedHookBottleneckDissimilarity_le` accepts any
nonnegative error bound, without a caller-supplied presentation, resolution,
or interleaving. In one coordinate the constant is one. The reused signed
bound follows [Botnan–Oppermann–Oudot–Scoccola, Theorem 6.1](https://arxiv.org/html/2208.00300v3).
Its signed cross-sum comparison is a dissimilarity; it has no triangle
inequality in general, as explained in their Remark 6.3 and the library's
[two-coordinate example](../api.md#two-coordinate-signed-hook-triangle-failure).

The constructions are mathematical APIs and may be noncomputable. They do
not provide an executable multiparameter barcode algorithm.
