# Exact distance of a positively scaled simplicial module to zero

Let $C$ be the boundary of the tetrahedron with the actual face grading $g$ from the [simplicial realization of the degree-two rank witness](rank-resolution-simplicial-realization.md). For positive coordinate scales $s : \mathrm{Fin}(2) \to \mathbb R$, with $s_i>0$, give each face the grade
$$
g_s(\sigma,i)=s_i g(\sigma,i), \qquad
M_s=\operatorname{finiteSimplicialHomology}(k,g_s,1).
$$
Here $M_s$ is the entire degree-one persistence module, or PH₁ module, of the sublevel filtration. Its fiber at $p\in\mathbb R^2$ is $H_1(C_{g_s\le p};k)$, and its structure map for $p\le q$ is induced by the inclusion of those sublevel complexes. The distance compares these modules together with their maps, not separate homology groups or Betti tables. The coefficient field $k$ is arbitrary, including characteristic two.

At every parameter $p$, the scaled sublevel is the original sublevel at
$$
\rho_s(p)_i=p_i/s_i.
$$
Thus the actual $M_s$ is naturally isomorphic to the original actual PH₁ module reindexed by coordinatewise division; the realization isomorphism commutes with every inclusion-induced structure map. Finite presentation follows from the actual finite simplicial input. Unit scaling recovers the literal unmodified grading and module.

An interleaving radius $\varepsilon\in\mathbb R_{\ge0}$ shifts evaluation diagonally, $p\mapsto p+\varepsilon(1,1)$. Its two composites are the actual structure maps from $p$ to $p+2\varepsilon(1,1)$, one in each module. The coordinate interleaving distance takes values in $\mathbb R_{\ge0\infty}$ and is the infimum over finite radii admitting an actual interleaving.

Write $a=s_0$, $b=s_1$, and set
$$
\lambda_A=\min(2a,b),\qquad
\lambda_B=\min(a,2b),\qquad
T=\max(\lambda_A,\lambda_B).
$$
Then the exact distance of this actual module to the zero module is
$$
d_I(M_s,0)=\operatorname{ENNReal.ofReal}(T/2).
$$

The two actual arm births are $(0,b)$ and $(a,0)$. From them, the corresponding inclusion-induced structure map after diagonal displacement $r\ge0$ is nonzero exactly for $r<\lambda_A$ and $r<\lambda_B$, respectively; at and after each endpoint it is zero. Each birth fiber is nonzero. Consequently every actual diagonal structure map of $M_s$ at displacement $T$ is zero. The explicit optimal interleaving with zero uses the two zero natural transformations at radius $T/2$. Conversely, an arm attaining $T$ still has a nonzero actual structure map at displacement $2\varepsilon$ whenever $\varepsilon<T/2$; the interleaving equation with the zero module would force that map to vanish. This proves the lower bound, including when the two arm lifetimes tie.

Some ordinary-import examples are:

| $s=(a,b)$ | $(\lambda_A,\lambda_B)$ | $d_I(M_s,0)$ |
|---|---:|---:|
| $(1,1)$ | $(1,1)$ | $1/2$ |
| $(2,2)$ | $(2,2)$ | $1$ |
| $(4,1)$, $(1,4)$ | $(1,2)$, $(2,1)$ | $1$ |
| $(3/2,1)$ | $(1,3/2)$ | $3/4$ |
| $(2,1)$ | $(1,2)$ | $1$ |
| $(1/4,1)$ | $(1/2,1/4)$ | $1/4$ |

For scale $(4,1)$, the second arm's map at displacement $r=3/2$ is nonzero, while the pullback of its target has original-grid floor $(1,1)$; at $r=2$ that arm map is zero. The swapped scale checks the first arm. The module also has no $3/4$-interleaving with zero in either skew case. These examples use the actual maps and the reindexing, rather than only evaluating the final distance formula.

The Lean import is **TDA.Persistence.RankResolutionDegreeTwoSimplicialScaling**; declarations are in namespace **TDA.Persistence.RankResolutionDegreeTwoSimplicial**. **scaledGrading** and **scaledHomology** define the actual scaled input and PH₁ module; **scaledHomologyReindexIso**, **scaledRealIso**, and **scaledRealIso_structureMap** expose its reindexing and naturality. **scaledHomology_structureMap_ne_zero_iff** characterizes its actual maps, while **scaledHomology_armA_structureMap_ne_zero_iff**, **scaledHomology_armB_structureMap_ne_zero_iff**, and the corresponding **..._zero_of_ge** theorems state the arm lifetimes. The theorem **coordinateInterleavingDistance_scaledHomology_zero** proves the exact distance and **scaledHomologyZeroInterleaving** gives its optimal witness. Ordinary-import consumers, including the characteristic-two cases, are in **TDA.Persistence.RankResolutionDegreeTwoSimplicialScalingExamples**.

This result concerns only the actual PH₁ module of this two-coordinate tetrahedron-boundary filtration under strictly positive coordinate scaling, and its distance to zero. It is not a distance formula for arbitrary module pairs, nonpositive or collapsed scales, other dimensions, or ordinary projective dimension. The face-level construction and claim boundaries are given in the [simplicial realization note](rank-resolution-simplicial-realization.md).
