# Exact distance for signed translates of a positively scaled simplicial module

Let $C$ be the tetrahedron boundary with the actual face grading $g$ from the
[simplicial realization note](rank-resolution-simplicial-realization.md). Fix
positive coordinate scales $s : \mathrm{Fin}(2) \to \mathbb R$, with
$s_i>0$. For a signed delay $t\in\mathbb R$, grade each face by
$$
g_{s,t}(\sigma,i)=s_i g(\sigma,i)+t,
\qquad
M_{s,t}=\operatorname{finiteSimplicialHomology}(k,g_{s,t},1).
$$
Here $M_{s,t}$ is the entire PH₁ persistence module of the actual sublevel
filtration. Its fiber at $p\in\mathbb R^2$ is
$H_1(C_{g_{s,t}\le p};k)$, and its maps for $p\le q$ are induced by the
actual inclusions of sublevel complexes. Thus the distance below compares
modules with their structure maps, not isolated H₁ groups or Betti tables.
The field $k$ and its universe are arbitrary, including characteristic two.

At parameter $p$, the actual $g_{s,t}$ sublevel is the $g_s$ sublevel at
$p-t(1,1)$, and hence the original unscaled $g$ sublevel at coordinates
$(p_i-t)/s_i$. These identifications give the natural reindexing isomorphism
and commute with every inclusion-induced map. Finite presentation follows
from the actual finite simplicial input. With $s=(1,1)$ this is the existing
uniform signed translation family; with $t=0$ it is the positively scaled
family.

An interleaving radius $\varepsilon\in\mathbb R_{\ge0}$ shifts evaluation
diagonally, $p\mapsto p+\varepsilon(1,1)$. Each of its two composite equations
is the actual structure map from $p$ to $p+2\varepsilon(1,1)$ in the
corresponding module. The coordinate interleaving distance takes values in
$\mathbb R_{\ge0\infty}$ and is the infimum over finite radii admitting an
actual interleaving.

Write $a=s_0$, $b=s_1$ and define the two arm lifetimes and their maximum by
$$
\lambda_A=\min(2a,b),\qquad
\lambda_B=\min(a,2b),\qquad
T=\max(\lambda_A,\lambda_B).
$$
For signed delays $t,u$, the exact distance is
$$
d_I(M_{s,t},M_{s,u})
 =\operatorname{ENNReal.ofReal}\!\left(\min\left(|t-u|,\frac T2\right)\right).
$$

The two actual arm births are $(0,b)+t(1,1)$ and $(a,0)+t(1,1)$.
Their diagonal structure maps at displacement $r\ge0$ are nonzero exactly
when $r<\lambda_A$ and $r<\lambda_B$, respectively; each map is zero at and
after its endpoint, and each birth fiber is nonzero. Thus every structure map
at the diagonal displacement $T$ is zero. The interleaving with zero cross
transformations at radius $T/2$ has both composite equations given by those
actual vanishing maps. Together with the magnitude witness at radius $|t-u|$,
the distance formula chooses the smaller of these two radii. At radius
$|t-u|$, the actual grade-error interleaving gives the magnitude bound. For the lower bound, if
$\varepsilon<|t-u|$ and $\varepsilon<T/2$, choose an arm attaining $T$.
Its actual map at displacement $2\varepsilon$ is nonzero, whereas its
cross-map target fiber at the intervening grade is zero by the zero-fiber
criterion. The corresponding interleaving equation would force that actual
source transition to vanish. This proves the sharp lower bound without an
assumption on a caller-supplied witness or finite-presentation certificate.

For $s=(4,1)$ the B arm has lifetime $2$ and the A arm lifetime $1$; the
roles reverse for $s=(1,4)$. At delay gap $3/4$, the longer-arm composite at
displacement $3/2$ is still nonzero, and the pair has no $5/8$-interleaving:
the actual double transition survives although the cross-map target fiber in
the other translated module is zero. At gap $1$, each skew-scale pair also has
a common grade where both actual fibers are nonzero, so distance $1$ is not
explained by one module having vanished. At gap $2$, the distance saturates
at $1$. The concrete signed pair $(-1/2,1/4)$ and its reverse have gap $3/4$;
for the small scale $(1/4,1)$, pair gaps $1/8$ and $1/2$ give distances
$1/8$ and the saturated value $1/4$, respectively.

The Lean module is **TDA.Persistence.RankResolutionDegreeTwoSimplicialScaledTranslation**;
its declarations are in namespace
**TDA.Persistence.RankResolutionDegreeTwoSimplicial**. The definitions
**scaledTranslatedGrading** and **scaledTranslatedHomology** expose the actual
input and full PH₁ module. **scaledTranslatedHomologyReindexIso** and
**scaledTranslatedRealIso_structureMap** give the actual reindexing and map
naturality. The theorem
**scaledTranslatedHomology_structureMap_ne_zero_iff** characterizes actual
maps; the two arm survival criteria give their lifetimes. The magnitude and
lifetime witnesses are **scaledTranslatedHomologyMagnitudeInterleaving** and
**scaledTranslatedHomologyLifetimeInterleaving**; the exact distance theorem
is **coordinateInterleavingDistance_scaledTranslatedHomology**. Ordinary
clients, including explicit rational and characteristic-two map obstructions,
are in **TDA.Persistence.RankResolutionDegreeTwoSimplicialScaledTranslationExamples**.

This result concerns pairs with the same fixed strictly positive coordinate
scale and differing uniform signed delays. It does not compare different
scales, nonpositive or collapsed scales, arbitrary module pairs, other
homological degrees, or ordinary projective dimensions. The geometric
construction and its claim boundaries are given in the
[simplicial realization note](rank-resolution-simplicial-realization.md).
