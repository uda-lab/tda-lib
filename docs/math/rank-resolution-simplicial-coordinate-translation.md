# Exact distance for independent coordinate translates of the simplicial filtration

Let \(C\) be the boundary of the tetrahedron with the actual face grading \(g\) from the [simplicial realization of the degree-two rank witness](rank-resolution-simplicial-realization.md). For a signed vector \(v : \mathrm{Fin}\,2 \to \mathbb R\), set
\[
g_v(\sigma,i)=g(\sigma,i)+v_i,
\qquad H_v=\operatorname{finiteSimplicialHomology}(k,g_v,1).
\]
Here \(H_v\) denotes the full degree-one persistence module (PH₁ module) of this sublevel filtration: its fiber at \(p\in\mathbb R^2\) is \(H_1(C_{g_v\le p};k)\), and for \(p\le q\) its structure map is induced on homology by the inclusion \(C_{g_v\le p}\hookrightarrow C_{g_v\le q}\). The distance below compares these modules together with their structure maps, not isolated \(H_1\) groups or dimension tables. The coefficient field \(k\) is arbitrary, including characteristic two. A positive coordinate of \(v\) delays the births of faces in that coordinate; a negative coordinate advances them. Each face is still graded on the same original two-coordinate parameter space.

For each real parameter \(p\), the translated sublevel is exactly the original sublevel at the coordinate pullback
\[
\rho_v(p)_i=p_i-v_i.
\]
This gives a natural isomorphism from the actual \(H_v\) to the original actual homology reindexed by \(\rho_v\), and then to the reindexed real-coordinate realization. Naturality identifies every actual structure map with the corresponding original map under this pullback. Finite presentation follows directly from the actual finite simplicial input.

An interleaving radius \(\varepsilon\in\mathbb R_{\ge0}\) still shifts evaluation diagonally, \(p\mapsto p+\varepsilon(1,1)\); the two composites equal the actual structure maps \(p\to p+2\varepsilon(1,1)\), one in each module. The coordinate interleaving distance is the \(\mathbb R_{\ge0\infty}\)-valued infimum over finite radii admitting an actual interleaving. With this convention, for all signed \(u,v:\mathrm{Fin}\,2\to\mathbb R\), with no coordinatewise comparison assumption,
\[
d_I(H_u,H_v)=\operatorname{ENNReal.ofReal}\!\left(\min\!\left(\max\{|v_0-u_0|,|v_1-u_1|\},\tfrac12\right)\right).
\]
The largest coordinate displacement governs the distance until the one-half lifetime bound is reached. Beyond it the distance stays at one half, including for arbitrarily large or oppositely signed delays.

The upper bound has two actual witnesses. If the maximum magnitude \(D=\max_i|v_i-u_i|\) is at most one half, finite simplicial grade perturbation supplies the radius-\(D\) interleaving by the shifted sublevel-inclusion maps. Otherwise, the radius-one-half witness has both natural transformations zero: each translated module's actual one-unit diagonal structure map vanishes. The optimal witness chooses the magnitude construction for \(D\le\tfrac12\) and the zero-map construction otherwise.

For the lower bound, coordinate \(i=0\) uses the arm born at \((0,1)+v\), and coordinate \(i=1\) uses the arm born at \((1,0)+v\). The selected coordinate of that birth is \(v_i\). Its actual structure-map transition is nonzero for every displacement \(0\le r<1\), while the actual fiber is zero below \(v_i\). If \(v_i-u_i>0\), a proposed radius smaller than that coordinate gap makes the forward interleaving component land in a zero target fiber. The interleaving equation would then force a nonzero source transition across \(2\varepsilon<1\) to vanish. For a negative gap the same argument applies to the symmetric interleaving. Choosing a coordinate realizing the maximum proves the lower bound for mixed-sign, tied, and incomparable vectors. At \(r=1\), the actual transition vanishes.

The Lean import path is TDA.Persistence.RankResolutionDegreeTwoSimplicialCoordinateTranslation; its declarations are in namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial. The declarations coordinateTranslatedGrading, coordinateTranslatedHomology, and coordinateTranslationPullback define the actual family and its reindexing; coordinateTranslatedHomologyMagnitudeInterleaving and coordinateTranslatedHomologyHalfInterleaving expose the witnesses; coordinateTranslatedHomology_no_interleaving states the coordinate obstruction; and coordinateInterleavingDistance_coordinateTranslatedHomology proves the formula. coordinateTranslatedGrading_const and coordinateTranslatedHomology_const identify the diagonal restriction with the existing scalar API and its distance theorem. Ordinary-import consumers over \(\mathbb Q\) and ZMod 2 are in module TDA.Persistence.RankResolutionDegreeTwoSimplicialCoordinateTranslationExamples.

This exact formula concerns only this actual degree-one homology family. It does not establish a global metric formula for arbitrary modules, a claim for every persistence module or dimension, ordinary projective dimension, or a barcode representation. The prerequisite face-level construction is documented in the [simplicial realization note](rank-resolution-simplicial-realization.md), alongside the [scalar translation note](rank-resolution-simplicial-translation.md) and [finite simplicial stability note](finite-simplicial-stability.md).
