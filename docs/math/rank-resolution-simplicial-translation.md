# Exact distance for a translated simplicial filtration

Let \(C\) be the boundary of the tetrahedron on four vertices, with the face grading \(g\) used in the [simplicial realization of the degree-two rank witness](rank-resolution-simplicial-realization.md). For a signed real parameter \(t\), define
\[
g_t(\sigma,i)=g(\sigma,i)+t,
\qquad
H_t=\operatorname{finiteSimplicialHomology}(k,g_t,1).
\]
Here \(H_t\) is the actual inclusion-induced degree-one homology module of the sublevel filtration. A positive \(t\) delays every face birth. At \(t=0\), the grading and module are the original ones. The coefficient field \(k\) is arbitrary, including characteristic two.

The sublevel at a real parameter \(p\in\mathbb R^2\) for \(g_t\) is exactly the original sublevel at \(p-t(1,1)\). This equality gives a natural isomorphism from \(H_t\) to the original actual homology reindexed by \(p\mapsto p-t(1,1)\). Composing with the existing real-coordinate realization isomorphism identifies this reindexing with the corresponding reindexing of the finite-grid model. The comparison is proved directly at all real parameters from the sublevel filtrations.

An interleaving radius \(\varepsilon\in\mathbb R_{\ge0}\) shifts evaluation from \(p\) to \(p+\varepsilon(1,1)\). Its two defining composites must equal the structure maps from \(p\) to \(p+2\varepsilon(1,1)\), one in each module. The coordinate interleaving distance is the \(\mathbb R_{\ge0\infty}\)-valued infimum over finite radii admitting such an interleaving.

For all \(s,t\in\mathbb R\), the existing extended coordinate interleaving distance, valued in \([0,\infty]\), is
\[
d_I(H_s,H_t)=\operatorname{ENNReal.ofReal}\!\left(\min\{|t-s|,\tfrac12\}\right).
\]
Thus the distance follows the translation gap up to one half and then stays at one half. In particular, the distance is zero for equal parameters, is one quarter for a quarter-unit gap, and is one half at the critical gap and for every larger gap. The formula is symmetric for negative and reversed parameters.

The upper bound has two explicit witnesses. When \(|t-s|\le\tfrac12\), the finite simplicial grade-perturbation construction gives the interleaving at radius \(|t-s|\); its components are the maps on homology induced by the actual shifted sublevel inclusions. Every actual \(H_t\) has zero structure maps across a one-unit diagonal displacement, while its first birth fiber is nonzero. Therefore the two zero natural transformations satisfy both interleaving equations at radius one half. This witness uses the vanishing of the one-unit transitions, not the vanishing of the module.

For the lower bound, the first cycle is born at \(b_s=(0,1)+s(1,1)\), and its actual structure map to \(b_s+r(1,1)\) is nonzero for every \(0\le r<1\). Suppose \(s\le t\) and an interleaving has radius \(\varepsilon<\min(t-s,\tfrac12)\). The target fiber at \(b_s+\varepsilon(1,1)\) is zero because its first coordinate is below every translated face birth. The forward component at \(b_s\) is therefore zero. But the first interleaving equation identifies the resulting zero composite with the nonzero source structure map across displacement \(2\varepsilon<1\), a contradiction. The universal lower-bound property of the distance infimum gives the stated bound; symmetry handles \(t<s\). This argument does not assume that the distance infimum is attained.

The exact theorem is `RankResolutionDegreeTwoSimplicial.coordinateInterleavingDistance_translatedHomology`. The actual upper witnesses are `translatedHomologyMagnitudeInterleaving`, `translatedHomologyHalfInterleaving`, and `translatedHomologyOptimalInterleaving`; the survival, transition-vanishing, and subcritical-obstruction results expose the lower-bound mechanism. Ordinary-import consumers check zero, quarter, half, saturated, negative, and reversed gaps over `\mathbb Q` and `ZMod 2`. The prerequisites and face-level construction are in the [simplicial realization note](rank-resolution-simplicial-realization.md) and [finite simplicial stability note](finite-simplicial-stability.md).

This result concerns only this actual degree-one homology family. It makes no claim about distances for all persistence modules, higher-dimensional sharpness, ordinary projective dimension of the module, or a barcode representation.

The independent two-coordinate translation family, with the same diagonal interleaving-radius convention, is documented in the [coordinate translation note](rank-resolution-simplicial-coordinate-translation.md).
