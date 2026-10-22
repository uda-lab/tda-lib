# Gaussian measure embeddings and C₀ approximation

Fix a nonzero real bandwidth σ. On the birth–death plane ℝ², use

\[
k_\sigma(p,q)=\exp\!\left(-\frac{\|p-q\|_2^2}{2\sigma^2}\right).
\]

The norm in this formula is Euclidean. The default product norm on the Lean type
`ℝ × ℝ` is the maximum norm; the analytic proof uses `WithLp 2 (ℝ × ℝ)` to express
the Euclidean geometry. Negative bandwidths give the same kernel as their absolute
values. The nonzero hypothesis is necessary because Lean's division convention
makes the zero-bandwidth kernel constant.

Let Hσ be the reproducing kernel Hilbert space constructed by
`WeightedKernel.Space σ`, and let φσ(p) be its kernel feature
`WeightedKernel.featureAt σ p`. Its Hilbert norm is one. Continuity and this
bound prove Bochner integrability against every finite positive measure and
integrability against the total variation of every finite signed measure.
The signed embedding

\[
E_\sigma(\mu)=\int \varphi_\sigma(p)\,d\mu(p)
\]

is `signedEmbedding`, defined with mathlib's Banach-valued vector-measure
integral. The Jordan formula, linearity and atomic evaluation are properties of
that integral. In particular an atom of coefficient c contributes c·φσ(p), and
finite sums agree with the existing finite-support `measureEmbedding` and
weighted finite-diagram embedding, preserving multiplicities.
`norm_signedEmbedding_le_totalVariation` gives ‖Eσ(μ)‖ ≤ |μ|(ℝ²).
`inner_signedEmbedding` identifies pairing with a function f in Hσ with its
scalar signed integral. `signedEmbedding_apply` gives evaluation by a
Gaussian section, and `norm_signedEmbedding_sq` and
`norm_signedEmbedding_sub_sq` identify squared norms and distances with
iterated signed kernel integrals. The Jordan comparison and bounded feature
integrability justify these identities without a compact-support premise.

`signedEmbedding_injective` proves that Eσ determines every finite signed Borel
measure on ℝ². Such measures are Radon. The positive-measure evaluation theorem
identifies evaluation at z with the integral of kσ(z,·). Restricting injectivity
to probability measures gives `probabilityEmbedding_injective`, the
characteristic-kernel conclusion. The diffuse fixture uses the negative of the
product of two standard Gaussian probability laws. Its total variation is
non-atomic and has positive mass outside every compact subset of ℝ²; the signed
mean comparison and injectivity theorem apply to this input.

The separation proof specializes mathlib's standard Gaussian characteristic
function. Bounded Fubini interchanges identify Gaussian double integrals with
products of characteristic functions. Equality of all Gaussian section
integrals forces the squared difference of the characteristic functions to
have integral zero under a full-support Gaussian law. Continuity then gives
equality everywhere, and characteristic-function uniqueness identifies the
measures. This supplies the general-measure step beyond finite Gram matrices.

## Uniform approximation on the full plane

C₀(ℝ²) consists of continuous real functions vanishing at infinity, with the
uniform norm. Every Gaussian section belongs to C₀, and
`rkhsFunction_zero_at_infty` proves the same for every element of Hσ.
`rkhsToC0CLM` is the continuous linear inclusion, whose operator bound is
one.

`gaussian_sections_dense` proves that finite linear combinations of Gaussian
sections are uniformly dense in C₀(ℝ²). Consequently `denseRange_rkhsToC0`
establishes C₀ universality for Hσ itself. `exists_gaussian_span_approx` gives a
uniform approximation statement for a target function and a positive error
tolerance, without unfolding density.

The density proof separates a hypothetical proper closed span by a bounded
linear functional. `C0MeasureRepresentation.exists_finite_regular_measure_sub`
represents that functional as the difference of integration against two finite
regular measures. Its finite-mass bound follows from compact cutoffs and the
functional's operator norm; uniform compact-support approximation extends the
representation from C_c to C₀. Gaussian separation makes an annihilating
functional zero. This is the C₀ duality argument relevant to
[SFL11 Proposition 2](references.md#SFL11), specialized to the full-plane
Gaussian rather than a general kernel characterization.

## Positive persistence measures with finite weighted mass

Use the existing `UpperPoint` space U = {(b,d) : b < d} of finite bars.
For positive Radon measures μ on U, take a continuous real weight w that is
strictly positive at every point. Assume

\[
\int_U w(p)\,d\mu(p)<\infty.
\]

`weightedPlaneMeasure` weights μ and includes it into ℝ².
`weightedPersistenceEmbedding` takes its full-plane Gaussian mean.
`integrable_weightedFeature` verifies integrability of the weighted feature
against μ, and `weightedPersistenceEmbedding_eq_integral` identifies the two
integral expressions. `weightedPersistenceEmbedding_eq_iff_continuous` proves recovery of μ among
Radon measures satisfying the same finite-weighted-mass condition. The more
general measurable-weight theorem `weightedPersistenceEmbedding_eq_iff` also
applies to arbitrary positive Borel measures. Finite weighted mass makes both
the weighted measure on U and its ambient pushforward regular. The
original measures may have infinite mass; no positive lower bound on w is
needed. Inverse weighting and injectivity of the measurable inclusion recover
them from their finite weighted measures.

`weightedPersistenceEmbedding_finite_occurrences` identifies the positive
finite occurrence measure with the existing birth–persistence weighted
`embedding`. Coincident labels contribute repeatedly.
`countableDiagramEmbedding_eq_iff` recovers locally finite countable occurrence
measures under summability of their strictly positive weights.

The countable fixture places one unit atom at (0,2⁻ⁿ), n ≥ 0. It has infinite
total mass and is locally finite, hence Radon, on U. Persistence weighting gives
finite mass because the geometric series converges. The recovery theorem
applies directly to this example.

The ambient plane matters. A Gaussian section restricted to U need not vanish
at infinity there: the same sequence approaches the excluded diagonal while
escaping every compact subset of U, and a restricted section can tend to a
positive value. `restricted_section_not_c0` verifies this boundary case. The
weighted recovery theorem uses the full-plane mean and does not assert a C₀
kernel on U. Essential bars remain separate data. Finite pixel persistence
images and Gaussian kernels applied to diagram embeddings have no
characteristic or universality conclusion here.

These are abstract noncomputable integral, representation and approximation
results. Finite atomic compatibility is a correctness bridge to the existing
finite sums; the package provides no executable numerical integration or
algorithm for choosing approximation coefficients.

Source identities and permitted uses are recorded under
[SFL11](references.md#SFL11), [KFH18](references.md#KFH18),
[mathlib](references.md#mathlib-0df444a), and the narrowly adapted
[Tau Ceti signed C_c source](references.md#TauCeti-b971ef7).
