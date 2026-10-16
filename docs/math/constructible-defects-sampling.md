# Constructible defects and shortness on critical samples

An actual interleaving of finite-constructible real modules supplies finite
sampled kernels and cokernels with a proved shortness bound. The bridge uses
actual natural transformations, categorical defects and within-cell
isomorphisms. It constructs the common grid and finite translation used in
the conclusion.

## Modules, grids and the two samples

Fix a finite strictly increasing grid `c : Fin n ↪o ℝ`. The predicate
`IsConstructible c M` requires an actual zero left tail and isomorphic actual
structure maps within each half-open cell, including the unbounded final cell.
The [reconstruction API](constructible-modules.md) counts these cells with
`cellIndex c`. A parameter exactly at a critical value belongs to its new cell.

Critical sampling is `reindex c.toOrderHom M` on `Fin n`, with a morphism sampled
by `reindexNatTrans c.toOrderHom f`. This is the sample used by `moduleDiagram`.
The distinct function `FiniteConstructible.sample c M` adds a zero initial stage
for reconstruction. The critical sample here has no padded stage, sentinel real
grade or appended terminal zero. An empty critical grid gives an empty sample;
constructibility on that grid also forces the actual real module to be pointwise zero.

Constructibility and natural defect comparisons work over a ring, with
independent coefficient and module-carrier universes. The finite
`TranslationTrivial` wrappers use the existing coefficient-field and same-carrier
universe convention. None of these shortness results requires finite dimensionality.

## Actual kernels and cokernels

Let `f : M → N` be an actual natural transformation, with M and N constructible
on c. The results `IsConstructible.kernel` and `IsConstructible.cokernel` prove
constructibility of mathlib's actual functor-category `kernel f` and `cokernel f`.
They do not assume a chosen defect model.

On the left tail, the kernel inclusion is a monomorphism into a zero fiber,
and the cokernel projection is an epimorphism out of a zero fiber. Thus both
defect fibers are zero. Within a cell, naturality gives a commuting square whose
source and target structure maps are isomorphisms. Evaluation preserves kernels
and cokernels; their induced maps for that square are isomorphisms. The actual
defect structure maps agree with these induced maps through the evaluation
comparisons, so they are isomorphisms as well.

Left whiskering by the critical-grid functor preserves kernels and cokernels.
The natural isomorphisms `criticalKernelIso` and `criticalCokernelIso` therefore
identify the critical sample of each real defect with the actual defect of the
sampled morphism. Their compatibility theorems retain the actual kernel
inclusion and cokernel projection. This closure argument applies to a morphism
between modules on a common grid; it makes no claim that arbitrary submodules
are constructible.

## Translating and rounding critical indices

Fix a finite nonnegative real `δ : ℝ≥0`. The positive-evaluation shift sends a
parameter t to `t+δ`. For every critical index i, the value `c_i+δ` lies on or
after `c_i`, so its cell is positive. Define

\[
\theta_\delta(i)=\operatorname{cellIndex}(c,c_i+\delta)-1.
\]

The function `sampleTranslation c δ` is this monotone inflationary endomap of
`Fin n`. Its selected critical value satisfies

\[
c_i\le c_{\theta_\delta(i)}\le c_i+\delta,
\qquad
\operatorname{cellIndex}(c,c_{\theta_\delta(i)})
 =\operatorname{cellIndex}(c,c_i+\delta).
\]

Thus rounding selects the start of the translated parameter's cell. It can fix
an interior index when δ is smaller than the next gap. Exact critical boundaries
advance to the critical value itself. At δ=0 the endomap is the identity.
The last observed index is fixed for every finite δ; its real cell remains
unbounded. No barcode terminal endpoint is introduced as an observed stage.

## Transferring actual annihilation

Suppose A is c-constructible and its actual real transition `transition δ A`
is zero. The map from `c_i` to `c_i+δ` factors as

\[
A(c_i)\longrightarrow A(c_{\theta_\delta(i)})
 \longrightarrow A(c_i+\delta).
\]

The second map is an actual within-cell isomorphism. Cancelling it from the
zero composite proves that the first map is zero. This is
`critical_structureMap_eq_zero`, expressed as `critical_translationTrivial`
over a field. Cancellation is essential when the translation rounds down.

Apply this to the actual real kernel or cokernel of f, then transport through
the natural sampling comparison. The results
`criticalKernel_translationTrivial` and `criticalCokernel_translationTrivial`
prove shortness of the actual finite defect of the sampled morphism. Their
generic real zero-transition hypothesis is explicit.

For an actual ε-interleaving of M and N on possibly different grids c and d,
`interleaving_critical_defects` constructs
`e = commonGrid c (shiftGrid ε d)`. The [grid results](constructible-refinement.md)
put M and the actual shifted target on e. The theorem derives constructibility
of both actual defects and both finite sampled shortness statements for
`sampleTranslation e (ε+ε)`. The real annihilation comes from the
[interleaving equations](real-interleaving-shortness.md); no shortness,
matching or decomposition witness is an input to this theorem.

## Boundary consumers and remaining scope

An actual one-interleaving obtained from zero comparison maps on `[0,2)` has
nonzero kernel and cokernel. Its constructed common grid includes a negative
shifted critical value. Both sampled defects satisfy the double-shift bound,
while the sampled kernel fails the shorter parameter because its real map
from 0 to 1 preserves coefficient one. The sampling comparisons retain their
actual inclusion and projection in this example.

The grid `[-3,0,10]` checks strict rounding, an interior fixed index, an exact
translated boundary and the fixed last observation. A genuine constructible
essential tail rejects every finite sampled shortness bound: its last self-map
is an isomorphism on a nonzero fiber. Parameter zero has actual zero defects
even when the original module is nonzero. Empty-grid sampling is also checked.
These consumers are in `TDA.Persistence.ConstructibleDefectExamples`.

[Bauer–Lesnick v4](https://arxiv.org/html/1311.3681v4), §2.1, gives the functor
and natural-transformation conventions; §3.1 defines positive shifts and
transitions. Section 6 defines epsilon-triviality by the zero transition, and
Lemma 6.3 derives double-shift defect annihilation from an interleaving. Its
field-valued case is a checked specialization of the existing ring-valued
annihilation theorem. Finite-grid defect closure, rounded critical translation
and the sampling bridge above are library constructions using mathlib's actual
limit comparisons, rather than numbered source sampling theorems.
Source and rights metadata are in [BL15-v4](references.md#BL15-v4).

No inspection of general infinite decomposition or the omitted Lemma 6.2 proof
is claimed. The [shift-diagram correspondence](constructible-shift-diagrams.md)
provides the actual shifted diagram and inverse occurrence labels. General
real induced matching and `d_B≤d_I` remain separate results. The
[finite quantitative matching API](finite-quantitative-induced-matching.md)
retains its finite-dimensionality and endpoint hypotheses.
