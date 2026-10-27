# Finite-length projective dimensions over the diagonal quotient

Let `k` be any field, `S` a finite lattice, `A` the interval-pair incidence algebra, `I` its
diagonal ideal, `B = A/I`, and `C = Bᵐᵒᵖ`. For each strict vertex `v`, let `Vᵥ` be the actual
right `B`-module, viewed as a left `C`-module, constructed in
[the simple-module classification](incidence-quotient-simple-modules.md).

For a finite-length `M : ModuleCat C`, the library proves

`projectiveDimension M ≤ ⨆ v : StrictVertex S, projectiveDimension Vᵥ`.

This is an inequality in Mathlib's `WithBot ℕ∞`: it includes the zero-module value `⊥` and allows
an infinite value. It gives no numerical estimate and does not require the supremum to be
attained. The public bound interface is also available at each natural degree: if every `Vᵥ` has
`HasProjectiveDimensionLE Vᵥ d`, every finite-length `M` has `HasProjectiveDimensionLE M d`.
Conversely, a bound on every finite-length module gives the same bound on every `Vᵥ`, since each
actual vertex module is simple and therefore finite length. These implications form the public
uniform-bound equivalence.

The finite-length lifting theorem follows Mathlib's `IsFiniteLength` induction. In the simple
quotient case, it uses the actual row `N → M → M/N` formed by `Submodule.subtype` and `Submodule.mkQ`.
The short-exactness proof is the module category's subtype/quotient exactness result. The quotient
is simple by the induction constructor, so the #699 classification supplies a `C`-linear
isomorphism to one of the actual `Vᵥ`. Transporting its dimension bound and applying
`ShortExact.hasProjectiveDimensionLT_X₂` completes the extension step. The zero case uses
Mathlib's zero-object criterion for `HasProjectiveDimensionLT`.

For the unconditional inequality, write the candidate bound as `D = ⨆ v, projectiveDimension Vᵥ`.
The proof unfolds `projectiveDimension` as the infimum of natural degrees admitting Ext
vanishing. Whenever `D < i`, each vertex dimension is below `i`; `projectiveDimension_lt_iff`
then supplies the common Ext-vanishing degree used in the finite-length theorem. Thus `D` is
admissible for `M`, even when the supremum is infinite or the vertex set is empty. No degree value
is introduced as a premise.

The underlying-field version uses the existing `restrictRightQuotientModule M` action. Its
finite-dimensionality gives both Noetherianity and Artinianity over `k`. With the actual scalar
tower `k → C → M`, Mathlib transfers these properties to `C`; the finite-length criterion then
gives `IsFiniteLength C M`. The already established inequality and uniform-bound equivalence
therefore apply to every module finite-dimensional over this restricted `k`-module. Each `Vᵥ`
itself is one-dimensional after restriction by `rightVertexModule_restrictKIso`, so the reverse
uniform-bound implication remains available in this class. No finite-field, algebraic-closure,
semisimplicity, or chosen-composition-series premise is added.

This is the finite-length reduction step suggested by [BOOS24-v3, §2.4 and the first paragraph of
Lemma 5.7](references.md#BOOS24-v3), using the actual quotient-simple classification from #699 and
Notation 5.9. It does not formalize the paper's subsequent tensor/base-change resolution, prove a
quotient-versus-incidence global-dimension inequality, or assert the numerical `2n−2` bound.

The finite-length induction structure adapts
[`ModuleCat.hasProjectiveDimensionLT_of_isFiniteLength`](https://github.com/TauCetiProject/TauCeti/blob/7b0d106bf79dbea38ba8819985bd029989181287/TauCeti/Algebra/Category/ModuleCat/Projective/Dimension.lean)
from TauCeti's `Dimension.lean` at commit
[`7b0d106bf79dbea38ba8819985bd029989181287`](https://github.com/TauCetiProject/TauCeti/tree/7b0d106bf79dbea38ba8819985bd029989181287).
That source is copyright © 2026 The Tau Ceti contributors and is licensed under Apache-2.0, as
stated in its [file header](https://github.com/TauCetiProject/TauCeti/blob/7b0d106bf79dbea38ba8819985bd029989181287/TauCeti/Algebra/Category/ModuleCat/Projective/Dimension.lean)
and [LICENSE](https://github.com/TauCetiProject/TauCeti/blob/7b0d106bf79dbea38ba8819985bd029989181287/LICENSE).
This module adapts the induction to the quotient-specific vertex bound and does not import or add
TauCeti as a dependency. Its public API remains specific to this quotient; it does not add a
second generic finite-length framework.
