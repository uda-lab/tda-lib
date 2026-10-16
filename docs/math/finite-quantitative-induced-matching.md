# Quantitative finite induced matchings from kernel and cokernel shortness

## Modules, occurrences and translations

Fix a field `k : Type u` and pointwise finite-dimensional modules
`M N : PModule.{u,0,u} k (Fin s)`. The input is an actual natural transformation
`f : M ⟶ N`. The field and module carriers share their universe.
The canonical barcodes contain half-open intervals `[birth,death)` with
`birth < death ≤ s`. Occurrences retain their original list indices, including
separate labels for repeated interval values.

A translation `theta : Fin s →o Fin s` is monotone and inflationary:
`hTheta : ∀ i, i ≤ theta i`. It may identify stages or fix them.
`TranslationTrivial theta hTheta K` means that every actual structure map
`K(i → theta i)` is zero. An interval `[b,d)` is long when `theta(b) < d`;
equality belongs to the short case.

Birth is an observed stage, packaged by `FiniteInterval.birthStage`.
Death may instead be the terminal endpoint `s`. Define its extension by

```text
thetaPlus(d) = theta(d),  d < s,
thetaPlus(s) = s.
```

`FiniteInterval.translatedDeath` implements this convention. Its value depends
only on death, and identity translation leaves every endpoint unchanged.
The terminal endpoint records finite observed survival and is never used as a
`Fin s` stage. The empty chain supplies no occurrence and selects no stage.

## Actual kernel shortness

`finiteKernel f` is mathlib's categorical kernel in the functor category.
`finiteKernelFiberIso` identifies its fiber with `ker(f_i)` and takes the actual
kernel inclusion to the subtype inclusion. Its finite dimensionality follows
from the source subspace. Naturality of the inclusion and its component
monomorphisms prove `finiteKernel_map_eq_zero_iff`. Thus
`kernel_translationTrivial_iff` gives

```text
TranslationTrivial theta hTheta (finiteKernel f)
  ↔ ∀ i, ker(f_i) ≤ ker M(i → theta i).
```

The right side is a proved criterion for the actual kernel, rather than a
substitute object or an assumed barcode condition.
The analogous actual cokernel criterion is explained in
[the mono translation estimate](finite-mono-translation.md).

## Shifted survival counts for an epimorphism

First suppose `p : M ⟶ N` is componentwise surjective and its actual kernel is
translation-trivial. Let `S_M(b,c)` count bars born exactly at `b` that survive
at `c`. The result is

```text
S_M(b,theta(c)) ≤ S_N(b,c),    b ≤ c < s.
```

The proof uses actual linear maps. Kernel shortness makes `M(c → theta c)`
kill `ker(p_c)`. The first isomorphism theorem therefore descends this transition
through the surjection `p_c` to a map `N_c → M_(theta c)`.
For any earlier stage `a ≤ c`, naturality identifies the image of
`N(a → c)(p_a x)` with `M(a → theta c)(x)`.

Consequently the descended map restricts to a surjection

```text
image N(b → c) → image M(b → theta c).
```

For positive birth, surjectivity at `b−1` and the same naturality equation
send the preceding target image into the preceding source image. Passing to
these image quotients gives a genuine surjection. Their dimensions are the
same-birth survival counts, so the dimension comparison proves the inequality.
Birth zero compares the images directly, without forming a predecessor.
`birthSuffixCount_translated_le_of_kernelTrivial` exposes the result.

## The canonical epi estimate

The [canonical epi embedding](finite-epi-matching.md) goes from target
occurrences back to source occurrences. It preserves birth and matches equal
ordinals in each birth group, ordered by descending death and original index.
For a target occurrence `J` and its source `I`,
`epiEmbedding_death_bounds_of_kernelTrivial` proves

```text
birth(I) = birth(J),
death(J) ≤ death(I) ≤ thetaPlus(death(J)).
```

At a finite target death `d`, if the source survived `theta(d)`, its ordinal
would lie below the translated source survival count. The target ordinal lies
at or above its survival count at `d`. Equal ordinals and the shifted inequality
contradict these two bounds. At terminal death, `death(I) ≤ s` supplies the upper
bound directly.

Taking `c=b` puts every long source ordinal below the target birth-group size.
`epiEmbedding_covers_long_of_kernelTrivial` therefore gives exactly one target
preimage for every long source. The unmatched-source result is its contrapositive.
Short source bars may also be matched. Terminal source bars are always long for
an endomap of `Fin s`, so kernel shortness forces their coverage too.

## Quantitative matching through the actual image

For an arbitrary `f`, the [actual image factorization](finite-induced-matching.md)
is an epi followed by a mono. Corestriction preserves the component kernel;
the image inclusion has the same range as `f`. The proved kernel/range criteria
therefore transfer actual shortness to the respective factors, without choosing
new kernel or cokernel objects as hypotheses.

Let `inducedMap f i = some j`, and write `I` and `J` for the source and target
intervals. Kernel shortness for `thetaK` and cokernel shortness for `thetaC` give

```text
birth(J) ≤ birth(I) ≤ thetaC(birth(J)),
birth(I) < death(J) ≤ death(I) ≤ thetaKPlus(death(J)).
```

The unique intermediate image occurrence has source birth and target death.
This connects the two factor estimates to the actual partial injection.
`inducedMap_endpoint_bounds_of_shortness` combines them.
The one-sided birth/death theorems require only their respective shortness
hypothesis. Independently, every kernel-long source has exactly one selected
target, and every cokernel-long target has exactly one selected source.
Unmatched occurrences satisfy the corresponding shortness bound.

Consumers include actual truncations attaining the finite death bound, a
positive-birth quotient, a noninjective translation, terminal coverage, distinct
duplicate labels, identity translation and the empty chain. Threshold-short
sources occur both matched and unmatched. A nonzero kernel at a fixed point
fails shortness. The genuine overlap map `[1,3) → [0,2)` has nonzero kernel and
cokernel, attains both endpoint upper bounds and exercises both coverage directions.

## Source correspondence and limits

Manifestation, attribution and rights: [BL15-v4](references.md#BL15-v4).
[Bauer–Lesnick v4, §6, formal Theorem 6.1](https://arxiv.org/html/1311.3681v4#S6)
controls matched births and long targets by cokernel triviality, and matched
deaths and long sources by kernel triviality. Its part (iii) is obtained by
dualizing (ii), with Proposition 5.5 and Lemma 6.2 giving an alternative route.
The canonical epi order is in §4.1 and Theorem 4.2(ii).

The arbitrary finite monotone translation theorem is a library extension.
The direct quotient-surjection proof here replaces the source's duality route;
no linear-dual or order-reversal adapter is supplied. The [real induced matching](real-induced-matchings.md) converts the rounded
finite bounds and actual partial injection to exact real endpoint estimates,
long-bar coverage and a total essential equivalence. The
[common-grid sampled defects](constructible-defects-sampling.md) supply its
actual shortness inputs. Its interleaving consumer reaches the shifted target;
the ε-cost estimate after +ε untranslation and `d_B≤d_I` remain separate steps.
The matching retains the qualitative construction and its restriction of
composition laws to monos and epis.
