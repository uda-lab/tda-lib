# Real open intervals and thickening

## Objects and morphisms

`TDA.Reeb.OpenInterval` is the type of open order-convex subsets of `ℝ`, bundled as a carrier
set with proofs of `IsOpen` and `Set.OrdConnected`. The objects are the empty set `⊥`, the
bounded intervals `ioo a b`, the open rays `ioi a` and `iio b`, and `ℝ` itself `⊤`. The
constructor `ioo a b` is defined for all real `a` and `b` and equals `⊥` when `b ≤ a`.

The order is inclusion of carriers (`le_iff_subset`), and the category is mathlib's thin
category of this partial order: a morphism `I ⟶ J` exists exactly when `I ⊆ J`. Binary
intersection is the meet of a `SemilatticeInf` instance, so overlap maps `I ⊓ J ⟶ I` are
`homOfLE inf_le_left`. No join is provided, because a union of order-convex sets need not be
order-convex.

Every object is determined by its endpoints in `EReal`. `lower I` and `upper I` are the infimum
and supremum of `I` in `EReal`, and `ofEReal a b = {x | a < x < b}`. The recovery theorem
`ofEReal_lower_upper` holds for every object, with `⊥` having endpoints `(⊤, ⊥)`. The encoding
is not a bijection: every pair with `b ≤ a` encodes `⊥`.

## Inclusion into the open sets of the line

`toOpens` sends an interval to its carrier in `TopologicalSpace.Opens ℝ`. It is monotone,
reflects the order (`toOpens_le_iff`), and so gives a fully faithful functor `toOpensFunctor`
between thin categories. It preserves binary intersections (`toOpens_inf`). If a family of
intervals has union `U`, the supremum of their images in `Opens ℝ` is the image of `U`
(`iSup_toOpens_eq`). These are the order-theoretic inputs for comparing gluing over interval
covers with gluing over all open covers; the comparison theorem itself is not part of this
API.

## Thickening

For `ε : ℝ≥0`, thickening is the pointwise sum with a closed interval:

```lean
(thicken ε I : Set ℝ) = (I : Set ℝ) + Set.Icc (-(ε : ℝ)) ε
```

equivalently `x ∈ thicken ε I ↔ ∃ y ∈ I, |x - y| ≤ ε` (`mem_thicken`). The parameter type
`ℝ≥0` encodes `ε ≥ 0`, so the laws below carry no side conditions. The thickening is open
because it is a union of translates of an open set, and order-convex because sums of convex
subsets of `ℝ` are convex.

The proved laws are:

- `thicken 0 I = I`, `thicken ε ⊥ = ⊥` and `thicken ε ⊤ = ⊤`;
- `I ≤ thicken ε I`, monotonicity in `I`, and `thicken ε I ≤ thicken δ I` for `ε ≤ δ`;
- `thicken ε (thicken δ I) = thicken (ε + δ) I`, from `Set.Icc_add_Icc`, and the other order
  `thicken δ (thicken ε I) = thicken (ε + δ) I`;
- for `a < b`, `thicken ε (ioo a b) = ioo (a - ε) (b + ε)`; for rays,
  `thicken ε (ioi a) = ioi (a - ε)` and `thicken ε (iio b) = iio (b + ε)`.

The bounded formula needs `a < b`. For `b ≤ a` the interval `ioo a b` is empty and stays empty,
while `ioo (a - ε) (b + ε)` is nonempty once `2ε > a - b`. Thickening does not preserve
disjointness: `(0, 1)` and `(2, 3)` are disjoint, but their `1`-thickenings both contain `3/2`.

For `0 < ε` and every open subset of `ℝ`, the thickening coincides with mathlib's
`Metric.thickening ε` (`thickenSet_eq_thickening`). At `ε = 0` they differ:
`Metric.thickening 0 s` is empty, while `thicken 0` is the identity. `Metric.cthickening 0 s` is
the closure of `s`, so it is not the identity either. Neither mathlib construction serves as the
definition.

## Endofunctor packaging

`thickenFunctor ε` is thickening as an endofunctor of the interval category. `thickenUnit ε`
is the natural transformation from the identity given by `I ⊆ thicken ε I`, and
`thickenMap h` for `h : ε ≤ δ` is the enlargement `thickenFunctor ε ⟶ thickenFunctor δ`.
`thickenZeroIso` identifies `thickenFunctor 0` with the identity. The composition isomorphism
applies `ε` first:

```lean
thickenCompIso ε δ : thickenFunctor ε ⋙ thickenFunctor δ ≅ thickenFunctor (ε + δ)
```

For a functor `F` out of the interval category, precomposing with `thickenFunctor δ` and then
with `thickenFunctor ε` is definitionally precomposition with
`thickenFunctor ε ⋙ thickenFunctor δ`. Because the category is thin, all coherence equations
between these maps hold automatically.

## Source correspondence

de Silva, Munch and Patel define **Int** as the category of open intervals of `ℝ` with
inclusions (*Categorified Reeb Graphs*, §3). For `I = (a, b)` and `ε ≥ 0` they set
`I^ε = (a - ε, b + ε)` (§4.1, before Definition 4.1). The expansion `Ω_ε : Int → Int` is a functor
with the unit `I ⊆ I^ε` (§4.2, Observation 4.11). `thicken_ioo` is the source formula on
nonempty bounded intervals. Admitting `∅`, rays and `ℝ` as objects, defining thickening as a
pointwise sum on every object, and taking `ε : ℝ≥0` are choices of the library; on nonempty
bounded intervals they agree with the source definition.

Sources: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147);
[pinned mathlib order-connected sets](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/Interval/Set/OrdConnected.lean);
[pinned mathlib interval sums](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Group/Pointwise/Interval.lean).
