# The thickening–cosheaf comparison on constructible ℝ-spaces

## Setting

`ConstructibleSpaceCat` is the full subcategory of constructible ℝ-spaces of the real slice
`Over (TopCat.of ℝ)`, with all continuous height-preserving maps (see
`reeb-constructible-quotient.md`). `IsConstructibleSpace` asks for an isomorphism over `ℝ` with the
realization of a presentation whose pieces are compact and locally path-connected; no piece and no
realization is assumed Hausdorff, and every presentation has at least one critical level, also
for the empty space.

- `T_ε = thickeningFunctor ε : ConstructibleSpaceCat ⥤ ConstructibleSpaceCat` is the product
  thickening `X × [-ε, ε]` with height `(x, t) ↦ f x + t` and maps `(x, t) ↦ (g x, t)`, for every
  `ε : ℝ≥0` (see `reeb-thickening-constructible.md`).
- `C' = constructibleCosheafFunctor : ConstructibleSpaceCat ⥤ ConstructibleCosheafCat.{0}` sends
  `X` to the path components of the inverse images of open intervals (see
  `reeb-constructible-comparison.md`).
- `S_ε = constructibleSmoothing ε : ConstructibleCosheafCat.{0} ⥤ ConstructibleCosheafCat.{0}`
  is the smoothing `F ↦ F ∘ (·)^ε` of constructible cosheaves (see
  `reeb-constructible-smoothing.md`). It is not `RGraph.constructibleSmoothing ε`, the endofunctor
  `ℛ T_ε` of constructible ℝ-spaces of `reeb-geometric-interleaving-equivalence.md`.
- `ℛ = quotientRGraphFunctor : ConstructibleSpaceCat ⥤ RGraphCat` is the Reeb functor and
  `C'' = RGraph.cosheafFunctor : RGraphCat ⥤ ConstructibleCosheafCat.{0}` the path-component
  cosheaf of a graph object (see `reeb-rgraph-cosheaf-equivalence.md`).
- `η = constructibleCosheafComparisonIso : C' ≅ ℛ ⋙ C''` is the comparison of the path components
  of a constructible ℝ-space with those of its Reeb quotient (see
  `reeb-constructible-comparison.md`).
- `ρ = GeometricThickening.componentComparisonNatIso ε` is the first-projection comparison
  `T_ε ⋙ C ≅ C ⋙ smoothing ε` on the whole real slice; on an interval `I` it sends the class of
  `(x, t)` in `{z | f x + t ∈ I}` to the class of `x` in `{x | f x ∈ I^ε}` (see
  `reeb-geometric-thickening.md`).

Everything is in universe `0`, as `ConstructibleSpaceCat` and `ConstructibleCosheafCat.{0}` are.
No new geometric argument is made: the results lift `ρ` through the full subcategories and
compose it with `η⁻¹`.

## The comparison

```lean
constructibleThickeningComparisonIso ε :
    thickeningFunctor ε ⋙ constructibleCosheafFunctor ≅
      constructibleCosheafFunctor ⋙ constructibleSmoothing ε
```

has the components of `ρ` (`constructibleThickeningComparisonIso_hom_app_hom`,
`constructibleThickeningComparisonIso_inv_app_hom`, and unbundled as
`GeometricThickening.componentComparison` of the structure map,
`constructibleThickeningComparisonIso_hom_app_hom_eq`, all by `rfl`). On representatives
(`constructibleThickeningComparisonIso_hom_app_hom_app_mk`), for every open interval `I` and every
`(x, t)` with `f x + t ∈ I`,

```text
ρ_X(I) [(x, t)] = [x]   in the components of {x | f x ∈ I^ε}.
```

Both inverse laws are those of an isomorphism in `ConstructibleCosheafCat.{0}`, so they hold for the
whole interval functors, and naturality is the naturality of `ρ` in slice morphisms: it holds for
every continuous height-preserving map, whatever presentations, critical lists or numbers of
levels its source and target have. Followed by the inclusion of constructible cosheaves it is `ρ`
whiskered by the inclusion of constructible ℝ-spaces
(`isoWhiskerRight_constructibleThickeningComparisonIso`).

## The companion

```lean
constructibleThickeningQuotientComparisonIso ε :
    thickeningFunctor ε ⋙ quotientRGraphFunctor ⋙ RGraph.cosheafFunctor ≅
      constructibleCosheafFunctor ⋙ constructibleSmoothing ε :=
  Functor.isoWhiskerLeft (thickeningFunctor ε) constructibleCosheafComparisonIso.symm ≪≫
    constructibleThickeningComparisonIso ε
```

Its source is also `RGraph.thickeningQuotient ε ⋙ RGraph.cosheafFunctor`
(`thickeningFunctor_comp_quotientRGraphFunctor_comp_cosheafFunctor`, by `rfl`). The component at
`X` is `β_X = η_(T_ε X).inv ≫ ρ_X`, in the full subcategory and on the underlying precosheaves
(`constructibleThickeningQuotientComparisonIso_hom_app`,
`constructibleThickeningQuotientComparisonIso_hom_app_hom`), with inverse `ρ_X⁻¹ ≫ η_(T_ε X)`
(`constructibleThickeningQuotientComparisonIso_inv_app`). Naturality is that of the composite of two
natural isomorphisms, again for all height-preserving maps.

The canonical hom-component equation `η_(T_ε X).hom ≫ β_X = ρ_X` holds in the full subcategory
(`constructibleCosheafComparisonIso_hom_app_comp_constructibleThickeningQuotientComparisonIso_hom_app`)
and unbundled, with `ReebQuotient.intervalComponentComparison` of the thickened height and
`GeometricThickening.componentComparison`
(`intervalComponentComparison_comp_constructibleThickeningQuotientComparisonIso_hom_app_hom`). On
representatives (`constructibleThickeningQuotientComparisonIso_hom_app_hom_app_mk`),

```text
β_X(I) [q (x, t)] = [x],
```

where `q` is the Reeb projection of `T_ε X`, the left class lies in the components of
`{p | q̄ p ∈ I}` of the Reeb quotient and the right class in the components of `{x | f x ∈ I^ε}`.
This is a statement about components; no map from points of the Reeb quotient to `X` is asserted.

## Zero section and unit

`thickeningFunctorZeroSection ε : 𝟭 ConstructibleSpaceCat ⟶ thickeningFunctor ε` is the zero
section `x ↦ (x, 0)` of `GeometricThickening.zeroSectionNatTrans ε`, lifted
(`thickeningFunctorZeroSection_app_hom`). The comparison sends `C'` of it to the lifted smoothing
unit:

```lean
constructibleCosheafFunctor.map ((thickeningFunctorZeroSection ε).app A) ≫
    (constructibleThickeningComparisonIso ε).hom.app A =
  (constructibleSmoothingUnit ε).app (constructibleCosheafFunctor.obj A)
```

(`constructibleCosheafFunctor_map_thickeningFunctorZeroSection_comp`), and as an equation of natural
transformations `C' ⟶ C' ⋙ S_ε`
(`whiskerRight_thickeningFunctorZeroSection_comp_constructibleThickeningComparisonIso`). Both are
`GeometricThickening.map_zeroSectionNatTrans_comp_componentComparisonNatIso`.

For the companion, the unit is the existing `RGraph.constructibleSmoothingUnit ε : X ⟶ ℛ T_ε X`,
the zero section followed by the Reeb projection (see
`reeb-geometric-interleaving-equivalence.md`); no new structure is introduced. Then

```lean
constructibleCosheafFunctor.map ((RGraph.constructibleSmoothingUnit ε).app A) ≫
    (constructibleThickeningQuotientComparisonIso ε).hom.app A =
  (constructibleSmoothingUnit ε).app (constructibleCosheafFunctor.obj A)
```

(`constructibleCosheafFunctor_map_constructibleSmoothingUnit_comp`): `C'` of the Reeb projection of
`T_ε X` is `η_(T_ε X).hom`, which cancels against `η_(T_ε X).inv` in `β_X`, and the zero-section
equation remains. On representatives, `[x] ↦ [q (x, 0)] ↦ [x]`
(`constructibleThickeningQuotientComparisonIso_hom_app_hom_app_unit_mk`).

## `ε = 0`

`thickeningFunctorZeroIso : thickeningFunctor 0 ≅ 𝟭 ConstructibleSpaceCat` lifts
`GeometricThickening.zeroIso`, the first projection `X × [0, 0] → X`
(`thickeningFunctorZeroIso_hom_app_hom`, `thickeningFunctorZeroIso_inv_app_hom`); its inverse is the
zero section (`thickeningFunctorZeroIso_inv`). At `ε = 0`,

```lean
constructibleCosheafFunctor.map (thickeningFunctorZeroIso.hom.app A) =
  (constructibleThickeningComparisonIso 0).hom.app A ≫
    constructibleSmoothingZeroIso.hom.app (constructibleCosheafFunctor.obj A)
```

(`constructibleCosheafFunctor_map_thickeningFunctorZeroIso_hom_app`, from
`GeometricThickening.map_zeroIso_hom_app`). On a constructible ℝ-space the Reeb quotient of
`T_0 X` is the Reeb quotient of `X`, not `X`, so the companion's zero comparison passes through
`η_X`:

```lean
RGraph.cosheafFunctor.map (quotientRGraphFunctor.map (thickeningFunctorZeroIso.hom.app A)) ≫
    constructibleCosheafComparisonIso.inv.app A =
  (constructibleThickeningQuotientComparisonIso 0).hom.app A ≫
    constructibleSmoothingZeroIso.hom.app (constructibleCosheafFunctor.obj A)
```

(`cosheafFunctor_map_thickeningFunctorZeroIso_comp_constructibleThickeningQuotientComparisonIso`),
by naturality of `η⁻¹` along `T_0 X ≅ X`.

## Graph objects

On graph objects `RGraph.rgraphToConstructible ⋙ thickeningFunctor ε` is
`RGraph.thickeningToConstructible ε` (see `reeb-thickening-constructible.md`). Along this inclusion

- the comparison is the graph comparison `RGraph.thickeningCosheafComparisonIso ε`
  (`isoWhiskerLeft_rgraphToConstructible_constructibleThickeningComparisonIso`, and componentwise
  `constructibleThickeningComparisonIso_hom_app_rgraphToConstructible`);
- the companion is `RGraph.geometricSmoothingComparisonIso ε`, DMP Proposition 4.32
  (`isoWhiskerLeft_rgraphToConstructible_constructibleThickeningQuotientComparisonIso`, and
  componentwise `constructibleThickeningQuotientComparisonIso_hom_app_rgraphToConstructible`).

Both equations hold by `rfl` on components; see `reeb-rgraph-smoothing.md` for the graph results,
which are unchanged.

## Values

`constructibleThickeningValueEquiv ε X I : C'(T_ε X)(I) ≃ C'(X)(I^ε)` and
`constructibleThickeningQuotientValueEquiv ε X I : C''(ℛ T_ε X)(I) ≃ C'(X)(I^ε)` are the
comparison and the companion at one interval (`constructibleThickeningValueEquiv_apply`,
`constructibleThickeningQuotientValueEquiv_apply`).

## Fixtures

`TDA.Reeb.ThickeningCosheafComparisonExamples` reuses the constant-height spaces
`constOver X c`, the indiscrete two-point space `IndiscreteBool` and the non-Hausdorff thickening
of `reeb-thickening-constructible.md`, and the single edge over `0 < 1`, its subdivision over
`0 < 1/2 < 1` and the subdivision isomorphism of `reeb-rgraph-cosheaf-equivalence.md`.

- **Empty input.** For the empty space at constant height, every value of `C'(T_ε X)` and of
  `C''(ℛ T_ε X)` is empty, for every `ε` (`thickening_empty_isEmpty`,
  `thickeningQuotient_empty_isEmpty`), transported through the value equivalences from the empty
  values of `C'(X)`.
- **A non-Hausdorff constant-height input.** For the indiscrete two-point space at height `c`,
  every map into a subspace is continuous, so any two points of an inverse image are joined
  (`joined_indiscreteBool`) and every value of `C'(X)` has at most one element. Through the
  comparison and the companion, every value of `C'(T_ε X)` and of `C''(ℛ T_ε X)` has at most one
  element, while `T_ε X` is not Hausdorff (`indiscrete_thickening_subsingleton`,
  `indiscrete_thickeningQuotient_subsingleton`); the value at `I` is nonempty when `c ∈ I^ε`
  (`indiscrete_thickening_nonempty`). For band coordinates `s, t` with `c + s, c + t ∈ I`, the
  classes of `(true, s)` and `(false, t)` agree, as do those of their Reeb classes, and both
  comparisons send them to `[true]` (`indiscrete_thickening_class_eq`,
  `indiscrete_thickeningQuotient_class_eq`).
- **`ε = 0`.** The zero comparisons of the comparison and the companion on the indiscrete
  two-point space (`indiscrete_zero_comparison`, `indiscrete_zero_companion`), and, for every
  constructible ℝ-space, the value of `C'(T_0 X)` at `I` corresponds to the value of `C'(X)` at `I`
  through `thicken_zero` (`zeroValueEquiv`).
- **Naturality for a nontrivial map across presentations.** `collapse` sends the indiscrete
  two-point space at height `0`, presented over the one level `0`, to the lower vertex of the
  single edge, presented over `0 < 1`; it identifies the two points (`collapse_not_injective`). The
  comparison and the companion are natural along it (`collapse_naturality`,
  `collapse_companion_naturality`). Along the subdivision isomorphism from the single edge over
  `0 < 1/2 < 1` to the single edge over `0 < 1`, the companion's naturality square is, as a term,
  the graph square `RGraphSmoothing.subdivision_naturality` (`subdivision_companion_naturality`).

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §3.4 and §4.3–4.4:

- **Theorem 4.24** states `𝒞T_ε ≅ S_ε𝒞` for ℝ-spaces, with the comparison `(ρ_f)_I = π₀[p_I]` of
  its proof; on the real slice this is `GeometricThickening.componentComparisonNatIso` (see
  `reeb-geometric-thickening.md`). Restricted to constructible ℝ-spaces, where `T_ε` preserves
  constructibility by **Theorem 4.27** (see `reeb-thickening-constructible.md`) and `𝒞` restricts
  to `𝒞'`, it reads `𝒞'T_ε ≅ S_ε𝒞'` as functors ℝ-**Top**ᶜ → **Csh**ᶜ; this restriction is
  `constructibleThickeningComparisonIso`. It is the source's theorem on a full subcategory, not a
  separately numbered statement of the source.
- **Theorem 3.17** states `𝒞' ≅ 𝒞''ℛ` on ℝ-**Top**ᶜ; this is `constructibleCosheafComparisonIso`
  (see `reeb-constructible-comparison.md`).
- **Proposition 4.32** states `𝒞''U_ε ≅ S_ε𝒞''` on **Reeb**, proved by
  `𝒞''ℛT_ε ≃ 𝒞'T_ε ≃ S_ε𝒞''` with Theorems 3.17 and 4.24. It is already proved on graph objects as
  `RGraph.geometricSmoothingComparisonIso` (see `reeb-rgraph-smoothing.md`). The companion
  `constructibleThickeningQuotientComparisonIso` is the same composite, `η⁻¹` at the thickening
  followed by the restricted Theorem 4.24, on all constructible ℝ-spaces, with `𝒞'` in place of
  `𝒞''` on the right. It is a library statement extending the proof of Proposition 4.32 to
  constructible input, not attributed to the source as a numbered result; the source states
  Proposition 4.32 only for ℝ-graphs, where its target `S_ε𝒞''` is `S_ε𝒞'` of the inclusion and the
  companion restricts to `RGraph.geometricSmoothingComparisonIso`.
- **Observation 4.23** gives the zero section `τ^ε : X → X_ε`, `x ↦ (x, 0)`, natural on all
  ℝ-spaces; `thickeningFunctorZeroSection` is its restriction to constructible ℝ-spaces, and
  `𝒞'(τ^ε)` followed by the restricted Theorem 4.24 is the smoothing unit.
- **Observation 4.34** and **Proposition 4.35** give the unit `ζ` as the zero section followed by
  the Reeb quotient and state its compatibility with `σ` through the isomorphism of Proposition
  4.32, for ℝ-graphs. The companion's unit equation uses the same zero section followed by the
  Reeb projection, `RGraph.constructibleSmoothingUnit`, on constructible ℝ-spaces, in the form
  `𝒞'(ζ) ≫ β = σ`; it is proved by exact cancellation of `η`, as on graph objects, and is a
  library statement on constructible input.

No new geometric argument, critical-set statement or reproof of the constructibility of `T_ε X`
is made. Not claimed here: `T_ε T_δ ≅ T_(ε+δ)` for product thickening (false in general, see
`reeb-geometric-thickening-addition.md`); an exact or minimal critical set for `T_ε X`, beyond the
admissible shifted set of `reeb-thickening-constructible.md`; any new interleaving distance;
ordered-space or Reeb-ordering results; universes other than `0`.

The statements of Theorems 3.17 and 4.24, Observation 4.23, Proposition 4.32, Observation 4.34 and Proposition 4.35
used here are those recorded, with their comparison against the HTML version of
arXiv:1501.04147v1, in `reeb-constructible-comparison.md`, `reeb-geometric-thickening.md` and
`reeb-rgraph-smoothing.md`.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §3.4, Theorem 3.17, §4.3, Observation
4.23, Theorems 4.24 and 4.27, and §4.4, Proposition 4.32, Observation 4.34 and Proposition
4.35](https://arxiv.org/html/1501.04147v1).
