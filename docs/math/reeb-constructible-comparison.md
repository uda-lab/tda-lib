# The comparison on constructible inputs

## Setting

Levels are `S : CriticalValues n` with `a 0 < ⋯ < a n`, stars `J i` and gaps `K e` (see
`reeb-constructible-cosheaf.md`). A presentation `P : CylinderPresentation n` has vertex pieces
`V i`, edge pieces `E e` and continuous endpoint maps. Its realization is `X = P.Realization S` with
height `h = P.height S` (see `reeb-constructible-space.md`). The Reeb quotient is
`Q = ReebQuotient h` with projection `q` and descended height `h̄`. `G` is the finite realization of
the component data `P.componentData`, whose vertex and edge sets `π₀ (V i)` and `π₀ (E e)` carry
the discrete topology. The maps `Φ = componentGraphMap : X → G` and
`θ = quotientComponentGraphMap : Q → G` satisfy `θ ∘ q = Φ` by definition (see
`reeb-constructible-quotient.md`).

For `f : C(Y, ℝ)`, `C_f = intervalComponents f` sends an open interval `I` to the path components
of `f ⁻¹ I`, with paths inside the inverse image. The comparison
`η_f = ReebQuotient.componentComparison f` of `reeb-quotient-comparison.md` is defined on all open
sets of `ℝ`.

## The map on open intervals

```text
ReebQuotient.intervalComponentComparison f : intervalComponents f ⟶ intervalComponents (height f)
```

is `componentComparison f` precomposed with `OpenInterval.toOpensFunctor`. It sends the path
component of `x` in `f ⁻¹ I` to the path component of `q x` in `f̄ ⁻¹ I`
(`intervalComponentComparison_app_mk`). Its identity with `componentComparison f` holds by `rfl`,
as transformations and at each interval (`intervalComponentComparison_eq`,
`intervalComponentComparison_app`), so no other bijection is introduced. It is surjective at every
interval (`intervalComponentComparison_app_surjective`).

`intervalComponentNatTrans h comm : intervalComponents f ⟶ intervalComponents g` is
`componentNatTrans h comm` precomposed with `toOpensFunctor`, for a continuous `h` with
`g ∘ h = f`. The interval component functor `intervalComponentsOver` of
`reeb-rgraph-cosheaf-equivalence.md` acts on a slice morphism `φ` by
`intervalComponentNatTrans φ.left.hom _` (`intervalComponentsOver_map_eq_intervalComponentNatTrans`,
by `rfl`). Naturality in height-preserving maps is `componentComparison_natural`, precomposed:

```text
intervalComponentNatTrans h comm ≫ η_g = η_f ≫ intervalComponentNatTrans (ReebQuotient.map h comm) _
```

(`intervalComponentComparison_natural`). When both comparisons are isomorphisms, the inverses
satisfy the reversed square (`inv_intervalComponentComparison_natural`).

On the real slice, the comparison at `A` is the path-component map of the projection `ρ_A`
(`componentComparisonOver_app_eq_map`, the source's `η = 𝒞ρ`). Precomposed with `toOpensFunctor`,

```text
ReebQuotient.intervalComponentComparisonOver :
    intervalComponentsOver ⟶ quotientFunctor ℝ ⋙ intervalComponentsOver
```

has as component at `A` the comparison of the structure map of `A`
(`intervalComponentComparisonOver_app`).

## Presentations

Assume that every piece of `P` is locally path-connected and has finitely many path components.
Compactness is not assumed. Nothing is assumed of Hausdorffness or of the endpoint maps.

1. **Factorization.** From `θ ∘ q = Φ`, `π₀(θ) ∘ η = π₀(Φ)` at every interval
   (`intervalComponentComparison_comp`, `intervalComponentComparison_comp_apply`).
2. **`π₀(Φ)` is a natural isomorphism.** Both `C_h` and the path-component cosheaf of `G` are
   constructible at `S` and interval cosheaves. At a star, `π₀(Φ)` carries the component bijection
   of `P` to that of `G`, precomposed with `c ↦ [c]` on the discrete vertex set of `G`
   (`componentGraphMap_star`), and likewise at a gap (`componentGraphMap_gap`). All three maps are
   bijections, so every star and gap component of `π₀(Φ)` is bijective. The short-interval test
   `CriticalValues.isIso_iff_shortIntervals` then gives an isomorphism on all intervals
   (`isIso_intervalComponentNatTrans_componentGraphMap`).
3. **Bijectivity.** At every open interval, including `⊥`, rays and `⊤`, `η_h` is injective because
   `π₀(θ) ∘ η_h = π₀(Φ)` is injective, and surjective by
   `intervalComponentComparison_app_surjective` (`bijective_intervalComponentComparison_app`).
4. **Isomorphism.** `η_h` is a natural isomorphism (the instance
   `CylinderPresentation.isIso_intervalComponentComparison`, and `intervalComponentComparisonIso`
   with hom the comparison by `intervalComponentComparisonIso_hom`).

Consequences: `C_{h̄}` is constructible at the same `S`
(`isConstructibleAt_intervalComponents_reebQuotient`), and `π₀(θ)` is a natural isomorphism
(`isIso_intervalComponentNatTrans_quotientComponentGraphMap`). At stars and gaps, `π₀(θ) ∘ η` is
the map taking each piece to its set of path components, read through the component bijections of
`P` and of `G` (`intervalComponentComparison_star`, `intervalComponentComparison_gap`). No lifting
of paths along general quotient maps is used.

## Constructible ℝ-spaces

`IsConstructibleSpace A` holds when `A` is isomorphic in the real slice to a realization with
compact locally path-connected pieces, and `ConstructibleSpaceCat` is the full subcategory on these
objects, with all continuous height-preserving maps (see `reeb-constructible-quotient.md`).

- **Objectwise.** For constructible `A`, the comparison of the structure map of `A` is an
  isomorphism (`isIso_intervalComponentComparison_of_constructible`). The presentation result is
  transported along `A ≅ (X, h)` by naturality of `intervalComponentComparisonOver`, not along a
  chosen bijection. Finiteness of the component sets follows from compactness and local
  path-connectedness.
- **Common levels.** For constructible `A`, `C` of the structure map and `C` of its Reeb quotient
  are constructible at one common list of levels
  (`exists_isConstructibleAt_of_isConstructibleSpace`).
- **Graph objects.** On a graph object the comparison is an isomorphism by the projection
  isomorphism `RGraph.projNatIso` alone (`isIso_intervalComponentComparison_of_isRGraph`).
- **Functor level.** `constructibleComponentComparison` is `intervalComponentComparisonOver`
  restricted to `ConstructibleSpaceCat`. It is an isomorphism (the instance
  `isIso_constructibleComponentComparison`), giving

  ```text
  constructibleComponentComparisonIso :
      ι ⋙ intervalComponentsOver ≅ ι ⋙ quotientFunctor ℝ ⋙ intervalComponentsOver
  ```

  whose component at `A` is the comparison of the structure map of `A`
  (`constructibleComponentComparison_app`, `constructibleComponentComparisonIso_hom_app`, by
  `rfl`). Its square for every morphism `g` is `componentComparison_natural` precomposed
  (`constructibleComponentComparison_naturality`).
- **Constructible cosheaves.** `constructibleCosheafFunctor : ConstructibleSpaceCat ⥤
  ConstructibleCosheafCat.{0}` lifts `ι ⋙ intervalComponentsOver`. It lands in constructible
  cosheaves because the interval components of every space over `ℝ` form an interval cosheaf and
  those of a constructible ℝ-space are constructible. The comparison is a natural isomorphism

  ```text
  constructibleCosheafComparisonIso :
      constructibleCosheafFunctor ≅ quotientRGraphFunctor ⋙ RGraph.cosheafFunctor
  (constructibleCosheafComparisonIso.hom.app A).hom
      = ReebQuotient.intervalComponentComparison (overBaseMap A.obj)
  ```

  with `quotientRGraphFunctor` of `reeb-constructible-quotient.md` and `RGraph.cosheafFunctor` of
  `reeb-rgraph-cosheaf-equivalence.md`. The component identity holds by `rfl`
  (`constructibleCosheafComparisonIso_hom_app_hom`); with `intervalComponentComparison_eq`, every
  component is `componentComparison` of the structure map, precomposed with `toOpensFunctor`.

## The graph case

For finite data `D`, the comparison at the realization of `D` is the path-component map of the
projection homeomorphism `RGraph.projHomeomorph` of `reeb-rgraph.md`, by `rfl`
(`intervalComponentComparison_ofFiniteData`). Its inverse is the path-component map of the inverse
projection `RGraph.projInv` (`inv_intervalComponentComparison_ofFiniteData`, with
`height_projInv`). At a graph object, the component of `constructibleComponentComparisonIso` is the
image of `RGraph.projNatIso` under `intervalComponentsOver`
(`constructibleComponentComparisonIso_app_of_isRGraph`). At the thickening of a graph object, the
inverse of the comparison is the first factor of the comparison of geometric smoothing with cosheaf
smoothing (see `reeb-rgraph-smoothing.md`).

## Hypotheses and their limits

Every isomorphism statement carries the presentation hypotheses, `IsConstructibleSpace`, or a
graph-object or finite-data hypothesis, under which the presentation hypotheses hold.
The instances are keyed on the height of a presentation and on the functor-level transformation; no
instance gives `IsIso` of the comparison for an arbitrary map. For arbitrary maps only the defining
identities, surjectivity and naturality are stated.

Constructibility of the source cosheaf does not suffice, nor constructibility of both cosheaves at a
common list. Take the closed topologist's sine curve as the single compact vertex piece at the one
level of a one-level list. It has two path components, so its path-component cosheaf is
constructible at that list. With constant height, the Reeb quotient is the set of its two path
components with the quotient topology. The graph part is open and the limit segment is not, so the
quotient is the Sierpiński space, which is path-connected. The quotient cosheaf therefore has one
element on every interval containing the level and is constructible at the same list, while the
comparison over `ℝ` sends two elements to one. The piece is compact but not locally
path-connected. This variant of the source's Example 3.21 is not machine-checked.

The source's Example 3.21, the topologist's sine curve with the first-coordinate projection, is the
nonconstructible obstruction: there `𝒞(𝕊, x)` and `𝒞ℛ(𝕊, x)` are not isomorphic. The fixture
`Examples.TopologistsSineCurve.intervalComponentComparison_not_injective` proves that the
comparison is not injective at the interval `ℝ`; see `reeb-quotient-comparison.md`. That no
isomorphism exists between the two cosheaves is not formalized.

## Universes

`intervalComponentNatTrans`, the comparison on open intervals with its formulas, surjectivity and
naturality, and all presentation results hold in every carrier universe. The slice, the full
subcategory of constructible ℝ-spaces and the functor-level isomorphisms are in universe `0`,
matching `Over (TopCat.of ℝ)`; the constructible-cosheaf form is at value universe `0`.

## Fixtures

`TDA.Reeb.ConstructibleComparisonExamples` works with the comparison on presentations, built from the constructible-space, cylinder, finite-graph and quotient fixtures:

- **Constant-height interval.** For `[0, 1]` at one level, `q` is not injective
  (`interval_proj_not_injective`), while the comparison is an isomorphism (`interval_isIso`) with
  one element on each side over `ℝ`.
- **`∅`, rays and `ℝ`.** For two unattached pieces at level `0`, the quotient cosheaf has two
  elements over `ℝ` and over the rays `(-∞, 1)` and `(-1, ∞)`, and is empty over `(-∞, 0)` and
  `(0, ∞)`. At `⊥` both values are empty and the comparison is bijective (`twoPieces_bot`).
- **Empty space.** For the thickening of empty data, the comparison is an isomorphism and every
  quotient value is empty.
- **Branch and merge.** The thickened cycle over `0 < 1 < 2` is a constructible ℝ-space with one
  vertex at `0`, two at `1`, one at `2` and two edges per gap. Its end stars are the rays `(-∞, 1)`
  and `(1, ∞)`. The quotient counts are `1, 2, 1` on the stars and `2` on each gap, and the
  quotient's incidence maps into the bottom and top stars are not injective.
- **Branching at equal cardinality.** For the thickened pinch, the counts at the bottom star and the
  gap are both `2`, and the gap-to-star map is not injective in the source, through the bottom gluing, and in the quotient, through the comparison.
- **Graph case.** For parallel edges over `0 < 1`, the comparison and its inverse are the
  path-component maps of `RGraph.projHomeomorph` and `RGraph.projInv`, the functor-level component
  is the image of `RGraph.projNatIso`, and the two edges stay two components of the quotient over
  the gap.
- **Transport.** The single edge refined over `0 < 1/2 < 1` is constructible through the refinement
  isomorphism to the single edge over `0 < 1`, and the comparison there is an isomorphism.
- **Height-dependent map.** The twist of the thickened parallel edges swaps the two edge components
  over the gap in the source and, through the comparison, in the quotient. The naturality squares
  hold for the comparison, its inverse and, as a morphism of `ConstructibleSpaceCat`, the
  functor-level isomorphism.

The helpers `natCard_quotient` and `quotient_map_injective_iff` transfer cardinalities and
injectivity of structure maps between the source and quotient cosheaves of a presentation.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*:

- §3.4: `𝒞(f)(I) = π₀ f⁻¹(I)`, with `𝒞'` its restriction to ℝ-**Top**ᶜ and `𝒞''` its restriction to
  **Reeb**. Here `𝒞` is `intervalComponentsOver`, `𝒞'` is `constructibleCosheafFunctor` and `𝒞''`
  is `RGraph.cosheafFunctor`. The Reeb functor `ℛ` on ℝ-**Top**ᶜ is `quotientRGraphFunctor`.
- Theorem 3.17: the functors `𝒞'` and `𝒞''ℛ` from ℝ-**Top**ᶜ to **Csh**ᶜ are naturally isomorphic.
  Here this is `constructibleCosheafComparisonIso`, natural on all morphisms of
  `ConstructibleSpaceCat`. `constructibleComponentComparisonIso` is the same isomorphism between
  functors to precosheaves on open intervals.
- Proof of Theorem 3.17: the source defines `η = 𝒞ρ` on all of ℝ-**Top**
  (`componentComparisonOver_app_eq_map` on open sets; on open intervals it follows by precomposition
  with `toOpensFunctor`), notes that `𝒞(f)` and `𝒞ℛ(f)` are constructible with the
  same critical set, and checks short intervals by Corollary 3.14. At stars and gaps it applies
  `π₀` to the homotopy equivalences of the cylinder principle (Lemma 2.4) in the diagrams (2.6)
  for `ρ`.
  - Here Corollary 3.14 is applied to `π₀(Φ)` for `Φ = θ ∘ ρ`, whose source and target are
    realizations over `S`. A presentation of the quotient over `S` would need the homeomorphism of
    `reeb-constructible-quotient.md`, hence compactness, before `C_{h̄}` is known to be
    constructible.
  - Injectivity of `η` follows from the factorization through `π₀(θ)`, and surjectivity from
    `componentComparison_app_surjective`.
  - The isomorphism is proved, and so is the proof's intermediate claim that both cosheaves are
    constructible at a common list (`isConstructibleAt_intervalComponents_reebQuotient`,
    `exists_isConstructibleAt_of_isConstructibleSpace`). The star and gap formulas
    `intervalComponentComparison_star` and `intervalComponentComparison_gap` are the source's two
    diagrams composed with `π₀(θ)`.
- The presentation-level theorem assumes finitely many path components and local
  path-connectedness of every piece, without compactness. The source's class, compact and locally
  path-connected pieces, implies these hypotheses, and the slice-level theorems use exactly that
  class.
- Example 3.21: the topologist's sine curve, where `𝒞(𝕊, x)` and `𝒞ℛ(𝕊, x)` are not isomorphic.
  The comparison is not injective at `ℝ`
  (`Examples.TopologistsSineCurve.intervalComponentComparison_not_injective`).

Not claimed here: an isomorphism of `componentComparison` on all open sets of `ℝ`; invertibility of
the comparison for arbitrary maps or for nonconstructible spaces; the non-isomorphism of the two
cosheaves in Example 3.21 (only non-injectivity of the comparison at `ℝ` is proved) or the
constant-height sine-curve variant; the functor-level statements in universes other than
`0`.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §3.4, Theorem 3.17 and
Example 3.21](https://arxiv.org/html/1501.04147v1).
