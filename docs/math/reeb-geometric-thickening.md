# Geometric thickening and its component comparison

## Setting

For a space `X` with continuous height `f : C(X, ℝ)`, `C_f = intervalComponents f` sends an open
interval `I` to the path components of `f ⁻¹ I`, with paths inside the inverse image (see
`reeb-components.md`). For `ε : ℝ≥0`, `thicken ε I = I + [-ε, ε]` is the interval thickening of
`reeb-intervals.md`, with `thicken 0 I = I` and `thicken ε ⊥ = ⊥`, and `smoothing ε` is the
smoothing endofunctor of `reeb-smoothing.md`, so `((smoothing ε).obj C_f).obj I` is the set of path
components of `f ⁻¹ (thicken ε I)`. Interval thickening is the expansion `Ω_ε` of open intervals;
this digest is about the thickening `T_ε` of spaces over `ℝ`.

For a continuous `h : C(X, Z)` with `g ∘ h = f`, `intervalComponentNatTrans h comm : C_f ⟶ C_g`
sends the class of `x` to the class of `h x` (see `reeb-constructible-comparison.md`). The interval
component functor `intervalComponentsOver` on the real slice `Over (TopCat.of ℝ)` acts on objects by
`C` of the structure map and on morphisms by `intervalComponentNatTrans` (see
`reeb-rgraph-cosheaf-equivalence.md`).

## The thickened space

```lean
Band ε = Set.Icc (-ε) ε
height f ε : C(X × Band ε, ℝ),       height f ε (x, t) = f x + t
map g ε : C(X × Band ε, Y × Band ε),  map g ε (x, t) = (g x, t)
zeroSection X ε : C(X, X × Band ε),   zeroSection X ε x = (x, 0)
```

`Band ε` carries the subspace topology of `ℝ`; it is an abbreviation, so `Set.projIcc` and the
convexity of `Set.Icc` apply to it directly.

- `map g ε` is defined for every continuous `g`. When `h ∘ g = f` it preserves height
  (`height_map`), and `map_id` and `map_comp` hold by `rfl`.
- The zero section does not depend on a height. It preserves height (`height_zeroSection`) and is
  natural on points (`map_comp_zeroSection`).
- For `ε ≤ δ`, band enlargement `bandInclusion X hεδ : X × Band ε → X × Band δ` is the identity on
  coordinates and preserves height (`height_bandInclusion`).
- `bandHomeomorph f ε : X × Band ε ≃ₜ {(x, u) : X × ℝ | u - ε ≤ f x ∧ f x ≤ u + ε}` sends `(x, t)`
  to `(x, f x + t)`, with inverse `(x, u) ↦ (x, u - f x)` (`coe_bandHomeomorph_apply`,
  `bandHomeomorph_symm_apply`). The thickened height becomes the second coordinate
  (`snd_bandHomeomorph`).

## Inverse images

For an open interval `I`, write `A(I) = {(x, t) | f x + t ∈ I}` for the inverse image under the
thickened height and `B(I) = {x | f x ∈ thicken ε I}`. The first projection

```lean
preimageProjection f ε I : C(A(I), B(I)),   (x, t) ↦ x
```

is well defined: `y = f x + t ∈ I` satisfies `|f x - y| = |t| ≤ ε` (`fst_mem_thicken`). For
`ε > 0` the first projection does not preserve height in general: it sends a point of height
`f x + t` to one of height `f x`. Only at `ε = 0`, where `t = 0`, is it height-preserving (`zeroHomeomorph` below).

**The clamp.** For `c, s : ℝ`, `clamp ε c s = max (-ε) (min ε (c - s))` lies in the band; it is
`Set.projIcc (-ε) ε _ (c - s)` and is continuous in `s`. If `c ∈ I` and `s ∈ thicken ε I`, pick
`y ∈ I` with `|s - y| ≤ ε`. Then `s + clamp ε c s` lies between `c` and `y`:

- if `c - s` lies in the band, it is `c`;
- if `c - s > ε`, it is `s + ε`, and `y ≤ s + ε < c`;
- if `c - s < -ε`, it is `s - ε`, and `c < s - ε ≤ y`.

Since `I` is order-connected, `s + clamp ε c s ∈ I` (`add_clamp_mem`). The argument uses no
positive radius and no finite endpoint: it holds for every open interval, including rays and `ℝ`,
and for `ε = 0`.

**The homotopy equivalence.** Let `c` be a point that lies in `I` whenever `I` is nonempty. The
section `q(x) = (x, clamp ε c (f x))` maps `B(I)` into `A(I)`, because `B(I)` is empty unless `I` is
nonempty (`nonempty_of_mem_thicken`). Then `p ∘ q = id` exactly
(`preimageProjection_comp_preimageSectionAt`), and

```text
H(r, (x, t)) = (x, (1 - r) · clamp ε c (f x) + r · t),   r ∈ [0, 1]
```

is a homotopy from `q ∘ p` to the identity of `A(I)` (`preimageHomotopyAt`). With
`λ = clamp ε c (f x)`, the band is convex, and
`f x + ((1 - r) λ + r t) = (1 - r)(f x + λ) + r (f x + t)` is a convex combination of two points of
`I` (`interp_mem_band`, `interp_mem`). This gives `preimageHomotopyEquivAt`.

`preimageHomotopyEquiv f ε I` uses `c = intervalCenter I`, a chosen point of `I` when `I` is
nonempty (`intervalCenter_mem`), so it exists for every open interval `I`, including `⊥`, and every
`ε ≥ 0`, with no hypothesis on `X`, which may be empty. Its forward map is the projection itself,
by `rfl` (`preimageHomotopyEquiv_toFun`, `coe_preimageHomotopyEquiv_apply`). The section, the
point `c` and the homotopy are choices; only the forward map is part of the interface.

The projection is natural on points in two ways, both by `rfl`:

- for `I ≤ J`, it commutes with the inclusions `A(I) ⊆ A(J)` and `B(I) ⊆ B(J)`
  (`preimageProjection_comp_inclusion`);
- for `g : X → Y` with `h ∘ g = f`, it commutes with `map g ε` on `A(I)` and with `g` on `B(I)`
  (`preimageProjection_comp_restrict`).

## The comparison

```lean
componentComparison f ε : intervalComponents (height f ε) ⟶ (smoothing ε).obj (intervalComponents f)
(componentComparison f ε).app I = π₀ (preimageProjection f ε I)
```

On representatives it sends the class of `(x, t)` to the class of `x`
(`componentComparison_app_mk`). Naturality in the interval (`componentComparison_naturality`) is
`π₀` of the first square above. At every `I`, its component is the forward map of the
path-component bijection `componentEquivOfHomotopyEquiv` of the homotopy equivalence
(`componentComparison_app_eq_componentEquiv`), so it is bijective
(`componentComparison_app_bijective`). The instance `isIso_componentComparison` follows, and
`componentComparisonIso f ε` is `asIso` of the comparison, with hom the comparison itself
(`componentComparisonIso_hom`).

Three equations of natural transformations hold, each by evaluation on representatives:

- **Naturality in maps.** For `g : X → Y` with `h ∘ g = f`,
  `intervalComponentNatTrans (map g ε) _ ≫ componentComparison h ε =
  componentComparison f ε ≫ (smoothing ε).map (intervalComponentNatTrans g comm)`
  (`componentComparison_natural`).
- **Unit.** `intervalComponentNatTrans (zeroSection X ε) _ ≫ componentComparison f ε =
  (smoothingUnit ε).app (intervalComponents f)` (`zeroSection_comp_componentComparison`). On
  representatives, the class of `(x, 0)` goes to the class of `x` in `f ⁻¹ (thicken ε I)`, which is
  the smoothing unit of the class of `x` (`componentComparison_app_zeroSection_mk`). The reason is
  that `p ∘ τ^ε` is the inclusion `f ⁻¹ I ⊆ f ⁻¹ (thicken ε I)` on points.
- **Band enlargement.** For `ε ≤ δ`,
  `intervalComponentNatTrans (bandInclusion X hεδ) _ ≫ componentComparison f δ =
  componentComparison f ε ≫ (smoothingMap hεδ).app (intervalComponents f)`
  (`bandInclusion_comp_componentComparison`).

## The real slice

```lean
functor ε : Over (TopCat.of ℝ) ⥤ Over (TopCat.of ℝ)
zeroSectionNatTrans ε : 𝟭 _ ⟶ functor ε
zeroIso : functor 0 ≅ 𝟭 _
componentComparisonNatIso ε : functor ε ⋙ intervalComponentsOver ≅ intervalComponentsOver ⋙ smoothing ε
```

`functor ε` sends `A` to `A.left × Band ε` with height `height (overBaseMap A) ε`
(`overBaseMap_functor_obj`) and a slice morphism `φ` to `map φ.left.hom ε`
(`functor_map_left_hom`). It acts on every morphism of the slice, that is, on every continuous
height-preserving map. The zero section is a natural transformation `𝟭 ⟶ functor ε`
(`zeroSectionNatTrans_app_left_hom`).

At `ε = 0` the band is `{0}` (`eq_zero_of_mem_band_zero`), and the first projection
`zeroHomeomorph X : X × Band 0 ≃ₜ X` is a homeomorphism with inverse the zero section
(`zeroHomeomorph_apply`, `zeroHomeomorph_symm_apply`). It preserves height:
`f (zeroHomeomorph X z) = height f 0 z` (`apply_zeroHomeomorph`). `zeroIso` has the zero
homeomorphisms as components over `ℝ` (`zeroIso_hom_app_left_hom`) and the zero section as inverse
(`zeroIso_inv`, `zeroIso_inv_app_left_hom`).

`componentComparisonNatIso ε` has component `componentComparison (overBaseMap A) ε` at `A`
(`componentComparisonNatIso_hom_app`), so it reuses `intervalComponentsOver` and the unbundled
comparison. On the slice:

- the unit equation holds objectwise,
  `intervalComponentsOver.map ((zeroSectionNatTrans ε).app A) ≫ (componentComparisonNatIso ε).hom.app A
  = (smoothingUnit ε).app (intervalComponentsOver.obj A)`
  (`map_zeroSectionNatTrans_comp_componentComparisonNatIso`);
- and as natural transformations `𝒞 ⟶ 𝒞 ⋙ S_ε`,
  `whiskerRight (zeroSectionNatTrans ε) intervalComponentsOver ≫ (componentComparisonNatIso ε).hom
  = whiskerLeft intervalComponentsOver (smoothingUnit ε)`
  (`whiskerRight_zeroSectionNatTrans_comp_componentComparisonNatIso`), with no unitors, since
  `𝟭 ⋙ 𝒞` and `𝒞 ⋙ 𝟭` are definitionally `𝒞`;
- at `ε = 0`, `π₀` of `zeroIso` is the comparison followed by `smoothingZeroIso`
  (`map_zeroIso_hom_app`).

For `ε > 0` the first projection does not preserve height in general and is never packaged as a
slice morphism; at `ε = 0` it is the height-preserving `zeroHomeomorph` underlying `zeroIso`.

## Names and universes

`height`, `map`, `map_id`, `map_comp`, `componentComparison` and its `_app_mk`, `_natural` and
`_naturality` lemmas share their short names with declarations in `ReebQuotient` or
`CylinderPresentation`. When one of those namespaces is also open, refer to these declarations by
qualified name, for example `GeometricThickening.height`.

The unbundled statements hold at an arbitrary carrier universe `u`, with interval components at
value universe `u`. `map`, `height_map`, `map_id` and `map_comp` allow independent carrier
universes; statements through `componentNatTrans`, `preimageRestrict` or
`intervalComponentNatTrans` put both spaces in one universe, as those declarations require. The
slice packaging is in universe `0`, as `intervalComponentsOver` is.

## Fixtures

`TDA.Reeb.GeometricThickeningExamples` works with the comparison into the smoothing:

- **Every kind of open interval.** For arbitrary `X` and `f`, both inverse images are empty at `⊥`
  (`bot_isEmpty`), and the comparison is bijective at `⊥`, `ioo a b`, `ioi a`, `iio b` and `⊤`.
- **`ε = 0`.** The clamp is `0` (`clamp_zero`), clamp membership holds for an arbitrary interval
  (`add_clamp_mem_zero`), and the comparison is bijective (`bijective_zero`).
- **Empty space.** At every universe, both sides are empty (`empty_isEmpty`) and the comparison is
  bijective (`empty_bijective`).
- **Constant height on a point.** The thickened point `(*, 1)` has height `1`, while the projected
  point has height `0` (`point_projection_not_height_preserving`).
- **Constant height on `[0, 1]`.** At `ε = 1` and `I = ℝ` the first projection is not injective
  (`interval_projection_not_injective`), while the comparison is bijective
  (`interval_bijective_top`).
- **Collapse.** `Bool → PUnit` over height `0` is a noninjective height-preserving map. Both
  composites of its component square send the class of `(true, 0)` to the class of the point, by
  evaluation and from the general theorem (`collapse_square_mk`, `collapse_square`). The target is
  a single class, so this square alone cannot detect a wrong map.
- **Exchange.** `Bool.not` over height `0` (`swapB`). Both composites of its component square send
  the class of `(true, 0)` at `⊤` to the class of `false` (`swap_square_mk`, `swap_square`), and the
  classes of `false` and `true` differ (`swap_target_distinct`).
- **Reparametrization.** `bandHomeomorph` sends `(true, 0)` to `(true, 0)` over height `0`
  (`bandHomeomorph_point`).

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.3 and §4.4:

- **Definition 4.22** sets `X_ε = X × [-ε, ε]`, `f_ε(x, t) = f(x) + t` and
  `T_ε[α](x, t) = (α(x), t)`; these are `Band`, `height`, `map` and `functor`. The definition
  writes `T_ε[α] : (X_ε, f_ε) → (Y_ε, f_ε)` for `α : (X, f) → (Y, g)`; the target height must be
  `g_ε`, which is `height_map`.
- **Observation 4.23**, the natural zero section `τ^ε`, is `zeroSection`, `map_comp_zeroSection`
  and `zeroSectionNatTrans`.
- **Lemma 4.25** states that the first projection restricts to a homotopy equivalence
  `f_ε⁻¹(I) → f⁻¹(I^ε)` for each interval `I`. Its proof writes `I = (a, b)` and gives `λ` as an
  example inside an open parallelogram, whose interior is empty at `ε = 0`. The proof only needs
  `λ(s) ∈ [-ε, ε]` and `s + λ(s) ∈ I`; the clamp meets both conditions for every open interval,
  including `∅`, rays and `ℝ`, and for every `ε ≥ 0`. The homotopy is the source's straight line in
  `t`; convexity of the band and of `I` replaces "meets each fiber in an interval". The source does
  not discuss empty `I`, which needs no separate case here.
- **Theorem 4.24** states `𝒞T_ε ≅ S_ε𝒞`. Its proof sets `(ρ_f)_I = π₀[p_I]`, which is
  `componentComparison_app`, and checks naturality in `I` and in `α` by two squares of spaces,
  which are `preimageProjection_comp_inclusion` and `preimageProjection_comp_restrict`.
  `componentComparisonNatIso` is the theorem on the real slice.
- **The proof of Theorem 4.27** (Figure 8) reparametrizes `X_ε` as
  `X̃_ε = {(x, u) ∈ X × ℝ | u - ε ≤ f(x) ≤ u + ε}` with height `u`; this is `bandHomeomorph`.
- **Proposition 4.35** (§4.4) is stated for ℝ-graphs, with `U_ε = ℛT_ε`, the transformation `ζ`
  given by the zero section followed by the Reeb quotient, and the isomorphism of Proposition 4.32,
  which composes Theorems 3.17 and 4.24. Its proof evaluates at `I` and reduces to a square of
  spaces with three maps: the zero section `L` into `f_ε⁻¹(I)`, the inclusion
  `R : f⁻¹(I) ⊆ f⁻¹(I^ε)`, and the homotopy inverse `H` of Lemma 4.25. It shows that `L` and `HR`
  are homotopic by a fiberwise straight-line homotopy. With the projection `p` in place of `H`, the
  square `p ∘ L = R` holds on points, since `p(x, 0) = x`, so the corresponding equation of `π₀`
  maps holds exactly on representatives, with no homotopy. That equation is the unit equation
  above, the part of the square of Proposition 4.35 that involves `T_ε` and Theorem 4.24; it holds
  for every space over `ℝ`.

Not claimed here: that the first projection is a map over `ℝ` or a slice morphism for `ε > 0`;
naturality of the homotopy inverse, of the chosen point or of the homotopy in `I` or in maps; Reeb
graphs of thickenings, or Proposition 4.35 for ℝ-graphs. Constructibility of the thickenings of
ℝ-graphs (Proposition 4.26), by the rest of the proof of Theorem 4.27 on graph input, is in
`reeb-rgraph-thickening.md`, and Theorem 4.27 for all constructible ℝ-spaces is in
`reeb-thickening-constructible.md`, with `componentComparisonNatIso` lifted to constructible ℝ-spaces
and cosheaves in `reeb-thickening-cosheaf-comparison.md`; the geometric smoothing `U_ε = ℛT_ε` of ℝ-graphs, with Proposition
4.35 for ℝ-graphs, is in `reeb-rgraph-smoothing.md`. The addition map `T_ε T_δ → T_(ε+δ)`, its lax
coherence and the failure of `T_ε T_δ ≅ T_(ε+δ)` on a point are in
`reeb-geometric-thickening-addition.md`.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.3, Definition 4.22, Observation
4.23, Theorem 4.24, Lemma 4.25 and the proof of Theorem 4.27, and §4.4, Proposition
4.35](https://arxiv.org/html/1501.04147v1).
