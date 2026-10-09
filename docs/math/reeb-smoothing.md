# Smoothing of interval precosheaves and interleavings

## Precosheaves and the target category

A precosheaf on the interval category is a functor `F : OpenInterval ⥤ C`. The target `C` is an
arbitrary category, with universe parameters `C : Type u` and `[Category.{v} C]`. The
`Set`-valued pre-cosheaves of de Silva, Munch and Patel are the case `C := Type u`. Every
statement below specialises to that case without added hypotheses, and no proof uses a property
of `Type`. Allowing a general target is a choice of the library.

## Smoothing

For `ε : ℝ≥0`, the smoothing endofunctor precomposes with thickening:

```lean
(smoothing ε).obj F = thickenFunctor ε ⋙ F
(smoothing ε).map α = Functor.whiskerLeft (thickenFunctor ε) α
```

Both equations hold by `rfl`, and `smoothing ε` is definitionally
`(whiskeringLeft _ _ C).obj (thickenFunctor ε)`. It is reducible and given by components, so
`((smoothing ε).obj F).obj I` reduces to `F.obj (thicken ε I)`.

The structure maps are:

- `smoothingUnit ε : 𝟭 ⟶ smoothing ε`, whose component at `F` and `I` is `F` applied to
  `I ⊆ thicken ε I`;
- `smoothingMap h : smoothing ε ⟶ smoothing δ` for `h : ε ≤ δ`, from `thickenMap h`;
- `smoothingZeroIso : smoothing 0 ≅ 𝟭`, from `thickenZeroIso`;
- `smoothingCompIso ε δ : smoothing δ ⋙ smoothing ε ≅ smoothing (ε + δ)`, from
  `thickenCompIso ε δ`. Its component at `F` is
  `(thickenFunctor ε ⋙ thickenFunctor δ) ⋙ F ≅ thickenFunctor (ε + δ) ⋙ F`, so `S_ε (S_δ F)`
  thickens by `ε` first;
- `smoothingCommIso ε δ : smoothing ε ⋙ smoothing δ ≅ smoothing δ ⋙ smoothing ε`, built from the
  two composition isomorphisms and `ε + δ = δ + ε`;
- `smoothingObjBotIso ε F : ((smoothing ε).obj F).obj ⊥ ≅ F.obj ⊥`, the image under `F` of
  `thicken ε ⊥ = ⊥`. It is an isomorphism, not an equality, because `thicken ε ⊥` is only
  propositionally equal to `⊥`.

The coherence laws are equations of natural transformations: `smoothingMap` preserves
identities and composition, the unit is compatible with enlargement, the zero unit is the
inverse of `smoothingZeroIso`, both composites `F ⟶ S_ε S_δ F ≅ S_(ε+δ) F` of two units are the
`ε + δ` unit, the two composites `S_ε S_δ S_γ F ⟶ S_((ε+δ)+γ) F` agree (sum associativity), and
`smoothingCompIso` is unital on both sides.

All of these follow from thinness of the interval category: a functor out of it sends parallel
morphisms to equal maps (`map_eq_map_of_interval`, `map_comp_map_of_interval`). The tactic
`interval_coherence` closes equations between composites of such images. It is a scoped macro,
available after `open TDA.Reeb`.

## Interleavings

An `ε`-interleaving of `F` and `G` is a structure `Interleaving ε F G` with fields

```lean
φ : F ⟶ (smoothing ε).obj G
ψ : G ⟶ (smoothing ε).obj F
φ_ψ : φ ≫ (smoothing ε).map ψ ≫ (smoothingCompIso ε ε).hom.app F = (smoothingUnit (ε + ε)).app F
ψ_φ : ψ ≫ (smoothing ε).map φ ≫ (smoothingCompIso ε ε).hom.app G = (smoothingUnit (ε + ε)).app G
```

The fields are equations of natural transformations, and `2ε` is written `ε + ε`. The
objectwise triangles `ψ_(T_ε I) ∘ φ_I = F[I ⊆ T_ε T_ε I]` and their mirror image are
`φ_ψ_app` and `ψ_φ_app`, and `ofApp` builds an interleaving from them. `Interleaving ε F G` is
data, not a proposition; `Nonempty (Interleaving ε F G)` is the existence statement.

The proved laws are:

- symmetry (`symm`), and identity witnesses at every parameter (`refl`, given by the units);
- enlargement (`mono`): an `ε`-interleaving is an `ε'`-interleaving for `ε ≤ ε'`;
- composition (`trans`): an `ε`-interleaving of `F, G` and a `δ`-interleaving of `G, H` give an
  `(ε + δ)`-interleaving of `F, H`;
- zero parameter (`ofIso`, `toIso`, `zeroEquivIso`): `0`-interleavings are equivalent to natural
  isomorphisms, `Interleaving 0 F G ≃ (F ≅ G)`, with both round trips proved;
- smoothing (`smooth`): `S_ε` carries a `δ`-interleaving of `F, G` to a `δ`-interleaving of
  `S_ε F, S_ε G`;
- self-smoothing (`selfSmoothing`): `F` is `ε`-interleaved with `S_ε F`, with `φ` the composite
  of two units and `ψ` the identity.

In `trans` the forward map is `F(I) → G(T_ε I) → H(T_δ T_ε I)`. The reverse map is
`H(I) → G(T_δ I) → F(T_ε T_δ I)`, followed by the identification with `F(T_(ε+δ) I)`.

No interleaving distance is defined here. The fixtures show why a zero interleaving parameter
must be kept apart from a zero infimum: `I ↦ {0 ∈ I}` and `I ↦ {0 ∈ closure I}` are
`ε`-interleaved for every `ε > 0` but are not `0`-interleaved, since they differ on `(0, 1)`.
The point precosheaves at `0` and `1` are `1`-interleaved and not `0`-interleaved.

## Source correspondence

de Silva, Munch and Patel work with pre-cosheaves `Int → Set` on nonempty bounded open
intervals (*Categorified Reeb Graphs*, §4.1–4.2).

- Definition 4.1 gives an `ε`-interleaving as natural families `φ_I : F(I) → G(I^ε)` and
  `ψ_I : G(I) → F(I^ε)` with `ψ_(I^ε) ∘ φ_I = F[I ⊆ I^(2ε)]` and the mirror equation, and notes
  that at `ε = 0` this is an isomorphism. Observations 4.10 and 4.12 restate it as natural
  transformations `φ : F ⇒ GΩ_ε`, `ψ : G ⇒ FΩ_ε` with `(ψΩ_ε) ∘ φ = σ^(2ε)_F` and
  `(φΩ_ε) ∘ ψ = σ^(2ε)_G`, using `Ω_εΩ_ε = Ω_(2ε)` implicitly. The structure fields are this
  form, with that identification made explicit as `smoothingCompIso ε ε`.
- Observations 4.11 and 4.15 give the unit `σ^ε_F = Fω^ε`, which is `smoothingUnit`.
- Definition 4.14 defines `S_ε` as precomposition with `Ω_ε`, with `S_ε[φ] = φΩ_ε`. This is
  `smoothing`, with `thickenFunctor ε` as `Ω_ε`.
- Proposition 4.16 states `Ω_(ε₁+ε₂) = Ω_(ε₂)Ω_(ε₁)`, hence `S_(ε₁+ε₂) = S_(ε₁)S_(ε₂)`. In the
  library these are isomorphisms (`thickenCompIso`, `smoothingCompIso`) in the same order, with
  their coherence proved.
- Proposition 4.5 states that the interleaving distance is an extended pseudometric. Its proof
  composes interleavings. The displayed reverse map `ψ³_I = ϕ¹_(I^ε₂) ∘ ψ²_I` is a misprint:
  `ψ²_I` lands in `G(I^ε₂)`, and the map out of `G(I^ε₂)` towards `F` is `ψ¹_(I^ε₂)`, giving
  `ψ³_I = ψ¹_(I^ε₂) ∘ ψ²_I`. `trans` uses the corrected map. `symm`, `refl` and `trans` are the
  witness-level content of symmetry, `d(F, F) = 0` and the triangle inequality.
- Proposition 4.17 states that smoothing does not increase interleaving distance. Its proof
  takes `φΩ_ε, ψΩ_ε` as the new witnesses. Their codomain is `GΩ_δΩ_ε`, while
  `S_δ(S_ε G) = GΩ_εΩ_δ`; the source identifies the two because both equal `Ω_(ε+δ)`. In the
  library `thicken ε (thicken δ I)` and `thicken δ (thicken ε I)` are equal but not
  definitionally, so `smooth` composes with `smoothingCommIso`.

Admitting `∅`, rays and `ℝ` as intervals, taking `ε : ℝ≥0`, and allowing an arbitrary target
category are choices of the library. Self-smoothing, the composition and commutation
isomorphisms, and the coherence laws are stated in the source only implicitly or not at all.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147).
