# Local cylinder comparisons and constructibility of path components

## Setting

Levels are `S : CriticalValues n` with `a 0 < ⋯ < a n`, stars `J i = (a (i-1), a (i+1))` and gaps
`K e = (a e, a (e+1))`, with infinite ends at the extremes (see `reeb-constructible-cosheaf.md`).
A presentation `P : CylinderPresentation n` has arbitrary topological pieces `V i`, `E e` and
continuous endpoint maps (see `reeb-constructible-space.md`). Write `X = P.Realization S` and
`h = P.height S`.

For an open interval `W`, `P.heightPreimage S W` is the subspace `{x : X // h x ∈ W}`. Its path
components are `(intervalComponents h).obj W` by definition (`intervalComponents_obj_eq`, proved by
`rfl`). The fiber inclusions are

- `vertexFiberInclusion i : V i → heightPreimage (J i)`, `v ↦ ofVertex i v`;
- `regularFiberInclusion e t : E e → heightPreimage (K e)`, `y ↦ ofStrip e (y, t)` for a chosen
  `t ∈ K e`.

## The clamp homotopy

Clamp data `c : S.ClampData J` consist of `lo ≤ hi` with `[lo, hi] ⊆ J` such that every level
lying in `J` lies in `[lo, hi]`. Put `κ t = max lo (min hi t)` and `κ_s t = t + s (κ t − t)` for
`s ∈ [0, 1]`.

1. On raw pieces, a vertex point is fixed and a cylinder point `(y, t)` of edge `e` goes to
   `(y, projIcc (κ_s t))`. Curried per piece, this is a continuous map from the whole raw sum into
   `C([0,1], X)` (`continuous_clampRaw`).
2. It respects the endpoint relation over `J` (`clampRaw_nf`). An end of a cylinder whose level
   lies in `J` has its level in `[lo, hi]`, so `κ_s` fixes it and the end still goes to its vertex
   image. No injectivity, surjectivity or embedding property of the endpoint maps is used.
3. The quotient map restricted to the open saturated set `h⁻¹ J` is a quotient map. So the family
   descends to a continuous `clampFamily c : C(heightPreimage J, C([0,1], X))`. It uncurries to a
   jointly continuous map because `[0,1]` is locally compact.
4. Inside `J`, `κ t` stays in the segment of the edge (`clampHeight_mem_seg`): if `a (e+1) ∈ J`,
   it lies in `[lo, hi]`, so `lo ≤ a (e+1)`; if `a (e+1) ∉ J`, then `J` lies below `a (e+1)` and
   so does `lo`. The case of `a e` is symmetric. Hence the
   height of `clampFamily c u s` is `κ_s (h u)` (`height_clampFamily`), which lies between `h u`
   and `κ (h u) ∈ [lo, hi]`.
5. For every open interval `W` with `[lo, hi] ⊆ W ≤ J`, the family maps `heightPreimage W` into
   itself. It is a homotopy from the identity to the end map `u ↦ clampFamily c u 1`
   (`clampHomotopy`).

Continuity is inherited from the raw sum through the quotient map, so no separate argument is
needed at a critical level or at the boundary of a strip. The clamp homotopy is an ordinary
homotopy, not a homotopy over `ℝ`, because heights move.

## Homotopy equivalences

- **Vertex.** Take `J = J i` and `lo = hi = a i`. The end map lands in the critical fiber
  `h⁻¹{a i} ≅ V i` (`criticalFiberHomeomorph`). Reading it there gives a retraction whose
  composite with `vertexFiberInclusion i` is the identity on the nose. The other composite is the
  end map, homotopic to the identity. So `vertexHomotopyEquiv i : V i ≃ₕ heightPreimage (J i)`.
- **Regular gap.** Take `J = K e` and `lo = hi = t`; no level lies in `K e`. The end map lands in
  `h⁻¹{t} ≅ E e` (`regularFiberHomeomorph`), giving `regularHomotopyEquiv e t`.
- **Nested intervals.** Let `I ≤ J` with `I` nonempty and the same levels in `I` and `J`. Take
  `lo` and `hi` to be the minimum and maximum of one point of `I` together with the levels in `I`
  (`exists_clampData_of_le`). Then `[lo, hi] ⊆ I`, and every level of `J` lies in `[lo, hi]`. The
  end map is a map `heightPreimage J → heightPreimage I`, and both composites with the inclusion
  are end maps of the same homotopy restricted to `W = I` and `W = J`. So the inclusion is a
  homotopy equivalence (`nestedHomotopyEquiv`).

These need no hypothesis on the pieces. The forward map of each `HomotopyEquiv` is the inclusion; that is the interface. The homotopy inverses are chosen clamp retractions and are not
part of it. The construction shows that the inclusion `heightPreimage I → heightPreimage J` is a
homotopy equivalence; it does not exhibit `heightPreimage I` as a deformation retract, since the
clamp also moves points of `heightPreimage I`.

## Component bijections and incidence

Homotopic maps induce equal maps on path components (`componentMap_eq_of_homotopic`), so a
homotopy equivalence induces an equivalence on `ZerothHomotopy` (`componentEquivOfHomotopyEquiv`)
whose forward map is `componentMap` of the forward map. This gives

```text
vertexComponentsEquiv i  : ZerothHomotopy (V i) ≃ (intervalComponents h).obj (J i)
edgeComponentsEquiv e t  : ZerothHomotopy (E e) ≃ (intervalComponents h).obj (K e)
```

with generators sent to the classes of the inclusions (`vertexComponentsEquiv_mk`,
`edgeComponentsEquiv_mk`).

The cylinder line from `(y, t)` to `(y, a e)` stays in `J e.castSucc` (`joinedIn_cylinder`). So
the gap-to-star map carries the edge bijection to the left endpoint map:

```text
(intervalComponents h).map (K e ≤ J e.castSucc) ∘ edgeComponentsEquiv e t
  = vertexComponentsEquiv e.castSucc ∘ componentMap (left e)
```

(`map_K_le_J_castSucc_edgeComponentsEquiv`), and analogously through `J e.succ` with `right e`
(`map_K_le_J_succ_edgeComponentsEquiv`). The conjugated forms
`vertexComponentsEquiv_symm_map_castSucc` and `vertexComponentsEquiv_symm_map_succ` state
`componentMap (left e)` and `componentMap (right e)` as the conjugated functor maps. These
proofs use paths only, not retractions.

## Naturality

Let `P` and `P'` be presentations over the same `S`, and let `φ : P.Realization S →
P'.Realization S` be any continuous map with `P'.height S ∘ φ = P.height S`. No presentation map
is assumed; a height-preserving map may vary along a cylinder.

- `φ` restricts to fibers, defining `vertexFiberMap φ i : V i → V' i` and
  `regularFiberMap φ e t : E e → E' e` through the fiber homeomorphisms, with
  `map_ofVertex_eq` and `map_ofStrip_eq`.
- The fiber inclusions commute with `φ` on the nose (`vertexFiberInclusion_naturality`,
  `regularFiberInclusion_naturality`, stated with `preimageRestrict`).
- Hence the component bijections are natural for `componentNatTrans φ`
  (`componentNatTrans_vertexComponentsEquiv`, `componentNatTrans_edgeComponentsEquiv`) and for its
  restriction to open intervals (`whiskerLeft_componentNatTrans_vertexComponentsEquiv`,
  `whiskerLeft_componentNatTrans_edgeComponentsEquiv`).

The chosen retractions and homotopies are not claimed to commute with `φ`.

## Height independence on path components

The edge bijection does not depend on the regular height: `edgeComponentsEquiv e t =
edgeComponentsEquiv e t'` (`edgeComponentsEquiv_indep`), by the cylinder line inside `K e`.
Combined with naturality, `componentMap (regularFiberMap φ e t)` does not depend on `t`
(`componentMap_regularFiberMap_indep`).

Pointwise independence is false in general. Take `E e = V = S¹` with identity endpoint maps, and
let `φ` rotate the strip point at height `t` by an angle `θ(t)` vanishing at both levels. Then `φ`
is continuous and height-preserving, and `regularFiberMap φ e t` is rotation by `θ(t)`. When the
edge piece of the target is discrete, the path-component statement does give pointwise
independence (`regularFiberMap_indep_of_discrete`). For a realized map of finite data the regular
fiber map is the edge component of the data map at every height (`regularFiberMap_realizeHom`).

## Constructibility

`intervalComponents_isConstructibleAt` proves `S.IsConstructibleAt (intervalComponents h)` under
`Finite (ZerothHomotopy (P.V i))` and `Finite (ZerothHomotopy (P.E e))` for every piece. These are
its only hypotheses.

- **Finite values** (`finite_intervalComponents`). The empty interval has an empty value. For
  nonempty `I`, every point of `heightPreimage I` is joined inside it to one of two kinds of
  point: a vertex point at a level of `I`, along its cylinder line when an endpoint level of its
  edge lies in `I`; or the strip point at one fixed height of `I`, when `I` contains neither
  endpoint level, which forces `I ≤ K e`. This gives a surjection from the finite type
  `(Σ levels k in I, π₀ (V k)) ⊕ (Σ e with I ≤ K e, π₀ (E e))`. Compactness of an open inverse
  image is never used; it fails in general, since `h⁻¹(K e) ≅ E e × K e`.
- **Bijectivity** (`intervalComponents_map_bijective`). For nonempty `I ≤ J` with the same levels,
  the map `(intervalComponents h).map (homOfLE _)` equals the component bijection of
  `nestedHomotopyEquiv`.
- **Exterior values** are empty by `height_preimage_lowerTail` and `height_preimage_upperTail`.

Corollaries: compact locally path-connected pieces have finitely many path components, so they
suffice (`isConstructibleAt_of_compact_lpc`); realized finite data have discrete pieces, which are
their own path components (`finiteData_isConstructibleAt`).

The cosheaf condition is not reproved here: `intervalComponents_isIntervalCosheaf` gives it for
every continuous height.

## Fixtures

`TDA.Reeb.ConstructibleCylinderExamples` computes the `intervalComponents` of realized
finite data:

- `n = 0` with two vertices: the value on `ℝ` has two elements, and the inclusion of `(-1, 1)` into
  `ℝ` is bijective;
- a pinch over levels `0 < 1` whose two edges both start at vertex `0`, a noninjective left
  endpoint map: the gap and the ray star `J 0 = (-∞, 1)` have two components each, both branches
  map to vertex `0`, and the right incidence `K 0 ≤ J 1` sends edge `y` to vertex `y`;
- the proper inclusion `K 0 ≤ J 0` into the ray crosses the level `0`, outside the equal-level
  condition, and is not injective;
- the regular interval `(1/4, 3/4)` avoids every level, has a nonempty inverse image with two
  components, and its inclusion into the gap is bijective;
- empty values on the lower tail for `n = 0` and on `(2, 3)` above the pinch;
- height independence on the pinch: the realized data map reversing the edges has the same
  regular fiber map, the reversal, at `1/2` and `3/4`, and it is not the identity; the edge
  component bijections at the two heights agree;
- `n = 2` with levels `0 < 1 < 2`: in the bounded star `J 1 = (0, 2)` the lower edge arrives by
  right incidence at vertex `0` and the upper edge by left incidence at vertex `1`, in different
  components.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*:

- §2.2, Lemma 2.4 (cylinder principle): the fiber inclusions `𝕍ᵢ → f⁻¹(aᵢ₋₁, aᵢ₊₁)` and
  `𝔼ᵢ → f⁻¹(aᵢ, aᵢ₊₁)` at some `a ∈ (aᵢ, aᵢ₊₁)` are homotopy equivalences fitting into the
  incidence diagrams (2.5), which commute up to homotopy, and natural in the sense of (2.6). Here
  the homotopy equivalences are `vertexHomotopyEquiv` and `regularHomotopyEquiv`, for arbitrary
  pieces. The incidence diagrams are proved on path components
  (`map_K_le_J_castSucc_edgeComponentsEquiv`, `map_K_le_J_succ_edgeComponentsEquiv`), and the
  naturality as exact squares of the fiber inclusions
  (`vertexFiberInclusion_naturality`, `regularFiberInclusion_naturality`). The parenthesis of the
  lemma indexes the absent edge sets so that the first genuine edge set would be empty. Here the
  incident edges of level `i` are the `e` with `e.castSucc = i` or `e.succ = i`, and `n = 0` has
  no edge.
- §3.4, Proposition 3.16: the path-component cosheaf of a constructible ℝ-space is constructible
  with the same critical set. Here this is `intervalComponents_isConstructibleAt`, with finite
  piece component sets in place of compact locally path-connected pieces. As in the source proof,
  the nested inclusion with the same critical points is a homotopy equivalence
  (`nestedHomotopyEquiv`).

Not claimed here: naturality for height-preserving maps between realizations over different
critical lists, which needs a re-presentation over a common refinement; naturality of the chosen
retractions; pointwise height independence of `regularFiberMap` for general pieces; a deformation
retraction onto an open inverse image; the incidence diagrams up to homotopy at the level of
spaces.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/html/1501.04147v1).
