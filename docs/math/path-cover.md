# Path-local open-cover subdivision

## Statement

Let `X` be a topological space, `γ : Path x y` a path in `X`, and `U i` a family of open sets
of `X`, indexed by an arbitrary `Sort`, whose union contains the range of `γ`. Then there are
`n : ℕ`, a monotone `t : Fin (n + 1) → [0, 1]` with `t 0 = 0` and `t n = 1`, and an index
`i : Fin n → ι` such that `γ` maps each segment `[t k, t (k + 1)]` into `U (i k)`
(`TDA.Topology.exists_subdivision`). Derived forms:

- `exists_subpath_chain`: the restricted path `γ.subpath (t k) (t (k + 1))` has range in
  `U (i k)`;
- `exists_overlap_chain`: chain points `p 0 = x, …, p n = y` with consecutive points joined
  inside a single member, and each interior junction `p (k + 1)` in the overlap
  `U (i k) ∩ U (i (k + 1))`;
- `reflTransGen_of_path`: `x` and `y` are related by the reflexive-transitive closure of
  "joined inside a single member";
- `reflTransGen_of_joined`: the same conclusion from `Joined x y`, when the members cover the
  path component of `x`;
- `exists_subdivision_opens`: the `TopologicalSpace.Opens` form, with the range of `γ` inside
  an open `W` and `W ≤ ⨆ i, V i`. The openness of `W` is not used.
- `reflTransGen_preimage`: for `f : C(X, Y)` and opens `V i` covering `W`, a path inside the
  preimage subspace `f ⁻¹ W` gives a chain whose links are joined inside single preimage
  subspaces `f ⁻¹ (V i)`. `V i ≤ W` is not assumed.

## Conventions

Subdivision points may repeat. A degenerate segment `[t, t]` maps to the point `γ t`, which
lies in the selected member, and its subpath is the constant path; no strict monotonicity is
claimed or needed. The chain is indexed by `Fin (n + 1)`, the convention of mathlib's
`Path.concat`. Open members are essential: the singletons of `[0, 1]` cover the identity path,
but no finite monotone subdivision fits them. No local path connectedness, Hausdorffness,
compactness or nonemptiness of `X` is assumed, and empty or duplicate members are allowed.

## Proof route

The positive-mesh step is mathlib's `exists_monotone_Icc_subset_open_cover_unitInterval`,
applied to the preimages `γ ⁻¹ U i`. It uses `lebesgue_number_lemma_of_metric` on the compact
unit interval and a uniform partition; compactness enters only there. The remaining content is
bookkeeping: `Path.range_subpath_of_le` identifies the range of each restricted path, and
induction along the chain gives the relational form.

The module `TDA.Topology.PathCover` depends on mathlib only and does not import the Reeb
modules, so it is reusable for other cover arguments. Its component-language consequence for
the open-set path-component functor is described in `reeb-components.md`.

## Source correspondence

de Silva, Munch and Patel prove the gluing property of the path-component pre-cosheaf by local
constancy over `[0, 1]` and connectedness (*Categorified Reeb Graphs*, Proposition 3.15). The
library proves the path step of that argument by finite subdivision instead: consecutive chain
points are joined inside single members. The gluing property itself is not proved here.
Arbitrary topological spaces, arbitrary open members and an arbitrary index sort are library
generalizations of the source's open-interval covers.

Sources: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147);
[pinned mathlib unit-interval subdivision](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UnitInterval.lean);
[pinned mathlib subpaths](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Subpath.lean).
