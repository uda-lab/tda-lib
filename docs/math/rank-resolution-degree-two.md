# A degree-two rank-projective witness in two real coordinates

Let `k` be any field. No characteristic, finiteness, or algebraic-closure
assumption is needed. The finite model lives on the actual grid
`G : CoordinateGrid 2` whose two coordinate sets are both `{0,1,2}`. Write
`H(x,y)` for the library's finite-death hook, with support

```text
{ p | x ≤ p and not (y ≤ p) }.
```

Thus a hook is not the bounded rectangle or half-open square between its
endpoints. In particular, `H((1,1),(2,2))` contains the points `(1,2)` and
`(2,1)` and dies at `(2,2)`.

## The finite module and its hook terms

Name the grid points

```text
       e=(2,0)    g=(2,1)    h=(2,2)
       b=(1,0)    c=(1,1)    f=(1,2)
       o=(0,0)    a=(0,1)    d=(0,2)
```

The module `finiteModule` is defined independently from a resolution. Its
support is

```text
S = ((↑a ∪ ↑b) ∩ ↓c) = {a,b,c}.
```

It has one copy of `k` at those three points, zero elsewhere, and identity
structure maps from `a` to `c` and from `b` to `c`. This is a pointwise
finite-dimensional module on a finite poset.

The concrete resolution uses the following actual finite hooks:

```text
A = H(a,d)    B = H(a,g)    C = H(b,f)    D = H(b,e)
E = H(a,h)    F = H(b,h)    J = H(c,f)    K = H(c,g)
L = H(c,h)

P₀ = A ⊕ B ⊕ C ⊕ D
P₁ = E ⊕ F ⊕ J ⊕ K
P₂ = L
```

Each summand of `P₀` maps to `finiteModule` by sending its birth unit to the
unit at `a` or `b`. The resulting augmentation `q₀ : P₀ → finiteModule` is
surjective, and its actual categorical kernel is `K₁ := kernel q₀`.

The next quotient `q₁ : P₁ → K₁` is defined by lifting the following map
through that actual kernel:

```text
           E   F   J   K
      A    1   0   1   0
      B   -1   0   0   1
      C    0   1  -1   0
      D    0  -1   0  -1
```

The degree-two map `j : L → P₁` has column `(1,-1,-1,1)` in the order
`(E,F,J,K)`. These are the literal maps `d1` and `j`, built from the
repository's normalized hook maps. The selected length-three resolution has
kernel objects `(finiteModule,K₁,L,0)`, terms `(P₀,P₁,L)`, quotients
`(q₀,q₁,id_L)`, and inclusions `(kernel.ι q₀,j,0)`.

## Rank exactness and minimality

Both nontrivial rows are proved rank exact from the maps. At every grid point,
`q₀` is surjective and every quotient vector killed by a structure map has a
lift in `P₀` killed at the same target. This supplies the actual-kernel
rank-exact row for `q₀`.

For the second row, the fiber at `c` of `K₁` consists of the coefficient
vectors `(A,B,C,D)` satisfying `A+B+C+D=0`; one preimage under `q₁` is
`(-B,-D,A+B,0)`. The kernel of `q₁` is exactly the image of the given `j`,
including at the boundary fibers `f` and `g`. For same-death lifting, a vector
at `c` dying toward `f` is a multiple of `A-C` and lifts through `J`; one
dying toward `g` is a multiple of `B-D` and lifts through `K`. The other
nonzero syzygy fibers propagate until `h`, where their `E` or `F` lifts die.
These pointwise facts give the row's rank additivity through the existing
same-death criterion. The last row is the split identity row on `L` and zero.

Each term is rank projective. Within each four-hook family, all off-diagonal
Hom spaces vanish; every endomorphism of a summand is a scalar identity.
Therefore every endomorphism of `P₀` or `P₁` fixed by its quotient is
diagonal with every scalar equal to one, since each quotient component is
nonzero at birth. This proves that `q₀` and `q₁` are rank-projective covers.
The final quotient is the identity cover. Hence the concrete resolution is a
certified minimal finite rank-projective resolution, rather than just a
rank-exact complex of the stated length.

The unit of `L` at `c` is nonzero, and the prescribed `j` is nonzero over
every field, including characteristic two. Termwise uniqueness of certified
minimal resolutions then shows that every minimal finite resolution of
`finiteModule` has nonzero term two and zero terms above two, including after
arbitrary terminal zero padding.

There is a separate ordinary projective-dimension calculation for the actual
finite hook-generator Hom object:

```text
projectiveDimension
  ((FiniteRankProjectiveHomExact.homFunctor (S := G.Point)).obj finiteModule) = 2.
```

This is a dimension over the actual opposite endomorphism ring of the finite
hook generator after applying the Hom functor. It is not a claim about the
ordinary functor-category projective dimension of `finiteModule`.

## The real-coordinate module

Define `realModule` literally as `G.lan.obj finiteModule`, the actual left Kan
extension along the grid embedding. Its original
`GradedFree.FinitelyPresented.{u,0,0}` predicate is derived from the
finite-dimensional fibers of the finite-poset module and the existing
finite-grid Kan preservation theorem. No resolution or finite-presentation
assumption is used to define the module.

Applying the actual Kan functor to the selected finite resolution gives a
concrete certified minimal resolution of `realModule`. The second term is
identified with the real hook `H((1,1),(2,2))` by the Kan comparison for
`H(c,h)`. This real hook is supported where both coordinates are at least one
and the point does not lie above `(2,2)`. It therefore continues along the
upper arm `(1,t)` for `t ≥ 1` and the right arm `(t,1)` for `t ≥ 1`, while its
birth unit dies at `(2,2)`.

For every certified minimal resolution of this real module, term two is
nonzero and all terms above degree two are zero. These conclusions use the
real term isomorphism and zero-padded termwise uniqueness, so they do not
depend on the supplied resolution's stored length. The module is thus a
concrete two-coordinate equality case for the general `2n-2` upper bound.

The construction proves no lower bound in every dimension, computes no
ordinary projective dimension for the module itself, and includes no signed
stability or primary-source comparison claim. The reusable theory is in
`TDA.Persistence.RankResolutionDegreeTwo`; the rational and characteristic-two
consumers are in the separate fixture module
`TDA.Persistence.RankResolutionDegreeTwoExamples`, under the declaration
namespace `TDA.Persistence.RankResolutionDegreeTwo.Examples`.
