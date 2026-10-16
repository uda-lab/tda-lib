# Real half-open barcode realization

`FiniteConstructible.barcodeRealizationIso` constructs a natural isomorphism from a
finite-constructible real-indexed module to the real interval realization of its
endpoint diagram. Repeated intervals remain separate summands, and bars surviving
the final critical stage extend over the entire right tail.

## Inputs and finite data

Fix a field `k : Type u`, a module `M : PModule.{u,0,u} k ℝ`, and a strictly increasing
critical grid `c : Fin n ↪o ℝ`. The field and module carriers share universe `u`, as in
the existing finite decomposition. Assume `IsConstructible c M`: fibers before all
critical values are zero, and actual structure maps within each left-closed/right-open
stratum are isomorphisms. The last stratum is unbounded. See
[finite-stratum reconstruction](constructible-modules.md) for this predicate.

The additional finiteness hypothesis is only

\[
\forall i\in\operatorname{Fin}(n),\quad \dim_k M(c_i)<\infty.
\]

For `q(t)=#{i | c_i≤t}`, let `A=sample c M`. This module on `Fin(n+1)` has a zero
initial fiber and `A(i+1)=M(c_i)`. Thus every sampled fiber is finite-dimensional;
global real-indexed finite-dimensionality is not an extra input. `sampleBarcode c M hfd`
is the canonical finite `rankBarcode A` with these derived finiteness instances.

## Removing the zero stage and relabeling endpoints

Every occurrence `[b,d)` in `rankBarcode A` has `b>0`. At index zero, the rank of the
identity on `A(0)` is zero. The existing barcode rank formula counts occurrences alive
there, so an occurrence born at zero would contradict that rank. The API proves this
exclusion before converting endpoints.

Sampling `A` at `Fin.succ`, namely indices `1,...,n`, replaces each positive endpoint
`e` by `e-1`. The proof computes the existing `sampledEndpoint` count. Consequently,
`restrictAlong` returns `some [b-1,d-1)` for every original occurrence. None is dropped
by `reindexBarcode`, and its cardinality is unchanged, including repetitions.

The existing `ofIndexBars` conversion then gives

\[
[b,d)\longmapsto
\begin{cases}
[c_{b-1},c_{d-1}) & d\le n,\\
[c_{b-1},\infty) & d=n+1.
\end{cases}
\]

The critical birth belongs to the support; a finite death does not. The initial zero
stage receives no real grade. The infinity case is justified by the unbounded final
cell of `q`, rather than by finite observation alone.

`moduleDiagram c M hfd` is defined from `rankBarcode (reindex c M)`, using only the
actual critical values. `moduleDiagram_eq_reindex_sample` identifies it with the
`Fin.succ` restriction of the padded sample's barcode via `rankBarcode_reindex`.
The resulting endpoint diagram is positive. For `n=0` both barcodes and the endpoint
multiset are empty, and their real realization is zero.

## Actual interval modules and natural isomorphisms

`RealBarcode.intervalModule (b,d)` is defined independently of `q`: its fiber is the
full coefficient field on `b≤t<d` and the zero submodule elsewhere. Structure maps
are identity on a pair of supported fibers and zero otherwise. `d=⊤` allows an
essential interval. The constructor also permits empty supports; the module-diagram
application uses positive endpoint pairs.

`RealBarcode.realize D` takes the finite product over the occurrences in
`D.points.toList`. A repeated pair contributes a repeated coordinate. Reordering an
enumeration induces a coordinate natural isomorphism, rather than identifying equal
values. Each realization fiber is finite-dimensional.

For each padded finite interval, `intervalPullbackIso` identifies its pullback with
the real interval at the converted endpoints. The support equivalence follows from
the critical-value counts. The fiber isomorphisms preserve the underlying coefficient,
and their naturality checks the actual identity/zero maps. `barcodePullbackIso`
assembles those maps over all occurrences and transports the enumeration to the
existing endpoint diagram.

For `D=moduleDiagram c M hfd`, the final composition is

\[
M\cong q^*A\cong q^*(\operatorname{barcodeModule}(\operatorname{rankBarcode}A))
\cong\operatorname{Realize}(D).
\]

The first map uses `reconstructionIso`; the middle map actually whiskers
`rankBarcodeIso A` along `q`. The final map is the occurrencewise interval comparison.
These are natural isomorphisms, so both transformations, their real structure-map
naturality and both inverse identities are part of the constructed value. The chosen
decomposition isomorphism is noncanonical; the diagram uses the fixed grid's canonical
rank barcode.

## Source and scope

[Bauer--Lesnick, arXiv:1311.3681v4](https://arxiv.org/html/1311.3681v4), §2.1,
defines real persistence modules, interval modules and barcode occurrences. Section 2.3
distinguishes decorated endpoints; this API uses `[b,d)` and `[b,∞)`. The source
manifestation and rights metadata remain in [BL15-v4](references.md#BL15-v4).

The proof here combines the existing finite-chain decomposition with finite-stratum
reconstruction. It realizes the bounded finite-constructible class, rather than proving
the paper's general p.f.d. decomposition theorem (Theorem 2.1). Grid independence,
arbitrary endpoint decorations, nonzero left tails, infinite/q-tame decomposition,
PH interleavings and either isometry inequality remain outside this API.
