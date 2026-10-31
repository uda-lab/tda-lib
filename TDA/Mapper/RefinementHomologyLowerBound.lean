import TDA.Mapper.RefinementHomologyInterleaving
import TDA.Simplicial.FiniteDimensionalHomology
import TDA.Simplicial.H0Augmentation

/-!
# Rank obstructions to interleavings of Mapper homology modules

Let `k` be a field and `M N` real-indexed persistence modules over `k`. In a real
`ε`-interleaving of `M` and `N`, the double-shift structure map `M(t → t + 2ε)` is the
composite `M t → N (t + ε) → M (t + 2ε)`, so its range lies in the range of the second
factor. When `N (t + ε)` is finite-dimensional, the rank of `M(t → t + 2ε)` is therefore at
most `dim N (t + ε)`, and the map is zero when `N (t + ε)` is zero. No finiteness of `M` is
assumed. Excluding every parameter below `r` in this way bounds the real interleaving
distance of `M` and `N` below by `r`. Conversely, over any ring, if every double-shift structure
map of both modules at `ε` is zero, the zero maps form an `ε`-interleaving
(`nonempty_realInterleaving_of_structureMap_eq_zero`).

For a continuous map `f` with a real cover tower `U`, a continuous map `g` with a real cover
tower `V`, a field `k` and a degree `n`, the structure maps of
`mapperHomologyPModule k f U rU n` are the homology maps of the selected refinements and its
values are Mapper homology. The rank obstruction becomes: if the homology map of
`U t → U (t + 2ε)` has rank larger than `dim Hₙ(mapper g (V (t + ε)))`, then the Mapper
homology modules of the two towers are not `ε`-interleaved. The zero-fibre form applies when
`mapper g (V (t + ε))` has no `n`-faces, in particular when it has no vertices. With
`g = f` this compares two towers of one map; with `U = V` the centred tower it combines with
`realInterleavingDistance_centredMapperHomology_le` for pointwise perturbations.

Nothing is claimed about bar-length lower bounds, decompositions, matchings or the isometry
theorem, about tightness of the rank obstruction, about lower bounds for graph-PL Reeb
distances, about multinerve homology, or about changing the component orders.
-/

namespace TDA.Mapper

open CategoryTheory
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence
open TDA.Persistence.RealShift
open scoped NNReal ENNReal

noncomputable section

universe u v w c

section Rank

variable {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ} {ε : ℝ≥0}

/-- The second factor of the double-shift structure map of an `ε`-interleaving: `i.ψ` at
`t + ε` followed by the shift transport, as a linear map out of `N (t + ε)`. -/
private def backMap (i : RealInterleaving ε M N) (t : ℝ) :
    N.obj (t + ε) →ₗ[k] M.obj (t + ((ε + ε : ℝ≥0) : ℝ)) :=
  (i.ψ.app (t + (ε : ℝ)) ≫ (compIso ε ε M).hom.app t).hom

/-- In an `ε`-interleaving, the structure map of `M` across `2ε` factors through
`N (t + ε)`. -/
private theorem structureMapLinear_eq_comp (i : RealInterleaving ε M N) (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) :
    structureMapLinear M h = (backMap i t).comp (i.φ.app t).hom := by
  have e := i.φ_ψ_app t
  rw [transition_app] at e
  change (structureMap M h).hom = _
  rw [show structureMap M h = structureMap M (le_add_of_nonneg_right
    (ε + ε).coe_nonneg) from rfl, ← e]
  rfl

/-- **Rank bound.** In an `ε`-interleaving of `M` and `N`, the rank of the structure map of `M`
from `t` to `t + 2ε` is at most the dimension of `N (t + ε)`, provided only that this one value
of `N` is finite-dimensional. -/
theorem finrank_range_structureMapLinear_le_of_realInterleaving (i : RealInterleaving ε M N)
    (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) [FiniteDimensional k (N.obj (t + ε))] :
    Module.finrank k (LinearMap.range (structureMapLinear M h)) ≤
      Module.finrank k (N.obj (t + ε)) := by
  rw [structureMapLinear_eq_comp i t h]
  exact (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
    (LinearMap.finrank_range_le (backMap i t))

/-- **Rank bound, symmetric form.** In an `ε`-interleaving of `M` and `N`, the rank of the
structure map of `N` from `t` to `t + 2ε` is at most the dimension of `M (t + ε)`. -/
theorem finrank_range_structureMapLinear_le_of_realInterleaving' (i : RealInterleaving ε M N)
    (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) [FiniteDimensional k (M.obj (t + ε))] :
    Module.finrank k (LinearMap.range (structureMapLinear N h)) ≤
      Module.finrank k (M.obj (t + ε)) :=
  finrank_range_structureMapLinear_le_of_realInterleaving i.symm t h

/-- **Zero fibre.** In an `ε`-interleaving of `M` and `N`, if `N (t + ε)` is zero then the
structure map of `M` from `t` to `t + 2ε` is zero. -/
theorem structureMap_eq_zero_of_realInterleaving (i : RealInterleaving ε M N) (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) [Subsingleton (N.obj (t + ε))] :
    structureMap M h = 0 := by
  apply ModuleCat.hom_ext
  rw [← structureMapLinear, structureMapLinear_eq_comp i t h]
  ext x
  change backMap i t ((i.φ.app t).hom x) = 0
  rw [Subsingleton.elim (α := N.obj (t + ε)) ((i.φ.app t).hom x) 0]
  exact (backMap i t).map_zero

/-- If the structure map of `M` from `t` to `t + 2ε` has rank larger than the dimension of a
finite-dimensional `N (t + ε)`, then `M` and `N` are not `ε`-interleaved. -/
theorem isEmpty_realInterleaving_of_finrank_lt (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ))
    [FiniteDimensional k (N.obj (t + ε))]
    (hlt : Module.finrank k (N.obj (t + ε)) <
      Module.finrank k (LinearMap.range (structureMapLinear M h))) :
    IsEmpty (RealInterleaving ε M N) :=
  ⟨fun i => (finrank_range_structureMapLinear_le_of_realInterleaving i t h).not_gt hlt⟩

/-- If the structure map of `M` from `t` to `t + 2ε` is nonzero and `N (t + ε)` is zero, then
`M` and `N` are not `ε`-interleaved. -/
theorem isEmpty_realInterleaving_of_structureMap_ne_zero (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) [Subsingleton (N.obj (t + ε))]
    (hne : structureMap M h ≠ 0) : IsEmpty (RealInterleaving ε M N) :=
  ⟨fun i => hne (structureMap_eq_zero_of_realInterleaving i t h)⟩

/-- **Distance lower bound.** If for every finite parameter `ε < r` some structure map of `M`
from `t` to `t + 2ε` has rank larger than the dimension of a finite-dimensional `N (t + ε)`,
then the real interleaving distance of `M` and `N` is at least `r`. -/
theorem le_realInterleavingDistance_of_finrank_lt {r : ℝ≥0∞}
    (hr : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      FiniteDimensional k (N.obj (t + ε)) ∧
        Module.finrank k (N.obj (t + ε)) <
          Module.finrank k (LinearMap.range (structureMapLinear M h))) :
    r ≤ realInterleavingDistance M N := by
  rw [le_realInterleavingDistance_iff]
  intro ε ⟨i⟩
  by_contra hεr
  obtain ⟨t, h, _, hlt⟩ := hr ε (not_le.1 hεr)
  exact (isEmpty_realInterleaving_of_finrank_lt t h hlt).false i

/-- **Distance lower bound, zero-fibre form.** If for every finite parameter `ε < r` some
structure map of `M` from `t` to `t + 2ε` is nonzero while `N (t + ε)` is zero, then the real
interleaving distance of `M` and `N` is at least `r`. -/
theorem le_realInterleavingDistance_of_structureMap_ne_zero {r : ℝ≥0∞}
    (hr : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      Subsingleton (N.obj (t + ε)) ∧ structureMap M h ≠ 0) :
    r ≤ realInterleavingDistance M N := by
  rw [le_realInterleavingDistance_iff]
  intro ε ⟨i⟩
  by_contra hεr
  obtain ⟨t, h, _, hne⟩ := hr ε (not_le.1 hεr)
  exact (isEmpty_realInterleaving_of_structureMap_ne_zero t h hne).false i

end Rank

section ZeroMaps

variable {R : Type u} [Ring R] {M N : PModule.{u,0,w} R ℝ}

/-- **Zero maps.** If every double-shift structure map of two real modules at the parameter `ε`
is zero, the zero maps form an `ε`-interleaving. This is a converse companion of
`isEmpty_realInterleaving_of_structureMap_ne_zero`. -/
theorem nonempty_realInterleaving_of_structureMap_eq_zero (ε : ℝ≥0)
    (hM : ∀ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)), structureMap M h = 0)
    (hN : ∀ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)), structureMap N h = 0) :
    Nonempty (RealInterleaving ε M N) :=
  ⟨RealInterleaving.ofApp 0 0
    (fun t => by
      rw [NatTrans.app_zero, Limits.zero_comp, transition_app]
      exact (hM t _).symm)
    (fun t => by
      rw [NatTrans.app_zero, Limits.zero_comp, transition_app]
      exact (hN t _).symm)⟩

end ZeroMaps

section Mapper

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A Mapper complex without component indices, for instance one over an empty domain or with
every member's inverse image empty, has no faces in any degree. -/
theorem isEmpty_face_mapper {I : Type w} (f : C(X, Y)) (U : I → Set Y)
    [LinearOrder (ComponentIndex f U)] [IsEmpty (ComponentIndex f U)] (n : ℕ) :
    IsEmpty (Face (mapper f U) n) :=
  ⟨fun σ => by
    obtain ⟨a, _⟩ := ((mem_mapper_iff f U σ.1).1 σ.2.1).1
    exact isEmptyElim a⟩

private theorem isZero_simplicialHomology {V : Type*} [LinearOrder V]
    (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R] (n : ℕ) [IsEmpty (Face K n)] :
    Limits.IsZero (simplicialHomology K R n) := by
  have hX : Limits.IsZero ((simplicialChainComplex K R).X n) := by
    rw [simplicialChainComplex_X]
    exact ModuleCat.isZero_of_subsingleton _
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ hX

variable (k : Type c) [Field k] {f g : C(X, Y)} {IndexU IndexV : ℝ → Type w}
  {U : (t : ℝ) → IndexU t → Set Y} {V : (t : ℝ) → IndexV t → Set Y}
  [∀ t, LinearOrder (ComponentIndex f (U t))] [∀ t, LinearOrder (ComponentIndex g (V t))]
  (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t))
  (rV : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t)) (n : ℕ) {ε : ℝ≥0}

/-- **Mapper rank obstruction.** If the homology map of the refinement `U t → U (t + 2ε)` has
rank larger than the dimension of a finite-dimensional `Hₙ(mapper g (V (t + ε)))`, then the
Mapper homology modules of `f` along `U` and of `g` along `V` are not `ε`-interleaved. -/
theorem isEmpty_realInterleaving_mapperHomologyPModule_of_finrank_lt (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ))
    [FiniteDimensional k (simplicialHomology (mapper g (V (t + ε))) k n)]
    (hlt : Module.finrank k (simplicialHomology (mapper g (V (t + ε))) k n) <
      Module.finrank k (LinearMap.range (mapperHomologyMap k f (rU h) n).hom)) :
    IsEmpty (RealInterleaving ε (mapperHomologyPModule k f U rU n)
      (mapperHomologyPModule k g V rV n)) :=
  have : FiniteDimensional k ((mapperHomologyPModule k g V rV n).obj (t + ε)) :=
    inferInstanceAs (FiniteDimensional k (simplicialHomology (mapper g (V (t + ε))) k n))
  isEmpty_realInterleaving_of_finrank_lt t h hlt

/-- **Mapper distance lower bound.** If for every finite parameter `ε < r` some homology map of a
refinement `U t → U (t + 2ε)` has rank larger than the dimension of a finite-dimensional
`Hₙ(mapper g (V (t + ε)))`, then the Mapper homology modules are at real interleaving distance
at least `r`. -/
theorem le_realInterleavingDistance_mapperHomologyPModule_of_finrank_lt {r : ℝ≥0∞}
    (hr : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      FiniteDimensional k (simplicialHomology (mapper g (V (t + ε))) k n) ∧
        Module.finrank k (simplicialHomology (mapper g (V (t + ε))) k n) <
          Module.finrank k (LinearMap.range (mapperHomologyMap k f (rU h) n).hom)) :
    r ≤ realInterleavingDistance (mapperHomologyPModule k f U rU n)
      (mapperHomologyPModule k g V rV n) :=
  le_realInterleavingDistance_of_finrank_lt hr

/-- **Mapper zero-fibre obstruction.** If `mapper g (V (t + ε))` has no `n`-faces and the
homology map of the refinement `U t → U (t + 2ε)` in degree `n` is nonzero, then the Mapper
homology modules are not `ε`-interleaved. -/
theorem isEmpty_realInterleaving_mapperHomologyPModule_of_isEmpty_face (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) [IsEmpty (Face (mapper g (V (t + ε))) n)]
    (hne : mapperHomologyMap k f (rU h) n ≠ 0) :
    IsEmpty (RealInterleaving ε (mapperHomologyPModule k f U rU n)
      (mapperHomologyPModule k g V rV n)) :=
  have : Subsingleton ((mapperHomologyPModule k g V rV n).obj (t + ε)) :=
    ModuleCat.subsingleton_of_isZero (isZero_simplicialHomology (mapper g (V (t + ε))) k n)
  isEmpty_realInterleaving_of_structureMap_ne_zero t h hne

/-- **Mapper distance lower bound, zero-fibre form.** If for every finite parameter `ε < r` some
`mapper g (V (t + ε))` has no `n`-faces while the homology map of a refinement
`U t → U (t + 2ε)` is nonzero, then the Mapper homology modules are at real interleaving
distance at least `r`. -/
theorem le_realInterleavingDistance_mapperHomologyPModule_of_isEmpty_face {r : ℝ≥0∞}
    (hr : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      IsEmpty (Face (mapper g (V (t + ε))) n) ∧ mapperHomologyMap k f (rU h) n ≠ 0) :
    r ≤ realInterleavingDistance (mapperHomologyPModule k f U rU n)
      (mapperHomologyPModule k g V rV n) := by
  refine le_realInterleavingDistance_of_structureMap_ne_zero fun ε hε => ?_
  obtain ⟨t, h, _, hne⟩ := hr ε hε
  exact ⟨t, h, ModuleCat.subsingleton_of_isZero
    (isZero_simplicialHomology (mapper g (V (t + ε))) k n), hne⟩

/-- Over a field, the degree-`0` homology map of a refinement is nonzero when the source family
has a component index: the class of the corresponding vertex is nonzero and maps to the class of
a vertex. -/
theorem mapperHomologyMap_zero_ne_zero {ι κ : Type w} {U : ι → Set Y} {V : κ → Set Y}
    [LinearOrder (ComponentIndex f U)] [LinearOrder (ComponentIndex f V)]
    (ρ : Refinement U V) (a : ComponentIndex f U) :
    mapperHomologyMap k f ρ 0 ≠ 0 := by
  intro h0
  let σ : Face (mapper f U) 0 := ⟨{a}, componentIndex_supported f U a, Finset.card_singleton a⟩
  have hclass := simplicialHomologyMap_class k (mapperMap f ρ) 0 (zeroVertexCycle _ k σ)
    (zeroVertexCycle _ k (vertexImageFace (mapperMap f ρ) σ (fun i j _ => Fin.ext (by omega))))
    (vertexChainMap_vertex k _ _ 1)
  rw [← mapperHomologyMap_def, h0] at hclass
  exact simplicialHomologyClass_zeroVertexCycle_ne_zero _ k _ hclass.symm

end Mapper

section Perturbation

variable {X : Type u} [TopologicalSpace X] (k : Type c) [Field k] {f g : C(X, ℝ)} (s : ℝ)
  [∀ t, LinearOrder (ComponentIndex f (centredCover s t))]
  [∀ t, LinearOrder (ComponentIndex g (centredCover s t))] (n : ℕ) {ε : ℝ≥0}

/-- **Centred-tower rank obstruction.** For real-valued maps `f` and `g` along the centred
tower of spacing `s`: if the homology map of `f` from radius `t` to radius `t + 2ε` has rank
larger than the dimension of a finite-dimensional `Hₙ(mapper g (centredCover s (t + ε)))`,
then the two Mapper homology modules are not `ε`-interleaved. -/
theorem isEmpty_realInterleaving_centredMapperHomology_of_finrank_lt (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ))
    [FiniteDimensional k (simplicialHomology (mapper g (centredCover s (t + ε))) k n)]
    (hlt : Module.finrank k (simplicialHomology (mapper g (centredCover s (t + ε))) k n) <
      Module.finrank k (LinearMap.range
        (mapperHomologyMap k f (centredCoverRefinement s h) n).hom)) :
    IsEmpty (RealInterleaving ε
      (mapperHomologyPModule k f (centredCover s) (centredCoverRefinement s) n)
      (mapperHomologyPModule k g (centredCover s) (centredCoverRefinement s) n)) :=
  isEmpty_realInterleaving_mapperHomologyPModule_of_finrank_lt k
    (centredCoverRefinement s) (centredCoverRefinement s) n t h hlt

/-- **Centred-tower distance lower bound.** If for every finite parameter `ε < r` some homology
map of `f` from radius `t` to radius `t + 2ε` along the centred tower has rank larger than the
dimension of a finite-dimensional `Hₙ(mapper g (centredCover s (t + ε)))`, then the two Mapper
homology modules are at real interleaving distance at least `r`. -/
theorem le_realInterleavingDistance_centredMapperHomology_of_finrank_lt {r : ℝ≥0∞}
    (hr : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      FiniteDimensional k (simplicialHomology (mapper g (centredCover s (t + ε))) k n) ∧
        Module.finrank k (simplicialHomology (mapper g (centredCover s (t + ε))) k n) <
          Module.finrank k (LinearMap.range
            (mapperHomologyMap k f (centredCoverRefinement s h) n).hom)) :
    r ≤ realInterleavingDistance
      (mapperHomologyPModule k f (centredCover s) (centredCoverRefinement s) n)
      (mapperHomologyPModule k g (centredCover s) (centredCoverRefinement s) n) :=
  le_realInterleavingDistance_mapperHomologyPModule_of_finrank_lt k
    (centredCoverRefinement s) (centredCoverRefinement s) n hr

end Perturbation

end

end TDA.Mapper
