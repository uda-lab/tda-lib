import TDA.Mapper.RefinementHomologyInterleaving
import TDA.Mapper.RefinementHomologyDomainMap
import TDA.Reeb.HeightMapPair
import TDA.Reeb.GraphPLHeight

/-!
# Centred Mapper homology interleavings from height-map pairs

A `HeightMapPair` between real-valued maps on possibly different spaces induces vertex maps
between their centred Mapper complexes, shifting the radius by the pair parameter. These maps
are natural in the radius. The composite maps agree on vertices with the double-radius tower
maps because the pair's composite paths remain in the enlarged inverse images. They therefore
give an interleaving of the Mapper homology modules in every degree and over every ring, for the
supplied component orders. No finiteness, coverage, nonemptiness, or order-independence claim is
made.
-/

namespace TDA.Mapper

open CategoryTheory
open TDA.Reeb
open TDA.Reeb.GraphPL
open TDA.Simplicial
open TDA.Persistence
open TDA.Persistence.RealShift
open TDA.Topology
open scoped NNReal

noncomputable section

universe u c

variable {X X' : Type u} [TopologicalSpace X] [TopologicalSpace X']
  {f : C(X, ℝ)} {g : C(X', ℝ)} {δ : ℝ≥0}

/-- The vertex map from the radius-`t` Mapper of `f` to the radius-`t + δ` Mapper of `g`
induced by the forward map of a height-map pair. -/
def centredMapperPairVertexMap (P : HeightMapPair f g δ) (s t : ℝ) :
    VertexMap (mapper f (centredCover s t)) (mapper g (centredCover s (t + δ))) :=
  VertexMap.comp
    (mapperMap (ContinuousMap.id X)
      (centredPullbackRefinement
        (fun x => (abs_sub_comm _ _).trans_le (P.hφ x)) s t))
    (mapperDomainMap (f := g.comp P.φ) (f' := g) P.φ (by intro x; rfl)
      (centredCover s (t + δ)))

/-- On a represented vertex, the forward map preserves its label and applies the domain map to
its representative. -/
@[simp] theorem centredMapperPairVertexMap_mk (P : HeightMapPair f g δ) (s t : ℝ)
    (k : ℤ) (x : PullbackSpace f (centredCover s t) k) :
    centredMapperPairVertexMap P s t ⟨k, ZerothHomotopy.mk x⟩ =
      ⟨k, ZerothHomotopy.mk ⟨P.φ x.1, by
        rw [mem_centredCover_iff]
        have hx : |f x.1 - k * s| < t := mem_centredCover_iff.mp x.2
        calc
          |g (P.φ x.1) - k * s| ≤ |g (P.φ x.1) - f x.1| + |f x.1 - k * s| :=
            abs_sub_le _ _ _
          _ < (δ : ℝ) + t := add_lt_add_of_le_of_lt (P.hφ x.1) hx
          _ = t + δ := add_comm _ _⟩⟩ := by
  rfl

/-- The vertex map in the reverse direction, induced by the reverse map of the pair. -/
def centredMapperPairVertexMapSymm (P : HeightMapPair f g δ) (s t : ℝ) :
    VertexMap (mapper g (centredCover s t)) (mapper f (centredCover s (t + δ))) :=
  centredMapperPairVertexMap P.symm s t

/-- On a represented vertex, the reverse map preserves its label and applies the reverse domain
map to its representative. -/
@[simp] theorem centredMapperPairVertexMapSymm_mk (P : HeightMapPair f g δ) (s t : ℝ)
    (k : ℤ) (y : PullbackSpace g (centredCover s t) k) :
    centredMapperPairVertexMapSymm P s t ⟨k, ZerothHomotopy.mk y⟩ =
      ⟨k, ZerothHomotopy.mk ⟨P.ψ y.1, by
        rw [mem_centredCover_iff]
        have hy : |g y.1 - k * s| < t := mem_centredCover_iff.mp y.2
        calc
          |f (P.ψ y.1) - k * s| ≤ |f (P.ψ y.1) - g y.1| + |g y.1 - k * s| :=
            abs_sub_le _ _ _
          _ < (δ : ℝ) + t := add_lt_add_of_le_of_lt (P.hψ y.1) hy
          _ = t + δ := add_comm _ _⟩⟩ := by
  rfl

/-- The forward pair map commutes strictly with the identity-selector refinements of the
centred towers. -/
theorem centredMapperPairVertexMap_natural (P : HeightMapPair f g δ) (s : ℝ)
    {t t' : ℝ} (h : t ≤ t') :
    VertexMap.comp (mapperMap f (centredCoverRefinement s h))
        (centredMapperPairVertexMap P s t') =
      VertexMap.comp (centredMapperPairVertexMap P s t)
        (mapperMap g (centredCoverRefinement s (add_le_add h le_rfl))) := by
  apply VertexMap.ext
  rintro ⟨k, c⟩
  induction c using ZerothHomotopy.rec with
  | mk x =>
    change centredMapperPairVertexMap P s t'
        (mapperMap f (centredCoverRefinement s h) ⟨k, ZerothHomotopy.mk x⟩) =
      mapperMap g (centredCoverRefinement s (add_le_add h le_rfl))
        (centredMapperPairVertexMap P s t ⟨k, ZerothHomotopy.mk x⟩)
    rw [mapperMap_mk, centredMapperPairVertexMap_mk,
      centredMapperPairVertexMap_mk, mapperMap_mk]
    rfl

/-- The reverse pair map commutes strictly with the identity-selector refinements of the
centred towers. -/
theorem centredMapperPairVertexMapSymm_natural (P : HeightMapPair f g δ) (s : ℝ)
    {t t' : ℝ} (h : t ≤ t') :
    VertexMap.comp (mapperMap g (centredCoverRefinement s h))
        (centredMapperPairVertexMapSymm P s t') =
      VertexMap.comp (centredMapperPairVertexMapSymm P s t)
        (mapperMap f (centredCoverRefinement s (add_le_add h le_rfl))) :=
  centredMapperPairVertexMap_natural P.symm s h

private theorem joinedIn_doubleShift_f (P : HeightMapPair f g δ) (s t : ℝ) (k : ℤ)
    (x : PullbackSpace f (centredCover s t) k) :
    JoinedIn (f ⁻¹' centredCover s (t + δ + δ) k) x.1 (P.ψ (P.φ x.1)) := by
  obtain ⟨γ, hγ⟩ := P.hψφ x.1
  refine ⟨γ, fun q => ?_⟩
  change f (γ q) ∈ centredCover s (t + δ + δ) k
  rw [mem_centredCover_iff]
  have hx : |f x.1 - k * s| < t := mem_centredCover_iff.mp x.2
  calc
    |f (γ q) - k * s| ≤ |f (γ q) - f x.1| + |f x.1 - k * s| := abs_sub_le _ _ _
    _ < δ + δ + t := by
      have hpath : |f (γ q) - f x.1| ≤ (δ : ℝ) + δ := by
        simpa only [NNReal.coe_add] using hγ q
      exact add_lt_add_of_le_of_lt hpath hx
    _ = t + δ + δ := by ring

private theorem joinedIn_doubleShift_g (P : HeightMapPair f g δ) (s t : ℝ) (k : ℤ)
    (y : PullbackSpace g (centredCover s t) k) :
    JoinedIn (g ⁻¹' centredCover s (t + δ + δ) k) y.1 (P.φ (P.ψ y.1)) := by
  obtain ⟨γ, hγ⟩ := P.hφψ y.1
  refine ⟨γ, fun q => ?_⟩
  change g (γ q) ∈ centredCover s (t + δ + δ) k
  rw [mem_centredCover_iff]
  have hy : |g y.1 - k * s| < t := mem_centredCover_iff.mp y.2
  calc
    |g (γ q) - k * s| ≤ |g (γ q) - g y.1| + |g y.1 - k * s| := abs_sub_le _ _ _
    _ < δ + δ + t := by
      have hpath : |g (γ q) - g y.1| ≤ (δ : ℝ) + δ := by
        simpa only [NNReal.coe_add] using hγ q
      exact add_lt_add_of_le_of_lt hpath hy
    _ = t + δ + δ := by ring

/-- The composite of the forward and reverse vertex maps agrees with the centred tower map
through radius `t + δ + δ`. -/
theorem centredMapperPairVertexMap_comp (P : HeightMapPair f g δ) (s t : ℝ) :
    VertexMap.comp (centredMapperPairVertexMap P s t)
        (centredMapperPairVertexMapSymm P s (t + δ)) =
      mapperMap f (centredCoverRefinement s (by
        have _hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
        linarith)) := by
  apply VertexMap.ext
  rintro ⟨k, c⟩
  induction c using ZerothHomotopy.rec with
  | mk x =>
    change centredMapperPairVertexMapSymm P s (t + δ)
        (centredMapperPairVertexMap P s t ⟨k, ZerothHomotopy.mk x⟩) =
      mapperMap f (centredCoverRefinement s (by
        have _hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
        linarith)) ⟨k, ZerothHomotopy.mk x⟩
    rw [centredMapperPairVertexMap_mk, centredMapperPairVertexMapSymm_mk,
      mapperMap_mk]
    simp only [centredCoverRefinement]
    change (⟨k, ZerothHomotopy.mk ⟨P.ψ (P.φ x.1), _⟩⟩ :
        ComponentIndex f (centredCover s (t + δ + δ))) =
      ⟨k, ZerothHomotopy.mk ⟨x.1, _⟩⟩
    apply congrArg (fun c : ZerothHomotopy (PullbackSpace f (centredCover s (t + δ + δ)) k) =>
      (⟨k, c⟩ : ComponentIndex f (centredCover s (t + δ + δ))))
    have hxlarge : f x.1 ∈ centredCover s (t + δ + δ) k := by
      rw [mem_centredCover_iff]
      have hx : |f x.1 - k * s| < t := mem_centredCover_iff.mp x.2
      have _hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
      linarith
    exact (TDA.Topology.mk_eq_of_joinedIn f (centredCover s (t + δ + δ) k)
      (joinedIn_doubleShift_f P s t k x) hxlarge
      (joinedIn_doubleShift_f P s t k x).target_mem).symm

/-- The reverse and forward vertex maps agree with the centred tower map through radius
`t + δ + δ`. -/
theorem centredMapperPairVertexMapSymm_comp (P : HeightMapPair f g δ) (s t : ℝ) :
    VertexMap.comp (centredMapperPairVertexMapSymm P s t)
        (centredMapperPairVertexMap P s (t + δ)) =
      mapperMap g (centredCoverRefinement s (by
        have _hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
        linarith)) :=
  centredMapperPairVertexMap_comp P.symm s t

variable (R : Type c) [Ring R] (s : ℝ)
  [hf : ∀ t, LinearOrder (ComponentIndex f (centredCover s t))]
  [hg : ∀ t, LinearOrder (ComponentIndex g (centredCover s t))]
  (n : ℕ)

private theorem mapperHomologyPModule_map_f {t t' : ℝ} (h : t ⟶ t') :
    (mapperHomologyPModule R f (centredCover s) (centredCoverRefinement s) n).map h =
      mapperHomologyMap R f (centredCoverRefinement s (leOfHom h)) n := rfl

private theorem mapperHomologyPModule_map_g {t t' : ℝ} (h : t ⟶ t') :
    (mapperHomologyPModule R g (centredCover s) (centredCoverRefinement s) n).map h =
      mapperHomologyMap R g (centredCoverRefinement s (leOfHom h)) n := rfl

/-- The forward vertex maps induce a natural transformation from the Mapper homology module of
`f` to the `δ`-shift of the module of `g`. -/
def centredMapperPairHomologyMap (P : HeightMapPair f g δ) :
    mapperHomologyPModule R f (centredCover s) (centredCoverRefinement s) n ⟶
      (shift δ).obj (mapperHomologyPModule R g (centredCover s)
        (centredCoverRefinement s) n) where
  app t := simplicialHomologyMap R (centredMapperPairVertexMap P s t) n
  naturality t t' h := by
    change mapperHomologyMap R f (centredCoverRefinement s (leOfHom h)) n ≫
        simplicialHomologyMap R (centredMapperPairVertexMap P s t') n =
      simplicialHomologyMap R (centredMapperPairVertexMap P s t) n ≫
        mapperHomologyMap R g
          (centredCoverRefinement s (add_le_add (leOfHom h) le_rfl)) n
    rw [mapperHomologyMap_def, mapperHomologyMap_def,
      ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp,
      centredMapperPairVertexMap_natural]

/-- The component of the forward homology transformation is induced by the forward vertex map. -/
@[simp] theorem centredMapperPairHomologyMap_app (P : HeightMapPair f g δ) (t : ℝ) :
    (centredMapperPairHomologyMap R s n P).app t =
      simplicialHomologyMap R (centredMapperPairVertexMap P s t) n := rfl

/-- The reverse vertex maps induce a natural transformation from the Mapper homology module of
`g` to the `δ`-shift of the module of `f`. -/
def centredMapperPairHomologyMapSymm (P : HeightMapPair f g δ) :
    mapperHomologyPModule R g (centredCover s) (centredCoverRefinement s) n ⟶
      (shift δ).obj (mapperHomologyPModule R f (centredCover s)
        (centredCoverRefinement s) n) where
  app t := simplicialHomologyMap R (centredMapperPairVertexMapSymm P s t) n
  naturality t t' h := by
    change mapperHomologyMap R g (centredCoverRefinement s (leOfHom h)) n ≫
        simplicialHomologyMap R (centredMapperPairVertexMapSymm P s t') n =
      simplicialHomologyMap R (centredMapperPairVertexMapSymm P s t) n ≫
        mapperHomologyMap R f
          (centredCoverRefinement s (add_le_add (leOfHom h) le_rfl)) n
    rw [mapperHomologyMap_def, mapperHomologyMap_def,
      ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp,
      centredMapperPairVertexMapSymm_natural]

/-- The component of the reverse homology transformation is induced by the reverse vertex map. -/
@[simp] theorem centredMapperPairHomologyMapSymm_app (P : HeightMapPair f g δ) (t : ℝ) :
    (centredMapperPairHomologyMapSymm R s n P).app t =
      simplicialHomologyMap R (centredMapperPairVertexMapSymm P s t) n := rfl

private theorem centredMapperPairHomologyMap_comp_f (P : HeightMapPair f g δ)
    (t : ℝ) :
    simplicialHomologyMap R (centredMapperPairVertexMap P s t) n ≫
        simplicialHomologyMap R (centredMapperPairVertexMapSymm P s (t + δ)) n =
      mapperHomologyMap R f
        (centredCoverRefinement s (by
          have _hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
          linarith)) n := by
  rw [← simplicialHomologyMap_comp R (centredMapperPairVertexMap P s t)
    (centredMapperPairVertexMapSymm P s (t + δ)) n,
    centredMapperPairVertexMap_comp P s t, ← mapperHomologyMap_def]

private theorem centredMapperPairHomologyMap_comp_g (P : HeightMapPair f g δ)
    (t : ℝ) :
    simplicialHomologyMap R (centredMapperPairVertexMapSymm P s t) n ≫
        simplicialHomologyMap R (centredMapperPairVertexMap P s (t + δ)) n =
      mapperHomologyMap R g
        (centredCoverRefinement s (by
          have _hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
          linarith)) n := by
  rw [← simplicialHomologyMap_comp R (centredMapperPairVertexMapSymm P s t)
    (centredMapperPairVertexMap P s (t + δ)) n,
    centredMapperPairVertexMapSymm_comp P s t, ← mapperHomologyMap_def]

/-- A height-map pair induces a `δ`-interleaving of its centred Mapper homology modules. -/
def centredMapperPairInterleaving (P : HeightMapPair f g δ) :
    RealInterleaving δ
      (mapperHomologyPModule R f (centredCover s) (centredCoverRefinement s) n)
      (mapperHomologyPModule R g (centredCover s) (centredCoverRefinement s) n) :=
  RealInterleaving.ofApp (centredMapperPairHomologyMap R s n P)
    (centredMapperPairHomologyMapSymm R s n P)
    (fun t => by
      rw [compIso_hom_app, transition_app, mapperHomologyPModule_map_f,
        structureMap_mapperHomologyPModule]
      simp only [centredMapperPairHomologyMap_app, centredMapperPairHomologyMapSymm_app,
        shift_obj, mapperHomologyPModule_obj]
      rw [← Category.assoc]
      rw [centredMapperPairHomologyMap_comp_f R s n P t]
      exact mapperHomologyMap_comp_eq R f _ _ _ n)
    (fun t => by
      rw [compIso_hom_app, transition_app, mapperHomologyPModule_map_g,
        structureMap_mapperHomologyPModule]
      simp only [centredMapperPairHomologyMap_app, centredMapperPairHomologyMapSymm_app,
        shift_obj, mapperHomologyPModule_obj]
      rw [← Category.assoc]
      rw [centredMapperPairHomologyMap_comp_g R s n P t]
      exact mapperHomologyMap_comp_eq R g _ _ _ n)

/-- A height-map pair bounds the real interleaving distance of its centred Mapper homology
modules by its parameter. -/
theorem realInterleavingDistance_centredMapperPair_le (P : HeightMapPair f g δ) :
    realInterleavingDistance
      (mapperHomologyPModule R f (centredCover s) (centredCoverRefinement s) n)
      (mapperHomologyPModule R g (centredCover s) (centredCoverRefinement s) n) ≤ δ :=
  (centredMapperPairInterleaving R s n P).distance_le

/-- The map-pair distance theorem specializes to the pointwise perturbation bound on one space.
-/
theorem realInterleavingDistance_centredMapperPair_le_ofUniformBound
    {g : C(X, ℝ)} [hg' : ∀ t, LinearOrder (ComponentIndex g (centredCover s t))]
    (hfg : ∀ x, |f x - g x| ≤ δ) :
    realInterleavingDistance
      (mapperHomologyPModule R f (centredCover s) (centredCoverRefinement s) n)
      (mapperHomologyPModule R g (centredCover s) (centredCoverRefinement s) n) ≤ δ := by
  exact realInterleavingDistance_centredMapperPair_le R s n
    (HeightMapPair.ofUniformBound hfg)

/-- Finite graph-PL inputs with a height-map pair have centred Mapper homology modules at real
interleaving distance at most the pair parameter. The theorem also holds without these finiteness
assumptions because it instantiates the general bound. -/
theorem realInterleavingDistance_centredMapperPair_graphPL_le
    {V V' : Type} [Finite V] [Finite V'] {G : SimpleGraph V} {G' : SimpleGraph V'}
    {h : V → ℝ} {h' : V' → ℝ}
    [∀ t, LinearOrder (ComponentIndex (plHeight G h) (centredCover s t))]
    [∀ t, LinearOrder (ComponentIndex (plHeight G' h') (centredCover s t))]
    (P : HeightMapPair (plHeight G h) (plHeight G' h') δ) :
    realInterleavingDistance
      (mapperHomologyPModule R (plHeight G h) (centredCover s)
        (centredCoverRefinement s) n)
      (mapperHomologyPModule R (plHeight G' h') (centredCover s)
        (centredCoverRefinement s) n) ≤ δ :=
  realInterleavingDistance_centredMapperPair_le R s n P

end

end TDA.Mapper
