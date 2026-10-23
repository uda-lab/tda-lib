import TDA.Mapper.RefinementHomology
import TDA.Persistence.RealInterleavingDistance

/-!
# Interleaved cover towers and Mapper homology persistence modules

Fix a continuous map `f : C(X, Y)`, a ring `R` and a degree `n`. A real-indexed cover tower
is a family `U t : IndexU t → Set Y` with a selected refinement `rU h` for every `h : s ≤ t`;
its Mapper homology module is `mapperHomologyPModule R f U rU n`. For `η : ℝ≥0`, selected
cover maps `ζ t : Refinement (U t) (V (t + η))` and `ξ t : Refinement (V t) (U (t + η))`
make the Mapper homology modules of two towers `η`-interleaved. The components of the two
interleaving maps are the homology maps induced by `ζ t` and `ξ t`; naturality and the two
double-shift identities hold because any two refinements between the same families induce
the same homology map. No commutation of the cover maps with the tower refinements, and no
identity or composition equation on any selector, is assumed. The real interleaving distance
of the two modules is therefore at most `η`, and the distance is subadditive along chains of
interleaved towers.

The Mapper complex of `f` along a family `U` is definitionally the Mapper complex of the
identity of `X` along the pulled-back family, with pulled-back refinements and the same
component orders, so the two persistence modules coincide.

For real-valued maps `f g : C(X, ℝ)` with `|f x - g x| ≤ δ` for every `x`, the pulled-back
centred interval towers `t ↦ (k * s - t, k * s + t)` admit identity-selector cover maps
shifting `t` by `δ`. Hence the Mapper homology modules of `f` and `g` along the centred tower
are `δ`-interleaved.

The tower is indexed by all of `ℝ`, and no finiteness, openness, coverage, field,
nonemptiness or local path-connectedness hypothesis enters. Nothing is claimed about
persistence diagrams, bottleneck distances, lower bounds on the interleaving distance, a
simplicial-tower interleaving up to contiguity, changes of the component linear orders, or
multinerve homology.
-/

namespace TDA.Mapper

open CategoryTheory
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence
open TDA.Persistence.RealShift
open scoped NNReal

noncomputable section

universe u v w c

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (R : Type c) [Ring R]

section Towers

variable (f : C(X, Y)) {IndexU IndexV : ℝ → Type w}
  {U : (t : ℝ) → IndexU t → Set Y} {V : (t : ℝ) → IndexV t → Set Y}
  [∀ t, LinearOrder (ComponentIndex f (U t))] [∀ t, LinearOrder (ComponentIndex f (V t))]

/-- Every transition map of a Mapper homology module is the homology map of the selected
refinement at the corresponding comparison. -/
theorem mapperHomologyPModule_map (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t)) (n : ℕ)
    {s t : ℝ} (h : s ⟶ t) :
    (mapperHomologyPModule R f U rU n).map h = mapperHomologyMap R f (rU (leOfHom h)) n :=
  rfl

/-- Selected cover maps into a tower shifted by `η` induce a natural map of Mapper homology
modules whose component at `t` is the homology map of the cover map at `t`. -/
def mapperHomologyShiftMap (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t))
    (rV : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t)) {η : ℝ≥0}
    (ζ : ∀ t, Refinement (U t) (V (t + η))) (n : ℕ) :
    mapperHomologyPModule R f U rU n ⟶ (shift η).obj (mapperHomologyPModule R f V rV n) where
  app t := mapperHomologyMap R f (ζ t) n
  naturality s t h := by
    change mapperHomologyMap R f (rU (leOfHom h)) n ≫ mapperHomologyMap R f (ζ t) n =
      mapperHomologyMap R f (ζ s) n ≫
        mapperHomologyMap R f (rV (add_le_add (leOfHom h) le_rfl)) n
    have hst : s + (η : ℝ) ≤ t + η := add_le_add (leOfHom h) le_rfl
    exact (mapperHomologyMap_comp_eq R f _ _ (Refinement.comp (ζ s) (rV hst)) n).trans
      (mapperHomologyMap_comp_eq R f _ _ _ n).symm

/-- The component of the induced map at `t` is the homology map of the cover map at `t`. -/
@[simp]
theorem mapperHomologyShiftMap_app (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t))
    (rV : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t)) {η : ℝ≥0}
    (ζ : ∀ t, Refinement (U t) (V (t + η))) (n : ℕ) (t : ℝ) :
    (mapperHomologyShiftMap R f rU rV ζ n).app t = mapperHomologyMap R f (ζ t) n :=
  rfl

/-- The induced map does not depend on the selected cover maps or on the selected tower
refinements. -/
theorem mapperHomologyShiftMap_app_eq (rU rU' : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t))
    (rV rV' : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t)) {η : ℝ≥0}
    (ζ ζ' : ∀ t, Refinement (U t) (V (t + η))) (n : ℕ) (t : ℝ) :
    (mapperHomologyShiftMap R f rU rV ζ n).app t =
      (mapperHomologyShiftMap R f rU' rV' ζ' n).app t :=
  mapperHomologyMap_eq R f (ζ t) (ζ' t) n

/-- For fixed tower refinements, the induced map does not depend on the selected cover
maps. -/
theorem mapperHomologyShiftMap_eq (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t))
    (rV : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t)) {η : ℝ≥0}
    (ζ ζ' : ∀ t, Refinement (U t) (V (t + η))) (n : ℕ) :
    mapperHomologyShiftMap R f rU rV ζ n = mapperHomologyShiftMap R f rU rV ζ' n :=
  NatTrans.ext (funext fun t => mapperHomologyShiftMap_app_eq R f rU rU rV rV ζ ζ' n t)

private theorem mapperHomologyMap_comp₃_eq {I J K L : Type w} {A : I → Set Y} {B : J → Set Y}
    {C : K → Set Y} {D : L → Set Y} [LinearOrder (ComponentIndex f A)]
    [LinearOrder (ComponentIndex f B)] [LinearOrder (ComponentIndex f C)]
    [LinearOrder (ComponentIndex f D)] (a : Refinement A B) (b : Refinement B C)
    (c : Refinement C D) (d : Refinement A D) (n : ℕ) :
    mapperHomologyMap R f a n ≫ mapperHomologyMap R f b n ≫ mapperHomologyMap R f c n =
      mapperHomologyMap R f d n := by
  rw [mapperHomologyMap_comp_eq R f b c (b.comp c), mapperHomologyMap_comp_eq R f a _ d]

/-- The double-shift identity: a cover map into the shifted second tower followed by a cover
map back into the first tower induces the double-shift transition. -/
private theorem mapperHomologyShiftMap_comp
    (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t))
    (rV : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t)) {η : ℝ≥0}
    (ζ : ∀ t, Refinement (U t) (V (t + η))) (ξ : ∀ t, Refinement (V t) (U (t + η)))
    (n : ℕ) (t : ℝ) :
    (mapperHomologyShiftMap R f rU rV ζ n).app t ≫
        (mapperHomologyShiftMap R f rV rU ξ n).app (t + (η : ℝ)) ≫
          (compIso η η (mapperHomologyPModule R f U rU n)).hom.app t =
      (transition (η + η) (mapperHomologyPModule R f U rU n)).app t := by
  rw [compIso_hom_app, transition_app, mapperHomologyPModule_map,
    structureMap_mapperHomologyPModule, mapperHomologyShiftMap_app,
    mapperHomologyShiftMap_app]
  exact mapperHomologyMap_comp₃_eq R f _ _ _ _ n

/-- Selected cover maps `ζ t : U t → V (t + η)` and `ξ t : V t → U (t + η)` give an
`η`-interleaving of the Mapper homology modules of the two towers. Its maps are the homology
maps induced by the cover maps; no commutation of the cover maps is assumed. -/
def mapperHomologyInterleaving (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t))
    (rV : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t)) {η : ℝ≥0}
    (ζ : ∀ t, Refinement (U t) (V (t + η))) (ξ : ∀ t, Refinement (V t) (U (t + η)))
    (n : ℕ) :
    RealInterleaving η (mapperHomologyPModule R f U rU n) (mapperHomologyPModule R f V rV n) :=
  RealInterleaving.ofApp (mapperHomologyShiftMap R f rU rV ζ n)
    (mapperHomologyShiftMap R f rV rU ξ n)
    (mapperHomologyShiftMap_comp R f rU rV ζ ξ n)
    (mapperHomologyShiftMap_comp R f rV rU ξ ζ n)

variable (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t))
  (rV : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t)) {η : ℝ≥0} (n : ℕ)

/-- The first interleaving map is the map induced by the cover maps into the second tower. -/
@[simp]
theorem mapperHomologyInterleaving_φ (ζ : ∀ t, Refinement (U t) (V (t + η)))
    (ξ : ∀ t, Refinement (V t) (U (t + η))) :
    (mapperHomologyInterleaving R f rU rV ζ ξ n).φ = mapperHomologyShiftMap R f rU rV ζ n :=
  rfl

/-- The second interleaving map is the map induced by the cover maps into the first tower. -/
@[simp]
theorem mapperHomologyInterleaving_ψ (ζ : ∀ t, Refinement (U t) (V (t + η)))
    (ξ : ∀ t, Refinement (V t) (U (t + η))) :
    (mapperHomologyInterleaving R f rU rV ζ ξ n).ψ = mapperHomologyShiftMap R f rV rU ξ n :=
  rfl

/-- The component of the first interleaving map at `t` is the homology map of `ζ t`. -/
@[simp]
theorem mapperHomologyInterleaving_φ_app (ζ : ∀ t, Refinement (U t) (V (t + η)))
    (ξ : ∀ t, Refinement (V t) (U (t + η))) (t : ℝ) :
    (mapperHomologyInterleaving R f rU rV ζ ξ n).φ.app t = mapperHomologyMap R f (ζ t) n :=
  rfl

/-- The component of the second interleaving map at `t` is the homology map of `ξ t`. -/
@[simp]
theorem mapperHomologyInterleaving_ψ_app (ζ : ∀ t, Refinement (U t) (V (t + η)))
    (ξ : ∀ t, Refinement (V t) (U (t + η))) (t : ℝ) :
    (mapperHomologyInterleaving R f rU rV ζ ξ n).ψ.app t = mapperHomologyMap R f (ξ t) n :=
  rfl

/-- The components of both interleaving maps do not depend on the selected cover maps or
tower refinements. -/
theorem mapperHomologyInterleaving_app_eq (ζ : ∀ t, Refinement (U t) (V (t + η)))
    (ξ : ∀ t, Refinement (V t) (U (t + η)))
    (rU' : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t))
    (rV' : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t))
    (ζ' : ∀ t, Refinement (U t) (V (t + η))) (ξ' : ∀ t, Refinement (V t) (U (t + η)))
    (t : ℝ) :
    (mapperHomologyInterleaving R f rU rV ζ ξ n).φ.app t =
        (mapperHomologyInterleaving R f rU' rV' ζ' ξ' n).φ.app t ∧
      (mapperHomologyInterleaving R f rU rV ζ ξ n).ψ.app t =
        (mapperHomologyInterleaving R f rU' rV' ζ' ξ' n).ψ.app t :=
  ⟨mapperHomologyMap_eq R f (ζ t) (ζ' t) n, mapperHomologyMap_eq R f (ξ t) (ξ' t) n⟩

/-- For fixed tower refinements, the interleaving does not depend on the selected cover
maps. -/
theorem mapperHomologyInterleaving_eq (ζ ζ' : ∀ t, Refinement (U t) (V (t + η)))
    (ξ ξ' : ∀ t, Refinement (V t) (U (t + η))) :
    mapperHomologyInterleaving R f rU rV ζ ξ n = mapperHomologyInterleaving R f rU rV ζ' ξ' n :=
  RealInterleaving.ext (mapperHomologyShiftMap_eq R f rU rV ζ ζ' n)
    (mapperHomologyShiftMap_eq R f rV rU ξ ξ' n)

/-- Mapper homology modules of towers with selected cover maps shifting by `η` in both
directions are at real interleaving distance at most `η`. -/
theorem realInterleavingDistance_mapperHomologyPModule_le
    (ζ : ∀ t, Refinement (U t) (V (t + η))) (ξ : ∀ t, Refinement (V t) (U (t + η))) :
    realInterleavingDistance (mapperHomologyPModule R f U rU n)
      (mapperHomologyPModule R f V rV n) ≤ η :=
  (mapperHomologyInterleaving R f rU rV ζ ξ n).distance_le

/-- Cover maps shifting by `η₁` between the first two towers and by `η₂` between the last two
bound the distance between the Mapper homology modules of the outer towers by `η₁ + η₂`. -/
theorem realInterleavingDistance_mapperHomologyPModule_le_add {IndexW : ℝ → Type w}
    {W : (t : ℝ) → IndexW t → Set Y} [∀ t, LinearOrder (ComponentIndex f (W t))]
    (rV : ∀ {s t : ℝ}, s ≤ t → Refinement (V s) (V t))
    (rW : ∀ {s t : ℝ}, s ≤ t → Refinement (W s) (W t)) {η₁ η₂ : ℝ≥0}
    (ζ₁ : ∀ t, Refinement (U t) (V (t + η₁))) (ξ₁ : ∀ t, Refinement (V t) (U (t + η₁)))
    (ζ₂ : ∀ t, Refinement (V t) (W (t + η₂))) (ξ₂ : ∀ t, Refinement (W t) (V (t + η₂))) :
    realInterleavingDistance (mapperHomologyPModule R f U rU n)
      (mapperHomologyPModule R f W rW n) ≤ η₁ + η₂ := by
  simpa only [ENNReal.coe_add] using
    ((mapperHomologyInterleaving R f rU rV ζ₁ ξ₁ n).trans
      (mapperHomologyInterleaving R f rV rW ζ₂ ξ₂ n)).distance_le

end Towers

section Pullback

variable (f : C(X, Y)) {Index : ℝ → Type w} (U : (t : ℝ) → Index t → Set Y)
  [hU : ∀ t, LinearOrder (ComponentIndex f (U t))]
  (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t)) (n : ℕ)

/-- The Mapper homology module of `f` along a tower is the module of the identity of `X`
along the pulled-back tower, with pulled-back refinements and the same component orders. -/
theorem mapperHomologyPModule_pullback :
    mapperHomologyPModule R f U rU n =
      @mapperHomologyPModule X X ℝ _ _ _ R _ (ContinuousMap.id X) Index
        (fun t => pullback f (U t)) hU (fun h => pullbackRefinement f (rU h)) n :=
  rfl

end Pullback

section Perturbation

/-- The centred interval family of spacing `s` and radius `t`: the member of label `k` is the
open interval of radius `t` about `k * s`. Every member is empty when `t ≤ 0`. -/
def centredCover (s t : ℝ) : ℤ → Set ℝ :=
  fun k => Set.Ioo (k * s - t) (k * s + t)

/-- Membership in a centred member is distance less than the radius from its centre. -/
theorem mem_centredCover_iff {s t y : ℝ} {k : ℤ} :
    y ∈ centredCover s t k ↔ |y - k * s| < t := by
  rw [centredCover, Set.mem_Ioo, abs_sub_lt_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Every member of a centred family of nonpositive radius is empty. -/
theorem centredCover_eq_empty {s t : ℝ} (ht : t ≤ 0) (k : ℤ) : centredCover s t k = ∅ :=
  Set.Ioo_eq_empty (by linarith)

/-- Increasing the radius refines the centred family with the identity selector. -/
def centredCoverRefinement (s : ℝ) {t t' : ℝ} (h : t ≤ t') :
    Refinement (centredCover s t) (centredCover s t') where
  selector k := k
  subset _ := Set.Ioo_subset_Ioo (by linarith) (by linarith)

/-- For nonzero spacing, the centred family covers `ℝ` once the radius exceeds half the
spacing. -/
theorem covers_centredCover {s t : ℝ} (hs : s ≠ 0) (ht : |s| / 2 < t) :
    Covers (centredCover s t) Set.univ := by
  intro y _
  refine ⟨round (y / s), mem_centredCover_iff.2 ?_⟩
  have hr := abs_sub_round (y / s)
  have hy : y - (round (y / s) : ℝ) * s = (y / s - round (y / s)) * s := by
    field_simp
  rw [hy, abs_mul]
  calc |y / s - round (y / s)| * |s| ≤ 1 / 2 * |s| :=
        mul_le_mul_of_nonneg_right hr (abs_nonneg s)
    _ < t := by linarith

variable {f g : C(X, ℝ)} {δ : ℝ≥0}

/-- A pointwise `δ`-bound moves the pulled-back centred member of radius `t` into the
pulled-back member of radius `t + δ` with the same label. -/
def centredPullbackRefinement (hfg : ∀ x, |f x - g x| ≤ δ) (s t : ℝ) :
    Refinement (pullback f (centredCover s t)) (pullback g (centredCover s (t + δ))) where
  selector k := k
  subset k x hx := by
    change f x ∈ centredCover s t k at hx
    change g x ∈ centredCover s (t + δ) k
    rw [mem_centredCover_iff] at hx ⊢
    have h := hfg x
    calc |g x - k * s| ≤ |g x - f x| + |f x - k * s| := abs_sub_le _ _ _
      _ < δ + t := by rw [abs_sub_comm]; exact add_lt_add_of_le_of_lt h hx
      _ = t + δ := add_comm _ _

variable (s : ℝ)
variable [hf : ∀ t, LinearOrder (ComponentIndex f (centredCover s t))]
  [hg : ∀ t, LinearOrder (ComponentIndex g (centredCover s t))]

/-- Real-valued maps at pointwise distance at most `δ` have `δ`-interleaved Mapper homology
modules along the centred tower of spacing `s`, in every degree and for all supplied component
orders. -/
def centredMapperHomologyInterleaving (hfg : ∀ x, |f x - g x| ≤ δ) (n : ℕ) :
    RealInterleaving δ (mapperHomologyPModule R f (centredCover s) (centredCoverRefinement s) n)
      (mapperHomologyPModule R g (centredCover s) (centredCoverRefinement s) n) :=
  @mapperHomologyInterleaving X X _ _ R _ (ContinuousMap.id X) (fun _ => ℤ) (fun _ => ℤ)
    (fun t => pullback f (centredCover s t)) (fun t => pullback g (centredCover s t)) hf hg
    (fun h => pullbackRefinement f (centredCoverRefinement s h))
    (fun h => pullbackRefinement g (centredCoverRefinement s h)) δ
    (centredPullbackRefinement hfg s)
    (centredPullbackRefinement (fun x => by rw [abs_sub_comm]; exact hfg x) s) n

/-- Perturbation stability: real-valued maps at pointwise distance at most `δ` have Mapper
homology modules along the centred tower at real interleaving distance at most `δ`. -/
theorem realInterleavingDistance_centredMapperHomology_le
    (hfg : ∀ x, |f x - g x| ≤ δ) (n : ℕ) :
    realInterleavingDistance
        (mapperHomologyPModule R f (centredCover s) (centredCoverRefinement s) n)
        (mapperHomologyPModule R g (centredCover s) (centredCoverRefinement s) n) ≤ δ :=
  (centredMapperHomologyInterleaving R s hfg n).distance_le

end Perturbation

end

end TDA.Mapper
