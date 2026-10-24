import TDA.Mapper.RefinementHomologyCappedTower
import TDA.Mapper.DomainMap
import TDA.Reeb.HeightMapPair
import TDA.Reeb.GraphPLHeight

/-!
# Capped centred Mapper diagrams from height-map pairs

A `HeightMapPair` between maps on possibly different spaces gives maps between the Mapper
complexes at any two capped stages whose radii satisfy the pair's domination inequality. These
maps are strictly natural in both stage indices. The pair's composite paths identify the
double-shift composites with the tower maps, so the two step modules are directly real-interleaved.
The constructible isometry then bounds the bottleneck distance of their capped centred diagrams.
-/

namespace TDA.Mapper

open CategoryTheory
open TDA.Reeb
open TDA.Reeb.GraphPL
open TDA.Simplicial
open TDA.Persistence
open TDA.Persistence.FiniteConstructible
open TDA.Persistence.RealShift
open TDA.Topology
open scoped NNReal ENNReal

noncomputable section

universe u

variable {X X' : Type u} [TopologicalSpace X] [TopologicalSpace X']
  {f : C(X, ℝ)} {g : C(X', ℝ)} {δ : ℝ≥0} {W : Type u}

/-- The vertex map between two capped stages induced by the forward map of a height-map pair.
The first step uses the pair's height control on `X`; the second applies its map of domains. -/
def cappedCentredPairVertexMap (P : HeightMapPair f g δ) (a s : ℝ) (ℓ : W → ℤ)
    {m m' : ℕ} (c : Fin m ↪o ℝ) (d : Fin m' ↪o ℝ)
    {i : Fin (m + 1)} {j : Fin (m' + 1)}
    (h : stageRadius c i + (δ : ℝ) ≤ stageRadius d j) :
    VertexMap (mapper f (fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)))
      (mapper g (fun w => (cappedCentredCover a s ℓ d j w : Set ℝ))) :=
  VertexMap.comp
    (mapperMap (ContinuousMap.id X)
      (cappedCentredPullbackRefinement (f := f) (g := g.comp P.φ) a s ℓ c d
        (fun x => (abs_sub_comm (f x) (g (P.φ x))).trans_le (P.hφ x)) h))
    (mapperDomainMap P.φ (by intro x; rfl)
      (fun w => (cappedCentredCover a s ℓ d j w : Set ℝ)))

/-- On a represented vertex, the forward stage map preserves the selected label and applies the
forward map of domains to its representative. -/
@[simp] theorem cappedCentredPairVertexMap_mk (P : HeightMapPair f g δ)
    (a s : ℝ) (ℓ : W → ℤ) {m m' : ℕ} (c : Fin m ↪o ℝ) (d : Fin m' ↪o ℝ)
    {i : Fin (m + 1)} {j : Fin (m' + 1)}
    (h : stageRadius c i + (δ : ℝ) ≤ stageRadius d j)
    (w : cappedIndex W i)
    (x : PullbackSpace f (fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) w) :
    cappedCentredPairVertexMap P a s ℓ c d h ⟨w, ZerothHomotopy.mk x⟩ =
      ⟨stageSelector i j (eq_zero_of_stageRadius_le h) w,
        ZerothHomotopy.mk ⟨P.φ x.1,
          mem_cappedCentredCover_of_stageRadius_le h w
            (P.hφ x.1) x.2⟩⟩ := by
  simp only [cappedCentredPairVertexMap, VertexMap.comp_apply,
    mapperMap_mk, mapperDomainMap_mk, pullbackRestrict_apply_val]
  rfl

/-- The vertex map from the second capped stage to the first, induced by the reverse map of a
height-map pair. -/
def cappedCentredPairVertexMapSymm (P : HeightMapPair f g δ) (a s : ℝ) (ℓ : W → ℤ)
    {m m' : ℕ} (c : Fin m ↪o ℝ) (d : Fin m' ↪o ℝ)
    {i : Fin (m + 1)} {j : Fin (m' + 1)}
    (h : stageRadius d j + (δ : ℝ) ≤ stageRadius c i) :
    VertexMap (mapper g (fun w => (cappedCentredCover a s ℓ d j w : Set ℝ)))
      (mapper f (fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))) :=
  cappedCentredPairVertexMap P.symm a s ℓ d c h

/-- On a represented vertex, the reverse stage map preserves the selected label and applies the
reverse map of domains to its representative. -/
@[simp] theorem cappedCentredPairVertexMapSymm_mk (P : HeightMapPair f g δ)
    (a s : ℝ) (ℓ : W → ℤ) {m m' : ℕ} (c : Fin m ↪o ℝ) (d : Fin m' ↪o ℝ)
    {i : Fin (m + 1)} {j : Fin (m' + 1)}
    (h : stageRadius d j + (δ : ℝ) ≤ stageRadius c i)
    (w : cappedIndex W j)
    (y : PullbackSpace g (fun w => (cappedCentredCover a s ℓ d j w : Set ℝ)) w) :
    cappedCentredPairVertexMapSymm P a s ℓ c d h ⟨w, ZerothHomotopy.mk y⟩ =
      ⟨stageSelector j i (eq_zero_of_stageRadius_le h) w,
        ZerothHomotopy.mk ⟨P.ψ y.1,
          mem_cappedCentredCover_of_stageRadius_le h w
            (P.hψ y.1) y.2⟩⟩ := by
  simp only [cappedCentredPairVertexMapSymm, cappedCentredPairVertexMap,
    VertexMap.comp_apply, mapperMap_mk, mapperDomainMap_mk,
    pullbackRestrict_apply_val]
  rfl

private theorem stageSelector_succ_succ {m m' : ℕ} (i : Fin m) (j : Fin m')
    (h : j.succ = 0 → i.succ = 0) (w : cappedIndex W i.succ) :
    stageSelector i.succ j.succ h w = w := by
  rfl

/-- The forward pair maps commute strictly with capped-stage refinements in both indices. -/
theorem cappedCentredPairVertexMap_natural (P : HeightMapPair f g δ)
    (a s : ℝ) (ℓ : W → ℤ) {m m' : ℕ} (c : Fin m ↪o ℝ) (d : Fin m' ↪o ℝ)
    {i i' : Fin (m + 1)} {j j' : Fin (m' + 1)}
    (hii : i ≤ i') (hjj : j ≤ j')
    (h : stageRadius c i + (δ : ℝ) ≤ stageRadius d j)
    (h' : stageRadius c i' + (δ : ℝ) ≤ stageRadius d j') :
    VertexMap.comp (mapperMap f (cappedCentredRefinement a s ℓ c hii))
        (cappedCentredPairVertexMap P a s ℓ c d h') =
      VertexMap.comp (cappedCentredPairVertexMap P a s ℓ c d h)
        (mapperMap g (cappedCentredRefinement a s ℓ d hjj)) := by
  apply VertexMap.ext
  rintro ⟨w, z⟩
  induction z using ZerothHomotopy.rec with
  | mk x =>
    obtain rfl | ⟨i₀, rfl⟩ := i.eq_zero_or_eq_succ
    · exact isEmptyElim w
    obtain rfl | ⟨i'₀, rfl⟩ := i'.eq_zero_or_eq_succ
    · exact False.elim (by simpa using hii)
    obtain rfl | ⟨j₀, rfl⟩ := j.eq_zero_or_eq_succ
    · exact False.elim (Fin.succ_ne_zero i₀ (eq_zero_of_stageRadius_le h rfl))
    obtain rfl | ⟨j'₀, rfl⟩ := j'.eq_zero_or_eq_succ
    · exact False.elim (Fin.succ_ne_zero i'₀ (eq_zero_of_stageRadius_le h' rfl))
    change cappedCentredPairVertexMap P a s ℓ c d h'
        (mapperMap f (cappedCentredRefinement a s ℓ c hii) ⟨w, ZerothHomotopy.mk x⟩) =
      mapperMap g (cappedCentredRefinement a s ℓ d hjj)
        (cappedCentredPairVertexMap P a s ℓ c d h ⟨w, ZerothHomotopy.mk x⟩)
    rw [mapperMap_mk]
    rw [cappedCentredPairVertexMap_mk]
    rw [cappedCentredPairVertexMap_mk]
    rw [mapperMap_mk]
    change (⟨w, ZerothHomotopy.mk ⟨P.φ x.1, _⟩⟩ :
        ComponentIndex g fun w => (cappedCentredCover a s ℓ d j'₀.succ w : Set ℝ)) =
      ⟨w, ZerothHomotopy.mk ⟨P.φ x.1, _⟩⟩
    rfl

private theorem joinedIn_cappedDoubleShift_f (a s : ℝ) (ℓ : W → ℤ)
    (P : HeightMapPair f g δ)
    {m : ℕ} (c : Fin m ↪o ℝ) {i k : Fin (m + 1)}
    (h : stageRadius c i + ((δ : ℝ) + (δ : ℝ)) ≤ stageRadius c k)
    (w : cappedIndex W i)
    (x : PullbackSpace f (fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) w) :
    JoinedIn (f ⁻¹' (cappedCentredCover a s ℓ c k
      (stageSelector i k (eq_zero_of_stageRadius_le h) w) : Set ℝ))
      x.1 (P.ψ (P.φ x.1)) := by
  obtain ⟨γ, hγ⟩ := P.hψφ x.1
  refine ⟨γ, fun q => ?_⟩
  change f (γ q) ∈ cappedCentredCover a s ℓ c k
    (stageSelector i k (eq_zero_of_stageRadius_le h) w)
  have hpath : |f (γ q) - f x.1| ≤ (δ : ℝ) + (δ : ℝ) := by
    simpa only [NNReal.coe_add] using hγ q
  exact mem_cappedCentredCover_of_stageRadius_le h w hpath x.2

private theorem joinedIn_cappedDoubleShift_g (a s : ℝ) (ℓ : W → ℤ)
    (P : HeightMapPair f g δ)
    {m : ℕ} (d : Fin m ↪o ℝ) {j k : Fin (m + 1)}
    (h : stageRadius d j + ((δ : ℝ) + (δ : ℝ)) ≤ stageRadius d k)
    (w : cappedIndex W j)
    (y : PullbackSpace g (fun w => (cappedCentredCover a s ℓ d j w : Set ℝ)) w) :
    JoinedIn (g ⁻¹' (cappedCentredCover a s ℓ d k
      (stageSelector j k (eq_zero_of_stageRadius_le h) w) : Set ℝ))
      y.1 (P.φ (P.ψ y.1)) :=
  joinedIn_cappedDoubleShift_f a s ℓ P.symm d h w y

/-- The composite of the forward and reverse stage maps is, as a vertex map, the capped tower
map through the double shift. -/
theorem cappedCentredPairVertexMap_comp (P : HeightMapPair f g δ)
    (a s : ℝ) (ℓ : W → ℤ) {m m' : ℕ} (c : Fin m ↪o ℝ) (d : Fin m' ↪o ℝ)
    {i : Fin (m + 1)} {j : Fin (m' + 1)} {k : Fin (m + 1)} (hik : i ≤ k)
    (hcd : stageRadius c i + (δ : ℝ) ≤ stageRadius d j)
    (hdc : stageRadius d j + (δ : ℝ) ≤ stageRadius c k) :
    VertexMap.comp (cappedCentredPairVertexMap P a s ℓ c d hcd)
        (cappedCentredPairVertexMapSymm P a s ℓ c d hdc) =
      mapperMap f (cappedCentredRefinement a s ℓ c hik) := by
  apply VertexMap.ext
  rintro ⟨w, z⟩
  induction z using ZerothHomotopy.rec with
  | mk x =>
    obtain rfl | ⟨i₀, rfl⟩ := i.eq_zero_or_eq_succ
    · exact isEmptyElim w
    obtain rfl | ⟨j₀, rfl⟩ := j.eq_zero_or_eq_succ
    · exact False.elim (Fin.succ_ne_zero i₀ (eq_zero_of_stageRadius_le hcd rfl))
    obtain rfl | ⟨k₀, rfl⟩ := k.eq_zero_or_eq_succ
    · exact False.elim (Fin.succ_ne_zero j₀ (eq_zero_of_stageRadius_le hdc rfl))
    have hdouble : stageRadius c i₀.succ + ((δ : ℝ) + (δ : ℝ)) ≤
        stageRadius c k₀.succ := by
      calc
        stageRadius c i₀.succ + ((δ : ℝ) + (δ : ℝ)) =
            (stageRadius c i₀.succ + (δ : ℝ)) + (δ : ℝ) := by rw [add_assoc]
        _ ≤ stageRadius d j₀.succ + (δ : ℝ) := add_le_add_left hcd (δ : EReal)
        _ ≤ stageRadius c k₀.succ := hdc
    change cappedCentredPairVertexMapSymm P a s ℓ c d hdc
        (cappedCentredPairVertexMap P a s ℓ c d hcd ⟨w, ZerothHomotopy.mk x⟩) =
      mapperMap f (cappedCentredRefinement a s ℓ c hik) ⟨w, ZerothHomotopy.mk x⟩
    rw [cappedCentredPairVertexMap_mk, cappedCentredPairVertexMapSymm_mk,
      mapperMap_mk]
    simp only [cappedCentredRefinement, stageSelector]
    change (⟨w, ZerothHomotopy.mk ⟨P.ψ (P.φ x.1), _⟩⟩ :
        ComponentIndex f fun w => (cappedCentredCover a s ℓ c k₀.succ w : Set ℝ)) =
      ⟨w, ZerothHomotopy.mk ⟨x.1, _⟩⟩
    apply congrArg (fun z : ZerothHomotopy
        (PullbackSpace f (fun w => (cappedCentredCover a s ℓ c k₀.succ w : Set ℝ)) w) =>
      (⟨w, z⟩ : ComponentIndex f fun w => (cappedCentredCover a s ℓ c k₀.succ w : Set ℝ)))
    have hxlarge := mem_cappedCentredCover_of_stageRadius_le hdouble w (z := f x.1)
      (y := f x.1) (by simp) x.2
    exact (mk_eq_of_joinedIn f _ (joinedIn_cappedDoubleShift_f a s ℓ P c hdouble w x)
      hxlarge (joinedIn_cappedDoubleShift_f a s ℓ P c hdouble w x).target_mem).symm

/-- The reverse-forward composite is the capped tower map through the double shift. -/
theorem cappedCentredPairVertexMapSymm_comp (P : HeightMapPair f g δ)
    (a s : ℝ) (ℓ : W → ℤ) {m m' : ℕ} (c : Fin m ↪o ℝ) (d : Fin m' ↪o ℝ)
    {i : Fin (m' + 1)} {j : Fin (m + 1)} {k : Fin (m' + 1)} (hik : i ≤ k)
    (hdc : stageRadius d i + (δ : ℝ) ≤ stageRadius c j)
    (hcd : stageRadius c j + (δ : ℝ) ≤ stageRadius d k) :
    VertexMap.comp (cappedCentredPairVertexMapSymm P a s ℓ c d hdc)
        (cappedCentredPairVertexMap P a s ℓ c d hcd) =
      mapperMap g (cappedCentredRefinement a s ℓ d hik) := by
  exact cappedCentredPairVertexMap_comp P.symm a s ℓ d c hik hdc hcd

section Interleaving

variable (k : Type u) [Field k] (a s : ℝ) (ℓ : W → ℤ) (n : ℕ)
  {m m' : ℕ} {c : Fin m ↪o ℝ} {d : Fin m' ↪o ℝ}
  [hf : ∀ i, LinearOrder (ComponentIndex f fun w =>
    (cappedCentredCover a s ℓ c i w : Set ℝ))]
  [hg : ∀ i, LinearOrder (ComponentIndex g fun w =>
    (cappedCentredCover a s ℓ d i w : Set ℝ))]

private theorem mapperHomologyPModule_cappedStep_map_f {t t' : ℝ} (h : t ⟶ t') :
    (mapperHomologyPModule k f (stepTower c fun i w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ))
        (stepRefinement c _ fun h => cappedCentredRefinement a s ℓ c h) n).map h =
      mapperHomologyMap k f
        (cappedCentredRefinement a s ℓ c ((cellIndex c).monotone (leOfHom h))) n := rfl

private theorem mapperHomologyPModule_cappedStep_map_g {t t' : ℝ} (h : t ⟶ t') :
    (mapperHomologyPModule k g (stepTower d fun i w =>
      (cappedCentredCover a s ℓ d i w : Set ℝ))
        (stepRefinement d _ fun h => cappedCentredRefinement a s ℓ d h) n).map h =
      mapperHomologyMap k g
        (cappedCentredRefinement a s ℓ d ((cellIndex d).monotone (leOfHom h))) n := rfl

/-- The stage maps induce a natural transformation from the first capped step module to the
`η`-shift of the second. -/
def cappedCentredPairHomologyMap (P : HeightMapPair f g δ) {η : ℝ≥0}
    (hcd : ∀ t, stageRadius c (cellIndex c t) + (δ : ℝ) ≤
      stageRadius d (cellIndex d (t + η))) :
    mapperHomologyPModule k f (stepTower c fun i w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ))
        (stepRefinement c _ fun h => cappedCentredRefinement a s ℓ c h) n ⟶
      (shift η).obj (mapperHomologyPModule k g (stepTower d fun i w =>
        (cappedCentredCover a s ℓ d i w : Set ℝ))
          (stepRefinement d _ fun h => cappedCentredRefinement a s ℓ d h) n) where
  app t := simplicialHomologyMap k
    (cappedCentredPairVertexMap P a s ℓ c d (hcd t)) n
  naturality t t' h := by
    have hii := (cellIndex c).monotone (leOfHom h)
    have ht : t + η ≤ t' + η := by linarith [leOfHom h]
    have hjj := (cellIndex d).monotone ht
    change mapperHomologyMap k f (cappedCentredRefinement a s ℓ c hii) n ≫
        simplicialHomologyMap k
          (cappedCentredPairVertexMap P a s ℓ c d (hcd t')) n =
      simplicialHomologyMap k
          (cappedCentredPairVertexMap P a s ℓ c d (hcd t)) n ≫
        mapperHomologyMap k g (cappedCentredRefinement a s ℓ d hjj) n
    rw [mapperHomologyMap_def, mapperHomologyMap_def,
      ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp,
      cappedCentredPairVertexMap_natural]

/-- The component of the forward homology transformation is induced by the forward stage map. -/
@[simp] theorem cappedCentredPairHomologyMap_app (P : HeightMapPair f g δ)
    {η : ℝ≥0} (hcd : ∀ t, stageRadius c (cellIndex c t) + (δ : ℝ) ≤
      stageRadius d (cellIndex d (t + η))) (t : ℝ) :
    (cappedCentredPairHomologyMap k a s ℓ n P hcd).app t =
      simplicialHomologyMap k
        (cappedCentredPairVertexMap P a s ℓ c d (hcd t)) n := rfl

/-- The reverse stage maps induce the natural transformation in the other direction. -/
def cappedCentredPairHomologyMapSymm (P : HeightMapPair f g δ) {η : ℝ≥0}
    (hdc : ∀ t, stageRadius d (cellIndex d t) + (δ : ℝ) ≤
      stageRadius c (cellIndex c (t + η))) :
    mapperHomologyPModule k g (stepTower d fun i w =>
      (cappedCentredCover a s ℓ d i w : Set ℝ))
        (stepRefinement d _ fun h => cappedCentredRefinement a s ℓ d h) n ⟶
      (shift η).obj (mapperHomologyPModule k f (stepTower c fun i w =>
        (cappedCentredCover a s ℓ c i w : Set ℝ))
          (stepRefinement c _ fun h => cappedCentredRefinement a s ℓ c h) n) :=
  cappedCentredPairHomologyMap k a s ℓ n P.symm hdc

/-- The component of the reverse homology transformation is induced by the reverse stage map. -/
@[simp] theorem cappedCentredPairHomologyMapSymm_app (P : HeightMapPair f g δ)
    {η : ℝ≥0} (hdc : ∀ t, stageRadius d (cellIndex d t) + (δ : ℝ) ≤
      stageRadius c (cellIndex c (t + η))) (t : ℝ) :
    (cappedCentredPairHomologyMapSymm k a s ℓ n P hdc).app t =
      simplicialHomologyMap k
        (cappedCentredPairVertexMapSymm P a s ℓ c d (hdc t)) n := rfl

private theorem cappedCentredPairHomologyMap_comp_f (P : HeightMapPair f g δ)
    {η : ℝ≥0} (hcd : ∀ t, stageRadius c (cellIndex c t) + (δ : ℝ) ≤
      stageRadius d (cellIndex d (t + η)))
    (hdc : ∀ t, stageRadius d (cellIndex d t) + (δ : ℝ) ≤
      stageRadius c (cellIndex c (t + η))) (t : ℝ) :
    simplicialHomologyMap k (cappedCentredPairVertexMap P a s ℓ c d (hcd t)) n ≫
      simplicialHomologyMap k
        (cappedCentredPairVertexMapSymm P a s ℓ c d (hdc (t + η))) n =
      mapperHomologyMap k f
        (cappedCentredRefinement a s ℓ c
          ((cellIndex c).monotone (by
            have hη : (0 : ℝ) ≤ (η : ℝ) := η.coe_nonneg
            linarith))) n := by
  rw [← simplicialHomologyMap_comp k _ _ n,
    cappedCentredPairVertexMap_comp P a s ℓ c d
      ((cellIndex c).monotone (by
        have hη : (0 : ℝ) ≤ (η : ℝ) := η.coe_nonneg
        linarith))
      (hcd t) (hdc (t + η)),
    ← mapperHomologyMap_def]

private theorem cappedCentredPairHomologyMap_comp_g (P : HeightMapPair f g δ)
    {η : ℝ≥0} (hcd : ∀ t, stageRadius c (cellIndex c t) + (δ : ℝ) ≤
      stageRadius d (cellIndex d (t + η)))
    (hdc : ∀ t, stageRadius d (cellIndex d t) + (δ : ℝ) ≤
      stageRadius c (cellIndex c (t + η))) (t : ℝ) :
    simplicialHomologyMap k
        (cappedCentredPairVertexMapSymm P a s ℓ c d (hdc t)) n ≫
      simplicialHomologyMap k (cappedCentredPairVertexMap P a s ℓ c d (hcd (t + η))) n =
      mapperHomologyMap k g
        (cappedCentredRefinement a s ℓ d
          ((cellIndex d).monotone (by
            have hη : (0 : ℝ) ≤ (η : ℝ) := η.coe_nonneg
            linarith))) n := by
  rw [← simplicialHomologyMap_comp k _ _ n,
    cappedCentredPairVertexMapSymm_comp P a s ℓ c d
      ((cellIndex d).monotone (by
        have hη : (0 : ℝ) ≤ (η : ℝ) := η.coe_nonneg
        linarith))
      (hdc t) (hcd (t + η)),
    ← mapperHomologyMap_def]

/-- A height-map pair directly real-interleaves the two capped centred step modules. -/
def cappedCentredPairInterleaving (P : HeightMapPair f g δ) {η : ℝ≥0}
    (hcd : ∀ t, stageRadius c (cellIndex c t) + (δ : ℝ) ≤
      stageRadius d (cellIndex d (t + η)))
    (hdc : ∀ t, stageRadius d (cellIndex d t) + (δ : ℝ) ≤
      stageRadius c (cellIndex c (t + η))) :
    RealInterleaving η
      (mapperHomologyPModule k f (stepTower c fun i w =>
        (cappedCentredCover a s ℓ c i w : Set ℝ))
          (stepRefinement c _ fun h => cappedCentredRefinement a s ℓ c h) n)
      (mapperHomologyPModule k g (stepTower d fun i w =>
        (cappedCentredCover a s ℓ d i w : Set ℝ))
          (stepRefinement d _ fun h => cappedCentredRefinement a s ℓ d h) n) :=
  RealInterleaving.ofApp (cappedCentredPairHomologyMap k a s ℓ n P hcd)
    (cappedCentredPairHomologyMapSymm k a s ℓ n P hdc)
    (fun t => by
      rw [compIso_hom_app, transition_app, mapperHomologyPModule_cappedStep_map_f,
        structureMap_mapperHomologyPModule]
      simp only [cappedCentredPairHomologyMap_app, cappedCentredPairHomologyMapSymm_app,
        shift_obj, mapperHomologyPModule_obj]
      rw [← Category.assoc]
      rw [cappedCentredPairHomologyMap_comp_f k a s ℓ n P hcd hdc t]
      exact mapperHomologyMap_comp_eq k f _ _ _ n)
    (fun t => by
      rw [compIso_hom_app, transition_app, mapperHomologyPModule_cappedStep_map_g,
        structureMap_mapperHomologyPModule]
      simp only [cappedCentredPairHomologyMap_app, cappedCentredPairHomologyMapSymm_app,
        shift_obj, mapperHomologyPModule_obj]
      rw [← Category.assoc]
      rw [cappedCentredPairHomologyMap_comp_g k a s ℓ n P hcd hdc t]
      exact mapperHomologyMap_comp_eq k g _ _ _ n)

end Interleaving

section Bounds

variable (k : Type u) [Field k] {W : Type u} (a s : ℝ) (ℓ : W → ℤ) (n : ℕ)

/-- If the stage radii of two capped centred Mapper towers dominate each other after shifting by
`η`, a `HeightMapPair` between their height maps bounds the bottleneck distance by `η`. The maps
act on the two step modules directly, so the domains may differ. -/
theorem bottleneck_cappedCentredDiagram_le_of_heightMapPair
    {X X' : Type u} [TopologicalSpace X] [TopologicalSpace X']
    {f : C(X, ℝ)} {g : C(X', ℝ)} {δ η : ℝ≥0} (P : HeightMapPair f g δ)
    {m m' : ℕ} {c : Fin m ↪o ℝ} {d : Fin m' ↪o ℝ}
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ))]
    [∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ)) n)]
    (hcd : ∀ t, stageRadius c (cellIndex c t) + (δ : ℝ) ≤
      stageRadius d (cellIndex d (t + η)))
    (hdc : ∀ t, stageRadius d (cellIndex d t) + (δ : ℝ) ≤
      stageRadius c (cellIndex c (t + η))) :
    bottleneck (cappedCentredDiagram k f a s ℓ c n)
      (cappedCentredDiagram k g a s ℓ d n) ≤ η := by
  calc
    bottleneck (cappedCentredDiagram k f a s ℓ c n)
        (cappedCentredDiagram k g a s ℓ d n) =
      realInterleavingDistance
        (mapperHomologyPModule k f (stepTower c fun i w =>
          (cappedCentredCover a s ℓ c i w : Set ℝ))
            (stepRefinement c _ fun h => cappedCentredRefinement a s ℓ c h) n)
        (mapperHomologyPModule k g (stepTower d fun i w =>
          (cappedCentredCover a s ℓ d i w : Set ℝ))
            (stepRefinement d _ fun h => cappedCentredRefinement a s ℓ d h) n) := by
          change bottleneck
            (moduleDiagram c
              (mapperHomologyPModule k f (stepTower c fun i w =>
                (cappedCentredCover a s ℓ c i w : Set ℝ))
                  (stepRefinement c _ fun h => cappedCentredRefinement a s ℓ c h) n) _)
            (moduleDiagram d
              (mapperHomologyPModule k g (stepTower d fun i w =>
                (cappedCentredCover a s ℓ d i w : Set ℝ))
                  (stepRefinement d _ fun h => cappedCentredRefinement a s ℓ d h) n) _) = _
          exact bottleneck_eq_distance
            (isConstructible_stepTower c _ k f _ n)
            (isConstructible_stepTower d _ k g _ n) _ _
    _ ≤ η := (cappedCentredPairInterleaving k a s ℓ n P hcd hdc).distance_le

/-- On one grid of mesh at most `μ`, the pair-bound for capped centred Mapper diagrams is at most
`δ + μ`. -/
theorem bottleneck_cappedCentredDiagram_pair_le
    {X X' : Type u} [TopologicalSpace X] [TopologicalSpace X']
    {f : C(X, ℝ)} {g : C(X', ℝ)} {m : ℕ} {c : Fin m ↪o ℝ}
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex g fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    {δ μ : ℝ≥0} (P : HeightMapPair f g δ)
    (hgap : ∀ i j : Fin m, j.val = i.val + 1 → c j ≤ c i + μ) :
    bottleneck (cappedCentredDiagram k f a s ℓ c n)
      (cappedCentredDiagram k g a s ℓ c n) ≤ (δ : ℝ≥0∞) + μ := by
  apply bottleneck_cappedCentredDiagram_le_of_heightMapPair k a s ℓ n P
  · intro t
    rw [NNReal.coe_add]
    exact stageRadius_add_le_of_gap c (by positivity) hgap t
  · intro t
    rw [NNReal.coe_add]
    exact stageRadius_add_le_of_gap c (by positivity) hgap t

/-- On a uniform grid, a pair parameter `δ = p * h` bounds the capped centred Mapper diagrams by
`δ`. -/
theorem bottleneck_cappedCentredDiagram_pair_uniformGrid_le
    {X X' : Type u} [TopologicalSpace X] [TopologicalSpace X']
    {f : C(X, ℝ)} {g : C(X', ℝ)} {δ : ℝ≥0}
    (P : HeightMapPair f g δ) (x₀ h : ℝ) (hh : 0 < h) (m : ℕ)
    [∀ i, LinearOrder (ComponentIndex f fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex g fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ))]
    [∀ i, Finite (Face (mapper g fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ)) n)]
    (p : ℕ) (hδ : (δ : ℝ) = p * h) :
    bottleneck
      (cappedCentredDiagram k f a s ℓ (uniformGrid x₀ h hh m) n)
      (cappedCentredDiagram k g a s ℓ (uniformGrid x₀ h hh m) n) ≤ δ := by
  apply bottleneck_cappedCentredDiagram_le_of_heightMapPair k a s ℓ n P
  · intro t
    rw [hδ]
    exact stageRadius_add_le_uniformGrid x₀ h hh m p t
  · intro t
    rw [hδ]
    exact stageRadius_add_le_uniformGrid x₀ h hh m p t

/-- The general pair bound recovers the one-domain capped centred perturbation theorem when the
pair is induced by a pointwise bound. -/
theorem bottleneck_cappedCentredDiagram_pair_le_ofUniformBound
    {X : Type u} [TopologicalSpace X] {f g : C(X, ℝ)} {m m' : ℕ}
    {c : Fin m ↪o ℝ} {d : Fin m' ↪o ℝ}
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ))]
    [∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ)) n)]
    {δ η : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ δ)
    (hcd : ∀ t, stageRadius c (cellIndex c t) + (δ : ℝ) ≤
      stageRadius d (cellIndex d (t + η)))
    (hdc : ∀ t, stageRadius d (cellIndex d t) + (δ : ℝ) ≤
      stageRadius c (cellIndex c (t + η))) :
    bottleneck (cappedCentredDiagram k f a s ℓ c n)
      (cappedCentredDiagram k g a s ℓ d n) ≤ η :=
  bottleneck_cappedCentredDiagram_le_of_heightMapPair k a s ℓ n
    (HeightMapPair.ofUniformBound hfg) hcd hdc

end Bounds

section GraphPL

variable (k : Type u) [Field k] {W : Type u} [Finite W]
  (a s : ℝ) (ℓ : W → ℤ) (n : ℕ)

/-- A pair of piecewise-linear heights on finite graphs gives the `δ + μ` capped centred
diagram bound on a grid of mesh at most `μ`; face-finiteness is supplied by the graph instances. -/
theorem bottleneck_cappedCentredDiagram_pair_plHeight_le
    {V V' : Type u} [Finite V] [Finite V'] {G : SimpleGraph V} {G' : SimpleGraph V'}
    {h : V → ℝ} {h' : V' → ℝ} {δ μ : ℝ≥0}
    (P : HeightMapPair (plHeight G h) (plHeight G' h') δ) {m : ℕ}
    {c : Fin m ↪o ℝ}
    [∀ i, LinearOrder (ComponentIndex (plHeight G h) fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, LinearOrder (ComponentIndex (plHeight G' h') fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ))]
    (hgap : ∀ i j : Fin m, j.val = i.val + 1 → c j ≤ c i + μ) :
    bottleneck (cappedCentredDiagram k (plHeight G h) a s ℓ c n)
      (cappedCentredDiagram k (plHeight G' h') a s ℓ c n) ≤ (δ : ℝ≥0∞) + μ :=
  bottleneck_cappedCentredDiagram_pair_le k a s ℓ n P hgap

/-- A pair of piecewise-linear heights on finite graphs gives the capped centred diagram bound
`δ` on a uniform grid when `δ = p * h`; face-finiteness is supplied by graph instances. -/
theorem bottleneck_cappedCentredDiagram_pair_plHeight_uniformGrid_le
    {V V' : Type u} [Finite V] [Finite V'] {G : SimpleGraph V} {G' : SimpleGraph V'}
    {h₁ : V → ℝ} {h₂ : V' → ℝ} {δ : ℝ≥0}
    (P : HeightMapPair (plHeight G h₁) (plHeight G' h₂) δ)
    (x₀ h : ℝ) (hh : 0 < h) (m : ℕ)
    [∀ i, LinearOrder (ComponentIndex (plHeight G h₁) fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ))]
    [∀ i, LinearOrder (ComponentIndex (plHeight G' h₂) fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ))]
    (p : ℕ) (hδ : (δ : ℝ) = p * h) :
    bottleneck
      (cappedCentredDiagram k (plHeight G h₁) a s ℓ (uniformGrid x₀ h hh m) n)
      (cappedCentredDiagram k (plHeight G' h₂) a s ℓ (uniformGrid x₀ h hh m) n) ≤ δ :=
  bottleneck_cappedCentredDiagram_pair_uniformGrid_le k a s ℓ n P x₀ h hh m p hδ

end GraphPL

end

end TDA.Mapper
