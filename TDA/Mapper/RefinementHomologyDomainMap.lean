import TDA.Mapper.DomainMap
import TDA.Mapper.RefinementHomologyCappedTower
import TDA.Reeb.GraphPLHeight

/-!
# Homology maps and persistence-module maps of height-preserving maps

Let `φ : C(X, X')` satisfy `f' (φ x) = f x`.  The Mapper vertex map `mapperDomainMap φ hφ U`
induces a map on the ordered-chain simplicial homology of `mapper f U` into that of
`mapper f' U`, over any ring and in every degree.  It commutes with the homology maps
`mapperHomologyMap` of every selected refinement of target families.  Hence, along a preorder of
cover families, the maps `mapperHomologyDomainMap` form a morphism of persistence modules
`mapperHomologyPModule R f cover r n ⟶ mapperHomologyPModule R f' cover r n`, compatible with
identities and composition.

A homeomorphism `e : X ≃ₜ X'` with `f' ∘ e = f` induces an isomorphism of these modules, whose
inverse is induced by `e.symm`.  Consequently the real interleaving distance of the two modules
over `ℝ` is `0`, and so is the bottleneck distance between the step diagrams of `f` and `f'` for
common step data with an empty initial family, and between their capped centred diagrams.  For
the piecewise-linear heights of two isomorphic finite-vertex graphs with matching vertex
heights, `realizationMap` of the isomorphism is such a homeomorphism.

Component orders of the two domains are independent supplied data, and no vertex map is assumed
monotone.  Equality of the diagrams themselves, compatibility of the domain maps with the
interleavings of cover maps, homotopy invariance and independence of the component orders are not
stated.
-/

namespace TDA.Mapper

open CategoryTheory
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence

noncomputable section

universe u v w p c

variable {X X' : Type u} {Y : Type v} {P : Type p}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [Preorder P]
variable (R : Type c) [Ring R]

section Homology

variable {f : C(X, Y)} {f' : C(X', Y)} (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x)
  {I J : Type w}

/-- The homology map of the Mapper vertex map induced by a map over `Y`. -/
def mapperHomologyDomainMap (U : I → Set Y) [LinearOrder (ComponentIndex f U)]
    [LinearOrder (ComponentIndex f' U)] (n : ℕ) :
    simplicialHomology (mapper f U) R n ⟶ simplicialHomology (mapper f' U) R n :=
  simplicialHomologyMap R (mapperDomainMap φ hφ U) n

/-- The identity map induces the identity on homology. -/
theorem mapperHomologyDomainMap_id (U : I → Set Y) [LinearOrder (ComponentIndex f U)] (n : ℕ) :
    mapperHomologyDomainMap R (ContinuousMap.id X) (fun _ => rfl) U n =
      𝟙 (simplicialHomology (mapper f U) R n) := by
  change simplicialHomologyMap R (mapperDomainMap (ContinuousMap.id X) (fun _ => rfl) U) n = _
  rw [mapperDomainMap_id, simplicialHomologyMap_id]

/-- Induced homology maps compose. -/
theorem mapperHomologyDomainMap_comp {X'' : Type u} [TopologicalSpace X''] {f'' : C(X'', Y)}
    (ψ : C(X', X'')) (hψ : ∀ x, f'' (ψ x) = f' x) (U : I → Set Y)
    [LinearOrder (ComponentIndex f U)] [LinearOrder (ComponentIndex f' U)]
    [LinearOrder (ComponentIndex f'' U)] (n : ℕ) :
    mapperHomologyDomainMap R (ψ.comp φ) (fun x => (hψ _).trans (hφ x)) U n =
      mapperHomologyDomainMap R φ hφ U n ≫ mapperHomologyDomainMap R ψ hψ U n := by
  change simplicialHomologyMap R (mapperDomainMap (ψ.comp φ) _ U) n = _
  rw [mapperDomainMap_comp φ hφ ψ hψ U]
  exact simplicialHomologyMap_comp R (mapperDomainMap φ hφ U) (mapperDomainMap ψ hψ U) n

/-- Equal maps induce equal homology maps. -/
theorem mapperHomologyDomainMap_congr {φ φ' : C(X, X')} (h : φ = φ')
    (hφ : ∀ x, f' (φ x) = f x) (hφ' : ∀ x, f' (φ' x) = f x) (U : I → Set Y)
    [LinearOrder (ComponentIndex f U)] [LinearOrder (ComponentIndex f' U)] (n : ℕ) :
    mapperHomologyDomainMap R φ hφ U n = mapperHomologyDomainMap R φ' hφ' U n := by
  subst h
  rfl

/-- The homology maps of a map over `Y` and of a selected refinement of target families commute. -/
theorem mapperHomologyMap_comp_mapperHomologyDomainMap {U : I → Set Y} {V : J → Set Y}
    [LinearOrder (ComponentIndex f U)] [LinearOrder (ComponentIndex f' U)]
    [LinearOrder (ComponentIndex f V)] [LinearOrder (ComponentIndex f' V)] (r : Refinement U V) (n : ℕ) :
    mapperHomologyMap R f r n ≫ mapperHomologyDomainMap R φ hφ V n =
      mapperHomologyDomainMap R φ hφ U n ≫ mapperHomologyMap R f' r n := by
  rw [mapperHomologyMap_def, mapperHomologyMap_def, mapperHomologyDomainMap,
    mapperHomologyDomainMap, ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp,
    mapperMap_comp_mapperDomainMap]

end Homology

section Tower

variable {f : C(X, Y)} {f' : C(X', Y)} (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x)
  {Index : P → Type w} (cover : (q : P) → Index q → Set Y)
  [∀ q, LinearOrder (ComponentIndex f (cover q))] [∀ q, LinearOrder (ComponentIndex f' (cover q))]
  (r : ∀ {q t : P}, q ≤ t → Refinement (cover q) (cover t)) (n : ℕ)

/-- A map over `Y` induces a morphism of Mapper homology persistence modules. -/
def mapperHomologyPModuleMap :
    mapperHomologyPModule R f cover r n ⟶ mapperHomologyPModule R f' cover r n where
  app q := mapperHomologyDomainMap R φ hφ (cover q) n
  naturality _ _ h :=
    mapperHomologyMap_comp_mapperHomologyDomainMap R φ hφ (r (leOfHom h)) n

@[simp]
theorem mapperHomologyPModuleMap_app (q : P) :
    (mapperHomologyPModuleMap R φ hφ cover r n).app q =
      mapperHomologyDomainMap R φ hφ (cover q) n :=
  rfl

/-- The identity map induces the identity morphism. -/
theorem mapperHomologyPModuleMap_id :
    mapperHomologyPModuleMap R (ContinuousMap.id X) (fun _ => rfl) cover r n =
      𝟙 (mapperHomologyPModule R f cover r n) := by
  exact NatTrans.ext (funext fun q => mapperHomologyDomainMap_id R (f := f) (cover q) n)

/-- Induced morphisms compose. -/
theorem mapperHomologyPModuleMap_comp {X'' : Type u} [TopologicalSpace X''] {f'' : C(X'', Y)}
    (ψ : C(X', X'')) (hψ : ∀ x, f'' (ψ x) = f' x)
    [∀ q, LinearOrder (ComponentIndex f'' (cover q))] :
    mapperHomologyPModuleMap R (ψ.comp φ) (fun x => (hψ _).trans (hφ x)) cover r n =
      mapperHomologyPModuleMap R φ hφ cover r n ≫ mapperHomologyPModuleMap R ψ hψ cover r n := by
  exact NatTrans.ext (funext fun q =>
    mapperHomologyDomainMap_comp R φ hφ ψ hψ (cover q) n)

/-- Equal maps induce equal morphisms. -/
theorem mapperHomologyPModuleMap_congr {φ φ' : C(X, X')} (h : φ = φ')
    (hφ : ∀ x, f' (φ x) = f x) (hφ' : ∀ x, f' (φ' x) = f x) :
    mapperHomologyPModuleMap R φ hφ cover r n = mapperHomologyPModuleMap R φ' hφ' cover r n := by
  exact NatTrans.ext (funext fun q => mapperHomologyDomainMap_congr R h hφ hφ' (cover q) n)

end Tower

section Homeomorph

variable {f : C(X, Y)} {f' : C(X', Y)} (e : X ≃ₜ X') (he : ∀ x, f' (e x) = f x)
  {Index : P → Type w} (cover : (q : P) → Index q → Set Y)
  [∀ q, LinearOrder (ComponentIndex f (cover q))] [∀ q, LinearOrder (ComponentIndex f' (cover q))]
  (r : ∀ {q t : P}, q ≤ t → Refinement (cover q) (cover t)) (n : ℕ)

private theorem symm_over (e : X ≃ₜ X') (he : ∀ x, f' (e x) = f x) (x' : X') :
    f (e.symm x') = f' x' := by
  rw [← he, e.apply_symm_apply]

/-- A homeomorphism over `Y` induces an isomorphism of Mapper homology persistence modules, with
inverse induced by the inverse homeomorphism. -/
def mapperHomologyPModuleIso :
    mapperHomologyPModule R f cover r n ≅ mapperHomologyPModule R f' cover r n where
  hom := mapperHomologyPModuleMap R (⟨e, e.continuous⟩ : C(X, X')) he cover r n
  inv := mapperHomologyPModuleMap R (⟨e.symm, e.symm.continuous⟩ : C(X', X)) (symm_over e he) cover r n
  hom_inv_id := by
    rw [← mapperHomologyPModuleMap_comp,
      mapperHomologyPModuleMap_congr R cover r n
        (φ' := ContinuousMap.id X) (ContinuousMap.ext e.symm_apply_apply) _ (fun _ => rfl),
      mapperHomologyPModuleMap_id]
  inv_hom_id := by
    rw [← mapperHomologyPModuleMap_comp,
      mapperHomologyPModuleMap_congr R cover r n
        (φ' := ContinuousMap.id X') (ContinuousMap.ext e.apply_symm_apply) _ (fun _ => rfl),
      mapperHomologyPModuleMap_id]

end Homeomorph

section Distance

variable {f : C(X, Y)} {f' : C(X', Y)} (e : X ≃ₜ X') (he : ∀ x, f' (e x) = f x)
  {Index : ℝ → Type w} (cover : (q : ℝ) → Index q → Set Y)
  [∀ q, LinearOrder (ComponentIndex f (cover q))] [∀ q, LinearOrder (ComponentIndex f' (cover q))]
  (r : ∀ {q t : ℝ}, q ≤ t → Refinement (cover q) (cover t)) (n : ℕ)

include e he in
/-- Homeomorphic domains over `Y` give real-indexed Mapper homology modules at real interleaving
distance `0`. -/
theorem realInterleavingDistance_mapperHomologyPModule_homeomorph :
    realInterleavingDistance (mapperHomologyPModule R f cover r n)
      (mapperHomologyPModule R f' cover r n) = 0 :=
  realInterleavingDistance_eq_zero_of_iso (mapperHomologyPModuleIso R e he cover r n)

end Distance

section Diagrams

open TDA.Persistence.FiniteConstructible

variable (k : Type u) [Field k] {f : C(X, Y)} {f' : C(X', Y)} (e : X ≃ₜ X')
  (he : ∀ x, f' (e x) = f x) {m : ℕ} (c : Fin m ↪o ℝ) {Index : Fin (m + 1) → Type u}
  (cover : (i : Fin (m + 1)) → Index i → Set Y)
  [∀ i, LinearOrder (ComponentIndex f (cover i))]
  [∀ i, LinearOrder (ComponentIndex f' (cover i))]
  (r : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j)) (n : ℕ)
  [∀ i, Finite (Face (mapper f (cover i)) n)] [∀ i, Finite (Face (mapper f' (cover i)) n)]
  [IsEmpty (Index 0)]

include e he in
/-- Homeomorphic domains over `Y` give step diagrams at bottleneck distance `0`. -/
theorem bottleneck_stepMapperDiagram_homeomorph :
    bottleneck (stepMapperDiagram k f c cover r n) (stepMapperDiagram k f' c cover r n) = 0 :=
  (bottleneck_eq_distance (isConstructible_stepTower c cover k f r n)
    (isConstructible_stepTower c cover k f' r n) _ _).trans
    (realInterleavingDistance_eq_zero_of_iso
      (mapperHomologyPModuleIso k e he (stepTower c cover) (stepRefinement c cover r) n))

end Diagrams

section Capped

variable (k : Type u) [Field k] {W : Type u} {f : C(X, ℝ)} {f' : C(X', ℝ)} (e : X ≃ₜ X')
  (he : ∀ x, f' (e x) = f x) (a s : ℝ) (ℓ : W → ℤ) {m : ℕ} (c : Fin m ↪o ℝ) (n : ℕ)
  [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
  [∀ i, LinearOrder (ComponentIndex f' fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
  [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
  [∀ i, Finite (Face (mapper f' fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]

include e he in
/-- Homeomorphic domains over `ℝ` give capped centred diagrams at bottleneck distance `0`. -/
theorem bottleneck_cappedCentredDiagram_homeomorph :
    bottleneck (cappedCentredDiagram k f a s ℓ c n) (cappedCentredDiagram k f' a s ℓ c n) = 0 :=
  bottleneck_stepMapperDiagram_homeomorph k e he c _ _ n

end Capped

section GraphPL

open TDA.Reeb.GraphRealization TDA.Reeb.GraphPL

variable {V V' : Type u} {G : SimpleGraph V} {G' : SimpleGraph V'}

/-- The realization map of a graph isomorphism is a homeomorphism of realizations, with inverse
the realization map of the inverse isomorphism. -/
def realizationHomeomorph (e : G ≃g G') : Realization G ≃ₜ Realization G' where
  toFun := realizationMap e.toHom
  invFun := realizationMap e.symm.toHom
  left_inv x := by
    rw [← ContinuousMap.comp_apply, ← realizationMap_comp, e.symm_toHom_comp_toHom,
      realizationMap_id]
    rfl
  right_inv x := by
    rw [← ContinuousMap.comp_apply, ← realizationMap_comp, e.toHom_comp_symm_toHom,
      realizationMap_id]
    rfl
  continuous_toFun := (realizationMap e.toHom).continuous
  continuous_invFun := (realizationMap e.symm.toHom).continuous

@[simp]
theorem realizationHomeomorph_apply (e : G ≃g G') (x : Realization G) :
    realizationHomeomorph e x = realizationMap e.toHom x :=
  rfl

/-- If vertex heights correspond along `e`, the piecewise-linear heights correspond along the
realization homeomorphism. -/
theorem plHeight_realizationHomeomorph (e : G ≃g G') {h : V → ℝ} {g : V' → ℝ}
    (hg : ∀ v, g (e v) = h v) (x : Realization G) :
    plHeight G' g (realizationHomeomorph e x) = plHeight G h x := by
  have key : (plHeight G' g).comp (realizationMap e.toHom) = plHeight G h :=
    plHeight_unique G h _ (fun v => hg v) fun d t => by
      change (1 - (t : ℝ)) * g (e d.fst) + (t : ℝ) * g (e d.snd) =
        (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd
      rw [hg, hg]
  exact congrArg (fun φ : C(Realization G, ℝ) => φ x) key

variable (k : Type u) [Field k] [Finite V] [Finite V'] {W : Type u} [Finite W]
  (a s : ℝ) (ℓ : W → ℤ) {m : ℕ} (c : Fin m ↪o ℝ) (n : ℕ)

/-- Isomorphic finite graphs with corresponding vertex heights have capped centred diagrams of
their piecewise-linear heights at bottleneck distance `0`. -/
theorem bottleneck_cappedCentredDiagram_plHeight_iso (e : G ≃g G') {h : V → ℝ} {g : V' → ℝ}
    (hg : ∀ v, g (e v) = h v)
    [∀ i, LinearOrder (ComponentIndex (plHeight G h) fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, LinearOrder (ComponentIndex (plHeight G' g) fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ))] :
    bottleneck (cappedCentredDiagram k (plHeight G h) a s ℓ c n)
      (cappedCentredDiagram k (plHeight G' g) a s ℓ c n) = 0 :=
  bottleneck_cappedCentredDiagram_homeomorph k (realizationHomeomorph e)
    (plHeight_realizationHomeomorph e hg) a s ℓ c n

end GraphPL

end

end TDA.Mapper
