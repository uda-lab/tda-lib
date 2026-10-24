import TDA.Mapper.Refinement
import TDA.Simplicial.VertexChainMap

/-!
# Mapper vertex maps induced by height-preserving maps

Let `φ : C(X, X')` satisfy `f' (φ x) = f x` for all `x`, where `f : C(X, Y)` and `f' : C(X', Y)`.
For every indexed target family `U`, the restriction of `φ` to the inverse images over the members
of `U` acts on path components, and so on the component indices of `f` and `f'`.  This index map
is a selected refinement of the component cover of `f` into the pullback along `φ` of the component
cover of `f'`.  It is therefore a vertex map `mapper f U → mapper f' U`, sending the class of a
point `x` over `i` to the class of `φ x` over `i`.

The construction preserves identities and composition, and commutes strictly with the vertex maps
`mapperMap f R` and `mapperMap f' R` of every selected refinement `R` of target families.  The two
domains may lie in different universes, and `φ` need not be injective, surjective or a
homeomorphism.  No ordering of component indices is involved at this level.
-/

namespace TDA.Mapper

open TDA.Topology
open TDA.Simplicial

noncomputable section

universe u u' v w z

variable {X : Type u} {X' : Type u'} {Y : Type v} {I : Type w} {J : Type z}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
  {f : C(X, Y)} {f' : C(X', Y)}

/-- The restriction of `φ` to the inverse images over the member `U i`. -/
def pullbackRestrict (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (U : I → Set Y) (i : I) :
    C(PullbackSpace f U i, PullbackSpace f' U i) where
  toFun x := ⟨φ x.1, by rw [hφ]; exact x.2⟩
  continuous_toFun := by fun_prop

@[simp]
theorem pullbackRestrict_apply_val (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (U : I → Set Y)
    (i : I) (x : PullbackSpace f U i) : (pullbackRestrict φ hφ U i x).1 = φ x.1 :=
  rfl

/-- The map on component indices induced by a map over `Y`: the class over `i` is sent to its
image class over the same `i`. -/
def domainIndexMap (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (U : I → Set Y) :
    ComponentIndex f U → ComponentIndex f' U :=
  fun a => ⟨a.1, componentMap (pullbackRestrict φ hφ U a.1) a.2⟩

@[simp]
theorem domainIndexMap_mk (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (U : I → Set Y) (i : I)
    (x : PullbackSpace f U i) :
    domainIndexMap φ hφ U ⟨i, ZerothHomotopy.mk x⟩ =
      ⟨i, ZerothHomotopy.mk (pullbackRestrict φ hφ U i x)⟩ :=
  rfl

theorem domainIndexMap_fst (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (U : I → Set Y)
    (a : ComponentIndex f U) : (domainIndexMap φ hφ U a).1 = a.1 :=
  rfl

/-- The identity map induces the identity on component indices. -/
theorem domainIndexMap_id (U : I → Set Y) :
    domainIndexMap (ContinuousMap.id X) (fun _ => rfl) U = (id : ComponentIndex f U → _) := by
  funext a
  rcases a with ⟨i, c⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  change componentMap _ c = c
  rw [show pullbackRestrict (ContinuousMap.id X) (fun _ => rfl) U i =
      ContinuousMap.id (PullbackSpace f U i) from rfl]
  exact congrFun componentMap_id c

/-- Induced index maps compose. -/
theorem domainIndexMap_comp {X'' : Type*} [TopologicalSpace X''] {f'' : C(X'', Y)}
    (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (ψ : C(X', X'')) (hψ : ∀ x, f'' (ψ x) = f' x)
    (U : I → Set Y) :
    domainIndexMap (ψ.comp φ) (fun x => (hψ _).trans (hφ x)) U =
      domainIndexMap ψ hψ U ∘ domainIndexMap φ hφ U := by
  funext a
  rcases a with ⟨i, c⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  change componentMap _ c = componentMap (pullbackRestrict ψ hψ U i)
    (componentMap (pullbackRestrict φ hφ U i) c)
  rw [show pullbackRestrict (ψ.comp φ) (fun x => (hψ _).trans (hφ x)) U i =
      (pullbackRestrict ψ hψ U i).comp (pullbackRestrict φ hφ U i) from rfl]
  exact congrFun (componentMap_comp _ _) c

/-- A point of the member over `a` is sent by `φ` into the member over its image index. -/
def componentDomainRefinement (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (U : I → Set Y) :
    Refinement (componentCover f U) (pullback φ (componentCover f' U)) where
  selector := domainIndexMap φ hφ U
  subset a x hx := by
    rcases a with ⟨i, c⟩
    rcases hx with ⟨hxi, hclass⟩
    change ZerothHomotopy.mk (⟨x, hxi⟩ : PullbackSpace f U i) = c at hclass
    refine ⟨by rw [hφ]; exact hxi, ?_⟩
    change componentMap (pullbackRestrict φ hφ U i)
        (ZerothHomotopy.mk (⟨x, hxi⟩ : PullbackSpace f U i)) =
      componentMap (pullbackRestrict φ hφ U i) c
    exact congrArg _ hclass

/-- The vertex map `mapper f U → mapper f' U` induced by a map `φ` with `f' ∘ φ = f`. -/
def mapperDomainMap (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (U : I → Set Y) :
    VertexMap (mapper f U) (mapper f' U) :=
  (nerveMap (componentDomainRefinement φ hφ U)).comp
    (inclusionVertexMap (nerve_pullback_le φ (componentCover f' U)))

@[simp]
theorem mapperDomainMap_apply (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (U : I → Set Y)
    (a : ComponentIndex f U) : mapperDomainMap φ hφ U a = domainIndexMap φ hφ U a :=
  rfl

/-- A represented component is sent to the class of the image point over the same member. -/
@[simp]
theorem mapperDomainMap_mk (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (U : I → Set Y) (i : I)
    (x : PullbackSpace f U i) :
    mapperDomainMap φ hφ U ⟨i, ZerothHomotopy.mk x⟩ =
      ⟨i, ZerothHomotopy.mk (pullbackRestrict φ hφ U i x)⟩ :=
  rfl

/-- The identity map induces the identity vertex map. -/
theorem mapperDomainMap_id (U : I → Set Y) :
    mapperDomainMap (ContinuousMap.id X) (fun _ => rfl) U = VertexMap.id (mapper f U) :=
  VertexMap.ext fun a => congrFun (domainIndexMap_id U) a

/-- Induced vertex maps compose. -/
theorem mapperDomainMap_comp {X'' : Type*} [TopologicalSpace X''] {f'' : C(X'', Y)}
    (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (ψ : C(X', X'')) (hψ : ∀ x, f'' (ψ x) = f' x)
    (U : I → Set Y) :
    mapperDomainMap (ψ.comp φ) (fun x => (hψ _).trans (hφ x)) U =
      VertexMap.comp (mapperDomainMap φ hφ U) (mapperDomainMap ψ hψ U) :=
  VertexMap.ext fun a => congrFun (domainIndexMap_comp φ hφ ψ hψ U) a

/-- Equal maps induce equal vertex maps. -/
theorem mapperDomainMap_congr {φ φ' : C(X, X')} (h : φ = φ') (hφ : ∀ x, f' (φ x) = f x)
    (hφ' : ∀ x, f' (φ' x) = f x) (U : I → Set Y) :
    mapperDomainMap φ hφ U = mapperDomainMap φ' hφ' U := by
  subst h
  rfl

/-- Maps with `ψ ∘ φ = id` induce vertex maps with composite the identity. -/
theorem mapperDomainMap_comp_eq_id (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x) (ψ : C(X', X))
    (hψ : ∀ x, f (ψ x) = f' x) (hψφ : ψ.comp φ = ContinuousMap.id X) (U : I → Set Y) :
    VertexMap.comp (mapperDomainMap φ hφ U) (mapperDomainMap ψ hψ U) =
      VertexMap.id (mapper f U) := by
  rw [← mapperDomainMap_comp, mapperDomainMap_congr hψφ _ (fun _ => rfl),
    mapperDomainMap_id]

/-- The domain map commutes strictly with the vertex maps of every selected refinement of target
families. -/
theorem mapperMap_comp_mapperDomainMap (φ : C(X, X')) (hφ : ∀ x, f' (φ x) = f x)
    {U : I → Set Y} {V : J → Set Y} (R : Refinement U V) :
    VertexMap.comp (mapperMap f R) (mapperDomainMap φ hφ V) =
      VertexMap.comp (mapperDomainMap φ hφ U) (mapperMap f' R) := by
  apply VertexMap.ext
  rintro ⟨i, c⟩
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

end

end TDA.Mapper
