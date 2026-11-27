import TDA.Simplicial.VertexChainMap
import TDA.Simplicial.Cone

set_option autoImplicit false

/-!
# Simplicial homology with the vertex order chosen internally

`simplicialHomology` takes a linear order on the vertex type: the signed boundary enumerates
the vertices of a face increasingly.  The homology modules do not depend on the order.  For two
linear orders `o₁`, `o₂` on `V`, the maps of `simplicialHomologyMap` induced by the identity
vertex map in the two directions are mutually inverse (`simplicialHomologyIso_of_linearOrder`),
and they are natural in the complex and the vertex map
(`simplicialHomologyMap_comp_iso_of_linearOrder`).

`simplicialHomologyOrderFree` is the homology for the order chosen classically (the
well-ordering `WellOrderingRel`).  It is defined for an arbitrary vertex type, and
`simplicialHomologyOrderFreeIso` identifies it with `simplicialHomology` for every supplied
order.  `simplicialHomologyMapOrderFree` is the induced map of a vertex map between vertex types
in one universe; `simplicialHomologyMapOrderFree_iso_naturality` states its naturality against
the comparison isomorphisms.  Dimensions are transported through the isomorphism
(`finrank_simplicialHomologyOrderFree_eq`).
-/

namespace TDA.Simplicial

open CategoryTheory

noncomputable section

universe u v

section ExplicitOrders

variable {V : Type u} (o₁ o₂ : LinearOrder V) (K : PreAbstractSimplicialComplex V)
  (R : Type v) [Ring R] (n : ℕ)

/-- Homology for two linear orders on the vertices is isomorphic: the maps induced by the
identity vertex map in the two directions are mutually inverse. -/
def simplicialHomologyIso_of_linearOrder :
    @simplicialHomology V o₁ K R _ n ≅ @simplicialHomology V o₂ K R _ n where
  hom := @simplicialHomologyMap V V o₁ o₂ K K R _ (VertexMap.id K) n
  inv := @simplicialHomologyMap V V o₂ o₁ K K R _ (VertexMap.id K) n
  hom_inv_id := by
    rw [← @simplicialHomologyMap_comp V V V o₁ o₂ o₁ K K K R _ (VertexMap.id K)
      (VertexMap.id K) n]
    exact @simplicialHomologyMap_id V o₁ R _ K n
  inv_hom_id := by
    rw [← @simplicialHomologyMap_comp V V V o₂ o₁ o₂ K K K R _ (VertexMap.id K)
      (VertexMap.id K) n]
    exact @simplicialHomologyMap_id V o₂ R _ K n

variable {W : Type u} (p₁ p₂ : LinearOrder W) {L : PreAbstractSimplicialComplex W}

/-- The comparison isomorphisms of `simplicialHomologyIso_of_linearOrder` are natural in the
vertex map: for a vertex map `f`, the map `f` for the orders `o₁`, `p₁` followed by the
comparison `p₁ → p₂` equals the comparison `o₁ → o₂` followed by the map `f` for the orders
`o₂`, `p₂`. -/
theorem simplicialHomologyMap_comp_iso_of_linearOrder (f : VertexMap K L) :
    @simplicialHomologyMap V W o₁ p₁ K L R _ f n ≫
        (simplicialHomologyIso_of_linearOrder p₁ p₂ L R n).hom =
      (simplicialHomologyIso_of_linearOrder o₁ o₂ K R n).hom ≫
        @simplicialHomologyMap V W o₂ p₂ K L R _ f n := by
  change _ ≫ @simplicialHomologyMap W W p₁ p₂ L L R _ (VertexMap.id L) n =
    @simplicialHomologyMap V V o₁ o₂ K K R _ (VertexMap.id K) n ≫ _
  rw [← @simplicialHomologyMap_comp V W W o₁ p₁ p₂ K L L R _ f (VertexMap.id L) n,
    ← @simplicialHomologyMap_comp V V W o₁ o₂ p₂ K K L R _ (VertexMap.id K) f n]
  rfl

end ExplicitOrders

section OrderFree

variable {V : Type u} (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (n : ℕ)

/-- Simplicial homology with the vertex order chosen classically (the well-ordering
`WellOrderingRel`).  It is defined for an arbitrary vertex type; `simplicialHomologyOrderFreeIso` identifies it
with `simplicialHomology` for every supplied linear order. -/
def simplicialHomologyOrderFree : ModuleCat.{max u v} R :=
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  simplicialHomology K R n

/-- The order-free homology is isomorphic to the homology for every supplied linear order. -/
def simplicialHomologyOrderFreeIso [o : LinearOrder V] :
    simplicialHomologyOrderFree K R n ≅ simplicialHomology K R n :=
  simplicialHomologyIso_of_linearOrder (IsWellOrder.linearOrder WellOrderingRel) o K R n

variable {W : Type u} {K} {L : PreAbstractSimplicialComplex W}

/-- The map of order-free homology induced by a vertex map between vertex types in one
universe. -/
def simplicialHomologyMapOrderFree (f : VertexMap K L) :
    simplicialHomologyOrderFree K R n ⟶ simplicialHomologyOrderFree L R n :=
  @simplicialHomologyMap V W (IsWellOrder.linearOrder WellOrderingRel)
    (IsWellOrder.linearOrder WellOrderingRel) K L R _ f n

/-- Naturality of `simplicialHomologyMapOrderFree` against the comparison isomorphisms to the
homology for supplied orders. -/
theorem simplicialHomologyMapOrderFree_iso_naturality [o : LinearOrder V] [p : LinearOrder W]
    (f : VertexMap K L) :
    simplicialHomologyMapOrderFree R n f ≫ (simplicialHomologyOrderFreeIso L R n).hom =
      (simplicialHomologyOrderFreeIso K R n).hom ≫ simplicialHomologyMap R f n :=
  simplicialHomologyMap_comp_iso_of_linearOrder (IsWellOrder.linearOrder WellOrderingRel) o K R
    n (IsWellOrder.linearOrder WellOrderingRel) p f

end OrderFree

section Dimension

variable {V : Type u} (K : PreAbstractSimplicialComplex V) (k : Type v) [Field k] (n : ℕ)

/-- The dimension of the order-free homology equals the dimension of the homology for every
supplied linear order. -/
theorem finrank_simplicialHomologyOrderFree_eq [LinearOrder V] :
    Module.finrank k (simplicialHomologyOrderFree K k n) =
      Module.finrank k (simplicialHomology K k n) :=
  (simplicialHomologyOrderFreeIso K k n).toLinearEquiv.finrank_eq

/-- The full finite nonempty complex has order-free degree-zero homology of dimension one. -/
theorem finrank_simplicialHomologyOrderFree_top_zero [Finite V] [Nonempty V] :
    Module.finrank k (simplicialHomologyOrderFree (⊤ : PreAbstractSimplicialComplex V) k 0) =
      1 :=
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  finrank_simplicialHomology_top_zero k

end Dimension

end

end TDA.Simplicial
