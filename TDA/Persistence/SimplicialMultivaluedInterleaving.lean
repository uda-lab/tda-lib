import TDA.Persistence.SimplicialMultivaluedMapComposition

/-!
# Canonical interleavings from simplicial relations

Restricting a total simplicial relation preserves its actual canonical homology map.
When two total relations are simplicial with the same nonnegative shift and each round
trip contains the identity relation, their canonical maps satisfy both interleaving
triangles. The identity relation at the double shift gives the actual transition map.

Subrelation invariance permits every real degree. Interleavings use the existing finite
nonnegative parameters. The converse-relation specialization realizes CDSO Propositions
3.4 and 4.2's mechanism on ordered signed chains; arbitrary rings and the two-relation
constructor are library extensions, with the existing nonempty-face convention.
-/

universe u v

namespace TDA.Persistence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TDA.Filtration TDA.Simplicial
open scoped NNReal

noncomputable section

variable {X Y : Type u} [LinearOrder X] [LinearOrder Y]
variable (R : Type v) [Ring R]
variable {F : SimplicialFiltration ℝ X} {G : SimplicialFiltration ℝ Y}

/-- A total subrelation induces the same entire actual canonical transformation. -/
theorem multivaluedSimplicialHomologyMap_of_subset {C C' : SetRel X Y} {a : ℝ}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hC'T : Relator.LeftTotal (fun x y => (x,y) ∈ C'))
    (hC : IsShiftedSimplicialRelation F G a C) (hsub : C' ⊆ C) (n : ℕ) :
    multivaluedSimplicialHomologyMap R hC'T (hC.of_subset hsub) n =
      multivaluedSimplicialHomologyMap R hCT hC n := by
  let f : X → Y := fun x => Classical.choose (hC'T x)
  have hf : Function.graph f ⊆ C' := by
    intro ⟨x,y⟩ hxy
    change f x = y at hxy
    rw [← hxy]
    exact Classical.choose_spec (hC'T x)
  rw [multivaluedSimplicialHomologyMap_eq R hC'T _ hf,
    multivaluedSimplicialHomologyMap_eq R hCT hC (hf.trans hsub)]

private theorem identityTotal (V : Type*) :
    Relator.LeftTotal (fun x y => (x,y) ∈ (SetRel.id : SetRel V V)) :=
  fun x => ⟨x,rfl⟩

omit [LinearOrder X] in
private theorem identityRelation (F : SimplicialFiltration ℝ X) (γ : ℝ≥0) :
    IsShiftedSimplicialRelation F F (γ : ℝ) SetRel.id := by
  apply (isShiftedSimplicialRelation_graph_iff id).mpr
  intro t σ hσ
  exact (inclusionVertexMap (F.monotone (le_add_of_nonneg_right γ.coe_nonneg))).map_face σ hσ

/-- The identity relation uses the inclusion at a positive shift, not merely the zero unit. -/
private theorem identityMap_transition (F : SimplicialFiltration ℝ X) (γ : ℝ≥0) (n : ℕ) :
    multivaluedSimplicialHomologyMapNNReal R (identityTotal X) (identityRelation F γ) n =
      RealShift.transition γ (simplicialHomologyPModule R F n) := by
  apply NatTrans.ext
  funext t
  change (multivaluedSimplicialHomologyMap R (identityTotal X) (identityRelation F γ) n).app t = _
  rw [multivaluedSimplicialHomologyMap_app R _ _ (f := id) (Set.Subset.refl _)]
  change simplicialHomologyMap R _ n = simplicialHomologyIncl R _ n
  have hm : ((identityRelation F γ).of_subordinate (Set.Subset.refl _)).vertexMap t =
      inclusionVertexMap (F.monotone (le_add_of_nonneg_right γ.coe_nonneg)) :=
    VertexMap.ext (fun _ => rfl)
  rw [hm, simplicialHomologyMap_inclusion]

private theorem roundTrip_transition {C : SetRel X Y} {D : SetRel Y X} {ε : ℝ≥0}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hDT : Relator.LeftTotal (fun y x => (y,x) ∈ D))
    (hC : IsShiftedSimplicialRelation F G (ε : ℝ) C)
    (hD : IsShiftedSimplicialRelation G F (ε : ℝ) D)
    (hdiag : SetRel.id ⊆ C.comp D) (n : ℕ) :
    multivaluedSimplicialHomologyMapNNReal R hCT hC n ≫
      (RealShift.shift ε).map (multivaluedSimplicialHomologyMapNNReal R hDT hD n) ≫
      (RealShift.compIso ε ε (simplicialHomologyPModule R F n)).hom =
    RealShift.transition (ε + ε) (simplicialHomologyPModule R F n) := by
  rw [multivaluedSimplicialHomologyMapNNReal_comp]
  exact (multivaluedSimplicialHomologyMap_of_subset R _ (identityTotal X)
    (show IsShiftedSimplicialRelation F F ((ε + ε : ℝ≥0) : ℝ) (C.comp D) from hC.comp hD)
    hdiag n).symm.trans (identityMap_transition R F (ε + ε) n)

/-- Total forward/backward simplicial relations with diagonal-containing round trips give
an actual interleaving whose maps are their canonical homology transformations. -/
def multivaluedSimplicialHomologyInterleaving {C : SetRel X Y} {D : SetRel Y X} {ε : ℝ≥0}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hDT : Relator.LeftTotal (fun y x => (y,x) ∈ D))
    (hC : IsShiftedSimplicialRelation F G (ε : ℝ) C)
    (hD : IsShiftedSimplicialRelation G F (ε : ℝ) D)
    (hX : SetRel.id ⊆ C.comp D) (hY : SetRel.id ⊆ D.comp C) (n : ℕ) :
    RealInterleaving ε (simplicialHomologyPModule R F n) (simplicialHomologyPModule R G n) where
  φ := multivaluedSimplicialHomologyMapNNReal R hCT hC n
  ψ := multivaluedSimplicialHomologyMapNNReal R hDT hD n
  φ_ψ := roundTrip_transition R hCT hDT hC hD hX n
  ψ_φ := roundTrip_transition R hDT hCT hD hC hY n

/-- The forward field is exactly the existing canonical map of the forward relation. -/
@[simp] theorem multivaluedSimplicialHomologyInterleaving_φ
    {C : SetRel X Y} {D : SetRel Y X} {ε : ℝ≥0}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hDT : Relator.LeftTotal (fun y x => (y,x) ∈ D))
    (hC : IsShiftedSimplicialRelation F G (ε : ℝ) C)
    (hD : IsShiftedSimplicialRelation G F (ε : ℝ) D)
    (hX : SetRel.id ⊆ C.comp D) (hY : SetRel.id ⊆ D.comp C) (n : ℕ) :
    (multivaluedSimplicialHomologyInterleaving R hCT hDT hC hD hX hY n).φ =
      multivaluedSimplicialHomologyMapNNReal R hCT hC n := rfl

/-- The backward field is exactly the existing canonical map of the backward relation. -/
@[simp] theorem multivaluedSimplicialHomologyInterleaving_ψ
    {C : SetRel X Y} {D : SetRel Y X} {ε : ℝ≥0}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hDT : Relator.LeftTotal (fun y x => (y,x) ∈ D))
    (hC : IsShiftedSimplicialRelation F G (ε : ℝ) C)
    (hD : IsShiftedSimplicialRelation G F (ε : ℝ) D)
    (hX : SetRel.id ⊆ C.comp D) (hY : SetRel.id ⊆ D.comp C) (n : ℕ) :
    (multivaluedSimplicialHomologyInterleaving R hCT hDT hC hD hX hY n).ψ =
      multivaluedSimplicialHomologyMapNNReal R hDT hD n := rfl

/-- A relation and its native converse give the canonical correspondence interleaving.
Both totalities concern all ambient vertices, including ghosts. -/
def multivaluedSimplicialHomologyConverseInterleaving {C : SetRel X Y} {ε : ℝ≥0}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hIT : Relator.LeftTotal (fun y x => (y,x) ∈ C.inv))
    (hC : IsShiftedSimplicialRelation F G (ε : ℝ) C)
    (hI : IsShiftedSimplicialRelation G F (ε : ℝ) C.inv) (n : ℕ) :
    RealInterleaving ε (simplicialHomologyPModule R F n) (simplicialHomologyPModule R G n) :=
  multivaluedSimplicialHomologyInterleaving R hCT hIT hC hI
    (by rintro ⟨x,x'⟩ rfl; obtain ⟨y,hxy⟩ := hCT x; exact ⟨y,hxy,hxy⟩)
    (by rintro ⟨y,y'⟩ rfl; obtain ⟨x,hyx⟩ := hIT y; exact ⟨x,hyx,hyx⟩) n

end
end TDA.Persistence
