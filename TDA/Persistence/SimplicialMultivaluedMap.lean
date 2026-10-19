import TDA.Filtration.ShiftedSimplicialMap
import TDA.Persistence.Simplicial
import TDA.Persistence.RealInterleaving
import TDA.Simplicial.ContiguityHomotopy
import Mathlib.Algebra.Order.Group.OrderIso

/-!
# Canonical shifted homology maps

A global shifted simplicial function gives a natural transformation with the existing actual
homology maps as components. A left-total simplicial relation gives the same transformation
for every subordinate function: finite joint images prove contiguity, and the actual signed
chain homotopy proves equality on homology. This realizes the mechanism of CDSO Proposition
3.3 over an arbitrary ring, with all real shifts and the library's nonempty-face convention.
-/

universe u v

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration
open scoped NNReal

noncomputable section

variable {X Y : Type u} [LinearOrder X] [LinearOrder Y]
variable (R : Type v) [Ring R]
variable {F : SimplicialFiltration ℝ X} {G : SimplicialFiltration ℝ Y} {ε : ℝ}

/-- Actual homology maps of one global function form a degree-ε natural transformation. -/
def shiftedSimplicialHomologyMap {f : X → Y} (hf : IsShiftedSimplicial F G ε f) (n : ℕ) :
    simplicialHomologyPModule R F n ⟶
      reindex (OrderHomClass.toOrderHom (OrderIso.addRight ε)) (simplicialHomologyPModule R G n) where
  app t := simplicialHomologyMap R (hf.vertexMap t) n
  naturality {t s} h := by
    change simplicialHomologyIncl R (F.monotone (leOfHom h)) n ≫
        simplicialHomologyMap R (hf.vertexMap s) n =
      simplicialHomologyMap R (hf.vertexMap t) n ≫
        simplicialHomologyIncl R (G.monotone (show t + ε ≤ s + ε from add_le_add (leOfHom h) le_rfl)) n
    rw [← simplicialHomologyMap_inclusion, ← simplicialHomologyMap_inclusion,
      ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp]
    exact congrArg (fun q => simplicialHomologyMap R q n) (VertexMap.ext (fun _ => rfl))

/-- A component is the actual map of the stage vertex map. -/
@[simp] theorem shiftedSimplicialHomologyMap_app {f : X → Y}
    (hf : IsShiftedSimplicial F G ε f) (n : ℕ) (t : ℝ) :
    (shiftedSimplicialHomologyMap R hf n).app t =
      simplicialHomologyMap R (hf.vertexMap t) n := rfl

private def selector {C : SetRel X Y} (hC : Relator.LeftTotal (fun x y => (x,y) ∈ C)) :
    X → Y := fun x => Classical.choose (hC x)

omit [LinearOrder X] [LinearOrder Y] in
private theorem selector_subordinate {C : SetRel X Y}
    (hC : Relator.LeftTotal (fun x y => (x,y) ∈ C)) : Function.graph (selector hC) ⊆ C := by
  intro ⟨x,y⟩ hxy
  change selector hC x = y at hxy
  rw [← hxy]
  exact Classical.choose_spec (hC x)

/-- Canonical actual homology transformation of a total shifted simplicial relation.
Selection uses all ambient vertices once, independently of the level. -/
def multivaluedSimplicialHomologyMap {C : SetRel X Y}
    (hTotal : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hC : IsShiftedSimplicialRelation F G ε C) (n : ℕ) :
    simplicialHomologyPModule R F n ⟶
      reindex (OrderHomClass.toOrderHom (OrderIso.addRight ε)) (simplicialHomologyPModule R G n) :=
  shiftedSimplicialHomologyMap R (hC.of_subordinate (selector_subordinate hTotal)) n

/-- The entire canonical transformation equals that of every subordinate global function. -/
theorem multivaluedSimplicialHomologyMap_eq {C : SetRel X Y}
    (hTotal : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hC : IsShiftedSimplicialRelation F G ε C) {f : X → Y}
    (hf : Function.graph f ⊆ C) (n : ℕ) :
    multivaluedSimplicialHomologyMap R hTotal hC n =
      shiftedSimplicialHomologyMap R (hC.of_subordinate hf) n := by
  apply NatTrans.ext
  funext t
  exact Contiguous.simplicialHomologyMap_eq R
    (hC.contiguous (selector_subordinate hTotal) hf t) n

/-- Canonical components are the existing actual homology maps of any selector. -/
theorem multivaluedSimplicialHomologyMap_app {C : SetRel X Y}
    (hTotal : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hC : IsShiftedSimplicialRelation F G ε C) {f : X → Y}
    (hf : Function.graph f ⊆ C) (n : ℕ) (t : ℝ) :
    (multivaluedSimplicialHomologyMap R hTotal hC n).app t =
      simplicialHomologyMap R ((hC.of_subordinate hf).vertexMap t) n := by
  rw [multivaluedSimplicialHomologyMap_eq R hTotal hC hf n]
  rfl

/-- On a function graph the canonical map is exactly its ordinary actual map. -/
theorem multivaluedSimplicialHomologyMap_graph {f : X → Y}
    (hf : IsShiftedSimplicial F G ε f) (n : ℕ) :
    multivaluedSimplicialHomologyMap R (C := Function.graph f)
      (fun x => ⟨f x, rfl⟩) ((isShiftedSimplicialRelation_graph_iff f).mpr hf) n =
      shiftedSimplicialHomologyMap R hf n :=
  multivaluedSimplicialHomologyMap_eq R _ _ (Set.Subset.refl _) n

/-- Nonnegative real reindexing agrees with the existing nonnegative shift functor. -/
theorem simplicialHomology_reindex_nnreal (G : SimplicialFiltration ℝ Y)
    (ε : ℝ≥0) (n : ℕ) :
    reindex (OrderHomClass.toOrderHom (OrderIso.addRight (ε : ℝ))) (simplicialHomologyPModule R G n) =
      (RealShift.shift ε).obj (simplicialHomologyPModule R G n) := rfl

/-- The canonical map at a nonnegative shift has the existing `RealShift` target. -/
def multivaluedSimplicialHomologyMapNNReal {C : SetRel X Y} {δ : ℝ≥0}
    (hTotal : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hC : IsShiftedSimplicialRelation F G (δ : ℝ) C) (n : ℕ) :
    simplicialHomologyPModule R F n ⟶
      (RealShift.shift δ).obj (simplicialHomologyPModule R G n) :=
  multivaluedSimplicialHomologyMap R hTotal hC n

/-- Nonnegative compatibility preserves the actual canonical map, including its components. -/
@[simp] theorem multivaluedSimplicialHomologyMapNNReal_eq {C : SetRel X Y} {δ : ℝ≥0}
    (hTotal : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hC : IsShiftedSimplicialRelation F G (δ : ℝ) C) (n : ℕ) :
    multivaluedSimplicialHomologyMapNNReal R hTotal hC n =
      multivaluedSimplicialHomologyMap R hTotal hC n := rfl

/-- The zero-shift identity function gives the identity after the existing zero identification. -/
theorem shiftedSimplicialHomologyMap_id (F : SimplicialFiltration ℝ X) (n : ℕ) :
    shiftedSimplicialHomologyMap R (isShiftedSimplicial_id F) n ≫
      (RealShift.zeroIso (simplicialHomologyPModule R F n)).hom =
        𝟙 (simplicialHomologyPModule R F n) := by
  have he : shiftedSimplicialHomologyMap R (isShiftedSimplicial_id F) n =
      RealShift.transition 0 (simplicialHomologyPModule R F n) := by
    apply NatTrans.ext
    funext t
    have hm : (isShiftedSimplicial_id F).vertexMap t =
        inclusionVertexMap (show F t ≤ F (t + 0) by simp) := by
      apply VertexMap.ext
      intro x
      rfl
    change simplicialHomologyMap R _ n = _
    rw [hm, simplicialHomologyMap_inclusion]
    rfl
  rw [he]
  exact RealShift.transition_zero _

end
end TDA.Persistence
