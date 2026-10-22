import TDA.Persistence.SimplicialMultivaluedMap

/-!
# Composition of canonical shifted homology maps

Finite intermediate witnesses compose the geometric relations, even when their images are
infinite. Composing global subordinate functions then proves composition of the canonical homology transformations by selector independence. The comparison transports the
index `(t+ε)+δ` to `t+(ε+δ)`; real degrees can have either sign.

This implements CDSO Proposition 3.5's mechanism in the ordered signed chain model over an
arbitrary ring. The paper fixes field coefficients; no geometric or singular comparison is
asserted here. homology retains a common vertex universe and independent vertex orders.
-/

universe u v

namespace TDA.Persistence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TDA.Simplicial TDA.Filtration
open scoped NNReal

noncomputable section

variable {X Y Z : Type u} [LinearOrder X] [LinearOrder Y] [LinearOrder Z]
variable (R : Type v) [Ring R]
variable {F : SimplicialFiltration ℝ X} {G : SimplicialFiltration ℝ Y}
variable {H : SimplicialFiltration ℝ Z} {ε δ : ℝ}

private def realReindexIso {a b : ℝ →o ℝ} (h : ∀ t, a t = b t)
    (M : PModule.{v,0,max u v} R ℝ) : reindex a M ≅ reindex b M :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun t => eqToIso (h t)) (by intros; apply Subsingleton.elim)) M

/-- Canonical index transport for two real shifts of simplicial homology. -/
def shiftedSimplicialHomologyCompIso (H : SimplicialFiltration ℝ Z) (ε δ : ℝ) (n : ℕ) :
    reindex (OrderHomClass.toOrderHom (OrderIso.addRight ε))
      (reindex (OrderHomClass.toOrderHom (OrderIso.addRight δ))
        (simplicialHomologyPModule R H n)) ≅
    reindex (OrderHomClass.toOrderHom (OrderIso.addRight (ε + δ)))
      (simplicialHomologyPModule R H n) :=
  realReindexIso R (a := (OrderHomClass.toOrderHom (OrderIso.addRight δ)).comp
    (OrderHomClass.toOrderHom (OrderIso.addRight ε)))
    (b := OrderHomClass.toOrderHom (OrderIso.addRight (ε + δ)))
    (fun t => add_assoc t ε δ) (simplicialHomologyPModule R H n)

/-- Its component is the homology structure map along associativity of indices. -/
@[simp] theorem shiftedSimplicialHomologyCompIso_hom_app
    (H : SimplicialFiltration ℝ Z) (ε δ : ℝ) (n : ℕ) (t : ℝ) :
    (shiftedSimplicialHomologyCompIso R H ε δ n).hom.app t =
      (simplicialHomologyPModule R H n).map (eqToHom (add_assoc t ε δ)) := rfl

/-- Maps of global shifted simplicial functions compose, including index transport. -/
theorem shiftedSimplicialHomologyMap_comp {f : X → Y} {g : Y → Z}
    (hf : IsShiftedSimplicial F G ε f) (hg : IsShiftedSimplicial G H δ g) (n : ℕ) :
    shiftedSimplicialHomologyMap R hf n ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight ε))
        (shiftedSimplicialHomologyMap R hg n) ≫
      (shiftedSimplicialHomologyCompIso R H ε δ n).hom =
    shiftedSimplicialHomologyMap R (hf.comp hg) n := by
  apply NatTrans.ext
  funext t
  change simplicialHomologyMap R (hf.vertexMap t) n ≫
      simplicialHomologyMap R (hg.vertexMap (t + ε)) n ≫
      simplicialHomologyIncl R (H.monotone (le_of_eq (add_assoc t ε δ))) n =
    simplicialHomologyMap R ((hf.comp hg).vertexMap t) n
  rw [← simplicialHomologyMap_inclusion, ← simplicialHomologyMap_comp,
    ← simplicialHomologyMap_comp]
  exact congrArg (fun q => simplicialHomologyMap R q n) (VertexMap.ext (fun _ => rfl))

/-- The second component is evaluated at `t+ε`, followed by the index equality map. -/
theorem shiftedSimplicialHomologyMap_comp_app {f : X → Y} {g : Y → Z}
    (hf : IsShiftedSimplicial F G ε f) (hg : IsShiftedSimplicial G H δ g) (n : ℕ) (t : ℝ) :
    (shiftedSimplicialHomologyMap R hf n).app t ≫
      (shiftedSimplicialHomologyMap R hg n).app (t + ε) ≫
      (simplicialHomologyPModule R H n).map (eqToHom (add_assoc t ε δ)) =
    (shiftedSimplicialHomologyMap R (hf.comp hg) n).app t :=
  congrArg (fun q => q.app t) (shiftedSimplicialHomologyMap_comp R hf hg n)

omit [LinearOrder X] [LinearOrder Y] [LinearOrder Z] in
private theorem comp_subordinate {C : SetRel X Y} {D : SetRel Y Z}
    {f : X → Y} {g : Y → Z} (hf : Function.graph f ⊆ C) (hg : Function.graph g ⊆ D) :
    Function.graph (g ∘ f) ⊆ C.comp D := by
  intro ⟨x,z⟩ hxz
  change g (f x) = z at hxz
  subst z
  exact ⟨f x, hf rfl, hg rfl⟩

/-- Canonical homology maps compose for ambient-total shifted simplicial relations. -/
theorem multivaluedSimplicialHomologyMap_comp {C : SetRel X Y} {D : SetRel Y Z}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hDT : Relator.LeftTotal (fun y z => (y,z) ∈ D))
    (hC : IsShiftedSimplicialRelation F G ε C)
    (hD : IsShiftedSimplicialRelation G H δ D) (n : ℕ) :
    multivaluedSimplicialHomologyMap R hCT hC n ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight ε))
        (multivaluedSimplicialHomologyMap R hDT hD n) ≫
      (shiftedSimplicialHomologyCompIso R H ε δ n).hom =
    multivaluedSimplicialHomologyMap R
      (Relator.LeftTotal.trans (r₁₃ := fun x z => (x,z) ∈ C.comp D)
        (fun _ y _ hxy hyz => ⟨y,hxy,hyz⟩) hCT hDT)
      (hC.comp hD) n := by
  let f : X → Y := fun x => Classical.choose (hCT x)
  let g : Y → Z := fun y => Classical.choose (hDT y)
  have hf : Function.graph f ⊆ C := by
    intro ⟨x,y⟩ hxy
    change f x = y at hxy
    rw [← hxy]
    exact Classical.choose_spec (hCT x)
  have hg : Function.graph g ⊆ D := by
    intro ⟨y,z⟩ hyz
    change g y = z at hyz
    rw [← hyz]
    exact Classical.choose_spec (hDT y)
  rw [multivaluedSimplicialHomologyMap_eq R hCT hC hf,
    multivaluedSimplicialHomologyMap_eq R hDT hD hg,
    multivaluedSimplicialHomologyMap_eq R _ (hC.comp hD) (comp_subordinate hf hg)]
  exact shiftedSimplicialHomologyMap_comp R _ _ n

/-- Component form of canonical composition, displaying the successive shifted level. -/
theorem multivaluedSimplicialHomologyMap_comp_app {C : SetRel X Y} {D : SetRel Y Z}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hDT : Relator.LeftTotal (fun y z => (y,z) ∈ D))
    (hC : IsShiftedSimplicialRelation F G ε C)
    (hD : IsShiftedSimplicialRelation G H δ D) (n : ℕ) (t : ℝ) :
    (multivaluedSimplicialHomologyMap R hCT hC n).app t ≫
      (multivaluedSimplicialHomologyMap R hDT hD n).app (t + ε) ≫
      (simplicialHomologyPModule R H n).map (eqToHom (add_assoc t ε δ)) =
    (multivaluedSimplicialHomologyMap R
      (Relator.LeftTotal.trans (r₁₃ := fun x z => (x,z) ∈ C.comp D)
        (fun _ y _ hxy hyz => ⟨y,hxy,hyz⟩) hCT hDT)
      (hC.comp hD) n).app t :=
  congrArg (fun q => q.app t) (multivaluedSimplicialHomologyMap_comp R hCT hDT hC hD n)

/-- At nonnegative degrees the comparison is the existing `RealShift.compIso`. -/
theorem shiftedSimplicialHomologyCompIso_nnreal (H : SimplicialFiltration ℝ Z)
    (ε δ : ℝ≥0) (n : ℕ) :
    shiftedSimplicialHomologyCompIso R H (ε : ℝ) (δ : ℝ) n =
      RealShift.compIso ε δ (simplicialHomologyPModule R H n) := by
  apply Iso.ext
  apply NatTrans.ext
  funext t
  rfl

/-- Canonical composition specializes to the existing nonnegative shift functor. -/
theorem multivaluedSimplicialHomologyMapNNReal_comp {C : SetRel X Y} {D : SetRel Y Z}
    {ε δ : ℝ≥0}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hDT : Relator.LeftTotal (fun y z => (y,z) ∈ D))
    (hC : IsShiftedSimplicialRelation F G (ε : ℝ) C)
    (hD : IsShiftedSimplicialRelation G H (δ : ℝ) D) (n : ℕ) :
    multivaluedSimplicialHomologyMapNNReal R hCT hC n ≫
      (RealShift.shift ε).map (multivaluedSimplicialHomologyMapNNReal R hDT hD n) ≫
      (RealShift.compIso ε δ (simplicialHomologyPModule R H n)).hom =
    multivaluedSimplicialHomologyMapNNReal R
      (Relator.LeftTotal.trans (r₁₃ := fun x z => (x,z) ∈ C.comp D)
        (fun _ y _ hxy hyz => ⟨y,hxy,hyz⟩) hCT hDT)
      (show IsShiftedSimplicialRelation F H ((ε + δ : ℝ≥0) : ℝ) (C.comp D) from hC.comp hD) n := by
  rw [← shiftedSimplicialHomologyCompIso_nnreal]
  exact multivaluedSimplicialHomologyMap_comp R hCT hDT hC hD n

end
end TDA.Persistence
