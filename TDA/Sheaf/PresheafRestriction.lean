import Mathlib.Topology.Category.TopCat.Opens

/-!
# Restrictions of presheaves along inclusions of opens

For a presheaf `P : (Opens X)ᵒᵖ ⥤ C` on a topological space `X`, the morphisms between two opens
form a subsingleton, so any two restrictions of `P` between the same opens agree
(`presheaf_map_eq`), and so do composites of restrictions with the same ends
(`presheaf_map_comp_map`, `presheaf_map_comp_map_eq`, `presheaf_map_comp_map_eq_comp`).
`restrictIso P h` is the restriction along an equality `h : U = V` of opens, as an isomorphism.
These are the restriction identities shared by the Alexandrov translation modules.
-/

set_option autoImplicit false

universe w u v

open CategoryTheory Opposite TopologicalSpace

namespace TDA.Sheaf

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C]

/-- Any two restrictions of a presheaf between the same opens agree. -/
theorem presheaf_map_eq (P : (Opens X)ᵒᵖ ⥤ C) {U V : (Opens X)ᵒᵖ} (f g : U ⟶ V) :
    P.map f = P.map g :=
  congrArg P.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- A composite of two restrictions is the restriction between the outer opens. -/
theorem presheaf_map_comp_map (P : (Opens X)ᵒᵖ ⥤ C) {U V W : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W) : P.map f ≫ P.map g = P.map h :=
  (P.map_comp f g).symm.trans (presheaf_map_eq P _ _)

/-- Two composites of two restrictions between the same opens agree. -/
theorem presheaf_map_comp_map_eq (P : (Opens X)ᵒᵖ ⥤ C) {U V V' W : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (f' : U ⟶ V') (g' : V' ⟶ W) :
    P.map f ≫ P.map g = P.map f' ≫ P.map g' :=
  (presheaf_map_comp_map P f g (f' ≫ g')).trans (P.map_comp f' g')

/-- A composite of two restrictions agrees with a composite of three between the same opens. -/
theorem presheaf_map_comp_map_eq_comp (P : (Opens X)ᵒᵖ ⥤ C)
    {U V V' V'' W : (Opens X)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (f' : U ⟶ V') (g' : V' ⟶ V'')
    (h' : V'' ⟶ W) : P.map f ≫ P.map g = P.map f' ≫ P.map g' ≫ P.map h' := by
  rw [presheaf_map_comp_map P f g (f' ≫ g' ≫ h'), P.map_comp, P.map_comp]

/-- The restriction of a presheaf along an equality of opens, as an isomorphism. -/
@[simps]
def restrictIso (P : (Opens X)ᵒᵖ ⥤ C) {U V : Opens X} (h : U = V) :
    P.obj (op U) ≅ P.obj (op V) where
  hom := P.map (homOfLE h.ge).op
  inv := P.map (homOfLE h.le).op
  hom_inv_id := by rw [← P.map_comp, ← P.map_id]; exact presheaf_map_eq P _ _
  inv_hom_id := by rw [← P.map_comp, ← P.map_id]; exact presheaf_map_eq P _ _

end TDA.Sheaf
