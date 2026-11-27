import TDA.Sheaf.PresheafRestriction
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Basic.ENNReal.Basic

/-!
# Sheaf shifts and interleavings along a family of translations

For `X : TopCat.{w}`, a `SpaceTranslation X` is a family of continuous maps `T ε : X ⟶ X`,
`ε : ℝ≥0`, whose preimages shrink opens (`map_le`: `T ε⁻¹(V) ≤ V`) and compose additively
(`map_comp`: `T δ⁻¹(T ε⁻¹(V)) = T (ε + δ)⁻¹(V)`). For `τ : SpaceTranslation X` and a category `C`:

* `τ.shift C ε` is pushforward along `T ε`, so `(τ.shift C ε F)(V) = F(T ε⁻¹(V))`;
  `τ.transition C ε : 𝟭 ⟶ τ.shift C ε` is restriction along `T ε⁻¹(V) ≤ V`, and
  `τ.compIso C ε δ : τ.shift C δ ⋙ τ.shift C ε ≅ τ.shift C (ε + δ)` is restriction along the
  equality of preimages; `transition_add` composes two transitions.
* `τ.Interleaving ε F G` has arrows `F ⟶ τ.shift C ε G`, `G ⟶ τ.shift C ε F` and the two
  double-shift equations, in the orientation of `RealInterleaving` and `CoordinateInterleaving`,
  with `ext`, `symm`, `refl` and `congr`; `τ.interleavingDistance F G` is the extended infimum of
  the radii of witnesses, invariant under isomorphisms (`interleavingDistance_congr`).

The translations of the ray space and of the orthant space (`TDA.Sheaf.OrthantSheaf`) are
instances.
-/

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite TopologicalSpace TopCat
open scoped NNReal ENNReal

namespace TDA.Sheaf

/-- A family of translations of a space: continuous maps `T ε : X ⟶ X` for `ε : ℝ≥0` whose
preimages shrink opens and compose additively. -/
structure SpaceTranslation (X : TopCat.{w}) where
  /-- The translation by `ε`. -/
  T : ℝ≥0 → (X ⟶ X)
  /-- The preimage of an open under a translation is contained in it. -/
  map_le (ε : ℝ≥0) (V : Opens X) : (Opens.map (T ε)).obj V ≤ V
  /-- Translating by `ε` and then by `δ` is translating by `ε + δ`. -/
  map_comp (ε δ : ℝ≥0) (V : Opens X) :
    (Opens.map (T δ)).obj ((Opens.map (T ε)).obj V) = (Opens.map (T (ε + δ))).obj V

namespace SpaceTranslation

noncomputable section

variable {X : TopCat.{w}} (τ : SpaceTranslation X)

/-! ## Shifts and transitions -/

section Shift

variable (C : Type u) [Category.{v} C]

/-- A composite of three restrictions is the restriction between the outer opens. -/
private theorem map_comp_map_comp (P : (Opens X)ᵒᵖ ⥤ C) {U V W Z : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ Z) (k : U ⟶ Z) :
    P.map f ≫ P.map g ≫ P.map h = P.map k :=
  (congrArg (P.map f ≫ ·) (presheaf_map_comp_map P g h (g ≫ h))).trans
    (presheaf_map_comp_map P _ _ _)

/-- The sheaf shift: pushforward along `T ε`, so `(shift ε F)(V) = F(T ε⁻¹(V))`. -/
def shift (ε : ℝ≥0) : X.Sheaf C ⥤ X.Sheaf C :=
  TopCat.Sheaf.pushforward C (τ.T ε)

/-- The transition `F ⟶ shift ε F`: restriction along `T ε⁻¹(V) ≤ V`. -/
def transition (ε : ℝ≥0) : 𝟭 (X.Sheaf C) ⟶ τ.shift C ε where
  app F := ObjectProperty.homMk
    { app := fun V => F.presheaf.map (homOfLE (τ.map_le ε V.unop)).op
      naturality := fun _ _ _ => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        exact presheaf_map_comp_map_eq _ _ _ _ _ }
  naturality _ _ φ := by
    apply CategoryTheory.Sheaf.hom_ext
    ext V
    exact (φ.hom.naturality _).symm

/-- The addition isomorphism `shift δ ⋙ shift ε ≅ shift (ε + δ)`. -/
def compIso (ε δ : ℝ≥0) : τ.shift C δ ⋙ τ.shift C ε ≅ τ.shift C (ε + δ) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (NatIso.ofComponents
      (fun V => TDA.Sheaf.restrictIso F.presheaf (τ.map_comp ε δ V.unop))
      (fun _ => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        exact presheaf_map_comp_map_eq _ _ _ _ _)))
    (fun φ => by
      apply CategoryTheory.Sheaf.hom_ext
      ext V
      exact (φ.hom.naturality _).symm)

variable {C}

@[simp]
theorem shift_obj_presheaf_obj (ε : ℝ≥0) (F : X.Sheaf C) (V : Opens X) :
    ((τ.shift C ε).obj F).presheaf.obj (op V) = F.presheaf.obj (op ((Opens.map (τ.T ε)).obj V)) :=
  rfl

@[simp]
theorem shift_map_hom_app (ε : ℝ≥0) {F G : X.Sheaf C} (φ : F ⟶ G) (V : Opens X) :
    ((τ.shift C ε).map φ).hom.app (op V) = φ.hom.app (op ((Opens.map (τ.T ε)).obj V)) :=
  rfl

@[simp]
theorem transition_app_hom_app (ε : ℝ≥0) (F : X.Sheaf C) (V : Opens X) :
    ((τ.transition C ε).app F).hom.app (op V) = F.presheaf.map (homOfLE (τ.map_le ε V)).op :=
  rfl

@[simp]
theorem compIso_hom_app_hom_app (ε δ : ℝ≥0) (F : X.Sheaf C) (V : Opens X) :
    ((τ.compIso C ε δ).hom.app F).hom.app (op V) =
      F.presheaf.map (homOfLE (τ.map_comp ε δ V).ge).op :=
  rfl

/-- Naturality of the addition isomorphism. -/
@[reassoc]
theorem compIso_hom_naturality (ε δ : ℝ≥0) {F G : X.Sheaf C} (φ : F ⟶ G) :
    (τ.shift C ε).map ((τ.shift C δ).map φ) ≫ (τ.compIso C ε δ).hom.app G =
      (τ.compIso C ε δ).hom.app F ≫ (τ.shift C (ε + δ)).map φ :=
  (τ.compIso C ε δ).hom.naturality φ

/-- Naturality of the transition. -/
@[reassoc]
theorem transition_naturality (ε : ℝ≥0) {F G : X.Sheaf C} (φ : F ⟶ G) :
    φ ≫ (τ.transition C ε).app G = (τ.transition C ε).app F ≫ (τ.shift C ε).map φ :=
  (τ.transition C ε).naturality φ

/-- Two transitions compose to the transition by the sum. -/
theorem transition_add (ε δ : ℝ≥0) (F : X.Sheaf C) :
    (τ.transition C ε).app F ≫ (τ.shift C ε).map ((τ.transition C δ).app F) ≫
        (τ.compIso C ε δ).hom.app F =
      (τ.transition C (ε + δ)).app F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext V
  exact map_comp_map_comp _ _ _ _ _ _

end Shift

/-! ## Interleavings -/

section Interleaving

variable {C : Type u} [Category.{v} C]

/-- An `ε`-interleaving of sheaves along `τ`, in the orientation of `RealInterleaving` and
`CoordinateInterleaving`. -/
structure Interleaving (ε : ℝ≥0) (F G : X.Sheaf C) where
  /-- The arrow from the first sheaf to the shifted second sheaf. -/
  φ : F ⟶ (τ.shift C ε).obj G
  /-- The arrow from the second sheaf to the shifted first sheaf. -/
  ψ : G ⟶ (τ.shift C ε).obj F
  /-- The first composite is the double-shift transition. -/
  φ_ψ : φ ≫ (τ.shift C ε).map ψ ≫ (τ.compIso C ε ε).hom.app F = (τ.transition C (ε + ε)).app F
  /-- The second composite is the double-shift transition. -/
  ψ_φ : ψ ≫ (τ.shift C ε).map φ ≫ (τ.compIso C ε ε).hom.app G = (τ.transition C (ε + ε)).app G

namespace Interleaving

variable {τ} {ε : ℝ≥0} {F G : X.Sheaf C}

/-- Two witnesses agree when their two arrows agree. -/
@[ext]
theorem ext {i j : τ.Interleaving ε F G} (hφ : i.φ = j.φ) (hψ : i.ψ = j.ψ) : i = j := by
  cases i; cases j; cases hφ; cases hψ; rfl

/-- Interchange the two arrows. -/
def symm (i : τ.Interleaving ε F G) : τ.Interleaving ε G F :=
  ⟨i.ψ, i.φ, i.ψ_φ, i.φ_ψ⟩

variable (τ) in
/-- A sheaf is interleaved with itself by its transitions. -/
def refl (ε : ℝ≥0) (F : X.Sheaf C) : τ.Interleaving ε F F :=
  ⟨(τ.transition C ε).app F, (τ.transition C ε).app F, τ.transition_add ε ε F,
    τ.transition_add ε ε F⟩

/-- Transport a witness along isomorphisms of both sheaves. -/
def congr {F' G' : X.Sheaf C} (i : τ.Interleaving ε F G) (e : F ≅ F') (d : G ≅ G') :
    τ.Interleaving ε F' G' := by
  have comp {A B A' B' : X.Sheaf C}
      (f : A ⟶ (τ.shift C ε).obj B) (g : B ⟶ (τ.shift C ε).obj A)
      (h : f ≫ (τ.shift C ε).map g ≫ (τ.compIso C ε ε).hom.app A =
        (τ.transition C (ε + ε)).app A)
      (a : A ≅ A') (b : B ≅ B') :
      (a.inv ≫ f ≫ (τ.shift C ε).map b.hom) ≫
        (τ.shift C ε).map (b.inv ≫ g ≫ (τ.shift C ε).map a.hom) ≫
          (τ.compIso C ε ε).hom.app A' = (τ.transition C (ε + ε)).app A' := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, b.hom_inv_id, (τ.shift C ε).map_id, Category.id_comp]
    rw [compIso_hom_naturality]
    have hh := congrArg (fun m => a.inv ≫ m ≫ (τ.shift C (ε + ε)).map a.hom) h
    simp only [Category.assoc] at hh
    rw [hh, ← transition_naturality, Iso.inv_hom_id_assoc]
  exact ⟨e.inv ≫ i.φ ≫ (τ.shift C ε).map d.hom,
    d.inv ≫ i.ψ ≫ (τ.shift C ε).map e.hom,
    comp i.φ i.ψ i.φ_ψ e d, comp i.ψ i.φ i.ψ_φ d e⟩

end Interleaving

/-- The extended-infimum interleaving distance of sheaves along `τ`. -/
def interleavingDistance (F G : X.Sheaf C) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (τ.Interleaving ε F G)), (ε : ℝ≥0∞)

/-- A witness bounds the distance by its radius. -/
theorem interleavingDistance_le {ε : ℝ≥0} {F G : X.Sheaf C} (i : τ.Interleaving ε F G) :
    τ.interleavingDistance F G ≤ ε :=
  iInf₂_le ε ⟨i⟩

/-- Isomorphisms preserve the distance in both arguments. -/
theorem interleavingDistance_congr {F G F' G' : X.Sheaf C} (e : F ≅ F') (d : G ≅ G') :
    τ.interleavingDistance F G = τ.interleavingDistance F' G' :=
  le_antisymm (le_iInf₂ fun ε ⟨i⟩ => iInf₂_le ε ⟨i.congr e.symm d.symm⟩)
    (le_iInf₂ fun ε ⟨i⟩ => iInf₂_le ε ⟨i.congr e d⟩)

end Interleaving

end

end SpaceTranslation

end TDA.Sheaf
