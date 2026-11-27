import TDA.Sheaf.BandDistance

/-!
# Band convolution distance on the bounded derived category

Bounded witnesses use the restricted band functors, composition, and augmentation.
The inclusion into the bounded-below derived category identifies both witness types and
preserves the extended distance.
-/

noncomputable section

open CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Sheaf.BandConvolution

variable (k : Type) [Ring k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

local notation "Dᵇ[" k "]" => DerivedCategory.Bounded (realLine.Sheaf (ModuleCat k))
local notation "ι[" k "]" => boundedToPlus (realLine.Sheaf (ModuleCat k))

/-- A witness between bounded objects, expressed using the bounded band functors. -/
structure WitnessB {ε : ℝ} (hε : 0 ≤ ε) (F G : Dᵇ[k]) where
  hom : (TB k ε).obj F ⟶ G
  inv : (TB k ε).obj G ⟶ F
  hom_inv : (TCompB k hε hε).inv.app F ≫ (TB k ε).map hom ≫ inv =
    (augB k (add_nonneg hε hε)).app F
  inv_hom : (TCompB k hε hε).inv.app G ≫ (TB k ε).map inv ≫ hom =
    (augB k (add_nonneg hε hε)).app G

variable {k} {ε : ℝ} {hε : 0 ≤ ε} {F G : Dᵇ[k]}

private theorem map_TCompB_inv_app (F : Dᵇ[k]) (hε : 0 ≤ ε) :
    ι[k].map ((TCompB k hε hε).inv.app F) =
      (TComp k hε hε).inv.app (ι[k].obj F) := by
  have h : ι[k].map ((TCompB k hε hε).hom.app F) =
      (TComp k hε hε).hom.app (ι[k].obj F) :=
    NatTrans.congr_app (whiskerRight_TCompB_hom k hε hε) F
  exact congrArg Iso.inv (Iso.ext h :
    ι[k].mapIso ((TCompB k hε hε).app F) = (TComp k hε hε).app (ι[k].obj F))

private theorem map_augB_app (F : Dᵇ[k]) (hε : 0 ≤ ε) :
    ι[k].map ((augB k hε).app F) = (aug k hε).app (ι[k].obj F) :=
  NatTrans.congr_app (whiskerRight_augB k hε) F

private theorem map_TB_map (ε : ℝ) {F G : Dᵇ[k]} (f : F ⟶ G) :
    ι[k].map ((TB k ε).map f) = (T k ε).map (ι[k].map f) := rfl

private theorem witnessB_equation_iff (f : (TB k ε).obj F ⟶ G) (g : (TB k ε).obj G ⟶ F) :
    (TCompB k hε hε).inv.app F ≫ (TB k ε).map f ≫ g = (augB k (add_nonneg hε hε)).app F ↔
    (TComp k hε hε).inv.app (ι[k].obj F) ≫ (T k ε).map (ι[k].map f) ≫ ι[k].map g =
      (aug k (add_nonneg hε hε)).app (ι[k].obj F) := by
  rw [← ι[k].map_injective_iff]
  simp only [Functor.map_comp, map_TCompB_inv_app, map_TB_map, map_augB_app]
  rfl

/-- View a bounded witness in the bounded-below category. -/
def WitnessB.toPlus (w : WitnessB k hε F G) : Witness k hε (ι[k].obj F) (ι[k].obj G) :=
  ⟨ι[k].map w.hom, ι[k].map w.inv,
    (witnessB_equation_iff _ _).mp w.hom_inv, (witnessB_equation_iff _ _).mp w.inv_hom⟩

/-- Restrict a witness between included bounded objects to the bounded category. -/
def WitnessB.ofPlus (w : Witness k hε (ι[k].obj F) (ι[k].obj G)) : WitnessB k hε F G where
  hom := ι[k].preimage w.hom
  inv := ι[k].preimage w.inv
  hom_inv := by
    apply (witnessB_equation_iff _ _).mpr
    erw [ι[k].map_preimage (X := (TB k ε).obj F) (Y := G) w.hom,
      ι[k].map_preimage (X := (TB k ε).obj G) (Y := F) w.inv]
    exact w.hom_inv
  inv_hom := by
    apply (witnessB_equation_iff _ _).mpr
    erw [ι[k].map_preimage (X := (TB k ε).obj G) (Y := F) w.inv,
      ι[k].map_preimage (X := (TB k ε).obj F) (Y := G) w.hom]
    exact w.inv_hom

/-- A radius admits a bounded witness exactly when it admits a witness after inclusion. -/
theorem nonempty_witnessB_iff :
    Nonempty (WitnessB k hε F G) ↔ Nonempty (Witness k hε (ι[k].obj F) (ι[k].obj G)) :=
  ⟨fun ⟨w⟩ => ⟨w.toPlus⟩, fun ⟨w⟩ => ⟨WitnessB.ofPlus w⟩⟩

/-- The band distance of bounded objects, computed in the bounded-below category. -/
def distanceB (F G : Dᵇ[k]) : ℝ≥0∞ := distance (ι[k].obj F) (ι[k].obj G)

/-- The bounded distance is the infimum of radii of bounded witnesses. -/
theorem distanceB_eq_iInf (F G : Dᵇ[k]) :
    distanceB F G = ⨅ (ε : ℝ≥0) (_ : Nonempty (WitnessB k ε.coe_nonneg F G)), (ε : ℝ≥0∞) := by
  simp only [distanceB, distance, nonempty_witnessB_iff]

/-- A bounded witness bounds the bounded distance by its radius. -/
theorem WitnessB.distance_le (w : WitnessB k hε F G) : distanceB F G ≤ ENNReal.ofReal ε :=
  w.toPlus.distance_le


/-- Enlarge the radius of a bounded witness. -/
def WitnessB.mono {δ : ℝ} {hδ : 0 ≤ δ} (w : WitnessB k hε F G) (h : ε ≤ δ) :
    WitnessB k hδ F G :=
  WitnessB.ofPlus (w.toPlus.mono h)

/-- Exchange the two objects of a bounded witness. -/
def WitnessB.symm (w : WitnessB k hε F G) : WitnessB k hε G F :=
  ⟨w.inv, w.hom, w.inv_hom, w.hom_inv⟩

/-- Compose two bounded witnesses at the sum of their radii. -/
def WitnessB.trans {δ : ℝ} {hδ : 0 ≤ δ} {H : Dᵇ[k]}
    (w : WitnessB k hε F G) (v : WitnessB k hδ G H) : WitnessB k (add_nonneg hε hδ) F H :=
  WitnessB.ofPlus (w.toPlus.trans v.toPlus)

/-- Bounded objects admit a zero-radius bounded witness exactly when they are isomorphic. -/
theorem WitnessB.nonempty_zero_iff :
    Nonempty (WitnessB k (le_refl (0 : ℝ)) F G) ↔ Nonempty (F ≅ G) := by
  rw [nonempty_witnessB_iff, Witness.nonempty_zero_iff]
  exact ⟨fun ⟨e⟩ => ⟨ι[k].preimageIso e⟩, fun ⟨e⟩ => ⟨ι[k].mapIso e⟩⟩

/-- The bounded distance from an object to itself is zero. -/
@[simp] theorem distanceB_self (F : Dᵇ[k]) : distanceB F F = 0 := distance_self _

/-- The bounded band distance is symmetric. -/
theorem distanceB_comm (F G : Dᵇ[k]) : distanceB F G = distanceB G F :=
  distance_comm _ _

/-- The bounded band distance satisfies the extended triangle inequality. -/
theorem distanceB_triangle (F G H : Dᵇ[k]) : distanceB F H ≤ distanceB F G + distanceB G H :=
  distance_triangle _ _ _

/-- Isomorphisms of bounded objects preserve the bounded band distance. -/
theorem distanceB_congr {F' G' : Dᵇ[k]} (e : F ≅ F') (i : G ≅ G') :
    distanceB F G = distanceB F' G' :=
  distance_congr (ι[k].mapIso e) (ι[k].mapIso i)

end TDA.Sheaf.BandConvolution
