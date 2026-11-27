import TDA.Sheaf.BoundedBandDistance

/-!
# Finite biproducts for the real-band distance

Witness maps assemble at a common radius. The distance bound follows by enlarging
individual witness radii to any radius strictly above the supremum of the distances.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal ZeroObject

namespace TDA.Sheaf

/-- The inclusion from bounded to bounded-below complexes preserves addition of morphisms. -/
instance boundedToPlus_additive (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] : (boundedToPlus C).Additive where
  map_add := rfl

end TDA.Sheaf

namespace TDA.Sheaf.BandConvolution

variable {k : Type} [Ring k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

local notation "D⁺[" k "]" => DerivedCategory.Plus (realLine.Sheaf (ModuleCat k))
local notation "Dᵇ[" k "]" => DerivedCategory.Bounded (realLine.Sheaf (ModuleCat k))
local notation "ι[" k "]" => boundedToPlus (realLine.Sheaf (ModuleCat k))

variable {ε : ℝ} {hε : 0 ≤ ε} {F G : D⁺[k]}

/-- Transport a witness along isomorphisms of its two objects at the same radius. -/
def Witness.congr {F' G' : D⁺[k]} (w : Witness k hε F G) (e : F ≅ F') (f : G ≅ G') :
    Witness k hε F' G' := by
  let u := (Witness.ofIso e.symm).trans (w.trans (Witness.ofIso f))
  exact u.mono (by simp only [add_zero, zero_add, le_refl])

/-- A witness to zero exists precisely when the augmentation at twice the radius vanishes. -/
theorem nonempty_witness_zero_iff :
    Nonempty (Witness k hε F 0) ↔ (aug k (add_nonneg hε hε)).app F = 0 := by
  constructor
  · rintro ⟨w⟩
    have hv : w.hom = 0 := (isZero_zero _).eq_of_tgt _ _
    simpa only [hv, Functor.map_zero, zero_comp, comp_zero] using w.hom_inv.symm
  · intro h
    refine ⟨⟨0, 0, ?_, ?_⟩⟩
    · simp only [comp_zero, h]
    · exact (isZero_zero _).eq_of_tgt _ _

private def assembleBiproductMap {I : Type} [Finite I] {A B : I → D⁺[k]}
    (f : ∀ i, (T k ε).obj (A i) ⟶ B i) : (T k ε).obj (⨁ A) ⟶ ⨁ B :=
  (T k ε).biproductComparison A ≫ biproduct.map f

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem assembleBiproductMap_π {I : Type} [Finite I] {A B : I → D⁺[k]}
    (f : ∀ i, (T k ε).obj (A i) ⟶ B i) (i : I) :
    assembleBiproductMap f ≫ biproduct.π B i = (T k ε).map (biproduct.π A i) ≫ f i := by
  simp only [assembleBiproductMap, Category.assoc, biproduct.map_π,
    Functor.biproductComparison_π_assoc]

private theorem assembleBiproductMap_equation {I : Type} [Finite I] {A B : I → D⁺[k]}
    (f : ∀ i, (T k ε).obj (A i) ⟶ B i) (g : ∀ i, (T k ε).obj (B i) ⟶ A i)
    (h : ∀ i, (TComp k hε hε).inv.app (A i) ≫ (T k ε).map (f i) ≫ g i =
      (aug k (add_nonneg hε hε)).app (A i)) :
    (TComp k hε hε).inv.app (⨁ A) ≫ (T k ε).map (assembleBiproductMap f) ≫
      assembleBiproductMap g = (aug k (add_nonneg hε hε)).app (⨁ A) := by
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, assembleBiproductMap_π, ← Functor.map_comp_assoc]
  have hn : (TComp k hε hε).inv.app (⨁ A) ≫
      (T k ε).map ((T k ε).map (biproduct.π A i)) =
        (T k (ε + ε)).map (biproduct.π A i) ≫ (TComp k hε hε).inv.app (A i) :=
    ((TComp k hε hε).inv.naturality (biproduct.π A i)).symm
  rw [(T k ε).map_comp, Category.assoc]
  erw [reassoc_of% hn, h i]
  exact (aug k (add_nonneg hε hε)).naturality (biproduct.π A i)

/-- Pointwise witnesses at a common radius give a witness between finite biproducts. -/
def Witness.biproduct {I : Type} [Finite I] {X Y : I → D⁺[k]}
    (w : ∀ i, Witness k hε (X i) (Y i)) : Witness k hε (⨁ X) (⨁ Y) where
  hom := assembleBiproductMap fun i => (w i).hom
  inv := assembleBiproductMap fun i => (w i).inv
  hom_inv := assembleBiproductMap_equation _ _ fun i => (w i).hom_inv
  inv_hom := assembleBiproductMap_equation _ _ fun i => (w i).inv_hom

/-- A strict distance bound gives a witness at the indicated radius. -/
theorem nonempty_witness_of_distance_lt {r : ℝ≥0} (h : distance F G < r) :
    Nonempty (Witness k r.coe_nonneg F G) := by
  obtain ⟨s, hs, ⟨w⟩⟩ := distance_lt_iff.mp h
  exact ⟨w.mono (ENNReal.coe_lt_coe.mp hs).le⟩

/-- The band distance of finite biproducts is bounded by the supremum of the summand distances. -/
theorem distance_biproduct_le {I : Type} [Finite I] (X Y : I → D⁺[k]) :
    distance (⨁ X) (⨁ Y) ≤ ⨆ i, distance (X i) (Y i) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro r hr hfin
  let s := ⨆ i, distance (X i) (Y i)
  have hs : s ≠ ⊤ := hfin.ne
  let t := s.toNNReal + r
  have ht : (t : ℝ≥0∞) = s + r := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hs]
  have w (i : I) : Nonempty (Witness k t.coe_nonneg (X i) (Y i)) :=
    nonempty_witness_of_distance_lt ((le_iSup (fun i => distance (X i) (Y i)) i).trans_lt
      (ht.symm ▸ ENNReal.lt_add_right hs (ENNReal.coe_ne_zero.mpr hr.ne')))
  have hw := (Witness.biproduct fun i => (w i).some).distance_le
  rwa [ENNReal.ofReal_coe_nnreal, ht] at hw

private def pairBiproductIso (X Y : D⁺[k]) : (⨁ pairFunction X Y) ≅ X ⊞ Y :=
  biprod.uniqueUpToIso _ _
    ((biproduct.bicone _).toBinaryBiconeIsBilimit.symm (biproduct.isBilimit _))

/-- Two witnesses at the same radius give a witness between binary biproducts. -/
def Witness.biprod {F' G' : D⁺[k]} (w : Witness k hε F G) (v : Witness k hε F' G') :
    Witness k hε (F ⊞ F') (G ⊞ G') :=
  (Witness.biproduct (X := pairFunction F F') (Y := pairFunction G G')
    (fun j => match j with | .left => w | .right => v)).congr
      (pairBiproductIso F F') (pairBiproductIso G G')

/-- The distance of binary biproducts is bounded by the larger summand distance. -/
theorem distance_biprod_le (F F' G G' : D⁺[k]) :
    distance (F ⊞ F') (G ⊞ G') ≤ distance F G ⊔ distance F' G' := by
  rw [← distance_congr (pairBiproductIso F F') (pairBiproductIso G G')]
  refine (distance_biproduct_le _ _).trans (iSup_le fun j => ?_)
  cases j
  · exact le_sup_left
  · exact le_sup_right

/-- Reindexing a biproduct by an equivalence on either side preserves the distance. -/
theorem distance_biproduct_reindex {I J I' J' : Type}
    [Finite I] [Finite J] [Finite I'] [Finite J']
    (X : I → D⁺[k]) (Y : J → D⁺[k]) (e : I' ≃ I) (f : J' ≃ J) :
    distance (⨁ X ∘ e) (⨁ Y ∘ f) = distance (⨁ X) (⨁ Y) :=
  distance_congr (biproduct.reindex e X) (biproduct.reindex f Y)

/-- Pointwise bounded witnesses at a common radius give a witness of the finite biproducts. -/
def WitnessB.biproduct {I : Type} [Finite I] {X Y : I → Dᵇ[k]}
    (w : ∀ i, WitnessB k hε (X i) (Y i)) : WitnessB k hε (⨁ X) (⨁ Y) :=
  WitnessB.ofPlus <| (Witness.biproduct fun i => (w i).toPlus).congr
    ((ι[k].mapBiproduct X).symm) ((ι[k].mapBiproduct Y).symm)

/-- The bounded band distance of finite biproducts is bounded by the summand distances. -/
theorem distanceB_biproduct_le {I : Type} [Finite I] (X Y : I → Dᵇ[k]) :
    distanceB (⨁ X) (⨁ Y) ≤ ⨆ i, distanceB (X i) (Y i) := by
  change distance (ι[k].obj (⨁ X)) (ι[k].obj (⨁ Y)) ≤ _
  rw [distance_congr (ι[k].mapBiproduct X) (ι[k].mapBiproduct Y)]
  exact distance_biproduct_le _ _

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- Two bounded witnesses at one radius give a witness between their binary biproducts. -/
def WitnessB.biprod {A B C D : Dᵇ[k]} (w : WitnessB k hε A B) (v : WitnessB k hε C D) :
    WitnessB k hε (A ⊞ C) (B ⊞ D) :=
  WitnessB.ofPlus <| (w.toPlus.biprod v.toPlus).congr
    ((ι[k].mapBiprod A C).symm) ((ι[k].mapBiprod B D).symm)

/-- The bounded band distance of binary biproducts is bounded by the larger summand distance. -/
theorem distanceB_biprod_le (A B C D : Dᵇ[k]) :
    distanceB (A ⊞ C) (B ⊞ D) ≤ distanceB A B ⊔ distanceB C D :=
  (distance_congr (ι[k].mapBiprod A C) (ι[k].mapBiprod B D)).le.trans
    (distance_biprod_le _ _ _ _)

/-- Reindexing a bounded biproduct by an equivalence on either side preserves the distance. -/
theorem distanceB_biproduct_reindex {I J I' J' : Type}
    [Finite I] [Finite J] [Finite I'] [Finite J']
    (X : I → Dᵇ[k]) (Y : J → Dᵇ[k]) (e : I' ≃ I) (f : J' ≃ J) :
    distanceB (⨁ X ∘ e) (⨁ Y ∘ f) = distanceB (⨁ X) (⨁ Y) :=
  distanceB_congr (biproduct.reindex e X) (biproduct.reindex f Y)

/-- A bounded witness to zero exists precisely when the bounded augmentation vanishes. -/
theorem nonempty_witnessB_zero_iff {A : Dᵇ[k]} :
    Nonempty (WitnessB k hε A 0) ↔ (augB k (add_nonneg hε hε)).app A = 0 := by
  constructor
  · rintro ⟨w⟩
    have hv : w.hom = 0 := (isZero_zero _).eq_of_tgt _ _
    let B := (TB k ε).obj A
    have hz : (TB k ε).map (0 : B ⟶ (0 : Dᵇ[k])) = 0 := by
      apply ι[k].map_injective
      simp only [ι[k].map_zero]
      change (T k ε).map (ι[k].map (0 : B ⟶ (0 : Dᵇ[k]))) = 0
      simp only [ι[k].map_zero, (T k ε).map_zero]
    simpa only [hv, hz, zero_comp, comp_zero] using w.hom_inv.symm
  · intro h
    refine ⟨⟨0, 0, ?_, (isZero_zero _).eq_of_tgt _ _⟩⟩
    simp only [comp_zero, h]

end TDA.Sheaf.BandConvolution
