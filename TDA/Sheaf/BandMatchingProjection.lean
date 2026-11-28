import TDA.Sheaf.BandMatchingNormalization

/-!
# Projected equations of finite interval witnesses

Cohomology in one degree restricts the witness equations between stable
intervals of a common endpoint type to their own block of intermediate labels.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open TDA.Persistence TDA.Sheaf.AlternatingDiagram TDA.Sheaf.RealConstructible
open TDA.Sheaf.RealStratification
open scoped BigOperators ENNReal ZeroObject

namespace TDA.Sheaf.BandConvolution

variable {k : Type} [Field k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

local notation "Sh" => realLine.Sheaf (ModuleCat k)
local notation "D⁺" => Plus Sh
local notation "Single" => Plus.singleFunctor Sh
local notation "H[" d "]" => Plus.homologyFunctor Sh d
local notation "ISh[" hp "," J "]" => Functor.obj (extension k hp) (interval _ J)

section Biproduct

variable {I J : Type} [Finite I] [Finite J]
variable {ε : ℝ} {hε : 0 ≤ ε}

/-- The component of a witness map from the convolution of a source summand
to a target summand. -/
def Witness.biproductHom (X : I → D⁺) (Y : J → D⁺) (w : Witness k hε (⨁ X) (⨁ Y)) (i : I) (j : J) :
    (T k ε).obj (X i) ⟶ Y j :=
  (T k ε).map (biproduct.ι X i) ≫ w.hom ≫ biproduct.π Y j

end Biproduct

private theorem sum_map_comp_biproduct_components
    {C : Type*} [Category C] [Preadditive C] {I J : Type} [Fintype J]
    (X : I → C) (Y : J → C) [HasBiproduct X] [HasBiproduct Y]
    (U V : C ⥤ C) [U.Additive] (μ : U ⋙ U ≅ V) (η : V ⟶ 𝟭 C)
    (f : U.obj (⨁ X) ⟶ ⨁ Y) (g : U.obj (⨁ Y) ⟶ ⨁ X)
    (h : μ.inv.app (⨁ X) ≫ U.map f ≫ g = η.app (⨁ X)) (i a : I) :
    (∑ j : J, U.map (U.map (biproduct.ι X i) ≫ f ≫ biproduct.π Y j) ≫
      U.map (biproduct.ι Y j) ≫ g ≫ biproduct.π X a) =
      μ.hom.app (X i) ≫ η.app (X i) ≫ biproduct.ι X i ≫ biproduct.π X a := by
  have hw : U.map f ≫ g = μ.hom.app (⨁ X) ≫ η.app (⨁ X) := by
    rw [← h, Iso.hom_inv_id_app_assoc]
  have hsum : (∑ j : J, U.map (biproduct.π Y j) ≫ U.map (biproduct.ι Y j)) =
      𝟙 (U.obj (⨁ Y)) := by
    simp only [← Functor.map_comp, ← U.map_sum, biproduct.total, U.map_id]
  have hμ : U.map (U.map (biproduct.ι X i)) ≫ μ.hom.app (⨁ X) =
      μ.hom.app (X i) ≫ V.map (biproduct.ι X i) := μ.hom.naturality (biproduct.ι X i)
  have hη : V.map (biproduct.ι X i) ≫ η.app (⨁ X) = η.app (X i) ≫ biproduct.ι X i :=
    η.naturality (biproduct.ι X i)
  calc
    _ = U.map (U.map (biproduct.ι X i)) ≫ U.map f ≫
          (∑ j : J, U.map (biproduct.π Y j) ≫ U.map (biproduct.ι Y j)) ≫
          g ≫ biproduct.π X a := by
      simp only [Preadditive.sum_comp, Preadditive.comp_sum, Functor.map_comp, Category.assoc]
    _ = U.map (U.map (biproduct.ι X i)) ≫ (U.map f ≫ g) ≫ biproduct.π X a := by
      rw [hsum, Category.id_comp, Category.assoc]
    _ = _ := by rw [hw, Category.assoc, reassoc_of% hμ, reassoc_of% hη]

section Projection

variable {m n l : ℕ} {p : Fin m → ℝ} {q : Fin n → ℝ} {s : Fin l → ℝ}
  {ε : ℝ}

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))] in
private theorem homology_map_comp_eq_zero_of_ne_degree (hε : 0 ≤ ε)
    (hq : StrictMono q) (K : GradedInterval n) (F : IntervalEndpoints)
    (hK : intervalSet q K.interval = F.support)
    (hF : F.hasDegreeOneOutput = false) {d : ℤ} (hd : d ≠ K.degree)
    {A C : D⁺} (f : A ⟶ (T k ε).obj (K.obj k hq)) (g : (T k ε).obj (K.obj k hq) ⟶ C) :
    H[d].map (f ≫ g) = 0 := by
  obtain ⟨L, _, ⟨e⟩⟩ := exists_iso_convolved_endpoints k hq K.interval K.degree hε F hF hK
  have hz : IsZero (H[d].obj ((T k ε).obj (K.obj k hq))) :=
    (isZero_homology_singleFunctor_obj _ hd).of_iso (H[d].mapIso e)
  rw [Functor.map_comp, hz.eq_of_tgt (H[d].map f) 0, zero_comp]

private theorem homology_map_comp_eq_zero_of_ne_type (hε : 0 ≤ ε)
    (hp : StrictMono p) (hq : StrictMono q) (hs : StrictMono s)
    (A : GradedInterval m) (B : GradedInterval n) (C : GradedInterval l)
    (E F G : IntervalEndpoints)
    (hJ : intervalSet p A.interval = E.support) (hK : intervalSet q B.interval = F.support)
    (hL : intervalSet s C.interval = G.support)
    (hE : E.hasDegreeOneOutput = false) (hF : F.hasDegreeOneOutput = false)
    (hbd : B.degree = A.degree) (hcd : C.degree = A.degree)
    (hEG : E.sameType G = true) (hEF : E.sameType F = false)
    (f : (T k ε).obj (A.obj k hp) ⟶ B.obj k hq)
    (g : (T k ε).obj (B.obj k hq) ⟶ C.obj k hs) :
    H[A.degree].map ((T k ε).map f ≫ g) = 0 := by
  rcases A with ⟨J, d⟩
  rcases B with ⟨K, b⟩
  rcases C with ⟨L, c⟩
  change b = d at hbd
  change c = d at hcd
  subst b
  subst c
  obtain ⟨A, hA, ⟨eA⟩⟩ :=
    exists_iso_convolved_endpoints k hp J d (add_nonneg hε hε) E hE hJ
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_iso_convolved_endpoints k hq K d hε F hF hK
  let hp' := strictMono_sortedBreakpoints (bandBreakpoints p (ε + ε))
  let hq' := strictMono_sortedBreakpoints (bandBreakpoints q ε)
  let A₀ := (Single d).obj ISh[hp,J]
  let B₀ := (Single d).obj ISh[hq,K]
  let C₀ := (Single d).obj ISh[hs,L]
  change (T k ε).obj A₀ ⟶ B₀ at f
  change (T k ε).obj B₀ ⟶ C₀ at g
  let e := singleFunctorCompHomologyFunctorIsoPlus Sh d
  let a : H[d].obj ((T k ε).obj ((T k ε).obj A₀)) ≅ ISh[hp',A] :=
    H[d].mapIso ((TComp k hε hε).app A₀ ≪≫ eA) ≪≫ e.app ISh[hp',A]
  let b : H[d].obj ((T k ε).obj B₀) ≅ ISh[hq',B] :=
    H[d].mapIso eB ≪≫ e.app ISh[hq',B]
  let c : H[d].obj C₀ ≅ ISh[hs,L] := e.app ISh[hs,L]
  let F' := H[d].map ((T k ε).map f)
  let G' := H[d].map g
  have h₀ : (E.convolved _ (add_nonneg hε hε)).sameType G = true := by
    rwa [IntervalEndpoints.sameType_convolved_left]
  have h₁ : (E.convolved _ (add_nonneg hε hε)).sameType (F.convolved _ hε) = false := by
    rwa [IntervalEndpoints.sameType_convolved_left, IntervalEndpoints.sameType_convolved_right]
  have hz := (E.convolved _ (add_nonneg hε hε)).hom_comp_eq_zero_of_different_type k
    hp' hq' hs _ G hA hB hL h₀ h₁ (a.inv ≫ F' ≫ b.hom) (b.inv ≫ G' ≫ c.hom)
  change H[d].map ((T k ε).map f ≫ g) = 0
  rw [H[d].map_comp]
  apply (cancel_epi a.inv).mp
  apply (cancel_mono c.hom).mp
  change (a.inv ≫ F' ≫ G') ≫ c.hom = 0 ≫ c.hom
  rw [Category.assoc, Category.assoc, zero_comp]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hz

variable {I J : Type} [Finite I] [Finite J] [Fintype J]
  {mi : I → ℕ} {nj : J → ℕ} {pi : (i : I) → Fin (mi i) → ℝ} {qj : (j : J) → Fin (nj j) → ℝ}
  (hpi : ∀ i, StrictMono (pi i)) (hqj : ∀ j, StrictMono (qj j))
  {X : (i : I) → GradedInterval (mi i)} {Y : (j : J) → GradedInterval (nj j)}

local notation "XX" => (fun i => GradedInterval.obj k (hpi i) (X i))
local notation "YY" => (fun j => GradedInterval.obj k (hqj j) (Y j))

/-- In the cohomological degree and endpoint type shared by the two outer labels,
only intermediate labels in that block contribute to the biproduct equation. -/
theorem Witness.sum_homology_biproductHom_in_block (hε : 0 ≤ ε)
    (w : Witness k hε (⨁ XX) (⨁ YY))
    (E : I → IntervalEndpoints) (F : J → IntervalEndpoints)
    (hX : ∀ i, intervalSet (pi i) (X i).interval = (E i).support)
    (hY : ∀ j, intervalSet (qj j) (Y j).interval = (F j).support)
    (hE : ∀ i, (E i).hasDegreeOneOutput = false)
    (hF : ∀ j, (F j).hasDegreeOneOutput = false)
    (i a : I) (hd : (X a).degree = (X i).degree) (ht : (E i).sameType (E a) = true) :
    (∑ j ∈ Finset.univ.filter
      (fun j => (Y j).degree = (X i).degree ∧ (E i).sameType (F j) = true),
      H[(X i).degree].map ((T k ε).map (w.biproductHom XX YY i j) ≫
        w.symm.biproductHom YY XX j a)) =
      H[(X i).degree].map ((TComp k hε hε).hom.app (XX i) ≫
        (aug k (add_nonneg hε hε)).app (XX i) ≫ biproduct.ι XX i ≫ biproduct.π XX a) := by
  let H := H[(X i).degree]
  have hfull :
      (∑ j : J, (T k ε).map (w.biproductHom XX YY i j) ≫ w.symm.biproductHom YY XX j a) =
        (TComp k hε hε).hom.app (XX i) ≫
          (aug k (add_nonneg hε hε)).app (XX i) ≫ biproduct.ι XX i ≫ biproduct.π XX a := by
    simpa only [Witness.biproductHom, Witness.symm, Category.assoc] using
      sum_map_comp_biproduct_components XX YY (T k ε) (T k (ε + ε)) (TComp k hε hε)
        (aug k (add_nonneg hε hε)) w.hom w.inv w.hom_inv i a
  have hp := congrArg H.map hfull
  rw [H.map_sum] at hp
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).trans hp
  intro j _ hj
  let f := w.biproductHom XX YY i j
  let g := w.symm.biproductHom YY XX j a
  change H.map ((T k ε).map f ≫ g) = 0
  have hout : ¬ ((Y j).degree = (X i).degree ∧ (E i).sameType (F j) = true) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
  by_cases hjd : (Y j).degree = (X i).degree
  · have hjt : (E i).sameType (F j) = false :=
      Bool.eq_false_iff.mpr fun h => hout ⟨hjd, h⟩
    exact homology_map_comp_eq_zero_of_ne_type hε (hpi i) (hqj j) (hpi a)
      (X i) (Y j) (X a) (E i) (F j) (E a) (hX i) (hY j) (hX a)
      (hE i) (hF j) hjd hd ht hjt f g
  · exact homology_map_comp_eq_zero_of_ne_degree hε (hqj j) (Y j) (F j)
      (hY j) (hF j) (Ne.symm hjd) ((T k ε).map f) g

/-- The degree of a stable interval detects its witness augmentation whenever its
deletion cost exceeds the witness radius. -/
theorem homology_band_augmentation_ne_zero_of_lt_deletionCost
    (hp : StrictMono p) (J : GradedInterval m) (E : IntervalEndpoints)
    (hJ : intervalSet p J.interval = E.support) (hE : E.hasDegreeOneOutput = false)
    (hε : 0 ≤ ε) (h : ENNReal.ofReal ε < E.deletionCost) :
    H[J.degree].map ((TComp k hε hε).hom.app (J.obj k hp) ≫
      (aug k (add_nonneg hε hε)).app (J.obj k hp)) ≠ 0 := by
  rcases J with ⟨J, d⟩
  let A := (GradedInterval.mk J d).obj k hp
  let H := H[d]
  obtain ⟨_, _, ⟨e⟩⟩ :=
    exists_iso_convolved_endpoints k hp J d (add_nonneg hε hε) E hE hJ
  intro hz
  have hw : (aug k (add_nonneg hε hε)).app A = 0 := by
    let e' : A ≅ (Single d).obj ISh[hp,J] := Iso.refl A
    apply (homology_map_bijective_of_iso_single k (d := d) e e').injective
    change H.map ((aug k (add_nonneg hε hε)).app A) =
      H.map (0 : (T k (ε + ε)).obj A ⟶ A)
    rw [H.map_zero]
    apply (cancel_epi (H.mapIso ((TComp k hε hε).app A)).hom).mp
    change H.map ((TComp k hε hε).hom.app A) ≫ H.map ((aug k (add_nonneg hε hε)).app A) =
      H.map ((TComp k hε hε).hom.app A) ≫ 0
    rw [← H.map_comp, comp_zero]
    exact hz
  obtain ⟨w⟩ := (nonempty_witness_zero_iff (hε := hε) (F := A)).mpr hw
  exact h.not_ge ((E.distance_zero_eq k hp ⟨J, d⟩ hJ) ▸ w.distance_le)

end Projection

end TDA.Sheaf.BandConvolution
