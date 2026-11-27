import TDA.Sheaf.BoundedBandDistance

/-!
# Stability of derived direct images on the real line

A pointwise displacement bound gives a map between the corresponding derived direct images
after closed-band convolution. Its adjoint is computed by restricting the band counit to the
graph of the two functions. On the two-band correspondence, the composite follows the triple
`(f x, g x, f x)`, whose first and last coordinates give the augmentation.
-/

noncomputable section

open CategoryTheory DerivedCategory
open scoped ENNReal

namespace TDA.Sheaf.BandConvolution

variable (k : Type) [Ring k]

-- The inverse image of the identity is an equivalence with idempotent composition comparison.
section Identity

variable {X Y : TopCat.{0}} [HasDerivedCategory (X.Sheaf (ModuleCat k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat k))]

local notation "L" => pullbackPlus k (𝟙 X)

private def idPullbackFullyFaithful : (L).FullyFaithful := by
  let adj := derivedAdjunction k (𝟙 X)
  letI : ∀ M, IsIso (adj.unit.app M) :=
    fun M => inferInstanceAs (IsIso ((derivedUnit k (𝟙 X)).app M))
  letI : ∀ M, IsIso (adj.counit.app M) :=
    fun M => inferInstanceAs (IsIso ((derivedCounit k (𝟙 X)).app M))
  exact adj.toEquivalence.fullyFaithfulFunctor

private def idPullbackHom : L ⟶ 𝟭 _ := by
  let e : L ⋙ L ≅ L := pullbackPlusCompIso k (𝟙 X) (𝟙 X)
  let ff := idPullbackFullyFaithful k (X := X)
  exact
    { app := fun F => ff.preimage (e.hom.app F)
      naturality := by
        intro F G f
        apply ff.map_injective
        simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage, Functor.id_map]
        exact e.hom.naturality f }

private lemma idPullbackHom_app_pullback (f : X ⟶ Y) (F : Plus (Y.Sheaf (ModuleCat k))) :
    (idPullbackHom k).app ((pullbackPlus k f).obj F) =
      (pullbackPlusCompIso k (𝟙 X) f).hom.app F := by
  let e : pullbackPlus k f ⋙ L ≅ pullbackPlus k f := pullbackPlusCompIso k (𝟙 X) f
  let ff := idPullbackFullyFaithful k (X := X)
  apply ff.map_injective
  have h : (L).map (e.hom.app F) ≫ e.hom.app F =
      (pullbackPlusCompIso k (𝟙 X) (𝟙 X)).hom.app ((pullbackPlus k f).obj F) ≫
        e.hom.app F :=
    pullbackPlusCompIso_hom_assoc_app k (𝟙 X) (𝟙 X) f F
  exact (ff.map_preimage _).trans
    ((cancel_mono (e.hom.app F)).mp h).symm

end Identity

section Graph

variable {X : TopCat.{0}} {a : ℝ} (f g : X ⟶ realLine)

/-- The thickening of a map by the closed band of radius `a`. -/
private abbrev E (f : X ⟶ realLine) (a : ℝ) : TopCat.{0} :=
  TopCat.of {z : X × ℝ | dist (f z.1) z.2 ≤ a}

private def projection : E f a ⟶ X := TopCat.ofHom ⟨fun z => z.1.1, by fun_prop⟩

private def toBand : E f a ⟶ D a :=
  TopCat.ofHom ⟨fun z => ⟨(f z.1.1, z.1.2), z.2⟩, by fun_prop⟩

private def sectionGraph (h : ∀ x, dist (f x) (g x) ≤ a) : X ⟶ E f a :=
  TopCat.ofHom ⟨fun x => ⟨(x, g x), h x⟩, by fun_prop⟩

/-- The graph of two maps whose displacement is bounded by the band radius. -/
def directImageGraph (h : ∀ x, dist (f x) (g x) ≤ a) : X ⟶ D a :=
  sectionGraph f g h ≫ toBand f

variable [HasDerivedCategory (X.Sheaf (ModuleCat k))]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]

local notation "Sh" => ModuleCat k
local notation "R" => pushforwardPlus k
local notation "P" => pullbackPlus k
local notation "π" => projection f (a := a)
local notation "r" => toBand f (a := a)

private instance : HasDerivedCategory ((E f a).Sheaf (ModuleCat k)) :=
  HasDerivedCategory.standard _

/-- If `dist (f x) (g x) ≤ a` everywhere, the closed-band mate over `f` followed by restriction to
the graph of `g` gives a map from the convolved direct image along `f` to the image along `g`. -/
def directImageComparison (h : ∀ x, dist (f x) (g x) ≤ a) (F : Plus (X.Sheaf Sh)) :
    (T k a).obj ((R f).obj F) ⟶ (R g).obj F :=
  (R (q a)).map
      ((baseChange k (show π ≫ f = r ≫ p a from rfl)).app F) ≫
    (pushforwardPlusCompIso k r (q a)).inv.app ((P π).obj F) ≫
    (corrRestr k (sectionGraph f g h) π (r ≫ q a)).app F ≫
    (R g).map ((idPullbackHom k).app F)

-- Moving a map across the comparison for a composite direct image.
private lemma map_unit_comp_comparison {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {G : C ⥤ D} {H : D ⥤ E} {U : C ⥤ E} (c : U ≅ G ⋙ H)
    {A : D} {B B' C' : C} (η : A ⟶ G.obj B) (α : B ⟶ B') (ψ : B' ⟶ C') :
    H.map (η ≫ G.map (α ≫ ψ)) ≫ c.inv.app C' =
      (H.map η ≫ c.inv.app B ≫ U.map α) ≫ U.map ψ := by
  have n := c.inv.naturality (α ≫ ψ)
  simp only [Functor.comp_map] at n
  simp only [Functor.map_comp, Category.assoc] at n ⊢
  rw [n]

private def bandMateCounit (F : Plus (X.Sheaf Sh)) :
    (P (r ≫ p a)).obj ((R f).obj F) ⟶ (P π).obj F :=
  (pullbackPlusCompIso k π f).inv.app ((R f).obj F) ≫
    (P π).map ((derivedCounit k f).app F)

private lemma baseChange_bandMate_app (F : Plus (X.Sheaf Sh)) :
    (baseChange k (show π ≫ f = r ≫ p a from rfl)).app F =
      (derivedUnit k r).app ((P (p a)).obj ((R f).obj F)) ≫
        (R r).map ((pullbackPlusCompIso k r (p a)).hom.app ((R f).obj F) ≫
          bandMateCounit k f F) := by
  let e : P f ⋙ P π ≅ P (r ≫ p a) := pullbackPlusCompIso k π f
  have hs : pullbackPlusSquare k (show π ≫ f = r ≫ p a from rfl) =
      (pullbackPlusCompIso k r (p a)).hom ≫ e.inv := by
    change (pullbackPlusCompIso k r (p a)).hom ≫
      eqToHom (rfl : P (r ≫ p a) = P (r ≫ p a)) ≫ e.inv = _
    rw [eqToHom_refl, Category.id_comp]
  rw [baseChange_app, hs]
  change _ ≫ (R r).map (_ ≫ e.inv.app _) ≫ (R r).map ((P π).map _) = _
  have hψ : bandMateCounit k f F =
      e.inv.app ((R f).obj F) ≫ (P π).map ((derivedCounit k f).app F) := rfl
  rw [hψ]
  simp only [Functor.map_comp, Category.assoc]

-- The base-change mate over the band is restriction along r followed by the pullback counit.
private lemma pushforward_bandMate (F : Plus (X.Sheaf Sh)) :
    (R (q a)).map ((baseChange k (show π ≫ f = r ≫ p a from rfl)).app F) ≫
      (pushforwardPlusCompIso k r (q a)).inv.app ((P π).obj F) =
    (corrRestr k r (p a) (q a)).app ((R f).obj F) ≫
      (R (r ≫ q a)).map (bandMateCounit k f F) := by
  rw [baseChange_bandMate_app, corrRestr_app]
  exact map_unit_comp_comparison (pushforwardPlusCompIso k r (q a)) _ _ _

private lemma graphCounit_paste (h : ∀ x, dist (f x) (g x) ≤ a) (F : Plus (X.Sheaf Sh)) :
    directImageComparison k f g h F =
      (corrRestr k (directImageGraph f g h) (p a) (q a)).app ((R f).obj F) ≫
        (R g).map ((derivedCounit k f).app F) := by
  let s := sectionGraph f g h
  let M := (R f).obj F
  let j : P f ⋙ P π ≅ P (r ≫ p a) := pullbackPlusCompIso k π f
  let e : P f ⋙ P (𝟙 X) ≅ P f := pullbackPlusCompIso k (𝟙 X) f
  let eπ : P π ⋙ P s ≅ P (𝟙 X) := pullbackPlusCompIso k s π
  let ef : P (r ≫ p a) ⋙ P s ≅ P f := pullbackPlusCompIso k s (r ≫ p a)
  let ε : (P f).obj M ⟶ F := (derivedCounit k f).app F
  let ψ := bandMateCounit k f (a := a) F
  let φ : (P f).obj M ⟶ (P (𝟙 X)).obj F := e.inv.app M ≫ (P (𝟙 X)).map ε
  have hc : ef.hom.app M ≫ φ = (P s).map ψ ≫ eπ.hom.app F := by
    have n : (P s).map ((P π).map ε) ≫ eπ.hom.app F =
        eπ.hom.app ((P f).obj M) ≫ (P (𝟙 X)).map ε := eπ.hom.naturality ε
    have assoc : (P s).map (j.hom.app M) ≫ ef.hom.app M =
      eπ.hom.app ((P f).obj M) ≫ e.hom.app M :=
      pullbackPlusCompIso_hom_assoc_app k s π f M
    have h : ef.hom.app M ≫ e.inv.app M =
        (P s).map (j.inv.app M) ≫ eπ.hom.app ((P f).obj M) := by
      have he := congrArg (fun t => (P s).map (j.inv.app M) ≫ t ≫ e.inv.app M) assoc
      change (P s).map (j.inv.app M) ≫
          ((P s).map (j.hom.app M) ≫ ef.hom.app M) ≫ e.inv.app M =
        (P s).map (j.inv.app M) ≫
          (eπ.hom.app ((P f).obj M) ≫ e.hom.app M) ≫ e.inv.app M at he
      simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        Iso.hom_inv_id_app] at he
      have hl : (P s).map (𝟙 ((P (r ≫ p a)).obj M)) ≫
          (ef.hom.app M ≫ e.inv.app M) = ef.hom.app M ≫ e.inv.app M := by
        rw [(P s).map_id, Category.id_comp]
      have hr := congrArg ((P s).map (j.inv.app M) ≫ ·)
        (Category.comp_id (eπ.hom.app ((P f).obj M)))
      exact hl.symm.trans (he.trans hr)
    change ef.hom.app M ≫ e.inv.app M ≫ (P (𝟙 X)).map ε =
      (P s).map (j.inv.app M ≫ (P π).map ε) ≫ eπ.hom.app F
    simp only [Functor.map_comp, Category.assoc, n, reassoc_of% h]
  let ρ : (T k a).obj M ⟶ (R (r ≫ q a)).obj ((P (r ≫ p a)).obj M) :=
    (corrRestr k r (p a) (q a)).app M
  let τ : (R (r ≫ q a)).obj ((P (r ≫ p a)).obj M) ⟶ (R g).obj ((P f).obj M) :=
    (corrRestr k s (r ≫ p a) (r ≫ q a)).app M
  let θ : (R (r ≫ q a)).obj ((P π).obj F) ⟶ (R g).obj ((P (𝟙 X)).obj F) :=
    (corrRestr k s π (r ≫ q a)).app F
  let σ : (R g).obj ((P (𝟙 X)).obj F) ⟶ (R g).obj F :=
    (R g).map ((idPullbackHom k).app F)
  have hp : τ ≫ (R g).map φ = (R (r ≫ q a)).map ψ ≫ θ :=
    corrRestr_app_comp_map k s (r ≫ p a) π (r ≫ q a) M F ψ φ hc
  have hcomp : ρ ≫ τ = (corrRestr k (directImageGraph f g h) (p a) (q a)).app M :=
    NatTrans.congr_app (corrRestr_comp k s r (p a) (q a)) M
  have hφ : φ ≫ (idPullbackHom k).app F = (derivedCounit k f).app F := by
    have n : (P (𝟙 X)).map ε ≫ (idPullbackHom k).app F = e.hom.app M ≫ ε :=
      ((idPullbackHom k).naturality ε).trans
        (congrArg (· ≫ ε) (idPullbackHom_app_pullback k f M))
    change (e.inv.app M ≫ (P (𝟙 X)).map ε) ≫ (idPullbackHom k).app F = ε
    rw [Category.assoc, n]
    exact Iso.inv_hom_id_app_assoc e M ε
  have hm : (R g).map φ ≫ σ = (R g).map ((derivedCounit k f).app F) := by
    dsimp only [σ]
    rw [← Functor.map_comp, hφ]
  simp only [directImageComparison, reassoc_of% (pushforward_bandMate k f (a := a) F)]
  change ρ ≫ (R (r ≫ q a)).map ψ ≫ θ ≫ σ = _
  rw [← reassoc_of% hp, hm, ← Category.assoc, hcomp]
  rfl

/-- The adjoint of the comparison along `g` is the counit of the band output projection
transported along `x ↦ (f x, g x)`, followed by the counit of `f`. -/
lemma directImageComparison_adjoint (h : ∀ x, dist (f x) (g x) ≤ a) (F : Plus (X.Sheaf Sh)) :
    (P g).map (directImageComparison k f g h F) ≫ (derivedCounit k g).app F =
      (transportCounit k (directImageGraph f g h) (p a) (q a)).app ((R f).obj F) ≫
        (derivedCounit k f).app F := by
  rw [graphCounit_paste]
  exact corrRestr_map_adjoint k (directImageGraph f g h) (p a) (q a) _ _

end Graph

section Composition

variable {X : TopCat.{0}} [HasDerivedCategory (X.Sheaf (ModuleCat k))]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]

local notation "R" => pushforwardPlus k
local notation "P" => pullbackPlus k

private lemma directImageComparison_self {a : ℝ} (ha : 0 ≤ a) (f : X ⟶ realLine)
    (F : Plus (X.Sheaf (ModuleCat k))) :
    directImageComparison k f f (fun x => (dist_self (f x)).le.trans ha) F =
      (aug k ha).app ((R f).obj F) := by
  let M := (R f).obj F
  let s := directImageGraph f f (fun x => (dist_self (f x)).le)
  let d : T k 0 ⟶ P f ⋙ R f := corrRestr k s (p 0) (q 0)
  have hu : (T0Iso k).inv ≫ d =
      (derivedUnit k f) ≫ Functor.whiskerRight (eqToHom (rfl : P f = P f)) (R f) :=
    corrUnitIso_inv_corrRestr k s p_zero_eq_q_zero
  simp only [eqToHom_refl, Functor.whiskerRight_id', Category.comp_id] at hu
  have ht : d = (T0Iso k).hom ≫ derivedUnit k f := by
    have e := congrArg ((T0Iso k).hom ≫ ·) hu
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using e
  have hc := NatTrans.congr_app (corrRestr_comp k s (incl ha) (p a) (q a)) M
  change (restr k ha ≫ d).app M =
    (corrRestr k (directImageGraph f f (fun x => (dist_self (f x)).le.trans ha))
      (p a) (q a)).app M at hc
  have tri : (derivedUnit k f).app M ≫ (R f).map ((derivedCounit k f).app F) = 𝟙 M :=
    (derivedAdjunction k f).right_triangle_components F
  rw [graphCounit_paste, ← hc]
  change ((restr k ha ≫ d).app M) ≫ (R f).map ((derivedCounit k f).app F) =
    (restr k ha ≫ (T0Iso k).hom).app M
  rw [ht]
  simp only [NatTrans.comp_app, Category.assoc, tri]
  exact congrArg ((restr k ha).app M ≫ ·) (Category.comp_id ((T0Iso k).hom.app M))

variable [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

private def graphChain {a b : ℝ} (f g l : X ⟶ realLine)
    (hfg : ∀ x, dist (f x) (g x) ≤ a) (hgl : ∀ x, dist (g x) (l x) ≤ b) :
    X ⟶ Z a b :=
  TopCat.ofHom ⟨fun x => ⟨(f x, g x, l x), hfg x, hgl x⟩, by fun_prop⟩

/-- Two graph comparisons compose to the comparison for the outer functions, with the
displacement budget obtained by adding the two radii. -/
theorem directImageComparison_comp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f g l : X ⟶ realLine) (hfg : ∀ x, dist (f x) (g x) ≤ a)
    (hgl : ∀ x, dist (g x) (l x) ≤ b) (F : Plus (X.Sheaf (ModuleCat k))) :
    (TComp k ha hb).inv.app ((R f).obj F) ≫
        (T k b).map (directImageComparison k f g hfg F) ≫ directImageComparison k g l hgl F =
      directImageComparison k f l (fun x =>
        (dist_triangle _ (g x) _).trans (add_le_add (hfg x) (hgl x))) F := by
  let M := (R f).obj F
  let N := (R g).obj F
  let A := directImageComparison k f g hfg F
  let B := directImageComparison k g l hgl F
  let C := directImageComparison k f l (fun x =>
    (dist_triangle _ (g x) _).trans (add_le_add (hfg x) (hgl x))) F
  let i := graphChain f g l hfg hgl
  let c₁₂ : T k a ⋙ P g ⟶ P f := transportCounit k (i ≫ pr₁₂ a b) (p a) (q a)
  let c₂₃ : T k b ⋙ P l ⟶ P g := transportCounit k (i ≫ pr₂₃ a b) (p b) (q b)
  let c₁₃ : T k (a + b) ⋙ P l ⟶ P f :=
    transportCounit k (i ≫ pr₁₃ a b) (p (a + b)) (q (a + b))
  have hp := transportCounit_TCompOfEq k i ha hb rfl M
  rw [TCompOfEq_rfl] at hp
  have pasting : (P l).map ((TComp k ha hb).hom.app M) ≫ c₁₃.app M =
      c₂₃.app ((T k a).obj M) ≫ c₁₂.app M := hp
  have hA : (P g).map A ≫ (derivedCounit k g).app F = c₁₂.app M ≫
      (derivedCounit k f).app F := directImageComparison_adjoint k f g hfg F
  have hB : (P l).map B ≫ (derivedCounit k l).app F = c₂₃.app N ≫
      (derivedCounit k g).app F := directImageComparison_adjoint k g l hgl F
  have hC : (P l).map C ≫ (derivedCounit k l).app F = c₁₃.app M ≫
      (derivedCounit k f).app F := directImageComparison_adjoint k f l _ F
  have n : (P l).map ((T k b).map A) ≫ c₂₃.app N =
      c₂₃.app ((T k a).obj M) ≫ (P g).map A := c₂₃.naturality A
  change (TComp k ha hb).inv.app M ≫ (T k b).map A ≫ B = C
  apply (cancel_epi ((TComp k ha hb).hom.app M)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  apply ((derivedAdjunction k l).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, derivedAdjunction_counit, Functor.map_comp, Category.assoc,
    hB, hC]
  change (P l).map ((R (q b)).map ((P (p b)).map A)) ≫
    c₂₃.app N ≫ (derivedCounit k g).app F = _
  rw [reassoc_of% n, hA, reassoc_of% pasting]

/-- A pointwise displacement bound gives a closed-band witness between the derived direct images
of the same coefficient complex. -/
def directImageWitness {a : ℝ} (ha : 0 ≤ a) (f g : X ⟶ realLine)
    (hfg : ∀ x, dist (f x) (g x) ≤ a) (F : Plus (X.Sheaf (ModuleCat k))) :
    Witness k ha ((R f).obj F) ((R g).obj F) where
  hom := directImageComparison k f g hfg F
  inv := directImageComparison k g f (fun x => by simpa only [dist_comm (g x) (f x)] using hfg x) F
  hom_inv := (directImageComparison_comp k ha ha f g f hfg _ F).trans
    (directImageComparison_self k (add_nonneg ha ha) f F)
  inv_hom := (directImageComparison_comp k ha ha g f g _ hfg F).trans
    (directImageComparison_self k (add_nonneg ha ha) g F)

/-- A uniform real displacement budget bounds the extended distance of the direct images. -/
theorem distance_directImage_le_of_dist_le {a : ℝ} (ha : 0 ≤ a) (f g : X ⟶ realLine)
    (hfg : ∀ x, dist (f x) (g x) ≤ a) (F : Plus (X.Sheaf (ModuleCat k))) :
    distance ((R f).obj F) ((R g).obj F) ≤ ENNReal.ofReal a :=
  (directImageWitness k ha f g hfg F).distance_le

/-- Stability of derived direct images with the literal extended supremum of displacements. -/
theorem distance_directImage_le (f g : X ⟶ realLine) (F : Plus (X.Sheaf (ModuleCat k))) :
    distance ((R f).obj F) ((R g).obj F) ≤ ⨆ x : X, edist (f x) (g x) := by
  let d := ⨆ x : X, edist (f x) (g x)
  change _ ≤ d
  by_cases h : d = ⊤
  · rw [h]
    exact le_top
  rw [← ENNReal.ofReal_toReal h]
  apply distance_directImage_le_of_dist_le k ENNReal.toReal_nonneg
  intro x
  have hx : edist (f x) (g x) ≤ d := le_iSup (fun x : X => edist (f x) (g x)) x
  have ht := ENNReal.toReal_mono h hx
  rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at ht

/-- Stability for bounded representatives of the direct images, specified up to isomorphism in
the bounded-below category. -/
theorem distanceB_directImage_le (f g : X ⟶ realLine) (F : Plus (X.Sheaf (ModuleCat k)))
    {A B : Bounded (realLine.Sheaf (ModuleCat k))}
    (ef : (boundedToPlus _).obj A ≅ (R f).obj F)
    (eg : (boundedToPlus _).obj B ≅ (R g).obj F) :
    distanceB A B ≤ ⨆ x : X, edist (f x) (g x) := by
  rw [distanceB, distance_congr ef eg]
  exact distance_directImage_le k f g F

end Composition

end TDA.Sheaf.BandConvolution
