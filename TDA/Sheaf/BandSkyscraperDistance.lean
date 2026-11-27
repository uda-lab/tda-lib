import TDA.Sheaf.BandDistance
import TDA.Sheaf.BandIntervalConvolution
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Band distance of real skyscraper sheaves

For a field `k`, the degree-zero skyscraper at `a` has band convolution supported on
`[a - ε, a + ε]`. A comparison to the skyscraper at `b` is induced by the germ at `b`.
The exact witness criterion includes the endpoints of the closed band.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory Opposite TopologicalSpace
  TopCat.Presheaf StalkSkyscraperPresheafAdjunctionAuxs
open scoped NNReal ENNReal ZeroObject

namespace TDA.Sheaf.BandConvolution

open TDA.Persistence AlternatingDiagram RealStratification RealConstructible

variable (k : Type) [Field k]

local notation "Sh[" k "]" => realLine.Sheaf (ModuleCat k)
local notation "D⁺[" k "]" => DerivedCategory.Plus (Sh[k])
local notation "Single[" k "]" => Plus.singleFunctor (Sh[k]) 0
local notation "H₀[" k "]" => Plus.homologyFunctor (Sh[k]) 0

attribute [local instance] Classical.propDecidable

/-- The sheaf of `k`-modules supported at `a` with stalk `k`. -/
abbrev skyscraperSheaf (a : ℝ) : Sh[k] :=
  _root_.skyscraperSheaf (X := realLine) a (ModuleCat.of k k)

private def skySectionsIso {a : ℝ} {U : Opens realLine} (h : a ∈ U) :
    (skyscraperSheaf k a).presheaf.obj (op U) ≅ ModuleCat.of k k :=
  eqToIso (ite_eq_left h)

private theorem skyRes_hom {a : ℝ} {U V : Opens realLine} (h : V ≤ U) (ha : a ∈ V) :
    (skyscraperSheaf k a).presheaf.map (homOfLE h).op ≫ (skySectionsIso k ha).hom =
      (skySectionsIso k (h ha)).hom := by
  change (skyscraperPresheaf a (ModuleCat.of k k)).map (homOfLE h).op ≫ _ = _
  rw [skyscraperPresheaf_map, dite_eq_left ha]
  unfold skySectionsIso
  erw [eqToIso.hom, eqToIso.hom, eqToHom_trans]
  rfl

private theorem isIso_sky_res {a : ℝ} {U V : Opens realLine}
    (h : V ≤ U) (ha : a ∈ V) :
    IsIso ((skyscraperSheaf k a).presheaf.map (homOfLE h).op) := by
  have : IsIso ((skyscraperSheaf k a).presheaf.map (homOfLE h).op ≫
      (skySectionsIso k ha).hom) := by
    rw [skyRes_hom]
    exact (skySectionsIso k (h ha)).isIso_hom
  exact IsIso.of_isIso_comp_right _ (skySectionsIso k ha).hom

/-- An interval sheaf with singleton support is the skyscraper sheaf at that point. -/
theorem nonempty_iso_skyscraperSheaf_interval {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) {a : ℝ}
    (hJ : intervalSet p J = {a}) :
    Nonempty (skyscraperSheaf k a ≅ (extension k hp).obj (interval (orient m) J)) := by
  have hm (U : Opens realLine) : MeetsClosed (intervalSet p J) U ↔ a ∈ U := by
    rw [hJ]
    exact ⟨fun h => by simpa using h.2,
      fun h => ⟨by rw [closure_singleton]; exact Set.inter_subset_left,
        ⟨a, h, Set.mem_singleton _⟩⟩⟩
  refine nonempty_iso_extension_interval_of_sections hp (skyscraperSheaf k a) J ?_ ?_ ?_
  · intro U _ h
    exact ⟨skySectionsIso k ((hm U).1 h)⟩
  · intro U _ h
    have ha := mt (hm U).2 h
    change IsZero ((skyscraperPresheaf a (ModuleCat.of k k)).obj (op U))
    rw [skyscraperPresheaf_obj, ite_eq_right ha]
    exact (isZero_zero _).of_iso HasZeroObject.zeroIsoTerminal.symm
  · intro U V h _ _ hu _
    exact isIso_sky_res k h ((hm U).1 hu)

private theorem nonempty_iso_sky_interval (a : ℝ) :
    ∃ (J : FiniteInterval 3),
      intervalSet (fun _ : Fin 1 => a) J = {a} ∧
      Nonempty (skyscraperSheaf k a ≅
        (extension k (Subsingleton.strictMono (fun _ : Fin 1 => a))).obj
          (interval (orient 1) J)) := by
  let p : Fin 1 → ℝ := fun _ => a
  have hp : StrictMono p := Subsingleton.strictMono p
  let J : FiniteInterval (2 * 1 + 1) := ⟨1, 2, by decide, by decide⟩
  have hJ : intervalSet p J = {a} := intervalSet_eq_singleton hp (i := 0) rfl rfl
  exact ⟨J, hJ, nonempty_iso_skyscraperSheaf_interval k hp J hJ⟩

private theorem skyHom_eq_of_fromStalk_eq {F : Sh[k]} {b : ℝ}
    {f g : F ⟶ skyscraperSheaf k b}
    (he : fromStalk (X := realLine) b f.hom = fromStalk (X := realLine) b g.hom) :
    f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  let lift := toSkyscraperPresheaf (X := realLine) (𝓕 := F.presheaf) (c := ModuleCat.of k k) b
  exact (to_skyscraper_fromStalk (X := realLine) b f.hom).symm.trans
    ((congrArg lift he).trans (to_skyscraper_fromStalk (X := realLine) b g.hom))

private theorem skyHom_ext {F : Sh[k]} {b : ℝ}
    (h : IsIso (F.presheaf.germ ⊤ b (Opens.mem_top b))) {f g : F ⟶ skyscraperSheaf k b}
    (he : f.hom.app (op ⊤) = g.hom.app (op ⊤)) : f = g := by
  apply skyHom_eq_of_fromStalk_eq k
  apply (cancel_epi (F.presheaf.germ ⊤ b (Opens.mem_top b))).mp
  erw [germ_fromStalk, germ_fromStalk, he]

variable [HasDerivedCategory (Sh[k])]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

/-- The skyscraper sheaf with value `k` at `a`, placed in degree zero. -/
abbrev skyscraper (a : ℝ) : D⁺[k] := Single[k].obj (skyscraperSheaf k a)

/-- Band convolution of a skyscraper is the degree-zero sheaf of the closed band interval. -/
theorem exists_iso_T_skyscraper (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ (n : ℕ) (p : Fin n → ℝ) (hp : StrictMono p) (J : FiniteInterval (2 * n + 1)),
      intervalSet p J = Set.Icc (a - ε) (a + ε) ∧
      Nonempty ((T k ε).obj (skyscraper k a) ≅
        Single[k].obj ((extension k hp).obj (interval (orient n) J))) := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := nonempty_iso_sky_interval k a
  obtain ⟨K, hK, ⟨i⟩⟩ := exists_intervalSheaf_T_singleton (k := k)
    (Subsingleton.strictMono (fun _ : Fin 1 => a)) J hε hJ
  exact ⟨_, _, _, K, hK, ⟨(T k ε).mapIso (Single[k].mapIso e) ≪≫ i⟩⟩

private def singleH0Iso : Single[k] ⋙ H₀[k] ≅ 𝟭 Sh[k] :=
  singleFunctorCompHomologyFunctorIsoPlus _ 0

omit [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem H0_map_bijective_of_iso_single {X Y : D⁺[k]} {F G : Sh[k]}
    (e : X ≅ Single[k].obj F) (i : Y ≅ Single[k].obj G) :
    Function.Bijective (H₀[k].map : (X ⟶ Y) → _) := by
  let L := H₀[k]
  have h (f : X ⟶ Y) : ∃ u : F ⟶ G, f = e.hom ≫ Single[k].map u ≫ i.inv := by
    obtain ⟨u, hu⟩ := (DerivedCategory.singleFunctor (Sh[k]) 0).map_surjective
      (Plus.ι.map (e.inv ≫ f ≫ i.hom))
    refine ⟨u, ?_⟩
    have h' : Single[k].map u = e.inv ≫ f ≫ i.hom := Plus.ι.map_injective hu
    rw [h']
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hmap (u : F ⟶ G) :
      L.map (e.hom ≫ Single[k].map u ≫ i.inv) =
        L.map e.hom ≫ (singleH0Iso k).hom.app F ≫ u ≫
          (singleH0Iso k).inv.app G ≫ L.map i.inv := by
    have hn : L.map (Single[k].map u) ≫ (singleH0Iso k).hom.app G =
        (singleH0Iso k).hom.app F ≫ u := (singleH0Iso k).hom.naturality u
    rw [L.map_comp, L.map_comp]
    have he : L.map (Single[k].map u) =
        (singleH0Iso k).hom.app F ≫ u ≫ (singleH0Iso k).inv.app G := by
      apply (cancel_mono ((singleH0Iso k).hom.app G)).mp
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
      exact hn
    rw [he]
    simp only [Category.assoc]
  constructor
  · intro f g he
    obtain ⟨u, rfl⟩ := h f
    obtain ⟨v, rfl⟩ := h g
    rw [hmap, hmap] at he
    have huv : u = v := by simpa only [cancel_epi, ← Category.assoc, cancel_mono] using he
    rw [huv]
  · intro f
    let u := (singleH0Iso k).inv.app F ≫ L.map e.inv ≫ f ≫
      L.map i.hom ≫ (singleH0Iso k).hom.app G
    refine ⟨e.hom ≫ Single[k].map u ≫ i.inv, ?_⟩
    rw [hmap]
    simp only [u, Category.assoc, Iso.hom_inv_id_app_assoc, ← L.map_comp_assoc,
      Iso.hom_inv_id, L.map_id, Category.id_comp]
    have hi : L.map i.hom ≫ L.map i.inv = 𝟙 (L.obj Y) := (L.mapIso i).hom_inv_id
    rw [hi, Category.comp_id]

private theorem H0_map_bijective_to_skyscraper {a b ε : ℝ} (hε : 0 ≤ ε) :
    Function.Bijective (H₀[k].map :
      ((T k ε).obj (skyscraper k a) ⟶ skyscraper k b) → _) := by
  obtain ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_iso_T_skyscraper k a hε
  exact H0_map_bijective_of_iso_single k e (Iso.refl _)

private abbrev H0BandSky (ε a : ℝ) : Sh[k] := H₀[k].obj ((T k ε).obj (skyscraper k a))

private theorem nonempty_iso_H0BandSky {a ε : ℝ} (hε : 0 ≤ ε) :
    ∃ (n : ℕ) (p : Fin n → ℝ) (hp : StrictMono p) (J : FiniteInterval (2 * n + 1)),
      intervalSet p J = Set.Icc (a - ε) (a + ε) ∧
      Nonempty (H0BandSky k ε a ≅ (extension k hp).obj (interval (orient n) J)) := by
  obtain ⟨n, p, hp, J, hJ, ⟨e⟩⟩ := exists_iso_T_skyscraper k a hε
  exact ⟨n, p, hp, J, hJ, ⟨H₀[k].mapIso e ≪≫ (singleH0Iso k).app _⟩⟩

private theorem isIso_germ_H0BandSky {a b ε : ℝ} (hε : 0 ≤ ε)
    (hb : b ∈ Set.Icc (a - ε) (a + ε)) :
    IsIso ((H0BandSky k ε a).presheaf.germ ⊤ b (Opens.mem_top b)) := by
  obtain ⟨_, p, hp, J, hJ, ⟨e⟩⟩ := nonempty_iso_H0BandSky k (a := a) hε
  have hclosed : IsClosed (intervalSet p J) := by rw [hJ]; exact isClosed_Icc
  have h := isIso_germ_extension_interval k hp J (U := ⊤) Set.ordConnected_univ
    (by rw [hclosed.closure_eq]; exact Set.inter_subset_left) (x := b) trivial (by rwa [hJ])
  let F := (H0BandSky k ε a).presheaf
  let G := ((extension k hp).obj (interval _ J)).presheaf
  let E : F ≅ G := (TopCat.Sheaf.forget (ModuleCat k) realLine).mapIso e
  let s := TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) b
  let m : F.stalk b ⟶ G.stalk b := (s.mapIso E).hom
  let φ := (E.app (op ⊤)).hom
  have hm : IsIso m := (s.mapIso E).isIso_hom
  have hn : F.germ ⊤ b (Opens.mem_top b) ≫ m = φ ≫ G.germ ⊤ b (Opens.mem_top b) :=
    stalkFunctor_map_germ ⊤ b (Opens.mem_top b) E.hom
  have hcomp : IsIso (φ ≫ G.germ ⊤ b (Opens.mem_top b)) :=
    IsIso.comp_isIso' (E.app (op ⊤)).isIso_hom h
  have hi : IsIso (F.germ ⊤ b (Opens.mem_top b) ≫ m) :=
    (congrArg (fun f => IsIso f) hn).mpr hcomp
  exact IsIso.of_isIso_comp_right (F.germ ⊤ b (Opens.mem_top b)) m

private theorem isZero_stalk_H0BandSky {a b ε : ℝ} (hε : 0 ≤ ε)
    (hb : b ∉ Set.Icc (a - ε) (a + ε)) :
    IsZero ((H0BandSky k ε a).presheaf.stalk b) := by
  obtain ⟨_, _, hp, J, hJ, ⟨e⟩⟩ := nonempty_iso_H0BandSky k (a := a) hε
  let s := TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
    TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) b
  exact (isZero_stalk_extension_interval k hp (J := J) (by rwa [hJ])).of_iso (s.mapIso e)

/-- The stalk of the point sheaf at its support is the coefficient module. -/
def skyscraperStalkIso (a : ℝ) :
    (skyscraperSheaf k a).presheaf.stalk a ≅ ModuleCat.of k k :=
  skyscraperPresheafStalkOfSpecializes (X := realLine) a (ModuleCat.of k k) (specializes_refl a)

private def skyWindowIso {a ε : ℝ} (hε : 0 ≤ ε) :
    (H0BandSky k ε a).presheaf.obj (op ⊤) ≅ ModuleCat.of k k :=
  H0TSectionsIso k ε (skyscraperSheaf k a) ⊤ Set.ordConnected_univ ≪≫
    skySectionsIso k (le_bandOpen hε ⊤ (show a ∈ (⊤ : Opens realLine) from trivial))

/-- Identify a stalk in the closed output band with the sections at the source point. -/
def skyscraperBandStalkIso {a b ε : ℝ} (hε : 0 ≤ ε)
    (hb : b ∈ Set.Icc (a - ε) (a + ε)) :
    (H₀[k].obj ((T k ε).obj (skyscraper k a))).presheaf.stalk b ≅ ModuleCat.of k k :=
  letI := isIso_germ_H0BandSky k hε hb
  (asIso ((H0BandSky k ε a).presheaf.germ ⊤ b (Opens.mem_top b))).symm ≪≫ skyWindowIso k hε

private theorem germ_top_bandStalkIso_hom {a b ε : ℝ} (hε : 0 ≤ ε)
    (hb : b ∈ Set.Icc (a - ε) (a + ε)) :
    (H0BandSky k ε a).presheaf.germ ⊤ b (Opens.mem_top b) ≫
        (skyscraperBandStalkIso k hε hb).hom =
      (skyWindowIso k hε).hom := by
  have := isIso_germ_H0BandSky k hε hb
  exact Iso.hom_inv_id_assoc (asIso ((H0BandSky k ε a).presheaf.germ ⊤ b (Opens.mem_top b))) _

omit [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem H0Aug_top_hom {a ε : ℝ} (hε : 0 ≤ ε) :
    (H0Aug k hε (skyscraperSheaf k a)).hom.app (op ⊤) ≫
        (skySectionsIso k (show a ∈ (⊤ : Opens realLine) from trivial)).hom =
      (skyWindowIso k (a := a) hε).hom := by
  rw [H0TSectionsIso_hom_aug k hε _ ⊤ Set.ordConnected_univ]
  change (H0TSectionsIso k ε (skyscraperSheaf k a) ⊤ Set.ordConnected_univ).hom ≫
    (skyscraperSheaf k a).presheaf.map (homOfLE (le_bandOpen hε ⊤)).op ≫ _ = _
  exact congrArg (fun f => (H0TSectionsIso k ε (skyscraperSheaf k a) ⊤
    Set.ordConnected_univ).hom ≫ f)
      (skyRes_hom k (le_bandOpen hε ⊤) (show a ∈ (⊤ : Opens realLine) from trivial))

/-- At the support point the augmentation is the identity under the stalk identifications. -/
theorem stalk_map_H0Aug_skyscraper {a ε : ℝ} (hε : 0 ≤ ε)
    (ha : a ∈ Set.Icc (a - ε) (a + ε)) :
    (TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) a).map
        (H0Aug k hε (skyscraperSheaf k a)).hom ≫ (skyscraperStalkIso k a).hom =
      (skyscraperBandStalkIso k hε ha).hom := by
  have := isIso_germ_H0BandSky k hε ha
  apply (cancel_epi ((H0BandSky k ε a).presheaf.germ ⊤ a (Opens.mem_top a))).mp
  erw [stalkFunctor_map_germ_assoc]
  have ht := germ_skyscraperPresheafStalkOfSpecializes_hom (X := realLine) a (ModuleCat.of k k)
    (specializes_refl a) ⊤ (show a ∈ (⊤ : Opens realLine) from trivial)
  change (skyscraperSheaf k a).presheaf.germ ⊤ a (Opens.mem_top a) ≫
    (skyscraperStalkIso k a).hom = _ at ht
  erw [ht, germ_top_bandStalkIso_hom k hε ha]
  exact H0Aug_top_hom k hε


/-- A radius restriction acts by the identity on a stalk in both closed output bands. -/
theorem stalk_map_H0Restr_skyscraper {a b δ ε : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ ε)
    (hb : b ∈ Set.Icc (a - δ) (a + δ)) (hb' : b ∈ Set.Icc (a - ε) (a + ε)) :
    (TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) b).map
        (H0Restr k h (skyscraperSheaf k a)).hom ≫ (skyscraperBandStalkIso k hδ hb).hom =
      (skyscraperBandStalkIso k (hδ.trans h) hb').hom := by
  have := isIso_germ_H0BandSky k (hδ.trans h) hb'
  apply (cancel_epi ((H0BandSky k ε a).presheaf.germ ⊤ b (Opens.mem_top b))).mp
  erw [stalkFunctor_map_germ_assoc, germ_top_bandStalkIso_hom k (hδ.trans h) hb',
    germ_top_bandStalkIso_hom k hδ hb]
  change (H0Restr k h (skyscraperSheaf k a)).hom.app (op ⊤) ≫
    ((H0TSectionsIso k δ (skyscraperSheaf k a) ⊤ Set.ordConnected_univ).hom ≫ _) = _
  rw [← Category.assoc, H0TSectionsIso_hom_restr k hδ h _ ⊤ Set.ordConnected_univ,
    Category.assoc]
  exact congrArg (fun f => (H0TSectionsIso k ε (skyscraperSheaf k a) ⊤
    Set.ordConnected_univ).hom ≫ f)
      (skyRes_hom k (bandOpen_mono h ⊤) (le_bandOpen hδ ⊤ (Opens.mem_top a)))

private abbrev evalTop : Sh[k] ⥤ ModuleCat k :=
  TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
    (evaluation _ _).obj (op (⊤ : Opens realLine))

private abbrev sectionsH0 : D⁺[k] ⥤ ModuleCat k := H₀[k] ⋙ evalTop k

private def skyTopIso (a : ℝ) : (sectionsH0 k).obj (skyscraper k a) ≅ ModuleCat.of k k :=
  (evalTop k).mapIso ((singleH0Iso k).app (skyscraperSheaf k a)) ≪≫
    skySectionsIso k (U := ⊤) trivial

omit [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem sectionsH0_aug_normalized {a ε : ℝ} (hε : 0 ≤ ε) :
    (sectionsH0 k).map ((aug k hε).app (skyscraper k a)) ≫ (skyTopIso k a).hom =
      (skyWindowIso k hε).hom := by
  change (evalTop k).map (H₀[k].map ((aug k hε).app (skyscraper k a))) ≫
    ((evalTop k).map ((singleH0Iso k).hom.app (skyscraperSheaf k a)) ≫ _) = _
  rw [← Category.assoc, ← (evalTop k).map_comp]
  exact H0Aug_top_hom k (a := a) hε

private theorem exists_skyscraper_comparison {a b ε : ℝ} (hε : 0 ≤ ε)
    (hb : b ∈ Set.Icc (a - ε) (a + ε)) :
    ∃ f : (T k ε).obj (skyscraper k a) ⟶ skyscraper k b,
      (sectionsH0 k).map f ≫ (skyTopIso k b).hom = (skyWindowIso k hε).hom := by
  let f₀ : H0BandSky k ε a ⟶ skyscraperSheaf k b :=
    ObjectProperty.homMk (toSkyscraperPresheaf (X := realLine)
      (𝓕 := (H0BandSky k ε a).presheaf) b (skyscraperBandStalkIso k hε hb).hom)
  obtain ⟨f, hf⟩ := (H0_map_bijective_to_skyscraper k hε).surjective
    (f₀ ≫ (singleH0Iso k).inv.app (skyscraperSheaf k b))
  refine ⟨f, ?_⟩
  have he : H₀[k].map f ≫ (singleH0Iso k).hom.app (skyscraperSheaf k b) = f₀ := by
    rw [hf, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  change (evalTop k).map (H₀[k].map f) ≫
    ((evalTop k).map ((singleH0Iso k).hom.app (skyscraperSheaf k b)) ≫ _) = _
  rw [← Category.assoc, ← (evalTop k).map_comp, he]
  change (toSkyscraperPresheaf (X := realLine) (𝓕 := (H0BandSky k ε a).presheaf)
    b (skyscraperBandStalkIso k hε hb).hom).app (op ⊤) ≫ _ = _
  rw [toSkyscraperPresheaf_app]
  erw [dite_eq_left (show b ∈ unop (op (⊤ : Opens realLine)) from Opens.mem_top b)]
  let s := skySectionsIso k (Opens.mem_top b)
  change ((H0BandSky k ε a).presheaf.germ ⊤ b (Opens.mem_top b) ≫
    (skyscraperBandStalkIso k hε hb).hom ≫ s.inv) ≫ s.hom = _
  rw [Category.assoc, Category.assoc, s.inv_hom_id, Category.comp_id]
  exact germ_top_bandStalkIso_hom k hε hb

/-- Beyond the closed band, every map from the translated skyscraper to the point is zero. -/
theorem hom_T_skyscraper_eq_zero {a b ε : ℝ} (hε : 0 ≤ ε)
    (hb : b ∉ Set.Icc (a - ε) (a + ε))
    (f : (T k ε).obj (skyscraper k a) ⟶ skyscraper k b) : f = 0 := by
  apply (H0_map_bijective_to_skyscraper k hε).injective
  rw [Functor.map_zero]
  apply (cancel_mono ((singleH0Iso k).hom.app (skyscraperSheaf k b))).mp
  erw [zero_comp]
  apply skyHom_eq_of_fromStalk_eq k
  exact (isZero_stalk_H0BandSky k hε hb).eq_of_src _ _

omit [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
/-- The augmentation of a skyscraper is nonzero at every nonnegative radius. -/
theorem aug_skyscraper_ne_zero (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (aug k hε).app (skyscraper k a) ≠ 0 := by
  intro h
  have ht := sectionsH0_aug_normalized k (a := a) hε
  rw [h] at ht
  change (evalTop k).map (H₀[k].map (0 : (T k ε).obj (skyscraper k a) ⟶ skyscraper k a)) ≫
    (skyTopIso k a).hom = _ at ht
  have hzero (F G : Sh[k]) : (evalTop k).map (0 : F ⟶ G) = 0 := rfl
  erw [Functor.map_zero, hzero, zero_comp] at ht
  have hi : IsIso (0 : (sectionsH0 k).obj ((T k ε).obj (skyscraper k a)) ⟶
      ModuleCat.of k k) := by
    rw [ht]
    exact (skyWindowIso k (a := a) hε).isIso_hom
  have hz := ((isIsoZero_iff_source_target_isZero _ _).1 hi).2
  exact zero_ne_one ((ModuleCat.isZero_iff_subsingleton.1 hz).elim (0 : k) 1)

variable [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]

private theorem skyscraper_comparison_equation {a b ε : ℝ} (hε : 0 ≤ ε)
    (f : (T k ε).obj (skyscraper k a) ⟶ skyscraper k b)
    (g : (T k ε).obj (skyscraper k b) ⟶ skyscraper k a)
    (hf : (sectionsH0 k).map f ≫ (skyTopIso k b).hom = (skyWindowIso k hε).hom)
    (hg : (sectionsH0 k).map g ≫ (skyTopIso k a).hom = (skyWindowIso k hε).hom) :
    (TComp k hε hε).inv.app (skyscraper k a) ≫ (T k ε).map f ≫ g =
      (aug k (add_nonneg hε hε)).app (skyscraper k a) := by
  let A := skyscraper k a
  let B := skyscraper k b
  let μ := TComp k hε hε
  let η := aug k hε
  let η₂ := aug k (add_nonneg hε hε)
  let L := sectionsH0 k
  have hunit : η.app ((T k ε).obj A) ≫ η.app A = μ.hom.app A ≫ η₂.app A := by
    have h := NatTrans.congr_app (hcomp_aug_TComp_hom k hε hε) A
    simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.id_map, Functor.id_obj,
      Functor.leftUnitor_hom_app] at h
    exact (Category.comp_id _).symm.trans h
  have hn : (T k ε).map f ≫ η.app B = η.app ((T k ε).obj A) ≫ f := η.naturality f
  have hpre :
      L.map ((T k ε).map f) ≫ L.map g ≫ (skyTopIso k a).hom =
        L.map (μ.hom.app A) ≫ L.map (η₂.app A) ≫ (skyTopIso k a).hom := by
    calc
      _ = L.map ((T k ε).map f) ≫ L.map (η.app B) ≫ (skyTopIso k b).hom := by
        rw [hg, sectionsH0_aug_normalized k (a := b) hε]
      _ = L.map (η.app ((T k ε).obj A)) ≫ L.map f ≫ (skyTopIso k b).hom := by
        simpa only [L.map_comp, Category.assoc] using
          congrArg (fun u => L.map u ≫ (skyTopIso k b).hom) hn
      _ = L.map (η.app ((T k ε).obj A)) ≫ L.map (η.app A) ≫ (skyTopIso k a).hom := by
        rw [hf, sectionsH0_aug_normalized k (a := a) hε]
      _ = _ := by
        simpa only [L.map_comp, Category.assoc] using
          congrArg (fun u => L.map u ≫ (skyTopIso k a).hom) hunit
  have he : L.map (μ.inv.app A ≫ (T k ε).map f ≫ g) ≫ (skyTopIso k a).hom =
      L.map (η₂.app A) ≫ (skyTopIso k a).hom := by
    rw [L.map_comp, L.map_comp, Category.assoc, Category.assoc, hpre,
      ← L.map_comp_assoc, Iso.inv_hom_id_app, L.map_id, Category.id_comp]
  let X := (T k (ε + ε)).obj A
  let u : X ⟶ A := μ.inv.app A ≫ (T k ε).map f ≫ g
  let v : X ⟶ A := η₂.app A
  change u = v
  apply (H0_map_bijective_to_skyscraper k (add_nonneg hε hε)).injective
  let e := (singleH0Iso k).app (skyscraperSheaf k a)
  apply (cancel_mono e.hom).mp
  apply skyHom_ext k (isIso_germ_H0BandSky k (add_nonneg hε hε) (b := a)
    ⟨by linarith, by linarith⟩)
  let e₀ := skySectionsIso k (U := ⊤) (Opens.mem_top a)
  change (evalTop k).map (H₀[k].map u ≫ e.hom) ≫ e₀.hom =
    (evalTop k).map (H₀[k].map v ≫ e.hom) ≫ e₀.hom at he
  exact (cancel_mono e₀.hom).mp he

private theorem mem_skyscraper_band_iff {a b ε : ℝ} :
    b ∈ Set.Icc (a - ε) (a + ε) ↔ |a - b| ≤ ε := by
  rw [Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Skyscrapers admit a band witness exactly when their separation is at most the radius. -/
theorem nonempty_witness_skyscraper_iff (a b : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    Nonempty (Witness k hε (skyscraper k a) (skyscraper k b)) ↔ |a - b| ≤ ε := by
  constructor
  · rintro ⟨w⟩
    by_contra h
    have hz := hom_T_skyscraper_eq_zero k hε (mt mem_skyscraper_band_iff.mp h) w.hom
    apply aug_skyscraper_ne_zero k a (add_nonneg hε hε)
    rw [← w.hom_inv, hz, Functor.map_zero, zero_comp, comp_zero]
  · intro h
    obtain ⟨f, hf⟩ := exists_skyscraper_comparison k (a := a) (b := b) hε
      (mem_skyscraper_band_iff.mpr h)
    obtain ⟨g, hg⟩ := exists_skyscraper_comparison k (a := b) (b := a) hε
      (mem_skyscraper_band_iff.mpr (by simpa only [abs_sub_comm b a] using h))
    exact ⟨⟨f, g, skyscraper_comparison_equation k hε f g hf hg,
      skyscraper_comparison_equation k hε g f hg hf⟩⟩

/-- The extended band distance between skyscrapers is their absolute separation. -/
theorem distance_skyscraper (a b : ℝ) :
    distance (skyscraper k a) (skyscraper k b) = ENNReal.ofReal |a - b| := by
  apply le_antisymm
  · obtain ⟨w⟩ := (nonempty_witness_skyscraper_iff k a b (abs_nonneg (a - b))).mpr le_rfl
    exact w.distance_le
  · apply le_distance_iff.mpr
    intro ε h
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal ((nonempty_witness_skyscraper_iff k a b ε.coe_nonneg).mp h)

/-- The distance from a skyscraper to the zero object is infinite. -/
theorem distance_skyscraper_zero (a : ℝ) : distance (skyscraper k a) 0 = ⊤ := by
  apply distance_eq_top_iff.mpr
  intro ε
  refine ⟨fun w => aug_skyscraper_ne_zero k a (add_nonneg ε.coe_nonneg ε.coe_nonneg) ?_⟩
  have hz := (isZero_zero (D⁺[k])).eq_of_tgt w.hom 0
  rw [← w.hom_inv, hz, Functor.map_zero, zero_comp, comp_zero]

end TDA.Sheaf.BandConvolution
