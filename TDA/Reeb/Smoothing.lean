import TDA.Reeb.Interval

/-!
# Smoothing of interval precosheaves and interleavings

Precosheaves on the interval category are functors `OpenInterval ⥤ C` into an arbitrary
category `C`; the `Type`-valued case is `C := Type u`. The smoothing endofunctor is
`S_ε F := thickenFunctor ε ⋙ F` (de Silva–Munch–Patel, Definition 4.14), acting on natural
transformations by whiskering. The unit `F ⟶ S_ε F` is `F` applied to `I ⊆ T_ε I`
(Observations 4.11 and 4.15), `smoothingMap` is the enlargement `S_ε ⟶ S_δ` for `ε ≤ δ`,
`smoothingZeroIso` identifies `S_0` with the identity, and `smoothingCompIso ε δ` identifies
`S_ε S_δ` with `S_(ε+δ)` (Proposition 4.16). The coherence laws between these maps are proved
as equations of natural transformations; `smoothingCommIso` commutes two smoothings.

An `ε`-interleaving is a pair of natural transformations `φ : F ⟶ S_ε G` and
`ψ : G ⟶ S_ε F` whose shifted composites, after `smoothingCompIso ε ε`, are the `ε + ε` units
(Definition 4.1 in the form of Observation 4.12). Interleavings are symmetric, compose with
added parameters, enlarge along `ε ≤ ε'`, are carried to interleavings by smoothing
(Proposition 4.17), and at parameter `0` are equivalent to natural isomorphisms. No
interleaving distance is defined here.

All coherence follows from thinness of the interval category: a functor out of it identifies
parallel morphisms (`map_eq_map_of_interval`). The scoped tactic `interval_coherence`, available
after `open TDA.Reeb`, closes equations between composites of images of interval morphisms.
See `docs/math/reeb-smoothing.md`.
-/

open Set CategoryTheory
open scoped NNReal

universe v u

namespace TDA.Reeb

open OpenInterval

section Smoothing

variable {C : Type u} [Category.{v} C]

/-- Thin-category coherence: a functor out of the interval category identifies parallel
morphisms. Every coherence law below reduces to this. -/
theorem map_eq_map_of_interval (F : OpenInterval ⥤ C) {I J : OpenInterval} (f g : I ⟶ J) :
    F.map f = F.map g :=
  congrArg F.map (Subsingleton.elim f g)

theorem map_comp_map_of_interval (F : OpenInterval ⥤ C) {I J K : OpenInterval} (f : I ⟶ J)
    (g : J ⟶ K) (h : I ⟶ K) : F.map f ≫ F.map g = F.map h :=
  (F.map_comp f g).symm.trans (map_eq_map_of_interval F _ _)

private theorem map_comp_map_comp_map_of_interval (F : OpenInterval ⥤ C) {I J K L : OpenInterval}
    (f : I ⟶ J) (g : J ⟶ K) (k : K ⟶ L) (h : I ⟶ L) :
    F.map f ≫ F.map g ≫ F.map k = F.map h := by
  rw [← F.map_comp, ← F.map_comp]; exact map_eq_map_of_interval F _ _

private theorem map_comp4_of_interval (F : OpenInterval ⥤ C) {I J K L M : OpenInterval}
    (f : I ⟶ J) (g : J ⟶ K) (k : K ⟶ L) (l : L ⟶ M) (h : I ⟶ M) :
    F.map f ≫ F.map g ≫ F.map k ≫ F.map l = F.map h := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp]; exact map_eq_map_of_interval F _ _

private theorem map_comp5_of_interval (F : OpenInterval ⥤ C) {I J K L M N : OpenInterval}
    (f : I ⟶ J) (g : J ⟶ K) (k : K ⟶ L) (l : L ⟶ M) (m : M ⟶ N) (h : I ⟶ N) :
    F.map f ≫ F.map g ≫ F.map k ≫ F.map l ≫ F.map m = F.map h := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp]
  exact map_eq_map_of_interval F _ _

private theorem map_comp6_of_interval (F : OpenInterval ⥤ C) {I J K L M N P : OpenInterval}
    (f : I ⟶ J) (g : J ⟶ K) (k : K ⟶ L) (l : L ⟶ M) (m : M ⟶ N) (n : N ⟶ P) (h : I ⟶ P) :
    F.map f ≫ F.map g ≫ F.map k ≫ F.map l ≫ F.map m ≫ F.map n = F.map h := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp]
  exact map_eq_map_of_interval F _ _

private theorem map_comp2_eq_comp2_of_interval (F : OpenInterval ⥤ C) {I J K J' : OpenInterval}
    (f : I ⟶ J) (g : J ⟶ K) (f' : I ⟶ J') (g' : J' ⟶ K) :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' :=
  (map_comp_map_of_interval F f g (f' ≫ g')).trans (F.map_comp f' g')

private theorem map_comp3_eq_comp2_of_interval (F : OpenInterval ⥤ C) {I J K L J' : OpenInterval}
    (f : I ⟶ J) (g : J ⟶ K) (k : K ⟶ L) (f' : I ⟶ J') (g' : J' ⟶ L) :
    F.map f ≫ F.map g ≫ F.map k = F.map f' ≫ F.map g' :=
  (map_comp_map_comp_map_of_interval F f g k (f' ≫ g')).trans (F.map_comp f' g')

/-- Closes an equation between composites of images of interval morphisms (right-associated,
with an image or an identity on the right-hand side). -/
scoped macro "interval_coherence" : tactic => `(tactic| first
  | exact map_eq_map_of_interval _ _ _
  | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
  | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
  | exact map_comp_map_of_interval _ _ _ _
  | exact map_comp_map_comp_map_of_interval _ _ _ _ _
  | exact map_comp4_of_interval _ _ _ _ _ _
  | exact map_comp5_of_interval _ _ _ _ _ _ _
  | exact map_comp6_of_interval _ _ _ _ _ _ _ _
  | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
  | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
  | exact (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans
      (CategoryTheory.Functor.map_id _ _)
  | exact (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans
      (CategoryTheory.Functor.map_id _ _))

/-- The smoothing endofunctor `S_ε F = T_ε ⋙ F` of precosheaves on the interval category
(DMP Definition 4.14), acting on transformations by whiskering. It is reducible and given by
components, so that `((smoothing ε).obj F).obj I` is reducibly `F.obj (thicken ε I)`; it is
definitionally `(whiskeringLeft _ _ _).obj (thickenFunctor ε)` (`smoothing_eq_whiskeringLeft`). -/
@[reducible] def smoothing (ε : ℝ≥0) : (OpenInterval ⥤ C) ⥤ (OpenInterval ⥤ C) where
  obj F :=
    { obj := fun I => F.obj (thicken ε I)
      map := fun f => F.map ((thickenFunctor ε).map f)
      map_id := fun _ => (map_eq_map_of_interval F _ (𝟙 _)).trans (F.map_id _)
      map_comp := fun _ _ => (map_comp_map_of_interval F _ _ _).symm }
  map α :=
    { app := fun I => α.app (thicken ε I)
      naturality := fun _ _ f => α.naturality ((thickenFunctor ε).map f) }

theorem smoothing_eq_whiskeringLeft (ε : ℝ≥0) :
    (smoothing ε : (OpenInterval ⥤ C) ⥤ _) =
      (Functor.whiskeringLeft OpenInterval OpenInterval C).obj (thickenFunctor ε) := rfl

theorem smoothing_obj (ε : ℝ≥0) (F : OpenInterval ⥤ C) :
    (smoothing ε).obj F = thickenFunctor ε ⋙ F := rfl

theorem smoothing_map (ε : ℝ≥0) {F G : OpenInterval ⥤ C} (α : F ⟶ G) :
    (smoothing ε).map α = Functor.whiskerLeft (thickenFunctor ε) α := rfl

@[simp] theorem smoothing_obj_obj (ε : ℝ≥0) (F : OpenInterval ⥤ C) (I : OpenInterval) :
    ((smoothing ε).obj F).obj I = F.obj (thicken ε I) := rfl

@[simp] theorem smoothing_obj_map (ε : ℝ≥0) (F : OpenInterval ⥤ C) {I J : OpenInterval}
    (f : I ⟶ J) : ((smoothing ε).obj F).map f = F.map ((thickenFunctor ε).map f) := rfl

@[simp] theorem smoothing_map_app (ε : ℝ≥0) {F G : OpenInterval ⥤ C} (α : F ⟶ G)
    (I : OpenInterval) : ((smoothing ε).map α).app I = α.app (thicken ε I) := rfl

/-- The unit `σ^ε : F ⟶ S_ε F`, `F` applied to `I ⊆ T_ε I` (DMP Observation 4.15). -/
def smoothingUnit (ε : ℝ≥0) : 𝟭 (OpenInterval ⥤ C) ⟶ smoothing ε where
  app F := Functor.whiskerRight (thickenUnit ε) F
  naturality F G α := by
    ext I
    exact (α.naturality _).symm

@[simp] theorem smoothingUnit_app_app (ε : ℝ≥0) (F : OpenInterval ⥤ C) (I : OpenInterval) :
    ((smoothingUnit ε).app F).app I = F.map ((thickenUnit ε).app I) := rfl

/-- Enlargement `S_ε ⟶ S_δ` for `ε ≤ δ`. -/
def smoothingMap {ε δ : ℝ≥0} (h : ε ≤ δ) :
    smoothing ε ⟶ (smoothing δ : (OpenInterval ⥤ C) ⥤ _) where
  app F := Functor.whiskerRight (thickenMap h) F
  naturality F G α := by
    ext I
    exact (α.naturality _).symm

@[simp] theorem smoothingMap_app_app {ε δ : ℝ≥0} (h : ε ≤ δ) (F : OpenInterval ⥤ C)
    (I : OpenInterval) : ((smoothingMap h).app F).app I = F.map ((thickenMap h).app I) := rfl

/-- `S_0 ≅ 𝟭`, from `thickenZeroIso`. -/
def smoothingZeroIso : smoothing 0 ≅ 𝟭 (OpenInterval ⥤ C) :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents (fun I => F.mapIso (thickenZeroIso.app I))
      (fun _ => by dsimp; interval_coherence))
    (fun α => by
      ext I
      exact (α.naturality _).symm)

@[simp] theorem smoothingZeroIso_hom_app_app (F : OpenInterval ⥤ C) (I : OpenInterval) :
    (smoothingZeroIso.hom.app F).app I = F.map (thickenZeroIso.hom.app I) := rfl

@[simp] theorem smoothingZeroIso_inv_app_app (F : OpenInterval ⥤ C) (I : OpenInterval) :
    (smoothingZeroIso.inv.app F).app I = F.map (thickenZeroIso.inv.app I) := rfl

/-- `S_ε S_δ ≅ S_(ε+δ)`: the component at `F` is `(T_ε ⋙ T_δ) ⋙ F ≅ T_(ε+δ) ⋙ F`, from
`thickenCompIso ε δ` (DMP Proposition 4.16). -/
def smoothingCompIso (ε δ : ℝ≥0) :
    smoothing δ ⋙ smoothing ε ≅ (smoothing (ε + δ) : (OpenInterval ⥤ C) ⥤ _) :=
  NatIso.ofComponents (fun F => Functor.isoWhiskerRight (thickenCompIso ε δ) F)
    (fun α => by
      ext I
      exact (α.naturality _).symm)

@[simp] theorem smoothingCompIso_hom_app_app (ε δ : ℝ≥0) (F : OpenInterval ⥤ C)
    (I : OpenInterval) :
    ((smoothingCompIso ε δ).hom.app F).app I = F.map ((thickenCompIso ε δ).hom.app I) := rfl

@[simp] theorem smoothingCompIso_inv_app_app (ε δ : ℝ≥0) (F : OpenInterval ⥤ C)
    (I : OpenInterval) :
    ((smoothingCompIso ε δ).inv.app F).app I = F.map ((thickenCompIso ε δ).inv.app I) := rfl

/-! ### Coherence laws (thin-category coherence) -/

theorem smoothingMap_refl (ε : ℝ≥0) :
    smoothingMap (le_refl ε) = 𝟙 (smoothing ε : (OpenInterval ⥤ C) ⥤ _) := by
  ext F I
  dsimp
  interval_coherence

theorem smoothingMap_comp {ε δ γ : ℝ≥0} (h : ε ≤ δ) (h' : δ ≤ γ) :
    smoothingMap h ≫ smoothingMap h' =
      (smoothingMap (h.trans h') : (smoothing ε : (OpenInterval ⥤ C) ⥤ _) ⟶ _) := by
  ext F I
  dsimp
  interval_coherence

/-- The unit is compatible with enlargement: `σ^ε ≫ (S_ε ⟶ S_δ) = σ^δ`. -/
theorem smoothingUnit_comp_smoothingMap {ε δ : ℝ≥0} (h : ε ≤ δ) :
    smoothingUnit ε ≫ smoothingMap h = (smoothingUnit δ : 𝟭 (OpenInterval ⥤ C) ⟶ _) := by
  ext F I
  dsimp
  interval_coherence

/-- The zero unit is the inverse of `S_0 ≅ 𝟭`. -/
theorem smoothingUnit_zero :
    smoothingUnit 0 = (smoothingZeroIso.inv : 𝟭 (OpenInterval ⥤ C) ⟶ _) := by
  ext F I
  dsimp
  interval_coherence

/-- Unit and composition, first form: `F ⟶ S_δ F ⟶ S_ε S_δ F ≅ S_(ε+δ) F` is `σ^(ε+δ)`. -/
theorem smoothingUnit_comp_smoothingUnit (ε δ : ℝ≥0) (F : OpenInterval ⥤ C) :
    (smoothingUnit δ).app F ≫ (smoothingUnit ε).app ((smoothing δ).obj F) ≫
      (smoothingCompIso ε δ).hom.app F = (smoothingUnit (ε + δ)).app F := by
  ext I
  dsimp
  interval_coherence

/-- Unit and composition, second form: `F ⟶ S_ε F ⟶ S_ε S_δ F ≅ S_(ε+δ) F` is `σ^(ε+δ)`. -/
theorem smoothingUnit_comp_map_smoothingUnit (ε δ : ℝ≥0) (F : OpenInterval ⥤ C) :
    (smoothingUnit ε).app F ≫ (smoothing ε).map ((smoothingUnit δ).app F) ≫
      (smoothingCompIso ε δ).hom.app F = (smoothingUnit (ε + δ)).app F := by
  ext I
  dsimp
  interval_coherence

/-- Sum associativity coherence: the two composites `S_ε S_δ S_γ F ⟶ S_((ε+δ)+γ) F` agree. -/
theorem smoothingCompIso_assoc (ε δ γ : ℝ≥0) (F : OpenInterval ⥤ C) :
    (smoothing ε).map ((smoothingCompIso δ γ).hom.app F) ≫
        (smoothingCompIso ε (δ + γ)).hom.app F ≫
        (smoothingMap (add_assoc ε δ γ).ge).app F =
      (smoothingCompIso ε δ).hom.app ((smoothing γ).obj F) ≫
        (smoothingCompIso (ε + δ) γ).hom.app F := by
  ext I
  dsimp
  erw [smoothing_obj_map]
  interval_coherence

/-- Left unitality: `S_0 S_δ ≅ S_(0+δ)` agrees with `S_0 ≅ 𝟭` at `S_δ F`. -/
theorem smoothingCompIso_zero_left (δ : ℝ≥0) (F : OpenInterval ⥤ C) :
    (smoothingCompIso 0 δ).hom.app F ≫ (smoothingMap (zero_add δ).le).app F =
      smoothingZeroIso.hom.app ((smoothing δ).obj F) := by
  ext I
  dsimp
  interval_coherence

/-- Right unitality: `S_δ S_0 ≅ S_(δ+0)` agrees with `S_δ` applied to `S_0 ≅ 𝟭`. -/
theorem smoothingCompIso_zero_right (δ : ℝ≥0) (F : OpenInterval ⥤ C) :
    (smoothingCompIso δ 0).hom.app F ≫ (smoothingMap (add_zero δ).le).app F =
      (smoothing δ).map (smoothingZeroIso.hom.app F) := by
  ext I
  dsimp
  interval_coherence

/-- `S_ε S_δ ≅ S_δ S_ε`, through `S_(δ+ε) = S_(ε+δ)`. -/
def smoothingCommIso (ε δ : ℝ≥0) :
    smoothing ε ⋙ smoothing δ ≅ (smoothing δ ⋙ smoothing ε : (OpenInterval ⥤ C) ⥤ _) where
  hom := (smoothingCompIso δ ε).hom ≫ smoothingMap (add_comm δ ε).le ≫ (smoothingCompIso ε δ).inv
  inv := (smoothingCompIso ε δ).hom ≫ smoothingMap (add_comm ε δ).le ≫ (smoothingCompIso δ ε).inv
  hom_inv_id := by
    ext F I
    dsimp
    simp only [Category.assoc]
    interval_coherence
  inv_hom_id := by
    ext F I
    dsimp
    simp only [Category.assoc]
    interval_coherence

theorem smoothingCommIso_hom_app_app (ε δ : ℝ≥0) (F : OpenInterval ⥤ C)
    (I : OpenInterval) :
    ((smoothingCommIso ε δ).hom.app F).app I =
      F.map (homOfLE (thicken_comm ε δ I).le) := by
  dsimp [smoothingCommIso]
  interval_coherence

/-- The smoothing of the empty interval is the value on the empty interval. -/
def smoothingObjBotIso (ε : ℝ≥0) (F : OpenInterval ⥤ C) :
    ((smoothing ε).obj F).obj ⊥ ≅ F.obj ⊥ :=
  F.mapIso (eqToIso (thicken_bot ε))

/-! ### Interleavings -/

/-- An `ε`-interleaving of precosheaves (DMP Definition 4.1 via Observation 4.12): natural
transformations `φ : F ⟶ S_ε G` and `ψ : G ⟶ S_ε F` whose shifted composites
`F ⟶ S_ε G ⟶ S_ε S_ε F ≅ S_(ε+ε) F` and `G ⟶ S_ε F ⟶ S_ε S_ε G ≅ S_(ε+ε) G` are the
`ε + ε` units. -/
structure Interleaving (ε : ℝ≥0) (F G : OpenInterval ⥤ C) where
  /-- `F ⟶ S_ε G`. -/
  φ : F ⟶ (smoothing ε).obj G
  /-- `G ⟶ S_ε F`. -/
  ψ : G ⟶ (smoothing ε).obj F
  φ_ψ : φ ≫ (smoothing ε).map ψ ≫ (smoothingCompIso ε ε).hom.app F =
    (smoothingUnit (ε + ε)).app F
  ψ_φ : ψ ≫ (smoothing ε).map φ ≫ (smoothingCompIso ε ε).hom.app G =
    (smoothingUnit (ε + ε)).app G

namespace Interleaving

variable {ε δ : ℝ≥0} {F G H : OpenInterval ⥤ C}

@[ext] theorem ext {i j : Interleaving ε F G} (hφ : i.φ = j.φ) (hψ : i.ψ = j.ψ) : i = j := by
  cases i; cases j; cases hφ; cases hψ; rfl

/-- Objectwise triangle (DMP (4.3)): `ψ_(T_ε I) ∘ φ_I = F[I ⊆ T_ε T_ε I]`. -/
@[reassoc]
theorem φ_ψ_app (i : Interleaving ε F G) (I : OpenInterval) :
    i.φ.app I ≫ i.ψ.app (thicken ε I) =
      F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε _))) := by
  have h : i.φ.app I ≫ i.ψ.app (thicken ε I) ≫ F.map (homOfLE (thicken_thicken' ε ε I).le) =
      F.map (homOfLE (le_thicken (ε + ε) I)) := congrArg (fun t => NatTrans.app t I) i.φ_ψ
  have e : F.map (homOfLE (thicken_thicken' ε ε I).le) ≫
      F.map (homOfLE (thicken_thicken' ε ε I).ge) = 𝟙 _ :=
    (map_comp_map_of_interval F _ _ (𝟙 _)).trans (F.map_id _)
  rw [← Category.comp_id (i.φ.app I ≫ i.ψ.app (thicken ε I)), ← e]
  simp only [Category.assoc]
  rw [reassoc_of% h]
  exact map_comp_map_of_interval F _ _ _

/-- Objectwise triangle (DMP (4.3)): `φ_(T_ε I) ∘ ψ_I = G[I ⊆ T_ε T_ε I]`. -/
@[reassoc]
theorem ψ_φ_app (i : Interleaving ε F G) (I : OpenInterval) :
    i.ψ.app I ≫ i.φ.app (thicken ε I) =
      G.map (homOfLE ((le_thicken ε I).trans (le_thicken ε _))) := by
  have h : i.ψ.app I ≫ i.φ.app (thicken ε I) ≫ G.map (homOfLE (thicken_thicken' ε ε I).le) =
      G.map (homOfLE (le_thicken (ε + ε) I)) := congrArg (fun t => NatTrans.app t I) i.ψ_φ
  have e : G.map (homOfLE (thicken_thicken' ε ε I).le) ≫
      G.map (homOfLE (thicken_thicken' ε ε I).ge) = 𝟙 _ :=
    (map_comp_map_of_interval G _ _ (𝟙 _)).trans (G.map_id _)
  rw [← Category.comp_id (i.ψ.app I ≫ i.φ.app (thicken ε I)), ← e]
  simp only [Category.assoc]
  rw [reassoc_of% h]
  exact map_comp_map_of_interval G _ _ _

/-- Componentwise triangle with an arbitrary middle map: `φ_I ≫ G[g] ≫ ψ_K = F[I ⊆ T_ε K]`. -/
@[reassoc]
theorem φ_map_ψ (i : Interleaving ε F G) {I K : OpenInterval} (g : thicken ε I ⟶ K) :
    i.φ.app I ≫ G.map g ≫ i.ψ.app K =
      F.map (homOfLE ((le_thicken ε I).trans (g.le.trans (le_thicken ε K)))) := by
  have e1 : i.φ.app I ≫ G.map g ≫ i.ψ.app K =
      i.φ.app I ≫ i.ψ.app (thicken ε I) ≫ F.map ((thickenFunctor ε).map g) :=
    congrArg (fun t => i.φ.app I ≫ t) (i.ψ.naturality g)
  rw [e1]
  erw [i.φ_ψ_app_assoc]
  exact map_comp_map_of_interval F _ _ _

/-- Componentwise triangle with an arbitrary middle map: `ψ_I ≫ F[g] ≫ φ_K = G[I ⊆ T_ε K]`. -/
@[reassoc]
theorem ψ_map_φ (i : Interleaving ε F G) {I K : OpenInterval} (g : thicken ε I ⟶ K) :
    i.ψ.app I ≫ F.map g ≫ i.φ.app K =
      G.map (homOfLE ((le_thicken ε I).trans (g.le.trans (le_thicken ε K)))) := by
  have e1 : i.ψ.app I ≫ F.map g ≫ i.φ.app K =
      i.ψ.app I ≫ i.φ.app (thicken ε I) ≫ G.map ((thickenFunctor ε).map g) :=
    congrArg (fun t => i.ψ.app I ≫ t) (i.φ.naturality g)
  rw [e1]
  erw [i.ψ_φ_app_assoc]
  exact map_comp_map_of_interval G _ _ _

/-- Two middle maps: `φ_I ≫ G[g₁] ≫ G[g₂] ≫ ψ_K = F[I ⊆ T_ε K]`. -/
@[reassoc]
theorem φ_map_map_ψ (i : Interleaving ε F G) {I J K : OpenInterval} (g₁ : thicken ε I ⟶ J)
    (g₂ : J ⟶ K) :
    i.φ.app I ≫ G.map g₁ ≫ G.map g₂ ≫ i.ψ.app K =
      F.map (homOfLE ((le_thicken ε I).trans ((g₁ ≫ g₂).le.trans (le_thicken ε K)))) := by
  rw [← G.map_comp_assoc]; exact i.φ_map_ψ (g₁ ≫ g₂)

/-- Two middle maps: `ψ_I ≫ F[g₁] ≫ F[g₂] ≫ φ_K = G[I ⊆ T_ε K]`. -/
@[reassoc]
theorem ψ_map_map_φ (i : Interleaving ε F G) {I J K : OpenInterval} (g₁ : thicken ε I ⟶ J)
    (g₂ : J ⟶ K) :
    i.ψ.app I ≫ F.map g₁ ≫ F.map g₂ ≫ i.φ.app K =
      G.map (homOfLE ((le_thicken ε I).trans ((g₁ ≫ g₂).le.trans (le_thicken ε K)))) := by
  rw [← F.map_comp_assoc]; exact i.ψ_map_φ (g₁ ≫ g₂)

/-- Objectwise constructor: natural transformations satisfying the componentwise triangle
identities of DMP (4.3) form an interleaving. -/
def ofApp (φ : F ⟶ (smoothing ε).obj G) (ψ : G ⟶ (smoothing ε).obj F)
    (hφψ : ∀ I, φ.app I ≫ ψ.app (thicken ε I) =
      F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε _))))
    (hψφ : ∀ I, ψ.app I ≫ φ.app (thicken ε I) =
      G.map (homOfLE ((le_thicken ε I).trans (le_thicken ε _)))) :
    Interleaving ε F G where
  φ := φ
  ψ := ψ
  φ_ψ := by
    ext I
    change φ.app I ≫ ψ.app (thicken ε I) ≫ F.map (homOfLE (thicken_thicken' ε ε I).le) =
      F.map (homOfLE (le_thicken (ε + ε) I))
    rw [reassoc_of% (hφψ I)]
    exact map_comp_map_of_interval F _ _ _
  ψ_φ := by
    ext I
    change ψ.app I ≫ φ.app (thicken ε I) ≫ G.map (homOfLE (thicken_thicken' ε ε I).le) =
      G.map (homOfLE (le_thicken (ε + ε) I))
    rw [reassoc_of% (hψφ I)]
    exact map_comp_map_of_interval G _ _ _

/-- Symmetry. -/
def symm (i : Interleaving ε F G) : Interleaving ε G F where
  φ := i.ψ
  ψ := i.φ
  φ_ψ := i.ψ_φ
  ψ_φ := i.φ_ψ

/-- Identity witnesses: `F` is `ε`-interleaved with itself by the units. -/
def refl (ε : ℝ≥0) (F : OpenInterval ⥤ C) : Interleaving ε F F :=
  ofApp ((smoothingUnit ε).app F) ((smoothingUnit ε).app F)
    (fun I => by dsimp; interval_coherence) (fun I => by dsimp; interval_coherence)

/-- Enlargement: an `ε`-interleaving is an `ε'`-interleaving for `ε ≤ ε'`. -/
def mono (i : Interleaving ε F G) {ε' : ℝ≥0} (h : ε ≤ ε') : Interleaving ε' F G :=
  ofApp (i.φ ≫ (smoothingMap h).app G) (i.ψ ≫ (smoothingMap h).app F)
    (fun I => by
      dsimp
      simp only [Category.assoc]
      erw [i.φ_map_ψ_assoc]
      interval_coherence)
    (fun I => by
      dsimp
      simp only [Category.assoc]
      erw [i.ψ_map_φ_assoc]
      interval_coherence)

/-- Composition: `F ↔ G` at `ε` and `G ↔ H` at `δ` give `F ↔ H` at `ε + δ`, with
`F(I) → G(T_ε I) → H(T_δ T_ε I)` and `H(I) → G(T_δ I) → F(T_ε T_δ I)`. -/
def trans (i : Interleaving ε F G) (j : Interleaving δ G H) : Interleaving (ε + δ) F H :=
  ofApp (i.φ ≫ (smoothing ε).map j.φ ≫ (smoothingCompIso ε δ).hom.app H)
    (j.ψ ≫ (smoothing δ).map i.ψ ≫ (smoothingCompIso δ ε).hom.app F ≫
      (smoothingMap (add_comm δ ε).le).app F)
    (fun I => by
      dsimp
      simp only [Category.assoc]
      erw [j.φ_map_ψ_assoc, i.φ_map_ψ_assoc]
      interval_coherence)
    (fun I => by
      dsimp
      simp only [Category.assoc]
      erw [i.ψ_map_map_φ_assoc, j.ψ_map_φ_assoc]
      interval_coherence)

/-- A natural isomorphism gives a `0`-interleaving. -/
def ofIso (e : F ≅ G) : Interleaving 0 F G :=
  ofApp (e.hom ≫ (smoothingUnit 0).app G) (e.inv ≫ (smoothingUnit 0).app F)
    (fun I => by
      dsimp
      simp only [Category.assoc]
      erw [e.inv.naturality_assoc, e.hom_inv_id_app_assoc]
      interval_coherence)
    (fun I => by
      dsimp
      simp only [Category.assoc]
      erw [e.hom.naturality_assoc, e.inv_hom_id_app_assoc]
      interval_coherence)

/-- A `0`-interleaving gives a natural isomorphism (DMP: "when `ε = 0` this is precisely an
isomorphism"). -/
def toIso (i : Interleaving 0 F G) : F ≅ G where
  hom := i.φ ≫ smoothingZeroIso.hom.app G
  inv := i.ψ ≫ smoothingZeroIso.hom.app F
  hom_inv_id := by
    ext I
    dsimp
    simp only [Category.assoc]
    erw [i.φ_map_ψ_assoc]
    interval_coherence
  inv_hom_id := by
    ext I
    dsimp
    simp only [Category.assoc]
    erw [i.ψ_map_φ_assoc]
    interval_coherence

/-- Zero-interleaving witnesses are equivalent to natural isomorphisms. -/
def zeroEquivIso : Interleaving 0 F G ≃ (F ≅ G) where
  toFun := toIso
  invFun := ofIso
  left_inv i := by
    ext : 1
    · change (i.φ ≫ smoothingZeroIso.hom.app G) ≫ (smoothingUnit 0).app G = i.φ
      rw [smoothingUnit_zero, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    · change (i.ψ ≫ smoothingZeroIso.hom.app F) ≫ (smoothingUnit 0).app F = i.ψ
      rw [smoothingUnit_zero, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  right_inv e := by
    apply Iso.ext
    change (e.hom ≫ (smoothingUnit 0).app G) ≫ smoothingZeroIso.hom.app G = e.hom
    rw [smoothingUnit_zero, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _

/-- Smoothing is nonexpansive on witnesses (DMP Proposition 4.17): `S_ε` carries a
`δ`-interleaving of `F, G` to a `δ`-interleaving of `S_ε F, S_ε G`. -/
def smooth (i : Interleaving δ F G) (ε : ℝ≥0) :
    Interleaving δ ((TDA.Reeb.smoothing ε).obj F) ((TDA.Reeb.smoothing ε).obj G) :=
  ofApp ((TDA.Reeb.smoothing ε).map i.φ ≫ (smoothingCommIso δ ε).hom.app G)
    ((TDA.Reeb.smoothing ε).map i.ψ ≫ (smoothingCommIso δ ε).hom.app F)
    (fun I => by
      dsimp
      rw [smoothingCommIso_hom_app_app, smoothingCommIso_hom_app_app]
      simp only [Category.assoc]
      erw [i.φ_map_ψ_assoc]
      interval_coherence)
    (fun I => by
      dsimp
      rw [smoothingCommIso_hom_app_app, smoothingCommIso_hom_app_app]
      simp only [Category.assoc]
      erw [i.ψ_map_φ_assoc]
      interval_coherence)

/-- A precosheaf is `ε`-interleaved with its own smoothing: `φ = σ^ε ≫ σ^ε` and `ψ = 𝟙`. -/
def selfSmoothing (ε : ℝ≥0) (F : OpenInterval ⥤ C) :
    Interleaving ε F ((TDA.Reeb.smoothing ε).obj F) :=
  ofApp ((smoothingUnit ε).app F ≫ (smoothingUnit ε).app ((TDA.Reeb.smoothing ε).obj F))
    (𝟙 _)
    (fun I => by dsimp; rw [Category.comp_id]; interval_coherence)
    (fun I => by dsimp; rw [Category.id_comp]; interval_coherence)

end Interleaving

end Smoothing

end TDA.Reeb
