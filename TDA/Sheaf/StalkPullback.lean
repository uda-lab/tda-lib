import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Stalks and sections of the inverse image of a sheaf of modules

Let `k` be a ring and `f : X ⟶ Y` a continuous map in `TopCat`. The sheaf inverse image
`f⁻¹ = TopCat.Sheaf.pullback (ModuleCat k) f` is left adjoint to the direct image `f_*`
(`TopCat.Sheaf.pullbackPushforwardAdjunction`). Mathlib computes the stalks of the presheaf
inverse image (`TopCat.Presheaf.stalkPullbackIso`); this file transfers the computation to
sheaves.

* `pullbackPushforwardAdjunction_unit_app_hom`: the unit `F ⟶ f_* f⁻¹ F` of the sheaf adjunction
  is the unit of the presheaf adjunction, followed by sheafification and the comparison
  `TopCat.Sheaf.pullbackIso` of `f⁻¹` with the sheafified presheaf inverse image.
* `stalkPullbackSheafIso f F x : F_{f x} ≅ (f⁻¹ F)_x`, the stalk of the sheaf inverse image.
* `germ_stalkPullbackSheafIso_hom` and `stalkPullbackSheafIso_unit`: the isomorphism sends the
  germ at `f x` of a section `n` over `V` to the germ at `x` of the image of `n` under the
  adjunction unit.
* `stalkPullbackSheafIso_hom_naturality`: the isomorphism is natural in `F`;
  `stalkPullbackSheafNatIso f x` packages it as a natural isomorphism of functors
  `Sh Y ⥤ ModuleCat k`.
* `pullbackSectionsIso hf V`: for an open embedding `f`, sections of `f⁻¹ F` over an open `V`
  are the sections of `F` over the open image `f(V)`, naturally in `F` (Mathlib's
  `IsOpenEmbedding.sheafPullbackIso`). `pullbackOpenSectionsIso U` is the case of the inclusion
  of an open `U` and `V` the whole of `U`: `Γ(U, ι⁻¹ F) ≅ F(U)`.
* `pullbackUnitRes f G hWB : G(B) ⟶ (f⁻¹ G)(W)`, for opens `W ⊆ f⁻¹ B`, is the adjunction unit on
  sections over `B` followed by restriction to `W`; its germs are given by
  `stalkPullbackSheafIso` (`germ_pullbackUnitRes`). It is natural in `G`
  (`pullbackUnitRes_naturality`) and compatible with restriction (`pullbackUnitRes_map`). If
  every point of `B` is the image of a point of `W`, it is injective
  (`injective_pullbackUnitRes`). If moreover `f` sends open subsets of `W` to open sets and the
  fibres `W ∩ f⁻¹ {y}`, `y ∈ B`, are preconnected, it is surjective
  (`surjective_pullbackUnitRes`), hence bijective and an isomorphism
  (`bijective_pullbackUnitRes`, `isIso_pullbackUnitRes`).
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable (k : Type) [Ring k]

/-- The unit of the sheaf adjunction `f⁻¹ ⊣ f_*` at `F` is the unit of the presheaf adjunction,
followed by sheafification of `f⁻¹ F` and the inverse of `TopCat.Sheaf.pullbackIso`. -/
theorem pullbackPushforwardAdjunction_unit_app_hom {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : Y.Sheaf (ModuleCat.{0} k)) :
    (TopCat.Presheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F.presheaf ≫
      (TopCat.Presheaf.pushforward _ f).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback (ModuleCat.{0} k) f).obj F.presheaf) ≫
            ((TopCat.Sheaf.pullbackIso (ModuleCat.{0} k) f).inv.app F).hom) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F).hom := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) (ModuleCat.{0} k)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f) F
  rw [← h]
  rfl

/-- **Stalks of the sheaf inverse image.** For a continuous map `f : X ⟶ Y`, a sheaf `F` of
`k`-modules on `Y` and `x : X`, the stalk of `f⁻¹ F` at `x` is the stalk of `F` at `f x`. -/
def stalkPullbackSheafIso {X Y : TopCat.{0}} (f : X ⟶ Y) (F : Y.Sheaf (ModuleCat.{0} k))
    (x : X) :
    F.presheaf.stalk (f x) ≅ ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj F).presheaf.stalk x :=
  TopCat.Presheaf.stalkPullbackIso _ f F.presheaf x ≪≫
    @asIso _ _ _ _ ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback (ModuleCat.{0} k) f).obj F.presheaf)))
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} k) _) ≪≫
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).mapIso
      ((sheafToPresheaf _ _).mapIso ((TopCat.Sheaf.pullbackIso (ModuleCat.{0} k) f).app F).symm)

/-- `stalkPullbackSheafIso` on germs: the germ of a section over `V` at `f x` goes to the germ at
`x` of its image under the adjunction unit `F ⟶ f_* f⁻¹ F`. -/
@[reassoc]
theorem germ_stalkPullbackSheafIso_hom {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : Y.Sheaf (ModuleCat.{0} k)) (V : Opens Y) (x : X) (hx : f x ∈ V) :
    F.presheaf.germ V (f x) hx ≫ (stalkPullbackSheafIso k f F x).hom =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F).hom.app
          (op V) ≫
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj F).presheaf.germ
          ((Opens.map f).obj V) x hx := by
  rw [← pullbackPushforwardAdjunction_unit_app_hom]
  change F.presheaf.germ V (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom _ f F.presheaf x ≫
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback (ModuleCat.{0} k) f).obj F.presheaf)) ≫
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).map
      ((TopCat.Sheaf.pullbackIso (ModuleCat.{0} k) f).inv.app F).hom = _
  rw [TopCat.Presheaf.germ_stalkPullbackHom_assoc]
  -- The membership proof `hx : f x ∈ V` is used at type `x ∈ (Opens.map f).obj V`, so the
  -- rewrite motive is only correct up to unfolding.
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- `stalkPullbackSheafIso` on elements: the germ of `n` at `f x` corresponds to the germ at `x`
of the image of `n` under the adjunction unit `F ⟶ f_* f⁻¹ F`. -/
theorem stalkPullbackSheafIso_unit {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : Y.Sheaf (ModuleCat.{0} k)) (V : Opens Y) (x : X) (hx : f x ∈ V)
    (n : F.presheaf.obj (op V)) :
    (stalkPullbackSheafIso k f F x).hom (F.presheaf.germ V (f x) hx n) =
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj F).presheaf.germ ((Opens.map f).obj V) x hx
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F).hom.app
          (op V) n) :=
  ConcreteCategory.congr_hom (germ_stalkPullbackSheafIso_hom k f F V x hx) n

/-- **Naturality of `stalkPullbackSheafIso`.** For a morphism `φ : F ⟶ G` of sheaves on `Y`, the
stalk map of `φ` at `f x` corresponds to the stalk map of `f⁻¹ φ` at `x`. -/
@[reassoc]
theorem stalkPullbackSheafIso_hom_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F G : Y.Sheaf (ModuleCat.{0} k)} (φ : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) (f x)).map φ.hom ≫
        (stalkPullbackSheafIso k f G x).hom =
      (stalkPullbackSheafIso k f F x).hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).map
          ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).map φ).hom := by
  refine ConcreteCategory.hom_ext _ _ fun g => ?_
  obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf g
  -- The unit `F ⟶ f_* f⁻¹ F` is natural in `F`; read it on sections over `V`.
  have h := congrArg (fun ψ => ψ.hom.app (Opposite.op V))
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.naturality φ)
  refine (congrArg (stalkPullbackSheafIso k f G x).hom
    (TopCat.Presheaf.stalkFunctor_map_germ_apply V (f x) hV φ.hom s)).trans ?_
  refine (stalkPullbackSheafIso_unit k f G V x hV _).trans ?_
  refine Eq.trans ?_ (congrArg _ (stalkPullbackSheafIso_unit k f F V x hV s)).symm
  refine Eq.trans ?_ (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map f).obj V) x hV
    ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).map φ).hom
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F).hom.app
      (Opposite.op V) s)).symm
  exact congrArg _ (ConcreteCategory.congr_hom h s)

/-- `stalkPullbackSheafIso` as a natural isomorphism: the stalk at `f x` is naturally isomorphic
to the stalk at `x` of the sheaf inverse image along `f`. -/
def stalkPullbackSheafNatIso {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    TopCat.Sheaf.forget (ModuleCat.{0} k) Y ⋙ TopCat.Presheaf.stalkFunctor _ (f x) ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} k) f ⋙ TopCat.Sheaf.forget _ X ⋙
        TopCat.Presheaf.stalkFunctor _ x :=
  NatIso.ofComponents (fun F => stalkPullbackSheafIso k f F x)
    (fun φ => stalkPullbackSheafIso_hom_naturality k f φ x)

/-- The components of `stalkPullbackSheafNatIso` are `stalkPullbackSheafIso`. -/
@[simp]
theorem stalkPullbackSheafNatIso_app {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X)
    (F : Y.Sheaf (ModuleCat.{0} k)) :
    (stalkPullbackSheafNatIso k f x).app F = stalkPullbackSheafIso k f F x := rfl

/-- **Sections of the inverse image along an open embedding.** For an open embedding
`f : X ⟶ Y` and an open `V` of `X`, the sections of `f⁻¹ F` over `V` are the sections of `F`
over the open image `f(V)`, naturally in the sheaf `F` of `k`-modules on `Y`. -/
def pullbackSectionsIso {X Y : TopCat.{0}} {f : X ⟶ Y} (hf : Topology.IsOpenEmbedding f)
    (V : Opens X) :
    TopCat.Sheaf.pullback (ModuleCat.{0} k) f ⋙ sheafToPresheaf _ _ ⋙
        (evaluation _ _).obj (op V) ≅
      sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (hf.functor.obj V)) :=
  Functor.isoWhiskerRight (hf.sheafPullbackIso (ModuleCat.{0} k))
      (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)) ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **Sections of the restriction to an open.** For an open `U` of `X` with inclusion `ι`, the
global sections of `ι⁻¹ F` are the sections of `F` over `U`, naturally in the sheaf `F` of
`k`-modules on `X`. -/
def pullbackOpenSectionsIso {X : TopCat.{0}} (U : Opens X) :
    TopCat.Sheaf.pullback (ModuleCat.{0} k) U.inclusion' ⋙ sheafToPresheaf _ _ ⋙
        (evaluation _ _).obj (op ⊤) ≅
      sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U) :=
  pullbackSectionsIso k U.isOpenEmbedding ⊤ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      ((evaluation _ _).mapIso (eqToIso (congrArg op (Opens.isOpenEmbedding_obj_top U))))

section unitRes

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (G : Y.Sheaf (ModuleCat.{0} k))

/-- The adjunction unit of `f⁻¹ ⊣ f_*` on sections over `B`, followed by restriction to an open
`W ⊆ f⁻¹ B`: the map `G(B) ⟶ (f⁻¹ G)(f⁻¹ B) ⟶ (f⁻¹ G)(W)`. -/
def pullbackUnitRes {W : Opens X} {B : Opens Y} (hWB : W ≤ (Opens.map f).obj B) :
    G.presheaf.obj (op B) ⟶
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.obj (op W) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app G).hom.app (op B) ≫
    ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.map (homOfLE hWB).op

/-- Germs of `pullbackUnitRes`: at `x ∈ W`, the germ of the image of `s` is the image of the germ
of `s` at `f x` under `stalkPullbackSheafIso`. -/
theorem germ_pullbackUnitRes {W : Opens X} {B : Opens Y} (hWB : W ≤ (Opens.map f).obj B)
    (s : G.presheaf.obj (op B)) (x : X) (hx : x ∈ W) :
    ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ W x hx
        ((pullbackUnitRes k f G hWB).hom s) =
      (stalkPullbackSheafIso k f G x).hom (G.presheaf.germ B (f x) (hWB hx) s) := by
  refine Eq.trans ?_ (stalkPullbackSheafIso_unit k f G B x (hWB hx) s).symm
  exact TopCat.Presheaf.germ_res_apply _ (homOfLE hWB) x hx _

/-- Equal germs upstairs of unit images give equal germs downstairs. -/
private theorem germ_eq_of_germ_unit_eq {z : X} {O O' : Opens Y} (h : f z ∈ O) (h' : f z ∈ O')
    (σ : G.presheaf.obj (op O)) (σ' : G.presheaf.obj (op O'))
    (he : ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ ((Opens.map f).obj O)
        z h (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app
          G).hom.app (op O) σ) =
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ ((Opens.map f).obj O')
        z h' (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app
          G).hom.app (op O') σ')) :
    G.presheaf.germ O (f z) h σ = G.presheaf.germ O' (f z) h' σ' := by
  apply (stalkPullbackSheafIso k f G z).toLinearEquiv.injective
  change (stalkPullbackSheafIso k f G z).hom _ = (stalkPullbackSheafIso k f G z).hom _
  rw [stalkPullbackSheafIso_unit, stalkPullbackSheafIso_unit]
  exact he

/-- A local representative of a section of `f⁻¹ G` near `z`. -/
private theorem exists_rep {W : Opens X}
    (t : ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.obj (op W)) {z : X}
    (hz : z ∈ W) :
    ∃ (O : Opens Y) (_ : f z ∈ O) (σ : G.presheaf.obj (op O)) (N : Opens X) (_ : z ∈ N)
      (hNW : N ≤ W) (hNO : N ≤ (Opens.map f).obj O),
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.map (homOfLE hNO).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app G).hom.app
            (op O) σ) =
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.map (homOfLE hNW).op t := by
  obtain ⟨O, hO, σ, hσ⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf
    ((stalkPullbackSheafIso k f G z).inv
      (((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ W z hz t))
  have he : ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ
      ((Opens.map f).obj O) z hO
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app G).hom.app
          (op O) σ) =
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ W z hz t := by
    rw [← stalkPullbackSheafIso_unit, hσ, Iso.inv_hom_id_apply]
  obtain ⟨N, hzN, i₁, i₂, hN⟩ := TopCat.Presheaf.germ_eq
    ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf z hO hz _ _ he
  exact ⟨O, hO, σ, N, hzN, leOfHom i₂, leOfHom i₁, hN⟩

/-- **Injectivity.** If every point of `B` is the image of a point of `W`, a section of `G` over
`B` whose image in `f⁻¹ G` vanishes over `W` is zero. -/
theorem injective_pullbackUnitRes {W : Opens X} {B : Opens Y} (hWB : W ≤ (Opens.map f).obj B)
    (himage : ∀ y ∈ B, ∃ x ∈ W, f x = y) :
    Function.Injective (pullbackUnitRes k f G hWB).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext G B s 0 fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := himage y hy
  apply (stalkPullbackSheafIso k f G x).toLinearEquiv.injective
  change (stalkPullbackSheafIso k f G x).hom _ = (stalkPullbackSheafIso k f G x).hom _
  rw [map_zero, map_zero]
  exact (germ_pullbackUnitRes k f G hWB s x hx).symm.trans (by rw [hs, map_zero])

/-- **Surjectivity.** If `f` maps `W` onto `B`, maps open subsets of `W` to open sets, and has
preconnected fibres `W ∩ f⁻¹ {y}` over `B`, every section of `f⁻¹ G` over `W` comes from a
section of `G` over `B`. Local representatives are glued along the cover of `B` by their open
images; on a fibre their germs agree because they are locally constant on a preconnected set. -/
theorem surjective_pullbackUnitRes {W : Opens X} {B : Opens Y} (hWB : W ≤ (Opens.map f).obj B)
    (himage : ∀ y ∈ B, ∃ x ∈ W, f x = y)
    (hopen : ∀ O : Opens X, O ≤ W → IsOpen (f '' (O : Set X)))
    (hconn : ∀ y ∈ B, _root_.IsPreconnected ((W : Set X) ∩ f ⁻¹' {y})) :
    Function.Surjective (pullbackUnitRes k f G hWB).hom := by
  intro t
  -- Representatives at every point of `W`.
  have hrep := fun z : W => exists_rep k f G t z.2
  choose O hO σ N hzN hNW hNO hN using hrep
  -- On `N z`, the unit image of `σ z` has the germs of `t`.
  have hloc : ∀ (z : W) (w : X) (hw : w ∈ N z),
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ
          ((Opens.map f).obj (O z)) w (hNO z hw)
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app G).hom.app
            (op (O z)) (σ z)) =
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ W w (hNW z hw) t := by
    intro z w hw
    have h := congrArg
      (((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ (N z) w hw) (hN z)
    -- The unit lands in `(𝟭 _).obj G` up to unfolding, so the germ rewrite needs `erw`.
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
    exact h
  -- Fact A: near `z` the representatives agree with the local ones.
  have hA : ∀ (z w : W) (hw : (w : X) ∈ N z) (x : Y) (h₁ : x ∈ O z) (h₂ : x ∈ O w), f w = x →
      G.presheaf.germ (O z) x h₁ (σ z) = G.presheaf.germ (O w) x h₂ (σ w) := by
    rintro z w hw x h₁ h₂ rfl
    refine germ_eq_of_germ_unit_eq k f G (hNO z hw) (hO w) _ _ ?_
    rw [hloc z w hw, hloc w w (hzN w)]
  -- Fact B: on a fibre, all representatives have the same germ.
  have hB : ∀ (y : Y) (hy : y ∈ B) (z w : W) (h₁ : y ∈ O z) (h₂ : y ∈ O w), f z = y → f w = y →
      G.presheaf.germ (O z) y h₁ (σ z) = G.presheaf.germ (O w) y h₂ (σ w) := by
    intro y hy z w h₁ h₂ hz hw
    have hpc := Subtype.preconnectedSpace (hconn y hy)
    have hmem : ∀ u : ((W : Set X) ∩ f ⁻¹' {y} : Set X), y ∈ O ⟨u.1, u.2.1⟩ := fun u =>
      (congrArg (fun a => a ∈ O ⟨u.1, u.2.1⟩) (show f u.1 = y from u.2.2)).mp (hO _)
    let c : ((W : Set X) ∩ f ⁻¹' {y} : Set X) → G.presheaf.stalk y := fun u =>
      G.presheaf.germ (O ⟨u.1, u.2.1⟩) y (hmem u) (σ ⟨u.1, u.2.1⟩)
    have hc : IsLocallyConstant c := by
      rw [IsLocallyConstant.iff_exists_open]
      intro u
      refine ⟨Subtype.val ⁻¹' (N ⟨u.1, u.2.1⟩ : Set X),
        (N _).isOpen.preimage continuous_subtype_val, hzN _, fun u' hu' => ?_⟩
      exact (hA ⟨u.1, u.2.1⟩ ⟨u'.1, u'.2.1⟩ hu' y _ _ u'.2.2).symm
    exact hc.apply_eq_of_preconnectedSpace ⟨z, z.2, hz⟩ ⟨w, w.2, hw⟩
  -- The cover of `B` by the images of the `N z`.
  let V : W → Opens Y := fun z => ⟨f '' (N z : Set X), hopen (N z) (hNW z)⟩
  have hVO : ∀ z, V z ≤ O z := by
    rintro z _ ⟨w, hw, rfl⟩
    exact hNO z hw
  have hVB : ∀ z, V z ≤ B := by
    rintro z _ ⟨w, hw, rfl⟩
    exact hWB (hNW z hw)
  let sf : ∀ z : W, G.presheaf.obj (op (V z)) := fun z => G.presheaf.map (homOfLE (hVO z)).op (σ z)
  have hgerm : ∀ (z : W) (x : Y) (hx : x ∈ V z),
      G.presheaf.germ (V z) x hx (sf z) = G.presheaf.germ (O z) x (hVO z hx) (σ z) :=
    fun z x hx => TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (hVO z)) x hx (σ z)
  -- Two representatives agree at every point of the overlap of their images.
  have hpair : ∀ (i j : W) (x : Y) (hi : x ∈ V i) (hj : x ∈ V j),
      G.presheaf.germ (O i) x (hVO i hi) (σ i) = G.presheaf.germ (O j) x (hVO j hj) (σ j) := by
    intro i j x hi hj
    obtain ⟨w, hw, hwx⟩ := hi
    obtain ⟨w', hw', hw'x⟩ := hj
    have hxB : x ∈ B := hVB i ⟨w, hw, hwx⟩
    have hxw : x ∈ O ⟨w, hNW i hw⟩ := hwx ▸ hO _
    have hxw' : x ∈ O ⟨w', hNW j hw'⟩ := hw'x ▸ hO _
    rw [hA i ⟨w, hNW i hw⟩ hw x _ hxw hwx,
      hB x hxB ⟨w, hNW i hw⟩ ⟨w', hNW j hw'⟩ hxw hxw' hwx hw'x,
      ← hA j ⟨w', hNW j hw'⟩ hw' x _ hxw' hw'x]
  have hcompat : TopCat.Presheaf.IsCompatible G.presheaf V sf := by
    intro i j
    apply TopCat.Presheaf.section_ext G
    intro x hx
    simp only [sf, TopCat.Presheaf.germ_res_apply]
    exact hpair i j x hx.1 hx.2
  have hcover : B ≤ iSup V := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := himage y hy
    exact Opens.mem_iSup.2 ⟨⟨z, hz⟩, z, hzN ⟨z, hz⟩, rfl⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' G V B (fun z => homOfLE (hVB z)) hcover
    sf hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Presheaf.section_ext ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G)
  intro z hz
  have e1 : ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ W z hz
      ((pullbackUnitRes k f G hWB).hom s) =
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.germ ((Opens.map f).obj B) z
        (hWB hz) (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app
          G).hom.app (op B) s) :=
    TopCat.Presheaf.germ_res_apply _ (homOfLE hWB) z hz _
  rw [e1]
  refine (stalkPullbackSheafIso_unit k f G B z (hWB hz) s).symm.trans ?_
  refine Eq.trans ?_ ((stalkPullbackSheafIso_unit k f G (O ⟨z, hz⟩) z (hO _) (σ _)).trans
    (hloc ⟨z, hz⟩ z (hzN _)))
  congr 1
  have hzV : f z ∈ V ⟨z, hz⟩ := ⟨z, hzN _, rfl⟩
  rw [← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (hVB ⟨z, hz⟩)) (f z) hzV, hs, hgerm]


/-- **Sections of an inverse image along a map with preconnected fibres.** If `f` maps `W` onto
`B`, maps open subsets of `W` to open sets and has preconnected fibres `W ∩ f⁻¹ {y}` over `B`,
the unit followed by restriction, `G(B) ⟶ (f⁻¹ G)(W)`, is bijective. -/
theorem bijective_pullbackUnitRes {W : Opens X} {B : Opens Y} (hWB : W ≤ (Opens.map f).obj B)
    (himage : ∀ y ∈ B, ∃ x ∈ W, f x = y)
    (hopen : ∀ O : Opens X, O ≤ W → IsOpen (f '' (O : Set X)))
    (hconn : ∀ y ∈ B, _root_.IsPreconnected ((W : Set X) ∩ f ⁻¹' {y})) :
    Function.Bijective (pullbackUnitRes k f G hWB).hom :=
  ⟨injective_pullbackUnitRes k f G hWB himage,
    surjective_pullbackUnitRes k f G hWB himage hopen hconn⟩

/-- `pullbackUnitRes` is an isomorphism under the hypotheses of `bijective_pullbackUnitRes`. -/
theorem isIso_pullbackUnitRes {W : Opens X} {B : Opens Y} (hWB : W ≤ (Opens.map f).obj B)
    (himage : ∀ y ∈ B, ∃ x ∈ W, f x = y)
    (hopen : ∀ O : Opens X, O ≤ W → IsOpen (f '' (O : Set X)))
    (hconn : ∀ y ∈ B, _root_.IsPreconnected ((W : Set X) ∩ f ⁻¹' {y})) :
    IsIso (pullbackUnitRes k f G hWB) :=
  (LinearEquiv.ofBijective _
    (bijective_pullbackUnitRes k f G hWB himage hopen hconn)).toModuleIso.isIso_hom

/-- `pullbackUnitRes` is natural in the sheaf. -/
@[reassoc]
theorem pullbackUnitRes_naturality {G G' : Y.Sheaf (ModuleCat.{0} k)} (φ : G ⟶ G')
    {W : Opens X} {B : Opens Y} (hWB : W ≤ (Opens.map f).obj B) :
    φ.hom.app (op B) ≫ pullbackUnitRes k f G' hWB =
      pullbackUnitRes k f G hWB ≫
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).map φ).hom.app (op W) := by
  have h : φ.hom.app (op B) ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app G').hom.app
        (op B) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app G).hom.app
          (op B) ≫
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).map φ).hom.app
          (op ((Opens.map f).obj B)) :=
    congrArg (fun ψ => ψ.hom.app (op B))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.naturality φ)
  refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _).symm
  refine (congrArg (· ≫ _) h).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_))
  exact (((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).map φ).hom.naturality
    (homOfLE hWB).op).symm

/-- `pullbackUnitRes` is compatible with restriction: for `W' ⊆ W` and `B' ⊆ B` with
`W' ⊆ f⁻¹ B'`, restricting from `W` to `W'` after the map over `(W, B)` is the map over
`(W', B')` after restricting from `B` to `B'`. -/
@[reassoc]
theorem pullbackUnitRes_map {W W' : Opens X} {B B' : Opens Y} (hWB : W ≤ (Opens.map f).obj B)
    (hW'B' : W' ≤ (Opens.map f).obj B') (hW : W' ≤ W) (hB : B' ≤ B) :
    pullbackUnitRes k f G hWB ≫
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.map (homOfLE hW).op =
      G.presheaf.map (homOfLE hB).op ≫ pullbackUnitRes k f G hW'B' := by
  have hB' : (Opens.map f).obj B' ≤ (Opens.map f).obj B := (Opens.map f).monotone hB
  have h : G.presheaf.map (homOfLE hB).op ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app G).hom.app
        (op B') =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app G).hom.app
          (op B) ≫
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj G).presheaf.map (homOfLE hB').op :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app
      G).hom.naturality (homOfLE hB).op
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) h).symm
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans
    ((congrArg _ (Subsingleton.elim _ _)).trans (Functor.map_comp _ _ _)))

end unitRes

end TDA.Sheaf
