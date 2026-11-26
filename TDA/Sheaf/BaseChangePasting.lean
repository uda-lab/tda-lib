import TDA.Sheaf.BaseChange

/-!
# The underived base change and pasting of base-change squares

Let `k` be a ring and write `Sh(X) := X.Sheaf (ModuleCat k)`. For a commutative square
`w : g' ≫ f = f' ≫ g` of continuous maps

```
      g'
  X' ---> X
  |       |
f'|       | f
  v       v
  Y' ---> Y
      g
```

`TDA.Sheaf.BaseChange` constructs the derived base-change morphism
`baseChange k w : Rf_* ⋙ g⁻¹ ⟶ g'⁻¹ ⋙ Rf'_*` on `D⁺`. This file relates it to sheaves and
composes it.

* `pullbackSquareSheaf k w : g⁻¹ ⋙ f'⁻¹ ⟶ f⁻¹ ⋙ g'⁻¹` is the isomorphism of sheaf inverse images
  (through `pullbackCompIso` and `w`), and the **underived base change**
  `baseChangeSheaf k w : f_* ⋙ g⁻¹ ⟶ g'⁻¹ ⋙ f'_*` is its mate for the sheaf adjunctions of `f` and
  `f'` (`baseChangeSheaf_app`). Its adjoint for `g⁻¹ ⊣ g_*` is `f_*` of the unit of `g'`
  (`unit_baseChangeSheaf`).
* `pullbackSquareCochain k w` and `baseChangeCochain k w` are the termwise versions on bounded
  below complexes (the mate for `pullbackPushforwardAdjunctionPlus`), degreewise equal to
  `pullbackSquareSheaf` and `baseChangeSheaf` (`pullbackSquareCochain_app_hom_f`,
  `baseChangeCochain_app_hom_f`).
* `pullbackPlusSquare_fac_app`: on `Q M`, the derived square `pullbackPlusSquare k w` is `Q` of
  `pullbackSquareCochain k w`, up to the derived-functor comparisons of the inverse images.
* `baseChange_app_Q`: **on `Q K`, the derived base change is the termwise underived base
  change**, for every bounded below complex `K`: after `g⁻¹` of the comparison `f_* K ⟶ Rf_* K`,
  `baseChange` is the inverse comparison of `g⁻¹`, then `Q` of `baseChangeCochain k w`, then the
  comparisons of `f'_*` and `g'⁻¹`.
* `baseChange_comp_app`: **pasting.** For a second square `w₂ : h' ≫ f' = f'' ≫ h` stacked on
  `w` along the inverse images, the base change of the composite square
  `(h' ≫ g') ≫ f = f'' ≫ h ≫ g` is `h⁻¹` of the base change of `w` followed by the base change of
  `w₂`, up to `pullbackPlusCompIso`.

Derived categories are instance arguments, one for each space a statement mentions.
-/

noncomputable section
open CategoryTheory Limits

namespace TDA.Sheaf

section mate

variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* E] [Category* F]

/-- The components of a mate (`mateEquiv`): the unit of the second adjunction, the 2-cell and the
counit of the first adjunction. -/
private lemma mateEquiv_app {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D}
    {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (b : B) :
    (mateEquiv adj₁ adj₂ α).app b =
      adj₂.unit.app (G.obj (R₁.obj b)) ≫ R₂.map (α.app (R₁.obj b)) ≫
        R₂.map (H.map (adj₁.counit.app b)) := by
  simp [mateEquiv_apply]

/-- **Pasting of mates.** If the 2-cell `γ : G ⋙ L₃ ⟶ L₁ ⋙ H` is the pasting of
`α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁` and `β : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂` up to isomorphisms `u : G ≅ G₁ ⋙ G₂` and
`v : H₁ ⋙ H₂ ≅ H`, then its mate is the pasting of the mates of `α` and `β`. -/
private lemma mateEquiv_paste {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F} {G : A ⥤ E}
    {H : B ⥤ F} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁)
    (β : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) (γ : G ⋙ L₃ ⟶ L₁ ⋙ H) (u : G ≅ G₁ ⋙ G₂) (v : H₁ ⋙ H₂ ≅ H)
    (hγ : ∀ a, γ.app a = L₃.map (u.hom.app a) ≫ β.app (G₁.obj a) ≫ H₂.map (α.app a) ≫
      v.hom.app (L₁.obj a)) (b : B) :
    (mateEquiv adj₁ adj₃ γ).app b =
      u.hom.app (R₁.obj b) ≫ G₂.map ((mateEquiv adj₁ adj₂ α).app b) ≫
        (mateEquiv adj₂ adj₃ β).app (H₁.obj b) ≫ R₃.map (v.hom.app b) := by
  rw [mateEquiv_app, mateEquiv_app, mateEquiv_app, hγ]
  simp only [Functor.map_comp, Category.assoc]
  have e0 := adj₃.unit.naturality (u.hom.app (R₁.obj b))
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at e0
  rw [← reassoc_of% e0]
  congr 1
  let x := adj₂.unit.app (G₁.obj (R₁.obj b)) ≫ R₂.map (α.app (R₁.obj b)) ≫
        R₂.map (H₁.map (adj₁.counit.app b))
  have e1 := adj₃.unit.naturality (G₂.map x)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at e1
  have e2 := β.naturality x
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at e2
  have hx : L₂.map x ≫ adj₂.counit.app (H₁.obj b) = α.app _ ≫ H₁.map (adj₁.counit.app b) := by
    simp [x]
  have e3 := v.hom.naturality (adj₁.counit.app b)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at e3
  calc _ = adj₃.unit.app _ ≫ R₃.map (β.app _ ≫ H₂.map (L₂.map x ≫ adj₂.counit.app (H₁.obj b)) ≫
        v.hom.app b) := by
          rw [hx]; simp only [Functor.map_comp, Category.assoc, e3, Functor.id_obj]
    _ = adj₃.unit.app _ ≫ R₃.map (L₃.map (G₂.map x) ≫ β.app _ ≫ H₂.map (adj₂.counit.app (H₁.obj b)) ≫
        v.hom.app b) := by
          dsimp only [Functor.id_obj]; rw [reassoc_of% e2]; simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
          dsimp only [Functor.id_obj]; rw [Functor.map_comp, ← reassoc_of% e1]; simp only [x, Functor.map_comp, Category.assoc, Functor.id_obj]

/-- **Mates against comparisons, abstractly.** Let `ac : fp ⊣ fs`, `ac' : f'p ⊣ f's` be
adjunctions and `ad : Lf ⊣ Rf`, `ad' : Lf' ⊣ Rf'` adjunctions between localizations `Q`, compatible
through comparisons `β` (of the right adjoints) and `γ` (of the left adjoints and of `gp`, `g'p`):
the units by `hU`, the counits by `hC`, and the 2-cells `sc`, `sd` by `hS`. Then the mate of `sd`
on `Q K`, after `Lg` of `β`, is the inverse comparison of `gp`, then `Q` of the mate of `sc`, then
the comparisons of `f's` and `g'p`. -/
private lemma mateEquiv_app_Q {AX AY AX' AY' DX DY DX' DY' : Type*} [Category* AX]
    [Category* AY] [Category* AX'] [Category* AY'] [Category* DX] [Category* DY] [Category* DX']
    [Category* DY'] (QX : AX ⥤ DX) (QY : AY ⥤ DY) (QX' : AX' ⥤ DX') (QY' : AY' ⥤ DY')
    {fs : AX ⥤ AY} {fp : AY ⥤ AX} {gp : AY ⥤ AY'} {f's : AX' ⥤ AY'} {f'p : AY' ⥤ AX'}
    {g'p : AX ⥤ AX'} {Rf : DX ⥤ DY} {Lf : DY ⥤ DX} {Lg : DY ⥤ DY'} {Rf' : DX' ⥤ DY'}
    {Lf' : DY' ⥤ DX'} {Lg' : DX ⥤ DX'} (ac : fp ⊣ fs) (ac' : f'p ⊣ f's) (ad : Lf ⊣ Rf)
    (ad' : Lf' ⊣ Rf') (βf : fs ⋙ QY ⟶ QX ⋙ Rf) (βf' : f's ⋙ QY' ⟶ QX' ⋙ Rf')
    (γf : fp ⋙ QX ⟶ QY ⋙ Lf) (γg : gp ⋙ QY' ⟶ QY ⋙ Lg) (γf' : f'p ⋙ QX' ⟶ QY' ⋙ Lf')
    (γg' : g'p ⋙ QX' ⟶ QX ⋙ Lg') [IsIso γf] [IsIso γg] (sc : gp ⋙ f'p ⟶ fp ⋙ g'p)
    (sd : Lg ⋙ Lf' ⟶ Lf ⋙ Lg')
    (hU : ∀ L, ad'.unit.app (QY'.obj L) =
      QY'.map (ac'.unit.app L) ≫ βf'.app (f'p.obj L) ≫ Rf'.map (γf'.app L))
    (hC : ∀ K, Lf.map (βf.app K) ≫ ad.counit.app (QX.obj K) =
      inv (γf.app (fs.obj K)) ≫ QX.map (ac.counit.app K))
    (hS : ∀ M, γf'.app (gp.obj M) ≫ Lf'.map (γg.app M) ≫ sd.app (QY.obj M) =
      QX'.map (sc.app M) ≫ γg'.app (fp.obj M) ≫ Lg'.map (γf.app M)) (K : AX) :
    Lg.map (βf.app K) ≫ (mateEquiv ad ad' sd).app (QX.obj K) =
      inv (γg.app (fs.obj K)) ≫ QY'.map ((mateEquiv ac ac' sc).app K) ≫
        βf'.app (g'p.obj K) ≫ Rf'.map (γg'.app K) := by
  rw [← cancel_epi (γg.app (fs.obj K)), IsIso.hom_inv_id_assoc, mateEquiv_app, mateEquiv_app]
  have n₁ := ad'.unit.naturality (γg.app (fs.obj K) ≫ Lg.map (βf.app K))
  have n₂ := sd.naturality (βf.app K)
  have n₃ := γg'.naturality (ac.counit.app K)
  have n₄ := βf'.naturality (sc.app (fs.obj K) ≫ g'p.map (ac.counit.app K))
  have hc : Lg'.map (γf.app (fs.obj K)) ≫ Lg'.map (Lf.map (βf.app K)) ≫
      Lg'.map (ad.counit.app (QX.obj K)) = Lg'.map (QX.map (ac.counit.app K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hC, IsIso.hom_inv_id_assoc]
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n₁ n₂ n₃ n₄
  rw [reassoc_of% n₁, hU, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Functor.map_comp Lf',
    Category.assoc, reassoc_of% n₂, reassoc_of% hS, hc, ← n₃]
  simp only [Functor.map_comp, Category.assoc] at n₄ ⊢
  rw [reassoc_of% n₄]

end mate

variable (k : Type) [Ring k]

section underived

variable {X Y X' Y' : TopCat.{0}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- For a commutative square `w : g' ≫ f = f' ≫ g`, the isomorphism of sheaf inverse images
`g⁻¹ ⋙ f'⁻¹ ≅ (f' ≫ g)⁻¹ = (g' ≫ f)⁻¹ ≅ f⁻¹ ⋙ g'⁻¹` (through `pullbackCompIso` and `w`). -/
def pullbackSquareSheaf (w : g' ≫ f = f' ≫ g) :
    TopCat.Sheaf.pullback (ModuleCat.{0} k) g ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} k) f' ⟶
      TopCat.Sheaf.pullback (ModuleCat.{0} k) f ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} k) g' :=
  (pullbackCompIso k f' g).hom ≫
    eqToHom (congrArg (TopCat.Sheaf.pullback (ModuleCat.{0} k)) w.symm) ≫
    (pullbackCompIso k g' f).inv

/-- `pullbackSquareSheaf` is invertible. -/
instance isIso_pullbackSquareSheaf (w : g' ≫ f = f' ≫ g) : IsIso (pullbackSquareSheaf k w) := by
  unfold pullbackSquareSheaf
  infer_instance

/-- **The underived base change** `f_* ⋙ g⁻¹ ⟶ g'⁻¹ ⋙ f'_*` of a commutative square
`w : g' ≫ f = f' ≫ g`, that is `g⁻¹ ∘ f_* ⟶ f'_* ∘ g'⁻¹` on sheaves of `k`-modules: the mate of
`pullbackSquareSheaf k w` for the sheaf adjunctions `f⁻¹ ⊣ f_*` and `f'⁻¹ ⊣ f'_*`. -/
def baseChangeSheaf (w : g' ≫ f = f' ≫ g) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} k) f ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} k) g ⟶
      TopCat.Sheaf.pullback (ModuleCat.{0} k) g' ⋙ TopCat.Sheaf.pushforward (ModuleCat.{0} k) f' :=
  mateEquiv (TopCat.Sheaf.pullbackPushforwardAdjunction _ f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ f') (pullbackSquareSheaf k w)

/-- The components of `baseChangeSheaf`: the unit of `f'`, then `pullbackSquareSheaf`, then the
counit of `f`. -/
lemma baseChangeSheaf_app (w : g' ≫ f = f' ≫ g) (G : X.Sheaf (ModuleCat.{0} k)) :
    (baseChangeSheaf k w).app G =
      (TopCat.Sheaf.pullbackPushforwardAdjunction _ f').unit.app
          ((TopCat.Sheaf.pullback _ g).obj ((TopCat.Sheaf.pushforward _ f).obj G)) ≫
        (TopCat.Sheaf.pushforward _ f').map
          ((pullbackSquareSheaf k w).app ((TopCat.Sheaf.pushforward _ f).obj G)) ≫
        (TopCat.Sheaf.pushforward _ f').map ((TopCat.Sheaf.pullback _ g').map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction _ f).counit.app G)) :=
  mateEquiv_app _ _ _ G

/-- The unit of `a` followed by `a_*` of the identification `a⁻¹ = b⁻¹` and of `ψ`, for `a = b`,
is the unit of `b` followed by `b_*` of `ψ`, up to the identification `b_* = a_*`. -/
private lemma unit_eqToHom {a b : X' ⟶ Y} (e : a = b)
    (h : TopCat.Sheaf.pullback (ModuleCat.{0} k) a = TopCat.Sheaf.pullback (ModuleCat.{0} k) b)
    (F : Y.Sheaf (ModuleCat.{0} k)) {Z : X'.Sheaf (ModuleCat.{0} k)}
    (ψ : (TopCat.Sheaf.pullback (ModuleCat.{0} k) b).obj F ⟶ Z) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ a).unit.app F ≫
        (TopCat.Sheaf.pushforward _ a).map ((eqToHom h).app F) ≫
        (TopCat.Sheaf.pushforward _ a).map ψ =
      (TopCat.Sheaf.pullbackPushforwardAdjunction _ b).unit.app F ≫
        (TopCat.Sheaf.pushforward _ b).map ψ ≫ eqToHom (by subst e; rfl) := by
  subst e
  simp

/-- **The adjoint of the underived base change.** For `g⁻¹ ⊣ g_*`, the adjoint of
`baseChangeSheaf k w` at `G` is `f_*` of the unit `G ⟶ g'_* g'⁻¹ G`, read in
`g_* f'_* g'⁻¹ G = (f' ≫ g)_* g'⁻¹ G = (g' ≫ f)_* g'⁻¹ G`. -/
theorem unit_baseChangeSheaf (w : g' ≫ f = f' ≫ g) (G : X.Sheaf (ModuleCat.{0} k)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ g).unit.app
        ((TopCat.Sheaf.pushforward _ f).obj G) ≫
      (TopCat.Sheaf.pushforward _ g).map ((baseChangeSheaf k w).app G) =
    (TopCat.Sheaf.pushforward _ f).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction _ g').unit.app G) ≫
      eqToHom (by
        change (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (g' ≫ f)).obj _ =
          (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (f' ≫ g)).obj _
        rw [w]) := by
  let F := (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).obj G
  have e₁ : (TopCat.Sheaf.pullbackPushforwardAdjunction _ g).unit.app F ≫
      (TopCat.Sheaf.pushforward _ g).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction _ f').unit.app
          ((TopCat.Sheaf.pullback _ g).obj F)) ≫
      (TopCat.Sheaf.pushforward _ g).map ((TopCat.Sheaf.pushforward _ f').map
        ((pullbackCompIso k f' g).hom.app F)) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (f' ≫ g)).unit.app F :=
    unit_pullbackCompIso_hom_app k f' g F
  have e₂ : (TopCat.Sheaf.pullbackPushforwardAdjunction _ (g' ≫ f)).unit.app F =
      (TopCat.Sheaf.pullbackPushforwardAdjunction _ f).unit.app F ≫
        (TopCat.Sheaf.pushforward _ f).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction _ g').unit.app
            ((TopCat.Sheaf.pullback _ f).obj F)) ≫
        (TopCat.Sheaf.pushforward _ f).map ((TopCat.Sheaf.pushforward _ g').map
          ((pullbackCompIso k g' f).hom.app F)) :=
    (unit_pullbackCompIso_hom_app k g' f F).symm
  have e₃ := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) g').unit.naturality
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).counit.app G)
  have e₄ := unit_eqToHom k w.symm (by rw [w]) F
    ((pullbackCompIso k g' f).inv.app F ≫ (TopCat.Sheaf.pullback _ g').map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction _ f).counit.app G))
  rw [baseChangeSheaf_app, pullbackSquareSheaf, NatTrans.comp_app, NatTrans.comp_app]
  simp only [Functor.map_comp, Category.assoc]
  have e₅ : (TopCat.Sheaf.pullbackPushforwardAdjunction _ (g' ≫ f)).unit.app F ≫
      (TopCat.Sheaf.pushforward _ (g' ≫ f)).map ((pullbackCompIso k g' f).inv.app F ≫
        (TopCat.Sheaf.pullback _ g').map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction _ f).counit.app G)) =
      (TopCat.Sheaf.pushforward _ f).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction _ g').unit.app G) := by
    change _ ≫ (TopCat.Sheaf.pushforward _ f).map ((TopCat.Sheaf.pushforward _ g').map
      ((pullbackCompIso k g' f).inv.app F ≫ (TopCat.Sheaf.pullback _ g').map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction _ f).counit.app G))) = _
    rw [e₂]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
    simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at e₃
    rw [← e₃, Functor.map_comp, Adjunction.right_triangle_components_assoc]
  simp only [Functor.map_comp] at e₄
  rw [reassoc_of% e₁]
  refine e₄.trans ?_
  rw [← e₅]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end underived

section cochain

variable {X Y X' Y' : TopCat.{0}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- `pullbackSquareSheaf` applied termwise to bounded below cochain complexes:
`g⁻¹ ⋙ f'⁻¹ ⟶ f⁻¹ ⋙ g'⁻¹` through `mapCochainComplexPlusCompIso` of `pullbackCompIso` and `w`. -/
def pullbackSquareCochain (w : g' ≫ f = f' ≫ g) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) g).mapCochainComplexPlus ⋙
        (TopCat.Sheaf.pullback (ModuleCat.{0} k) f').mapCochainComplexPlus ⟶
      (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).mapCochainComplexPlus ⋙
        (TopCat.Sheaf.pullback (ModuleCat.{0} k) g').mapCochainComplexPlus :=
  (mapCochainComplexPlusCompIso (pullbackCompIso k f' g)).hom ≫
    NatTrans.mapCochainComplexPlus
      (eqToHom (congrArg (TopCat.Sheaf.pullback (ModuleCat.{0} k)) w.symm)) ≫
    (mapCochainComplexPlusCompIso (pullbackCompIso k g' f)).inv

/-- In degree `n`, `pullbackSquareCochain` is `pullbackSquareSheaf` at the `n`-th term. -/
@[simp]
lemma pullbackSquareCochain_app_hom_f (w : g' ≫ f = f' ≫ g)
    (M : CochainComplex.Plus (Y.Sheaf (ModuleCat.{0} k))) (n : ℤ) :
    ((pullbackSquareCochain k w).app M).hom.f n = (pullbackSquareSheaf k w).app (M.obj.X n) := by
  simp [pullbackSquareCochain, pullbackSquareSheaf]

/-- **The underived base change, termwise**: the mate of `pullbackSquareCochain k w` for the
termwise adjunctions `pullbackPushforwardAdjunctionPlus` of `f` and `f'`. In degree `n` it is
`baseChangeSheaf k w` at the `n`-th term (`baseChangeCochain_app_hom_f`). -/
def baseChangeCochain (w : g' ≫ f = f' ≫ g) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).mapCochainComplexPlus ⋙
        (TopCat.Sheaf.pullback (ModuleCat.{0} k) g).mapCochainComplexPlus ⟶
      (TopCat.Sheaf.pullback (ModuleCat.{0} k) g').mapCochainComplexPlus ⋙
        (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f').mapCochainComplexPlus :=
  mateEquiv (pullbackPushforwardAdjunctionPlus k f) (pullbackPushforwardAdjunctionPlus k f')
    (pullbackSquareCochain k w)

/-- The components of `baseChangeCochain`: the termwise unit of `f'`, then
`pullbackSquareCochain`, then the termwise counit of `f`. -/
lemma baseChangeCochain_app (w : g' ≫ f = f' ≫ g)
    (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{0} k))) :
    (baseChangeCochain k w).app K =
      (unitCochain k f').app ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g).mapCochainComplexPlus.obj
          ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).mapCochainComplexPlus.obj K)) ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f').mapCochainComplexPlus.map
          ((pullbackSquareCochain k w).app
            ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).mapCochainComplexPlus.obj K)) ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f').mapCochainComplexPlus.map
          ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g').mapCochainComplexPlus.map
            ((pullbackPushforwardAdjunctionPlus k f).counit.app K)) :=
  mateEquiv_app _ _ _ K

/-- In degree `n`, `baseChangeCochain` is `baseChangeSheaf` at the `n`-th term. -/
@[simp]
lemma baseChangeCochain_app_hom_f (w : g' ≫ f = f' ≫ g)
    (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{0} k))) (n : ℤ) :
    ((baseChangeCochain k w).app K).hom.f n = (baseChangeSheaf k w).app (K.obj.X n) := by
  rw [baseChangeCochain_app, baseChangeSheaf_app]
  simp only [ObjectProperty.FullSubcategory.comp_hom, HomologicalComplex.comp_f,
    unitCochain_app_hom_f, Functor.mapCochainComplexPlus_map_hom,
    Functor.mapHomologicalComplex_map_f, pullbackSquareCochain_app_hom_f,
    pullbackPushforwardAdjunctionPlus_counit_app_hom_f]
  rfl

end cochain

section derived

variable {X Y X' Y' : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- `pullbackPlusSquare` with the identification along `w` written through `congrArg`. Proofs
below use this form: kernel checks against the `rw`-built proof term of the definition are slow. -/
private lemma pullbackPlusSquare_eq (w : g' ≫ f = f' ≫ g) :
    pullbackPlusSquare k w = (pullbackPlusCompIso k f' g).hom ≫
      eqToHom (congrArg (pullbackPlus k) w.symm) ≫ (pullbackPlusCompIso k g' f).inv :=
  rfl

/-- The derived square on `Q M`, for a second inverse-image comparison `A` compatible with a
termwise `A₀`; the identification along `f' ≫ g = ψ` is eliminated by `subst`. -/
private lemma pullbackPlusSquare_fac_app_aux {ψ : X' ⟶ Y} (e : f' ≫ g = ψ)
    (p : pullbackPlus k (f' ≫ g) = pullbackPlus k ψ)
    (p₀ : TopCat.Sheaf.pullback (ModuleCat.{0} k) (f' ≫ g) =
      TopCat.Sheaf.pullback (ModuleCat.{0} k) ψ)
    (A : pullbackPlus k ψ ⟶ pullbackPlus k f ⋙ pullbackPlus k g')
    (A₀ : (TopCat.Sheaf.pullback (ModuleCat.{0} k) ψ).mapCochainComplexPlus ⟶
      (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).mapCochainComplexPlus ⋙
        (TopCat.Sheaf.pullback (ModuleCat.{0} k) g').mapCochainComplexPlus)
    (M : CochainComplex.Plus (Y.Sheaf (ModuleCat.{0} k)))
    (Γ : DerivedCategory.Plus.Q.obj ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g').mapCochainComplexPlus.obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).mapCochainComplexPlus.obj M)) ⟶
      (pullbackPlus k f ⋙ pullbackPlus k g').obj (DerivedCategory.Plus.Q.obj M))
    (hA : (TopCat.Sheaf.pullback (ModuleCat.{0} k) ψ).rightDerivedFunctorPlusUnit.app M ≫
        A.app (DerivedCategory.Plus.Q.obj M) =
      DerivedCategory.Plus.Q.map (A₀.app M) ≫ Γ) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) f').rightDerivedFunctorPlusUnit.app
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g).mapCochainComplexPlus.obj M) ≫
      (pullbackPlus k f').map
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g).rightDerivedFunctorPlusUnit.app M) ≫
      ((pullbackPlusCompIso k f' g).hom ≫ eqToHom p ≫ A).app (DerivedCategory.Plus.Q.obj M) =
    DerivedCategory.Plus.Q.map (((mapCochainComplexPlusCompIso (pullbackCompIso k f' g)).hom ≫
      NatTrans.mapCochainComplexPlus (eqToHom p₀) ≫ A₀).app M) ≫ Γ := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, NatTrans.comp_app,
    pullbackPlusCompIso_hom_fac_app_assoc, hA, NatTrans.mapCochainComplexPlus_id, Functor.map_comp,
    Category.assoc]

/-- **The derived square on `Q M`.** After the derived-functor comparisons of `f'⁻¹` and `g⁻¹`,
`pullbackPlusSquare k w` at `Q M` is `Q` of the termwise square `pullbackSquareCochain k w`,
followed by the comparisons of `g'⁻¹` and `f⁻¹`. -/
@[reassoc]
lemma pullbackPlusSquare_fac_app (w : g' ≫ f = f' ≫ g)
    (M : CochainComplex.Plus (Y.Sheaf (ModuleCat.{0} k))) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) f').rightDerivedFunctorPlusUnit.app
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g).mapCochainComplexPlus.obj M) ≫
      (pullbackPlus k f').map
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g).rightDerivedFunctorPlusUnit.app M) ≫
      (pullbackPlusSquare k w).app (DerivedCategory.Plus.Q.obj M) =
    DerivedCategory.Plus.Q.map ((pullbackSquareCochain k w).app M) ≫
      (TopCat.Sheaf.pullback (ModuleCat.{0} k) g').rightDerivedFunctorPlusUnit.app
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).mapCochainComplexPlus.obj M) ≫
      (pullbackPlus k g').map
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit.app M) := by
  rw [pullbackPlusSquare_eq, pullbackSquareCochain, pullbackPlusCompIso_inv]
  exact pullbackPlusSquare_fac_app_aux k w.symm _ _ _ _ M _
    (pullbackPlusCompHom_fac_app k g' f M)

/-- **On `Q K`, the derived base change is the termwise underived base change.** For every
bounded below complex `K` of sheaves on `X`, `g⁻¹` of the comparison `f_* K ⟶ Rf_* K` followed by
`baseChange k w` is the inverse comparison of `g⁻¹`, then `Q` of the termwise underived base change
`baseChangeCochain k w`, then the comparisons of `f'_*` and `g'⁻¹`. -/
theorem baseChange_app_Q (w : g' ≫ f = f' ≫ g)
    (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k g).map
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit.app K) ≫
      (baseChange k w).app (DerivedCategory.Plus.Q.obj K) =
    inv ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g).rightDerivedFunctorPlusUnit.app
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Plus.Q.map ((baseChangeCochain k w).app K) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f').rightDerivedFunctorPlusUnit.app
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g').mapCochainComplexPlus.obj K) ≫
      (pushforwardPlus k f').map
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) g').rightDerivedFunctorPlusUnit.app K) := by
  rw [baseChange_eq, baseChangeCochain]
  exact mateEquiv_app_Q (Rf := pushforwardPlus k f) (Lf := pullbackPlus k f)
    (Lg := pullbackPlus k g) (Rf' := pushforwardPlus k f') (Lf' := pullbackPlus k f')
    (Lg' := pullbackPlus k g') DerivedCategory.Plus.Q DerivedCategory.Plus.Q DerivedCategory.Plus.Q
    DerivedCategory.Plus.Q (pullbackPushforwardAdjunctionPlus k f)
    (pullbackPushforwardAdjunctionPlus k f') (derivedAdjunction k f) (derivedAdjunction k f')
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f').rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) g).rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) f').rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) g').rightDerivedFunctorPlusUnit
    (pullbackSquareCochain k w) (pullbackPlusSquare k w)
    (fun L => by rw [derivedAdjunction_unit, pullbackPushforwardAdjunctionPlus_unit];
                 exact derivedUnit_app_Q k f' L)
    (fun K => by rw [derivedAdjunction_counit]; exact derivedCounit_fac_app k f K)
    (fun M => pullbackPlusSquare_fac_app k w M) K

end derived

section paste

variable {X Y X' Y' X'' Y'' V Z W : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X''.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y''.Sheaf (ModuleCat.{0} k))]

omit [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X''.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y''.Sheaf (ModuleCat.{0} k))] in
/-- `pullbackPlusCompIso k i p` against the identification along `p = p'`. -/
private lemma pullbackPlusCompIso_hom_eqToHom_right
    [HasDerivedCategory (V.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Z.Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory (W.Sheaf (ModuleCat.{0} k))] (i : V ⟶ Z) {p p' : Z ⟶ W} (e : p = p')
    (N : DerivedCategory.Plus (W.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlusCompIso k i p).hom.app N ≫
        (eqToHom (congrArg (pullbackPlus k) (congrArg (i ≫ ·) e))).app N =
      (pullbackPlus k i).map ((eqToHom (congrArg (pullbackPlus k) e)).app N) ≫
        (pullbackPlusCompIso k i p').hom.app N := by
  subst e
  simp

omit [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X''.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y''.Sheaf (ModuleCat.{0} k))] in
/-- `pullbackPlusCompIso k p j` against the identification along `p = p'`. -/
private lemma pullbackPlusCompIso_hom_eqToHom_left
    [HasDerivedCategory (V.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Z.Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory (W.Sheaf (ModuleCat.{0} k))] {p p' : V ⟶ Z} (e : p = p') (j : Z ⟶ W)
    (N : DerivedCategory.Plus (W.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlusCompIso k p j).hom.app N ≫
        (eqToHom (congrArg (pullbackPlus k) (congrArg (· ≫ j) e))).app N =
      (eqToHom (congrArg (pullbackPlus k) e)).app ((pullbackPlus k j).obj N) ≫
        (pullbackPlusCompIso k p' j).hom.app N := by
  subst e
  simp

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

/-- The pasted derived square: `pullbackPlusSquare` of the composite square is the square of
`w₂` followed by `h'⁻¹` of the square of `w₁`, up to `pullbackPlusCompIso`. -/
private lemma pullbackPlusSquare_comp_app (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (w : (h' ≫ g') ≫ f = f'' ≫ h ≫ g) (N : DerivedCategory.Plus (Y.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlusSquare k w).app N =
      (pullbackPlus k f'').map ((pullbackPlusCompIso k h g).inv.app N) ≫
        (pullbackPlusSquare k w₂).app ((pullbackPlus k g).obj N) ≫
        (pullbackPlus k h').map ((pullbackPlusSquare k w₁).app N) ≫
        (pullbackPlusCompIso k h' g').hom.app ((pullbackPlus k f).obj N) := by
  rw [pullbackPlusSquare_eq, pullbackPlusSquare_eq, pullbackPlusSquare_eq]
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have hα := pullbackPlusCompIso_hom_assoc_app k f'' h g N
  have hγ := pullbackPlusCompIso_hom_assoc_app k h' f' g N
  have hε := pullbackPlusCompIso_hom_assoc_app k h' g' f N
  have hβ := pullbackPlusCompIso_hom_eqToHom_left k w₂.symm g N
  have hδ := pullbackPlusCompIso_hom_eqToHom_right k h' w₁.symm N
  have hE : (eqToHom (congrArg (pullbackPlus k) w.symm)).app N =
      (eqToHom (congrArg (pullbackPlus k) (congrArg (· ≫ g) w₂.symm))).app N ≫
        (eqToHom (congrArg (pullbackPlus k) (congrArg (h' ≫ ·) w₁.symm))).app N := by
    -- `simp` rather than `rw [eqToHom_trans]`: the latter's kernel check unfolds the inverse
    -- images along the reassociated composites and is slow.
    simp only [eqToHom_app, eqToHom_trans]
  have hα' : (pullbackPlusCompIso k f'' (h ≫ g)).hom.app N =
      (pullbackPlus k f'').map ((pullbackPlusCompIso k h g).inv.app N) ≫ (pullbackPlusCompIso k f'' h).hom.app ((pullbackPlus k g).obj N) ≫
        (pullbackPlusCompIso k (f'' ≫ h) g).hom.app N := by
    rw [← hα, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hγ' : (pullbackPlusCompIso k (h' ≫ f') g).hom.app N =
      (pullbackPlusCompIso k h' f').inv.app ((pullbackPlus k g).obj N) ≫ (pullbackPlus k h').map ((pullbackPlusCompIso k f' g).hom.app N) ≫
        (pullbackPlusCompIso k h' (f' ≫ g)).hom.app N := by
    rw [hγ, Iso.inv_hom_id_app_assoc]
  have hε'' : (pullbackPlusCompIso k h' (g' ≫ f)).hom.app N =
      (pullbackPlus k h').map ((pullbackPlusCompIso k g' f).inv.app N) ≫
        (pullbackPlusCompIso k h' g').hom.app ((pullbackPlus k f).obj N) ≫
        (pullbackPlusCompIso k (h' ≫ g') f).hom.app N := by
    refine Eq.trans ?_ (congrArg
      (fun x => (pullbackPlus k h').map ((pullbackPlusCompIso k g' f).inv.app N) ≫ x) hε)
    simp
  have hε' : (pullbackPlusCompIso k h' (g' ≫ f)).hom.app N ≫
      (pullbackPlusCompIso k (h' ≫ g') f).inv.app N =
      (pullbackPlus k h').map ((pullbackPlusCompIso k g' f).inv.app N) ≫
        (pullbackPlusCompIso k h' g').hom.app ((pullbackPlus k f).obj N) := by
    simp only [hε'', Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  simp only [hE, hα', Category.assoc, reassoc_of% hβ, hγ', reassoc_of% hδ, hε']

/-- **Pasting of base-change squares** (stacked along the inverse images). For commutative squares
`w₁ : g' ≫ f = f' ≫ g` and `w₂ : h' ≫ f' = f'' ≫ h`, the base change of the composite square
`w : (h' ≫ g') ≫ f = f'' ≫ h ≫ g` at `M` is `h⁻¹` of the base change of `w₁`, followed by the base
change of `w₂` at `g'⁻¹ M`, conjugated by `pullbackPlusCompIso`. -/
theorem baseChange_comp_app (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (w : (h' ≫ g') ≫ f = f'' ≫ h ≫ g) (M : DerivedCategory.Plus (X.Sheaf (ModuleCat.{0} k))) :
    (baseChange k w).app M =
      (pullbackPlusCompIso k h g).inv.app ((pushforwardPlus k f).obj M) ≫
        (pullbackPlus k h).map ((baseChange k w₁).app M) ≫
        (baseChange k w₂).app ((pullbackPlus k g').obj M) ≫
        (pushforwardPlus k f'').map ((pullbackPlusCompIso k h' g').hom.app M) := by
  rw [baseChange_eq, baseChange_eq, baseChange_eq]
  exact mateEquiv_paste (G₁ := pullbackPlus k g) (G₂ := pullbackPlus k h)
    (H₁ := pullbackPlus k g') (H₂ := pullbackPlus k h') (G := pullbackPlus k (h ≫ g))
    (H := pullbackPlus k (h' ≫ g')) (derivedAdjunction k f) (derivedAdjunction k f')
    (derivedAdjunction k f'') (pullbackPlusSquare k w₁) (pullbackPlusSquare k w₂)
    (pullbackPlusSquare k w) (pullbackPlusCompIso k h g).symm (pullbackPlusCompIso k h' g')
    (fun N => pullbackPlusSquare_comp_app k w₁ w₂ w N) M

end paste

end TDA.Sheaf
