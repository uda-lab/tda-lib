import TDA.Sheaf.BaseChange

/-!
# Units, counits and restrictions of correspondences

Let `k` be a ring and write `Sh(X) := X.Sheaf (ModuleCat k)`. For continuous maps, `f⁻¹` is
`pullbackPlus k f`, `Rf_*` is `pushforwardPlus k f`, `η_f` and `ε_f` are the unit and counit of the
derived adjunction `f⁻¹ ⊣ Rf_*` (`derivedUnit`, `derivedCounit`), and `corrRestr k j p q` is the
restriction `p⁻¹ ⋙ Rq_* ⟶ (j ≫ p)⁻¹ ⋙ R(j ≫ q)_*` of `TDA.Sheaf.DerivedPlus`.

* **Composites.** `derivedCounit_comp_app`: the counit of `f ≫ g`, after
  `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`, is `(f ≫ g)⁻¹ ≅ f⁻¹ g⁻¹`, then `f⁻¹` of the counit of `g`, then the
  counit of `f`. `derivedUnit_comp_app_counit` and `derivedUnit_comp_app_pullbackPlusCompIso_inv`
  are the corresponding statements for the unit of a composite.
* **Restrictions.** `corrRestr_counit`: the adjoint of the restriction along `j` is the
  restriction `j⁻¹` of the counit of `q`. `corrRestr_app_comp_map`: the restriction is natural in
  the inverse-image leg. `corrRestr_eq_of_eq`: restrictions along equal maps agree up to the
  identifications of their targets.
* **Transport.** For `φ : q⁻¹ N ⟶ p⁻¹ M` on `X` and `j : X' ⟶ X`, its transport along `j` is
  `(j ≫ q)⁻¹ N ≅ j⁻¹ q⁻¹ N ⟶ j⁻¹ p⁻¹ M ≅ (j ≫ p)⁻¹ M`. `pullbackPlusCompIso_transport`: transport
  along `i ≫ j` is transport along `j`, then along `i`; `eqToHom_comp_transport`: transports along
  equal maps agree. `pullbackPlusCompIso_hom_app_eqToHom` and `pullbackPlusCompIso_inv_app_eqToHom`
  compare the composition isomorphisms along equal maps.
* **Equal legs.** For `u = v : X ⟶ Y` with invertible derived unit of `v`, `corrUnitIso k h` is
  the isomorphism `u⁻¹ ⋙ Rv_* ≅ 𝟭`; `pullbackPlus_map_corrUnitIso_inv_app_counit` and
  `pullbackPlus_map_corrUnitIso_inv_app_transport` compute its inverse against the counit of `v`
  and against its transport.
* **Transported counits.** `transportCounit k π u v : (u⁻¹ ⋙ Rv_*) ⋙ (π ≫ v)⁻¹ ⟶ (π ≫ u)⁻¹` is
  the transport along `π` of the counit of `v`, as a natural transformation
  (`transportCounit_app`). Against equal legs: `whiskerRight_corrUnitIso_inv_transportCounit`
  (it inverts `corrUnitIso`) and `corrUnitIso_inv_corrRestr` (the inverse of `corrUnitIso`
  followed by a restriction is a derived unit); `whiskerLeft_derivedUnit_transportCounit` (the
  unit of a composite against the transported counit is a restriction) and
  `corrUnitIso_corrRestr_transportCounit` (a restriction through equal legs), all as equations
  of natural transformations.

The coherence proofs are carried out for abstract adjunctions (private lemmas) and instantiated.
Derived categories are instance arguments, one for each space a statement mentions.
-/

noncomputable section
open CategoryTheory Limits

namespace TDA.Sheaf

variable (k : Type) [Ring k]

/-- For an adjunction `L ⊣ R` and `h : A ⟶ R M`, the unit at `A` followed by `R` of the adjoint
`L h ≫ ε M` of `h` is `h`. -/
private lemma unit_map_counit {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : C} {M : D} (h : A ⟶ R.obj M) :
    adj.unit.app A ≫ R.map (L.map h ≫ adj.counit.app M) = h := by
  simp

section abstract

variable {CZ CY CX : Type*} [Category* CZ] [Category* CY] [Category* CX]
  {Lq : CZ ⥤ CY} {Rq : CY ⥤ CZ} {Lτ : CY ⥤ CX} {Rτ : CX ⥤ CY} {Lc : CZ ⥤ CX} {Rc : CX ⥤ CZ}
  (adjq : Lq ⊣ Rq) (adjτ : Lτ ⊣ Rτ) (adjc : Lc ⊣ Rc) (cL : Lq ⋙ Lτ ≅ Lc) (cR : Rc ≅ Rτ ⋙ Rq)

/-- Abstract form of `derivedUnit_comp_app_counit`. -/
private lemma unit_comp_counit_abs
    (hU : ∀ A, adjc.unit.app A = adjq.unit.app A ≫ Rq.map (adjτ.unit.app (Lq.obj A)) ≫
      Rq.map (Rτ.map (cL.hom.app A)) ≫ cR.inv.app (Lc.obj A)) (N : CY) :
    adjc.unit.app (Rq.obj N) ≫ Rc.map (cL.inv.app (Rq.obj N) ≫ Lτ.map (adjq.counit.app N)) =
      Rq.map (adjτ.unit.app N) ≫ cR.inv.app (Lτ.obj N) := by
  rw [hU]
  have n₁ := cR.inv.naturality (cL.inv.app (Rq.obj N) ≫ Lτ.map (adjq.counit.app N))
  simp only [Functor.comp_map, Functor.comp_obj] at n₁
  simp only [Category.assoc, ← n₁, ← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app_assoc]
  have n₂ := adjτ.unit.naturality (adjq.counit.app N)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n₂
  rw [← n₂, Functor.map_comp, Category.assoc, adjq.right_triangle_components_assoc]
  rfl

/-- Abstract form of `derivedUnit_comp_app_pullbackPlusCompIso_inv`. -/
private lemma unit_comp_inv_abs
    (hU : ∀ A, adjc.unit.app A = adjq.unit.app A ≫ Rq.map (adjτ.unit.app (Lq.obj A)) ≫
      Rq.map (Rτ.map (cL.hom.app A)) ≫ cR.inv.app (Lc.obj A)) (A : CZ) :
    adjc.unit.app A ≫ Rc.map (cL.inv.app A) =
      adjq.unit.app A ≫ Rq.map (adjτ.unit.app (Lq.obj A)) ≫ cR.inv.app (Lτ.obj (Lq.obj A)) := by
  rw [hU]
  have n := cR.inv.naturality (cL.inv.app A)
  simp only [Functor.comp_map, Functor.comp_obj] at n
  simp only [Category.assoc, ← n, ← Functor.map_comp_assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  simp

/-- Abstract form of `corrRestr_counit`. -/
private lemma counit_comp_unit_abs
    (hC : ∀ Y, Lc.map (cR.inv.app Y) ≫ adjc.counit.app Y =
      cL.inv.app (Rq.obj (Rτ.obj Y)) ≫ Lτ.map (adjq.counit.app (Rτ.obj Y)) ≫ adjτ.counit.app Y)
    (N : CY) :
    Lc.map (Rq.map (adjτ.unit.app N) ≫ cR.inv.app (Lτ.obj N)) ≫ adjc.counit.app (Lτ.obj N) =
      cL.inv.app (Rq.obj N) ≫ Lτ.map (adjq.counit.app N) := by
  rw [Functor.map_comp, Category.assoc, hC]
  have n₁ := cL.inv.naturality (Rq.map (adjτ.unit.app N))
  simp only [Functor.comp_map, Functor.comp_obj] at n₁
  rw [reassoc_of% n₁, ← Functor.map_comp_assoc]
  have n₂ := adjq.counit.naturality (adjτ.unit.app N)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n₂
  rw [n₂, Functor.map_comp, Category.assoc, adjτ.left_triangle_components, Category.comp_id]

end abstract

section counit

variable {X Y Z : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{0} k))]

/-- **The counit of a composite.** For `f : X ⟶ Y`, `g : Y ⟶ Z` and `M ∈ D⁺(Sh X)`,
`(f ≫ g)⁻¹` of `Rg_* Rf_* M ≅ R(f ≫ g)_* M` followed by the counit of `f ≫ g` is
`(f ≫ g)⁻¹ ≅ f⁻¹ g⁻¹`, then `f⁻¹` of the counit of `g` at `Rf_* M`, then the counit of `f`. -/
lemma derivedCounit_comp_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory.Plus (X.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k (f ≫ g)).map ((pushforwardPlusCompIso k f g).inv.app M) ≫
        (derivedCounit k (f ≫ g)).app M =
      (pullbackPlusCompIso k f g).inv.app ((pushforwardPlus k g).obj ((pushforwardPlus k f).obj M)) ≫
        (pullbackPlus k f).map ((derivedCounit k g).app ((pushforwardPlus k f).obj M)) ≫
        (derivedCounit k f).app M := by
  apply ((derivedAdjunction k (f ≫ g)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, derivedAdjunction_unit, Functor.map_comp, Functor.comp_obj]
  have n₁ := (derivedUnit k (f ≫ g)).naturality ((pushforwardPlusCompIso k f g).inv.app M)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n₁
  rw [← reassoc_of% n₁]
  have t := (derivedAdjunction k (f ≫ g)).right_triangle_components M
  simp only [derivedAdjunction_unit, derivedAdjunction_counit] at t
  rw [t, Category.comp_id, derivedUnit_comp_app']
  have n₂ := (pushforwardPlusCompIso k f g).inv.naturality
    ((pullbackPlusCompIso k f g).inv.app ((pushforwardPlus k g).obj ((pushforwardPlus k f).obj M)) ≫
      (pullbackPlus k f).map ((derivedCounit k g).app ((pushforwardPlus k f).obj M)) ≫
      (derivedCounit k f).app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp] at n₂
  simp only [Category.assoc]
  rw [← n₂]
  have n₃ := (derivedUnit k f).naturality ((derivedCounit k g).app ((pushforwardPlus k f).obj M))
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n₃
  have t₁ := (derivedAdjunction k f).right_triangle_components M
  have t₂ := (derivedAdjunction k g).right_triangle_components ((pushforwardPlus k f).obj M)
  simp only [derivedAdjunction_unit, derivedAdjunction_counit] at t₁ t₂
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  have key : (derivedUnit k f).app
        ((pullbackPlus k g).obj ((pushforwardPlus k g).obj ((pushforwardPlus k f).obj M))) ≫
      (pushforwardPlus k f).map
        ((pullbackPlus k f).map ((derivedCounit k g).app ((pushforwardPlus k f).obj M)) ≫
          (derivedCounit k f).app M) = (derivedCounit k g).app ((pushforwardPlus k f).obj M) := by
    exact unit_map_counit (derivedAdjunction k f) _
  simp only [key, Functor.id_obj, reassoc_of% t₂]

/-- **The unit of a composite against a counit.** For `τ : X ⟶ Y`, `q : Y ⟶ Z` and
`N ∈ D⁺(Sh Y)`, the derived unit of `τ ≫ q` at `Rq_* N`, followed by `R(τ ≫ q)_*` of
`(τ ≫ q)⁻¹ ≅ τ⁻¹ q⁻¹` and `τ⁻¹` of the counit of `q`, is `Rq_*` of the unit of `τ` followed by
`Rq_* Rτ_* ≅ R(τ ≫ q)_*`. -/
lemma derivedUnit_comp_app_counit (τ : X ⟶ Y) (q : Y ⟶ Z)
    (N : DerivedCategory.Plus (Y.Sheaf (ModuleCat.{0} k))) :
    (derivedUnit k (τ ≫ q)).app ((pushforwardPlus k q).obj N) ≫
        (pushforwardPlus k (τ ≫ q)).map
          ((pullbackPlusCompIso k τ q).inv.app ((pushforwardPlus k q).obj N) ≫
            (pullbackPlus k τ).map ((derivedCounit k q).app N)) =
      (pushforwardPlus k q).map ((derivedUnit k τ).app N) ≫
        (pushforwardPlusCompIso k τ q).inv.app ((pullbackPlus k τ).obj N) :=
  unit_comp_counit_abs (Lq := pullbackPlus k q) (Rq := pushforwardPlus k q)
    (Lτ := pullbackPlus k τ) (Rτ := pushforwardPlus k τ) (Lc := pullbackPlus k (τ ≫ q))
    (Rc := pushforwardPlus k (τ ≫ q)) (derivedAdjunction k q) (derivedAdjunction k τ)
    (derivedAdjunction k (τ ≫ q)) (pullbackPlusCompIso k τ q) (pushforwardPlusCompIso k τ q)
    (fun A => derivedUnit_comp_app' k τ q A) N

/-- **The unit of a composite against the composition isomorphism.** The derived unit of
`τ ≫ q` at `N`, followed by `R(τ ≫ q)_*` of `(τ ≫ q)⁻¹ ≅ τ⁻¹ q⁻¹`, is the unit of `q`, then
`Rq_*` of the unit of `τ`, then `Rq_* Rτ_* ≅ R(τ ≫ q)_*`. -/
lemma derivedUnit_comp_app_pullbackPlusCompIso_inv (τ : X ⟶ Y) (q : Y ⟶ Z)
    (N : DerivedCategory.Plus (Z.Sheaf (ModuleCat.{0} k))) :
    (derivedUnit k (τ ≫ q)).app N ≫
        (pushforwardPlus k (τ ≫ q)).map ((pullbackPlusCompIso k τ q).inv.app N) =
      (derivedUnit k q).app N ≫ (pushforwardPlus k q).map ((derivedUnit k τ).app ((pullbackPlus k q).obj N)) ≫
        (pushforwardPlusCompIso k τ q).inv.app ((pullbackPlus k τ).obj ((pullbackPlus k q).obj N)) :=
  unit_comp_inv_abs (Lq := pullbackPlus k q) (Rq := pushforwardPlus k q)
    (Lτ := pullbackPlus k τ) (Rτ := pushforwardPlus k τ) (Lc := pullbackPlus k (τ ≫ q))
    (Rc := pushforwardPlus k (τ ≫ q)) (derivedAdjunction k q) (derivedAdjunction k τ)
    (derivedAdjunction k (τ ≫ q)) (pullbackPlusCompIso k τ q) (pushforwardPlusCompIso k τ q)
    (fun A => derivedUnit_comp_app' k τ q A) N

end counit

section corr

variable {X' X Z W Z' : TopCat.{0}}
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (W.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Z'.Sheaf (ModuleCat.{0} k))]

/-- **`corrRestr` against the counit.** For `j : X' ⟶ X`, `(j ≫ q)⁻¹` of the restriction
`corrRestr k j p q` at `M`, followed by the counit of `j ≫ q`, is `(j ≫ q)⁻¹ ≅ j⁻¹ q⁻¹`, then `j⁻¹`
of the counit of `q`, then `j⁻¹ p⁻¹ ≅ (j ≫ p)⁻¹`: the adjoint of the restriction is the
restriction of the counit. -/
lemma corrRestr_counit (j : X' ⟶ X) (p : X ⟶ Z) (q : X ⟶ W)
    (M : DerivedCategory.Plus (Z.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k (j ≫ q)).map ((corrRestr k j p q).app M) ≫
        (derivedCounit k (j ≫ q)).app ((pullbackPlus k (j ≫ p)).obj M) =
      (pullbackPlusCompIso k j q).inv.app ((pushforwardPlus k q).obj ((pullbackPlus k p).obj M)) ≫
        (pullbackPlus k j).map ((derivedCounit k q).app ((pullbackPlus k p).obj M)) ≫
        (pullbackPlusCompIso k j p).hom.app M := by
  have h := counit_comp_unit_abs (Lq := pullbackPlus k q) (Rq := pushforwardPlus k q)
    (Lτ := pullbackPlus k j) (Rτ := pushforwardPlus k j) (Lc := pullbackPlus k (j ≫ q))
    (Rc := pushforwardPlus k (j ≫ q)) (derivedAdjunction k q) (derivedAdjunction k j)
    (derivedAdjunction k (j ≫ q)) (pullbackPlusCompIso k j q) (pushforwardPlusCompIso k j q)
    (fun Y => derivedCounit_comp_app k j q Y) ((pullbackPlus k p).obj M)
  simp only [derivedAdjunction_unit, derivedAdjunction_counit, Functor.map_comp,
    Category.assoc] at h
  have n := (derivedCounit k (j ≫ q)).naturality ((pullbackPlusCompIso k j p).hom.app M)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n
  simp only [corrRestr_app, Functor.map_comp, Category.assoc, n, reassoc_of% h]

/-- **Naturality of `corrRestr` in the inverse image.** Let `ψ₁ : p⁻¹ Y ⟶ p'⁻¹ M` and
`ψ₀ : (j ≫ p)⁻¹ Y ⟶ (j ≫ p')⁻¹ M` agree up to `j⁻¹ p⁻¹ ≅ (j ≫ p)⁻¹` and `j⁻¹ p'⁻¹ ≅ (j ≫ p')⁻¹`.
Then the restriction along `j` followed by `R(j ≫ q)_* ψ₀` is `Rq_* ψ₁` followed by the
restriction along `j`. -/
lemma corrRestr_app_comp_map (j : X' ⟶ X) (p : X ⟶ Z) (p' : X ⟶ Z') (q : X ⟶ W)
    (Y : DerivedCategory.Plus (Z.Sheaf (ModuleCat.{0} k)))
    (M : DerivedCategory.Plus (Z'.Sheaf (ModuleCat.{0} k)))
    (ψ₁ : (pullbackPlus k p).obj Y ⟶ (pullbackPlus k p').obj M)
    (ψ₀ : (pullbackPlus k (j ≫ p)).obj Y ⟶ (pullbackPlus k (j ≫ p')).obj M)
    (h : (pullbackPlusCompIso k j p).hom.app Y ≫ ψ₀ =
      (pullbackPlus k j).map ψ₁ ≫ (pullbackPlusCompIso k j p').hom.app M) :
    (corrRestr k j p q).app Y ≫ (pushforwardPlus k (j ≫ q)).map ψ₀ =
      (pushforwardPlus k q).map ψ₁ ≫ (corrRestr k j p' q).app M := by
  have n₁ := (pushforwardPlusCompIso k j q).inv.naturality ((pullbackPlus k j).map ψ₁)
  have n₂ := (derivedUnit k j).naturality ψ₁
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n₁ n₂
  simp only [corrRestr_app, Category.assoc, ← Functor.map_comp, h]
  simp only [Functor.map_comp, ← Functor.map_comp_assoc, n₂]
  simp only [Category.assoc, reassoc_of% n₁]

end corr

section transport

variable {V X' X Z Z' : TopCat.{0}}
  [HasDerivedCategory (V.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Z'.Sheaf (ModuleCat.{0} k))]

/-- **Transport of a morphism of inverse images along a composite.** For
`φ : q⁻¹ N ⟶ p⁻¹ M` on `X` and `i : V ⟶ X'`, `j : X' ⟶ X`, the transport
`(i ≫ j ≫ q)⁻¹ N ⟶ (i ≫ j ≫ p)⁻¹ M` of `φ` along `i ≫ j` (through `pullbackPlusCompIso`) is `i⁻¹`
of its transport along `j`, up to `i⁻¹ (j ≫ q)⁻¹ ≅ (i ≫ j ≫ q)⁻¹` and
`i⁻¹ (j ≫ p)⁻¹ ≅ (i ≫ j ≫ p)⁻¹`. -/
lemma pullbackPlusCompIso_transport (i : V ⟶ X') (j : X' ⟶ X) (q : X ⟶ Z) (p : X ⟶ Z')
    (N : DerivedCategory.Plus (Z.Sheaf (ModuleCat.{0} k)))
    (M : DerivedCategory.Plus (Z'.Sheaf (ModuleCat.{0} k)))
    (φ : (pullbackPlus k q).obj N ⟶ (pullbackPlus k p).obj M) :
    (pullbackPlusCompIso k i (j ≫ q)).hom.app N ≫ (pullbackPlusCompIso k (i ≫ j) q).inv.app N ≫
        (pullbackPlus k (i ≫ j)).map φ ≫ (pullbackPlusCompIso k (i ≫ j) p).hom.app M =
      (pullbackPlus k i).map ((pullbackPlusCompIso k j q).inv.app N ≫ (pullbackPlus k j).map φ ≫
          (pullbackPlusCompIso k j p).hom.app M) ≫
        (pullbackPlusCompIso k i (j ≫ p)).hom.app M := by
  have a₁ := pullbackPlusCompIso_hom_assoc_app k i j q N
  have a₂ := pullbackPlusCompIso_hom_assoc_app k i j p M
  have n := (pullbackPlusCompIso k i j).hom.naturality φ
  simp only [Functor.comp_map, Functor.comp_obj] at n
  have a₁' : (pullbackPlusCompIso k i (j ≫ q)).hom.app N ≫
      (pullbackPlusCompIso k (i ≫ j) q).inv.app N =
      (pullbackPlus k i).map ((pullbackPlusCompIso k j q).inv.app N) ≫
        (pullbackPlusCompIso k i j).hom.app ((pullbackPlus k q).obj N) := by
    rw [← cancel_epi ((pullbackPlus k i).map ((pullbackPlusCompIso k j q).hom.app N)),
      reassoc_of% a₁]
    simp only [Iso.hom_inv_id_app, ← Functor.map_comp_assoc, Functor.comp_obj]
    simp only [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% a₁', reassoc_of% n, a₂]

/-- The transport along `τ` and along `π` of a morphism `φ : q⁻¹ N ⟶ p⁻¹ M` agree along
`τ = π`, up to the identifications of the inverse images. -/
lemma eqToHom_comp_transport {τ π : V ⟶ X} (h : τ = π) (q : X ⟶ Z) (p : X ⟶ Z')
    (N : DerivedCategory.Plus (Z.Sheaf (ModuleCat.{0} k)))
    (M : DerivedCategory.Plus (Z'.Sheaf (ModuleCat.{0} k)))
    (φ : (pullbackPlus k q).obj N ⟶ (pullbackPlus k p).obj M) :
    eqToHom (congrArg (fun r => (pullbackPlus k (r ≫ q)).obj N) h) ≫
        (pullbackPlusCompIso k π q).inv.app N ≫ (pullbackPlus k π).map φ ≫
          (pullbackPlusCompIso k π p).hom.app M =
      ((pullbackPlusCompIso k τ q).inv.app N ≫ (pullbackPlus k τ).map φ ≫
          (pullbackPlusCompIso k τ p).hom.app M) ≫
        eqToHom (congrArg (fun r => (pullbackPlus k (r ≫ p)).obj M) h) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end transport

section eq

variable {X Y R X' Z W : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (R.Sheaf (ModuleCat.{0} k))]

/-- `pullbackPlusCompIso k π u` against the identification along `u = u'`: `π⁻¹` of the
identification `u⁻¹ M = u'⁻¹ M`, then `π⁻¹ u'⁻¹ ≅ (π ≫ u')⁻¹`, then the identification
`(π ≫ u')⁻¹ M = (π ≫ u)⁻¹ M`, is `π⁻¹ u⁻¹ ≅ (π ≫ u)⁻¹`. -/
lemma pullbackPlusCompIso_hom_app_eqToHom (π : X ⟶ Y) {u u' : Y ⟶ R} (h : u = u')
    (M : DerivedCategory.Plus (R.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k π).map ((eqToHom (congrArg (pullbackPlus k) h)).app M) ≫
        (pullbackPlusCompIso k π u').hom.app M ≫
        eqToHom (congrArg (fun r => (pullbackPlus k (π ≫ r)).obj M) h.symm) =
      (pullbackPlusCompIso k π u).hom.app M := by
  subst h
  simp

/-- `pullbackPlusCompIso k π u` against the identification along `u = u'`, the other way round:
`(π ≫ u)⁻¹ ≅ π⁻¹ u⁻¹`, then `π⁻¹` of the identification `u⁻¹ M = u'⁻¹ M`, then
`π⁻¹ u'⁻¹ ≅ (π ≫ u')⁻¹` is the identification `(π ≫ u)⁻¹ M = (π ≫ u')⁻¹ M`. -/
lemma pullbackPlusCompIso_inv_app_eqToHom (π : X ⟶ Y) {u u' : Y ⟶ R} (h : u = u')
    (M : DerivedCategory.Plus (R.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlusCompIso k π u).inv.app M ≫
        (pullbackPlus k π).map ((eqToHom (congrArg (pullbackPlus k) h)).app M) ≫
        (pullbackPlusCompIso k π u').hom.app M =
      eqToHom (congrArg (fun r => (pullbackPlus k (π ≫ r)).obj M) h) := by
  subst h
  simp

variable [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (W.Sheaf (ModuleCat.{0} k))]

omit [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (R.Sheaf (ModuleCat.{0} k))] in
/-- `corrRestr` along equal maps `j' = j`: the restriction along `j'` is the restriction along `j`
followed by the identifications `(j ≫ p)⁻¹ = (j' ≫ p)⁻¹` and `R(j ≫ q)_* = R(j' ≫ q)_*`. -/
lemma corrRestr_eq_of_eq {j j' : X' ⟶ X} (h : j' = j) (p : X ⟶ Z) (q : X ⟶ W) :
    corrRestr k j' p q = corrRestr k j p q ≫
      Functor.whiskerRight (eqToHom (congrArg (fun r => pullbackPlus k (r ≫ p)) h.symm))
        (pushforwardPlus k (j ≫ q)) ≫
      Functor.whiskerLeft (pullbackPlus k (j' ≫ p))
        (eqToHom (congrArg (fun r => pushforwardPlus k (r ≫ q)) h.symm)) := by
  subst h
  simp only [eqToHom_refl, Functor.whiskerRight_id', Functor.whiskerLeft_id', Category.comp_id]

end eq

section unitIso

variable {X Y Z' : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Z'.Sheaf (ModuleCat.{0} k))]

/-- **The unit isomorphism of a correspondence with equal legs.** For `u = v : X ⟶ Y` with
invertible derived unit `𝟭 ⟶ v⁻¹ ⋙ Rv_*`, the isomorphism `u⁻¹ ⋙ Rv_* ≅ 𝟭`: `u⁻¹ = v⁻¹`, then the
inverse of the derived unit of `v`. -/
def corrUnitIso {u v : X ⟶ Y} (h : u = v) [IsIso (derivedUnit k v)] :
    pullbackPlus k u ⋙ pushforwardPlus k v ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (eqToIso (congrArg (pullbackPlus k) h)) (pushforwardPlus k v) ≪≫
    (asIso (derivedUnit k v)).symm

/-- `v⁻¹` of the inverse of `corrUnitIso`, followed by the counit of `v` at `u⁻¹ M`, is the
identification `v⁻¹ M = u⁻¹ M`. -/
lemma pullbackPlus_map_corrUnitIso_inv_app_counit {u v : X ⟶ Y} (h : u = v)
    [IsIso (derivedUnit k v)] (M : DerivedCategory.Plus (Y.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k v).map ((corrUnitIso k h).inv.app M) ≫
        (derivedCounit k v).app ((pullbackPlus k u).obj M) =
      (eqToHom (congrArg (pullbackPlus k) h.symm)).app M := by
  subst h
  have t := (derivedAdjunction k u).left_triangle_components M
  rw [derivedAdjunction_unit, derivedAdjunction_counit] at t
  simp [corrUnitIso, t]

omit [HasDerivedCategory (Z'.Sheaf (ModuleCat.{0} k))] in
/-- A composite through a naturality square `nat`, a factorisation `hX` and an identity `hV`. -/
private lemma comp_eq_of_nat' {C : Type*} [Category* C] {A A' B B' G F : C} (X'' : A ⟶ A')
    (ci : A' ⟶ B') (Le : B' ⟶ G) (c : G ⟶ F) (ci₀ : A ⟶ B) (LX : B ⟶ B') (Lf : B ⟶ G)
    (R' : A ⟶ F) (nat : X'' ≫ ci = ci₀ ≫ LX) (hX : LX ≫ Le = Lf) (hV : ci₀ ≫ Lf ≫ c = R') :
    X'' ≫ ci ≫ Le ≫ c = R' := by
  rw [reassoc_of% nat, reassoc_of% hX, hV]

/-- **`corrUnitIso` against a transported counit.** For `π : Z' ⟶ X`, `(π ≫ v)⁻¹` of the inverse
of `corrUnitIso` followed by the transport along `π` of the counit of `v` at `u⁻¹ M` is the
identification `(π ≫ v)⁻¹ M = (π ≫ u)⁻¹ M`. -/
lemma pullbackPlus_map_corrUnitIso_inv_app_transport (π : Z' ⟶ X) {u v : X ⟶ Y} (h : u = v)
    [IsIso (derivedUnit k v)] (M : DerivedCategory.Plus (Y.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k (π ≫ v)).map ((corrUnitIso k h).inv.app M) ≫
        (pullbackPlusCompIso k π v).inv.app ((pullbackPlus k u ⋙ pushforwardPlus k v).obj M) ≫
        (pullbackPlus k π).map ((derivedCounit k v).app ((pullbackPlus k u).obj M)) ≫
        (pullbackPlusCompIso k π u).hom.app M =
      eqToHom (congrArg (fun r => (pullbackPlus k (π ≫ r)).obj M) h.symm) := by
  have nat := (pullbackPlusCompIso k π v).inv.naturality ((corrUnitIso k h).inv.app M)
  simp only [Functor.comp_map] at nat
  exact comp_eq_of_nat' _ _ _ _ _ _ _ _ nat
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      (congrArg (pullbackPlus k π).map (pullbackPlus_map_corrUnitIso_inv_app_counit k h M)))
    (pullbackPlusCompIso_inv_app_eqToHom k π h.symm M)

end unitIso

section transportCounit

variable {X Y Y' Z' W : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Z'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (W.Sheaf (ModuleCat.{0} k))]

/-- **The transported counit as a natural transformation.** For `π : Z' ⟶ X` and a correspondence
`(u, v)` out of `X`, `(π ≫ v)⁻¹ (Rv_* u⁻¹ M) ≅ π⁻¹ v⁻¹ Rv_* u⁻¹ M ⟶ π⁻¹ u⁻¹ M ≅ (π ≫ u)⁻¹ M`:
`(π ≫ v)⁻¹ ≅ π⁻¹ v⁻¹`, then `π⁻¹` of the counit of `v` at `u⁻¹ M`, then `π⁻¹ u⁻¹ ≅ (π ≫ u)⁻¹`
(`transportCounit_app`). -/
def transportCounit (π : Z' ⟶ X) (u : X ⟶ Y') (v : X ⟶ Y) :
    (pullbackPlus k u ⋙ pushforwardPlus k v) ⋙ pullbackPlus k (π ≫ v) ⟶ pullbackPlus k (π ≫ u) :=
  Functor.whiskerLeft (pullbackPlus k u ⋙ pushforwardPlus k v) (pullbackPlusCompIso k π v).inv ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (pullbackPlus k u)
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedCounit k v) (pullbackPlus k π) ≫
        (Functor.leftUnitor _).hom) ≫
    (pullbackPlusCompIso k π u).hom

omit [HasDerivedCategory (W.Sheaf (ModuleCat.{0} k))] in
/-- The components of `transportCounit`. -/
lemma transportCounit_app (π : Z' ⟶ X) (u : X ⟶ Y') (v : X ⟶ Y)
    (M : DerivedCategory.Plus (Y'.Sheaf (ModuleCat.{0} k))) :
    (transportCounit k π u v).app M =
      (pullbackPlusCompIso k π v).inv.app ((pullbackPlus k u ⋙ pushforwardPlus k v).obj M) ≫
        (pullbackPlus k π).map ((derivedCounit k v).app ((pullbackPlus k u).obj M)) ≫
        (pullbackPlusCompIso k π u).hom.app M := by
  simp [transportCounit]

omit [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (W.Sheaf (ModuleCat.{0} k))] in
/-- **Equal legs against the transported counit.** For `u = v` with invertible derived unit of `v`,
`(π ≫ v)⁻¹` of the inverse of `corrUnitIso k h`, followed by `transportCounit k π u v`, is the
identification `(π ≫ v)⁻¹ = (π ≫ u)⁻¹`; a statement about natural transformations. -/
lemma whiskerRight_corrUnitIso_inv_transportCounit (π : Z' ⟶ X) {u v : X ⟶ Y} (h : u = v)
    [IsIso (derivedUnit k v)] :
    Functor.whiskerRight (corrUnitIso k h).inv (pullbackPlus k (π ≫ v)) ≫
        transportCounit k π u v =
      (Functor.leftUnitor _).hom ≫ eqToHom (congrArg (fun r => pullbackPlus k (π ≫ r)) h.symm) := by
  subst h
  refine NatTrans.ext (funext fun M => ?_)
  have := pullbackPlus_map_corrUnitIso_inv_app_transport k π (rfl : u = u) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, transportCounit_app,
    Functor.leftUnitor_hom_app, eqToHom_refl, NatTrans.id_app] at this ⊢
  exact this.trans (Category.id_comp _).symm

omit [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))] in
/-- **Equal legs against a restriction.** For `u = v : W ⟶ Y` with invertible derived unit of `v`
and `σ : Z' ⟶ W`, the inverse of `corrUnitIso k h` followed by the restriction along `σ` is the
derived unit of `σ ≫ v` followed by the identification `(σ ≫ v)⁻¹ = (σ ≫ u)⁻¹`. -/
lemma corrUnitIso_inv_corrRestr (σ : Z' ⟶ W) {u v : W ⟶ Y} (h : u = v)
    [IsIso (derivedUnit k v)] :
    (corrUnitIso k h).inv ≫ corrRestr k σ u v =
      derivedUnit k (σ ≫ v) ≫ Functor.whiskerRight
        (eqToHom (congrArg (fun r => pullbackPlus k (σ ≫ r)) h.symm))
        (pushforwardPlus k (σ ≫ v)) := by
  subst h
  refine NatTrans.ext (funext fun M => ?_)
  have n := (pushforwardPlusCompIso k σ u).inv.naturality ((pullbackPlusCompIso k σ u).hom.app M)
  simp only [Functor.comp_map] at n
  simp only [corrUnitIso, NatTrans.comp_app, Iso.trans_inv, Iso.symm_inv, asIso_hom,
    Functor.isoWhiskerRight_inv, eqToIso_refl, Iso.refl_inv, Functor.whiskerRight_id',
    Category.comp_id, eqToHom_refl, corrRestr_app, derivedUnit_comp_app', n]
  rfl

omit [HasDerivedCategory (W.Sheaf (ModuleCat.{0} k))] in
/-- **The unit of a composite against the transported counit.** For `π : Z' ⟶ X`, a
correspondence `(u, v)` out of `X` and `c = π ≫ v`, the derived unit of `c` at `Rv_* u⁻¹ M`,
followed by `Rc_*` of the transported counit, is the restriction `corrRestr k π u v` along `π`,
up to the identifications `c⁻¹ = (π ≫ v)⁻¹` and `R(π ≫ v)_* = Rc_*`. -/
lemma whiskerLeft_derivedUnit_transportCounit (π : Z' ⟶ X) (u : X ⟶ Y') (v : X ⟶ Y)
    {c : Z' ⟶ Y} (hc : π ≫ v = c) :
    Functor.whiskerLeft (pullbackPlus k u ⋙ pushforwardPlus k v) (derivedUnit k c) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.whiskerLeft (pullbackPlus k u ⋙ pushforwardPlus k v)
          (eqToHom (congrArg (pullbackPlus k) hc.symm)) ≫ transportCounit k π u v)
          (pushforwardPlus k c) =
      (Functor.rightUnitor _).hom ≫ corrRestr k π u v ≫
        Functor.whiskerLeft (pullbackPlus k (π ≫ u))
          (eqToHom (congrArg (pushforwardPlus k) hc)) := by
  subst hc
  refine NatTrans.ext (funext fun M => ?_)
  have t := derivedUnit_comp_app_counit k π v ((pullbackPlus k u).obj M)
  simp only [Functor.map_comp] at t
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.rightUnitor_hom_app, eqToHom_refl,
    Functor.whiskerLeft_id', Category.id_comp, Category.comp_id,
    transportCounit_app, corrRestr_app, Functor.map_comp, Functor.comp_obj]
  rw [reassoc_of% t]
  exact (Category.id_comp _).symm

/-- **A restriction through equal legs.** Let `π : Z' ⟶ X` with a correspondence `(u, v)` out of
`X`, and `σ : Z' ⟶ W` with equal legs `u₀ = v₀ : W ⟶ Y` and invertible derived unit of `v₀`, such
that `σ ≫ u₀ = π ≫ v` and `π ≫ v = σ ≫ v₀`. Whiskered by `u⁻¹ ⋙ Rv_*`, the inverse of
`corrUnitIso k h₀` and the restriction along `σ`, followed by `R(σ ≫ v₀)_*` of a transformation
`γ` equal to the transported counit, is the restriction along `π` followed by a transformation `ε`
equal to the identification `R(π ≫ v)_* = R(σ ≫ v₀)_*`. -/
lemma corrUnitIso_corrRestr_transportCounit (π : Z' ⟶ X) (u : X ⟶ Y') (v : X ⟶ Y)
    (σ : Z' ⟶ W) {u₀ v₀ : W ⟶ Y} (h₀ : u₀ = v₀) [IsIso (derivedUnit k v₀)]
    (w : σ ≫ u₀ = π ≫ v) (hc : π ≫ v = σ ≫ v₀)
    (γ : (pullbackPlus k u ⋙ pushforwardPlus k v) ⋙ pullbackPlus k (σ ≫ u₀) ⟶
      pullbackPlus k (π ≫ u))
    (hγ : γ = Functor.whiskerLeft _ (eqToHom (congrArg (pullbackPlus k) w)) ≫
      transportCounit k π u v)
    (ε : pullbackPlus k (π ≫ u) ⋙ pushforwardPlus k (π ≫ v) ⟶
      pullbackPlus k (π ≫ u) ⋙ pushforwardPlus k (σ ≫ v₀))
    (hε : ε = Functor.whiskerLeft _ (eqToHom (congrArg (pushforwardPlus k) hc))) :
    Functor.whiskerLeft (pullbackPlus k u ⋙ pushforwardPlus k v) (corrUnitIso k h₀).inv ≫
        Functor.whiskerLeft (pullbackPlus k u ⋙ pushforwardPlus k v) (corrRestr k σ u₀ v₀) ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ (pushforwardPlus k (σ ≫ v₀)) =
      (Functor.rightUnitor _).hom ≫ corrRestr k π u v ≫ ε := by
  subst h₀ hγ hε
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, corrUnitIso_inv_corrRestr]
  simp only [eqToHom_refl, Functor.whiskerRight_id', Category.comp_id]
  exact whiskerLeft_derivedUnit_transportCounit k π u v hc

end transportCounit

end TDA.Sheaf
