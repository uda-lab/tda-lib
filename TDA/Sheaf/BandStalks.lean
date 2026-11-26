import TDA.Sheaf.IntervalAcyclic
import TDA.Sheaf.IntervalFibre

/-!
# Stalks of the derived direct image along a band projection

Let `k` be a ring and `a y : ℝ`. The fibre `(q a)⁻¹ {y}` of the second projection of the closed
band `D a` is parametrised by `[y - a, y + a]` through `fibreEmb a y : x ↦ (x, y)`
(`mem_range_fibreEmb`; `fibreEmb_eq` relates it to `fibreIso a y`). The stalk at `y` is read
through the inverse image along `ptAt y : pt ⟶ ℝ`, and `fibreEmb a y ≫ q a = toPt _ ≫ ptAt y`
(`fibreEmb_comp_q`).

Degree-0 tautness of the fibre:

* `exists_le_eq_zero_of_pullback_eq_zero` (any continuous `i`): a section of `G` whose image in
  `i⁻¹ G` vanishes over an open `N` vanishes over an open neighbourhood of `i(N)`.
* `exists_preimage_q_le`: tubes `(q a)⁻¹ U`, `U ∋ y` open, are cofinal among the open
  neighbourhoods of the fibre, since `q a` is proper.
* `exists_unit_eq_fibreEmb`: every section of `(fibreEmb a y)⁻¹ G` over the fibre comes from a
  section of `G` over an open neighbourhood of the fibre. Local representatives are merged from
  left to right along `[y - a, y + a]` (a supremum argument); on the overlap two representatives
  agree near the fibre, hence on a box around a point of the fibre, and the two opens are cut at
  that point.
* `exists_unit_eq_of_pt`: global sections of an inverse image to the point are restrictions of
  unit images of sections near the image point.

The stalk:

* `stalkComparison a y G : (ptAt y)⁻¹ (q a)_* G ⟶ Γ([y - a, y + a]; (fibreEmb a y)⁻¹ G)`, the
  adjoint of `(q a)_*` applied to the unit; it is described on sections by
  `stalkComparison_app_top`, is natural (`stalkComparison_naturality`) and is an isomorphism
  (`isIso_stalkComparison`). `stalkIso a y` is the natural isomorphism
  `(q a)_* ⋙ (ptAt y)⁻¹ ≅ (fibreEmb a y)⁻¹ ⋙ Γ([y - a, y + a]; -)`, and `stalkSectionsIso` reads
  it as `((q a)_* G)_y ≅ Γ([y - a, y + a]; (fibreEmb a y)⁻¹ G)`.

The stalk formula, for `F ∈ D⁺(Sh(D a))`:

* `nonempty_stalkFormula`, `stalkFormula`: `Hⁱ((ptAt y)⁻¹ R(q a)_* F) ≅
  Hⁱ([y - a, y + a]; (fibreEmb a y)⁻¹ F)`. On a bounded below injective model `I` of `F`,
  `(q a)_* I` computes `R(q a)_* F`, `stalkIso` identifies `(ptAt y)⁻¹ (q a)_* I` with
  `Γ([y - a, y + a]; (fibreEmb a y)⁻¹ I)` termwise, and the sheaves `(fibreEmb a y)⁻¹ Iⁿ` are
  germ-surjective (`germSurjective_pullback_of_isFlasque`), hence compute
  `RΓ([y - a, y + a]; -)` (`isIso_rightDerivedFunctorPlusUnit_app_toPt_Icc_of_germSurjective`).
* `isZero_H_stalk_pushforwardPlus_q`: for a sheaf `G` placed in degree `0`, these stalks vanish in
  degrees `i ≥ 2` (`isZero_H_Icc`).

Derived categories are instance arguments for exactly the spaces each statement mentions.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable {k : Type} [Ring k]

section taut

/-- **Vanishing near a subset.** Let `i : K ⟶ X` be continuous, `s` a section of a sheaf `G` of
`k`-modules over `W`, and `N ≤ i⁻¹ W` open. If the image of `s` in `i⁻¹ G` vanishes over `N`,
then `s` vanishes over an open `O ≤ W` with `N ≤ i⁻¹ O`. -/
theorem exists_le_eq_zero_of_pullback_eq_zero {K X : TopCat.{0}} (i : K ⟶ X)
    (G : X.Sheaf (ModuleCat.{0} k)) {W : Opens X} (s : G.presheaf.obj (op W)) {N : Opens K}
    (hN : N ≤ (Opens.map i).obj W)
    (hs : ((TopCat.Sheaf.pullback (ModuleCat.{0} k) i).obj G).presheaf.map (homOfLE hN).op
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) i).unit.app G).hom.app
        (op W) s) = 0) :
    ∃ (O : Opens X) (hO : O ≤ W), N ≤ (Opens.map i).obj O ∧
      G.presheaf.map (homOfLE hO).op s = 0 := by
  have hgerm (x : K) (hx : x ∈ N) : ∃ (V : Opens X) (_ : i x ∈ V) (hVW : V ≤ W),
      G.presheaf.map (homOfLE hVW).op s = 0 := by
    have h1 : (stalkPullbackSheafIso k i G x).hom (G.presheaf.germ W (i x) (hN hx) s) = 0 :=
      (stalkPullbackSheafIso_unit k i G W x (hN hx) s).trans
        ((TopCat.Presheaf.germ_res_apply _ (homOfLE hN) x hx _).symm.trans (by rw [hs, map_zero]))
    have h2 : G.presheaf.germ W (i x) (hN hx) s = G.presheaf.germ W (i x) (hN hx) 0 := by
      rw [map_zero]
      have := congrArg (stalkPullbackSheafIso k i G x).inv h1
      rwa [Iso.hom_inv_id_apply, map_zero] at this
    obtain ⟨V, hxV, i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq G.presheaf (i x) (hN hx) (hN hx) s 0 h2
    refine ⟨V, hxV, leOfHom i₁, ?_⟩
    rw [show homOfLE (leOfHom i₁) = i₁ from Subsingleton.elim _ _, he, map_zero]
  choose V hxV hVW hV using hgerm
  let U : N → Opens X := fun x => V x.1 x.2
  have hO : iSup U ≤ W := iSup_le fun x => hVW x.1 x.2
  refine ⟨iSup U, hO, fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV x hx⟩, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq G U _ _ fun x => ?_
  rw [map_zero, ← ConcreteCategory.comp_apply, ← G.presheaf.map_comp, ← op_comp,
    Subsingleton.elim (Opens.leSupr U x ≫ homOfLE hO) (homOfLE (hVW x.1 x.2))]
  exact hV x.1 x.2

/-- **Global sections of an inverse image to the point.** For `f : pt ⟶ Y` and a sheaf `M` of
`k`-modules on `Y`, every global section of `f⁻¹ M` is the restriction of the image under the
adjunction unit of a section of `M` over an open `U` containing the image point. -/
theorem exists_unit_eq_of_pt {Y : TopCat.{0}} (f : pt ⟶ Y) (M : Y.Sheaf (ModuleCat.{0} k))
    (x : ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj M).presheaf.obj (op ⊤)) :
    ∃ (U : Opens Y) (hU : ⊤ ≤ (Opens.map f).obj U) (s : M.presheaf.obj (op U)),
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj M).presheaf.map (homOfLE hU).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app M).hom.app
          (op U) s) = x := by
  let P := (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj M
  let p : pt := PUnit.unit
  obtain ⟨U, hU, s, hs⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf
    ((stalkPullbackSheafIso k f M p).inv (P.presheaf.germ ⊤ p trivial x))
  have hTop : ⊤ ≤ (Opens.map f).obj U := fun q _ => by
    obtain rfl : q = p := Subsingleton.elim _ _
    exact hU
  refine ⟨U, hTop, s, (germ_top_bijective P p).1 ?_⟩
  exact (TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE hTop) p trivial _).trans
    ((stalkPullbackSheafIso_unit k f M U p hU s).symm.trans (by rw [hs, Iso.inv_hom_id_apply]))

end taut

namespace BandConvolution

/-- The point `y` of the real line, as a map from the one-point space. -/
def ptAt (y : ℝ) : pt ⟶ realLine := TopCat.ofHom (ContinuousMap.const _ y)

/-- The fibre `(q a)⁻¹ {y}` parametrised by `[y - a, y + a]`: `x ↦ (x, y)`. -/
def fibreEmb (a y : ℝ) : TopCat.of (Set.Icc (y - a) (y + a)) ⟶ D a :=
  TopCat.ofHom ⟨fun x => ⟨(x.1, y), by
      change dist x.1 y ≤ a
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [x.2.1, x.2.2], by linarith [x.2.1, x.2.2]⟩⟩,
    (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩

/-- `fibreEmb a y` sends `x` to `(x, y)`. -/
@[simp]
theorem coe_fibreEmb_apply (a y : ℝ) (x : TopCat.of (Set.Icc (y - a) (y + a))) :
    ((fibreEmb a y x : band a) : ℝ × ℝ) = (x.1, y) := rfl

/-- `fibreEmb a y` is the inverse of `fibreIso a y` followed by the inclusion of the fibre. -/
theorem fibreEmb_eq (a y : ℝ) :
    fibreEmb a y = (fibreIso a y).inv ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :=
  rfl

/-- The image of `fibreEmb a y` is the fibre `(q a)⁻¹ {y}`. -/
theorem mem_range_fibreEmb {a y : ℝ} {z : D a} : z ∈ Set.range (fibreEmb a y) ↔ q a z = y := by
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro h
    refine ⟨fibreHomeo a y ⟨z, h⟩, Subtype.ext (Prod.ext rfl ?_)⟩
    exact h.symm

/-- The fibre square: `fibreEmb a y ≫ q a = toPt _ ≫ ptAt y`. -/
theorem fibreEmb_comp_q (a y : ℝ) : fibreEmb a y ≫ q a = toPt _ ≫ ptAt y := rfl

/-- **Tubes are cofinal.** An open subset of the band containing the fibre `(q a)⁻¹ {y}`
contains `(q a)⁻¹ U` for an open `U ∋ y`, because `q a` is a closed map (`isProperMap_q`). -/
theorem exists_preimage_q_le (a y : ℝ) (W : Opens (D a)) (hW : ∀ z : D a, q a z = y → z ∈ W) :
    ∃ U : Opens realLine, y ∈ U ∧ (Opens.map (q a)).obj U ≤ W := by
  have hc : IsClosed ((q a) '' (W : Set (D a))ᶜ) :=
    (isProperMap_q a).isClosedMap _ W.isOpen.isClosed_compl
  refine ⟨⟨_, hc.isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨z, hz, hzy⟩
    exact hz (hW z hzy)
  · intro z hz
    by_contra h
    exact hz ⟨z, h, rfl⟩

/-- An open subset of the band whose preimage under `fibreEmb a y` is everything contains
`(q a)⁻¹ U` for an open `U ∋ y`. -/
theorem exists_preimage_q_le_of_fibreEmb (a y : ℝ) (W : Opens (D a))
    (hW : ⊤ ≤ (Opens.map (fibreEmb a y)).obj W) :
    ∃ U : Opens realLine, y ∈ U ∧ (Opens.map (q a)).obj U ≤ W :=
  exists_preimage_q_le a y W fun z hz => by
    obtain ⟨x, rfl⟩ := mem_range_fibreEmb.2 hz
    exact hW trivial

/-- A point of a band near which an open set contains a box. -/
private theorem exists_box_le {a : ℝ} (O : Opens (D a)) {z₀ : D a} (h : z₀ ∈ O) :
    ∃ ε > 0, ∀ z : D a, dist z.1.1 z₀.1.1 < ε → dist z.1.2 z₀.1.2 < ε → z ∈ O := by
  obtain ⟨V, hV, hVO⟩ := isOpen_induced_iff.mp O.isOpen
  have hz₀ : z₀.1 ∈ V := by
    have : z₀ ∈ (Subtype.val ⁻¹' V : Set (band a)) := by rw [hVO]; exact h
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV _ hz₀
  refine ⟨ε, hε, fun z h₁ h₂ => ?_⟩
  have : z ∈ (Subtype.val ⁻¹' V : Set (band a)) :=
    hball (by rw [Metric.mem_ball, Prod.dist_eq]; exact max_lt h₁ h₂)
  rw [hVO] at this
  exact this

variable (k)

/-- The open subset `{(x, y') | l < x < r}` of the band. -/
private abbrev pIoo {a : ℝ} (l r : ℝ) : Opens (D a) :=
  (Opens.map (p a)).obj ⟨Set.Ioo l r, isOpen_Ioo⟩

section surj

variable {a y : ℝ} (G : (D a).Sheaf (ModuleCat.{0} k))

/-- The inverse image of `G` on the parametrised fibre (local shorthand). -/
private abbrev fH (a y : ℝ) (G : (D a).Sheaf (ModuleCat.{0} k)) :
    (TopCat.of (Set.Icc (y - a) (y + a))).Sheaf (ModuleCat.{0} k) :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G

/-- The adjunction unit `G ⟶ (fibreEmb a y)_* (fibreEmb a y)⁻¹ G` (local shorthand). -/
private abbrev fη (a y : ℝ) (G : (D a).Sheaf (ModuleCat.{0} k)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (fibreEmb a y)).unit.app G).hom

local notation "ι" => fibreEmb a y
local notation "H" => fH k a y G
local notation "η" => fη k a y G

/-- The adjunction unit commutes with restriction. -/
private theorem unit_res {W W' : Opens (D a)} (h : W' ≤ W) (s : G.presheaf.obj (op W)) :
    (η).app (op W') (G.presheaf.map (homOfLE h).op s) =
      (H).presheaf.map ((Opens.map ι).map (homOfLE h)).op ((η).app (op W) s) :=
  NatTrans.naturality_apply (η) (homOfLE h).op s

/-- Restricting a representative of `t` near the fibre. -/
private theorem good_res {t : (H).presheaf.obj (op ⊤)} {W W' : Opens (D a)} (h : W' ≤ W)
    {s : G.presheaf.obj (op W)}
    (hs : (H).presheaf.map (homOfLE le_top).op t = (η).app (op W) s) :
    (H).presheaf.map (homOfLE le_top).op t = (η).app (op W') (G.presheaf.map (homOfLE h).op s) := by
  rw [unit_res, ← hs, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Every section of `(fibreEmb a y)⁻¹ G` over the fibre is represented near each point. -/
private theorem exists_good_local (t : (H).presheaf.obj (op ⊤))
    (x : TopCat.of (Set.Icc (y - a) (y + a))) :
    ∃ (W : Opens (D a)) (s : G.presheaf.obj (op W)),
      (H).presheaf.map (homOfLE le_top).op t = (η).app (op W) s ∧ x ∈ (Opens.map ι).obj W := by
  obtain ⟨W₀, hW₀, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf
    ((stalkPullbackSheafIso k ι G x).inv ((H).presheaf.germ ⊤ x trivial t))
  have h1 : (H).presheaf.germ ⊤ x trivial t =
      (H).presheaf.germ ((Opens.map ι).obj W₀) x hW₀ ((η).app _ s₀) := by
    rw [← stalkPullbackSheafIso_unit, hs₀, Iso.inv_hom_id_apply]
  obtain ⟨N, hxN, i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq (H).presheaf (U := ⊤)
    (V := (Opens.map ι).obj W₀) x trivial hW₀ t _ h1
  obtain ⟨δ, hδ, hδN⟩ := exists_openIoo_le hxN
  let W := W₀ ⊓ pIoo (x.1 - δ) (x.1 + δ)
  have hWN : (Opens.map ι).obj W ≤ N := fun z hz => hδN (mem_openIoo.2 hz.2)
  refine ⟨W, G.presheaf.map (homOfLE inf_le_left).op s₀, ?_, hW₀, ?_⟩
  · have e1 : (H).presheaf.map (homOfLE hWN).op ((H).presheaf.map i₁.op t) =
        (H).presheaf.map (homOfLE le_top).op t := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    have e2 : (H).presheaf.map (homOfLE hWN).op ((H).presheaf.map i₂.op ((η).app _ s₀)) =
        (η).app (op W) (G.presheaf.map (homOfLE inf_le_left).op s₀) := by
      exact (presheaf_map_map_apply _ hWN (leOfHom i₂) _).trans (unit_res k G _ s₀).symm
    exact e1.symm.trans ((congrArg _ he).trans e2)
  · change x.1 - δ < x.1 ∧ x.1 < x.1 + δ
    constructor <;> linarith

/-- **Sections over the fibre come from a neighbourhood (degree-0 tautness, surjectivity).** Every
section of `(fibreEmb a y)⁻¹ G` over `[y - a, y + a]` is the restriction of the image under the
adjunction unit of a section of `G` over an open neighbourhood `W` of the fibre. -/
theorem exists_unit_eq_fibreEmb
    (t : ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G).presheaf.obj (op ⊤)) :
    ∃ (W : Opens (D a)) (hW : ⊤ ≤ (Opens.map (fibreEmb a y)).obj W) (s : G.presheaf.obj (op W)),
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G).presheaf.map (homOfLE hW).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (fibreEmb a y)).unit.app
          G).hom.app (op W) s) = t := by
  rcases lt_or_ge (y + a) (y - a) with hlt | hle
  · -- The empty fibre: every section vanishes.
    refine ⟨⊤, fun _ _ => trivial, 0, ?_⟩
    exact TopCat.Presheaf.section_ext _ _ _ _ (fun x _ => absurd (x.2.1.trans x.2.2)
      (not_le.2 hlt))
  -- `A`: right ends `r` such that a representative covers the fibre points with `x < r`.
  let A : Set ℝ := {r | ∃ (W : Opens (D a)) (s : G.presheaf.obj (op W)),
    (H).presheaf.map (homOfLE le_top).op t = (η).app (op W) s ∧
      ∀ z : TopCat.of (Set.Icc (y - a) (y + a)), z.1 < r → z ∈ (Opens.map ι).obj W}
  suffices ∃ r ∈ A, y + a < r by
    obtain ⟨r, ⟨W, s, hs, hW⟩, hr⟩ := this
    have hW' : ⊤ ≤ (Opens.map ι).obj W := fun z _ => hW z (lt_of_le_of_lt z.2.2 hr)
    refine ⟨W, hW', s, ?_⟩
    rw [← hs, presheaf_map_map_apply, presheaf_map_eq _ _ (𝟙 _), CategoryTheory.Functor.map_id]
    rfl
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  -- A representative near the left end.
  obtain ⟨W₀, s₀, hs₀, hx₀⟩ := exists_good_local k G t ⟨y - a, le_rfl, hle⟩
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := exists_openIoo_le hx₀
  have hA₀ : y - a + δ₀ ∈ A := ⟨W₀, s₀, hs₀, fun z hz =>
    hδ₀W (mem_openIoo.2 ⟨by linarith [z.2.1], by simpa using hz⟩)⟩
  have hbdd : BddAbove A := ⟨y + a, hcon⟩
  set τ := sSup A with hτ
  have hτ₀ : y - a + δ₀ ≤ τ := le_csSup hbdd hA₀
  have hτd : τ ≤ y + a := csSup_le ⟨_, hA₀⟩ hcon
  -- A representative near `τ`.
  obtain ⟨W₂, s₂, hs₂, hx₂⟩ := exists_good_local k G t ⟨τ, by linarith, hτd⟩
  obtain ⟨δ, hδ, hδW₂⟩ := exists_openIoo_le hx₂
  set lo := max (τ - δ) (y - a) with hlo
  have hloτ : lo < τ := max_lt (by linarith) (by linarith)
  obtain ⟨r, ⟨W₁, s₁, hs₁, hW₁⟩, hlor⟩ := exists_lt_of_lt_csSup ⟨_, hA₀⟩ hloτ
  have hrτ : r ≤ τ := le_csSup hbdd ⟨W₁, s₁, hs₁, hW₁⟩
  have hlo₁ : τ - δ ≤ lo := le_max_left _ _
  have hlo₂ : y - a ≤ lo := le_max_right _ _
  set m := (lo + r) / 2 with hm
  have hm₁ : lo < m := by linarith
  have hm₂ : m < r := by linarith
  let km : TopCat.of (Set.Icc (y - a) (y + a)) := ⟨m, by linarith, by linarith⟩
  have hkm₁ : km ∈ (Opens.map ι).obj W₁ := hW₁ km hm₂
  have hkm₂ : km ∈ (Opens.map ι).obj W₂ :=
    hδW₂ (mem_openIoo.2 ⟨by change τ - δ < m; linarith, by change m < τ + δ; linarith⟩)
  -- The two representatives agree near the fibre over `W₁ ⊓ W₂`.
  let d₀ := G.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op s₁ -
    G.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op s₂
  have hd₀ : (H).presheaf.map (homOfLE (le_refl ((Opens.map ι).obj (W₁ ⊓ W₂)))).op
      ((η).app _ d₀) = 0 := by
    have : (η).app _ d₀ = 0 := by
      simp only [d₀, map_sub]
      rw [← good_res k G inf_le_left hs₁, ← good_res k G inf_le_right hs₂]
      exact sub_self _
    rw [this]
    exact map_zero _
  obtain ⟨O, hO, hNO, hOs⟩ := exists_le_eq_zero_of_pullback_eq_zero ι G d₀ le_rfl hd₀
  obtain ⟨ε, hε, hεO⟩ := exists_box_le O (hNO ⟨hkm₁, hkm₂⟩)
  -- Shrink: left of `m` keep `s₁`, right of `m` keep `s₂`, near `(m, y)` they agree.
  let B : Opens (D a) := pIoo (m - ε) (m + ε) ⊓ (Opens.map (q a)).obj ⟨Set.Ioo (y - ε) (y + ε),
    isOpen_Ioo⟩
  have hBO : B ≤ O := fun z hz => by
    obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := hz
    change m - ε < z.1.1 at h₁
    change z.1.1 < m + ε at h₂
    change y - ε < z.1.2 at h₃
    change z.1.2 < y + ε at h₄
    refine hεO z ?_ ?_
    · change dist z.1.1 m < ε
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    · change dist z.1.2 y < ε
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
  let Pl : Opens (D a) := (Opens.map (p a)).obj ⟨Set.Iio m, isOpen_Iio⟩
  let Pg : Opens (D a) := (Opens.map (p a)).obj ⟨Set.Ioi m, isOpen_Ioi⟩
  let W₁' := W₁ ⊓ (Pl ⊔ B)
  let W₂' := W₂ ⊓ (Pg ⊔ B)
  have hint : W₁' ⊓ W₂' ≤ O := by
    rintro z ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩
    rcases Opens.mem_sup.1 h₁ with h₁ | h₁
    · rcases Opens.mem_sup.1 h₂ with h₂ | h₂
      · exact absurd (lt_trans (show z.1.1 < m from h₁) (show m < z.1.1 from h₂)) (lt_irrefl _)
      · exact hBO h₂
    · exact hBO h₁
  -- Glue `s₁` left of `m` with `s₂` right of `m`.
  let σ₁ := G.presheaf.map (homOfLE (inf_le_left : W₁' ≤ W₁)).op s₁
  let σ₂ := G.presheaf.map (homOfLE (inf_le_left : W₂' ≤ W₂)).op s₂
  have hagree : G.presheaf.map (homOfLE (inf_le_left : W₁' ⊓ W₂' ≤ W₁')).op σ₁ =
      G.presheaf.map (homOfLE (inf_le_right : W₁' ⊓ W₂' ≤ W₂')).op σ₂ := by
    have hle : W₁' ⊓ W₂' ≤ W₁ ⊓ W₂ := inf_le_inf inf_le_left inf_le_left
    have h0 : G.presheaf.map (homOfLE hle).op d₀ = 0 := by
      rw [← presheaf_map_map_apply _ hint hO, hOs, map_zero]
    simp only [d₀, map_sub] at h0
    rw [presheaf_map_map_apply, presheaf_map_map_apply] at h0
    simp only [σ₁, σ₂]
    rw [presheaf_map_map_apply, presheaf_map_map_apply]
    exact sub_eq_zero.1 h0
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_glue₂ G σ₁ σ₂ hagree
  have hgood : (H).presheaf.map (homOfLE le_top).op t = (η).app (op (W₁' ⊔ W₂')) σ := by
    refine TopCat.Sheaf.eq_of_locally_eq₂ (H)
      (homOfLE (leOfHom ((Opens.map ι).map (homOfLE (le_sup_left : W₁' ≤ W₁' ⊔ W₂')))))
      (homOfLE (leOfHom ((Opens.map ι).map (homOfLE (le_sup_right : W₂' ≤ W₁' ⊔ W₂')))))
      (fun z hz => Opens.mem_sup.2 (Opens.mem_sup.1 hz)) _ _ ?_ ?_
    · exact (presheaf_map_map_apply _ _ _ _).trans ((good_res k G inf_le_left hs₁).trans
        ((congrArg _ hσ₁.symm).trans (unit_res k G le_sup_left σ)))
    · exact (presheaf_map_map_apply _ _ _ _).trans ((good_res k G inf_le_left hs₂).trans
        ((congrArg _ hσ₂.symm).trans (unit_res k G le_sup_right σ)))
  have hcov : ∀ z : TopCat.of (Set.Icc (y - a) (y + a)), z.1 < τ + δ →
      z ∈ (Opens.map ι).obj (W₁' ⊔ W₂') := by
    intro z hz
    rcases lt_trichotomy z.1 m with hzm | hzm | hzm
    · exact Opens.mem_sup.2 (Or.inl ⟨hW₁ z (hzm.trans hm₂), Opens.mem_sup.2 (Or.inl hzm)⟩)
    · refine Opens.mem_sup.2 (Or.inl ⟨hW₁ z (hzm ▸ hm₂), Opens.mem_sup.2 (Or.inr ?_)⟩)
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · change m - ε < z.1
        linarith
      · change z.1 < m + ε
        linarith
      · change y - ε < y
        linarith
      · change y < y + ε
        linarith
    · refine Opens.mem_sup.2 (Or.inr ⟨hδW₂ (mem_openIoo.2 ⟨?_, ?_⟩), Opens.mem_sup.2 (Or.inl hzm)⟩)
      · change τ - δ < z.1
        linarith
      · change z.1 < τ + δ
        exact hz
  have := le_csSup hbdd (⟨W₁' ⊔ W₂', σ, hgood, hcov⟩ : τ + δ ∈ A)
  linarith

end surj

section stalk

variable (a y : ℝ)

/-- **The stalk comparison.** For a sheaf `G` of `k`-modules on the band `D a`, the morphism
`(ptAt y)⁻¹ (q a)_* G ⟶ Γ([y - a, y + a]; (fibreEmb a y)⁻¹ G)` of sheaves on the point adjoint to
`(q a)_*` applied to the unit `G ⟶ (fibreEmb a y)_* (fibreEmb a y)⁻¹ G`; the composite
`fibreEmb a y ≫ q a` is `toPt _ ≫ ptAt y` (`fibreEmb_comp_q`). -/
def stalkComparison (G : (D a).Sheaf (ModuleCat.{0} k)) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G) ⟶
      (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (ptAt y)).homEquiv _ _).symm
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (fibreEmb a y)).unit.app G))

/-- **The stalk comparison on sections.** For an open `U ∋ y` and a section `s` of `G` over
`(q a)⁻¹ U`, the comparison sends the restriction to the point of the unit image of `s` to the
restriction to `[y - a, y + a]` of the unit image of `s` in `(fibreEmb a y)⁻¹ G`. -/
theorem stalkComparison_app_top (G : (D a).Sheaf (ModuleCat.{0} k)) {U : Opens realLine}
    (hU : ⊤ ≤ (Opens.map (ptAt y)).obj U)
    (hU' : ⊤ ≤ (Opens.map (fibreEmb a y)).obj ((Opens.map (q a)).obj U))
    (s : G.presheaf.obj (op ((Opens.map (q a)).obj U))) :
    (stalkComparison k a y G).hom.app (op ⊤)
        (((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj
            ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G)).presheaf.map
          (homOfLE hU).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (ptAt y)).unit.app
            ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G)).hom.app (op U) s)) =
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G).presheaf.map
        (homOfLE hU').op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (fibreEmb a y)).unit.app
          G).hom.app (op ((Opens.map (q a)).obj U)) s) := by
  have hφ : (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (ptAt y)).unit.app
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (ptAt y)).map (stalkComparison k a y G) =
      (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (fibreEmb a y)).unit.app
          G) := by
    exact ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k)
      (ptAt y)).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have h1 := congrArg (fun φ => φ.hom.app (op U) s) hφ
  exact (NatTrans.naturality_apply _ _ _).trans (congrArg _ h1)

/-- The stalk comparison is natural in `G`. -/
theorem stalkComparison_naturality {G G' : (D a).Sheaf (ModuleCat.{0} k)} (φ : G ⟶ G') :
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).map
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).map φ) ≫ stalkComparison k a y G' =
      stalkComparison k a y G ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (toPt _)).map
          ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).map φ) := by
  refine (Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans
    (Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm _ _ _))
  congr 1
  exact ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).map_comp _ _).symm.trans
    ((congrArg (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k)
        (fibreEmb a y)).unit.naturality φ)).trans
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).map_comp _ _))

/-- **The stalk comparison is an isomorphism** (degree-0 tautness of the fibre). -/
instance isIso_stalkComparison (G : (D a).Sheaf (ModuleCat.{0} k)) :
    IsIso (stalkComparison k a y G) := by
  let M := (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G
  let P := (TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj M
  let ηp := ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (ptAt y)).unit.app M).hom
  apply isIso_of_bijective_app_top
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨U, hU, s, rfl⟩ := exists_unit_eq_of_pt (ptAt y) M x
    have hyU : y ∈ U := hU (show (PUnit.unit : pt) ∈ (⊤ : Opens pt) from trivial)
    have hU' : ⊤ ≤ (Opens.map (fibreEmb a y)).obj ((Opens.map (q a)).obj U) := fun _ _ => hyU
    have hx' := (stalkComparison_app_top k a y G hU hU' s).symm.trans hx
    obtain ⟨O, hO, hNO, hOs⟩ := exists_le_eq_zero_of_pullback_eq_zero _ G s hU' hx'
    obtain ⟨U', hyU', hU'O⟩ := exists_preimage_q_le_of_fibreEmb a y O hNO
    have hle : (Opens.map (q a)).obj (U ⊓ U') ≤ O := fun z hz => hU'O hz.2
    have hs0 : M.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op s = 0 :=
      (presheaf_map_map_apply G.presheaf hle hO s).symm.trans ((congrArg _ hOs).trans (map_zero _))
    have hU'' : ⊤ ≤ (Opens.map (ptAt y)).obj (U ⊓ U') := fun _ _ => ⟨hyU, hyU'⟩
    have e := (NatTrans.naturality_apply ηp (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op s).symm.trans
      ((congrArg (ηp.app _) hs0).trans (map_zero _))
    exact (presheaf_map_map_apply P.presheaf hU'' (fun _ hz => hz.1) _).symm.trans
      ((congrArg _ e).trans (map_zero _))
  · intro t
    obtain ⟨W, hW, s, hs⟩ := exists_unit_eq_fibreEmb k G t
    obtain ⟨U, hyU, hUW⟩ := exists_preimage_q_le_of_fibreEmb a y W hW
    have hU : ⊤ ≤ (Opens.map (ptAt y)).obj U := fun _ _ => hyU
    have hU' : ⊤ ≤ (Opens.map (fibreEmb a y)).obj ((Opens.map (q a)).obj U) := fun _ _ => hyU
    refine ⟨P.presheaf.map (homOfLE hU).op (ηp.app (op U) (G.presheaf.map (homOfLE hUW).op s)),
      ?_⟩
    exact (stalkComparison_app_top k a y G hU hU' _).trans ((congrArg _ (unit_res k G hUW s)).trans
      ((presheaf_map_map_apply _ _ _ _).trans hs))

/-- **The stalk of `(q a)_* G` at `y` is the sections of `G` over the fibre.** The stalk
comparison as a natural isomorphism `(q a)_* ⋙ (ptAt y)⁻¹ ≅ (fibreEmb a y)⁻¹ ⋙ Γ([y - a, y + a]; -)`
of functors from sheaves of `k`-modules on `D a` to sheaves on the point. -/
def stalkIso :
    TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y) ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y) ⋙
        TopCat.Sheaf.pushforward (ModuleCat.{0} k) (toPt (TopCat.of (Set.Icc (y - a) (y + a)))) :=
  NatIso.ofComponents (fun G => asIso (stalkComparison k a y G))
    (fun φ => stalkComparison_naturality k a y φ)

/-- The components of `stalkIso` are the stalk comparisons. -/
@[simp]
theorem stalkIso_hom_app (G : (D a).Sheaf (ModuleCat.{0} k)) :
    (stalkIso k a y).hom.app G = stalkComparison k a y G := rfl

/-- **The stalk of `(q a)_* G` at `y` as sections over the fibre.** The stalk at `y` of the direct
image `(q a)_* G` is the module of sections of `(fibreEmb a y)⁻¹ G` over `[y - a, y + a]`
(`stalkPullbackSheafIso`, `germ_top_bijective` and `stalkComparison` on global sections). -/
def stalkSectionsIso (G : (D a).Sheaf (ModuleCat.{0} k)) :
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G).presheaf.stalk y ≅
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G).presheaf.obj (op ⊤) :=
  have := (ConcreteCategory.isIso_iff_bijective _).2 (germ_top_bijective
    ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G)) PUnit.unit)
  stalkPullbackSheafIso k (ptAt y) _ PUnit.unit ≪≫
    (asIso (((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G)).presheaf.germ ⊤ PUnit.unit
        trivial)).symm ≪≫
    ((TopCat.Sheaf.forget (ModuleCat.{0} k) pt).mapIso (asIso (stalkComparison k a y G))).app
      (op ⊤)

end stalk

section formula

variable (a y : ℝ) [HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory ((TopCat.of (Set.Icc (y - a) (y + a))).Sheaf (ModuleCat.{0} k))]

/-- The stalk formula on a bounded below complex of injective sheaves: `q_* I` computes
`R(q a)_* I`, `(ptAt y)⁻¹` is exact, `stalkIso` identifies the terms, and the inverse images
`(fibreEmb a y)⁻¹ Iⁿ` are germ-surjective, so they compute `RΓ([y - a, y + a]; -)`. -/
private def stalkFormulaInj (I : CochainComplex.Plus ((D a).Sheaf (ModuleCat.{0} k)))
    [∀ n, Injective (I.obj.X n)] :
    (pullbackPlus k (ptAt y)).obj ((pushforwardPlus k (q a)).obj (DerivedCategory.Plus.Q.obj I)) ≅
      (pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).obj
        ((pullbackPlus k (fibreEmb a y)).obj (DerivedCategory.Plus.Q.obj I)) :=
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)) I
  have := isIso_rightDerivedFunctorPlusUnit_app_toPt_Icc_of_germSurjective
    ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).mapCochainComplexPlus.obj I)
    (fun n => @germSurjective_pullback_of_isFlasque k _ _ _ (fibreEmb a y) (I.obj.X n)
      (isFlasque_of_injective k _))
  (pullbackPlus k (ptAt y)).mapIso
      (asIso ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).rightDerivedFunctorPlusUnit.app
        I)).symm ≪≫
    (asIso ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).rightDerivedFunctorPlusUnit.app
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).mapCochainComplexPlus.obj I))).symm ≪≫
    DerivedCategory.Plus.Q.mapIso ((mapCochainComplexPlusCompIso (stalkIso k a y)).app I ≪≫
      (mapCochainComplexPlusCompIso (Iso.refl (TopCat.Sheaf.pullback (ModuleCat.{0} k)
        (fibreEmb a y) ⋙ TopCat.Sheaf.pushforward (ModuleCat.{0} k)
          (toPt (TopCat.of (Set.Icc (y - a) (y + a))))))).symm.app I) ≪≫
    asIso ((TopCat.Sheaf.pushforward (ModuleCat.{0} k)
      (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).rightDerivedFunctorPlusUnit.app
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).mapCochainComplexPlus.obj I)) ≪≫
    (pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).mapIso
      (asIso ((TopCat.Sheaf.pullback (ModuleCat.{0} k)
        (fibreEmb a y)).rightDerivedFunctorPlusUnit.app I))

/-- **The stalk formula for the band projections exists.** For `F ∈ D⁺(Sh(D a))`, the stalk at
`y` of `R(q a)_* F` (its inverse image `(ptAt y)⁻¹` to the point) is isomorphic in `D⁺(Sh pt)` to
`RΓ` of the fibre `(q a)⁻¹ {y} ≅ [y - a, y + a]` with coefficients in `(fibreEmb a y)⁻¹ F`; in
particular so are their `Hⁱ`. -/
theorem nonempty_stalkFormula (F : DerivedCategory.Plus ((D a).Sheaf (ModuleCat.{0} k))) :
    Nonempty ((pullbackPlus k (ptAt y)).obj ((pushforwardPlus k (q a)).obj F) ≅
      (pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).obj
        ((pullbackPlus k (fibreEmb a y)).obj F)) := by
  obtain ⟨n, hn⟩ := F.property
  have : F.IsGE n := (F.isGE_ι_obj_iff n).1 hn
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso F n
  have (m : ℤ) : Injective
      (((InjectiveObject.ι ((D a).Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L).obj.X m) :=
    (L.obj.X m).property
  exact ⟨(pullbackPlus k (ptAt y)).mapIso ((pushforwardPlus k (q a)).mapIso e.symm) ≪≫
    stalkFormulaInj k a y _ ≪≫
    (pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).mapIso
      ((pullbackPlus k (fibreEmb a y)).mapIso e)⟩

/-- **The stalk formula for the band projections, on cohomology.** For `F ∈ D⁺(Sh(D a))` and
every degree `i`, `Hⁱ` of the stalk at `y` of `R(q a)_* F` (read through `(ptAt y)⁻¹`) is
isomorphic to `Hⁱ((q a)⁻¹ {y}; (fibreEmb a y)⁻¹ F)`, the fibre parametrised by
`[y - a, y + a]`. -/
theorem nonempty_stalkFormula_homology
    (F : DerivedCategory.Plus ((D a).Sheaf (ModuleCat.{0} k))) (i : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((pullbackPlus k (ptAt y)).obj ((pushforwardPlus k (q a)).obj F)) ≅
      (DerivedCategory.Plus.homologyFunctor _ i).obj
        ((pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).obj
          ((pullbackPlus k (fibreEmb a y)).obj F))) :=
  ⟨(DerivedCategory.Plus.homologyFunctor _ i).mapIso (nonempty_stalkFormula k a y F).some⟩

/-- **Stalks of `R(q a)_*` of a sheaf vanish above degree one.** For a sheaf `G` of `k`-modules on
`D a` placed in degree `0`, `Hⁱ` of the stalk at `y` of `R(q a)_* G` vanishes for `2 ≤ i`. -/
theorem isZero_H_stalk_pushforwardPlus_q (G : (D a).Sheaf (ModuleCat.{0} k)) {i : ℤ}
    (hi : 2 ≤ i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((pullbackPlus k (ptAt y)).obj ((pushforwardPlus k (q a)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) :=
  (isZero_H_Icc ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G) hi).of_iso
    ((nonempty_stalkFormula_homology k a y _ i).some ≪≫
      (DerivedCategory.Plus.homologyFunctor _ i).mapIso
      ((pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).mapIso
        (rightDerivedFunctorPlusSingleIso (TopCat.Sheaf.pullback (ModuleCat.{0} k)
          (fibreEmb a y)) 0 G)))

end formula

end BandConvolution

end TDA.Sheaf
