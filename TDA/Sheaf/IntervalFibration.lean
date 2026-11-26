import TDA.Sheaf.IntervalAcyclic
import TDA.Sheaf.PointDetection

/-!
# Base change on the fibres of interval fibrations

Let `k` be a ring and `π : X ⟶ Y` a continuous map.

* A **fibre coordinate** `c : FibreCoordinate π` is a continuous `c.t : X → ℝ` such that
  `z ↦ (π z, c.t z)` is inducing, for a closed map `π`. A **fibre parametrisation** of `π` at `y`
  in this coordinate, `c.IsFibreParam y ε`, is a map `ε : [u, v] ⟶ X` with
  `ε ≫ π = toPt _ ≫ ptOf y`, `c.t ∘ ε = id` and `π⁻¹ {y} ⊆ range ε`, so that the range of `ε` is
  the fibre `π⁻¹ {y}` (`mem_range_iff`). The interval may be empty (`v < u`, an empty fibre) or a
  point (`u = v`).
* An **interval fibration** `IntervalFibration π` is a fibre coordinate together with fibre
  parametrisations `e y : [lo y, hi y] ⟶ X` at every point `y : Y` (`e_comp`, `t_e`,
  `mem_range`).

Degree-0 tautness of the fibres:

* `exists_le_eq_zero_of_pullback_eq_zero` (any continuous `i`): a section of `G` whose image in
  `i⁻¹ G` vanishes over an open `N` vanishes over an open neighbourhood of `i(N)`.
* `exists_unit_eq_of_pt`: global sections of an inverse image to the point are restrictions of
  unit images of sections near the image point.
* `exists_preimage_le_of_isClosedMap`: for a closed map, tubes `π⁻¹ U`, `U ∋ y` open, are cofinal
  among the open neighbourhoods of the fibre `π⁻¹ {y}`.
* `FibreCoordinate.IsFibreParam.exists_unit_eq`: every section of `ε⁻¹ G` over the fibre comes
  from a section of `G` over an open neighbourhood of the fibre. Local representatives are merged
  from left to right along `[u, v]` (a supremum argument); on the overlap two representatives
  agree near the fibre, hence on a set `π⁻¹ V ∩ c.t⁻¹ (m - ε, m + ε)` around a point of the
  fibre, and the two opens are cut at that point.

The stalk and the base change:

* `FibreCoordinate.IsFibreParam.isIso_baseChangeSheaf_app`: the underived base change of the
  fibre square, `(ptOf y)⁻¹ π_* G ⟶ Γ([u, v]; ε⁻¹ G)`, is an isomorphism of sheaves on the
  point. It is described on sections by `baseChangeSheaf_app_hom_app_top`.
* `FibreCoordinate.IsFibreParam.isIso_baseChange`: **proper base change on the fibres.** The
  derived base-change morphism `Rπ_* ⋙ (ptOf y)⁻¹ ⟶ ε⁻¹ ⋙ RΓ([u, v]; -)` is an isomorphism. On a
  bounded below injective model `I`, `baseChange_app_Q` identifies it with `Q` of the termwise
  underived base change, between the comparisons for `π_*` (injective terms) and for
  `Γ([u, v]; -)` (the germ-surjective terms `ε⁻¹ Iⁿ`).
* `IntervalFibration.isIso_baseChange`, `IntervalFibration.stalkFormula`: the same at every point
  of an interval fibration; the canonical stalk formula
  `Rπ_* ⋙ (ptOf y)⁻¹ ≅ (e y)⁻¹ ⋙ RΓ([lo y, hi y]; -)`. For a sheaf placed in degree `0`, the
  stalks of its derived direct image vanish in degrees `i ≥ 2`
  (`IsFibreParam.isZero_H_stalk_pushforwardPlus`,
  `IntervalFibration.isZero_H_stalk_pushforwardPlus`).
* `isIso_baseChange_of_isFibreParam`: the fibrewise criterion (`isIso_baseChange_of_fibres`)
  for a square `w : g' ≫ f = f' ≫ g` with `f'` an interval fibration whose fibre parametrisations
  `e z`, followed by `g'`, parametrise the fibres of `f` at `g z` in a fibre coordinate of `f`.
* `IntervalFibration.isIso_derivedUnit`: for an interval fibration with nonempty fibres, the
  derived unit `𝟭 ⟶ π⁻¹ ⋙ Rπ_*` is an isomorphism. At each point, `derivedUnit_baseChange` relates
  it to the derived unit of the fibre interval (`isIso_derivedUnit_Icc`) through the invertible
  base change of the fibre square; detection at points concludes.

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

/-- **Tubes around a fibre of a closed map are cofinal.** For a closed map `π : X ⟶ Y`, every
open subset of `X` containing the fibre `π⁻¹ {y}` contains `π⁻¹ U` for an open `U ∋ y`. -/
theorem exists_preimage_le_of_isClosedMap {X Y : TopCat.{0}} {π : X ⟶ Y} (hπ : IsClosedMap π)
    (y : Y) (W : Opens X) (hW : ∀ z : X, π z = y → z ∈ W) :
    ∃ U : Opens Y, y ∈ U ∧ (Opens.map π).obj U ≤ W := by
  have hc : IsClosed (π '' (W : Set X)ᶜ) := hπ _ W.isOpen.isClosed_compl
  refine ⟨⟨_, hc.isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨z, hz, hzy⟩
    exact hz (hW z hzy)
  · intro z hz
    by_contra h
    exact hz ⟨z, h, rfl⟩

end taut

/-- **A fibre coordinate** for a continuous map `π : X ⟶ Y`: a continuous function `t : X → ℝ`
such that `z ↦ (π z, t z)` is inducing, for a closed map `π`. -/
structure FibreCoordinate {X Y : TopCat.{0}} (π : X ⟶ Y) where
  /-- The coordinate along the fibres. -/
  t : C(X, ℝ)
  /-- The topology of `X` is induced by `z ↦ (π z, t z)`. -/
  isInducing : Topology.IsInducing fun z => (π z, t z)
  /-- The map `π` is closed. -/
  isClosedMap : IsClosedMap π

namespace FibreCoordinate

variable {X Y : TopCat.{0}} {π : X ⟶ Y} (c : FibreCoordinate π)

/-- **A fibre parametrisation** of `π` at `y` in the coordinate `c.t`: a map `ε : [u, v] ⟶ X`
into the fibre `π⁻¹ {y}` (the square `ε ≫ π = toPt _ ≫ ptOf y`), with `c.t (ε x) = x` and whose
range contains the fibre. The interval may be empty or a point. -/
structure IsFibreParam (y : Y) {u v : ℝ} (ε : TopCat.of (Set.Icc u v) ⟶ X) : Prop where
  /-- The fibre square. -/
  comp_eq : ε ≫ π = toPt _ ≫ ptOf y
  /-- `ε` is a section of the coordinate. -/
  t_apply : ∀ x : TopCat.of (Set.Icc u v), c.t (ε x) = x.1
  /-- The fibre lies in the range of `ε`. -/
  mem_range : ∀ z : X, π z = y → z ∈ Set.range ε

/-- The open subset `c.t⁻¹ s` of `X`, for an open `s ⊆ ℝ`. -/
private def tOpen (s : Set ℝ) (hs : IsOpen s) : Opens X :=
  ⟨c.t ⁻¹' s, hs.preimage c.t.continuous⟩

/-- **Product neighbourhoods.** An open subset `O ∋ z₀` of `X` contains
`π⁻¹ V ∩ c.t⁻¹ (c.t z₀ - ε, c.t z₀ + ε)` for an open `V ∋ π z₀` and some `ε > 0`. -/
private theorem exists_nhd_le (O : Opens X) {z₀ : X} (h : z₀ ∈ O) :
    ∃ V : Opens Y, π z₀ ∈ V ∧ ∃ ε > 0, ∀ z : X, π z ∈ V → dist (c.t z) (c.t z₀) < ε → z ∈ O := by
  obtain ⟨U, hU, hUO⟩ := c.isInducing.isOpen_iff.1 O.isOpen
  have hz₀ : (π z₀, c.t z₀) ∈ U := by
    have : z₀ ∈ ((fun z => (π z, c.t z)) ⁻¹' U) := by rw [hUO]; exact h
    exact this
  obtain ⟨V, I, hV, hI, hzV, hzI, hVI⟩ := isOpen_prod_iff.1 hU _ _ hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI _ hzI
  refine ⟨⟨V, hV⟩, hzV, ε, hε, fun z hz hd => ?_⟩
  have : z ∈ ((fun z => (π z, c.t z)) ⁻¹' U) := hVI ⟨hz, hball hd⟩
  rw [hUO] at this
  exact this

variable {c} {y : Y} {u v : ℝ} {ε : TopCat.of (Set.Icc u v) ⟶ X}

namespace IsFibreParam

variable (hε : c.IsFibreParam y ε)
include hε

/-- A fibre parametrisation lands in the fibre: `π (ε x) = y`. -/
theorem apply_eq (x : TopCat.of (Set.Icc u v)) : π (ε x) = y :=
  ConcreteCategory.congr_hom hε.comp_eq x

/-- The range of a fibre parametrisation is the fibre. -/
theorem mem_range_iff {z : X} : z ∈ Set.range ε ↔ π z = y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact hε.apply_eq x
  · exact hε.mem_range z

/-- Membership of the preimage under `ε` of `c.t⁻¹ s`. -/
private theorem mem_tOpen (s : Set ℝ) (hs : IsOpen s) {x : TopCat.of (Set.Icc u v)} :
    x ∈ (Opens.map ε).obj (c.tOpen s hs) ↔ x.1 ∈ s := by
  change c.t (ε x) ∈ s ↔ _
  rw [hε.t_apply]

/-- An open subset of `X` whose preimage under the fibre parametrisation is everything contains
`π⁻¹ U` for an open `U ∋ y`. -/
theorem exists_preimage_le (W : Opens X) (hW : ⊤ ≤ (Opens.map ε).obj W) :
    ∃ U : Opens Y, y ∈ U ∧ (Opens.map π).obj U ≤ W :=
  exists_preimage_le_of_isClosedMap c.isClosedMap y W fun z hz => by
    obtain ⟨x, rfl⟩ := hε.mem_range z hz
    exact hW trivial

omit hε in
variable (k) in
/-- The inverse image of `G` on the parametrised fibre (local shorthand). -/
private abbrev fH (ε : TopCat.of (Set.Icc u v) ⟶ X) (G : X.Sheaf (ModuleCat.{0} k)) :
    (TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k) :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} k) ε).obj G

omit hε in
variable (k) in
/-- The adjunction unit `G ⟶ ε_* ε⁻¹ G` (local shorthand). -/
private abbrev fη (ε : TopCat.of (Set.Icc u v) ⟶ X) (G : X.Sheaf (ModuleCat.{0} k)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) ε).unit.app G).hom

omit hε

variable (G : X.Sheaf (ModuleCat.{0} k))

local notation "H" => fH k ε G
local notation "η" => fη k ε G

/-- The adjunction unit commutes with restriction. -/
private theorem unit_res {W W' : Opens X} (h : W' ≤ W) (s : G.presheaf.obj (op W)) :
    (η).app (op W') (G.presheaf.map (homOfLE h).op s) =
      (H).presheaf.map ((Opens.map ε).map (homOfLE h)).op ((η).app (op W) s) :=
  NatTrans.naturality_apply (η) (homOfLE h).op s

/-- Restricting a representative of `t` near the fibre. -/
private theorem good_res {t : (H).presheaf.obj (op ⊤)} {W W' : Opens X} (h : W' ≤ W)
    {s : G.presheaf.obj (op W)}
    (hs : (H).presheaf.map (homOfLE le_top).op t = (η).app (op W) s) :
    (H).presheaf.map (homOfLE le_top).op t =
      (η).app (op W') (G.presheaf.map (homOfLE h).op s) := by
  rw [unit_res, ← hs, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

include hε in
/-- Every section of `ε⁻¹ G` over the fibre is represented near each point. -/
private theorem exists_good_local (t : (H).presheaf.obj (op ⊤))
    (x : TopCat.of (Set.Icc u v)) :
    ∃ (W : Opens X) (s : G.presheaf.obj (op W)),
      (H).presheaf.map (homOfLE le_top).op t = (η).app (op W) s ∧
        x ∈ (Opens.map ε).obj W := by
  obtain ⟨W₀, hW₀, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf
    ((stalkPullbackSheafIso k ε G x).inv ((H).presheaf.germ ⊤ x trivial t))
  have h1 : (H).presheaf.germ ⊤ x trivial t =
      (H).presheaf.germ ((Opens.map ε).obj W₀) x hW₀ ((η).app _ s₀) := by
    rw [← stalkPullbackSheafIso_unit, hs₀, Iso.inv_hom_id_apply]
  obtain ⟨N, hxN, i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq (H).presheaf (U := ⊤)
    (V := (Opens.map ε).obj W₀) x trivial hW₀ t _ h1
  obtain ⟨δ, hδ, hδN⟩ := exists_openIoo_le hxN
  let W := W₀ ⊓ c.tOpen (Set.Ioo (x.1 - δ) (x.1 + δ)) isOpen_Ioo
  have hWN : (Opens.map ε).obj W ≤ N := fun z hz =>
    hδN (mem_openIoo.2 ((hε.mem_tOpen (Set.Ioo (x.1 - δ) (x.1 + δ)) isOpen_Ioo).1 hz.2))
  refine ⟨W, G.presheaf.map (homOfLE inf_le_left).op s₀, ?_, ⟨hW₀, ?_⟩⟩
  · have e1 : (H).presheaf.map (homOfLE hWN).op ((H).presheaf.map i₁.op t) =
        (H).presheaf.map (homOfLE le_top).op t := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    have e2 : (H).presheaf.map (homOfLE hWN).op ((H).presheaf.map i₂.op ((η).app _ s₀)) =
        (η).app (op W) (G.presheaf.map (homOfLE inf_le_left).op s₀) :=
      (presheaf_map_map_apply _ hWN (leOfHom i₂) _).trans (unit_res G _ s₀).symm
    exact e1.symm.trans ((congrArg _ he).trans e2)
  · exact (hε.mem_tOpen (Set.Ioo (x.1 - δ) (x.1 + δ)) isOpen_Ioo).2
      ⟨by linarith, by linarith⟩

include hε in
/-- **Sections over the fibre come from a neighbourhood (degree-0 tautness, surjectivity).** Every
section of `ε⁻¹ G` over `[u, v]` is the restriction of the image under the adjunction unit of a
section of `G` over an open neighbourhood `W` of the fibre. -/
theorem exists_unit_eq
    (t : ((TopCat.Sheaf.pullback (ModuleCat.{0} k) ε).obj G).presheaf.obj (op ⊤)) :
    ∃ (W : Opens X) (hW : ⊤ ≤ (Opens.map ε).obj W) (s : G.presheaf.obj (op W)),
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) ε).obj G).presheaf.map (homOfLE hW).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) ε).unit.app
          G).hom.app (op W) s) = t := by
  rcases lt_or_ge v u with hlt | hle
  · -- The empty fibre: every section vanishes.
    refine ⟨⊤, fun _ _ => trivial, 0, ?_⟩
    exact TopCat.Presheaf.section_ext _ _ _ _ (fun x _ => absurd (x.2.1.trans x.2.2)
      (not_le.2 hlt))
  -- `A`: right ends `r` such that a representative covers the fibre points with `x < r`.
  let A : Set ℝ := {r | ∃ (W : Opens X) (s : G.presheaf.obj (op W)),
    (H).presheaf.map (homOfLE le_top).op t = (η).app (op W) s ∧
      ∀ z : TopCat.of (Set.Icc u v), z.1 < r → z ∈ (Opens.map ε).obj W}
  suffices ∃ r ∈ A, v < r by
    obtain ⟨r, ⟨W, s, hs, hW⟩, hr⟩ := this
    have hW' : ⊤ ≤ (Opens.map ε).obj W := fun z _ => hW z (lt_of_le_of_lt z.2.2 hr)
    refine ⟨W, hW', s, ?_⟩
    rw [← hs, presheaf_map_map_apply, presheaf_map_eq _ _ (𝟙 _), CategoryTheory.Functor.map_id]
    rfl
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  -- A representative near the left end.
  obtain ⟨W₀, s₀, hs₀, hx₀⟩ := exists_good_local hε G t ⟨u, le_rfl, hle⟩
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := exists_openIoo_le hx₀
  have hA₀ : u + δ₀ ∈ A := ⟨W₀, s₀, hs₀, fun z hz =>
    hδ₀W (mem_openIoo.2 ⟨by linarith [z.2.1], by simpa using hz⟩)⟩
  have hbdd : BddAbove A := ⟨v, hcon⟩
  set τ := sSup A with hτ
  have hτ₀ : u + δ₀ ≤ τ := le_csSup hbdd hA₀
  have hτd : τ ≤ v := csSup_le ⟨_, hA₀⟩ hcon
  -- A representative near `τ`.
  obtain ⟨W₂, s₂, hs₂, hx₂⟩ := exists_good_local hε G t ⟨τ, by linarith, hτd⟩
  obtain ⟨δ, hδ, hδW₂⟩ := exists_openIoo_le hx₂
  set l₀ := max (τ - δ) u with hl₀
  have hl₀τ : l₀ < τ := max_lt (by linarith) (by linarith)
  obtain ⟨r, ⟨W₁, s₁, hs₁, hW₁⟩, hl₀r⟩ := exists_lt_of_lt_csSup ⟨_, hA₀⟩ hl₀τ
  have hrτ : r ≤ τ := le_csSup hbdd ⟨W₁, s₁, hs₁, hW₁⟩
  have hl₀₁ : τ - δ ≤ l₀ := le_max_left _ _
  have hl₀₂ : u ≤ l₀ := le_max_right _ _
  set m := (l₀ + r) / 2 with hm
  have hm₁ : l₀ < m := by linarith
  have hm₂ : m < r := by linarith
  let km : TopCat.of (Set.Icc u v) := ⟨m, by linarith, by linarith⟩
  have hkm₁ : km ∈ (Opens.map ε).obj W₁ := hW₁ km hm₂
  have hkm₂ : km ∈ (Opens.map ε).obj W₂ :=
    hδW₂ (mem_openIoo.2 ⟨by change τ - δ < m; linarith, by change m < τ + δ; linarith⟩)
  -- The two representatives agree near the fibre over `W₁ ⊓ W₂`.
  let d₀ := G.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op s₁ -
    G.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op s₂
  have hd₀ : (H).presheaf.map (homOfLE (le_refl ((Opens.map ε).obj (W₁ ⊓ W₂)))).op
      ((η).app _ d₀) = 0 := by
    have : (η).app _ d₀ = 0 := by
      simp only [d₀, map_sub]
      rw [← good_res G inf_le_left hs₁, ← good_res G inf_le_right hs₂]
      exact sub_self _
    rw [this]
    exact map_zero _
  obtain ⟨O, hO, hNO, hOs⟩ := exists_le_eq_zero_of_pullback_eq_zero ε G d₀ le_rfl hd₀
  obtain ⟨V, hV, ε₀, hε₀, hε₀O⟩ := c.exists_nhd_le O (hNO ⟨hkm₁, hkm₂⟩)
  have hkmy : π (ε km) = y := hε.apply_eq km
  have hkmt : c.t (ε km) = m := hε.t_apply km
  rw [hkmy] at hV
  -- Shrink: left of `m` keep `s₁`, right of `m` keep `s₂`, near `ε m` they agree.
  let B : Opens X := c.tOpen (Set.Ioo (m - ε₀) (m + ε₀)) isOpen_Ioo ⊓ (Opens.map π).obj V
  have hBO : B ≤ O := fun z hz => by
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hz
    refine hε₀O z h₃ ?_
    rw [hkmt, Real.dist_eq, abs_lt]
    constructor <;> linarith
  let Pl : Opens X := c.tOpen (Set.Iio m) isOpen_Iio
  let Pg : Opens X := c.tOpen (Set.Ioi m) isOpen_Ioi
  let W₁' := W₁ ⊓ (Pl ⊔ B)
  let W₂' := W₂ ⊓ (Pg ⊔ B)
  have hint : W₁' ⊓ W₂' ≤ O := by
    rintro z ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩
    rcases Opens.mem_sup.1 h₁ with h₁ | h₁
    · rcases Opens.mem_sup.1 h₂ with h₂ | h₂
      · exact absurd (lt_trans (show c.t z < m from h₁) (show m < c.t z from h₂)) (lt_irrefl _)
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
      (homOfLE (leOfHom ((Opens.map ε).map (homOfLE (le_sup_left : W₁' ≤ W₁' ⊔ W₂')))))
      (homOfLE (leOfHom ((Opens.map ε).map (homOfLE (le_sup_right : W₂' ≤ W₁' ⊔ W₂')))))
      (fun z hz => Opens.mem_sup.2 (Opens.mem_sup.1 hz)) _ _ ?_ ?_
    · exact (presheaf_map_map_apply _ _ _ _).trans ((good_res G inf_le_left hs₁).trans
        ((congrArg _ hσ₁.symm).trans (unit_res G le_sup_left σ)))
    · exact (presheaf_map_map_apply _ _ _ _).trans ((good_res G inf_le_left hs₂).trans
        ((congrArg _ hσ₂.symm).trans (unit_res G le_sup_right σ)))
  have hcov : ∀ z : TopCat.of (Set.Icc u v), z.1 < τ + δ →
      z ∈ (Opens.map ε).obj (W₁' ⊔ W₂') := by
    intro z hz
    rcases lt_trichotomy z.1 m with hzm | hzm | hzm
    · have hl : ε z ∈ Pl := (hε.mem_tOpen (Set.Iio m) isOpen_Iio).2 hzm
      exact Opens.mem_sup.2 (Or.inl ⟨hW₁ z (hzm.trans hm₂), Opens.mem_sup.2 (Or.inl hl)⟩)
    · have h1 : ε z ∈ c.tOpen (Set.Ioo (m - ε₀) (m + ε₀)) isOpen_Ioo :=
        (hε.mem_tOpen (Set.Ioo (m - ε₀) (m + ε₀)) isOpen_Ioo).2
          ⟨by rw [hzm]; linarith, by rw [hzm]; linarith⟩
      have h2 : π (ε z) ∈ V := by
        rw [hε.apply_eq z]
        exact hV
      have hb : ε z ∈ B := ⟨h1, h2⟩
      exact Opens.mem_sup.2 (Or.inl ⟨hW₁ z (hzm ▸ hm₂), Opens.mem_sup.2 (Or.inr hb)⟩)
    · have hg : ε z ∈ Pg := (hε.mem_tOpen (Set.Ioi m) isOpen_Ioi).2 hzm
      refine Opens.mem_sup.2 (Or.inr ⟨hδW₂ (mem_openIoo.2 ⟨?_, ?_⟩),
        Opens.mem_sup.2 (Or.inl hg)⟩)
      · change τ - δ < z.1
        linarith
      · change z.1 < τ + δ
        exact hz
  have := le_csSup hbdd (⟨W₁' ⊔ W₂', σ, hgood, hcov⟩ : τ + δ ∈ A)
  linarith

include hε in
/-- **The stalk comparison of a fibre square is an isomorphism** (degree-0 tautness of the
fibre). For a sheaf `G` of `k`-modules on `X`, the underived base change
`(ptOf y)⁻¹ π_* G ⟶ Γ([u, v]; ε⁻¹ G)` of the fibre square `hε.comp_eq` is an isomorphism of sheaves
on the point. -/
theorem isIso_baseChangeSheaf_app : IsIso ((baseChangeSheaf k hε.comp_eq).app G) := by
  let M := (TopCat.Sheaf.pushforward (ModuleCat.{0} k) π).obj G
  let P := (TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptOf y)).obj M
  let ηp := ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (ptOf y)).unit.app M).hom
  have hfib {U : Opens Y} (hyU : y ∈ U) : ⊤ ≤ (Opens.map ε).obj ((Opens.map π).obj U) :=
    fun x _ => by
      change π (ε x) ∈ U
      rw [hε.apply_eq x]
      exact hyU
  apply isIso_of_bijective_app_top
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨U, hU, s, rfl⟩ := exists_unit_eq_of_pt (ptOf y) M x
    have hyU : y ∈ U := hU (show (PUnit.unit : pt) ∈ (⊤ : Opens pt) from trivial)
    have hx' := (baseChangeSheaf_app_hom_app_top k hε.comp_eq G hU (hfib hyU) s).symm.trans hx
    obtain ⟨O, hO, hNO, hOs⟩ := exists_le_eq_zero_of_pullback_eq_zero _ G s (hfib hyU) hx'
    obtain ⟨U', hyU', hU'O⟩ := hε.exists_preimage_le O hNO
    have hle : (Opens.map π).obj (U ⊓ U') ≤ O := fun z hz => hU'O hz.2
    have hs0 : M.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op s = 0 :=
      (presheaf_map_map_apply G.presheaf hle hO s).symm.trans ((congrArg _ hOs).trans (map_zero _))
    have hU'' : ⊤ ≤ (Opens.map (ptOf y)).obj (U ⊓ U') := fun _ _ => ⟨hyU, hyU'⟩
    have e := (NatTrans.naturality_apply ηp (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op s).symm.trans
      ((congrArg (ηp.app _) hs0).trans (map_zero _))
    exact (presheaf_map_map_apply P.presheaf hU'' (fun _ hz => hz.1) _).symm.trans
      ((congrArg _ e).trans (map_zero _))
  · intro t
    obtain ⟨W, hW, s, hs⟩ := hε.exists_unit_eq G t
    obtain ⟨U, hyU, hUW⟩ := hε.exists_preimage_le W hW
    have hU : ⊤ ≤ (Opens.map (ptOf y)).obj U := fun _ _ => hyU
    refine ⟨P.presheaf.map (homOfLE hU).op (ηp.app (op U) (G.presheaf.map (homOfLE hUW).op s)),
      ?_⟩
    exact (baseChangeSheaf_app_hom_app_top k hε.comp_eq G hU (hfib hyU) _).trans
      ((congrArg _ (unit_res G hUW s)).trans ((presheaf_map_map_apply _ _ _ _).trans hs))

variable (k) in
include hε in
/-- The termwise underived base change of a fibre square is an isomorphism of complexes. -/
theorem isIso_baseChangeCochain_app (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{0} k))) :
    IsIso ((baseChangeCochain k hε.comp_eq).app K) :=
  TDA.Sheaf.isIso_baseChangeCochain_app k hε.comp_eq (fun G => hε.isIso_baseChangeSheaf_app G) K

variable (k) [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]

include hε in
/-- **Proper base change on a fibre.** For a fibre parametrisation `ε : [u, v] ⟶ X` of `π` at `y`,
the base-change morphism of the fibre square `ε ≫ π = toPt _ ≫ ptOf y`,
`Rπ_* ⋙ (ptOf y)⁻¹ ⟶ ε⁻¹ ⋙ RΓ([u, v]; -)`, is an isomorphism. -/
theorem isIso_baseChange : IsIso (baseChange k hε.comp_eq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  obtain ⟨n, hn⟩ := F.property
  have : F.IsGE n := (F.isGE_ι_obj_iff n).1 hn
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso F n
  rw [← NatTrans.isIso_app_iff_of_iso (baseChange k hε.comp_eq) e]
  have hI (m : ℤ) : Injective
      (((InjectiveObject.ι (X.Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L).obj.X m) :=
    (L.obj.X m).property
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) π)
    ((InjectiveObject.ι (X.Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L)
  have := isIso_rightDerivedFunctorPlusUnit_app_toPt_Icc_of_germSurjective
    ((TopCat.Sheaf.pullback (ModuleCat.{0} k) ε).mapCochainComplexPlus.obj
      ((InjectiveObject.ι (X.Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L))
    (fun m => @germSurjective_pullback_of_isFlasque k _ _ _ ε
      (((InjectiveObject.ι (X.Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L).obj.X m)
      (isFlasque_of_injective k _))
  have := hε.isIso_baseChangeCochain_app k
    ((InjectiveObject.ι (X.Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L)
  rw [← isIso_comp_left_iff ((pullbackPlus k (ptOf y)).map
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) π).rightDerivedFunctorPlusUnit.app _)),
    baseChange_app_Q]
  infer_instance

include hε in
/-- **Stalks of the derived direct image of a sheaf vanish above degree one.** If `π` has a fibre
parametrisation at `y`, then for a sheaf `G` of `k`-modules on `X` placed in degree `0`, `Hⁱ` of
the stalk at `y` of `Rπ_* G` vanishes for `2 ≤ i`. -/
theorem isZero_H_stalk_pushforwardPlus (G : X.Sheaf (ModuleCat.{0} k)) {i : ℤ} (hi : 2 ≤ i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((pullbackPlus k (ptOf y)).obj ((pushforwardPlus k π).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) :=
  have := hε.isIso_baseChange k
  (isZero_H_Icc ((TopCat.Sheaf.pullback (ModuleCat.{0} k) ε).obj G) hi).of_iso
    ((DerivedCategory.Plus.homologyFunctor _ i).mapIso
        ((asIso (baseChange k hε.comp_eq)).app _) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ i).mapIso
      ((pushforwardPlus k (toPt (TopCat.of (Set.Icc u v)))).mapIso
        (rightDerivedFunctorPlusSingleIso (TopCat.Sheaf.pullback (ModuleCat.{0} k) ε) 0 G)))

end IsFibreParam

end FibreCoordinate

/-- **An interval fibration** `π : X ⟶ Y`: a fibre coordinate `t` (`(π, t)` inducing, `π`
closed) with, at every point `y : Y`, a fibre parametrisation `e y : [lo y, hi y] ⟶ X` of the
fibre `π⁻¹ {y}` (`e_comp`, `t_e`, `mem_range`). A fibre is empty when `hi y < lo y` and a point
when `lo y = hi y`. -/
structure IntervalFibration {X Y : TopCat.{0}} (π : X ⟶ Y) extends FibreCoordinate π where
  /-- The left end of the fibre interval. -/
  lo : Y → ℝ
  /-- The right end of the fibre interval. -/
  hi : Y → ℝ
  /-- The fibre parametrisations. -/
  e : ∀ y, TopCat.of (Set.Icc (lo y) (hi y)) ⟶ X
  /-- `e y` parametrises the fibre at `y` in the coordinate `t`. -/
  isFibreParam : ∀ y, toFibreCoordinate.IsFibreParam y (e y)

namespace IntervalFibration

variable {X Y : TopCat.{0}} {π : X ⟶ Y} (hπ : IntervalFibration π) (y : Y)

/-- The fibre square of an interval fibration at `y`: `e y ≫ π = toPt _ ≫ ptOf y`. -/
theorem e_comp : hπ.e y ≫ π = toPt _ ≫ ptOf y := (hπ.isFibreParam y).comp_eq

/-- The fibre parametrisation is a section of the fibre coordinate. -/
theorem t_e (x : TopCat.of (Set.Icc (hπ.lo y) (hπ.hi y))) : hπ.t (hπ.e y x) = x.1 :=
  (hπ.isFibreParam y).t_apply x

/-- The range of the fibre parametrisation at `y` is the fibre `π⁻¹ {y}`. -/
theorem mem_range {y : Y} {z : X} : z ∈ Set.range (hπ.e y) ↔ π z = y :=
  (hπ.isFibreParam y).mem_range_iff

/-- The fibre parametrisation at `y` lands in the fibre. -/
@[simp]
theorem apply_e (x : TopCat.of (Set.Icc (hπ.lo y) (hπ.hi y))) : π (hπ.e y x) = y :=
  (hπ.isFibreParam y).apply_eq x

/-- **The stalk comparison of an interval fibration is an isomorphism.** For a sheaf `G` of
`k`-modules on `X`, the underived base change `(ptOf y)⁻¹ π_* G ⟶ Γ([lo y, hi y]; (e y)⁻¹ G)` is
an isomorphism. -/
instance isIso_baseChangeSheaf_app (G : X.Sheaf (ModuleCat.{0} k)) :
    IsIso ((baseChangeSheaf k (hπ.e_comp y)).app G) :=
  (hπ.isFibreParam y).isIso_baseChangeSheaf_app G

variable (k) [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory ((TopCat.of (Set.Icc (hπ.lo y) (hπ.hi y))).Sheaf (ModuleCat.{0} k))]

/-- **Proper base change on the fibres of an interval fibration.** At every point `y : Y`, the
base-change morphism of the fibre square `e y ≫ π = toPt _ ≫ ptOf y`,
`Rπ_* ⋙ (ptOf y)⁻¹ ⟶ (e y)⁻¹ ⋙ RΓ([lo y, hi y]; -)`, is an isomorphism. -/
instance isIso_baseChange : IsIso (baseChange k (hπ.e_comp y)) :=
  (hπ.isFibreParam y).isIso_baseChange k

/-- **The canonical stalk formula of an interval fibration.** For `F ∈ D⁺(Sh X)`, the stalk at `y`
of `Rπ_* F` (its inverse image `(ptOf y)⁻¹` to the point) is `RΓ` of the fibre
`π⁻¹ {y} ≅ [lo y, hi y]` with coefficients in `(e y)⁻¹ F`, naturally in `F`; the isomorphism is
the base-change morphism of the fibre square. -/
def stalkFormula :
    pushforwardPlus k π ⋙ pullbackPlus k (ptOf y) ≅
      pullbackPlus k (hπ.e y) ⋙
        pushforwardPlus k (toPt (TopCat.of (Set.Icc (hπ.lo y) (hπ.hi y)))) :=
  asIso (baseChange k (hπ.e_comp y))

/-- The stalk formula is the base-change morphism of the fibre square. -/
@[simp]
theorem stalkFormula_hom : (hπ.stalkFormula k y).hom = baseChange k (hπ.e_comp y) := rfl

include hπ in
/-- **Stalks of the derived direct image of a sheaf vanish above degree one.** For a sheaf `G` of
`k`-modules on `X` placed in degree `0`, `Hⁱ` of the stalk at `y` of `Rπ_* G` vanishes for
`2 ≤ i`. -/
theorem isZero_H_stalk_pushforwardPlus (G : X.Sheaf (ModuleCat.{0} k)) {i : ℤ} (hi : 2 ≤ i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((pullbackPlus k (ptOf y)).obj ((pushforwardPlus k π).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) :=
  (hπ.isFibreParam y).isZero_H_stalk_pushforwardPlus k G hi

end IntervalFibration

section fibrewise

variable (k) {X Y X' Y' : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The fibrewise criterion for interval fibrations.** Let `w : g' ≫ f = f' ≫ g` be a
commutative square, `c` a fibre coordinate of `f` and `hf'` an interval fibration structure on
`f'`. If for every `z : Y'` the fibre parametrisation `hf'.e z` of `f'` at `z`, followed by `g'`,
is a fibre parametrisation of `f` at `g z` in the coordinate `c`, then the base-change morphism
`Rf_* ⋙ g⁻¹ ⟶ g'⁻¹ ⋙ Rf'_*` of `w` is an isomorphism. -/
theorem isIso_baseChange_of_isFibreParam (w : g' ≫ f = f' ≫ g) (c : FibreCoordinate f)
    (hf' : IntervalFibration f')
    [∀ z, HasDerivedCategory ((TopCat.of (Set.Icc (hf'.lo z) (hf'.hi z))).Sheaf (ModuleCat.{0} k))]
    (h : ∀ z, c.IsFibreParam (g z) (hf'.e z ≫ g')) :
    IsIso (baseChange k w) :=
  isIso_baseChange_of_fibres k w (fun z => TopCat.of (Set.Icc (hf'.lo z) (hf'.hi z))) hf'.e
    hf'.e_comp (fun z => hf'.isIso_baseChange k z) (fun z wz =>
      (isIso_baseChange_congr k (h z).comp_eq wz rfl rfl).1 ((h z).isIso_baseChange k))

end fibrewise

namespace IntervalFibration

variable (k) {X Y : TopCat.{0}} {π : X ⟶ Y}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]

/-- **The derived unit of an interval fibration with nonempty fibres is an isomorphism.** If every
fibre interval `[lo y, hi y]` of the interval fibration `π : X ⟶ Y` is nonempty, the derived unit
`𝟭 ⟶ π⁻¹ ⋙ Rπ_*` of `D⁺(Sh Y)` is an isomorphism, that is `Rπ_* π⁻¹ N ≅ N` naturally in `N`. At a
point `y`, `(ptOf y)⁻¹` of the unit followed by the invertible base change of the fibre square is
the derived unit of the nonempty interval `[lo y, hi y]` (`derivedUnit_baseChange`,
`isIso_derivedUnit_Icc`), and detection at points concludes. -/
theorem isIso_derivedUnit (hπ : IntervalFibration π)
    [∀ y, HasDerivedCategory ((TopCat.of (Set.Icc (hπ.lo y) (hπ.hi y))).Sheaf (ModuleCat.{0} k))]
    (h : ∀ y, hπ.lo y ≤ hπ.hi y) : IsIso (derivedUnit k π) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  rw [isIso_iff_forall_isIso_pullbackPlus_pt]
  intro y
  have := isIso_derivedUnit_Icc (k := k) (h y)
  have h₁ : IsIso ((pullbackPlus k (ptOf y)).map ((derivedUnit k π).app N) ≫
      (baseChange k (hπ.e_comp y)).app ((pullbackPlus k π).obj N)) := by
    rw [derivedUnit_baseChange]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((baseChange k (hπ.e_comp y)).app ((pullbackPlus k π).obj N))

end IntervalFibration

end TDA.Sheaf
