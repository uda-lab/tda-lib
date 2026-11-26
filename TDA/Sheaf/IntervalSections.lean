import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import TDA.Sheaf.PresheafRestriction
import TDA.Sheaf.SheafFlasque

/-!
# Lifting global sections on subspaces of the real line

Let `k` be a ring, `S ⊆ ℝ` with the subspace topology, and `X₁ ⟶ X₂ ⟶ X₃` an exact complex of
sheaves of `k`-modules on `S` whose first term is germ-surjective (`GermSurjective`, for
instance flasque or injective). This file shows that a global section `s` of `X₃` that lifts to
`X₂` near every point lifts to `X₂` globally when `S` is a compact interval.

* `openIoo S p q` is the open subset `S ∩ (p, q)` of `S` (`mem_openIoo`,
  `openIoo_le_openIoo`); every neighbourhood of a point `x` contains some
  `openIoo S (x - δ) (x + δ)` (`exists_openIoo_le`).
* `exists_section_lift_extend` is the extension step, for any order-connected `S`: a lift of
  `s` over `S ∩ (l, a)` extends to a lift over `S ∩ (l, t)` for some `t > b`, for any `b ∈ S`,
  without changing it over `S ∩ (l, a')`, where `l < a' < a` and `a' ∈ S`. The proof is a
  supremum argument: at the supremum `τ` of the reachable right ends, the given lift and a local
  lift near `τ` differ near a point `r < τ` by the image of a section of `X₁`; germ-surjectivity
  extends that section over the local neighbourhood, and the corrected local lift glues with
  the given one.
* `exists_section_lift_Icc`: on `[u, v]` every locally liftable global section lifts globally.
* `sections_exact_Icc`: for a complex `L₀ ⟶ L₁ ⟶ L₂ ⟶ L₃` of sheaves on `[u, v]`, exact at
  `L₁` and `L₂`, with `L₀` germ-surjective, the global sections are exact at `Γ(L₂)`.

The statements on `[u, v]` hold for all `u` and `v`; the empty interval is included.
Extension to open and half-open intervals (a countable gluing of the extension step) is not
treated here.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable (k : Type) [Ring k]

section Opens

variable (S : Set ℝ)

/-- The open subset `S ∩ (p, q)` of a subspace `S` of the real line. -/
def openIoo (p q : ℝ) : Opens (TopCat.of S) :=
  ⟨Subtype.val ⁻¹' Set.Ioo p q, isOpen_Ioo.preimage continuous_subtype_val⟩

variable {S}

@[simp]
theorem mem_openIoo {p q : ℝ} {x : TopCat.of S} :
    x ∈ openIoo S p q ↔ p < (x : ℝ) ∧ (x : ℝ) < q := by
  simp only [openIoo, Opens.mem_mk, Set.mem_preimage, Set.mem_Ioo]

theorem openIoo_le_openIoo {p p' q q' : ℝ} (hp : p ≤ p') (hq : q' ≤ q) :
    openIoo S p' q' ≤ openIoo S p q :=
  fun _ hx => by
    rw [mem_openIoo] at hx ⊢
    exact ⟨hp.trans_lt hx.1, hx.2.trans_le hq⟩

/-- Every open neighbourhood of a point `x` of `S` contains `S ∩ (x - δ, x + δ)` for some
`δ > 0`. -/
theorem exists_openIoo_le {W : Opens (TopCat.of S)} {x : TopCat.of S} (hx : x ∈ W) :
    ∃ δ > 0, openIoo S ((x : ℝ) - δ) ((x : ℝ) + δ) ≤ W := by
  obtain ⟨V, hV, hVW⟩ := isOpen_induced_iff.mp W.isOpen
  have hxV : (x : ℝ) ∈ V := by
    have : x ∈ (Subtype.val ⁻¹' V : Set S) := by rw [hVW]; exact hx
    exact this
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV _ hxV
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have : y ∈ (Subtype.val ⁻¹' V : Set S) :=
    hball (by rw [Real.ball_eq_Ioo]; exact mem_openIoo.1 hy)
  rw [hVW] at this
  exact this

end Opens

variable {k}

variable (k) in
/-- **The extension step.** Let `S ⊆ ℝ` be order-connected, `X₁ ⟶ X₂ ⟶ X₃` an exact complex of
sheaves of `k`-modules on `S` with `X₁` germ-surjective, and `s` a global section of `X₃` that
lifts to `X₂` near every point. Let `l < a' < a` with `a' ∈ S`, and let `g₀` lift `s` over
`S ∩ (l, a)`. Then for every `b ∈ S` there are `t > b` (with `t ≥ a`) and a lift of `s` over
`S ∩ (l, t)` that agrees with `g₀` over `S ∩ (l, a')`. -/
theorem exists_section_lift_extend {S : Set ℝ} (hS : S.OrdConnected)
    (Sc : ShortComplex ((TopCat.of S).Sheaf (ModuleCat.{0} k))) (hSc : Sc.Exact)
    (h₁ : GermSurjective k Sc.X₁) (s : Sc.X₃.presheaf.obj (op ⊤))
    (hs : ∀ x : TopCat.of S, ∃ (W : Opens (TopCat.of S)) (_ : x ∈ W)
      (t : Sc.X₂.presheaf.obj (op W)),
      Sc.g.hom.app _ t = Sc.X₃.presheaf.map (homOfLE le_top).op s)
    {l a' a b : ℝ} (hla' : l < a') (ha'a : a' < a) (ha' : a' ∈ S) (hb : b ∈ S)
    (g₀ : Sc.X₂.presheaf.obj (op (openIoo S l a)))
    (hg₀ : Sc.g.hom.app _ g₀ = Sc.X₃.presheaf.map (homOfLE le_top).op s) :
    ∃ t, b < t ∧ ∃ (hat : a ≤ t) (g : Sc.X₂.presheaf.obj (op (openIoo S l t))),
      Sc.g.hom.app _ g = Sc.X₃.presheaf.map (homOfLE le_top).op s ∧
      Sc.X₂.presheaf.map (homOfLE (openIoo_le_openIoo le_rfl (ha'a.le.trans hat))).op g =
        Sc.X₂.presheaf.map (homOfLE (openIoo_le_openIoo le_rfl ha'a.le)).op g₀ := by
  have mm := presheaf_map_map_apply (k := k) (X := TopCat.of S)
  have nat := @sheafHom_naturality_apply k _ (TopCat.of S)
  have gf := @shortComplex_g_f_apply k _ (TopCat.of S)
  rcases lt_or_ge b a with hba | hab
  · exact ⟨a, hba, le_rfl, g₀, hg₀, rfl⟩
  -- `A` is the set of right ends `t ≥ a` reachable by a lift extending `g₀`.
  let A : Set ℝ := {t | ∃ (hat : a ≤ t) (g : Sc.X₂.presheaf.obj (op (openIoo S l t))),
      Sc.g.hom.app _ g = Sc.X₃.presheaf.map (homOfLE le_top).op s ∧
      Sc.X₂.presheaf.map (homOfLE (openIoo_le_openIoo le_rfl (ha'a.le.trans hat))).op g =
        Sc.X₂.presheaf.map (homOfLE (openIoo_le_openIoo le_rfl ha'a.le)).op g₀}
  suffices ∃ t ∈ A, b < t by
    obtain ⟨t, ⟨hat, g, hg, hag⟩, hbt⟩ := this
    exact ⟨t, hbt, hat, g, hg, hag⟩
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hA : a ∈ A := ⟨le_rfl, g₀, hg₀, rfl⟩
  have hbdd : BddAbove A := ⟨b, hcon⟩
  set τ := sSup A with hτ
  have haτ : a ≤ τ := le_csSup hbdd hA
  have hτb : τ ≤ b := csSup_le ⟨a, hA⟩ hcon
  have hτS : τ ∈ S := hS.out ha' hb ⟨(ha'a.trans_le haτ).le, hτb⟩
  -- A local lift `h` over a neighbourhood `W ⊇ S ∩ (τ - δ, τ + δ)` of `τ`.
  obtain ⟨W, hxW, h, hh⟩ := hs ⟨τ, hτS⟩
  obtain ⟨δ, hδ, hδW⟩ := exists_openIoo_le hxW
  change openIoo S (τ - δ) (τ + δ) ≤ W at hδW
  -- A reachable right end `t` close to `τ`, with its lift `g`.
  set m := max (τ - δ) a' with hm
  have hmτ : m < τ := max_lt (by linarith) (ha'a.trans_le haτ)
  obtain ⟨t, ⟨hat, g, hg, hag⟩, hmt⟩ := exists_lt_of_lt_csSup ⟨a, hA⟩ hmτ
  have htτ : t ≤ τ := le_csSup hbdd ⟨hat, g, hg, hag⟩
  have hτδm : τ - δ ≤ m := le_max_left _ _
  have ha'm : a' ≤ m := le_max_right _ _
  -- A point `r ∈ S` strictly between `m` and `t`.
  set r := (m + t) / 2 with hr
  have hmr : m < r := by linarith
  have hrt : r < t := by linarith
  have hrS : r ∈ S := hS.out ha' hb ⟨ha'm.trans hmr.le, hrt.le.trans (htτ.trans hτb)⟩
  let xr : TopCat.of S := ⟨r, hrS⟩
  -- The difference `d` of the two lifts over `N = S ∩ (m, t)` maps to zero.
  have hNt : openIoo S m t ≤ openIoo S l t :=
    openIoo_le_openIoo (hla'.le.trans ha'm) le_rfl
  have hNW : openIoo S m t ≤ W :=
    (openIoo_le_openIoo hτδm (by linarith)).trans hδW
  let d : Sc.X₂.presheaf.obj (op (openIoo S m t)) :=
    Sc.X₂.presheaf.map (homOfLE hNt).op g - Sc.X₂.presheaf.map (homOfLE hNW).op h
  have hd : Sc.g.hom.app _ d = 0 := by
    simp only [d, map_sub, nat, hg, hh, mm, sub_self]
  have hxrN : xr ∈ openIoo S m t := ⟨hmr, hrt⟩
  -- Near `r`, `d` is the image of a section `c` of `X₁`.
  obtain ⟨W₁, hxW₁, hW₁N, c, hc⟩ := exists_local_preimage_of_exact k Sc hSc d hd xr hxrN
  -- Germ-surjectivity extends the germ of `c` at `r` to a section `c'` over `W`.
  have hxrW : xr ∈ W := hNW hxrN
  obtain ⟨c', hc'⟩ := h₁ W xr hxrW (Sc.X₁.presheaf.germ W₁ xr hxW₁ c)
  obtain ⟨W₂, hxW₂, iW, iW₁, hcc⟩ := TopCat.Presheaf.germ_eq _ xr hxrW hxW₁ c' c hc'
  obtain ⟨ε, hε, hεW₂⟩ := exists_openIoo_le hxW₂
  change openIoo S (r - ε) (r + ε) ≤ W₂ at hεW₂
  set ε' := min ε (min (t - r) (r - m)) with hε'
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'1 : ε' ≤ t - r := (min_le_right _ _).trans (min_le_left _ _)
  have hε'2 : ε' ≤ r - m := (min_le_right _ _).trans (min_le_right _ _)
  have hε'pos : 0 < ε' := lt_min hε (lt_min (by linarith) (by linarith))
  -- Glue `g` over `U₁ = S ∩ (l, r + ε')` with the corrected local lift over
  -- `U₂ = S ∩ (r - ε', τ + δ)`.
  have hU₁ : openIoo S l (r + ε') ≤ openIoo S l t := openIoo_le_openIoo le_rfl (by linarith)
  have hU₂ : openIoo S (r - ε') (τ + δ) ≤ W :=
    (openIoo_le_openIoo (by linarith) le_rfl).trans hδW
  have hV : openIoo S l (r + ε') ⊓ openIoo S (r - ε') (τ + δ) ≤ W₂ :=
    fun x hx => hεW₂ ⟨by linarith [hx.2.1], by linarith [hx.1.2]⟩
  have hVW₁ := hV.trans (leOfHom iW₁)
  let σ₁ := Sc.X₂.presheaf.map (homOfLE hU₁).op g
  let σ₂ := Sc.X₂.presheaf.map (homOfLE hU₂).op h +
    Sc.f.hom.app _ (Sc.X₁.presheaf.map (homOfLE hU₂).op c')
  have hcc' : Sc.X₁.presheaf.map (homOfLE (hV.trans (leOfHom iW))).op c' =
      Sc.X₁.presheaf.map (homOfLE hVW₁).op c := by
    have := congrArg (Sc.X₁.presheaf.map (homOfLE hV).op) hcc
    rwa [← homOfLE_leOfHom iW, ← homOfLE_leOfHom iW₁, mm, mm] at this
  have hfc : Sc.f.hom.app _ (Sc.X₁.presheaf.map (homOfLE hVW₁).op c) =
      Sc.X₂.presheaf.map (homOfLE (hU₁.trans' inf_le_left)).op g -
        Sc.X₂.presheaf.map (homOfLE (hU₂.trans' inf_le_right)).op h := by
    rw [nat, hc]
    simp only [d, map_sub, mm]
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_glue₂ Sc.X₂ σ₁ σ₂ (by
    simp only [σ₁, σ₂, map_add, ← nat, mm]
    rw [hcc', hfc]
    abel)
  -- The glued section is a lift over `S ∩ (l, τ + δ)` extending `g₀`, so `τ + δ ∈ A`.
  have hcover : openIoo S l (τ + δ) ≤ openIoo S l (r + ε') ⊔ openIoo S (r - ε') (τ + δ) := by
    intro x hx
    by_cases hxr : (x : ℝ) < r + ε'
    · exact Or.inl ⟨hx.1, hxr⟩
    · exact Or.inr ⟨by linarith, hx.2⟩
  have hΩ₁ : openIoo S l (r + ε') ≤ openIoo S l (τ + δ) := openIoo_le_openIoo le_rfl (by linarith)
  have hΩ₂ : openIoo S (r - ε') (τ + δ) ≤ openIoo S l (τ + δ) :=
    openIoo_le_openIoo (by linarith) le_rfl
  let gl := Sc.X₂.presheaf.map (homOfLE hcover).op σ
  have hgl₁ : Sc.X₂.presheaf.map (homOfLE hΩ₁).op gl = σ₁ := by
    rw [mm]; exact hσ₁
  have hgl₂ : Sc.X₂.presheaf.map (homOfLE hΩ₂).op gl = σ₂ := by
    rw [mm]; exact hσ₂
  have hmem : τ + δ ∈ A := by
    refine ⟨by linarith, gl, ?_, ?_⟩
    · refine TopCat.Sheaf.eq_of_locally_eq₂ Sc.X₃ (homOfLE hΩ₁) (homOfLE hΩ₂) hcover _ _ ?_ ?_
      · rw [← nat, hgl₁]
        simp only [σ₁, nat, hg, mm]
      · rw [← nat, hgl₂]
        simp only [σ₂, map_add, gf, map_zero, add_zero, nat, hh,
          mm]
    · have hA' : openIoo S l a' ≤ openIoo S l (r + ε') := openIoo_le_openIoo le_rfl (by linarith)
      rw [← mm _ hA' hΩ₁ gl, hgl₁]
      simp only [σ₁, mm]
      exact hag
  have := le_csSup hbdd hmem
  linarith

variable (k) in
/-- **Section lifting on a compact interval.** On `[u, v]`, let `X₁ ⟶ X₂ ⟶ X₃` be an exact
complex of sheaves of `k`-modules with `X₁` germ-surjective. A global section of `X₃` that lifts
to `X₂` near every point lifts to a global section of `X₂`. -/
theorem exists_section_lift_Icc {u v : ℝ}
    (Sc : ShortComplex ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))) (hSc : Sc.Exact)
    (h₁ : GermSurjective k Sc.X₁) (s : Sc.X₃.presheaf.obj (op ⊤))
    (hs : ∀ x : TopCat.of (Set.Icc u v), ∃ (W : Opens (TopCat.of (Set.Icc u v))) (_ : x ∈ W)
      (t : Sc.X₂.presheaf.obj (op W)),
      Sc.g.hom.app _ t = Sc.X₃.presheaf.map (homOfLE le_top).op s) :
    ∃ t : Sc.X₂.presheaf.obj (op ⊤), Sc.g.hom.app _ t = s := by
  have mm := presheaf_map_map_apply (k := k) (X := TopCat.of (Set.Icc u v))
  have nat := @sheafHom_naturality_apply k _ (TopCat.of (Set.Icc u v))
  rcases lt_or_ge v u with hvu | huv
  · -- The empty interval: there are no points, so every section vanishes.
    refine ⟨0, ?_⟩
    rw [map_zero]
    refine (TopCat.Presheaf.section_ext Sc.X₃ ⊤ _ _ (fun x _ => ?_)).symm
    exact absurd (x.2.1.trans x.2.2) (not_le.2 hvu)
  -- A local lift near `u` starts the extension step, which reaches past `v`.
  obtain ⟨W, huW, h, hh⟩ := hs ⟨u, le_rfl, huv⟩
  obtain ⟨δ, hδ, hδW⟩ := exists_openIoo_le huW
  change openIoo _ (u - δ) (u + δ) ≤ W at hδW
  have hle : openIoo (Set.Icc u v) (u - δ) (u + δ / 2) ≤ W :=
    (openIoo_le_openIoo le_rfl (by linarith)).trans hδW
  obtain ⟨t, hvt, -, g, hg, -⟩ := exists_section_lift_extend k Set.ordConnected_Icc Sc hSc h₁ s
    hs (l := u - δ) (a' := u) (a := u + δ / 2) (b := v) (by linarith) (by linarith)
    ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ (Sc.X₂.presheaf.map (homOfLE hle).op h) (by rw [nat, hh, mm])
  have htop : (⊤ : Opens (TopCat.of (Set.Icc u v))) ≤ openIoo _ (u - δ) t :=
    fun x _ => ⟨by linarith [x.2.1], by linarith [x.2.2]⟩
  refine ⟨Sc.X₂.presheaf.map (homOfLE htop).op g, ?_⟩
  rw [nat, hg, mm, presheaf_map_eq _ _ (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

variable (k) in
/-- **Exactness of global sections on a compact interval.** On `[u, v]`, let
`L₀ ⟶ L₁ ⟶ L₂ ⟶ L₃` be a complex of sheaves of `k`-modules, exact at `L₁` and `L₂`, with `L₀`
germ-surjective. Then a global section of `L₂` that maps to zero in `L₃` is the image of a global
section of `L₁`. -/
theorem sections_exact_Icc {u v : ℝ}
    {L₀ L₁ L₂ L₃ : (TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k)}
    (d₀ : L₀ ⟶ L₁) (d₁ : L₁ ⟶ L₂) (d₂ : L₂ ⟶ L₃) (w₀ : d₀ ≫ d₁ = 0) (w₁ : d₁ ≫ d₂ = 0)
    (h₁ : (ShortComplex.mk d₀ d₁ w₀).Exact) (h₂ : (ShortComplex.mk d₁ d₂ w₁).Exact)
    (hL₀ : GermSurjective k L₀) (s : L₂.presheaf.obj (op ⊤)) (hs : d₂.hom.app _ s = 0) :
    ∃ t : L₁.presheaf.obj (op ⊤), d₁.hom.app _ t = s :=
  exists_section_lift_Icc k (ShortComplex.mk d₀ d₁ w₀) h₁ hL₀ s (fun x => by
    obtain ⟨W, hxW, _, t, ht⟩ :=
      exists_local_preimage_of_exact k (ShortComplex.mk d₁ d₂ w₁) h₂ s hs x trivial
    exact ⟨W, hxW, t, ht⟩)

end TDA.Sheaf
