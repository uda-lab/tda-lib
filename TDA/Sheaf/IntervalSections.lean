import Mathlib.Data.Rat.Denumerable
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import TDA.Sheaf.PresheafRestriction
import TDA.Sheaf.SheafFlasque

/-!
# Lifting global sections on subspaces of the real line

Let `k` be a ring, `S ⊆ ℝ` with the subspace topology, and `X₁ ⟶ X₂ ⟶ X₃` an exact complex of
sheaves of `k`-modules on `S`. This file shows that a global section `s` of `X₃` that lifts to
`X₂` near every point lifts to `X₂` globally when `S` is order-connected (an open, half-open,
closed or unbounded interval, or `ℝ`) and `X₁` is germ-surjective (`GermSurjective`, for
instance flasque or injective) on the opens avoiding one point `c`.

* `openIoo S p q` is the open subset `S ∩ (p, q)` of `S` (`mem_openIoo`,
  `openIoo_le_openIoo`); every neighbourhood of a point `x` contains some
  `openIoo S (x - δ) (x + δ)` (`exists_openIoo_le`).
* `exists_glue_monotone`: compatible sections over an increasing sequence of opens glue.
* `exists_section_lift_extend_right` is the extension step, for any order-connected `S`, with
  `X₁` germ-surjective on the opens above `a'`: a lift of `s` over `S ∩ (l, a)` extends to a lift
  over `S ∩ (l, t)` for some `t > b`, for any `b ∈ S`, without changing it over `S ∩ (l, a')`,
  where `l < a' < a` and `a' ∈ S`. The proof is a supremum argument: at the supremum `τ` of the
  reachable right ends, the given lift and a local lift near `τ` differ near a point `r < τ` by
  the image of a section of `X₁`; germ-surjectivity extends that section over the part of the
  local neighbourhood above `a'`, and the corrected local lift glues with the given one.
  `exists_section_lift_extend` is the case of a germ-surjective `X₁`, and
  `exists_section_lift_extend_left` the leftward step, with `X₁` germ-surjective on the opens
  below `a'`. Both directions are one proof, for the coordinate `x` or `-x` on `S`.
* `exists_section_lift_ordConnected`: on an order-connected `S`, with `X₁` germ-surjective on
  the opens avoiding `c`, every locally liftable global section lifts. A local lift at a base
  point (`c` when `c ∈ S`) is swept to the right and to the left along cofinal increasing
  sequences (`exists_glue_monotone`), and the two sweeps glue near the base point.
* `sections_exact_ordConnected`: for a complex `L₀ ⟶ L₁ ⟶ L₂ ⟶ L₃` of sheaves on an
  order-connected `S`, exact at `L₁` and `L₂`, with `L₀` germ-surjective on the opens avoiding
  `c`, the global sections are exact at `Γ(L₂)`.
* `exists_section_lift_Icc` and `sections_exact_Icc` are the cases `S = [u, v]`, for all `u` and
  `v`; the empty interval is included.
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

/-- **Gluing along an increasing sequence of opens.** Compatible sections over an increasing
sequence of opens glue to a section over their union. -/
theorem exists_glue_monotone {X : TopCat.{0}} (F : X.Sheaf (ModuleCat.{0} k))
    (U : ℕ → Opens X) (hU : Monotone U) (s : ∀ n, F.presheaf.obj (op (U n)))
    (hs : ∀ n, F.presheaf.map (homOfLE (hU (Nat.le_succ n))).op (s (n + 1)) = s n) :
    ∃ t : F.presheaf.obj (op (⨆ n, U n)),
      ∀ n, F.presheaf.map (homOfLE (le_iSup U n)).op t = s n := by
  have hle : ∀ i j (h : i ≤ j), F.presheaf.map (homOfLE (hU h)).op (s j) = s i := by
    intro i j h
    induction j, h using Nat.le_induction with
    | base =>
      rw [show (homOfLE (hU (le_refl i))).op = 𝟙 (op (U i)) from Subsingleton.elim _ _,
        F.presheaf.map_id]
      rfl
    | succ j hij ih =>
      rw [← ih, ← hs j, presheaf_map_map_apply]
  have key : ∀ i j, i ≤ j → F.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (s i) =
      F.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j) := by
    intro i j h
    rw [← hle i j h, presheaf_map_map_apply]
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing F U s (fun i j => by
    rcases le_total i j with h | h
    · exact key i j h
    · rw [← hle j i h]
      exact (presheaf_map_map_apply F.presheaf (inf_le_right : U i ⊓ U j ≤ U j) (hU h)
        (s i)).symm)
  exact ⟨t, ht⟩

variable {k}

/-! ### Sweeps along a coordinate

The extension step and the sweeps are proved once for a continuous coordinate `φ : X → ℝ` that
is an embedding onto an order-connected subset; the rightward statements use `φ = Subtype.val`
and the leftward ones `φ = -Subtype.val`. -/

section Coordinate

variable {X : TopCat.{0}} (φ : X → ℝ) (hφ : Continuous φ)

/-- The open `{x | p < φ x < q}`. -/
private def coordIoo (p q : ℝ) : Opens X :=
  ⟨φ ⁻¹' Set.Ioo p q, isOpen_Ioo.preimage hφ⟩

/-- The open `{x | p < φ x}`. -/
private def coordIoi (p : ℝ) : Opens X :=
  ⟨φ ⁻¹' Set.Ioi p, isOpen_Ioi.preimage hφ⟩

private theorem coordIoo_le {p p' q q' : ℝ} (hp : p ≤ p') (hq : q' ≤ q) :
    coordIoo φ hφ p' q' ≤ coordIoo φ hφ p q :=
  fun _ hx => ⟨hp.trans_lt hx.1, hx.2.trans_le hq⟩

private theorem coordIoo_le_coordIoi {p p' q : ℝ} (hp : p ≤ p') :
    coordIoo φ hφ p' q ≤ coordIoi φ hφ p :=
  fun _ hx => hp.trans_lt hx.1

variable (k) in
/-- The extension step along the coordinate `φ`, with germ-surjectivity of `X₁` required only
on opens whose points lie above `a'`. -/
private theorem extend_core
    (hconn : ∀ x y : X, ∀ z, φ x ≤ z → z ≤ φ y → ∃ w : X, φ w = z)
    (hnbhd : ∀ {W : Opens X} {x : X}, x ∈ W → ∃ δ > 0, coordIoo φ hφ (φ x - δ) (φ x + δ) ≤ W)
    (Sc : ShortComplex (X.Sheaf (ModuleCat.{0} k))) (hSc : Sc.Exact) {l a' a b : ℝ}
    (h₁ : ∀ V : Opens X, (∀ y ∈ V, a' < φ y) → ∀ (x : X) (hx : x ∈ V),
      Function.Surjective (Sc.X₁.presheaf.germ V x hx))
    (s : Sc.X₃.presheaf.obj (op ⊤))
    (hs : ∀ x : X, ∃ (W : Opens X) (_ : x ∈ W) (t : Sc.X₂.presheaf.obj (op W)),
      Sc.g.hom.app _ t = Sc.X₃.presheaf.map (homOfLE le_top).op s)
    (hla' : l < a') (ha'a : a' < a) (ha' : ∃ x : X, φ x = a') (hb : ∃ y : X, φ y = b)
    (g₀ : Sc.X₂.presheaf.obj (op (coordIoo φ hφ l a)))
    (hg₀ : Sc.g.hom.app _ g₀ = Sc.X₃.presheaf.map (homOfLE le_top).op s) :
    ∃ t, b < t ∧ ∃ (hat : a ≤ t) (g : Sc.X₂.presheaf.obj (op (coordIoo φ hφ l t))),
      Sc.g.hom.app _ g = Sc.X₃.presheaf.map (homOfLE le_top).op s ∧
      Sc.X₂.presheaf.map (homOfLE (coordIoo_le φ hφ le_rfl (ha'a.le.trans hat))).op g =
        Sc.X₂.presheaf.map (homOfLE (coordIoo_le φ hφ le_rfl ha'a.le)).op g₀ := by
  have mm := presheaf_map_map_apply (k := k) (X := X)
  have nat := @sheafHom_naturality_apply k _ X
  have gf := @shortComplex_g_f_apply k _ X
  obtain ⟨xa', hxa'⟩ := ha'
  obtain ⟨yb, hyb⟩ := hb
  rcases lt_or_ge b a with hba | hab
  · exact ⟨a, hba, le_rfl, g₀, hg₀, rfl⟩
  -- `A` is the set of right ends `t ≥ a` reachable by a lift extending `g₀`.
  let A : Set ℝ := {t | ∃ (hat : a ≤ t) (g : Sc.X₂.presheaf.obj (op (coordIoo φ hφ l t))),
      Sc.g.hom.app _ g = Sc.X₃.presheaf.map (homOfLE le_top).op s ∧
      Sc.X₂.presheaf.map (homOfLE (coordIoo_le φ hφ le_rfl (ha'a.le.trans hat))).op g =
        Sc.X₂.presheaf.map (homOfLE (coordIoo_le φ hφ le_rfl ha'a.le)).op g₀}
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
  obtain ⟨xτ, hxτ⟩ := hconn xa' yb τ (by rw [hxa']; linarith) (by rw [hyb]; exact hτb)
  -- A local lift `h` over a neighbourhood `W ⊇ {τ - δ < φ < τ + δ}` of `τ`.
  obtain ⟨W, hxW, h, hh⟩ := hs xτ
  obtain ⟨δ, hδ, hδW⟩ := hnbhd hxW
  rw [hxτ] at hδW
  -- A reachable right end `t` close to `τ`, with its lift `g`.
  set m := max (τ - δ) a' with hm
  have hmτ : m < τ := max_lt (by linarith) (ha'a.trans_le haτ)
  obtain ⟨t, ⟨hat, g, hg, hag⟩, hmt⟩ := exists_lt_of_lt_csSup ⟨a, hA⟩ hmτ
  have htτ : t ≤ τ := le_csSup hbdd ⟨hat, g, hg, hag⟩
  have hτδm : τ - δ ≤ m := le_max_left _ _
  have ha'm : a' ≤ m := le_max_right _ _
  -- A point `xr` with coordinate `r` strictly between `m` and `t`.
  set r := (m + t) / 2 with hr
  have hmr : m < r := by linarith
  have hrt : r < t := by linarith
  obtain ⟨xr, hxr⟩ := hconn xa' yb r (by rw [hxa']; linarith) (by rw [hyb]; linarith)
  -- The difference `d` of the two lifts over `N = {m < φ < t}` maps to zero.
  have hNt : coordIoo φ hφ m t ≤ coordIoo φ hφ l t :=
    coordIoo_le φ hφ (hla'.le.trans ha'm) le_rfl
  have hNW : coordIoo φ hφ m t ≤ W :=
    (coordIoo_le φ hφ hτδm (by linarith)).trans hδW
  let d : Sc.X₂.presheaf.obj (op (coordIoo φ hφ m t)) :=
    Sc.X₂.presheaf.map (homOfLE hNt).op g - Sc.X₂.presheaf.map (homOfLE hNW).op h
  have hd : Sc.g.hom.app _ d = 0 := by
    simp only [d, map_sub, nat, hg, hh, mm, sub_self]
  have hxrN : xr ∈ coordIoo φ hφ m t := by
    change m < φ xr ∧ φ xr < t
    rw [hxr]
    exact ⟨hmr, hrt⟩
  -- Near `xr`, `d` is the image of a section `c` of `X₁`.
  obtain ⟨W₁, hxW₁, hW₁N, c, hc⟩ := exists_local_preimage_of_exact k Sc hSc d hd xr hxrN
  -- Germ-surjectivity on `W' = {m < φ < τ + δ}`, whose points lie above `a'`, extends the germ
  -- of `c` at `xr` to a section `c'` over `W'`.
  let W' := coordIoo φ hφ m (τ + δ)
  have hW'W : W' ≤ W := (coordIoo_le φ hφ hτδm le_rfl).trans hδW
  have hxrW' : xr ∈ W' := by
    change m < φ xr ∧ φ xr < τ + δ
    rw [hxr]
    exact ⟨hmr, by linarith⟩
  obtain ⟨c', hc'⟩ := h₁ W' (fun y hy => ha'm.trans_lt hy.1) xr hxrW'
    (Sc.X₁.presheaf.germ W₁ xr hxW₁ c)
  obtain ⟨W₂, hxW₂, iW, iW₁, hcc⟩ := TopCat.Presheaf.germ_eq _ xr hxrW' hxW₁ c' c hc'
  obtain ⟨ε, hε, hεW₂⟩ := hnbhd hxW₂
  rw [hxr] at hεW₂
  set ε' := min ε (min (t - r) (r - m)) with hε'
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'1 : ε' ≤ t - r := (min_le_right _ _).trans (min_le_left _ _)
  have hε'2 : ε' ≤ r - m := (min_le_right _ _).trans (min_le_right _ _)
  have hε'pos : 0 < ε' := lt_min hε (lt_min (by linarith) (by linarith))
  -- Glue `g` over `U₁ = {l < φ < r + ε'}` with the corrected local lift over
  -- `U₂ = {r - ε' < φ < τ + δ}`.
  have hU₁ : coordIoo φ hφ l (r + ε') ≤ coordIoo φ hφ l t :=
    coordIoo_le φ hφ le_rfl (by linarith)
  have hU₂W' : coordIoo φ hφ (r - ε') (τ + δ) ≤ W' := coordIoo_le φ hφ (by linarith) le_rfl
  have hU₂ : coordIoo φ hφ (r - ε') (τ + δ) ≤ W := hU₂W'.trans hW'W
  have hV : coordIoo φ hφ l (r + ε') ⊓ coordIoo φ hφ (r - ε') (τ + δ) ≤ W₂ :=
    fun x hx => hεW₂ ⟨by linarith [hx.2.1], by linarith [hx.1.2]⟩
  have hVW₁ := hV.trans (leOfHom iW₁)
  let σ₁ := Sc.X₂.presheaf.map (homOfLE hU₁).op g
  let σ₂ := Sc.X₂.presheaf.map (homOfLE hU₂).op h +
    Sc.f.hom.app _ (Sc.X₁.presheaf.map (homOfLE hU₂W').op c')
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
  -- The glued section is a lift over `{l < φ < τ + δ}` extending `g₀`, so `τ + δ ∈ A`.
  have hcover : coordIoo φ hφ l (τ + δ) ≤
      coordIoo φ hφ l (r + ε') ⊔ coordIoo φ hφ (r - ε') (τ + δ) := by
    intro x hx
    by_cases hxr' : φ x < r + ε'
    · exact Or.inl ⟨hx.1, hxr'⟩
    · exact Or.inr ⟨by linarith, hx.2⟩
  have hΩ₁ : coordIoo φ hφ l (r + ε') ≤ coordIoo φ hφ l (τ + δ) :=
    coordIoo_le φ hφ le_rfl (by linarith)
  have hΩ₂ : coordIoo φ hφ (r - ε') (τ + δ) ≤ coordIoo φ hφ l (τ + δ) :=
    coordIoo_le φ hφ (by linarith) le_rfl
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
        simp only [σ₂, map_add, gf, map_zero, add_zero, nat, hh, mm]
    · have hA' : coordIoo φ hφ l a' ≤ coordIoo φ hφ l (r + ε') :=
        coordIoo_le φ hφ le_rfl (by linarith)
      rw [← mm _ hA' hΩ₁ gl, hgl₁]
      simp only [σ₁, mm]
      exact hag
  have := le_csSup hbdd hmem
  linarith

variable (k) in
/-- The sweep along the coordinate `φ`: a lift over `{l < φ < a}` extends to a lift over
`{l < φ}` that agrees with it over `{l < φ < a'}`. Without a largest coordinate the lift is
glued along a cofinal increasing sequence of coordinates (`exists_glue_monotone`). -/
private theorem sweep_core
    (hconn : ∀ x y : X, ∀ z, φ x ≤ z → z ≤ φ y → ∃ w : X, φ w = z)
    (hnbhd : ∀ {W : Opens X} {x : X}, x ∈ W → ∃ δ > 0, coordIoo φ hφ (φ x - δ) (φ x + δ) ≤ W)
    (Sc : ShortComplex (X.Sheaf (ModuleCat.{0} k))) (hSc : Sc.Exact) {l a' a : ℝ}
    (h₁ : ∀ V : Opens X, (∀ y ∈ V, a' < φ y) → ∀ (x : X) (hx : x ∈ V),
      Function.Surjective (Sc.X₁.presheaf.germ V x hx))
    (s : Sc.X₃.presheaf.obj (op ⊤))
    (hs : ∀ x : X, ∃ (W : Opens X) (_ : x ∈ W) (t : Sc.X₂.presheaf.obj (op W)),
      Sc.g.hom.app _ t = Sc.X₃.presheaf.map (homOfLE le_top).op s)
    (hla' : l < a') (ha'a : a' < a) (ha' : ∃ x : X, φ x = a')
    (g₀ : Sc.X₂.presheaf.obj (op (coordIoo φ hφ l a)))
    (hg₀ : Sc.g.hom.app _ g₀ = Sc.X₃.presheaf.map (homOfLE le_top).op s) :
    ∃ g : Sc.X₂.presheaf.obj (op (coordIoi φ hφ l)),
      Sc.g.hom.app _ g = Sc.X₃.presheaf.map (homOfLE le_top).op s ∧
      Sc.X₂.presheaf.map (homOfLE (coordIoo_le_coordIoi φ hφ (q := a') le_rfl)).op g =
        Sc.X₂.presheaf.map (homOfLE (coordIoo_le φ hφ le_rfl ha'a.le)).op g₀ := by
  have mm := presheaf_map_map_apply (k := k) (X := X)
  have nat := @sheafHom_naturality_apply k _ X
  obtain ⟨xa', hxa'⟩ := ha'
  by_cases hmax : ∃ z : X, ∀ y : X, φ y ≤ φ z
  · -- A largest coordinate: one extension step past it.
    obtain ⟨z, hz⟩ := hmax
    obtain ⟨t, hzt, hat, g, hg, hag⟩ := extend_core k φ hφ hconn hnbhd Sc hSc h₁ s hs hla' ha'a
      ⟨xa', hxa'⟩ ⟨z, rfl⟩ g₀ hg₀
    have hle : coordIoi φ hφ l ≤ coordIoo φ hφ l t := fun y hy => ⟨hy, (hz y).trans_lt hzt⟩
    refine ⟨Sc.X₂.presheaf.map (homOfLE hle).op g, by rw [nat, hg, mm], ?_⟩
    rw [mm]
    exact hag
  push Not at hmax
  -- A cofinal sequence of points `u n` with increasing coordinates, starting at `a'`.
  obtain ⟨u, hu0, humono, hucof⟩ : ∃ u : ℕ → X, φ (u 0) = a' ∧ Monotone (fun n => φ (u n)) ∧
      ∀ x : X, ∃ n, φ x < φ (u n) := by
    have hw : ∀ q : ℚ, ∃ w : X, (∃ y : X, (q : ℝ) < φ y) → (q : ℝ) < φ w := fun q => by
      by_cases h : ∃ y : X, (q : ℝ) < φ y
      · obtain ⟨y, hy⟩ := h
        exact ⟨y, fun _ => hy⟩
      · exact ⟨xa', fun h' => absurd h' h⟩
    choose w hw using hw
    have hst : ∀ x z : X, φ x ≤ φ (if φ x ≤ φ z then z else x) ∧
        φ z ≤ φ (if φ x ≤ φ z then z else x) := by
      intro x z
      split_ifs with h
      · exact ⟨h, le_rfl⟩
      · exact ⟨le_rfl, (not_le.1 h).le⟩
    let u : ℕ → X := fun n => Nat.rec (motive := fun _ => X) xa'
      (fun n x => if φ x ≤ φ (w (Denumerable.ofNat ℚ n)) then w (Denumerable.ofNat ℚ n) else x) n
    have hsucc : ∀ n, φ (u n) ≤ φ (u (n + 1)) ∧ φ (w (Denumerable.ofNat ℚ n)) ≤ φ (u (n + 1)) :=
      fun n => hst (u n) (w (Denumerable.ofNat ℚ n))
    refine ⟨u, hxa', monotone_nat_of_le_succ fun n => (hsucc n).1, fun x => ?_⟩
    obtain ⟨y, hy⟩ := hmax x
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hy
    obtain ⟨n, hn⟩ : ∃ n, Denumerable.ofNat ℚ n = q := ⟨_, Denumerable.ofNat_encode q⟩
    refine ⟨n + 1, hxq.trans ((hw q ⟨y, hqy⟩).trans_le ?_)⟩
    have := (hsucc n).2
    rwa [hn] at this
  have hl : ∀ n, l < φ (u n) := fun n =>
    hla'.trans_le (by rw [← hu0]; exact humono (Nat.zero_le n))
  have hgerm : ∀ n, ∀ V : Opens X, (∀ y ∈ V, φ (u n) < φ y) → ∀ (x : X) (hx : x ∈ V),
      Function.Surjective (Sc.X₁.presheaf.germ V x hx) := fun n V hV =>
    h₁ V fun y hy => (by rw [← hu0]; exact humono (Nat.zero_le n) : a' ≤ φ (u n)).trans_lt
      (hV y hy)
  -- Successive lifts over `{l < φ < t n}` with `t n > φ (u n)`, each agreeing with the previous
  -- one over `{l < φ < φ (u n)}`.
  let St : ℕ → Type := fun n => {x : Σ t : ℝ, Sc.X₂.presheaf.obj (op (coordIoo φ hφ l t)) //
    φ (u n) < x.1 ∧ Sc.g.hom.app _ x.2 = Sc.X₃.presheaf.map (homOfLE le_top).op s}
  obtain ⟨t₀, ht₀, hat₀, G₀, hG₀, hagG₀⟩ := extend_core k φ hφ hconn hnbhd Sc hSc h₁ s hs hla'
    ha'a ⟨xa', hxa'⟩ ⟨u 0, rfl⟩ g₀ hg₀
  let x₀ : St 0 := ⟨⟨t₀, G₀⟩, ht₀, hG₀⟩
  have hstep : ∀ n (x : St n), ∃ x' : St (n + 1),
      Sc.X₂.presheaf.map (homOfLE (coordIoo_le φ hφ le_rfl
        ((humono (Nat.le_succ n)).trans x'.2.1.le))).op x'.1.2 =
      Sc.X₂.presheaf.map (homOfLE (coordIoo_le φ hφ le_rfl x.2.1.le)).op x.1.2 := by
    intro n x
    obtain ⟨t, hbt, hat, g, hg, hag⟩ := extend_core k φ hφ hconn hnbhd Sc hSc (a' := φ (u n))
      (a := x.1.1) (b := φ (u (n + 1))) (hgerm n) s hs (hl n) x.2.1 ⟨u n, rfl⟩
      ⟨u (n + 1), rfl⟩ x.1.2 x.2.2
    exact ⟨⟨⟨t, g⟩, hbt, hg⟩, hag⟩
  choose next hnext using hstep
  let sq : ∀ n, St n := fun n => Nat.rec (motive := St) x₀ (fun n x => next n x) n
  let U : ℕ → Opens X := fun n => coordIoo φ hφ l (φ (u n))
  have hU : Monotone U := fun i j hij => coordIoo_le φ hφ le_rfl (humono hij)
  obtain ⟨σ, hσ⟩ := exists_glue_monotone k Sc.X₂ U hU
    (fun n => Sc.X₂.presheaf.map (homOfLE (coordIoo_le φ hφ le_rfl (sq n).2.1.le)).op (sq n).1.2)
    (fun n => by
      have := hnext n (sq n)
      simp only [mm]
      exact this)
  have hcov : coordIoi φ hφ l ≤ ⨆ n, U n := fun y hy => by
    obtain ⟨n, hn⟩ := hucof y
    exact Opens.mem_iSup.2 ⟨n, hy, hn⟩
  have hσlift : Sc.g.hom.app _ σ = Sc.X₃.presheaf.map (homOfLE le_top).op s := by
    refine TopCat.Sheaf.eq_of_locally_eq Sc.X₃ U _ _ fun n => ?_
    change Sc.X₃.presheaf.map (homOfLE (le_iSup U n)).op _ =
      Sc.X₃.presheaf.map (homOfLE (le_iSup U n)).op _
    rw [← nat, hσ n, nat]
    exact (congrArg (Sc.X₃.presheaf.map _) (sq n).2.2).trans ((mm _ _ _ _).trans (mm _ _ _ _).symm)
  refine ⟨Sc.X₂.presheaf.map (homOfLE hcov).op σ, by rw [nat, hσlift, mm], ?_⟩
  have hA0 : coordIoo φ hφ l a' ≤ U 0 := coordIoo_le φ hφ le_rfl hu0.ge
  have e := congrArg (Sc.X₂.presheaf.map (homOfLE hA0).op) (hσ 0)
  simp only [mm] at e ⊢
  rw [e]
  exact hagG₀

end Coordinate

variable (k) in
/-- **The extension step, rightward.** Let `S ⊆ ℝ` be order-connected, `X₁ ⟶ X₂ ⟶ X₃` an exact
complex of sheaves of `k`-modules on `S`, and `s` a global section of `X₃` that lifts to `X₂`
near every point. Let `l < a' < a` with `a' ∈ S`, let `X₁` be germ-surjective on the opens
whose points lie above `a'`, and let `g₀` lift `s` over `S ∩ (l, a)`. Then for every `b ∈ S`
there are `t > b` (with `t ≥ a`) and a lift of `s` over `S ∩ (l, t)` that agrees with `g₀` over
`S ∩ (l, a')`. -/
theorem exists_section_lift_extend_right {S : Set ℝ} (hS : S.OrdConnected)
    (Sc : ShortComplex ((TopCat.of S).Sheaf (ModuleCat.{0} k))) (hSc : Sc.Exact) {l a' a b : ℝ}
    (h₁ : ∀ V : Opens (TopCat.of S), (∀ y ∈ V, a' < (y : ℝ)) → ∀ (x : TopCat.of S) (hx : x ∈ V),
      Function.Surjective (Sc.X₁.presheaf.germ V x hx))
    (s : Sc.X₃.presheaf.obj (op ⊤))
    (hs : ∀ x : TopCat.of S, ∃ (W : Opens (TopCat.of S)) (_ : x ∈ W)
      (t : Sc.X₂.presheaf.obj (op W)),
      Sc.g.hom.app _ t = Sc.X₃.presheaf.map (homOfLE le_top).op s)
    (hla' : l < a') (ha'a : a' < a) (ha' : a' ∈ S) (hb : b ∈ S)
    (g₀ : Sc.X₂.presheaf.obj (op (openIoo S l a)))
    (hg₀ : Sc.g.hom.app _ g₀ = Sc.X₃.presheaf.map (homOfLE le_top).op s) :
    ∃ t, b < t ∧ ∃ (hat : a ≤ t) (g : Sc.X₂.presheaf.obj (op (openIoo S l t))),
      Sc.g.hom.app _ g = Sc.X₃.presheaf.map (homOfLE le_top).op s ∧
      Sc.X₂.presheaf.map (homOfLE (openIoo_le_openIoo le_rfl (ha'a.le.trans hat))).op g =
        Sc.X₂.presheaf.map (homOfLE (openIoo_le_openIoo le_rfl ha'a.le)).op g₀ :=
  extend_core k (X := TopCat.of S) (fun y => (y : ℝ)) continuous_subtype_val
    (fun x y z hx hy => ⟨⟨z, hS.out x.2 y.2 ⟨hx, hy⟩⟩, rfl⟩) (fun hx => exists_openIoo_le hx)
    Sc hSc h₁ s hs hla' ha'a ⟨⟨a', ha'⟩, rfl⟩ ⟨⟨b, hb⟩, rfl⟩ g₀ hg₀

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
        Sc.X₂.presheaf.map (homOfLE (openIoo_le_openIoo le_rfl ha'a.le)).op g₀ :=
  exists_section_lift_extend_right k hS Sc hSc (fun V _ => h₁ V) s hs hla' ha'a ha' hb g₀ hg₀

variable (k) in
/-- **The extension step, leftward.** Let `S ⊆ ℝ` be order-connected, `X₁ ⟶ X₂ ⟶ X₃` an exact
complex of sheaves of `k`-modules on `S`, and `s` a global section of `X₃` that lifts to `X₂`
near every point. Let `a < a' < r` with `a' ∈ S`, let `X₁` be germ-surjective on the opens
whose points lie below `a'`, and let `g₀` lift `s` over `S ∩ (a, r)`. Then for every `b ∈ S`
there are `t < b` (with `t ≤ a`) and a lift of `s` over `S ∩ (t, r)` that agrees with `g₀` over
`S ∩ (a', r)`. This is the rightward step for the coordinate `-x`. -/
theorem exists_section_lift_extend_left {S : Set ℝ} (hS : S.OrdConnected)
    (Sc : ShortComplex ((TopCat.of S).Sheaf (ModuleCat.{0} k))) (hSc : Sc.Exact) {r a' a b : ℝ}
    (h₁ : ∀ V : Opens (TopCat.of S), (∀ y ∈ V, (y : ℝ) < a') → ∀ (x : TopCat.of S) (hx : x ∈ V),
      Function.Surjective (Sc.X₁.presheaf.germ V x hx))
    (s : Sc.X₃.presheaf.obj (op ⊤))
    (hs : ∀ x : TopCat.of S, ∃ (W : Opens (TopCat.of S)) (_ : x ∈ W)
      (t : Sc.X₂.presheaf.obj (op W)),
      Sc.g.hom.app _ t = Sc.X₃.presheaf.map (homOfLE le_top).op s)
    (ha'r : a' < r) (haa' : a < a') (ha' : a' ∈ S) (hb : b ∈ S)
    (g₀ : Sc.X₂.presheaf.obj (op (openIoo S a r)))
    (hg₀ : Sc.g.hom.app _ g₀ = Sc.X₃.presheaf.map (homOfLE le_top).op s) :
    ∃ t, t < b ∧ ∃ (hta : t ≤ a) (g : Sc.X₂.presheaf.obj (op (openIoo S t r))),
      Sc.g.hom.app _ g = Sc.X₃.presheaf.map (homOfLE le_top).op s ∧
      Sc.X₂.presheaf.map (homOfLE (openIoo_le_openIoo (hta.trans haa'.le) le_rfl)).op g =
        Sc.X₂.presheaf.map (homOfLE (openIoo_le_openIoo haa'.le le_rfl)).op g₀ := by
  have mm := presheaf_map_map_apply (k := k) (X := TopCat.of S)
  have nat := @sheafHom_naturality_apply k _ (TopCat.of S)
  have hφ : Continuous fun y : TopCat.of S => -(y : ℝ) := continuous_subtype_val.neg
  have hle₀ : coordIoo (fun y : TopCat.of S => -(y : ℝ)) hφ (-r) (-a) ≤ openIoo S a r :=
    fun x hx => by
      change -r < -(x : ℝ) ∧ -(x : ℝ) < -a at hx
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  obtain ⟨t', hbt', hat', g', hg', hag'⟩ := extend_core k (X := TopCat.of S)
    (fun y => -(y : ℝ)) hφ
    (fun x y z hx hy => by
      change -(x : ℝ) ≤ z at hx
      change z ≤ -(y : ℝ) at hy
      exact ⟨⟨-z, hS.out y.2 x.2 ⟨by linarith, by linarith⟩⟩, neg_neg z⟩)
    (fun {_W} {x} hx => by
      obtain ⟨δ, hδ, hδW⟩ := exists_openIoo_le hx
      refine ⟨δ, hδ, fun y hy => hδW ?_⟩
      change -(x : ℝ) - δ < -(y : ℝ) ∧ -(y : ℝ) < -(x : ℝ) + δ at hy
      exact ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    Sc hSc (l := -r) (a' := -a') (a := -a) (b := -b)
    (fun V hV => h₁ V fun y hy => by
      have := hV y hy
      change -a' < -(y : ℝ) at this
      linarith)
    s hs (by linarith) (by linarith) ⟨⟨a', ha'⟩, rfl⟩ ⟨⟨b, hb⟩, rfl⟩
    (Sc.X₂.presheaf.map (homOfLE hle₀).op g₀) (by rw [nat, hg₀, mm])
  have hle₁ : openIoo S (-t') r ≤ coordIoo (fun y : TopCat.of S => -(y : ℝ)) hφ (-r) t' :=
    fun x hx => by
      change -t' < (x : ℝ) ∧ (x : ℝ) < r at hx
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hle₂ : openIoo S a' r ≤ coordIoo (fun y : TopCat.of S => -(y : ℝ)) hφ (-r) (-a') :=
    fun x hx => by
      change a' < (x : ℝ) ∧ (x : ℝ) < r at hx
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  refine ⟨-t', by linarith, by linarith, Sc.X₂.presheaf.map (homOfLE hle₁).op g',
    by rw [nat, hg', mm], ?_⟩
  have e := congrArg (Sc.X₂.presheaf.map (homOfLE hle₂).op) hag'
  simp only [mm] at e ⊢
  exact e

variable (k) in
/-- **Section lifting on an order-connected subset of the real line.** Let `S ⊆ ℝ` be
order-connected (an open, half-open, closed or unbounded interval, or `ℝ`), `c ∈ ℝ`, and
`X₁ ⟶ X₂ ⟶ X₃` an exact complex of sheaves of `k`-modules on `S` such that `X₁` is
germ-surjective on every open avoiding `c`. A global section of `X₃` that lifts to `X₂` near
every point lifts to a global section of `X₂`.

The proof starts from a local lift at a base point `x₀` (the point `c` when `c ∈ S`) and sweeps
it to the right (`exists_section_lift_extend_right` and `exists_glue_monotone`) and to the left
(the same for the coordinate `-x`), gluing the two sweeps near `x₀`. -/
theorem exists_section_lift_ordConnected {S : Set ℝ} (hS : S.OrdConnected) (c : ℝ)
    (Sc : ShortComplex ((TopCat.of S).Sheaf (ModuleCat.{0} k))) (hSc : Sc.Exact)
    (h₁ : ∀ V : Opens (TopCat.of S), (∀ y ∈ V, (y : ℝ) ≠ c) → ∀ (x : TopCat.of S) (hx : x ∈ V),
      Function.Surjective (Sc.X₁.presheaf.germ V x hx))
    (s : Sc.X₃.presheaf.obj (op ⊤))
    (hs : ∀ x : TopCat.of S, ∃ (W : Opens (TopCat.of S)) (_ : x ∈ W)
      (t : Sc.X₂.presheaf.obj (op W)),
      Sc.g.hom.app _ t = Sc.X₃.presheaf.map (homOfLE le_top).op s) :
    ∃ t : Sc.X₂.presheaf.obj (op ⊤), Sc.g.hom.app _ t = s := by
  have mm := presheaf_map_map_apply (k := k) (X := TopCat.of S)
  have nat := @sheafHom_naturality_apply k _ (TopCat.of S)
  rcases S.eq_empty_or_nonempty with hSe | ⟨y₀, hy₀⟩
  · -- The empty set: there are no points, so every section vanishes.
    refine ⟨0, ?_⟩
    rw [map_zero]
    refine (TopCat.Presheaf.section_ext Sc.X₃ ⊤ _ _ (fun x _ => ?_)).symm
    exact (Set.eq_empty_iff_forall_notMem.1 hSe _ x.2).elim
  -- A base point `x₀`, equal to `c` when `c ∈ S`.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : TopCat.of S, ∀ y : TopCat.of S, (y : ℝ) = c → (y : ℝ) = x₀ := by
    by_cases hc : c ∈ S
    · exact ⟨⟨c, hc⟩, fun y hy => hy⟩
    · refine ⟨⟨y₀, hy₀⟩, fun y hy => ?_⟩
      exact absurd ((congrArg (· ∈ S) hy).mp y.2) hc
  have hne : ∀ y : TopCat.of S, (y : ℝ) ≠ x₀ → (y : ℝ) ≠ c := fun y hy hyc => hy (hx₀ y hyc)
  obtain ⟨W, hxW, h, hh⟩ := hs x₀
  obtain ⟨δ, hδ, hδW⟩ := exists_openIoo_le hxW
  have hφ : Continuous fun y : TopCat.of S => -(y : ℝ) := continuous_subtype_val.neg
  -- The rightward sweep: a lift over `S ∩ (x₀ - δ, ∞)` agreeing with `h` near `x₀`.
  obtain ⟨ρ, hxρ, hρ, gR, hgR, hagR⟩ : ∃ ρ, (x₀ : ℝ) < ρ ∧ ρ < x₀ + δ ∧
      ∃ g : Sc.X₂.presheaf.obj
        (op (coordIoi (fun y : TopCat.of S => (y : ℝ)) continuous_subtype_val (x₀ - δ))),
      Sc.g.hom.app _ g = Sc.X₃.presheaf.map (homOfLE le_top).op s ∧
      ∀ (h₁ : openIoo S (x₀ - δ) ρ ≤
          coordIoi (fun y : TopCat.of S => (y : ℝ)) continuous_subtype_val (x₀ - δ))
        (h₂ : openIoo S (x₀ - δ) ρ ≤ W),
        Sc.X₂.presheaf.map (homOfLE h₁).op g = Sc.X₂.presheaf.map (homOfLE h₂).op h := by
    have hle : coordIoo (fun y : TopCat.of S => (y : ℝ)) continuous_subtype_val (x₀ - δ)
        (x₀ + δ / 2) ≤ W :=
      (openIoo_le_openIoo le_rfl (by linarith)).trans hδW
    by_cases hpt : ∃ a' ∈ S, (x₀ : ℝ) < a' ∧ a' < x₀ + δ / 2
    · obtain ⟨a', ha'S, hxa', ha'δ⟩ := hpt
      obtain ⟨g, hg, hag⟩ := sweep_core k (X := TopCat.of S) (fun y => (y : ℝ))
        continuous_subtype_val (fun x y z hx hy => ⟨⟨z, hS.out x.2 y.2 ⟨hx, hy⟩⟩, rfl⟩)
        (fun hx => exists_openIoo_le hx) Sc hSc (l := x₀ - δ) (a' := a') (a := x₀ + δ / 2)
        (fun V hV => h₁ V fun y hy => hne y (hxa'.trans (hV y hy)).ne')
        s hs (by linarith) ha'δ ⟨⟨a', ha'S⟩, rfl⟩
        (Sc.X₂.presheaf.map (homOfLE hle).op h) (by rw [nat, hh, mm])
      refine ⟨a', hxa', by linarith, g, hg, fun h₁ h₂ => ?_⟩
      have e := hag
      simp only [mm] at e
      exact e
    · -- No point of `S` in `(x₀, x₀ + δ/2)`, hence none above `x₀`.
      push Not at hpt
      have hbd : ∀ y : TopCat.of S, (y : ℝ) < x₀ + δ / 2 := fun y => by
        by_contra hy
        push Not at hy
        exact absurd (hpt (x₀ + δ / 4)
          (hS.out x₀.2 y.2 ⟨by linarith, by linarith⟩) (by linarith)) (by linarith)
      have hle'' : coordIoi (fun y : TopCat.of S => (y : ℝ)) continuous_subtype_val (x₀ - δ) ≤
          coordIoo (fun y : TopCat.of S => (y : ℝ)) continuous_subtype_val (x₀ - δ) (x₀ + δ / 2) :=
        fun y hy => ⟨hy, hbd y⟩
      have hle' := hle''.trans hle
      refine ⟨x₀ + δ / 2, by linarith, by linarith, Sc.X₂.presheaf.map (homOfLE hle').op h,
        by rw [nat, hh, mm], fun h₁ h₂ => by rw [mm]⟩
  -- The leftward sweep: a lift over `S ∩ (-∞, x₀ + δ)` agreeing with `h` near `x₀`.
  obtain ⟨lam, hlam, hlx, gL, hgL, hagL⟩ : ∃ lam, (x₀ : ℝ) - δ < lam ∧ lam < x₀ ∧
      ∃ g : Sc.X₂.presheaf.obj
        (op (coordIoi (fun y : TopCat.of S => -(y : ℝ)) hφ (-(x₀ + δ)))),
      Sc.g.hom.app _ g = Sc.X₃.presheaf.map (homOfLE le_top).op s ∧
      ∀ (h₁ : openIoo S lam (x₀ + δ) ≤
          coordIoi (fun y : TopCat.of S => -(y : ℝ)) hφ (-(x₀ + δ)))
        (h₂ : openIoo S lam (x₀ + δ) ≤ W),
        Sc.X₂.presheaf.map (homOfLE h₁).op g = Sc.X₂.presheaf.map (homOfLE h₂).op h := by
    have hle : coordIoo (fun y : TopCat.of S => -(y : ℝ)) hφ (-(x₀ + δ)) (-(x₀ - δ / 2)) ≤ W :=
      fun y hy => hδW (by
        change -(x₀ + δ) < -(y : ℝ) ∧ -(y : ℝ) < -(x₀ - δ / 2) at hy
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    by_cases hpt : ∃ a' ∈ S, (x₀ : ℝ) - δ / 2 < a' ∧ a' < x₀
    · obtain ⟨a', ha'S, ha'δ, ha'x⟩ := hpt
      obtain ⟨g, hg, hag⟩ := sweep_core k (X := TopCat.of S) (fun y => -(y : ℝ)) hφ
        (fun x y z hx hy => by
          change -(x : ℝ) ≤ z at hx
          change z ≤ -(y : ℝ) at hy
          exact ⟨⟨-z, hS.out y.2 x.2 ⟨by linarith, by linarith⟩⟩, neg_neg z⟩)
        (fun {_W} {x} hx => by
          obtain ⟨δ', hδ', hδW'⟩ := exists_openIoo_le hx
          refine ⟨δ', hδ', fun y hy => hδW' ?_⟩
          change -(x : ℝ) - δ' < -(y : ℝ) ∧ -(y : ℝ) < -(x : ℝ) + δ' at hy
          exact ⟨by linarith [hy.2], by linarith [hy.1]⟩)
        Sc hSc (l := -(x₀ + δ)) (a' := -a') (a := -(x₀ - δ / 2))
        (fun V hV => h₁ V fun y hy => hne y (by
          have := hV y hy
          change -a' < -(y : ℝ) at this
          exact (show (y : ℝ) < x₀ by linarith).ne))
        s hs (by linarith) (by linarith) ⟨⟨a', ha'S⟩, rfl⟩
        (Sc.X₂.presheaf.map (homOfLE hle).op h) (by rw [nat, hh, mm])
      refine ⟨a', by linarith, ha'x, g, hg, fun h₁ h₂ => ?_⟩
      have hle₂ : openIoo S a' (x₀ + δ) ≤
          coordIoo (fun y : TopCat.of S => -(y : ℝ)) hφ (-(x₀ + δ)) (-a') := fun y hy => by
        change a' < (y : ℝ) ∧ (y : ℝ) < x₀ + δ at hy
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have e := congrArg (Sc.X₂.presheaf.map (homOfLE hle₂).op) hag
      simp only [mm] at e
      exact e
    · push Not at hpt
      have hbd : ∀ y : TopCat.of S, (x₀ : ℝ) - δ / 2 < y := fun y => by
        by_contra hy
        push Not at hy
        exact absurd (hpt (x₀ - δ / 4)
          (hS.out y.2 x₀.2 ⟨by linarith, by linarith⟩) (by linarith)) (by linarith)
      have hle' : coordIoi (fun y : TopCat.of S => -(y : ℝ)) hφ (-(x₀ + δ)) ≤ W :=
        fun y hy => hδW (by
          change -(x₀ + δ) < -(y : ℝ) at hy
          exact ⟨by linarith [hbd y], by linarith⟩)
      refine ⟨x₀ - δ / 2, by linarith, by linarith, Sc.X₂.presheaf.map (homOfLE hle').op h,
        by rw [nat, hh, mm], fun h₁ h₂ => by rw [mm]⟩
  -- Glue the two sweeps over `A = S ∩ (lam, ∞)` and `B = S ∩ (-∞, ρ)`.
  let A := coordIoi (fun y : TopCat.of S => (y : ℝ)) continuous_subtype_val lam
  let B := coordIoi (fun y : TopCat.of S => -(y : ℝ)) hφ (-ρ)
  have hAR : A ≤ coordIoi (fun y : TopCat.of S => (y : ℝ)) continuous_subtype_val (x₀ - δ) :=
    fun y hy => by
      change lam < (y : ℝ) at hy
      change (x₀ : ℝ) - δ < y
      linarith
  have hBL : B ≤ coordIoi (fun y : TopCat.of S => -(y : ℝ)) hφ (-(x₀ + δ)) := fun y hy => by
    change -ρ < -(y : ℝ) at hy
    change -(x₀ + δ) < -(y : ℝ)
    linarith
  have hAB : A ⊓ B ≤ openIoo S lam ρ := fun y hy => by
    have h1 : lam < (y : ℝ) := hy.1
    have h2 : -ρ < -(y : ℝ) := hy.2
    exact ⟨h1, by linarith⟩
  have hABR : openIoo S lam ρ ≤ openIoo S (x₀ - δ) ρ := openIoo_le_openIoo hlam.le le_rfl
  have hABL : openIoo S lam ρ ≤ openIoo S lam (x₀ + δ) := openIoo_le_openIoo le_rfl hρ.le
  have hWR : openIoo S (x₀ - δ) ρ ≤ W := (openIoo_le_openIoo le_rfl hρ.le).trans hδW
  have hWL : openIoo S lam (x₀ + δ) ≤ W := (openIoo_le_openIoo hlam.le le_rfl).trans hδW
  have hR₁ : openIoo S (x₀ - δ) ρ ≤
      coordIoi (fun y : TopCat.of S => (y : ℝ)) continuous_subtype_val (x₀ - δ) :=
    fun y hy => hy.1
  have hL₁ : openIoo S lam (x₀ + δ) ≤ coordIoi (fun y : TopCat.of S => -(y : ℝ)) hφ (-(x₀ + δ)) :=
    fun y hy => by
      change -(x₀ + δ) < -(y : ℝ)
      have := hy.2
      linarith
  have eR : Sc.X₂.presheaf.map (homOfLE (inf_le_left.trans hAR : A ⊓ B ≤ _)).op gR =
      Sc.X₂.presheaf.map (homOfLE ((hAB.trans hABR).trans hWR)).op h := by
    rw [← mm _ (hAB.trans hABR) hR₁, hagR hR₁ hWR, mm]
  have eL : Sc.X₂.presheaf.map (homOfLE (inf_le_right.trans hBL : A ⊓ B ≤ _)).op gL =
      Sc.X₂.presheaf.map (homOfLE ((hAB.trans hABL).trans hWL)).op h := by
    rw [← mm _ (hAB.trans hABL) hL₁, hagL hL₁ hWL, mm]
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_glue₂ Sc.X₂ (Sc.X₂.presheaf.map (homOfLE hAR).op gR)
    (Sc.X₂.presheaf.map (homOfLE hBL).op gL) (by rw [mm, mm, eR, eL])
  have htop : (⊤ : Opens (TopCat.of S)) ≤ A ⊔ B := fun y _ => by
    by_cases hy : lam < (y : ℝ)
    · exact Or.inl hy
    · refine Or.inr ?_
      change -ρ < -(y : ℝ)
      linarith
  refine ⟨Sc.X₂.presheaf.map (homOfLE htop).op σ, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq₂ Sc.X₃ (homOfLE (le_top : A ≤ ⊤))
    (homOfLE (le_top : B ≤ ⊤)) htop _ _ ?_ ?_
  · rw [← nat, mm, hσ₁, nat, hgR, mm]
  · rw [← nat, mm, hσ₂, nat, hgL, mm]

variable (k) in
/-- **Exactness of global sections on an order-connected subset of the real line.** On an
order-connected `S ⊆ ℝ`, let `L₀ ⟶ L₁ ⟶ L₂ ⟶ L₃` be a complex of sheaves of `k`-modules, exact
at `L₁` and `L₂`, with `L₀` germ-surjective on every open avoiding a point `c`. Then a global
section of `L₂` that maps to zero in `L₃` is the image of a global section of `L₁`. -/
theorem sections_exact_ordConnected {S : Set ℝ} (hS : S.OrdConnected) (c : ℝ)
    {L₀ L₁ L₂ L₃ : (TopCat.of S).Sheaf (ModuleCat.{0} k)}
    (d₀ : L₀ ⟶ L₁) (d₁ : L₁ ⟶ L₂) (d₂ : L₂ ⟶ L₃) (w₀ : d₀ ≫ d₁ = 0) (w₁ : d₁ ≫ d₂ = 0)
    (h₁ : (ShortComplex.mk d₀ d₁ w₀).Exact) (h₂ : (ShortComplex.mk d₁ d₂ w₁).Exact)
    (hL₀ : ∀ V : Opens (TopCat.of S), (∀ y ∈ V, (y : ℝ) ≠ c) → ∀ (x : TopCat.of S) (hx : x ∈ V),
      Function.Surjective (L₀.presheaf.germ V x hx))
    (s : L₂.presheaf.obj (op ⊤)) (hs : d₂.hom.app _ s = 0) :
    ∃ t : L₁.presheaf.obj (op ⊤), d₁.hom.app _ t = s :=
  exists_section_lift_ordConnected k hS c (ShortComplex.mk d₀ d₁ w₀) h₁ hL₀ s (fun x => by
    obtain ⟨W, hxW, _, t, ht⟩ :=
      exists_local_preimage_of_exact k (ShortComplex.mk d₁ d₂ w₁) h₂ s hs x trivial
    exact ⟨W, hxW, t, ht⟩)

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
    ∃ t : Sc.X₂.presheaf.obj (op ⊤), Sc.g.hom.app _ t = s :=
  exists_section_lift_ordConnected k Set.ordConnected_Icc u Sc hSc (fun V _ => h₁ V) s hs

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
  sections_exact_ordConnected k Set.ordConnected_Icc u d₀ d₁ d₂ w₀ w₁ h₁ h₂ (fun V _ => hL₀ V) s
    hs

end TDA.Sheaf
