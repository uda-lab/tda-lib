import TDA.Sheaf.RealLine
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Topology.Order.IntermediateValue

/-!
# Interval-local constancy and transport on the real line

Let `k` be a ring and `F` a sheaf of `k`-modules on `realLine`. A *convex* open is an open subset
of `ℝ` that is order-connected (`Set.OrdConnected`): an open interval, possibly unbounded.

* `IsLocallyConstantOn F U`: every point of `U` has an open neighbourhood `N ⊆ U` such that
  restriction between nested, nonempty, convex opens inside `N` is an isomorphism. This is the
  definition of local constancy used for constructible sheaves on the real line (#1181). It is
  intended to be equivalent, on `ℝ`, to "locally isomorphic to a constant sheaf"; that
  equivalence is not proved in Lean (follow-up #1250). `IsLocallyConstantOn.mono` restricts it
  to a smaller open set.
* `restrict_isIso_of_isLocallyConstantOn` (trivialisation on an interval): if `F` is locally
  constant on a convex open `W`, then restriction `F(W) ⟶ F(V)` to every nonempty convex open
  `V ⊆ W` is an isomorphism.
* `transportIso`: for nonempty convex opens `V₁, V₂ ⊆ W`, the resulting isomorphism
  `F(V₁) ≅ F(V₂)` through `F(W)`. It is restriction when `V₂ ⊆ V₁`
  (`transportIso_hom_eq_map`) and composes (`transportIso_trans`).
* `isIso_germ_of_isIso_map`: for a presheaf of `k`-modules, if restriction from an open `T` to
  every convex open neighbourhood of `x` inside `T` is an isomorphism, then so is the germ map
  `F(T) ⟶ F_x`. With the trivialisation this gives `isIso_germ_of_isLocallyConstantOn`:
  sections over a convex open on which `F` is locally constant are isomorphic to every stalk
  there.

The proof of the trivialisation follows the plan of the #1181 probe. Call an open `G` good if
restriction from `G` to every nonempty convex open inside it is an isomorphism. The union of two
good convex opens that meet is good, by the binary gluing square of `F`
(`TopCat.Sheaf.isLimitPullbackCone`). By `IsPreconnected.induction₂'`, any two points of `W` lie
in a good convex open inside `W`. Gluing over the good convex opens that contain a fixed good
convex open `G` (`TopCat.Sheaf.existsUnique_gluing'`, `TopCat.Sheaf.eq_of_locally_eq'`) shows
that `F(W) ⟶ F(G)` is bijective.
-/

set_option autoImplicit false

open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf.LocalSystem

/-! ### Restrictions between nested opens -/

section Restriction

variable {X : TopCat} {C : Type*} [Category C]

/-- Two successive restrictions are one restriction. -/
private theorem map_comp_map (F : X.Presheaf C) {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) :
    F.map (homOfLE h₁).op ≫ F.map (homOfLE h₂).op = F.map (homOfLE (h₂.trans h₁)).op := by
  rw [← F.map_comp]
  rfl

/-- If `D ⊆ A ∪ B` and `F(B) ⟶ F(A ∩ B)` is an isomorphism, so is `F(D) ⟶ F(A)`, where
`A, B ⊆ D`. This is the binary gluing square of `F`. -/
private theorem isIso_map_of_le_sup (F : X.Sheaf C) {A B D : Opens X} (hA : A ≤ D) (hB : B ≤ D)
    (hD : D ≤ A ⊔ B) (h : IsIso (F.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op)) :
    IsIso (F.presheaf.map (homOfLE hA).op) := by
  obtain rfl : D = A ⊔ B := le_antisymm hD (sup_le hA hB)
  exact (IsPullback.of_isLimit (TopCat.Sheaf.isLimitPullbackCone F A B)).isIso_fst_of_isIso h

end Restriction

/-! ### Convex balls -/

/-- The open ball `(x - ε, x + ε)` as an open of the real line. -/
private def ballOpen (x ε : ℝ) : Opens realLine := ⟨Metric.ball x ε, Metric.isOpen_ball⟩

private theorem ordConnected_ballOpen (x ε : ℝ) :
    ((ballOpen x ε : Opens realLine) : Set ℝ).OrdConnected := by
  show (Metric.ball x ε).OrdConnected
  rw [Real.ball_eq_Ioo]
  exact Set.ordConnected_Ioo

private theorem mem_ballOpen_self {x ε : ℝ} (hε : 0 < ε) : x ∈ ballOpen x ε :=
  Metric.mem_ball_self hε

/-- Every open neighbourhood of `x` contains a convex ball around `x`. -/
private theorem exists_ballOpen_le {U : Opens realLine} {x : ℝ} (hx : x ∈ U) :
    ∃ ε > 0, ballOpen x ε ≤ U := by
  obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  exact ⟨ε, hε, h⟩

/-! ### Interval-local constancy -/

variable {k : Type} [Ring k]

/-- **Interval-local constancy.** A sheaf `F` of `k`-modules on the real line is locally
constant on `U ⊆ ℝ` when every `x ∈ U` has an open neighbourhood `N ⊆ U` such that, for all
nonempty convex (order-connected) opens `V ⊆ W ⊆ N`, the restriction `F(W) ⟶ F(V)` is an
isomorphism.

This definition is intended to be equivalent, on `ℝ`, to "locally isomorphic to a constant
sheaf". That equivalence is **not yet proved in Lean**; the bridge is follow-up #1250. -/
def IsLocallyConstantOn (F : TopCat.Sheaf (ModuleCat.{0} k) realLine) (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∃ N : Opens realLine, x ∈ N ∧ (N : Set ℝ) ⊆ U ∧
    ∀ ⦃V W : Opens realLine⦄ (hVW : V ≤ W), (V : Set ℝ).Nonempty → (V : Set ℝ).OrdConnected →
      (W : Set ℝ).OrdConnected → W ≤ N → IsIso (F.presheaf.map (homOfLE hVW).op)

/-- Local constancy passes to open subsets. -/
theorem IsLocallyConstantOn.mono {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} {U U' : Set ℝ}
    (hF : IsLocallyConstantOn F U) (hU' : IsOpen U') (h : U' ⊆ U) :
    IsLocallyConstantOn F U' := by
  intro x hx
  obtain ⟨N, hxN, -, hN⟩ := hF x (h hx)
  refine ⟨N ⊓ ⟨U', hU'⟩, ⟨hxN, hx⟩, fun y hy => hy.2, ?_⟩
  intro V W hVW hVne hVc hWc hWN
  exact hN hVW hVne hVc hWc (hWN.trans inf_le_left)

section Trivialisation

variable {F : TopCat.Sheaf (ModuleCat.{0} k) realLine}

/-- `G` is good for `F`: restriction from `G` to every nonempty convex open inside it is an
isomorphism. -/
private def Good (F : TopCat.Sheaf (ModuleCat.{0} k) realLine) (G : Opens realLine) : Prop :=
  ∀ ⦃V : Opens realLine⦄ (h : V ≤ G), (V : Set ℝ).Nonempty → (V : Set ℝ).OrdConnected →
    IsIso (F.presheaf.map (homOfLE h).op)

/-- Inside a good open, restriction between nested nonempty convex opens is an isomorphism. -/
private theorem Good.isIso_map {G V' V : Opens realLine} (hG : Good F G) (h₁ : V' ≤ G)
    (h₂ : V ≤ V') (hV'ne : (V' : Set ℝ).Nonempty) (hV'c : (V' : Set ℝ).OrdConnected)
    (hVne : (V : Set ℝ).Nonempty) (hVc : (V : Set ℝ).OrdConnected) :
    IsIso (F.presheaf.map (homOfLE h₂).op) := by
  have e₁ := hG h₁ hV'ne hV'c
  have e := hG (h₂.trans h₁) hVne hVc
  rw [← map_comp_map F.presheaf h₁ h₂] at e
  exact IsIso.of_isIso_comp_left (F.presheaf.map (homOfLE h₁).op) _

/-- The union of two good convex opens that meet is good. -/
private theorem good_sup {G₁ G₂ : Opens realLine} (h₁ : Good F G₁) (h₂ : Good F G₂)
    (c₁ : (G₁ : Set ℝ).OrdConnected) (c₂ : (G₂ : Set ℝ).OrdConnected)
    (hne : ((G₁ ⊓ G₂ : Opens realLine) : Set ℝ).Nonempty) : Good F (G₁ ⊔ G₂) := by
  have hIc : ((G₁ ⊓ G₂ : Opens realLine) : Set ℝ).OrdConnected := by
    rw [Opens.coe_inf]
    exact c₁.inter c₂
  have hne' : ((G₂ ⊓ G₁ : Opens realLine) : Set ℝ).Nonempty := by
    rw [inf_comm]
    exact hne
  have hIc' : ((G₂ ⊓ G₁ : Opens realLine) : Set ℝ).OrdConnected := by
    rw [inf_comm]
    exact hIc
  have e₁ : IsIso (F.presheaf.map (homOfLE (le_sup_left : G₁ ≤ G₁ ⊔ G₂)).op) :=
    isIso_map_of_le_sup F le_sup_left le_sup_right le_rfl (h₂ inf_le_right hne hIc)
  have e₂ : IsIso (F.presheaf.map (homOfLE (le_sup_right : G₂ ≤ G₁ ⊔ G₂)).op) :=
    isIso_map_of_le_sup F le_sup_right le_sup_left (sup_comm G₁ G₂).le
      (h₁ inf_le_right hne' hIc')
  intro V hV hVne hVc
  -- Restriction to `V` through a piece containing it.
  have through : ∀ {G : Opens realLine} (hG : G ≤ G₁ ⊔ G₂) (hVG : V ≤ G),
      IsIso (F.presheaf.map (homOfLE hG).op) → IsIso (F.presheaf.map (homOfLE hVG).op) →
        IsIso (F.presheaf.map (homOfLE hV).op) := by
    intro G hG hVG e e'
    have hc : F.presheaf.map (homOfLE hV).op =
        F.presheaf.map (homOfLE hG).op ≫ F.presheaf.map (homOfLE hVG).op :=
      (map_comp_map F.presheaf hG hVG).symm
    rw [hc]
    infer_instance
  by_cases hV₁ : V ≤ G₁
  · exact through le_sup_left hV₁ e₁ (h₁ hV₁ hVne hVc)
  by_cases hV₂ : V ≤ G₂
  · exact through le_sup_right hV₂ e₂ (h₂ hV₂ hVne hVc)
  -- Otherwise `V` meets both pieces, hence their intersection.
  have hsub : (V : Set ℝ) ⊆ (G₁ : Set ℝ) ∪ G₂ := fun x hx => Opens.mem_sup.1 (hV hx)
  obtain ⟨a, haV, haG₁⟩ := IsConcreteLE.not_le_iff_exists.1 hV₁
  obtain ⟨b, hbV, hbG₂⟩ := IsConcreteLE.not_le_iff_exists.1 hV₂
  obtain ⟨y, hyV, hy₁, hy₂⟩ := hVc.isPreconnected _ _ G₁.isOpen G₂.isOpen hsub
    ⟨b, hbV, (hsub hbV).resolve_right hbG₂⟩ ⟨a, haV, (hsub haV).resolve_left haG₁⟩
  have hVsup : V ≤ (V ⊓ G₁) ⊔ (V ⊓ G₂) := fun x hx =>
    Opens.mem_sup.2 ((hsub hx).imp (fun h => ⟨hx, h⟩) (fun h => ⟨hx, h⟩))
  have c₁' : ((V ⊓ G₁ : Opens realLine) : Set ℝ).OrdConnected := by
    rw [Opens.coe_inf]
    exact hVc.inter c₁
  have c₂' : ((V ⊓ G₂ : Opens realLine) : Set ℝ).OrdConnected := by
    rw [Opens.coe_inf]
    exact hVc.inter c₂
  have c₁₂ : (((V ⊓ G₁) ⊓ (V ⊓ G₂) : Opens realLine) : Set ℝ).OrdConnected := by
    rw [Opens.coe_inf]
    exact c₁'.inter c₂'
  -- `F(V) ⟶ F(V ∩ G₁)` and `F(G₁) ⟶ F(V ∩ G₁)` are isomorphisms.
  have e₃ : IsIso (F.presheaf.map (homOfLE (inf_le_left : V ⊓ G₁ ≤ V)).op) :=
    isIso_map_of_le_sup F inf_le_left inf_le_left hVsup
      (Good.isIso_map h₂ inf_le_right inf_le_right ⟨y, hyV, hy₂⟩ c₂'
        ⟨y, ⟨hyV, hy₁⟩, ⟨hyV, hy₂⟩⟩ c₁₂)
  have e₄ : IsIso (F.presheaf.map (homOfLE (inf_le_right : V ⊓ G₁ ≤ G₁)).op) :=
    h₁ inf_le_right ⟨y, hyV, hy₁⟩ c₁'
  have hsq : F.presheaf.map (homOfLE hV).op ≫
        F.presheaf.map (homOfLE (inf_le_left : V ⊓ G₁ ≤ V)).op =
      F.presheaf.map (homOfLE (le_sup_left : G₁ ≤ G₁ ⊔ G₂)).op ≫
        F.presheaf.map (homOfLE (inf_le_right : V ⊓ G₁ ≤ G₁)).op := by
    rw [map_comp_map, map_comp_map]
  have : IsIso (F.presheaf.map (homOfLE hV).op ≫
      F.presheaf.map (homOfLE (inf_le_left : V ⊓ G₁ ≤ V)).op) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.presheaf.map (homOfLE (inf_le_left : V ⊓ G₁ ≤ V)).op)

/-- Every point of a set on which `F` is locally constant has a good convex ball around it
inside the set. -/
private theorem exists_good {U : Set ℝ} (hF : IsLocallyConstantOn F U) {x : ℝ} (hx : x ∈ U) :
    ∃ ε > 0, ((ballOpen x ε : Opens realLine) : Set ℝ) ⊆ U ∧ Good F (ballOpen x ε) := by
  obtain ⟨N, hxN, hNU, hN⟩ := hF x hx
  obtain ⟨ε, hε, hεN⟩ := exists_ballOpen_le hxN
  exact ⟨ε, hε, fun y hy => hNU (hεN hy),
    fun V h hne hc => hN h hne hc (ordConnected_ballOpen x ε) hεN⟩

/-- If `F` is locally constant on a convex open `W`, restriction from `W` to a nonempty good
convex open `G ⊆ W` is an isomorphism. -/
private theorem isIso_map_of_good {W G : Opens realLine} (hWc : (W : Set ℝ).OrdConnected)
    (hF : IsLocallyConstantOn F W) (hGW : G ≤ W) (hG : Good F G)
    (hGne : (G : Set ℝ).Nonempty) (hGc : (G : Set ℝ).OrdConnected) :
    IsIso (F.presheaf.map (homOfLE hGW).op) := by
  -- Any two points of `W` lie in a good convex open inside `W`.
  let P : ℝ → ℝ → Prop := fun x y => ∃ H : Opens realLine, H ≤ W ∧
    (H : Set ℝ).OrdConnected ∧ Good F H ∧ x ∈ H ∧ y ∈ H
  have hunion : ∀ {H₁ H₂ : Opens realLine} {b : ℝ}, (H₁ : Set ℝ).OrdConnected →
      (H₂ : Set ℝ).OrdConnected → b ∈ H₁ → b ∈ H₂ →
        ((H₁ ⊔ H₂ : Opens realLine) : Set ℝ).OrdConnected := by
    intro H₁ H₂ b c₁ c₂ hb₁ hb₂
    rw [Opens.coe_sup]
    exact isPreconnected_iff_ordConnected.1
      (IsPreconnected.union b hb₁ hb₂ c₁.isPreconnected c₂.isPreconnected)
  have hP : ∀ x ∈ (W : Set ℝ), ∀ y ∈ (W : Set ℝ), P x y := by
    intro x hx y hy
    refine hWc.isPreconnected.induction₂' P (fun z hz => ?_)
      (fun a b c _ _ _ hab hbc => ?_) hx hy
    · obtain ⟨ε, hε, hεW, hgood⟩ := exists_good hF hz
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hε)] with w hw
      exact ⟨⟨ballOpen z ε, hεW, ordConnected_ballOpen z ε, hgood, mem_ballOpen_self hε, hw⟩,
        ⟨ballOpen z ε, hεW, ordConnected_ballOpen z ε, hgood, hw, mem_ballOpen_self hε⟩⟩
    · obtain ⟨H₁, hH₁W, c₁, g₁, ha₁, hb₁⟩ := hab
      obtain ⟨H₂, hH₂W, c₂, g₂, hb₂, hc₂⟩ := hbc
      exact ⟨H₁ ⊔ H₂, sup_le hH₁W hH₂W, hunion c₁ c₂ hb₁ hb₂,
        good_sup g₁ g₂ c₁ c₂ ⟨b, hb₁, hb₂⟩, Opens.mem_sup.2 (Or.inl ha₁),
        Opens.mem_sup.2 (Or.inr hc₂)⟩
  -- Every point of `W` lies in a good convex open `K x` with `G ⊆ K x ⊆ W`.
  obtain ⟨y₀, hy₀⟩ := hGne
  have hK : ∀ x : (W : Set ℝ), ∃ K : Opens realLine, K ≤ W ∧ ∃ _ : G ≤ K,
      (x : ℝ) ∈ K ∧ Good F K ∧ (K : Set ℝ).OrdConnected := by
    rintro ⟨x, hx⟩
    obtain ⟨H, hHW, hHc, hHg, hxH, hyH⟩ := hP x hx y₀ (hGW hy₀)
    exact ⟨H ⊔ G, sup_le hHW hGW, le_sup_right, Opens.mem_sup.2 (Or.inl hxH),
      good_sup hHg hG hHc hGc ⟨y₀, hyH, hy₀⟩, hunion hHc hGc hyH hy₀⟩
  choose K hKW hGK hxK hKg hKc using hK
  have hcov : W ≤ iSup K := fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hxK ⟨z, hz⟩⟩
  have bij : ∀ x, Function.Bijective (F.presheaf.map (homOfLE (hGK x)).op) := fun x =>
    haveI := hKg x (hGK x) ⟨y₀, hy₀⟩ hGc
    ConcreteCategory.bijective_of_isIso _
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro s t hst
    refine TopCat.Sheaf.eq_of_locally_eq' F K W (fun x => homOfLE (hKW x)) hcov s t fun x => ?_
    apply (bij x).1
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, map_comp_map]
    exact hst
  · intro t
    choose s hs using fun x => (bij x).2 t
    -- The preimages of `t` over two members agree with the preimage over their union.
    have key : ∀ x x', ∃ u : F.presheaf.obj (op (K x ⊔ K x')),
        F.presheaf.map (homOfLE le_sup_left).op u = s x ∧
          F.presheaf.map (homOfLE le_sup_right).op u = s x' := by
      intro x x'
      have hL : Good F (K x ⊔ K x') :=
        good_sup (hKg x) (hKg x') (hKc x) (hKc x') ⟨y₀, hGK x hy₀, hGK x' hy₀⟩
      have hGL : G ≤ K x ⊔ K x' := (hGK x).trans le_sup_left
      have := hL hGL ⟨y₀, hy₀⟩ hGc
      obtain ⟨u, hu⟩ := (ConcreteCategory.bijective_of_isIso
        (F.presheaf.map (homOfLE hGL).op)).2 t
      refine ⟨u, (bij x).1 ?_, (bij x').1 ?_⟩
      · rw [← ConcreteCategory.comp_apply, map_comp_map, hs]
        exact hu
      · rw [← ConcreteCategory.comp_apply, map_comp_map, hs]
        exact hu
    obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' F K W
      (fun x => homOfLE (hKW x)) hcov s (by
        intro x x'
        obtain ⟨u, hu₁, hu₂⟩ := key x x'
        show F.presheaf.map (homOfLE inf_le_left).op (s x) =
          F.presheaf.map (homOfLE inf_le_right).op (s x')
        rw [← hu₁, ← hu₂, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          map_comp_map, map_comp_map])
    refine ⟨σ, ?_⟩
    let x₀ : (W : Set ℝ) := ⟨y₀, hGW hy₀⟩
    rw [← hs x₀, ← hσ x₀, ← ConcreteCategory.comp_apply, map_comp_map]

/-- **Trivialisation of a local system on an interval.** If `F` is locally constant on a convex
open `W`, then restriction `F(W) ⟶ F(V)` to every nonempty convex open `V ⊆ W` is an
isomorphism. -/
theorem restrict_isIso_of_isLocallyConstantOn (F : TopCat.Sheaf (ModuleCat.{0} k) realLine)
    {V W : Opens realLine} (hVW : V ≤ W) (hVne : (V : Set ℝ).Nonempty)
    (hVc : (V : Set ℝ).OrdConnected) (hWc : (W : Set ℝ).OrdConnected)
    (hF : IsLocallyConstantOn F W) : IsIso (F.presheaf.map (homOfLE hVW).op) := by
  obtain ⟨y, hy⟩ := hVne
  have hFV : IsLocallyConstantOn F V := hF.mono V.isOpen hVW
  obtain ⟨ε, hε, hεV, hg⟩ := exists_good hFV hy
  have hBV : ballOpen y ε ≤ V := hεV
  have e₁ := isIso_map_of_good hWc hF (hBV.trans hVW) hg ⟨y, mem_ballOpen_self hε⟩
    (ordConnected_ballOpen y ε)
  have e₂ := isIso_map_of_good hVc hFV hBV hg ⟨y, mem_ballOpen_self hε⟩
    (ordConnected_ballOpen y ε)
  rw [← map_comp_map F.presheaf hVW hBV] at e₁
  exact IsIso.of_isIso_comp_right _ (F.presheaf.map (homOfLE hBV).op)

end Trivialisation

/-! ### Transport -/

section Transport

variable (F : TopCat.Sheaf (ModuleCat.{0} k) realLine) {W : Opens realLine}
  (hWc : (W : Set ℝ).OrdConnected) (hF : IsLocallyConstantOn F W)

/-- **Transport.** For nonempty convex opens `V₁, V₂ ⊆ W`, where `F` is locally constant on the
convex open `W`, the isomorphism `F(V₁) ≅ F(W) ≅ F(V₂)` given by the trivialisation. -/
noncomputable def transportIso {V₁ V₂ : Opens realLine} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W)
    (hne₁ : (V₁ : Set ℝ).Nonempty) (hc₁ : (V₁ : Set ℝ).OrdConnected)
    (hne₂ : (V₂ : Set ℝ).Nonempty) (hc₂ : (V₂ : Set ℝ).OrdConnected) :
    F.presheaf.obj (op V₁) ≅ F.presheaf.obj (op V₂) :=
  haveI := restrict_isIso_of_isLocallyConstantOn F h₁ hne₁ hc₁ hWc hF
  haveI := restrict_isIso_of_isLocallyConstantOn F h₂ hne₂ hc₂ hWc hF
  (asIso (F.presheaf.map (homOfLE h₁).op)).symm ≪≫ asIso (F.presheaf.map (homOfLE h₂).op)

/-- Transport is compatible with restriction from `W`. -/
theorem map_comp_transportIso_hom {V₁ V₂ : Opens realLine} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W)
    (hne₁ : (V₁ : Set ℝ).Nonempty) (hc₁ : (V₁ : Set ℝ).OrdConnected)
    (hne₂ : (V₂ : Set ℝ).Nonempty) (hc₂ : (V₂ : Set ℝ).OrdConnected) :
    F.presheaf.map (homOfLE h₁).op ≫ (transportIso F hWc hF h₁ h₂ hne₁ hc₁ hne₂ hc₂).hom =
      F.presheaf.map (homOfLE h₂).op := by
  simp [transportIso]

/-- Transport into a smaller convex open is restriction. -/
theorem transportIso_hom_eq_map {V₁ V₂ : Opens realLine} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W)
    (hne₁ : (V₁ : Set ℝ).Nonempty) (hc₁ : (V₁ : Set ℝ).OrdConnected)
    (hne₂ : (V₂ : Set ℝ).Nonempty) (hc₂ : (V₂ : Set ℝ).OrdConnected) (h : V₂ ≤ V₁) :
    (transportIso F hWc hF h₁ h₂ hne₁ hc₁ hne₂ hc₂).hom = F.presheaf.map (homOfLE h).op := by
  have := restrict_isIso_of_isLocallyConstantOn F h₁ hne₁ hc₁ hWc hF
  rw [← cancel_epi (F.presheaf.map (homOfLE h₁).op), map_comp_transportIso_hom, map_comp_map]

/-- Transport composes. -/
theorem transportIso_trans {V₁ V₂ V₃ : Opens realLine} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W)
    (h₃ : V₃ ≤ W) (hne₁ : (V₁ : Set ℝ).Nonempty) (hc₁ : (V₁ : Set ℝ).OrdConnected)
    (hne₂ : (V₂ : Set ℝ).Nonempty) (hc₂ : (V₂ : Set ℝ).OrdConnected)
    (hne₃ : (V₃ : Set ℝ).Nonempty) (hc₃ : (V₃ : Set ℝ).OrdConnected) :
    transportIso F hWc hF h₁ h₂ hne₁ hc₁ hne₂ hc₂ ≪≫ transportIso F hWc hF h₂ h₃ hne₂ hc₂ hne₃ hc₃ =
      transportIso F hWc hF h₁ h₃ hne₁ hc₁ hne₃ hc₃ := by
  ext : 1
  simp [transportIso]

end Transport

/-! ### Stalks -/

/-- If restriction from an open `T` to every convex open neighbourhood of `x` inside `T` is an
isomorphism, then the germ map `F(T) ⟶ F_x` is an isomorphism. -/
theorem isIso_germ_of_isIso_map (F : realLine.Presheaf (ModuleCat.{0} k)) {T : Opens realLine}
    {x : ℝ} (hx : x ∈ T)
    (h : ∀ ⦃V : Opens realLine⦄ (hVT : V ≤ T), x ∈ V → (V : Set ℝ).OrdConnected →
      IsIso (F.map (homOfLE hVT).op)) :
    IsIso (F.germ T x hx) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro s t hst
    obtain ⟨U, hxU, iU, iV, he⟩ := F.germ_eq x hx hx s t hst
    rw [Subsingleton.elim iU (homOfLE (leOfHom iU)),
      Subsingleton.elim iV (homOfLE (leOfHom iU))] at he
    obtain ⟨ε, hε, hεU⟩ := exists_ballOpen_le hxU
    have hBT : ballOpen x ε ≤ T := hεU.trans (leOfHom iU)
    have := h hBT (mem_ballOpen_self hε) (ordConnected_ballOpen x ε)
    apply (ConcreteCategory.bijective_of_isIso (F.map (homOfLE hBT).op)).1
    have := congrArg (F.map (homOfLE hεU).op) he
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, map_comp_map] at this
    exact this
  · intro t
    obtain ⟨U, hUT, hxU, s, hs⟩ := F.exists_le_germ_eq t hx
    obtain ⟨ε, hε, hεU⟩ := exists_ballOpen_le hxU
    have hBT : ballOpen x ε ≤ T := hεU.trans hUT
    have := h hBT (mem_ballOpen_self hε) (ordConnected_ballOpen x ε)
    obtain ⟨σ, hσ⟩ := (ConcreteCategory.bijective_of_isIso (F.map (homOfLE hBT).op)).2
      (F.map (homOfLE hεU).op s)
    refine ⟨σ, ?_⟩
    rw [← hs, ← F.germ_res_apply (homOfLE hBT) x (mem_ballOpen_self hε) σ, hσ,
      F.germ_res_apply (homOfLE hεU) x (mem_ballOpen_self hε) s]

/-- If `F` is locally constant on a convex open `W`, the germ map `F(W) ⟶ F_x` is an
isomorphism at every `x ∈ W`. -/
theorem isIso_germ_of_isLocallyConstantOn (F : TopCat.Sheaf (ModuleCat.{0} k) realLine)
    {W : Opens realLine} (hWc : (W : Set ℝ).OrdConnected) (hF : IsLocallyConstantOn F W)
    {x : ℝ} (hx : x ∈ W) : IsIso (F.presheaf.germ W x hx) :=
  isIso_germ_of_isIso_map F.presheaf hx fun _ hVW hxV hVc =>
    restrict_isIso_of_isLocallyConstantOn F hVW ⟨x, hxV⟩ hVc hWc hF

end TDA.Sheaf.LocalSystem
