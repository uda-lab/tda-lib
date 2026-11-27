import TDA.Sheaf.LocalSystem
import TDA.Sheaf.RealStratification

/-!
# Constructible sheaves on the real line and finite alternating diagrams

Fix strictly increasing breakpoints `p : Fin m → ℝ` (`hp : StrictMono p`) with set
`S = breakpoints p`, and write `o = orient m` for the orientation of
`TDA.Sheaf.RealStratification`, in which every arrow goes from a point to an adjacent cell.

* `IsConstructible S F` for a sheaf `F` of `k`-modules on `realLine`: `F` is locally constant on
  the complement of `S`, in the interval-local sense `IsLocallyConstantOn` of
  `TDA.Sheaf.LocalSystem`, and every stalk of `F` is finite-dimensional. That local constancy is
  intended to be equivalent, on `ℝ`, to "locally isomorphic to a constant sheaf"; this
  equivalence is **not yet proved in Lean** (follow-up #1250).
* `isIso_res_sameStratum`: if `F` is locally constant on the complement of `S`, then `F` inverts
  every inclusion `U ⊆ V` of basic opens with `U ∩ S = V ∩ S`. On a cell this is the
  trivialisation of `TDA.Sheaf.LocalSystem`; at a breakpoint `s` it glues the two sides
  `V ∩ (-∞, s)` and `V ∩ (s, ∞)` along binary sheaf squares (`isIso_map_of_le_sup`).
* `isConstructible_iff`: `F` is constructible exactly when it inverts these inclusions and its
  sections over every basic open are finite-dimensional. Constructibility is monotone in `S`
  (`IsConstructible.mono`), and for a constructible sheaf the germ at `x` of sections over a
  basic open meeting `S` at most in `x` is an isomorphism (`isIso_germ_of_isConstructible`).
* `sections k p : TopCat.Sheaf (ModuleCat.{0} k) realLine ⥤ Diagram k o` (`Γ`) takes sections
  over the stars: `(Γ F)(v) = F(star p v)` (`sections_obj_obj`), and the arrow from a point to
  an adjacent cell is restriction from the star of the point to the cell (`sections_map_gen`).
* `extension k hp : Diagram k o ⥤ TopCat.Sheaf (ModuleCat.{0} k) realLine` (`Φ`) composes a
  diagram with the stratum functor `tauFunctor hp` (`basisSheaf`) and extends the resulting
  sheaf on the basis by `basisEquiv`. `extensionBasicIso` and `extensionStarIso` give
  `(Φ M)(U) ≅ M(tau p U)` and `(Φ M)(star p v) ≅ M v`, and `Φ M` is constructible whenever `M`
  has finite-dimensional values (`isConstructible_extension`).
* The counit `extensionSectionsIso : extension k hp ⋙ sections k p ≅ 𝟭 _` (components
  `extensionStarIso`) and the unit `sectionsExtensionIso`, `F ≅ Φ (Γ F)` naturally in
  constructible `F`, give `equivalence k hp : Constructible k p ≌ FinDiagram k m` between the
  full subcategories of constructible sheaves and of diagrams with finite-dimensional values.

Finite-dimensionality uses a division ring; the diagram side, `Diagram k o`, uses a field. The
coefficients live in `k : Type`, matching `realLine : TopCat.{0}`. The adjunction `Φ ⊣ Γ` on all
sheaves, of which `equivalence k hp` is the restriction, is in
`TDA.Sheaf.RealConstructibleAdjunction`.
-/

set_option autoImplicit false

open CategoryTheory Limits TopologicalSpace Opposite TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.RealStratification TDA.Sheaf.LocalSystem

namespace TDA.Sheaf.RealConstructible

/-! ### Same-stratum inclusions -/

section SameStratum

variable {k : Type} [Ring k]

/-- An open of the real line contains points on both sides of each of its points. -/
private theorem exists_lt_gt_mem {U : Opens realLine} {s : ℝ} (hs : s ∈ U) :
    (∃ y ∈ U, y < s) ∧ ∃ y ∈ U, s < y := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp U.isOpen s hs
  refine ⟨⟨s - ε / 2, hball ?_, by linarith⟩, ⟨s + ε / 2, hball ?_, by linarith⟩⟩ <;>
    rw [Metric.mem_ball, Real.dist_eq] <;> rw [abs_lt] <;> constructor <;> linarith

/-- **Same-stratum inclusions.** If `F` is locally constant on the complement of `S`, then the
restriction `F(V) ⟶ F(U)` is an isomorphism for every inclusion `U ⊆ V` of basic opens that
contain the same points of `S`. Local constancy is the interval-local
`IsLocallyConstantOn`, not yet proved in Lean to be equivalent to "locally isomorphic to a
constant sheaf" (#1250). -/
theorem isIso_res_sameStratum {S : Finset ℝ} {F : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (hF : IsLocallyConstantOn F (↑S)ᶜ) {U V : Opens realLine} (hU : IsBasicOpen S U)
    (hV : IsBasicOpen S V) (hUV : U ≤ V) (hS : (U : Set ℝ) ∩ S = (V : Set ℝ) ∩ S) :
    IsIso (F.presheaf.map (homOfLE hUV).op) := by
  have lc : ∀ W : Opens realLine, (W : Set ℝ) ∩ S = ∅ → IsLocallyConstantOn F W :=
    fun W hW => hF.mono W.isOpen fun x hx hxS => Set.eq_empty_iff_forall_notMem.1 hW x ⟨hx, hxS⟩
  by_cases hs : ((V : Set ℝ) ∩ S).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hs
    exact restrict_isIso_of_isLocallyConstantOn F hUV hU.1 hU.2.1 hV.2.1 (lc V hs)
  obtain ⟨s, hsV, hsS⟩ := hs
  have hsU : s ∈ U := (hS ▸ (⟨hsV, hsS⟩ : s ∈ (V : Set ℝ) ∩ S) : s ∈ (U : Set ℝ) ∩ S).1
  have huniq : ∀ y ∈ (V : Set ℝ), y ∈ (S : Set ℝ) → y = s := fun y hy hyS =>
    hV.2.2 ⟨hy, hyS⟩ ⟨hsV, hsS⟩
  obtain ⟨⟨a, haU, has⟩, ⟨b, hbU, hsb⟩⟩ := exists_lt_gt_mem hsU
  let L : Opens realLine := V ⊓ ⟨Set.Iio s, isOpen_Iio⟩
  let R : Opens realLine := V ⊓ ⟨Set.Ioi s, isOpen_Ioi⟩
  let W : Opens realLine := U ⊔ R
  have hLS : (L : Set ℝ) ∩ S = ∅ := Set.eq_empty_iff_forall_notMem.2 fun y ⟨⟨hyV, hys⟩, hyS⟩ =>
    (ne_of_lt (show y < s from hys)) (huniq y hyV hyS)
  have hRS : (R : Set ℝ) ∩ S = ∅ := Set.eq_empty_iff_forall_notMem.2 fun y ⟨⟨hyV, hys⟩, hyS⟩ =>
    (ne_of_gt (show s < y from hys)) (huniq y hyV hyS)
  have hLc : (L : Set ℝ).OrdConnected := hV.2.1.inter Set.ordConnected_Iio
  have hRc : (R : Set ℝ).OrdConnected := hV.2.1.inter Set.ordConnected_Ioi
  have hWV : W ≤ V := sup_le hUV inf_le_left
  -- `F(V) ⟶ F(W)` is an isomorphism: glue `W` and the left side `L`.
  have e₁ : IsIso (F.presheaf.map (homOfLE hWV).op) := by
    refine isIso_map_of_le_sup F (B := L) hWV inf_le_left (fun y hy => ?_) ?_
    · rcases lt_trichotomy y s with h | rfl | h
      · exact Opens.mem_sup.2 (Or.inr ⟨hy, h⟩)
      · exact Opens.mem_sup.2 (Or.inl (Opens.mem_sup.2 (Or.inl hsU)))
      · exact Opens.mem_sup.2 (Or.inl (Opens.mem_sup.2 (Or.inr ⟨hy, h⟩)))
    · refine restrict_isIso_of_isLocallyConstantOn F inf_le_right
        ⟨a, Opens.mem_sup.2 (Or.inl haU), hUV haU, has⟩ ⟨fun x hx z hz w hw => ?_⟩ hLc (lc L hLS)
      have hxU : x ∈ U := by
        rcases Opens.mem_sup.1 hx.1 with h | h
        · exact h
        · exact absurd (show x < s from hx.2.2) (not_lt.2 (le_of_lt h.2))
      have hzU : z ∈ U := by
        rcases Opens.mem_sup.1 hz.1 with h | h
        · exact h
        · exact absurd (show z < s from hz.2.2) (not_lt.2 (le_of_lt h.2))
      exact ⟨Opens.mem_sup.2 (Or.inl (hU.2.1.out hxU hzU hw)), hLc.out hx.2 hz.2 hw⟩
  -- `F(W) ⟶ F(U)` is an isomorphism: glue `U` and the right side `R`.
  have e₂ : IsIso (F.presheaf.map (homOfLE (le_sup_left : U ≤ W)).op) :=
    isIso_map_of_le_sup F (B := R) le_sup_left le_sup_right le_rfl
      (restrict_isIso_of_isLocallyConstantOn F inf_le_right ⟨b, hbU, hUV hbU, hsb⟩
        (hU.2.1.inter hRc) hRc (lc R hRS))
  have hc : F.presheaf.map (homOfLE hUV).op =
      F.presheaf.map (homOfLE hWV).op ≫ F.presheaf.map (homOfLE (le_sup_left : U ≤ W)).op := by
    rw [← F.presheaf.map_comp]
    rfl
  rw [hc]
  infer_instance

end SameStratum

/-! ### Constructible sheaves -/

section Constructible

variable {k : Type} [DivisionRing k]

/-- **Constructible sheaves.** A sheaf `F` of `k`-modules on the real line is constructible with
respect to a finite set `S` when it is locally constant on the complement of `S`, in the
interval-local sense `IsLocallyConstantOn`, and all its stalks are finite-dimensional.

That local constancy is intended to be equivalent, on `ℝ`, to "locally isomorphic to a constant
sheaf". This equivalence is **not yet proved in Lean**; the bridge is follow-up #1250. -/
def IsConstructible (S : Finset ℝ) (F : TopCat.Sheaf (ModuleCat.{0} k) realLine) : Prop :=
  IsLocallyConstantOn F (↑S)ᶜ ∧ ∀ x : ℝ, FiniteDimensional k (F.presheaf.stalk x)

/-- A basic open contains a point `x` such that it meets `S` at most in `x`. -/
private theorem exists_mem_inter_subset {S : Finset ℝ} {T : Opens realLine}
    (hT : IsBasicOpen S T) : ∃ x ∈ T, ∀ y ∈ (T : Set ℝ) ∩ S, y = x := by
  by_cases hs : ((T : Set ℝ) ∩ S).Nonempty
  · obtain ⟨s, hs⟩ := hs
    exact ⟨s, hs.1, fun y hy => hT.2.2 hy hs⟩
  · obtain ⟨x, hx⟩ := hT.1
    exact ⟨x, hx, fun y hy => absurd ⟨y, hy⟩ hs⟩

/-- The germ at `x` of sections over a basic open `T` that meets `S` at most in `x` is an
isomorphism, for a presheaf that inverts same-stratum inclusions. -/
private theorem isIso_germ_of_sameStratum {S : Finset ℝ}
    (P : realLine.Presheaf (ModuleCat.{0} k))
    (hP : ∀ ⦃U V : Opens realLine⦄ (h : U ≤ V), IsBasicOpen S U → IsBasicOpen S V →
      (U : Set ℝ) ∩ S = (V : Set ℝ) ∩ S → IsIso (P.map (homOfLE h).op))
    {T : Opens realLine} (hT : IsBasicOpen S T) {x : ℝ} (hxT : x ∈ T)
    (hx : ∀ y ∈ (T : Set ℝ) ∩ S, y = x) : IsIso (P.germ T x hxT) := by
  refine isIso_germ_of_isIso_map P hxT fun V hVT hxV hVc => hP hVT
    ⟨⟨x, hxV⟩, hVc, hT.2.2.anti (Set.inter_subset_inter_left _ hVT)⟩ hT ?_
  refine Set.Subset.antisymm (Set.inter_subset_inter_left _ hVT) fun y hy => ⟨?_, hy.2⟩
  rw [hx y hy]
  exact hxV

/-- **Constructibility on the basis.** `F` is constructible exactly when it inverts every
inclusion of basic opens with the same points of `S` and its sections over every basic open are
finite-dimensional. Local constancy is the interval-local
`IsLocallyConstantOn`, not yet proved in Lean to be equivalent to "locally isomorphic to a
constant sheaf" (#1250). -/
theorem isConstructible_iff {S : Finset ℝ} {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} :
    IsConstructible S F ↔
      (∀ ⦃U V : Opens realLine⦄ (h : U ≤ V), IsBasicOpen S U → IsBasicOpen S V →
        (U : Set ℝ) ∩ S = (V : Set ℝ) ∩ S → IsIso (F.presheaf.map (homOfLE h).op)) ∧
      ∀ U : Opens realLine, IsBasicOpen S U → FiniteDimensional k (F.presheaf.obj (op U)) := by
  constructor
  · rintro ⟨hlc, hfin⟩
    have hP : ∀ ⦃U V : Opens realLine⦄ (h : U ≤ V), IsBasicOpen S U → IsBasicOpen S V →
        (U : Set ℝ) ∩ S = (V : Set ℝ) ∩ S → IsIso (F.presheaf.map (homOfLE h).op) :=
      fun U V h hU hV hS => isIso_res_sameStratum hlc hU hV h hS
    refine ⟨hP, fun U hU => ?_⟩
    obtain ⟨x, hxU, hx⟩ := exists_mem_inter_subset hU
    have := isIso_germ_of_sameStratum F.presheaf hP hU hxU hx
    exact (asIso (F.presheaf.germ U x hxU)).toLinearEquiv.symm.finiteDimensional
  · rintro ⟨hP, hfin⟩
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · refine ⟨⟨(↑S)ᶜ, S.finite_toSet.isClosed.isOpen_compl⟩, hx, subset_rfl,
        fun V W hVW hVne hVc hWc hWN => ?_⟩
      have hW : (W : Set ℝ) ∩ S = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun y hy => hWN hy.1 hy.2
      have hV : (V : Set ℝ) ∩ S = ∅ := Set.subset_eq_empty
        (Set.inter_subset_inter_left _ hVW) hW
      exact hP hVW ⟨hVne, hVc, by rw [hV]; exact Set.subsingleton_empty⟩
        ⟨hVne.mono hVW, hWc, by rw [hW]; exact Set.subsingleton_empty⟩ (hV.trans hW.symm)
    · -- A basic open around `x` that meets `S` at most in `x`.
      have hO : IsOpen ((↑S \ {x} : Set ℝ)ᶜ) :=
        ((S.finite_toSet.subset Set.sdiff_subset).isClosed).isOpen_compl
      obtain ⟨T, hT, hxT, hTO⟩ := Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen S)
        (show x ∈ (⟨_, hO⟩ : Opens realLine) from fun h => h.2 rfl)
      have hx : ∀ y ∈ (T : Set ℝ) ∩ S, y = x := by
        intro y hy
        by_contra hne
        exact hTO hy.1 ⟨hy.2, hne⟩
      have := isIso_germ_of_sameStratum F.presheaf hP hT hxT hx
      have := hfin T hT
      exact (asIso (F.presheaf.germ T x hxT)).toLinearEquiv.finiteDimensional

/-- **Constructibility is invariant under isomorphism**: a sheaf isomorphic to a sheaf that is
constructible for `S` is constructible for `S`. -/
theorem isConstructible_of_iso {S : Finset ℝ} {F G : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (e : F ≅ G) (hF : IsConstructible S F) : IsConstructible S G := by
  obtain ⟨h₁, h₂⟩ := isConstructible_iff.1 hF
  let e' := (sheafToPresheaf _ _).mapIso e
  refine isConstructible_iff.2 ⟨fun U V h hU hV hS => ?_, fun U hU => ?_⟩
  swap
  · have : FiniteDimensional k (((sheafToPresheaf _ _).obj F).obj (op U)) := h₂ U hU
    exact (e'.app (op U)).toLinearEquiv.finiteDimensional
  have := h₁ h hU hV hS
  have hn : F.presheaf.map (homOfLE h).op ≫ (e'.app (op U)).hom =
      (e'.app (op V)).hom ≫ G.presheaf.map (homOfLE h).op := e'.hom.naturality _
  have : IsIso ((e'.app (op V)).hom ≫ G.presheaf.map (homOfLE h).op) := by
    rw [← hn]; infer_instance
  exact IsIso.of_isIso_comp_left (e'.app (op V)).hom _

/-- **Constructibility is monotone in the breakpoints**: a sheaf constructible for `S` is
constructible for every finite `S' ⊇ S`. -/
theorem IsConstructible.mono {S S' : Finset ℝ} (h : S ⊆ S')
    {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} (hF : IsConstructible S F) :
    IsConstructible S' F :=
  ⟨hF.1.mono S'.finite_toSet.isClosed.isOpen_compl
    (Set.compl_subset_compl.2 (Finset.coe_subset.2 h)), hF.2⟩

/-- **Stalks of a constructible sheaf.** For a sheaf constructible for `S`, the germ at `x` of
sections over a basic open `T ∋ x` that meets `S` at most in `x` is an isomorphism
`F(T) ≅ F_x`. -/
theorem isIso_germ_of_isConstructible {S : Finset ℝ}
    {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} (hF : IsConstructible S F)
    {T : Opens realLine} (hT : IsBasicOpen S T) {x : ℝ} (hxT : x ∈ T)
    (hx : ∀ y ∈ (T : Set ℝ) ∩ S, y = x) : IsIso (F.presheaf.germ T x hxT) :=
  isIso_germ_of_sameStratum F.presheaf (isConstructible_iff.1 hF).1 hT hxT hx

end Constructible

/-! ### Sections over the stars -/

variable {m : ℕ}

/-- The stars as a functor out of the free category of `orient m`: the arrow from a point to an
adjacent cell goes to the inclusion of the cell into the star of the point. -/
def starFunctor (p : Fin m → ℝ) : Paths (Vertex (orient m)) ⥤ (Opens realLine)ᵒᵖ :=
  Paths.lift
    { obj := fun v => op (star p v)
      map := fun e => (homOfLE (star_le_star_of_arrow p e.down)).op }

variable (k : Type) [Field k]

/-- **The section functor `Γ`.** Sections over the stars: `(Γ F)(v) = F(star p v)`, and the
arrow from a point to an adjacent cell is restriction from the star of the point to the cell. -/
noncomputable def sections (p : Fin m → ℝ) :
    TopCat.Sheaf (ModuleCat.{0} k) realLine ⥤ Diagram k (orient m) :=
  TopCat.Sheaf.forget _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj (starFunctor p)

/-- `(Γ F)(v) = F(star p v)`. -/
theorem sections_obj_obj (p : Fin m → ℝ) (F : TopCat.Sheaf (ModuleCat.{0} k) realLine)
    (v : Fin (2 * m + 1)) :
    ((sections k p).obj F).obj (vtx (orient m) v) = F.presheaf.obj (op (star p v)) :=
  rfl

/-- `(Γ F)(gen h)` is restriction from the star of the point to the adjacent cell. -/
theorem sections_map_gen (p : Fin m → ℝ) (F : TopCat.Sheaf (ModuleCat.{0} k) realLine)
    {v w : Fin (2 * m + 1)} (h : Arrow (orient m) v w) :
    ((sections k p).obj F).map (gen h) = F.presheaf.map (homOfLE (star_le_star_of_arrow p h)).op :=
  congrArg F.presheaf.map (Subsingleton.elim _ _)

/-! ### The extension functor `Φ` -/

variable {p : Fin m → ℝ}

/-- A diagram read on basic opens through their strata, as a sheaf on the basis. -/
noncomputable def basisSheaf (hp : StrictMono p) :
    Diagram k (orient m) ⥤ Sheaf (basicTopology (breakpoints p)) (ModuleCat.{0} k) :=
  ObjectProperty.lift _ ((Functor.whiskeringLeft _ _ _).obj (tauFunctor hp))
    (isSheaf_tauFunctor_comp hp)

/-- **The extension functor `Φ`.** A diagram is read on basic opens through their strata and
extended to the real line by `basisEquiv`. -/
noncomputable def extension (hp : StrictMono p) :
    Diagram k (orient m) ⥤ TopCat.Sheaf (ModuleCat.{0} k) realLine :=
  basisSheaf k hp ⋙ (basisEquiv (breakpoints p) k).functor

/-- Sections of `Φ M` over a basic open `U` are `M` at the stratum of `U`. -/
noncomputable def extensionBasicIso (hp : StrictMono p) (M : Diagram k (orient m))
    (U : BasicCat (breakpoints p)) :
    ((extension k hp).obj M).presheaf.obj (op U.1) ≅ M.obj (vtx (orient m) (tau p U)) :=
  (((sheafToPresheaf _ _).mapIso ((basisEquiv _ k).unitIso.app ((basisSheaf k hp).obj M))).app
    (op U)).symm

/-- `(Φ M)(star p v) ≅ M v`. -/
noncomputable def extensionStarIso (hp : StrictMono p) (M : Diagram k (orient m))
    (v : Fin (2 * m + 1)) :
    ((extension k hp).obj M).presheaf.obj (op (star p v)) ≅ M.obj (vtx (orient m) v) :=
  extensionBasicIso k hp M ⟨star p v, isBasicOpen_star hp v⟩ ≪≫
    M.mapIso (eqToIso (congrArg (vtx (orient m)) (tau_star hp v (isBasicOpen_star hp v))))

/-- `Φ M` is constructible when `M` has finite-dimensional values.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
theorem isConstructible_extension (hp : StrictMono p) {M : Diagram k (orient m)}
    (hM : ∀ X, FiniteDimensional k (M.obj X)) :
    IsConstructible (breakpoints p) ((extension k hp).obj M) := by
  refine isConstructible_iff.2 ⟨fun U V h hU hV hS => ?_, fun U hU => ?_⟩
  · let U' : BasicCat (breakpoints p) := ⟨U, hU⟩
    let V' : BasicCat (breakpoints p) := ⟨V, hV⟩
    let f : U' ⟶ V' := InducedCategory.homMk (homOfLE h)
    have := isIso_tauFunctor_map hp f hS
    exact isIso_map_basisEquiv k ((basisSheaf k hp).obj M) f
      (inferInstance : IsIso (M.map ((tauFunctor hp).map f.op)))
  · exact (extensionBasicIso k hp M ⟨U, hU⟩).toLinearEquiv.symm.finiteDimensional

/-- The sections of a constructible sheaf over the stars are finite-dimensional.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
theorem finiteDimensional_sections (hp : StrictMono p)
    {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} (hF : IsConstructible (breakpoints p) F)
    (X : Paths (Vertex (orient m))) : FiniteDimensional k (((sections k p).obj F).obj X) :=
  (isConstructible_iff.1 hF).2 _ (isBasicOpen_star hp X)

private theorem extensionStarIso_hom (hp : StrictMono p) (M : Diagram k (orient m))
    (v : Fin (2 * m + 1)) :
    (extensionStarIso k hp M v).hom =
      ((basisEquiv _ k).unitIso.app ((basisSheaf k hp).obj M)).inv.hom.app
          (op (⟨star p v, isBasicOpen_star hp v⟩ : BasicCat (breakpoints p))) ≫
        M.map (eqToHom (congrArg (vtx (orient m)) (tau_star hp v (isBasicOpen_star hp v)))) :=
  rfl

/-- **The counit** `Γ (Φ M) ≅ M`, with components `extensionStarIso`. -/
noncomputable def extensionSectionsIso (hp : StrictMono p) :
    extension k hp ⋙ sections k p ≅ 𝟭 (Diagram k (orient m)) :=
  NatIso.ofComponents
    (fun M => isoMk (fun X => extensionStarIso k hp M X) (by
      intro v w h
      change ((sections k p).obj ((extension k hp).obj M)).map (gen h) ≫
        (extensionStarIso k hp M w).hom = (extensionStarIso k hp M v).hom ≫ M.map (gen h)
      rw [sections_map_gen, extensionStarIso_hom, extensionStarIso_hom]
      erw [Category.assoc]
      let V : BasicCat (breakpoints p) := ⟨star p v, isBasicOpen_star hp v⟩
      let W : BasicCat (breakpoints p) := ⟨star p w, isBasicOpen_star hp w⟩
      let f : W ⟶ V := InducedCategory.homMk (homOfLE (star_le_star_of_arrow p h))
      have nat := ((basisEquiv _ k).unitIso.app ((basisSheaf k hp).obj M)).inv.hom.naturality f.op
      erw [reassoc_of% nat]
      refine whisker_eq _ ?_
      erw [← M.map_comp, ← M.map_comp]
      exact congrArg M.map (Subsingleton.elim _ _)))
    (by
      intro M N φ
      apply NatTrans.ext
      funext X
      change ((extension k hp).map φ).hom.app (op (star p X)) ≫ (extensionStarIso k hp N X).hom =
        (extensionStarIso k hp M X).hom ≫ φ.app X
      erw [extensionStarIso_hom, extensionStarIso_hom, Category.assoc]
      have nat := NatTrans.congr_app (Sheaf.hom_ext_iff.1
        ((basisEquiv _ k).unitIso.inv.naturality ((basisSheaf k hp).map φ)))
        (op (⟨star p X, isBasicOpen_star hp X⟩ : BasicCat (breakpoints p)))
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at nat
      erw [reassoc_of% nat]
      refine whisker_eq _ ?_
      exact (φ.naturality _).symm)

/-- The component of the counit at a vertex is `extensionStarIso`. -/
theorem extensionSectionsIso_app_app (hp : StrictMono p) (M : Diagram k (orient m))
    (v : Fin (2 * m + 1)) :
    ((extensionSectionsIso k hp).app M).app (vtx (orient m) v) = extensionStarIso k hp M v :=
  rfl

/-- Restriction from the star of the stratum to a basic open, as a morphism of sheaves on the
basis from `Ψ (Γ F)` to the restriction of `F`. -/
noncomputable def toBasis (hp : StrictMono p) :
    sections k p ⋙ basisSheaf k hp ⟶
      ((basisEquiv (breakpoints p) k).inverse : TopCat.Sheaf (ModuleCat.{0} k) realLine ⥤ _) where
  app F := ObjectProperty.homMk
    { app := fun U => F.presheaf.map (homOfLE (le_star_tau hp U.unop)).op
      naturality := fun U V f => by
        dsimp only [Functor.comp_map]
        erw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
        exact congrArg F.presheaf.map (Subsingleton.elim _ _) }
  naturality F G φ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact (φ.hom.naturality (homOfLE (le_star_tau hp U.unop)).op).symm

/-- The restriction from the star of the stratum is an isomorphism for a constructible sheaf. -/
private theorem isIso_toBasis_app (hp : StrictMono p)
    (F : ObjectProperty.FullSubcategory (IsConstructible (k := k) (breakpoints p))) :
    IsIso ((toBasis k hp).app F.obj) := by
  have : IsIso ((sheafToPresheaf _ _).map ((toBasis k hp).app F.obj)) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun U => ?_
    exact isIso_res_sameStratum F.property.1 U.unop.2 (isBasicOpen_star hp _)
      (le_star_tau hp U.unop) (star_tau_inter hp U.unop).symm
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- Constructible sheaves of `k`-modules on the real line, for the breakpoints of `p`, as a full
subcategory.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
abbrev Constructible (p : Fin m → ℝ) :=
  ObjectProperty.FullSubcategory (IsConstructible (k := k) (breakpoints p))

/-- Diagrams on the strata with finite-dimensional values, as a full subcategory. -/
abbrev FinDiagram (n : ℕ) :=
  ObjectProperty.FullSubcategory fun M : Diagram k (orient n) =>
    ∀ X, FiniteDimensional k (M.obj X)

/-- **The unit** `F ≅ Φ (Γ F)` for constructible `F`: the counit of `basisEquiv` composed with
the restrictions `F(star p (tau p U)) ⟶ F(U)` from the stars of the strata, which are
isomorphisms by `isIso_res_sameStratum`.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
noncomputable def sectionsExtensionIso (hp : StrictMono p) :
    ObjectProperty.ι _ ≅ ObjectProperty.ι (IsConstructible (k := k) (breakpoints p)) ⋙
      sections k p ⋙ extension k hp :=
  haveI : IsIso (Functor.whiskerLeft (ObjectProperty.ι (IsConstructible (k := k) (breakpoints p)))
      (toBasis k hp)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F => isIso_toBasis_app k hp F
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _) (basisEquiv (breakpoints p) k).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (Functor.whiskerLeft (ObjectProperty.ι _) (toBasis k hp))).symm
      (basisEquiv (breakpoints p) k).functor

/-- `Γ` on constructible sheaves, valued in diagrams with finite-dimensional values.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
noncomputable def sectionsFin (hp : StrictMono p) : Constructible k p ⥤ FinDiagram k m :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ sections k p)
    fun F => finiteDimensional_sections k hp F.property

/-- `Φ` on diagrams with finite-dimensional values, valued in constructible sheaves.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
noncomputable def extensionFin (hp : StrictMono p) : FinDiagram k m ⥤ Constructible k p :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ extension k hp)
    fun M => isConstructible_extension k hp M.property

/-- **Constructible sheaves on the real line are finite alternating diagrams.** For strictly
increasing breakpoints `p`, taking sections over the stars is an equivalence from sheaves of
`k`-modules on `ℝ` that are constructible for the breakpoints of `p` to diagrams on
`orient m` with finite-dimensional values. Its inverse is the extension functor `Φ`.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
noncomputable def equivalence (hp : StrictMono p) : Constructible k p ≌ FinDiagram k m :=
  CategoryTheory.Equivalence.mk (sectionsFin k hp) (extensionFin k hp)
    (((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
      (sectionsExtensionIso k hp))
    (((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (ObjectProperty.ι _) (extensionSectionsIso k hp)))

/-- The functor of the equivalence is `Γ`. -/
theorem equivalence_functor_obj_obj (hp : StrictMono p) (F : Constructible k p) :
    ((equivalence k hp).functor.obj F).obj = (sections k p).obj F.obj :=
  rfl

/-- The map equation through the equivalence: on a generating arrow, the diagram of a
constructible sheaf is restriction between stars. -/
theorem equivalence_functor_obj_map_gen (hp : StrictMono p) (F : Constructible k p)
    {v w : Fin (2 * m + 1)} (h : Arrow (orient m) v w) :
    ((equivalence k hp).functor.obj F).obj.map (gen h) =
      F.obj.presheaf.map (homOfLE (star_le_star_of_arrow p h)).op :=
  sections_map_gen k p F.obj h

/-- The inverse of the equivalence is `Φ`. -/
theorem equivalence_inverse_obj_obj (hp : StrictMono p) (M : FinDiagram k m) :
    ((equivalence k hp).inverse.obj M).obj = (extension k hp).obj M.obj :=
  rfl

end TDA.Sheaf.RealConstructible
