import TDA.Sheaf.RealConstructibleAdjunction
import TDA.Sheaf.IntervalAcyclic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# The extension functor induces bijections on `Ext`

Fix strictly increasing breakpoints `p : Fin m → ℝ` (`hp : StrictMono p`), a field `k`, and
write `Φ` for `extension k hp` from diagrams on the strata `orient m` to sheaves of `k`-modules
on `ℝ` (`TDA.Sheaf.RealConstructible`).

* `germ_extension_surjective`: `Φ N` is germ-surjective on every open of `ℝ` that contains no
  breakpoint, for every diagram `N`. Near a point `y` that is not a breakpoint, `Φ N` is constant
  on the cell of `y`; a germ at `y` extends over the part of the open in that cell and by zero
  over the rest.
* `exists_forall_mem_star_breakpoints_eq`: the star `star p v` contains at most one breakpoint
  `c`. `germ_pullback_extension_star_surjective`: the restriction `ι⁻¹ (Φ N)` of `Φ N` to the
  star (`ι` the inclusion of `star p v`) is germ-surjective on the opens of the star that avoid
  `c`, which is the hypothesis of `sections_exact_ordConnected` on the star.
* `sections_exact_star`: for every injective resolution `R` of `Φ N` and every vertex `v`, the
  complex of sections of `R` over `star p v` is exact in every degree `q + 1`, that is
  `Hⁿ(star p v; Φ N) = 0` for `n ≥ 1`. The resolution restricted to the star is exact
  (`TopCat.Sheaf.pullback` is exact), its sections over the star are those of `R`
  (`pullbackOpenSectionsIso`), and `sections_exact_ordConnected` applies on the open interval
  `star p v`: in degree `1` with the germ-surjectivity of `ι⁻¹ (Φ N)` above, in degrees `≥ 2`
  with that of the inverse images of the injective terms.
* Consequently `Ext^{q+1}(Φ P_v, Φ N) = 0` (`ext_representable_extension_eq_zero`) and
  `Ext^{q+1}(Φ (⊕_j P_(σ j) ⊗ V_j), Φ N) = 0` (`ext_sumTensor_extension_eq_zero`).
* `mapExt_bijective_extension`: for all diagrams `M` and `N` and every `n`, the map
  `Ext^n(M, N) ⟶ Ext^n(Φ M, Φ N)` induced by the exact functor `Φ` (Mathlib's
  `Functor.mapExtAddHom`) is bijective; `extensionExtEquiv` is the resulting additive
  equivalence. The proof follows Mathlib's `Functor.mapExt_bijective_of_preservesProjectiveObjects`,
  by induction on `n` along the standard resolution `0 → L → P → M → 0` of `M`
  (`resolution_shortExact`) and the five lemma; in place of the projectivity of `Φ P` it uses
  the vanishing of `Ext^{q+1}(Φ P, Φ N)` above. In degree `0` it is the full faithfulness of
  `Φ`.
* `ext_extension_eq_zero_of_two_le`: `Ext^n(Φ M, Φ N) = 0` for `n ≥ 2`, and
  `ext_constructible_eq_zero_of_two_le`: `Ext^n(F, G) = 0` for `n ≥ 2` for all sheaves `F` and
  `G` constructible for the breakpoints of `p`, with `Ext` computed in all sheaves of
  `k`-modules on `ℝ` (transport along D1's unit `sectionsExtensionIso`).

The diagrams are arbitrary: no finite-dimensionality is assumed. The `Ext` groups are those of
Mathlib's `Abelian.Ext` for instances `HasExt.{0}` of the two categories, which hold by
`hasExt_sheaf_realLine` and `hasExt_diagram`.
-/

open CategoryTheory Limits TopologicalSpace Opposite Abelian TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.RealStratification

namespace TDA.Sheaf.RealConstructible

variable (k : Type) [Field k] {m : ℕ} {p : Fin m → ℝ}

/-! ### Germs of `Φ N` away from the breakpoints -/

/-- The points separated from the star of `v` by a breakpoint: below a breakpoint that lies
below `v`, or above a breakpoint that lies above `v`. -/
private def starSep (p : Fin m → ℝ) (v : Fin (2 * m + 1)) : Opens realLine :=
  ⟨(⋃ (i : Fin m) (_ : 2 * i.val + 1 < v.val), Set.Iio (p i)) ∪
      ⋃ (i : Fin m) (_ : v.val < 2 * i.val + 1), Set.Ioi (p i),
    (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Iio).union
      (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioi)⟩

private theorem mem_starSep {v : Fin (2 * m + 1)} {x : ℝ} :
    x ∈ starSep p v ↔ ∃ i : Fin m, (2 * i.val + 1 < v.val ∧ x < p i) ∨
      (v.val < 2 * i.val + 1 ∧ p i < x) := by
  change x ∈ (⋃ (i : Fin m) (_ : 2 * i.val + 1 < v.val), Set.Iio (p i)) ∪
      ⋃ (i : Fin m) (_ : v.val < 2 * i.val + 1), Set.Ioi (p i) ↔ _
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_Iio, Set.mem_Ioi, exists_prop]
  constructor
  · rintro (⟨i, h⟩ | ⟨i, h⟩)
    exacts [⟨i, Or.inl h⟩, ⟨i, Or.inr h⟩]
  · rintro ⟨i, h | h⟩
    exacts [Or.inl ⟨i, h⟩, Or.inr ⟨i, h⟩]

private theorem star_inf_starSep (p : Fin m → ℝ) (v : Fin (2 * m + 1)) :
    star p v ⊓ starSep p v = ⊥ := by
  refine Opens.ext (Set.eq_empty_iff_forall_notMem.2 fun x ⟨hx, hs⟩ => ?_)
  obtain ⟨i, ⟨h, h'⟩ | ⟨h, h'⟩⟩ := mem_starSep.1 hs
  · exact lt_asymm h' ((hx i).1 h)
  · exact lt_asymm h' ((hx i).2 h)

/-- A point that is not a breakpoint lies in the star of `v` or is separated from it. -/
private theorem mem_star_sup_starSep (v : Fin (2 * m + 1)) {x : ℝ} (hx : x ∉ breakpoints p) :
    x ∈ star p v ⊔ starSep p v := by
  by_cases hsep : x ∈ starSep p v
  · exact Opens.mem_sup.2 (Or.inr hsep)
  refine Opens.mem_sup.2 (Or.inl fun i => ⟨fun h1 => ?_, fun h1 => ?_⟩)
  all_goals
    have hne : x ≠ p i := fun he => hx (he ▸ apply_mem_breakpoints p i)
    by_contra h2
    rw [not_lt] at h2
  · exact hsep (mem_starSep.2 ⟨i, Or.inl ⟨h1, lt_of_le_of_ne h2 hne⟩⟩)
  · exact hsep (mem_starSep.2 ⟨i, Or.inr ⟨h1, lt_of_le_of_ne h2 hne.symm⟩⟩)

/-- A point that is not a breakpoint lies in the star of a vertex whose star contains no
breakpoint (its cell). -/
private theorem exists_cell (hp : StrictMono p) {y : ℝ} (hy : y ∉ breakpoints p) :
    ∃ v : Fin (2 * m + 1), y ∈ star p v ∧ ∀ z ∈ star p v, z ∉ breakpoints p := by
  have hO : IsOpen ((breakpoints p : Set ℝ)ᶜ) :=
    (breakpoints p).finite_toSet.isClosed.isOpen_compl
  obtain ⟨B, hB, hyB, hBO⟩ := Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen (breakpoints p))
    (show y ∈ (⟨_, hO⟩ : Opens realLine) from hy)
  refine ⟨tau p ⟨B, hB⟩, le_star_tau hp ⟨B, hB⟩ hyB, fun z hz hzS => ?_⟩
  have : z ∈ (B : Set ℝ) ∩ breakpoints p := by
    rw [← star_tau_inter hp ⟨B, hB⟩]
    exact ⟨hz, hzS⟩
  exact hBO this.1 this.2

/-- **`Φ N` is germ-surjective away from the breakpoints.** For every diagram `N` and every open
`W` of `ℝ` containing no breakpoint, every germ of `Φ N` at a point of `W` is the germ of a
section over `W`. -/
theorem germ_extension_surjective (hp : StrictMono p) (N : Diagram k (orient m))
    {W : Opens realLine} (hW : ∀ y ∈ W, y ∉ breakpoints p) {y : ℝ} (hy : y ∈ W) :
    Function.Surjective (((extension k hp).obj N).presheaf.germ W y hy) := by
  let G := (extension k hp).obj N
  intro g
  obtain ⟨W₀, hyW₀, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf g
  obtain ⟨v, hyv, hv⟩ := exists_cell hp (hW y hy)
  obtain ⟨B, hB, hyB, hBle⟩ := Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen (breakpoints p))
    (show y ∈ W₀ ⊓ star p v from ⟨hyW₀, hyv⟩)
  have hBs : B ≤ star p v := hBle.trans inf_le_right
  have hBW : B ≤ W₀ := hBle.trans inf_le_left
  -- The restriction from the cell `star p v` to the basic open `B` is an isomorphism.
  have hS : (B : Set ℝ) ∩ breakpoints p = (star p v : Set ℝ) ∩ breakpoints p := by
    have h1 : (B : Set ℝ) ∩ breakpoints p = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun z hz => hv z (hBs hz.1) hz.2
    have h2 : (star p v : Set ℝ) ∩ breakpoints p = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun z hz => hv z hz.1 hz.2
    rw [h1, h2]
  let B' : BasicCat (breakpoints p) := ⟨B, hB⟩
  let C' : BasicCat (breakpoints p) := ⟨star p v, isBasicOpen_star hp v⟩
  let f : B' ⟶ C' := InducedCategory.homMk (homOfLE hBs)
  have := isIso_tauFunctor_map hp f hS
  have hiso : IsIso (G.presheaf.map (homOfLE hBs).op) :=
    isIso_map_basisEquiv k ((basisSheaf k hp).obj N) f
      (inferInstance : IsIso (N.map ((tauFunctor hp).map f.op)))
  obtain ⟨σ, hσ⟩ := (asIso (G.presheaf.map (homOfLE hBs).op)).toLinearEquiv.surjective
    (G.presheaf.map (homOfLE hBW).op t)
  change G.presheaf.map (homOfLE hBs).op σ = _ at hσ
  -- Glue `σ` over `W ∩ star p v` with `0` over the separated part of `W`.
  let A : Opens realLine := W ⊓ star p v
  let D : Opens realLine := W ⊓ starSep p v
  have hAD : A ⊓ D = ⊥ := le_bot_iff.1 (by
    rw [← star_inf_starSep p v]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  have hsub : Subsingleton (G.presheaf.obj (op (A ⊓ D))) :=
    ModuleCat.subsingleton_of_isZero (TopCat.Sheaf.isTerminalOfEqEmpty G hAD).isZero
  obtain ⟨τ, hτA, -⟩ := TDA.Sheaf.exists_glue₂ G
    (G.presheaf.map (homOfLE (inf_le_right : A ≤ star p v)).op σ) (0 : G.presheaf.obj (op D))
    (Subsingleton.elim _ _)
  have hWAD : W ≤ A ⊔ D := fun z hz => by
    rcases Opens.mem_sup.1 (mem_star_sup_starSep v (hW z hz)) with h | h
    exacts [Opens.mem_sup.2 (Or.inl ⟨hz, h⟩), Opens.mem_sup.2 (Or.inr ⟨hz, h⟩)]
  refine ⟨G.presheaf.map (homOfLE hWAD).op τ, ?_⟩
  have e1 := TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE hWAD) y hy τ
  have e2 := TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (le_sup_left : A ≤ A ⊔ D)) y
    ⟨hy, hyv⟩ τ
  have e3 := TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_right : A ≤ star p v)) y
    ⟨hy, hyv⟩ σ
  have e4 := TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE hBs) y hyB σ
  have e5 := TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE hBW) y hyB t
  rw [hτA] at e2
  rw [hσ] at e4
  exact e1.trans (e2.symm.trans (e3.trans (e4.symm.trans e5)))

/-- **A star contains at most one breakpoint**: there is a point `c` such that every breakpoint
in `star p v` is `c` (the breakpoint of `v` when `v` is a breakpoint, and any point otherwise). -/
theorem exists_forall_mem_star_breakpoints_eq (hp : StrictMono p) (v : Fin (2 * m + 1)) :
    ∃ c : ℝ, ∀ y ∈ star p v, y ∈ breakpoints p → y = c := by
  rcases (isBasicOpen_star hp v).2.2.eq_empty_or_singleton with h | ⟨c, hc⟩
  · exact ⟨0, fun y hy hyS => (Set.eq_empty_iff_forall_notMem.1 h y ⟨hy, hyS⟩).elim⟩
  · exact ⟨c, fun y hy hyS => (Set.ext_iff.1 hc y).1 ⟨hy, hyS⟩⟩

/-- **`Φ N` restricted to a star is germ-surjective on the cell parts of the star.** Let `ι` be
the inclusion of the open star `star p v` and `c` a point such that every breakpoint in the star
is `c`. For every diagram `N`, the restriction `ι⁻¹ (Φ N)` is germ-surjective on every open of
the star that avoids `c`. -/
theorem germ_pullback_extension_star_surjective (hp : StrictMono p) (N : Diagram k (orient m))
    (v : Fin (2 * m + 1)) {c : ℝ} (hc : ∀ y ∈ star p v, y ∈ breakpoints p → y = c)
    (V : Opens (TopCat.of (star p v : Set ℝ))) (hV : ∀ y ∈ V, (y : ℝ) ≠ c)
    (x : TopCat.of (star p v : Set ℝ)) (hx : x ∈ V) :
    Function.Surjective (((TopCat.Sheaf.pullback (ModuleCat.{0} k) (star p v).inclusion').obj
      ((extension k hp).obj N)).presheaf.germ V x hx) := by
  have hO : IsOpen ((breakpoints p : Set ℝ)ᶜ) :=
    (breakpoints p).finite_toSet.isClosed.isOpen_compl
  let W : Opens realLine := star p v ⊓ ⟨_, hO⟩
  have hVW : V ≤ (Opens.map (star p v).inclusion').obj W := fun z hz =>
    ⟨z.2, fun hzS => hV z hz (hc z z.2 hzS)⟩
  exact TDA.Sheaf.germ_pullback_surjective _ _ hx hVW
    (germ_extension_surjective k hp N (W := W) (fun y hy => hy.2) _)

/-! ### Sections of injective resolutions over the stars -/

/-- **Sections over a star of an injective resolution of `Φ N` are exact in positive degrees.**
For every diagram `N`, every injective resolution `R` of `Φ N`, every vertex `v` and every `q`,
a section of `R^{q+1}` over `star p v` killed by the differential is the image of a section of
`R^q` over `star p v`: `H^{q+1}(star p v; Φ N) = 0`. This is the hypothesis of
`ext_extension_representable_eq_zero` and `ext_extension_sumTensor_eq_zero`. -/
theorem sections_exact_star (hp : StrictMono p) (N : Diagram k (orient m))
    (R : InjectiveResolution ((extension k hp).obj N)) (v : Fin (2 * m + 1)) (q : ℕ)
    (s : (R.cocomplex.X (q + 1)).presheaf.obj (op (star p v)))
    (hs : (R.cocomplex.d (q + 1) (q + 2)).hom.app _ s = 0) :
    ∃ t : (R.cocomplex.X q).presheaf.obj (op (star p v)),
      (R.cocomplex.d q (q + 1)).hom.app _ t = s := by
  let U := star p v
  let P := TopCat.Sheaf.pullback (ModuleCat.{0} k) U.inclusion'
  let e := TDA.Sheaf.pullbackOpenSectionsIso k U
  have nat : ∀ {F G : TopCat.Sheaf (ModuleCat.{0} k) realLine} (φ : F ⟶ G)
      (x : (P.obj F).presheaf.obj (op ⊤)),
      (e.app G).hom ((P.map φ).hom.app (op ⊤) x) = φ.hom.app (op U) ((e.app F).hom x) :=
    fun φ x => ConcreteCategory.congr_hom (e.hom.naturality φ) x
  obtain ⟨c, hc⟩ := exists_forall_mem_star_breakpoints_eq hp v
  have hS : (U : Set ℝ).OrdConnected := (isBasicOpen_star hp v).2.1
  let s' := (e.app _).inv s
  have hs' : (P.map (R.cocomplex.d (q + 1) (q + 2))).hom.app (op ⊤) s' = 0 := by
    apply (e.app _).toLinearEquiv.injective
    change (e.app _).hom _ = (e.app _).hom 0
    rw [nat, Iso.inv_hom_id_apply, map_zero]
    exact hs
  have key : ∃ t' : (P.obj (R.cocomplex.X q)).presheaf.obj (op ⊤),
      (P.map (R.cocomplex.d q (q + 1))).hom.app (op ⊤) t' = s' := by
    cases q with
    | zero =>
      exact sections_exact_ordConnected k hS c (P.map (R.ι.f 0)) (P.map (R.cocomplex.d 0 1))
        (P.map (R.cocomplex.d 1 2)) _ _ (R.exact₀.map P) ((R.exact_succ 0).map P)
        (germ_pullback_extension_star_surjective k hp N v hc) s' hs'
    | succ q =>
      have := isFlasque_of_injective k (R.cocomplex.X q)
      exact sections_exact_ordConnected k hS c (P.map (R.cocomplex.d q (q + 1)))
        (P.map (R.cocomplex.d (q + 1) (q + 2))) (P.map (R.cocomplex.d (q + 2) (q + 3))) _ _
        ((R.exact_succ q).map P) ((R.exact_succ (q + 1)).map P)
        (fun V _ => germSurjective_pullback_of_isFlasque _ _ V) s' hs'
  obtain ⟨t', ht'⟩ := key
  refine ⟨(e.app _).hom t', ?_⟩
  rw [← nat, ht', Iso.inv_hom_id_apply]

/-! ### `Ext` between extended diagrams -/

section Ext

variable [HasExt.{0} (TopCat.Sheaf (ModuleCat.{0} k) realLine)]

/-- **`Ext` out of `Φ P_v` into `Φ N` vanishes in positive degrees**:
`Ext^{q+1}(Φ P_v, Φ N) = 0` for every vertex `v` and every diagram `N`. -/
theorem ext_representable_extension_eq_zero (hp : StrictMono p) (v : Fin (2 * m + 1))
    (N : Diagram k (orient m)) (q : ℕ)
    (e : Ext ((extension k hp).obj (representable k (orient m) v)) ((extension k hp).obj N)
      (q + 1)) : e = 0 :=
  ext_extension_representable_eq_zero k hp v _ (injectiveResolution _) q
    (sections_exact_star k hp N _ v q) e

/-- **`Ext` out of `Φ` of a finite sum of path tensors into `Φ N` vanishes in positive
degrees**: `Ext^{q+1}(Φ (⊕_j P_(σ j) ⊗ V_j), Φ N) = 0` for every diagram `N`. -/
theorem ext_sumTensor_extension_eq_zero (hp : StrictMono p) {J : Type} [Fintype J]
    (σ : J → Fin (2 * m + 1)) (V : J → ModuleCat.{0} k) (N : Diagram k (orient m)) (q : ℕ)
    (e : Ext ((extension k hp).obj (sumTensor (o := orient m) σ V)) ((extension k hp).obj N)
      (q + 1)) : e = 0 :=
  ext_extension_sumTensor_eq_zero k hp σ V _ (injectiveResolution _) q
    (fun j => sections_exact_star k hp N _ (σ j) q) e

section Comparison

variable [HasExt.{0} (Diagram k (orient m))]

/-- **The `Ext` comparison.** For all diagrams `M` and `N` on the strata and every degree `n`,
the map `Ext^n(M, N) ⟶ Ext^n(Φ M, Φ N)` induced by the exact functor `Φ` is bijective:
`Ext` of diagrams is `Ext` of the extended sheaves in all sheaves of `k`-modules on `ℝ`. -/
theorem mapExt_bijective_extension (hp : StrictMono p) (M N : Diagram k (orient m)) (n : ℕ) :
    Function.Bijective ((extension k hp).mapExtAddHom M N n) := by
  induction n generalizing M with
  | zero =>
    simpa [Ext.mapExactFunctor₀] using
      ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩
  | succ n hn =>
    let S := resolution M
    have hS : S.ShortExact := resolution_shortExact M
    have h₂ : ∀ e : Ext S.X₂ N (n + 1), e = 0 := fun e =>
      Ext.eq_zero_of_projective (P := resolutionMiddle M) e
    have h₂' : ∀ e : Ext ((extension k hp).obj S.X₂) ((extension k hp).obj N) (n + 1),
        e = 0 :=
      fun e => ext_sumTensor_extension_eq_zero k hp _ _ N n e
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      ((extension k hp).mapExtAddHom S.X₂ N n) ((extension k hp).mapExtAddHom S.X₁ N n)
      ((extension k hp).mapExtAddHom S.X₃ N (n + 1))
      (by
        ext x
        simp [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀])
      (by
        ext x
        simp [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass])
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' hS N n (n + 1) (add_comm 1 n)))
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' (hS.map_of_exact (extension k hp))
          ((extension k hp).obj N) n (n + 1) (add_comm 1 n)))
      (hn _).surjective (hn _)
      (fun x₃ ↦ Ext.contravariant_sequence_exact₃ hS _ x₃ (h₂ _) (add_comm 1 n))
      (fun y₃ ↦ Ext.contravariant_sequence_exact₃ (hS.map_of_exact (extension k hp)) _ y₃
        (h₂' _) (add_comm 1 n))

/-- **The `Ext` comparison as an additive equivalence**
`Ext^n(M, N) ≃+ Ext^n(Φ M, Φ N)`, given by `Φ` (`mapExt_bijective_extension`). -/
noncomputable def extensionExtEquiv (hp : StrictMono p) (M N : Diagram k (orient m)) (n : ℕ) :
    Ext M N n ≃+ Ext ((extension k hp).obj M) ((extension k hp).obj N) n :=
  AddEquiv.ofBijective _ (mapExt_bijective_extension k hp M N n)

/-- `extensionExtEquiv` maps a class by the exact functor `Φ`. -/
theorem extensionExtEquiv_apply (hp : StrictMono p) (M N : Diagram k (orient m)) (n : ℕ)
    (e : Ext M N n) : extensionExtEquiv k hp M N n e = e.mapExactFunctor (extension k hp) :=
  rfl

end Comparison

/-- **`Ext` between extended diagrams vanishes in degrees at least two**:
`Ext^n(Φ M, Φ N) = 0` for all diagrams `M`, `N` and `n ≥ 2`, computed in all sheaves of
`k`-modules on `ℝ`. -/
theorem ext_extension_eq_zero_of_two_le (hp : StrictMono p) (M N : Diagram k (orient m))
    {n : ℕ} (hn : 2 ≤ n) (e : Ext ((extension k hp).obj M) ((extension k hp).obj N) n) :
    e = 0 := by
  have := hasExt_diagram k (orient m)
  obtain ⟨e', rfl⟩ := (mapExt_bijective_extension k hp M N n).2 e
  rw [ext_eq_zero M N hn e']
  exact map_zero _

/-- `Ext` vanishes in degree `n` between objects isomorphic to objects with vanishing `Ext`. -/
private theorem ext_eq_zero_of_iso {X X' Y Y' : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (α : X ≅ X') (β : Y ≅ Y') {n : ℕ} (h : ∀ e' : Ext X' Y' n, e' = 0) (e : Ext X Y n) :
    e = 0 := by
  have h₁ : e = (Ext.mk₀ α.hom).comp ((((Ext.mk₀ α.inv).comp e (zero_add n)).comp
      (Ext.mk₀ β.hom) (add_zero n)).comp (Ext.mk₀ β.inv) (add_zero n)) (zero_add n) := by
    simp
  rw [h₁, h (((Ext.mk₀ α.inv).comp e (zero_add n)).comp (Ext.mk₀ β.hom) (add_zero n)),
    Ext.zero_comp, Ext.comp_zero]

/-- **Constructible sheaves on the real line have no `Ext` in degrees at least two.** For
sheaves `F` and `G` of `k`-modules on `ℝ` constructible for the breakpoints of `p`,
`Ext^n(F, G) = 0` for `n ≥ 2`, computed in all sheaves of `k`-modules on `ℝ`. -/
theorem ext_constructible_eq_zero_of_two_le (hp : StrictMono p) (F G : Constructible k p)
    {n : ℕ} (hn : 2 ≤ n) (e : Ext F.obj G.obj n) : e = 0 :=
  ext_eq_zero_of_iso k ((sectionsExtensionIso k hp).app F) ((sectionsExtensionIso k hp).app G)
    (ext_extension_eq_zero_of_two_le k hp _ _ hn) e

end Ext

end TDA.Sheaf.RealConstructible
