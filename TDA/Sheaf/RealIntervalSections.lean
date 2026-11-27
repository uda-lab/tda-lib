import TDA.Sheaf.RealIntervalSets
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.Abelian

/-!
# Sections of interval sheaves over order-connected opens of the real line

Fix strictly increasing breakpoints `p : Fin m → ℝ`, a field `k : Type` and an interval `J` of the
strata path, with interval sheaf `Φ (interval J) = (extension k hp).obj (interval (orient m) J)`
and interval set `I = intervalSet p J`.

* `eq_or_arrow_of_mem_star_of_mem_stratum`: a point of the star of `v` lies in the stratum of `v`
  or of a cell `u` with an arrow `v ⟶ u`.
* `isIso_germ_star_extension_interval`: for `v` in `J`, the germ `Φ(J)(star p v) ⟶ Φ(J)_z` is an
  isomorphism at every point `z` of `star p v ∩ I`.
* `injective_germ_extension_interval`: for an order-connected open `U` and `x ∈ U ∩ I`, the germ
  `Φ(J)(U) ⟶ Φ(J)_x` is injective. The set of points of `U ∩ I` where a section has zero germ is
  open and closed in the preconnected `U ∩ I`, and germs off `I` vanish.
* `surjective_germ_extension_interval`: if `I ∩ U` is relatively closed in `U`
  (`closure I ∩ U ⊆ I`), the germ at `x ∈ U ∩ I` is surjective. A section is glued from the
  generators of `Φ(J)` over the stars of the vertices of `J` and from `0` on `U \ closure I`.
* **Case (a).** `isIso_germ_extension_interval`: for an order-connected open `U` with
  `closure I ∩ U ⊆ I`, the germ at every `x ∈ U ∩ I` is an isomorphism; hence
  `finrank k (Φ(J)(U)) = 1` when moreover `U ∩ I` is nonempty
  (`finrank_sections_extension_interval_eq_one`), and restriction between two such opens
  `V ≤ U` meeting `I` is an isomorphism (`isIso_map_extension_interval`).
* **Case (b).** `isZero_sections_extension_interval`: if `U` is order-connected and not
  (`closure I ∩ U ⊆ I` and `U ∩ I` nonempty), then `Φ(J)(U) = 0`, so
  `finrank k (Φ(J)(U)) = 0` (`finrank_sections_extension_interval_eq_zero`). The two halves are
  `isZero_sections_extension_interval_of_inter_eq_empty` (no convexity needed) and
  `isZero_sections_extension_interval_of_mem_closure` (a point of `U ∩ closure I` outside `I`).

Cases (a) and (b) are exhaustive for order-connected opens; for an empty `U` both
`Φ(J)(U) = 0` and case (b) hold. Coefficients live in `k : Type`, matching `realLine : TopCat.{0}`.
-/

open CategoryTheory Limits TopologicalSpace Opposite TDA.Persistence
  TDA.Sheaf.AlternatingDiagram

namespace TDA.Sheaf.RealStratification

variable {m : ℕ} {p : Fin m → ℝ}

/-- **Strata in a star.** A point of the star of `v` lies in the stratum of `v` or in the stratum
of a cell `u` adjacent to the point `v`, with an arrow `v ⟶ u`. -/
theorem eq_or_arrow_of_mem_star_of_mem_stratum {v u : Fin (2 * m + 1)} {z : ℝ}
    (hz : z ∈ star p v) (hu : z ∈ stratum p u) : u = v ∨ Arrow (orient m) v u := by
  rw [arrow_orient_iff]
  rcases lt_trichotomy u.val v.val with h | h | h
  · right
    rcases Nat.even_or_odd' u.val with ⟨j, hj | hj⟩
    · by_contra hc
      have hi : j < m := by omega
      exact lt_asymm ((hz ⟨j, hi⟩).1 (by simp; omega)) ((hu.1 ⟨j, hi⟩).2 (by simp; omega))
    · have hi : j < m := by omega
      exact absurd ((hz ⟨j, hi⟩).1 (by simp; omega))
        (by rw [hu.2 ⟨j, hi⟩ (by simp; omega)]; exact lt_irrefl _)
  · exact Or.inl (Fin.ext h)
  · right
    rcases Nat.even_or_odd' u.val with ⟨j, hj | hj⟩
    · by_contra hc
      have hi : j - 1 < m := by omega
      exact lt_asymm ((hu.1 ⟨j - 1, hi⟩).1 (by simp; omega)) ((hz ⟨j - 1, hi⟩).2 (by simp; omega))
    · have hi : j < m := by omega
      exact absurd ((hz ⟨j, hi⟩).2 (by simp; omega))
        (by rw [hu.2 ⟨j, hi⟩ (by simp; omega)]; exact lt_irrefl _)

end TDA.Sheaf.RealStratification

namespace TDA.Sheaf.RealConstructible

open TDA.Sheaf.RealStratification

variable (k : Type) [Field k] {m : ℕ} {p : Fin m → ℝ}

/-! ### Germs over stars -/

/-- **Germs of interval sheaves over stars.** For a vertex `v` of `J`, the germ
`Φ(J)(star p v) ⟶ Φ(J)_z` is an isomorphism at every point `z` of `star p v ∩ intervalSet p J`:
the stratum `u` of `z` is `v` or a cell with an arrow `v ⟶ u`, both in `J`. -/
theorem isIso_germ_star_extension_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {v : Fin (2 * m + 1)} (hv : J.alive v) {z : ℝ} (hz : z ∈ star p v)
    (hzI : z ∈ intervalSet p J) :
    IsIso (((extension k hp).obj (interval (orient m) J)).presheaf.germ (star p v) z hz) := by
  obtain ⟨u, hzu⟩ := exists_mem_stratum hp z
  have hu : J.alive u := (mem_intervalSet_iff_alive hzu).1 hzI
  have hgerm := isIso_germ_star_of_mem_stratum hp
    (isConstructible_extension k hp (M := interval (orient m) J) fun _ => inferInstance) hzu
  rcases eq_or_arrow_of_mem_star_of_mem_stratum hz hzu with rfl | h
  · exact hgerm
  · have := isIso_extension_interval_map k hp J h hv hu
    rw [← TopCat.Presheaf.germ_res _ (homOfLE (star_le_star_of_arrow p h)) z
      (stratum_subset_star u hzu)]
    infer_instance

/-- A germ of an interval sheaf at a point outside the interval set vanishes. -/
private theorem germ_eq_of_notMem (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {z : ℝ} (hzI : z ∉ intervalSet p J)
    (a b : ((extension k hp).obj (interval (orient m) J)).presheaf.stalk z) : a = b :=
  (ModuleCat.isZero_iff_subsingleton.1 (isZero_stalk_extension_interval k hp hzI)).elim a b

/-! ### Injectivity of germs -/

/-- **Germs of interval sheaves are injective on order-connected opens.** For an order-connected
open `U` and `x ∈ U ∩ intervalSet p J`, a section of `Φ(J)` over `U` with zero germ at `x` is
zero. -/
theorem injective_germ_extension_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected) {x : ℝ} (hx : x ∈ U)
    (hxI : x ∈ intervalSet p J) :
    Function.Injective
      (((extension k hp).obj (interval (orient m) J)).presheaf.germ U x hx).hom := by
  set F := (extension k hp).obj (interval (orient m) J)
  rw [injective_iff_map_eq_zero]
  intro s hs
  let A : Set ℝ := (U : Set ℝ) ∩ intervalSet p J
  have hpc : _root_.IsPreconnected A := (hU.inter (ordConnected_intervalSet hp J)).isPreconnected
  have := Subtype.preconnectedSpace hpc
  let c : A → Prop := fun y => F.presheaf.germ U y.1 y.2.1 s = 0
  have hc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro y
    obtain ⟨v, hyv⟩ := exists_mem_stratum hp y.1
    have hv : J.alive v := (mem_intervalSet_iff_alive hyv).1 y.2.2
    have hiso := isIso_germ_star_extension_interval k hp J hv (stratum_subset_star v hyv) y.2.2
    let t := (asIso (F.presheaf.germ (star p v) y.1 (stratum_subset_star v hyv))).inv
      (F.presheaf.germ U y.1 y.2.1 s)
    have ht : F.presheaf.germ (star p v) y.1 (stratum_subset_star v hyv) t =
        F.presheaf.germ U y.1 y.2.1 s :=
      Iso.inv_hom_id_apply (asIso (F.presheaf.germ (star p v) y.1 _)) _
    obtain ⟨N, hyN, i₁, i₂, hN⟩ :=
      TopCat.Presheaf.germ_eq F.presheaf y.1 (stratum_subset_star v hyv) y.2.1 t s ht
    refine ⟨Subtype.val ⁻¹' (N : Set ℝ), N.isOpen.preimage continuous_subtype_val, hyN,
      fun z hz => ?_⟩
    have hzt : F.presheaf.germ U z.1 z.2.1 s =
        F.presheaf.germ (star p v) z.1 (leOfHom i₁ hz) t := by
      have h := congrArg (F.presheaf.germ N z.1 hz) hN
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
      exact h.symm
    have hz' := isIso_germ_star_extension_interval k hp J hv (leOfHom i₁ hz) z.2.2
    have e₁ : F.presheaf.germ (star p v) z.1 (leOfHom i₁ hz) t = 0 ↔ t = 0 :=
      (asIso (F.presheaf.germ (star p v) z.1 (leOfHom i₁ hz))).toLinearEquiv.map_eq_zero_iff
    have e₂ : F.presheaf.germ (star p v) y.1 (stratum_subset_star v hyv) t = 0 ↔ t = 0 :=
      (asIso (F.presheaf.germ (star p v) y.1 _)).toLinearEquiv.map_eq_zero_iff
    change (F.presheaf.germ U z.1 z.2.1 s = 0) = (F.presheaf.germ U y.1 y.2.1 s = 0)
    rw [hzt, ← ht]
    exact propext (e₁.trans e₂.symm)
  refine TopCat.Presheaf.section_ext F U s 0 fun y hy => ?_
  rw [map_zero]
  by_cases hyI : y ∈ intervalSet p J
  · exact Eq.mpr (hc.apply_eq_of_preconnectedSpace ⟨y, hy, hyI⟩ ⟨x, hx, hxI⟩) hs
  · exact germ_eq_of_notMem k hp J hyI _ _

/-! ### Case (b): vanishing sections -/

/-- If `U` does not meet `intervalSet p J`, the interval sheaf has no nonzero sections over `U`. -/
theorem isZero_sections_extension_interval_of_inter_eq_empty (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {U : Opens realLine}
    (h : (U : Set ℝ) ∩ intervalSet p J = ∅) :
    IsZero (((extension k hp).obj (interval (orient m) J)).presheaf.obj (op U)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun s t => TopCat.Presheaf.section_ext _ U s t fun y hy => ?_⟩
  exact germ_eq_of_notMem k hp J (fun hyI => (Set.eq_empty_iff_forall_notMem.1 h) y ⟨hy, hyI⟩)
    _ _

/-- If an order-connected open `U` contains a point of the closure of `intervalSet p J` outside
`intervalSet p J`, the interval sheaf has no nonzero sections over `U`: a section vanishes near
that point, hence at a point of the interval set, hence everywhere. -/
theorem isZero_sections_extension_interval_of_mem_closure (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    {y : ℝ} (hy : y ∈ U) (hyc : y ∈ closure (intervalSet p J)) (hyI : y ∉ intervalSet p J) :
    IsZero (((extension k hp).obj (interval (orient m) J)).presheaf.obj (op U)) := by
  set F := (extension k hp).obj (interval (orient m) J)
  rw [ModuleCat.isZero_iff_subsingleton]
  suffices h : ∀ s : F.presheaf.obj (op U), s = 0 from
    ⟨fun s t => (h s).trans (h t).symm⟩
  intro s
  have h0 : F.presheaf.germ U y hy s = F.presheaf.germ U y hy 0 :=
    germ_eq_of_notMem k hp J hyI _ _
  obtain ⟨N, hyN, i₁, i₂, hN⟩ := TopCat.Presheaf.germ_eq F.presheaf y hy hy s 0 h0
  obtain ⟨x, hxN, hxI⟩ := mem_closure_iff.1 hyc N N.isOpen hyN
  have hxU : x ∈ U := leOfHom i₁ hxN
  refine injective_germ_extension_interval k hp J hU hxU hxI ?_
  have h := congrArg (F.presheaf.germ N x hxN) hN
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
  exact h

/-- **Case (b).** For an order-connected open `U` such that `intervalSet p J ∩ U` is empty or not
relatively closed in `U`, the interval sheaf has no nonzero sections over `U`. -/
theorem isZero_sections_extension_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    (h : ¬ (closure (intervalSet p J) ∩ U ⊆ intervalSet p J ∧
      ((U : Set ℝ) ∩ intervalSet p J).Nonempty)) :
    IsZero (((extension k hp).obj (interval (orient m) J)).presheaf.obj (op U)) := by
  rw [not_and_or] at h
  rcases h with h | h
  · obtain ⟨y, ⟨hyc, hy⟩, hyI⟩ := Set.not_subset.1 h
    exact isZero_sections_extension_interval_of_mem_closure k hp J hU hy hyc hyI
  · exact isZero_sections_extension_interval_of_inter_eq_empty k hp J
      (Set.not_nonempty_iff_eq_empty.1 h)

/-! ### Case (a): one-dimensional sections -/

/-- `1 ∈ k` lies in the fibre of an interval at a vertex of the interval. -/
private theorem one_mem_fiber {J : FiniteInterval (2 * m + 1)} {v : Fin (2 * m + 1)}
    (hv : J.alive v) : (1 : k) ∈ J.fiber (k := k) v := by
  simp [FiniteInterval.fiber, hv]

/-- The generator of `Φ(J)` over the star of a vertex `v` of `J`: the image of `1 ∈ k`. -/
private noncomputable def starGen (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    (v : Fin (2 * m + 1)) (hv : J.alive v) :
    ((extension k hp).obj (interval (orient m) J)).presheaf.obj (op (star p v)) :=
  (extensionStarIso k hp (interval (orient m) J) v).inv ⟨1, one_mem_fiber k hv⟩

/-- Restriction along an arrow `v ⟶ w` of `J` sends generator to generator. -/
private theorem map_starGen (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {v w : Fin (2 * m + 1)} (h : Arrow (orient m) v w) (hv : J.alive v) (hw : J.alive w) :
    ((extension k hp).obj (interval (orient m) J)).presheaf.map
        (homOfLE (star_le_star_of_arrow p h)).op (starGen k hp J v hv) =
      starGen k hp J w hw := by
  have hn := ConcreteCategory.congr_hom
    (((extensionSectionsIso k hp).app (interval (orient m) J)).inv.naturality (gen h))
    ⟨1, one_mem_fiber k hv⟩
  have hmap : (interval (k := k) (orient m) J).map (gen h) =
      ModuleCat.ofHom (fiberMap J v w) :=
    ofArrows_map_gen _ _ h
  have hM : ((interval (k := k) (orient m) J).map (gen h)).hom
      ⟨1, one_mem_fiber k hv⟩ = ⟨1, one_mem_fiber k hw⟩ := by
    rw [hmap]
    exact Subtype.ext ((fiberMap_val J v w ⟨1, one_mem_fiber k hv⟩).trans (ite_eq_left ⟨hv, hw⟩))
  change _ = ((sections k p).obj ((extension k hp).obj (interval (orient m) J))).map (gen h)
    (starGen k hp J v hv) at hn
  rw [sections_map_gen] at hn
  refine hn.symm.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  exact congrArg _ hM

/-- The germ of a generator at a point of `J` is the germ of the generator of its stratum. -/
private theorem germ_starGen (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {v u : Fin (2 * m + 1)} (hv : J.alive v) (hu : J.alive u) {z : ℝ} (hz : z ∈ star p v)
    (hzu : z ∈ stratum p u) :
    ((extension k hp).obj (interval (orient m) J)).presheaf.germ (star p v) z hz
        (starGen k hp J v hv) =
      ((extension k hp).obj (interval (orient m) J)).presheaf.germ (star p u) z
        (stratum_subset_star u hzu) (starGen k hp J u hu) := by
  rcases eq_or_arrow_of_mem_star_of_mem_stratum hz hzu with rfl | h
  · rfl
  · rw [← map_starGen k hp J h hv hu, TopCat.Presheaf.germ_res_apply]

/-- The germ of a generator at a point of its stratum is nonzero. -/
private theorem germ_starGen_ne_zero (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {v : Fin (2 * m + 1)} (hv : J.alive v) {z : ℝ} (hzv : z ∈ stratum p v) :
    ((extension k hp).obj (interval (orient m) J)).presheaf.germ (star p v) z
        (stratum_subset_star v hzv) (starGen k hp J v hv) ≠ 0 := by
  have hiso := isIso_germ_star_of_mem_stratum hp
    (isConstructible_extension k hp (M := interval (orient m) J) fun _ => inferInstance) hzv
  intro h0
  have h0' : starGen k hp J v hv = 0 :=
    ((asIso (((extension k hp).obj (interval (orient m) J)).presheaf.germ (star p v) z
      (stratum_subset_star v hzv))).toLinearEquiv.map_eq_zero_iff).1 h0
  have h1 := (Iso.inv_hom_id_apply (extensionStarIso k hp (interval (orient m) J) v)
    ⟨1, one_mem_fiber k hv⟩).symm.trans
    ((congrArg (extensionStarIso k hp (interval (orient m) J) v).hom h0').trans (map_zero _))
  exact one_ne_zero (congrArg Subtype.val h1)

/-- **Germs of interval sheaves are surjective on relatively closed traces.** If
`intervalSet p J ∩ U` is relatively closed in the open `U`, the germ at every
`x ∈ U ∩ intervalSet p J` is surjective. -/
theorem surjective_germ_extension_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {U : Opens realLine} (hcl : closure (intervalSet p J) ∩ U ⊆ intervalSet p J) {x : ℝ}
    (hx : x ∈ U) (hxI : x ∈ intervalSet p J) :
    Function.Surjective
      (((extension k hp).obj (interval (orient m) J)).presheaf.germ U x hx).hom := by
  set F := (extension k hp).obj (interval (orient m) J)
  let O : Opens realLine := U ⊓ ⟨(closure (intervalSet p J))ᶜ, isClosed_closure.isOpen_compl⟩
  let V : Option {v // J.alive v} → Opens realLine
    | none => O
    | some v => U ⊓ star p v.1
  have hVU : ∀ o, V o ≤ U := by
    rintro (_ | v)
    · exact inf_le_left
    · exact inf_le_left
  let sf : ∀ o, F.presheaf.obj (op (V o))
    | none => 0
    | some v => F.presheaf.map (homOfLE (inf_le_right : U ⊓ star p v.1 ≤ star p v.1)).op
        (starGen k hp J v.1 v.2)
  -- The germs of the local sections at a point of `J`.
  have hG : ∀ (o : Option {v // J.alive v}) (z : ℝ) (hz : z ∈ V o) (u : Fin (2 * m + 1))
      (hzu : z ∈ stratum p u) (hu : J.alive u),
      F.presheaf.germ (V o) z hz (sf o) =
        F.presheaf.germ (star p u) z (stratum_subset_star u hzu) (starGen k hp J u hu) := by
    rintro (_ | v) z hz u hzu hu
    · exact absurd (subset_closure ((mem_intervalSet_iff_alive hzu).2 hu)) hz.2
    · refine (TopCat.Presheaf.germ_res_apply F.presheaf
        (homOfLE (inf_le_right : U ⊓ star p v.1 ≤ star p v.1)) z hz _).trans ?_
      exact germ_starGen k hp J v.2 hu _ hzu
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf V sf := by
    intro i j
    refine TopCat.Presheaf.section_ext F _ _ _ fun z hz => ?_
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    by_cases hzI : z ∈ intervalSet p J
    · obtain ⟨u, hzu⟩ := exists_mem_stratum hp z
      have hu := (mem_intervalSet_iff_alive hzu).1 hzI
      rw [hG i z hz.1 u hzu hu, hG j z hz.2 u hzu hu]
    · exact germ_eq_of_notMem k hp J hzI _ _
  have hcover : U ≤ iSup V := by
    intro y hy
    by_cases hyI : y ∈ intervalSet p J
    · obtain ⟨v, hyv⟩ := exists_mem_stratum hp y
      exact Opens.mem_iSup.2 ⟨some ⟨v, (mem_intervalSet_iff_alive hyv).1 hyI⟩,
        hy, stratum_subset_star v hyv⟩
    · exact Opens.mem_iSup.2 ⟨none, hy, fun hyc => hyI (hcl ⟨hyc, hy⟩)⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' F V U (fun o => homOfLE (hVU o))
    hcover sf hcompat
  obtain ⟨v, hxv⟩ := exists_mem_stratum hp x
  have hv : J.alive v := (mem_intervalSet_iff_alive hxv).1 hxI
  have hxV : x ∈ V (some ⟨v, hv⟩) := ⟨hx, stratum_subset_star v hxv⟩
  have hgx : F.presheaf.germ U x hx s =
      F.presheaf.germ (star p v) x (stratum_subset_star v hxv) (starGen k hp J v hv) :=
    (TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (hVU (some ⟨v, hv⟩))) x hxV s).symm.trans
      ((congrArg (F.presheaf.germ (V (some ⟨v, hv⟩)) x hxV) (hs (some ⟨v, hv⟩))).trans
        (hG (some ⟨v, hv⟩) x hxV v hxv hv))
  have hne : F.presheaf.germ U x hx s ≠ 0 := hgx ▸ germ_starGen_ne_zero k hp J hv hxv
  intro w
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1
    (finrank_stalk_extension_interval_of_mem k hp hxI) w
  exact ⟨c • s, map_smul _ c s⟩

/-- **Case (a).** For an order-connected open `U` in which `intervalSet p J` is relatively closed
(`closure I ∩ U ⊆ I`), the germ `Φ(J)(U) ⟶ Φ(J)_x` is an isomorphism at every
`x ∈ U ∩ intervalSet p J`. -/
theorem isIso_germ_extension_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    (hcl : closure (intervalSet p J) ∩ U ⊆ intervalSet p J) {x : ℝ} (hx : x ∈ U)
    (hxI : x ∈ intervalSet p J) :
    IsIso (((extension k hp).obj (interval (orient m) J)).presheaf.germ U x hx) :=
  (LinearEquiv.ofBijective _ ⟨injective_germ_extension_interval k hp J hU hx hxI,
    surjective_germ_extension_interval k hp J hcl hx hxI⟩).toModuleIso.isIso_hom

/-- **Dimension in case (a).** For an order-connected open `U` meeting `intervalSet p J` in a
nonempty relatively closed set, the sections of the interval sheaf over `U` are one-dimensional. -/
theorem finrank_sections_extension_interval_eq_one (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    (hcl : closure (intervalSet p J) ∩ U ⊆ intervalSet p J)
    (hne : ((U : Set ℝ) ∩ intervalSet p J).Nonempty) :
    Module.finrank k (((extension k hp).obj (interval (orient m) J)).presheaf.obj (op U)) = 1 := by
  obtain ⟨x, hx, hxI⟩ := hne
  have := isIso_germ_extension_interval k hp J hU hcl hx hxI
  rw [(asIso (((extension k hp).obj (interval (orient m) J)).presheaf.germ U x
    hx)).toLinearEquiv.finrank_eq]
  exact finrank_stalk_extension_interval_of_mem k hp hxI

/-- **Dimension in case (b).** For an order-connected open `U` such that `intervalSet p J ∩ U` is
empty or not relatively closed in `U`, the sections of the interval sheaf over `U` vanish. -/
theorem finrank_sections_extension_interval_eq_zero (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    (h : ¬ (closure (intervalSet p J) ∩ U ⊆ intervalSet p J ∧
      ((U : Set ℝ) ∩ intervalSet p J).Nonempty)) :
    Module.finrank k (((extension k hp).obj (interval (orient m) J)).presheaf.obj (op U)) = 0 := by
  have := ModuleCat.isZero_iff_subsingleton.1 (isZero_sections_extension_interval k hp J hU h)
  exact Module.finrank_zero_of_subsingleton

/-- **Restrictions in case (a).** For order-connected opens `V ≤ U` in both of which
`intervalSet p J` is relatively closed, and a point `x ∈ V ∩ intervalSet p J`, restriction
`Φ(J)(U) ⟶ Φ(J)(V)` is an isomorphism: both germs at `x` are. -/
theorem isIso_map_extension_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {V U : Opens realLine} (hVU : V ≤ U) (hV : (V : Set ℝ).OrdConnected)
    (hU : (U : Set ℝ).OrdConnected) (hclV : closure (intervalSet p J) ∩ V ⊆ intervalSet p J)
    (hclU : closure (intervalSet p J) ∩ U ⊆ intervalSet p J) {x : ℝ} (hx : x ∈ V)
    (hxI : x ∈ intervalSet p J) :
    IsIso (((extension k hp).obj (interval (orient m) J)).presheaf.map (homOfLE hVU).op) := by
  have hgV := isIso_germ_extension_interval k hp J hV hclV hx hxI
  have hgU := isIso_germ_extension_interval k hp J hU hclU (hVU hx) hxI
  have h := TopCat.Presheaf.germ_res ((extension k hp).obj (interval (orient m) J)).presheaf
    (homOfLE hVU) x hx
  have : IsIso (((extension k hp).obj (interval (orient m) J)).presheaf.map (homOfLE hVU).op ≫
      ((extension k hp).obj (interval (orient m) J)).presheaf.germ V x hx) := by
    rw [h]
    exact hgU
  exact IsIso.of_isIso_comp_right _
    (((extension k hp).obj (interval (orient m) J)).presheaf.germ V x hx)

variable {k} {n : ℕ} {q : Fin n → ℝ}

/-- A morphism between closed interval sheaves vanishes if the target interval has a
point outside the source interval. -/
theorem hom_extension_interval_eq_zero_of_not_subset
    (hp : StrictMono p) (hq : StrictMono q)
    {J : FiniteInterval (2 * m + 1)} {K : FiniteInterval (2 * n + 1)}
    (hJ : IsClosed (intervalSet p J)) (hK : IsClosed (intervalSet q K))
    (h : ¬ intervalSet q K ⊆ intervalSet p J)
    (f : (extension k hp).obj (interval _ J) ⟶ (extension k hq).obj (interval _ K)) :
    f = 0 := by
  let F := (extension k hp).obj (interval _ J)
  let G := (extension k hq).obj (interval _ K)
  let f' : F.presheaf ⟶ G.presheaf := f.hom
  let U : Opens realLine := ⊤
  have hm (x : ℝ) : x ∈ U := trivial
  let st (x : ℝ) := TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) x
  have topGerm {r : ℕ} {s : Fin r → ℝ} (hs : StrictMono s) (L : FiniteInterval (2 * r + 1))
      (hL : IsClosed (intervalSet s L)) {x : ℝ} (hx : x ∈ intervalSet s L) :
      IsIso (((extension k hs).obj (interval _ L)).presheaf.germ U x (hm x)) :=
    isIso_germ_extension_interval k hs L (U := U) Set.ordConnected_univ
      (by rw [hL.closure_eq]; exact Set.inter_subset_left) (hm x) hx
  obtain ⟨b, hbK, hbJ⟩ := Set.not_subset.mp h
  have htop : f'.app (op U) = 0 := by
    have := topGerm hq K hK hbK
    apply (cancel_mono (G.presheaf.germ U b (hm b))).mp
    rw [zero_comp, ← TopCat.Presheaf.stalkFunctor_map_germ U b (hm b) f']
    have hz : F.presheaf.germ U b (hm b) = 0 :=
      (isZero_stalk_extension_interval k hp hbJ).eq_of_tgt _ _
    rw [hz]
    exact zero_comp
  have hst (x : ℝ) : (st x).map f' = 0 := by
    by_cases hx : x ∈ intervalSet p J
    · have := topGerm hp J hJ hx
      apply (cancel_epi (F.presheaf.germ U x (hm x))).mp
      have hcomp : f'.app (op U) ≫ G.presheaf.germ U x (hm x) =
          F.presheaf.germ U x (hm x) ≫ (0 : F.presheaf.stalk x ⟶ G.presheaf.stalk x) := by
        rw [htop, zero_comp, comp_zero]
      exact (TopCat.Presheaf.stalkFunctor_map_germ U x (hm x) f').trans hcomp
    · exact (isZero_stalk_extension_interval k hp hx).eq_of_src _ _
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change f'.app V = 0
  ext s : 2
  change f'.app V s = (0 : G.presheaf.obj V)
  refine TopCat.Presheaf.section_ext G V.unop _ _ fun x hx => ?_
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply V.unop x hx f', hst x]
  change (0 : F.presheaf.stalk x ⟶ G.presheaf.stalk x) (F.presheaf.germ V.unop x hx s) =
    G.presheaf.germ V.unop x hx 0
  rw [map_zero]
  rfl

end TDA.Sheaf.RealConstructible
