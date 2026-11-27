import TDA.Sheaf.RealIntervalSets
import TDA.Sheaf.RealConstructibleDerived

/-!
# Refinement of the breakpoints and graded barcodes on the real line

Fix strictly increasing breakpoints `p : Fin m → ℝ` and `q : Fin m' → ℝ` (`hp`, `hq`) with
`hpq : breakpoints p ⊆ breakpoints q`, a field `k : Type`, `Φ_p = extension k hp` and
`Γ_q = sections k q`.

* `refinementVertex hq hpq : Fin (2 * m' + 1) → Fin (2 * m + 1)`: the vertex of the stratum of `p`
  containing a stratum of `q` (`stratum_subset_stratum_refinementVertex`,
  `refinementVertex_eq_of_mem`); it is monotone and surjective (`refinementVertex_mono`,
  `refinementVertex_surjective`).
* `refineInterval hp hq hpq J`: the interval of the strata path of `q` of the vertices whose
  refinement vertex lies in `J` (`alive_refineInterval`), with the same interval set
  (`intervalSet_refineInterval`).
* `sectionsExtensionIntervalIso : Γ_q (Φ_p (interval J)) ≅ interval (refineInterval J)`: the
  interval sheaf of `J` read on the stars of `q` is the interval diagram of the refined interval;
  `sectionsIntervalSheafSumIso` extends it to interval sums.
* Refinement invariance: for `F` constructible for `p`, `barcode (Γ_q F)` is the image of
  `barcode (Γ_p F)` under `refineInterval` (`barcode_sections_eq_map_refineInterval`), so the two
  barcodes have the same multiset of interval sets (`barcode_sections_map_intervalSet_refine`).
  For `K` with cohomology constructible for `p`, the same holds for the graded barcodes in every
  degree (`gradedBarcode_eq_map_refineInterval`, `gradedBarcode_map_intervalSet_refine`).
* `gradedBarcodeSets k hp K hK i`: the graded barcode as a multiset of subsets of `ℝ`. It is
  invariant under refinement (`gradedBarcodeSets_refine`) and under isomorphism
  (`gradedBarcodeSets_eq_of_iso`), and it is the same for any two breakpoint families for which
  `K` has constructible cohomology (`gradedBarcodeSets_eq`), through their common refinement
  `sortedBreakpoints` (the sorted elements of a finite set, `strictMono_sortedBreakpoints`,
  `breakpoints_sortedBreakpoints`).
* `hasConstructibleCohomology_sortedBreakpoints`: cohomology sheaves constructible for their own
  finite breakpoint sets, finitely many nonzero, are all constructible for the sorted union of
  these sets.
-/

open CategoryTheory Limits TopologicalSpace Opposite TDA.Persistence
  TDA.Sheaf.AlternatingDiagram

namespace TDA.Sheaf.RealStratification

variable {m m' : ℕ} {p : Fin m → ℝ} {q : Fin m' → ℝ}

/-- **The refinement map on vertices.** For breakpoints of `p` among those of `q`, the vertex of
the strata path of `p` whose stratum contains the stratum `w` of `q`
(`stratum_subset_stratum_refinementVertex`): the stratum for `p` of the star of `w`, which is a
basic open for the breakpoints of `p`. -/
noncomputable def refinementVertex (hq : StrictMono q) (hpq : breakpoints p ⊆ breakpoints q)
    (w : Fin (2 * m' + 1)) : Fin (2 * m + 1) :=
  tau p ⟨star q w, (isBasicOpen_star hq w).anti hpq⟩

/-- Each stratum of `q` lies in the stratum of `p` of its refinement vertex. -/
theorem stratum_subset_stratum_refinementVertex (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) (w : Fin (2 * m' + 1)) :
    stratum q w ⊆ stratum p (refinementVertex hq hpq w) := by
  intro x hx
  let U : Basic (breakpoints p) := ⟨star q w, (isBasicOpen_star hq w).anti hpq⟩
  refine ⟨le_star_tau hp U hx.1, fun i hi => ?_⟩
  have hpi : p i ∈ (U.1 : Set ℝ) ∩ ↑(breakpoints p) :=
    star_tau_inter hp U ▸ ⟨(apply_mem_star_iff hp i).2 hi, apply_mem_breakpoints p i⟩
  obtain ⟨j, hj⟩ := mem_breakpoints.1 (hpq hpi.2)
  have hjw : q j ∈ star q w := by rw [hj]; exact hpi.1
  rw [← hj]
  exact hx.2 j ((apply_mem_star_iff hq j).1 hjw)

/-- The refinement vertex of `w` is the vertex of the stratum of `p` containing any point of the
stratum `w` of `q`. -/
theorem refinementVertex_eq_of_mem (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) {w : Fin (2 * m' + 1)} {v : Fin (2 * m + 1)} {x : ℝ}
    (hw : x ∈ stratum q w) (hv : x ∈ stratum p v) : refinementVertex hq hpq w = v :=
  eq_of_mem_stratum (stratum_subset_stratum_refinementVertex hp hq hpq w hw) hv

/-- The refinement map on vertices is monotone. -/
theorem refinementVertex_mono (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) : Monotone (refinementVertex hq hpq) := by
  intro w w' h
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  obtain ⟨x, hx⟩ := stratum_nonempty hq w
  obtain ⟨y, hy⟩ := stratum_nonempty hq w'
  by_contra hc
  exact lt_asymm (lt_of_mem_stratum hx hy h)
    (lt_of_mem_stratum (stratum_subset_stratum_refinementVertex hp hq hpq w' hy)
      (stratum_subset_stratum_refinementVertex hp hq hpq w hx) (not_le.1 hc))

/-- The refinement map on vertices is surjective: every stratum of `p` contains a stratum of
`q`. -/
theorem refinementVertex_surjective (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) : Function.Surjective (refinementVertex hq hpq) := by
  intro v
  obtain ⟨x, hx⟩ := stratum_nonempty hp v
  obtain ⟨w, hw⟩ := exists_mem_stratum hq x
  exact ⟨w, refinementVertex_eq_of_mem hp hq hpq hw hx⟩

/-- A downward-closed predicate on `Fin N` holds exactly below the number of its solutions. -/
private theorem lt_card_filter_iff {N : ℕ} (P : Fin N → Prop) [DecidablePred P]
    (hP : ∀ a b, a ≤ b → P b → P a) (a : Fin N) :
    P a ↔ a.val < (Finset.univ.filter P).card := by
  constructor
  · intro ha
    have : Finset.Iic a ⊆ Finset.univ.filter P := fun b hb =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hP b a (Finset.mem_Iic.1 hb) ha⟩
    have := Finset.card_le_card this
    rw [Fin.card_Iic] at this
    omega
  · intro ha
    by_contra hna
    have : Finset.univ.filter P ⊆ Finset.Iio a := fun b hb =>
      Finset.mem_Iio.2 (lt_of_not_ge fun hab => hna (hP a b hab (Finset.mem_filter.1 hb).2))
    have := Finset.card_le_card this
    rw [Fin.card_Iio] at this
    omega

/-- `ρ w < c` is downward closed in `w`. -/
private theorem refinementVertex_lt_of_le (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) (c : ℕ) (a b : Fin (2 * m' + 1)) (hab : a ≤ b)
    (hb : (refinementVertex hq hpq b).val < c) : (refinementVertex hq hpq a).val < c :=
  (Fin.le_def.1 (refinementVertex_mono hp hq hpq hab)).trans_lt hb

/-- **The refined interval.** For an interval `J` of the strata path of `p`, the interval of the
strata path of `q` of the vertices whose refinement vertex lies in `J` (`alive_refineInterval`):
its endpoints count the vertices of `q` whose refinement vertex lies below `J.birth` and below
`J.death`. -/
noncomputable def refineInterval (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) (J : FiniteInterval (2 * m + 1)) :
    FiniteInterval (2 * m' + 1) where
  birth := (Finset.univ.filter fun w => (refinementVertex hq hpq w).val < J.birth).card
  death := (Finset.univ.filter fun w => (refinementVertex hq hpq w).val < J.death).card
  birth_lt_death := by
    obtain ⟨w, hw⟩ := refinementVertex_surjective hp hq hpq
      ⟨J.birth, J.birth_lt_death.trans_le J.death_le_size⟩
    have h1 := (lt_card_filter_iff _ (refinementVertex_lt_of_le hp hq hpq J.death) w).1
      (by rw [hw]; exact J.birth_lt_death)
    have h2 := mt (lt_card_filter_iff _ (refinementVertex_lt_of_le hp hq hpq J.birth) w).2
      (by rw [hw]; exact lt_irrefl _)
    omega
  death_le_size := (Finset.card_filter_le _ _).trans (by simp)

/-- A vertex of `q` lies in the refined interval of `J` exactly when its refinement vertex lies
in `J`. -/
theorem alive_refineInterval (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) (J : FiniteInterval (2 * m + 1))
    (w : Fin (2 * m' + 1)) :
    (refineInterval hp hq hpq J).alive w ↔ J.alive (refinementVertex hq hpq w) := by
  have hb := lt_card_filter_iff _ (refinementVertex_lt_of_le hp hq hpq J.birth) w
  have hd := lt_card_filter_iff _ (refinementVertex_lt_of_le hp hq hpq J.death) w
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨not_lt.1 fun h => absurd (hb.1 h) (not_lt.2 h1), hd.2 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨not_lt.1 fun h => absurd (hb.2 h) (not_lt.2 h1), hd.1 h2⟩

/-- **Refinement keeps the interval set**: the refined interval of `J` has the interval set of
`J`. -/
theorem intervalSet_refineInterval (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) (J : FiniteInterval (2 * m + 1)) :
    intervalSet q (refineInterval hp hq hpq J) = intervalSet p J := by
  ext x
  obtain ⟨w, hw⟩ := exists_mem_stratum hq x
  rw [mem_intervalSet_iff_alive hw, alive_refineInterval,
    mem_intervalSet_iff_alive (stratum_subset_stratum_refinementVertex hp hq hpq w hw)]

/-- The elements of a finite set `S ⊆ ℝ` in increasing order, as breakpoints. -/
noncomputable def sortedBreakpoints (S : Finset ℝ) : Fin S.card → ℝ := S.orderEmbOfFin rfl

/-- The sorted breakpoints are strictly increasing. -/
theorem strictMono_sortedBreakpoints (S : Finset ℝ) : StrictMono (sortedBreakpoints S) :=
  (S.orderEmbOfFin rfl).strictMono

/-- The breakpoints of the sorted elements of `S` are `S`. -/
theorem breakpoints_sortedBreakpoints (S : Finset ℝ) : breakpoints (sortedBreakpoints S) = S := by
  ext x
  rw [mem_breakpoints, ← Finset.mem_coe, ← Finset.range_orderEmbOfFin S rfl]
  rfl

end TDA.Sheaf.RealStratification

namespace TDA.Sheaf.RealConstructible

open TDA.Sheaf.RealStratification

variable {m m' : ℕ} {p : Fin m → ℝ} {q : Fin m' → ℝ}

variable (k : Type) [Field k]

/-- A morphism of the strata path is an identity or a generating arrow. -/
private theorem eq_or_arrow_of_hom {a b : Fin (2 * m + 1)}
    (f : vtx (orient m) a ⟶ vtx (orient m) b) : a = b ∨ Arrow (orient m) a b := by
  change Quiver.Path (V := Vertex (orient m)) a b at f
  cases f with
  | nil => exact Or.inl rfl
  | cons f e =>
    cases f with
    | nil => exact Or.inr e.down
    | cons f e' =>
      have h1 := arrow_orient_iff.1 e'.down
      have h2 := arrow_orient_iff.1 e.down
      omega

/-- The maps of an interval diagram along any morphism of the strata path: the identity of `k`
between two vertices of the interval, zero otherwise. -/
private theorem interval_map_val (J : FiniteInterval (2 * m + 1)) {a b : Fin (2 * m + 1)}
    (f : vtx (orient m) a ⟶ vtx (orient m) b) (x : J.fiber (k := k) a) :
    ((show J.fiber (k := k) b from ((interval (orient m) J).map f).hom x) : k) =
      if J.alive a ∧ J.alive b then (x : k) else 0 := by
  rcases eq_or_arrow_of_hom f with rfl | h
  · rw [show f = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    by_cases ha : J.alive a
    · simp [ha]
      rfl
    · simp only [ha, and_self, ite_false]
      exact fiber_val_eq_zero ha x
  · have e : (interval (k := k) (orient m) J).map (gen h) = ModuleCat.ofHom (fiberMap J a b) :=
      ofArrows_map_gen _ _ h
    rw [show f = gen h from Subsingleton.elim _ _, e]
    exact fiberMap_val J a b x

/-- The vector `1` of an interval fibre on the interval, `0` off it. -/
private def unitVec (J : FiniteInterval (2 * m + 1)) (j : Fin (2 * m + 1)) :
    J.fiber (k := k) j :=
  ⟨if J.alive j then 1 else 0, by by_cases h : J.alive j <;> simp [FiniteInterval.fiber, h]⟩

/-- **Sections of an interval sheaf over the stars of a refinement.** For breakpoints of `p` among
those of `q`, the sections over the stars of `q` of the interval sheaf `Φ_p (interval J)` form the
interval diagram of the refined interval `refineInterval hp hq hpq J`. -/
noncomputable def sectionsExtensionIntervalIso (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) (J : FiniteInterval (2 * m + 1)) :
    (sections k q).obj ((extension k hp).obj (interval (orient m) J)) ≅
      interval (orient m') (refineInterval hp hq hpq J) := by
  let M : Diagram k (orient m) := interval (orient m) J
  let U : Fin (2 * m' + 1) → BasicCat (breakpoints p) := fun w =>
    ⟨star q w, (isBasicOpen_star hq w).anti hpq⟩
  let ε : ∀ w, ((extension k hp).obj M).presheaf.obj (op (star q w)) ≃ₗ[k]
      J.fiber (k := k) (refinementVertex hq hpq w) := fun w =>
    (extensionBasicIso k hp M (U w)).toLinearEquiv
  refine (intervalIso _ (refineInterval hp hq hpq J)
    (fun w => (ε w).symm (unitVec k J (refinementVertex hq hpq w))) ?_ ?_ ?_ ?_).symm
  · intro w y
    refine ⟨((ε w y : J.fiber (k := k) _) : k), ?_⟩
    have key : ε w y =
        ((ε w y : J.fiber (k := k) _) : k) • unitVec k J (refinementVertex hq hpq w) := by
      apply Subtype.ext
      by_cases h : J.alive (refinementVertex hq hpq w)
      · simp [unitVec, h]
      · simp [unitVec, h, fiber_val_eq_zero h]
    exact ((ε w).symm_apply_apply y).symm.trans
      ((congrArg (ε w).symm key).trans ((ε w).symm.map_smul _ _))
  · intro w hw h0
    have := congrArg Subtype.val ((ε w).symm.map_eq_zero_iff.1 h0)
    simp [unitVec, (alive_refineInterval hp hq hpq J w).1 hw] at this
  · intro w hw
    have : unitVec k J (refinementVertex hq hpq w) = 0 :=
      Subtype.ext (by simp [unitVec, mt (alive_refineInterval hp hq hpq J w).2 hw])
    rw [this, map_zero]
    rfl
  · intro w w' h hw hw'
    have hv := (alive_refineInterval hp hq hpq J w).1 hw
    have hv' := (alive_refineInterval hp hq hpq J w').1 hw'
    let f : U w' ⟶ U w := InducedCategory.homMk (homOfLE (star_le_star_of_arrow q h))
    have nat := ((basisEquiv (breakpoints p) k).unitIso.app
      ((basisSheaf k hp).obj M)).hom.hom.naturality f.op
    let η := ((basisEquiv (breakpoints p) k).unitIso.app ((basisSheaf k hp).obj M)).hom.hom
    have h1 : (η.app (op (U w'))).hom ((((basisSheaf k hp).obj M).obj.map f.op).hom
        (unitVec k J (refinementVertex hq hpq w))) =
        ((((basisEquiv (breakpoints p) k).functor ⋙ (basisEquiv (breakpoints p) k).inverse).obj
          ((basisSheaf k hp).obj M)).obj.map f.op).hom
          ((η.app (op (U w))).hom (unitVec k J (refinementVertex hq hpq w))) :=
      congrArg (fun φ => φ.hom (unitVec k J (refinementVertex hq hpq w))) nat
    have ha : J.alive ((tauFunctor hp).obj (op (U w))) := hv
    have hb : J.alive ((tauFunctor hp).obj (op (U w'))) := hv'
    have hu : (((basisSheaf k hp).obj M).obj.map f.op).hom
        (unitVec k J (refinementVertex hq hpq w)) = unitVec k J (refinementVertex hq hpq w') := by
      apply Subtype.ext
      exact (interval_map_val k J ((tauFunctor hp).map f.op) _).trans
        (by simp [unitVec, ha, hb, hv, hv'])
    rw [hu] at h1
    rw [sections_map_gen]
    exact h1.symm

/-- The sections over the stars of `q` of the interval sum `⊞_{J ∈ xs} Φ_p (interval J)` form the
interval sum of the refined intervals. -/
noncomputable def sectionsIntervalSheafSumIso (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) (xs : List (FiniteInterval (2 * m + 1))) :
    (sections k q).obj (intervalSheafSum k hp xs) ≅
      intervalSum (orient m') (xs.map (refineInterval hp hq hpq)) := by
  haveI := preservesBinaryBiproducts_of_preservesBiproducts (sections k q)
  induction xs with
  | nil => exact ((sections k q).map_isZero (isZero_zero _)).iso (isZero_zero _)
  | cons J xs ih =>
    exact (sections k q).mapBiprod _ _ ≪≫
      biprod.mapIso (sectionsExtensionIntervalIso k hp hq hpq J) ih

/-- **Refinement of the barcode of a constructible sheaf.** For breakpoints of `p` among those
of `q` and a sheaf `F` constructible for `p`, the barcode of `Γ_q F` is the image of the barcode
of `Γ_p F` under `refineInterval`. -/
theorem barcode_sections_eq_map_refineInterval (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) {F : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (hF : IsConstructible (breakpoints p) F) :
    haveI := finiteDimensional_sections k hq (hF.mono hpq)
    haveI := finiteDimensional_sections k hp hF
    barcode ((sections k q).obj F) =
      (barcode ((sections k p).obj F)).map (refineInterval hp hq hpq) := by
  have := finiteDimensional_sections k hq (hF.mono hpq)
  have := finiteDimensional_sections k hp hF
  let B := barcode ((sections k p).obj F)
  let e : F ≅ intervalSheafSum k hp B.toList :=
    (sectionsExtensionIso k hp).app ⟨F, hF⟩ ≪≫
      (extension k hp).mapIso (barcodeIso ((sections k p).obj F)) ≪≫
      extensionBarcodeDiagramIso k hp B
  rw [barcode_eq_of_iso_intervalSum _ ((sections k q).mapIso e ≪≫
    sectionsIntervalSheafSumIso k hp hq hpq B.toList), ← Multiset.map_coe, Multiset.coe_toList]

/-- **Refinement invariance, sheaf level.** For breakpoints of `p` among those of `q` and a sheaf
`F` constructible for `p`, the bars of `Γ_q F` and of `Γ_p F` have the same multiset of interval
sets. -/
theorem barcode_sections_map_intervalSet_refine (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) {F : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (hF : IsConstructible (breakpoints p) F) :
    haveI := finiteDimensional_sections k hq (hF.mono hpq)
    haveI := finiteDimensional_sections k hp hF
    (barcode ((sections k q).obj F)).map (intervalSet q) =
      (barcode ((sections k p).obj F)).map (intervalSet p) := by
  rw [barcode_sections_eq_map_refineInterval k hp hq hpq hF, Multiset.map_map]
  exact Multiset.map_congr rfl fun J _ => intervalSet_refineInterval hp hq hpq J

variable [HasDerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)]

/-- **Refinement of the graded barcode.** For breakpoints of `p` among those of `q`, the graded
barcode of `K` for `q` is the image under `refineInterval` of its graded barcode for `p`, in every
degree. -/
theorem gradedBarcode_eq_map_refineInterval (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine))
    (hK : HasConstructibleCohomology k p K) (hK' : HasConstructibleCohomology k q K) (i : ℤ) :
    gradedBarcode k hq K hK' i = (gradedBarcode k hp K hK i).map (refineInterval hp hq hpq) :=
  barcode_sections_eq_map_refineInterval k hp hq hpq (hK i)

/-- **Refinement invariance of the graded barcode.** For breakpoints of `p` among those of `q` and
`K` with cohomology constructible for `p` (hence for `q`), the graded barcodes of `K` for `p` and
for `q` have the same multiset of interval sets in every degree. -/
theorem gradedBarcode_map_intervalSet_refine (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine))
    (hK : HasConstructibleCohomology k p K) (hK' : HasConstructibleCohomology k q K) (i : ℤ) :
    (gradedBarcode k hq K hK' i).map (intervalSet q) =
      (gradedBarcode k hp K hK i).map (intervalSet p) :=
  barcode_sections_map_intervalSet_refine k hp hq hpq (hK i)

/-- **The graded barcode as subsets of `ℝ`.** The multiset of interval sets of the degree-`i`
graded barcode. -/
noncomputable def gradedBarcodeSets (hp : StrictMono p)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine))
    (hK : HasConstructibleCohomology k p K) (i : ℤ) : Multiset (Set ℝ) :=
  (gradedBarcode k hp K hK i).map (intervalSet p)

/-- The graded barcode as subsets of `ℝ` is invariant under refinement of the breakpoints. -/
theorem gradedBarcodeSets_refine (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine))
    (hK : HasConstructibleCohomology k p K) (hK' : HasConstructibleCohomology k q K) (i : ℤ) :
    gradedBarcodeSets k hq K hK' i = gradedBarcodeSets k hp K hK i :=
  gradedBarcode_map_intervalSet_refine k hp hq hpq K hK hK' i

/-- Isomorphic objects have the same graded barcode as subsets of `ℝ` in every degree. -/
theorem gradedBarcodeSets_eq_of_iso (hp : StrictMono p)
    {K L : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)} (e : K ≅ L)
    (hK : HasConstructibleCohomology k p K) (hL : HasConstructibleCohomology k p L) (i : ℤ) :
    gradedBarcodeSets k hp K hK i = gradedBarcodeSets k hp L hL i := by
  rw [gradedBarcodeSets, gradedBarcodeSets, gradedBarcode_eq_of_iso k hp e hK hL]

/-- **Independence of the stratification.** For two strictly increasing breakpoint families for
which `K` has constructible cohomology, the graded barcodes of `K` as subsets of `ℝ` agree in every
degree; both agree with that of the sorted union of the two breakpoint sets. -/
theorem gradedBarcodeSets_eq (hp : StrictMono p) (hq : StrictMono q)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine))
    (hK : HasConstructibleCohomology k p K) (hK' : HasConstructibleCohomology k q K) (i : ℤ) :
    gradedBarcodeSets k hp K hK i = gradedBarcodeSets k hq K hK' i := by
  let S := breakpoints p ∪ breakpoints q
  have hS := breakpoints_sortedBreakpoints S
  have hpS : breakpoints p ⊆ breakpoints (sortedBreakpoints S) := by
    rw [hS]
    exact Finset.subset_union_left
  have hqS : breakpoints q ⊆ breakpoints (sortedBreakpoints S) := by
    rw [hS]
    exact Finset.subset_union_right
  have hr := strictMono_sortedBreakpoints S
  rw [← gradedBarcodeSets_refine k hp hr hpS K hK (hK.mono hpS) i,
    gradedBarcodeSets_refine k hq hr hqS K hK' (hK.mono hpS) i]

/-- **Breakpoints per degree, made common.** If the cohomology of `K` vanishes outside a finite set
`T` of degrees and every `Hⁱ K` with `i ∈ T` is constructible for its own finite set `S i`, then
`K` has constructible cohomology for the sorted union of the sets `S i`. -/
theorem hasConstructibleCohomology_sortedBreakpoints
    {K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)} (T : Finset ℤ)
    (S : ℤ → Finset ℝ)
    (hK : ∀ i ∈ T, IsConstructible (S i) ((DerivedCategory.homologyFunctor _ i).obj K))
    (hz : ∀ i ∉ T, IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    HasConstructibleCohomology k (sortedBreakpoints (T.biUnion S)) K :=
  hasConstructibleCohomology_of_isConstructible k (strictMono_sortedBreakpoints _) T S
    (fun i hi => by
      rw [breakpoints_sortedBreakpoints]
      exact Finset.subset_biUnion_of_mem S hi) hK hz

end TDA.Sheaf.RealConstructible
