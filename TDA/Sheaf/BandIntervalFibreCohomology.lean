import TDA.Sheaf.BandAmplitude
import TDA.Sheaf.BandIntervalDegreeZero

/-!
# Cohomology of band fibres with interval coefficients

The degree-one output set records the windows that contain the closure of a nonempty open
interval. Outside this set, at most one excluded endpoint lies in the window. The pullback
of the interval sheaf then has surjective germs on all opens avoiding that endpoint.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory TopologicalSpace
  TDA.Persistence

namespace TDA.Sheaf.BandConvolution

open RealStratification RealConstructible AlternatingDiagram

/-- The centres whose closed radius-`ε` window contains the closure of a nonempty open set
`I`. For intervals, this tests whether the trace is nonempty and open with both endpoints
excluded. -/
def outSet1 (ε : ℝ) (I : Set ℝ) : Set ℝ :=
  {y | I.Nonempty ∧ IsOpen I ∧ closure I ⊆ Set.Icc (y - ε) (y + ε)}

/-- A nonempty bounded open interval gives the closed degree-one output
`[b - ε, a + ε]`, which can be empty. -/
theorem outSet1_Ioo {ε a b : ℝ} (_hε : 0 ≤ ε) (hab : a < b) :
    outSet1 ε (Set.Ioo a b) = Set.Icc (b - ε) (a + ε) := by
  ext y
  change (_ ∧ _ ∧ closure (Set.Ioo a b) ⊆ _) ↔ _
  simp only [closure_Ioo hab.ne, Set.nonempty_Ioo.mpr hab, isOpen_Ioo, true_and,
    Set.Icc_subset_Icc_iff hab.le]
  simp only [Set.mem_Icc]
  constructor <;> rintro ⟨hl, hr⟩ <;> exact ⟨by linarith, by linarith⟩

/-- At the open-interval threshold, the degree-one output is the midpoint. -/
theorem outSet1_Ioo_threshold {ε a b : ℝ} (hε : 0 ≤ ε) (hab : a < b)
    (h : 2 * ε = b - a) :
    outSet1 ε (Set.Ioo a b) = {(a + b) / 2} := by
  rw [outSet1_Ioo hε hab, show b - ε = (a + b) / 2 by linarith,
    show a + ε = (a + b) / 2 by linarith, Set.Icc_self]

private theorem outSet1_eq_empty_of_not_isOpen {ε : ℝ} {I : Set ℝ} (h : ¬ IsOpen I) :
    outSet1 ε I = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ hy => h hy.2.1

/-- A nonempty closed bounded interval has empty degree-one output. -/
theorem outSet1_Icc {ε a b : ℝ} (_hε : 0 ≤ ε) (hab : a ≤ b) :
    outSet1 ε (Set.Icc a b) = ∅ :=
  outSet1_eq_empty_of_not_isOpen fun h => by
    have ha : a ∈ interior (Set.Icc a b) := h.interior_eq.symm ▸ Set.left_mem_Icc.mpr hab
    simp [interior_Icc] at ha

/-- A bounded interval closed only on the left has empty degree-one output. -/
theorem outSet1_Ico {ε a b : ℝ} (_hε : 0 ≤ ε) (hab : a < b) :
    outSet1 ε (Set.Ico a b) = ∅ :=
  outSet1_eq_empty_of_not_isOpen fun h => by
    have ha : a ∈ interior (Set.Ico a b) := h.interior_eq.symm ▸ ⟨le_rfl, hab⟩
    simp [interior_Ico] at ha

/-- A bounded interval closed only on the right has empty degree-one output. -/
theorem outSet1_Ioc {ε a b : ℝ} (_hε : 0 ≤ ε) (hab : a < b) :
    outSet1 ε (Set.Ioc a b) = ∅ :=
  outSet1_eq_empty_of_not_isOpen fun h => by
    have hb : b ∈ interior (Set.Ioc a b) := h.interior_eq.symm ▸ ⟨hab, le_rfl⟩
    simp [interior_Ioc] at hb

/-- A singleton has empty degree-one output. -/
theorem outSet1_singleton {ε : ℝ} (hε : 0 ≤ ε) (a : ℝ) :
    outSet1 ε {a} = ∅ := by
  rw [← Set.Icc_self]
  exact outSet1_Icc hε le_rfl

private theorem outSet1_eq_empty_of_not_bddAbove {ε : ℝ} {I : Set ℝ} (h : ¬ BddAbove I) :
    outSet1 ε I = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
    h ⟨y + ε, fun _ hx => (hy.2.2 (subset_closure hx)).2⟩

private theorem outSet1_eq_empty_of_not_bddBelow {ε : ℝ} {I : Set ℝ} (h : ¬ BddBelow I) :
    outSet1 ε I = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
    h ⟨y - ε, fun _ hx => (hy.2.2 (subset_closure hx)).1⟩

/-- An open right ray has empty degree-one output. -/
theorem outSet1_Ioi {ε : ℝ} (_hε : 0 ≤ ε) (a : ℝ) : outSet1 ε (Set.Ioi a) = ∅ :=
  outSet1_eq_empty_of_not_bddAbove (not_bddAbove_Ioi a)

/-- A closed right ray has empty degree-one output. -/
theorem outSet1_Ici {ε : ℝ} (_hε : 0 ≤ ε) (a : ℝ) : outSet1 ε (Set.Ici a) = ∅ :=
  outSet1_eq_empty_of_not_bddAbove (not_bddAbove_Ici a)

/-- An open left ray has empty degree-one output. -/
theorem outSet1_Iio {ε : ℝ} (_hε : 0 ≤ ε) (b : ℝ) : outSet1 ε (Set.Iio b) = ∅ :=
  outSet1_eq_empty_of_not_bddBelow (not_bddBelow_Iio b)

/-- A closed left ray has empty degree-one output. -/
theorem outSet1_Iic {ε : ℝ} (_hε : 0 ≤ ε) (b : ℝ) : outSet1 ε (Set.Iic b) = ∅ :=
  outSet1_eq_empty_of_not_bddBelow (not_bddBelow_Iic b)

/-- The whole line has empty degree-one output. -/
theorem outSet1_univ {ε : ℝ} (_hε : 0 ≤ ε) : outSet1 ε (Set.univ : Set ℝ) = ∅ :=
  outSet1_eq_empty_of_not_bddAbove not_bddAbove_univ

private theorem eq_Ioo_of_excluded_endpoints {I : Set ℝ} (hI : I.OrdConnected)
    {a b : ℝ} (ha : a ∈ closure I \ I) (hb : b ∈ closure I \ I) (hab : a < b) :
    I = Set.Ioo a b := by
  have hc := convex_iff_ordConnected.2 hI
  refine Set.Subset.antisymm (fun x hx => ⟨?_, ?_⟩)
    (hc.Ioo_subset_of_mem_closure ha.1 hb.1)
  · by_contra! h
    exact ha.2 (hc.Ioo_subset_of_mem_closure (subset_closure hx) hb.1
      ⟨lt_of_le_of_ne h (fun e => ha.2 (e ▸ hx)), hab⟩)
  · by_contra! h
    exact hb.2 (hc.Ioo_subset_of_mem_closure ha.1 (subset_closure hx)
      ⟨hab, lt_of_le_of_ne h (fun e => hb.2 (e.symm ▸ hx))⟩)

private theorem exists_distinguished_point {ε y : ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hy : y ∉ outSet1 ε I) :
    ∃ c : ℝ, (closure I \ I) ∩ Set.Icc (y - ε) (y + ε) ⊆ {c} := by
  let B := (closure I \ I) ∩ Set.Icc (y - ε) (y + ε)
  rcases B.eq_empty_or_nonempty with hB | ⟨c, hc⟩
  · exact ⟨y, by change B ⊆ _; rw [hB]; exact Set.empty_subset _⟩
  refine ⟨c, fun x hx => Set.mem_singleton_iff.mpr ?_⟩
  by_contra hne
  have key {a b : ℝ} (ha : a ∈ B) (hb : b ∈ B) (hab : a < b) : y ∈ outSet1 ε I := by
    rw [eq_Ioo_of_excluded_endpoints hI ha.1 hb.1 hab]
    exact ⟨Set.nonempty_Ioo.mpr hab, isOpen_Ioo, by
      rw [closure_Ioo hab.ne]
      exact Set.Icc_subset_Icc ha.2.1 hb.2.2⟩
  exact hy ((lt_or_gt_of_ne hne).elim (key hx hc) (key hc hx))

/-- The inclusion of the window `[y - ε, y + ε]` into the input line. -/
def windowInclusion (ε y : ℝ) : TopCat.of (Set.Icc (y - ε) (y + ε)) ⟶ realLine :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The fibre cohomology of an input sheaf, valued in sheaves on the point. -/
abbrev fibreCohomology (k : Type) [Ring k] (ε y : ℝ)
    [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
    [HasDerivedCategory ((TopCat.of (Set.Icc (y - ε) (y + ε))).Sheaf (ModuleCat k))]
    (F : realLine.Sheaf (ModuleCat k)) (i : ℤ) : pt.Sheaf (ModuleCat k) :=
  (Plus.homologyFunctor _ i).obj
    ((pushforwardPlus k (toPt _)).obj ((Plus.singleFunctor _ 0).obj
      ((TopCat.Sheaf.pullback (ModuleCat k) (windowInclusion ε y)).obj F)))

variable {k : Type} [Field k] {m : ℕ} {p : Fin m → ℝ}
  (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) {ε y : ℝ}

local notation "ISh[" k "," hp "," J "]" => Functor.obj (extension k hp) (interval _ J)

section Fibre

variable [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [HasDerivedCategory ((TopCat.of (Set.Icc (y - ε) (y + ε))).Sheaf (ModuleCat k))]

/-- Degree-one cohomology of the fibre vanishes away from the degree-one output set. The proof
lifts germs on opens avoiding the excluded endpoint in the window, if there is one. -/
theorem isZero_fibreCohomology_one_interval (_hε : 0 ≤ ε)
    (hy : y ∉ outSet1 ε (intervalSet p J)) :
    IsZero (fibreCohomology k ε y (ISh[k,hp,J]) 1) := by
  let I := intervalSet p J
  obtain ⟨c, hc⟩ := exists_distinguished_point (ordConnected_intervalSet hp J) hy
  apply isZero_H_one_of_germSurjective_away Set.ordConnected_Icc c
  intro V hV x hx
  let W : Opens realLine := ⟨(closure I \ I)ᶜ, (isLocallyClosed_intervalSet hp J).isOpen_coborder⟩
  have hVW : V ≤ (Opens.map (windowInclusion ε y)).obj W := fun z hz hb =>
    hV z hz (hc ⟨hb, z.2⟩)
  apply germ_pullback_surjective (windowInclusion ε y) _ hx (W := W) hVW
  by_cases hxI : (x : ℝ) ∈ I
  · exact surjective_germ_extension_interval k hp J
      (fun z hz => by
        have hW : z ∉ closure I \ I := hz.2
        exact not_not.mp (fun hn => hW ⟨hz.1, hn⟩)) (hVW hx) hxI
  · intro g
    exact ⟨0, (ModuleCat.isZero_iff_subsingleton.1
      (isZero_stalk_extension_interval k hp hxI)).elim _ _⟩

end Fibre

local notation "H[" k "," ε "," i "]" =>
  (Plus.singleFunctor _ 0 ⋙ T k ε ⋙ Plus.homologyFunctor _ i)

section Stalk

variable [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [HasDerivedCategory ((TopCat.of (Set.Icc (y - ε) (y + ε))).Sheaf (ModuleCat k))]

/-- The stalk at `y` of degree-`i` convolution is the degree-`i` cohomology of the fibre,
viewed as a sheaf on the point. -/
theorem nonempty_iso_pullback_homology_T_fibre (_hε : 0 ≤ ε)
    (F : realLine.Sheaf (ModuleCat k)) (i : ℤ) :
    Nonempty ((TopCat.Sheaf.pullback (ModuleCat k) (ptOf (X := realLine) y)).obj
      ((H[k,ε,i]).obj F) ≅ fibreCohomology k ε y F i) := by
  let A := (Plus.singleFunctor _ 0).obj F
  let G := (pullbackPlus k (p ε)).obj A
  let K := TopCat.of (Set.Icc (y - ε) (y + ε))
  let : HasDerivedCategory ((TopCat.of
    (Set.Icc ((intervalFibration_q ε).lo y) ((intervalFibration_q ε).hi y))).Sheaf
      (ModuleCat k)) := inferInstanceAs (HasDerivedCategory (K.Sheaf (ModuleCat k)))
  have hcomp : fibreEmb ε y ≫ p ε = windowInclusion ε y := rfl
  obtain ⟨e⟩ := nonempty_homology_rightDerivedFunctorPlus_of_exact
    (TopCat.Sheaf.pullback (ModuleCat k) (ptOf (X := realLine) y)) ((T k ε).obj A) i
  refine ⟨e.symm ≪≫ (Plus.homologyFunctor _ i).mapIso
    (((intervalFibration_q ε).stalkFormula k y).app G ≪≫
      (pushforwardPlus k (toPt K)).mapIso ?_)⟩
  exact ((pullbackPlusCompIso k (fibreEmb ε y) (p ε)).app A) ≪≫
    (eqToIso (congrArg (pullbackPlus k) hcomp)).app A ≪≫
    rightDerivedFunctorPlusSingleIso (TopCat.Sheaf.pullback (ModuleCat k)
      (windowInclusion ε y)) 0 F

/-- The stalk of the convolution cohomology sheaf is the coefficient module of the fibre
cohomology sheaf on the point. -/
theorem nonempty_iso_stalk_T_fibre (hε : 0 ≤ ε) (F : realLine.Sheaf (ModuleCat k)) (i : ℤ) :
    Nonempty (((H[k,ε,i]).obj F).presheaf.stalk y ≅
      (fibreCohomology k ε y F i).presheaf.stalk (PUnit.unit : pt)) := by
  obtain ⟨e⟩ := nonempty_iso_pullback_homology_T_fibre (y := y) hε F i
  let es := stalkPullbackSheafIso k (ptOf (X := realLine) y) ((H[k,ε,i]).obj F) (PUnit.unit : pt)
  let stalk := TopCat.Presheaf.stalkFunctor (X := pt) (ModuleCat k) PUnit.unit
  exact ⟨es ≪≫ stalk.mapIso ((TopCat.Sheaf.forget (ModuleCat k) pt).mapIso e)⟩

/-- The degree-one convolution sheaf has zero stalk at every centre outside the output set. -/
theorem isZero_stalk_H1T_interval (hε : 0 ≤ ε)
    (hy : y ∉ outSet1 ε (intervalSet p J)) :
    IsZero (((H[k,ε,1]).obj (ISh[k,hp,J])).presheaf.stalk y) := by
  obtain ⟨e⟩ := nonempty_iso_stalk_T_fibre (y := y) hε (ISh[k,hp,J]) 1
  let st := TopCat.Sheaf.forget (ModuleCat k) pt ⋙
    TopCat.Presheaf.stalkFunctor (X := pt) (ModuleCat k) PUnit.unit
  exact (st.map_isZero (isZero_fibreCohomology_one_interval hp J hε hy)).of_iso e

/-- Degree-zero fibre cohomology has coefficient module `k` at every centre in the
degree-zero output set. -/
theorem nonempty_iso_fibreCohomology_zero_interval (hε : 0 ≤ ε)
    (hy : y ∈ outSet0 ε (intervalSet p J)) :
    Nonempty ((fibreCohomology k ε y (ISh[k,hp,J]) 0).presheaf.stalk (PUnit.unit : pt) ≅
      ModuleCat.of k k) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_intervalSheaf_H0T (k := k) hp J hε ⟨y, hy⟩
  obtain ⟨ey⟩ := nonempty_iso_stalk_T_fibre (y := y) hε (ISh[k,hp,J]) 0
  obtain ⟨ek⟩ := nonempty_stalk_extension_interval_iso k (strictMono_sortedBreakpoints _)
    (J := K) (hK.symm ▸ hy)
  let st := TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
    TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) y
  exact ⟨ey.symm ≪≫ st.mapIso e ≪≫ ek⟩

/-- Degree-zero fibre cohomology vanishes outside the degree-zero output set. -/
theorem isZero_fibreCohomology_zero_interval (hε : 0 ≤ ε)
    (hy : y ∉ outSet0 ε (intervalSet p J)) :
    IsZero (fibreCohomology k ε y (ISh[k,hp,J]) 0) := by
  obtain ⟨ey⟩ := nonempty_iso_stalk_T_fibre (y := y) hε (ISh[k,hp,J]) 0
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  intro x
  have hx : x = (PUnit.unit : pt) := Subsingleton.elim _ _
  subst x
  refine IsZero.of_iso ?_ ey.symm
  let st := TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
    TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) y
  rcases (outSet0 ε (intervalSet p J)).eq_empty_or_nonempty with he | hn
  · exact st.map_isZero (isZero_H0T_interval (k := k) hp J hε he)
  · obtain ⟨K, hK, ⟨e⟩⟩ := exists_intervalSheaf_H0T (k := k) hp J hε hn
    exact (isZero_stalk_extension_interval k (strictMono_sortedBreakpoints _)
      (J := K) (fun hx => hy (hK ▸ hx))).of_iso (st.mapIso e)

end Stalk

section Amplitude

variable [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

/-- The convolution of a sheaf in degree zero has no cohomology outside degrees zero and one. -/
theorem isZero_homology_T_single (ε : ℝ) (_hε : 0 ≤ ε)
    (F : realLine.Sheaf (ModuleCat k)) (i : ℤ) (hi : i < 0 ∨ 2 ≤ i) :
    IsZero ((H[k,ε,i]).obj F) := by
  let A := (Plus.singleFunctor _ 0).obj F
  rcases hi with hi | hi
  · have := isGE_T_obj k ε A 0
    exact Plus.isZero_homology_of_isGE ((T k ε).obj A) 0 i hi
  · have : ((T k ε).obj A).IsLE 1 := by simpa only [zero_add] using isLE_T_obj k ε A 0
    exact Plus.isZero_homology_of_isLE ((T k ε).obj A) 1 i (by omega)

/-- An empty degree-one output gives zero degree-one convolution cohomology. -/
theorem isZero_H1T_interval (hε : 0 ≤ ε)
    (he : outSet1 ε (intervalSet p J) = ∅) :
    IsZero ((H[k,ε,1]).obj (ISh[k,hp,J])) := by
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  intro y
  exact isZero_stalk_H1T_interval hp J hε (y := y) (by simp [he])

end Amplitude

end TDA.Sheaf.BandConvolution
