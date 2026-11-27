import TDA.Sheaf.BandMatchingIntervalCosts

/-!
# Numeric band costs for graded interval sheaves

Deletion costs are determined by the endpoint types. A bounded half-open interval
has deletion cost equal to half its length. Every other interval has infinite
deletion cost. The pair table covers distinct degrees, bounded closed intervals
in a common degree, and opposite half-open types in a common degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open TDA.Persistence TDA.Sheaf.AlternatingDiagram TDA.Sheaf.RealConstructible
open TDA.Sheaf.RealStratification
open scoped ENNReal NNReal ZeroObject

namespace TDA.Sheaf.BandConvolution

variable (k : Type) [Field k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

local notation "Sh" => realLine.Sheaf (ModuleCat k)
local notation "D⁺" => DerivedCategory.Plus Sh
local notation "Single" => Plus.singleFunctor Sh
local notation "ISh[" hp "," J "]" => Functor.obj (extension k hp) (interval _ J)

variable {m n : ℕ} {p : Fin m → ℝ} {q : Fin n → ℝ}

private def shiftSingleIso (F : Sh) (i d : ℤ) :
    (shiftFunctor D⁺ (-d)).obj ((Single i).obj F) ≅ (Single (i + d)).obj F :=
  ((Plus.singleFunctors Sh).shiftIso (-d) (i + d) i (by omega)).app F

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem aug_single_eq_zero_iff {r : ℝ} (hr : 0 ≤ r) (F : Sh) (d : ℤ) :
    (aug k hr).app ((Single d).obj F) = 0 ↔ (aug k hr).app ((Single 0).obj F) = 0 := by
  let S := shiftFunctor D⁺ (-d)
  let X := (Single 0).obj F
  let Y := (Single d).obj F
  let e : S.obj X ≅ Y := by simpa only [zero_add] using shiftSingleIso k F 0 d
  let C := ((T k r).commShiftIso (-d)).app X
  have hn : (T k r).map e.hom ≫ (aug k hr).app Y =
      C.hom ≫ S.map ((aug k hr).app X) ≫ e.hom := by
    have hs := (aug k hr).shift_app_comm (-d) X
    rw [Functor.commShiftIso_id_hom_app] at hs
    have hshift : (aug k hr).app (S.obj X) = C.hom ≫ S.map ((aug k hr).app X) :=
      (hs.trans (Category.comp_id _)).symm
    have h := (aug k hr).naturality e.hom
    change (T k r).map e.hom ≫ (aug k hr).app Y =
      (aug k hr).app (S.obj X) ≫ e.hom at h
    exact h.trans ((congrArg (· ≫ e.hom) hshift).trans (Category.assoc _ _ _))
  constructor
  · intro h
    rw [h, comp_zero] at hn
    have h' : C.hom ≫ S.map ((aug k hr).app X) ≫ e.hom =
        C.hom ≫ (0 : S.obj ((T k r).obj X) ⟶ S.obj X) ≫ e.hom := by
      simpa only [zero_comp, comp_zero] using hn.symm
    have h'' := (cancel_mono e.hom).mp ((cancel_epi C.hom).mp h')
    exact S.map_injective (h''.trans (S.map_zero _ _).symm)
  · intro h
    rw [h, S.map_zero, zero_comp, comp_zero] at hn
    let te := (T k r).mapIso e
    exact (cancel_epi te.hom).mp (hn.trans (comp_zero (f := te.hom)).symm)

private theorem distance_zero_eq_top_of_aug_ne_zero {F : D⁺}
    (h : ∀ (r : ℝ≥0), (aug k (add_nonneg r.coe_nonneg r.coe_nonneg)).app F ≠ 0) :
    distance F 0 = ⊤ :=
  distance_eq_top_iff.mpr fun r => ⟨fun w => h r (nonempty_witness_zero_iff.mp ⟨w⟩)⟩

private theorem distance_zero_eq_of_witness_iff {F : D⁺} {t : ℝ≥0}
    (h : ∀ r : ℝ≥0, Nonempty (Witness k r.coe_nonneg F 0) ↔ t ≤ r) :
    distance F 0 = (t : ℝ≥0∞) := by
  obtain ⟨w⟩ := (h t).2 le_rfl
  exact le_antisymm (by simpa only [ENNReal.ofReal_coe_nnreal] using w.distance_le)
    (le_distance_iff.mpr fun r hw => ENNReal.coe_le_coe.mpr ((h r).1 hw))

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))] in
private theorem aug_zero_single_of_outSet0_disjoint (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {r : ℝ} (hr : 0 ≤ r)
    (hne : (outSet0 r (intervalSet p J)).Nonempty)
    (hdis : ¬ (outSet0 r (intervalSet p J) ∩ intervalSet p J).Nonempty) :
    (aug k hr).app ((Single 0).obj ISh[hp,J]) = 0 := by
  obtain ⟨K, hK⟩ := exists_intervalSet_outSet0 hp J hr hne
  obtain ⟨e⟩ := nonempty_iso_T_interval_zero (k := k) hp J hr
    (strictMono_sortedBreakpoints (bandBreakpoints p r)) K hK
  apply (H0_map_bijective_of_iso_single k e (Iso.refl _)).injective
  rw [Functor.map_zero]
  apply (cancel_mono ((singleFunctorCompHomologyFunctorIsoPlus Sh 0).hom.app ISh[hp,J])).mp
  rw [zero_comp]
  exact not_ne_iff.mp (mt (H0Aug_interval_ne_zero_iff (k := k) hr hp J).mp hdis)

private theorem distance_interval_zero_of_overlap (hp : StrictMono p) (J : GradedInterval m)
    (h : ∀ r : ℝ≥0, (outSet0 ((r : ℝ) + r) (intervalSet p J.interval) ∩
      intervalSet p J.interval).Nonempty) :
    distance (J.obj k hp) 0 = ⊤ := by
  apply distance_zero_eq_top_of_aug_ne_zero k
  intro r hz
  have h₀ := (aug_single_eq_zero_iff k _ ISh[hp,J.interval] J.degree).mp hz
  have hn := (H0Aug_interval_ne_zero_iff (k := k)
    (add_nonneg r.coe_nonneg r.coe_nonneg) hp J.interval).2 (h r)
  exact hn (by simp only [H0Aug, h₀, Functor.map_zero, zero_comp])

private theorem witness_interval_zero_iff_of_overlap_iff (hp : StrictMono p) (J : GradedInterval m)
    {r : ℝ} (hr : 0 ≤ r) {t : ℝ}
    (hne : (outSet0 (r + r) (intervalSet p J.interval)).Nonempty)
    (h : (outSet0 (r + r) (intervalSet p J.interval) ∩ intervalSet p J.interval).Nonempty ↔
      r < t) :
    Nonempty (Witness k hr (J.obj k hp) 0) ↔ t ≤ r := by
  change Nonempty (Witness k hr ((Single J.degree).obj ISh[hp,J.interval]) 0) ↔ _
  rw [nonempty_witness_zero_iff, aug_single_eq_zero_iff k _ ISh[hp,J.interval] J.degree, ← not_lt]
  constructor
  · intro hz hlt
    exact (H0Aug_interval_ne_zero_iff (k := k) (add_nonneg hr hr) hp J.interval).2
      (h.2 hlt) (by simp only [H0Aug, hz, Functor.map_zero, zero_comp])
  · exact fun hn => aug_zero_single_of_outSet0_disjoint k hp J.interval
      (add_nonneg hr hr) hne (mt h.1 hn)

/-- Deletion of a left-closed bounded interval is possible from the half-length radius onward. -/
theorem nonempty_witness_interval_Ico_zero_iff (hp : StrictMono p) (J : GradedInterval m)
    {a b : ℝ} (hab : a < b) (hJ : intervalSet p J.interval = Set.Ico a b)
    {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (Witness k hr (J.obj k hp) 0) ↔ (b - a) / 2 ≤ r := by
  refine witness_interval_zero_iff_of_overlap_iff k hp J hr ?_ ?_
  · rw [hJ, outSet0_Ico (add_nonneg hr hr) hab]
    exact Set.nonempty_Ico.mpr (by linarith)
  rw [hJ, outSet0_Ico (add_nonneg hr hr) hab]
  constructor
  · rintro ⟨x, ⟨_, hx⟩, ⟨ha, _⟩⟩
    linarith
  · intro ht
    exact ⟨a, ⟨by linarith, by linarith⟩, ⟨le_rfl, hab⟩⟩

/-- Deletion of a right-closed bounded interval is possible from the half-length radius onward. -/
theorem nonempty_witness_interval_Ioc_zero_iff (hp : StrictMono p) (J : GradedInterval m)
    {a b : ℝ} (hab : a < b) (hJ : intervalSet p J.interval = Set.Ioc a b)
    {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (Witness k hr (J.obj k hp) 0) ↔ (b - a) / 2 ≤ r := by
  refine witness_interval_zero_iff_of_overlap_iff k hp J hr ?_ ?_
  · rw [hJ, outSet0_Ioc (add_nonneg hr hr) hab]
    exact Set.nonempty_Ioc.mpr (by linarith)
  rw [hJ, outSet0_Ioc (add_nonneg hr hr) hab]
  constructor
  · rintro ⟨x, ⟨hx, _⟩, ⟨_, hb⟩⟩
    linarith
  · intro ht
    exact ⟨b, ⟨by linarith, by linarith⟩, ⟨hab, le_rfl⟩⟩

/-- A bounded interval closed on the left has deletion cost equal to half its length. -/
theorem distance_interval_Ico_zero (hp : StrictMono p) (J : GradedInterval m)
    {a b : ℝ} (hab : a < b) (hJ : intervalSet p J.interval = Set.Ico a b) :
    distance (J.obj k hp) 0 = ENNReal.ofReal ((b - a) / 2) := by
  let t : ℝ≥0 := ⟨(b - a) / 2, by linarith⟩
  change _ = ENNReal.ofReal (t : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact distance_zero_eq_of_witness_iff k (t := t) fun r =>
    nonempty_witness_interval_Ico_zero_iff k hp J hab hJ r.coe_nonneg

/-- A bounded interval closed on the right has deletion cost equal to half its length. -/
theorem distance_interval_Ioc_zero (hp : StrictMono p) (J : GradedInterval m)
    {a b : ℝ} (hab : a < b) (hJ : intervalSet p J.interval = Set.Ioc a b) :
    distance (J.obj k hp) 0 = ENNReal.ofReal ((b - a) / 2) := by
  let t : ℝ≥0 := ⟨(b - a) / 2, by linarith⟩
  change _ = ENNReal.ofReal (t : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact distance_zero_eq_of_witness_iff k (t := t) fun r =>
    nonempty_witness_interval_Ioc_zero_iff k hp J hab hJ r.coe_nonneg

/-- A nonempty bounded closed interval has infinite deletion cost. -/
theorem distance_interval_Icc_zero (hp : StrictMono p) (J : GradedInterval m)
    {a b : ℝ} (hab : a ≤ b) (hJ : intervalSet p J.interval = Set.Icc a b) :
    distance (J.obj k hp) 0 = ⊤ := by
  apply distance_interval_zero_of_overlap k hp J
  intro r
  rw [hJ, outSet0_Icc (add_nonneg r.coe_nonneg r.coe_nonneg) hab]
  have hr := r.coe_nonneg
  exact ⟨a, ⟨by linarith, by linarith⟩, ⟨le_rfl, hab⟩⟩

/-- A singleton interval sheaf in any degree has infinite deletion cost. -/
theorem distance_interval_singleton_zero (hp : StrictMono p) (J : GradedInterval m)
    {a : ℝ} (hJ : intervalSet p J.interval = {a}) :
    distance (J.obj k hp) 0 = ⊤ :=
  distance_interval_Icc_zero k hp J le_rfl (hJ.trans (Set.Icc_self a).symm)

/-- A right ray with its endpoint has infinite deletion cost. -/
theorem distance_interval_Ici_zero (hp : StrictMono p) (J : GradedInterval m)
    {a : ℝ} (hJ : intervalSet p J.interval = Set.Ici a) :
    distance (J.obj k hp) 0 = ⊤ := by
  apply distance_interval_zero_of_overlap k hp J
  intro r
  rw [hJ, outSet0_Ici (add_nonneg r.coe_nonneg r.coe_nonneg)]
  exact ⟨a, Set.mem_Ici.mpr (sub_le_self _ (add_nonneg r.coe_nonneg r.coe_nonneg)),
    Set.mem_Ici.mpr le_rfl⟩

/-- A left ray with its endpoint has infinite deletion cost. -/
theorem distance_interval_Iic_zero (hp : StrictMono p) (J : GradedInterval m)
    {b : ℝ} (hJ : intervalSet p J.interval = Set.Iic b) :
    distance (J.obj k hp) 0 = ⊤ := by
  apply distance_interval_zero_of_overlap k hp J
  intro r
  rw [hJ, outSet0_Iic (add_nonneg r.coe_nonneg r.coe_nonneg)]
  exact ⟨b, Set.mem_Iic.mpr (le_add_of_nonneg_right (add_nonneg r.coe_nonneg r.coe_nonneg)),
    Set.mem_Iic.mpr le_rfl⟩

/-- A right ray with its endpoint excluded has infinite deletion cost. -/
theorem distance_interval_Ioi_zero (hp : StrictMono p) (J : GradedInterval m)
    {a : ℝ} (hJ : intervalSet p J.interval = Set.Ioi a) :
    distance (J.obj k hp) 0 = ⊤ := by
  apply distance_interval_zero_of_overlap k hp J
  intro r
  rw [hJ, outSet0_Ioi (add_nonneg r.coe_nonneg r.coe_nonneg)]
  refine ⟨a + (r : ℝ) + r + 1, Set.mem_Ioi.mpr ?_, Set.mem_Ioi.mpr ?_⟩ <;>
    linarith [r.coe_nonneg]

/-- A left ray with its endpoint excluded has infinite deletion cost. -/
theorem distance_interval_Iio_zero (hp : StrictMono p) (J : GradedInterval m)
    {b : ℝ} (hJ : intervalSet p J.interval = Set.Iio b) :
    distance (J.obj k hp) 0 = ⊤ := by
  apply distance_interval_zero_of_overlap k hp J
  intro r
  rw [hJ, outSet0_Iio (add_nonneg r.coe_nonneg r.coe_nonneg)]
  refine ⟨b - (r : ℝ) - r - 1, Set.mem_Iio.mpr ?_, Set.mem_Iio.mpr ?_⟩ <;>
    linarith [r.coe_nonneg]

/-- The whole-line interval sheaf has infinite deletion cost. -/
theorem distance_interval_univ_zero (hp : StrictMono p) (J : GradedInterval m)
    (hJ : intervalSet p J.interval = Set.univ) :
    distance (J.obj k hp) 0 = ⊤ := by
  apply distance_interval_zero_of_overlap k hp J
  intro r
  rw [hJ, outSet0_univ (add_nonneg r.coe_nonneg r.coe_nonneg)]
  exact ⟨0, trivial, trivial⟩

/-- A nonempty bounded open interval has infinite deletion cost. -/
theorem distance_interval_Ioo_zero (hp : StrictMono p) (J : GradedInterval m)
    {a b : ℝ} (hab : a < b) (hJ : intervalSet p J.interval = Set.Ioo a b) :
    distance (J.obj k hp) 0 = ⊤ := by
  rw [distance_eq_top_iff]
  intro r
  refine ⟨fun w => ?_⟩
  have hz := (aug_single_eq_zero_iff k _ ISh[hp,J.interval] J.degree).mp
    (nonempty_witness_zero_iff.mp ⟨w⟩)
  let F := (GradedInterval.mk J.interval 0).obj k hp
  let Y := (Single 1).obj (skyscraperSheaf k ((a + b) / 2))
  have hw : Nonempty (Witness k r.coe_nonneg F 0) := nonempty_witness_zero_iff.mpr hz
  have ht := distance_singleFunctor_skyscraper_zero k ((a + b) / 2) 1
  have hr : 0 ≤ (b - a) / 2 := by linarith
  obtain ⟨e⟩ := nonempty_iso_T_interval_Ioo_shifted_skyscraper k hp J.interval hr hab
    (by linarith) hJ
  obtain ⟨v⟩ := hw
  let u := (Witness.toConvolution F hr).congr (Iso.refl _) e
  exact (distance_eq_top_iff.mp ht ⟨_, add_nonneg hr r.coe_nonneg⟩).false (u.symm.trans v)

private theorem interval_eq_of_same_support (hp : StrictMono p)
    {J K : FiniteInterval (2 * m + 1)} (h : intervalSet p J = intervalSet p K) : J = K := by
  have hAlive (v : Fin (2 * m + 1)) : J.alive v ↔ K.alive v := by
    obtain ⟨x, hx⟩ := stratum_nonempty hp v
    rw [← mem_intervalSet_iff_alive hx, ← mem_intervalSet_iff_alive hx, h]
  let j : Fin (2 * m + 1) := ⟨J.birth, J.birth_lt_death.trans_le J.death_le_size⟩
  let k' : Fin (2 * m + 1) := ⟨K.birth, K.birth_lt_death.trans_le K.death_le_size⟩
  have hjd := J.death_le_size
  have hkd := K.death_le_size
  have hjb := J.birth_lt_death
  have hkb := K.birth_lt_death
  let j' : Fin (2 * m + 1) := ⟨J.death - 1, by omega⟩
  let k'' : Fin (2 * m + 1) := ⟨K.death - 1, by omega⟩
  have hj := (hAlive j).1 ⟨le_rfl, J.birth_lt_death⟩
  have hk := (hAlive k').2 ⟨le_rfl, K.birth_lt_death⟩
  have hj' := (hAlive j').1 (by
    change J.birth ≤ J.death - 1 ∧ J.death - 1 < J.death
    omega)
  have hk' := (hAlive k'').2 (by
    change K.birth ≤ K.death - 1 ∧ K.death - 1 < K.death
    omega)
  have hb : J.birth = K.birth := le_antisymm hk.1 hj.1
  have hd : J.death = K.death := by
    have h1 : J.death - 1 < K.death := hj'.2
    have h2 : K.death - 1 < J.death := hk'.2
    omega
  cases J
  cases K
  simpa only [FiniteInterval.mk.injEq] using And.intro hb hd

private def refineIntervalIso (hp : StrictMono p) (hq : StrictMono q)
    (hpq : breakpoints p ⊆ breakpoints q) (J : FiniteInterval (2 * m + 1)) :
    ISh[hp,J] ≅ ISh[hq,refineInterval hp hq hpq J] :=
  (sectionsExtensionIso k hq).app
    ⟨ISh[hp,J], (isConstructible_extension k hp
      (M := interval (orient m) J) fun _ => inferInstance).mono hpq⟩ ≪≫
    (extension k hq).mapIso (sectionsExtensionIntervalIso k hp hq hpq J)

omit [HasDerivedCategory Sh] [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
/-- Two interval sheaves with the same support are isomorphic across breakpoint families. -/
theorem nonempty_iso_intervalSheaf_of_intervalSet_eq (hp : StrictMono p) (hq : StrictMono q)
    {J : FiniteInterval (2 * m + 1)} {K : FiniteInterval (2 * n + 1)}
    (h : intervalSet p J = intervalSet q K) : Nonempty (ISh[hp,J] ≅ ISh[hq,K]) := by
  let B := breakpoints p ∪ breakpoints q
  let hs := strictMono_sortedBreakpoints B
  have hps : breakpoints p ⊆ breakpoints (sortedBreakpoints B) := by
    rw [breakpoints_sortedBreakpoints]
    exact Finset.subset_union_left
  have hqs : breakpoints q ⊆ breakpoints (sortedBreakpoints B) := by
    rw [breakpoints_sortedBreakpoints]
    exact Finset.subset_union_right
  have he := interval_eq_of_same_support hs
    ((intervalSet_refineInterval hp hs hps J).trans
      (h.trans (intervalSet_refineInterval hq hs hqs K).symm))
  exact ⟨refineIntervalIso k hp hs hps J ≪≫
    (extension k hs).mapIso (eqToIso (congrArg (interval (k := k) (orient B.card)) he)) ≪≫
    (refineIntervalIso k hq hs hqs K).symm⟩

private def convSingleIso {r : ℝ} {E F : Sh} {j : ℤ}
    (e : (T k r).obj ((Single 0).obj F) ≅ (Single j).obj E) (i : ℤ) :
    (T k r).obj ((Single i).obj F) ≅ (Single (j + i)).obj E :=
  (T k r).mapIso (by simpa only [zero_add] using (shiftSingleIso k F 0 i).symm) ≪≫
    ((T k r).commShiftIso (-i)).app _ ≪≫ (shiftFunctor D⁺ (-i)).mapIso e ≪≫
    shiftSingleIso k E j i

private def convGradedIso (hp : StrictMono p) (J : GradedInterval m)
    {r : ℝ} {F : Sh} {j : ℤ}
    (e : (T k r).obj ((Single 0).obj ISh[hp,J.interval]) ≅ (Single j).obj F) :
    (T k r).obj (J.obj k hp) ≅ (Single (j + J.degree)).obj F := by
  change (T k r).obj ((Single J.degree).obj ISh[hp,J.interval]) ≅ _
  exact convSingleIso k e J.degree

omit [HasDerivedCategory Sh] [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem hom_extension_eq_zero_of_stalk (hp : StrictMono p) (hq : StrictMono q)
    {J : FiniteInterval (2 * m + 1)} {K : FiniteInterval (2 * n + 1)}
    (f : ISh[hp,J] ⟶ ISh[hq,K])
    (h : ∀ x ∈ intervalSet p J, x ∈ intervalSet q K →
      (TopCat.Presheaf.stalkFunctor (ModuleCat k) (X := realLine) x).map f.hom = 0) :
    f = 0 := by
  let F := ISh[hp,J]
  let G := ISh[hq,K]
  let st (x : ℝ) := TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) x
  have hst (x : ℝ) : (st x).map f.hom = 0 := by
    by_cases hx : x ∈ intervalSet p J
    · by_cases hy : x ∈ intervalSet q K
      · exact h x hx hy
      · exact (isZero_stalk_extension_interval k hq hy).eq_of_tgt _ _
    · exact (isZero_stalk_extension_interval k hp hx).eq_of_src _ _
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change f.hom.app V = 0
  ext s : 2
  change f.hom.app V s = (0 : G.presheaf.obj V)
  refine TopCat.Presheaf.section_ext G V.unop _ _ fun x hx => ?_
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply V.unop x hx f.hom, hst x]
  change (0 : F.presheaf.stalk x →ₗ[k] G.presheaf.stalk x) (F.presheaf.germ V.unop x hx s) =
    G.presheaf.germ V.unop x hx 0
  rw [map_zero]
  rfl

omit [HasDerivedCategory Sh] [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem hom_extension_eq_zero_of_nonclosed (hp : StrictMono p) (hq : StrictMono q)
    {J : FiniteInterval (2 * m + 1)} {K : FiniteInterval (2 * n + 1)}
    (hj : IsClosed (intervalSet p J)) (hk : ¬ IsClosed (intervalSet q K))
    (f : ISh[hp,J] ⟶ ISh[hq,K]) : f = 0 := by
  let U : TopologicalSpace.Opens realLine := ⊤
  let F := ISh[hp,J]
  let st (x : ℝ) := TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) x
  have hz := isZero_sections_extension_interval k hq K (U := U) Set.ordConnected_univ
    (fun h => hk (closure_eq_iff_isClosed.mp (Set.Subset.antisymm
      (fun _ hx => h.1 ⟨hx, TopologicalSpace.Opens.mem_top _⟩) subset_closure)))
  have htop : f.hom.app (Opposite.op U) = 0 := hz.eq_of_tgt _ _
  apply hom_extension_eq_zero_of_stalk k hp hq f
  intro x hx _
  have := isIso_germ_extension_interval k hp J (U := U) Set.ordConnected_univ
    (by rw [hj.closure_eq]; exact Set.inter_subset_left) (TopologicalSpace.Opens.mem_top x) hx
  change (st x).map f.hom = 0
  have hUx : x ∈ U := TopologicalSpace.Opens.mem_top x
  apply (cancel_epi (F.presheaf.germ U x hUx)).mp
  refine (TopCat.Presheaf.stalkFunctor_map_germ U x hUx f.hom).trans ?_
  rw [htop, zero_comp]
  exact (comp_zero (f := F.presheaf.germ U x hUx)).symm

omit [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem hom_eq_zero_of_interval_hom_eq_zero (hp : StrictMono p) (hq : StrictMono q)
    {J : FiniteInterval (2 * m + 1)} {K : FiniteInterval (2 * n + 1)} {d : ℤ} {X Y : D⁺}
    (e : X ≅ (Single d).obj ISh[hp,J]) (f : Y ≅ (Single d).obj ISh[hq,K])
    (h : ∀ v : ISh[hp,J] ⟶ ISh[hq,K], v = 0) (u : X ⟶ Y) : u = 0 := by
  obtain ⟨v, hv⟩ := (DerivedCategory.singleFunctor Sh d).map_surjective
    (Plus.ι.map (e.inv ≫ u ≫ f.hom))
  have he : (Single d).map v = e.inv ≫ u ≫ f.hom := Plus.ι.map_injective hv
  rw [h v, Functor.map_zero] at he
  apply (cancel_mono f.hom).mp
  apply (cancel_epi e.inv).mp
  simpa only [comp_zero, zero_comp] using he.symm

private theorem Witness.aug_eq_zero_of_hom_eq_zero {r : ℝ} {hr : 0 ≤ r} {X Y : D⁺}
    (w : Witness k hr X Y) (h : w.hom = 0) :
    (aug k (add_nonneg hr hr)).app X = 0 := by
  rw [← w.hom_inv, h, Functor.map_zero, zero_comp, comp_zero]

private theorem Witness.aug_target_eq_zero_of_hom_eq_zero {r : ℝ} {hr : 0 ≤ r}
    {X Y : D⁺} (w : Witness k hr X Y) (h : w.hom = 0) :
    (aug k (add_nonneg hr hr)).app Y = 0 := by
  simp only [← w.inv_hom, h, comp_zero]

private theorem no_witness_zero_of_distance_top {X : D⁺} (h : distance X 0 = ⊤)
    {r : ℝ} (hr : 0 ≤ r) : ¬ Nonempty (Witness k hr X 0) := by
  rintro ⟨w⟩
  exact (distance_eq_top_iff.mp h ⟨r, hr⟩).false w

private theorem closed_witness_subset (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b c e r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r)
    (hJ : intervalSet p J = Set.Icc a b) (hK : intervalSet q K = Set.Icc c e)
    (w : Witness k hr ((GradedInterval.mk J d).obj k hp)
      ((GradedInterval.mk K d).obj k hq)) :
    Set.Icc c e ⊆ Set.Icc (a - r) (b + r) := by
  by_contra hn
  obtain ⟨L, hL, ⟨iso⟩⟩ := exists_intervalSheaf_T_Icc (k := k) hp J hr hab hJ
  let hl := strictMono_sortedBreakpoints (bandBreakpoints p r)
  have f0 := hom_eq_zero_of_interval_hom_eq_zero k hl hq
    (by simpa only [zero_add] using convGradedIso k hp ⟨J, d⟩ iso) (Iso.refl _)
    (hom_extension_interval_eq_zero_of_not_subset hl hq
      (hL.symm ▸ isClosed_Icc) (hK.symm ▸ isClosed_Icc)
      (by rw [hL, hK]; exact hn)) w.hom
  exact no_witness_zero_of_distance_top k (distance_interval_Icc_zero k hp ⟨J, d⟩ hab hJ) hr
    (nonempty_witness_zero_iff.mpr (w.aug_eq_zero_of_hom_eq_zero k f0))

private theorem distance_le_Icc (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e)
    (hJ : intervalSet p J = Set.Icc a b) (hK : intervalSet q K = Set.Icc c e) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) ≤
      ENNReal.ofReal (|(a + b) / 2 - (c + e) / 2| + |(b - a) / 2 - (e - c) / 2|) := by
  let x := (a + b) / 2
  let y := (c + e) / 2
  let r := (b - a) / 2
  let s := (e - c) / 2
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hx : Set.Icc (x - r) (x + r) = Set.Icc a b := by
    rw [show x - r = a by dsimp [x, r]; ring, show x + r = b by dsimp [x, r]; ring]
  have hy : Set.Icc (y - s) (y + s) = Set.Icc c e := by
    rw [show y - s = c by dsimp [y, s]; ring, show y + s = e by dsimp [y, s]; ring]
  obtain ⟨_, _, hu, U, hU, ⟨eu⟩⟩ := exists_iso_T_skyscraper k x hr
  obtain ⟨_, _, hv, V, hV, ⟨ev⟩⟩ := exists_iso_T_skyscraper k y hs
  obtain ⟨i⟩ := nonempty_iso_intervalSheaf_of_intervalSet_eq k hu hp
    (hU.trans (hx.trans hJ.symm))
  obtain ⟨j⟩ := nonempty_iso_intervalSheaf_of_intervalSet_eq k hv hq
    (hV.trans (hy.trans hK.symm))
  let ex := eu ≪≫ (Single 0).mapIso i
  let ey := ev ≪≫ (Single 0).mapIso j
  obtain ⟨w⟩ := (nonempty_witness_skyscraper_iff k x y (abs_nonneg (x - y))).2 le_rfl
  have nested (z : ℝ) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
      Witness k (sub_nonneg.mpr htu) ((T k t).obj (skyscraper k z))
        ((T k u).obj (skyscraper k z)) :=
    let h := sub_nonneg.mpr htu
    (Witness.toConvolution ((T k t).obj (skyscraper k z)) h).congr (Iso.refl _)
      ((TCompOfEq k ht h (by ring)).app (skyscraper k z))
  have pair : ∃ h : 0 ≤ |x - y| + |r - s|,
      Nonempty (Witness k h ((T k r).obj (skyscraper k x)) ((T k s).obj (skyscraper k y))) := by
    refine ⟨add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
    rcases le_total r s with hrs | hsr
    · exact ⟨((w.convolve hr).trans (nested y hr hrs)).mono
        (by rw [abs_of_nonpos (sub_nonpos.mpr hrs)]; linarith)⟩
    · exact ⟨((nested x hs hsr).symm.trans (w.convolve hs)).mono
        (by rw [abs_of_nonneg (sub_nonneg.mpr hsr)]; linarith)⟩
  obtain ⟨h, ⟨v⟩⟩ := pair
  let sx := (shiftFunctor D⁺ (-d)).mapIso ex ≪≫ shiftSingleIso k ISh[hp,J] 0 d
  let sy := (shiftFunctor D⁺ (-d)).mapIso ey ≪≫ shiftSingleIso k ISh[hq,K] 0 d
  change distance ((Single d).obj ISh[hp,J]) ((Single d).obj ISh[hq,K]) ≤ _
  exact ((v.shift (-d)).congr
    (by simpa only [zero_add] using sx) (by simpa only [zero_add] using sy)).distance_le

/-- In a common degree, the cost of two closed bounded intervals is the larger
of the two absolute endpoint differences. Degenerate closed intervals are singletons. -/
theorem distance_interval_Icc_Icc (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e)
    (hJ : intervalSet p J = Set.Icc a b) (hK : intervalSet q K = Set.Icc c e) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      ENNReal.ofReal (max |a - c| |b - e|) := by
  refine le_antisymm ?_ (le_distance_iff.mpr fun r ⟨w⟩ => ?_)
  · have halg : |(a + b) / 2 - (c + e) / 2| + |(b - a) / 2 - (e - c) / 2| =
        max |a - c| |b - e| := by
      simp only [abs_eq_max_neg, max_def]
      split_ifs <;> linarith
    rw [← halg]
    exact distance_le_Icc k hp hq J K d hab hce hJ hK
  · have ⟨h₁, h₂⟩ := (Set.Icc_subset_Icc_iff hce).mp
      (closed_witness_subset k hp hq J K d hab r.coe_nonneg hJ hK w)
    have ⟨h₃, h₄⟩ := (Set.Icc_subset_Icc_iff hab).mp
      (closed_witness_subset k hq hp K J d hce r.coe_nonneg hK hJ w.symm)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
      (abs_le.mpr ⟨by linarith, by linarith⟩))

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))] in
private theorem closed_subset_of_nonzero_hom_T_Ioo_succ (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b r : ℝ} (hr : 0 ≤ r) (hab : a < b) (hJ : intervalSet p J = Set.Ioo a b)
    {f : (T k r).obj ((GradedInterval.mk J d).obj k hp) ⟶
      (GradedInterval.mk K (d + 1)).obj k hq} (hf : f ≠ 0) :
    IsClosed (intervalSet q K) ∧ intervalSet q K ⊆ Set.Icc (b - r) (a + r) := by
  have hb : b - a ≤ 2 * r := by
    by_contra! hlt
    obtain ⟨L, _, ⟨iso⟩⟩ := exists_intervalSheaf_T_Ioo_below (k := k) hp J hr hab hlt hJ
    have e' := convGradedIso k hp ⟨J, d⟩ iso
    have ht : ((GradedInterval.mk K (d + 1)).obj k hq).IsGE (d + 1) := by
      change ((Single (d + 1)).obj ISh[hq,K]).IsGE (d + 1)
      infer_instance
    have hz : e'.inv ≫ f = 0 :=
      Plus.TStructure.t.zero_of_isLE_of_isGE _ (0 + d) (d + 1)
        (by omega) inferInstance ht
    exact hf ((cancel_epi e'.inv).mp (hz.trans (comp_zero (f := e'.inv)).symm))
  obtain ⟨L, hL⟩ := exists_intervalSet_outSet1 hp J hr (by
    rw [hJ, outSet1_Ioo hr hab]
    exact Set.nonempty_Icc.mpr (by linarith))
  let hl := strictMono_sortedBreakpoints (bandBreakpoints p r)
  obtain ⟨iso⟩ := nonempty_iso_T_interval_one (k := k) hp J hr hl L hL
  have htL : intervalSet (sortedBreakpoints (bandBreakpoints p r)) L =
      Set.Icc (b - r) (a + r) := by rw [hL, hJ, outSet1_Ioo hr hab]
  have hclosed : IsClosed (intervalSet _ L) := htL.symm ▸ isClosed_Icc
  have hnonzero (h : ∀ u : ISh[hl,L] ⟶ ISh[hq,K], u = 0) : False :=
    hf (hom_eq_zero_of_interval_hom_eq_zero k hl hq
      (by simpa only [add_comm 1 d] using convGradedIso k hp ⟨J, d⟩ iso) (Iso.refl _) h f)
  have hK : IsClosed (intervalSet q K) := by
    by_contra hn
    exact hnonzero (hom_extension_eq_zero_of_nonclosed k hl hq hclosed hn)
  refine ⟨hK, ?_⟩
  by_contra hn
  rw [← htL] at hn
  exact hnonzero (hom_extension_interval_eq_zero_of_not_subset hl hq hclosed hK hn)

/-- In consecutive degrees, the cost of a bounded open interval and a bounded closed interval
is the least radius whose degree-one output contains the closed interval. -/
theorem distance_interval_Ioo_Icc_succ (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b c e : ℝ} (hab : a < b) (hce : c ≤ e)
    (hJ : intervalSet p J = Set.Ioo a b) (hK : intervalSet q K = Set.Icc c e) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K (d + 1)).obj k hq) =
      ENNReal.ofReal (max (b - c) (e - a)) := by
  let X := (GradedInterval.mk J d).obj k hp
  let Y := (GradedInterval.mk K (d + 1)).obj k hq
  let t := (b - a) / 2
  let x := (a + b) / 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  obtain ⟨e₀⟩ := nonempty_iso_T_interval_Ioo_shifted_skyscraper k hp J ht hab
    (by dsimp [t]; ring) hJ
  let v := (Witness.toConvolution X ht).congr (Iso.refl _)
    (convGradedIso k hp ⟨J, d⟩ e₀ ≪≫ eqToIso (congrArg
      (fun i => (Single i).obj (skyscraperSheaf k x)) (add_comm 1 d)))
  let L : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩
  have hL : intervalSet (fun _ : Fin 1 => x) L = {x} :=
    intervalSet_eq_singleton (Subsingleton.strictMono _) (i := 0) rfl rfl
  let hmono : StrictMono (fun _ : Fin 1 => x) := Subsingleton.strictMono _
  obtain ⟨i⟩ := nonempty_iso_skyscraperSheaf_interval k hmono L hL
  let X' := (GradedInterval.mk L (d + 1)).obj k hmono
  have ix : (Single (d + 1)).obj (skyscraperSheaf k x) ≅ X' := (Single (d + 1)).mapIso i
  have hv := (v.congr (Iso.refl _) ix).distance_le
  refine le_antisymm ?_ (le_distance_iff.mpr fun r ⟨w⟩ => ?_)
  · have hc := distance_interval_Icc_Icc k hmono hq L K
      (d + 1) le_rfl hce (hL.trans (Set.Icc_self x).symm) hK
    have hsum : t + max |x - c| |x - e| = max (b - c) (e - a) := by
      dsimp [t, x]
      simp only [abs_eq_max_neg, max_def]
      split_ifs <;> linarith
    rw [← hsum, ENNReal.ofReal_add ht (le_trans (abs_nonneg _) (le_max_left _ _))]
    exact (distance_triangle X X' Y).trans (add_le_add hv hc.le)
  · have htop := distance_interval_Icc_zero k hq ⟨K, d + 1⟩ hce hK
    have hnonzero : w.hom ≠ 0 := fun hz =>
      no_witness_zero_of_distance_top k htop r.coe_nonneg
        (nonempty_witness_zero_iff.mpr (w.aug_target_eq_zero_of_hom_eq_zero k hz))
    have hsub := (closed_subset_of_nonzero_hom_T_Ioo_succ k hp hq J K d
      r.coe_nonneg hab hJ hnonzero).2
    rw [hK] at hsub
    obtain ⟨h₁, h₂⟩ := (Set.Icc_subset_Icc_iff hce).mp hsub
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (max_le (by linarith) (by linarith))

/-- An open bounded interval has infinite cost against an interval one degree higher
whose support is nonclosed or unbounded. -/
theorem distance_interval_Ioo_succ_eq_top (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b : ℝ} (hab : a < b) (hJ : intervalSet p J = Set.Ioo a b)
    (hK : ¬ (IsClosed (intervalSet q K) ∧
      BddBelow (intervalSet q K) ∧ BddAbove (intervalSet q K))) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K (d + 1)).obj k hq) =
      ⊤ := by
  rw [distance_eq_top_iff]
  intro r
  refine ⟨fun w => ?_⟩
  have hz : w.hom = 0 := by
    by_contra hf
    obtain ⟨hc, hs⟩ := closed_subset_of_nonzero_hom_T_Ioo_succ k hp hq J K d
      r.coe_nonneg hab hJ hf
    exact hK ⟨hc, bddBelow_Icc.mono hs, bddAbove_Icc.mono hs⟩
  exact no_witness_zero_of_distance_top k (distance_interval_Ioo_zero k hp ⟨J, d⟩ hab hJ)
    r.coe_nonneg (nonempty_witness_zero_iff.mpr (w.aug_eq_zero_of_hom_eq_zero k hz))

/-- Endpoint data for a nonempty real interval. A singleton is a closed interval
with coincident endpoints. -/
inductive IntervalEndpoints where
  | icc (a b : ℝ) (h : a ≤ b)
  | ico (a b : ℝ) (h : a < b)
  | ioc (a b : ℝ) (h : a < b)
  | ioo (a b : ℝ) (h : a < b)
  | ici (a : ℝ)
  | iic (b : ℝ)
  | ioi (a : ℝ)
  | iio (b : ℝ)
  | univ

namespace IntervalEndpoints

/-- The subset of the real line determined by the endpoint data. -/
def support : IntervalEndpoints → Set ℝ
  | .icc a b _ => Set.Icc a b
  | .ico a b _ => Set.Ico a b
  | .ioc a b _ => Set.Ioc a b
  | .ioo a b _ => Set.Ioo a b
  | .ici a => Set.Ici a
  | .iic b => Set.Iic b
  | .ioi a => Set.Ioi a
  | .iio b => Set.Iio b
  | .univ => Set.univ

/-- Deleting a bounded half-open interval costs half its length. The other
endpoint types have infinite deletion cost. -/
def deletionCost : IntervalEndpoints → ℝ≥0∞
  | .ico a b _ | .ioc a b _ => ENNReal.ofReal ((b - a) / 2)
  | _ => ⊤

/-- Whether the interval can have degree-one output under nonnegative convolution. -/
def hasDegreeOneOutput : IntervalEndpoints → Bool
  | .ioo .. => true
  | _ => false

private theorem outSet1_eq_empty {r : ℝ} (hr : 0 ≤ r) (E : IntervalEndpoints)
    (h : E.hasDegreeOneOutput = false) : outSet1 r E.support = ∅ := by
  cases E with
  | icc a b hab => exact outSet1_Icc hr hab
  | ico a b hab => exact outSet1_Ico hr hab
  | ioc a b hab => exact outSet1_Ioc hr hab
  | ioo => cases h
  | ici a => exact outSet1_Ici hr a
  | iic b => exact outSet1_Iic hr b
  | ioi a => exact outSet1_Ioi hr a
  | iio b => exact outSet1_Iio hr b
  | univ => exact outSet1_univ hr

/-- The endpoint deletion cost computes the band distance to zero in every degree. -/
theorem distance_zero_eq (hp : StrictMono p) (J : GradedInterval m)
    (E : IntervalEndpoints) (hJ : intervalSet p J.interval = E.support) :
    distance (J.obj k hp) 0 = E.deletionCost := by
  cases E with
  | icc a b h => exact distance_interval_Icc_zero k hp J h hJ
  | ico a b h => exact distance_interval_Ico_zero k hp J h hJ
  | ioc a b h => exact distance_interval_Ioc_zero k hp J h hJ
  | ioo a b h => exact distance_interval_Ioo_zero k hp J h hJ
  | ici a => exact distance_interval_Ici_zero k hp J hJ
  | iic b => exact distance_interval_Iic_zero k hp J hJ
  | ioi a => exact distance_interval_Ioi_zero k hp J hJ
  | iio b => exact distance_interval_Iio_zero k hp J hJ
  | univ => exact distance_interval_univ_zero k hp J hJ

end IntervalEndpoints

private theorem distance_eq_sup_deletions_of_hom_eq_zero {X Y : D⁺}
    (h : ∀ r : ℝ≥0, ∀ f : (T k r).obj X ⟶ Y, f = 0) :
    distance X Y = distance X 0 ⊔ distance Y 0 := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro r hr hfin
    let s := distance X 0 ⊔ distance Y 0
    let t := s.toNNReal + r
    have ht : (t : ℝ≥0∞) = s + r := by rw [ENNReal.coe_add, ENNReal.coe_toNNReal hfin.ne]
    have hs : s < (t : ℝ≥0∞) :=
      ht.symm ▸ ENNReal.lt_add_right hfin.ne (ENNReal.coe_ne_zero.mpr hr.ne')
    obtain ⟨u⟩ := nonempty_witness_of_distance_lt
      ((le_sup_left : distance X 0 ≤ s).trans_lt hs)
    obtain ⟨v⟩ := nonempty_witness_of_distance_lt
      ((le_sup_right : distance Y 0 ≤ s).trans_lt hs)
    have w : Witness k t.coe_nonneg X Y := ⟨0, 0,
      by simp [nonempty_witness_zero_iff.mp ⟨u⟩],
      by simp [nonempty_witness_zero_iff.mp ⟨v⟩]⟩
    simpa only [ENNReal.ofReal_coe_nnreal, ht] using w.distance_le
  · apply le_distance_iff.mpr
    intro r ⟨w⟩
    have hz := h r w.hom
    obtain ⟨u⟩ := (nonempty_witness_zero_iff (hε := r.coe_nonneg)).mpr
      (w.aug_eq_zero_of_hom_eq_zero k hz)
    obtain ⟨v⟩ := (nonempty_witness_zero_iff (hε := r.coe_nonneg)).mpr
      (w.aug_target_eq_zero_of_hom_eq_zero k hz)
    exact sup_le (by simpa only [ENNReal.ofReal_coe_nnreal] using u.distance_le)
      (by simpa only [ENNReal.ofReal_coe_nnreal] using v.distance_le)

omit [HasDerivedCategory Sh] [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem hom_extension_eq_zero_Ico_Ioc (hp : StrictMono p) (hq : StrictMono q)
    {J : FiniteInterval (2 * m + 1)} {K : FiniteInterval (2 * n + 1)}
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hJ : intervalSet p J = Set.Ico a b) (hK : intervalSet q K = Set.Ioc c e)
    (f : ISh[hp,J] ⟶ ISh[hq,K]) : f = 0 := by
  let F := ISh[hp,J]
  let st (x : ℝ) := TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) x
  apply hom_extension_eq_zero_of_stalk k hp hq f
  intro x hx hy
  have hxJ : x ∈ Set.Ico a b := hJ ▸ hx
  have hxK : x ∈ Set.Ioc c e := hK ▸ hy
  let U : TopologicalSpace.Opens realLine := ⟨Set.Ioo (min a c - 1) b, isOpen_Ioo⟩
  have hxU : x ∈ U := ⟨by linarith [min_le_left a c, hxJ.1], hxJ.2⟩
  have hcU : c ∈ U := ⟨by linarith [min_le_right a c], hxK.1.trans hxJ.2⟩
  have hcl : closure (intervalSet p J) ∩ (U : Set ℝ) ⊆ intervalSet p J := by
    rw [hJ, closure_Ico hab.ne]
    exact fun _ h => ⟨h.1.1, h.2.2⟩
  have := isIso_germ_extension_interval k hp J Set.ordConnected_Ioo hcl hxU hx
  have hzero := isZero_sections_extension_interval_of_mem_closure k hq K
    Set.ordConnected_Ioo hcU (by rw [hK, closure_Ioc hce.ne]; exact ⟨le_rfl, hce.le⟩)
    (by rw [hK]; exact fun h => lt_irrefl c h.1)
  have htop : f.hom.app (Opposite.op U) = 0 := hzero.eq_of_tgt _ _
  change (st x).map f.hom = 0
  apply (cancel_epi (F.presheaf.germ U x hxU)).mp
  refine (TopCat.Presheaf.stalkFunctor_map_germ U x hxU f.hom).trans ?_
  rw [htop, zero_comp]
  exact (comp_zero (f := F.presheaf.germ U x hxU)).symm

/-- Opposite half-open types in a common degree have the larger of their deletion costs. -/
theorem distance_interval_Ico_Ioc (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hJ : intervalSet p J = Set.Ico a b) (hK : intervalSet q K = Set.Ioc c e) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      ENNReal.ofReal ((b - a) / 2) ⊔ ENNReal.ofReal ((e - c) / 2) := by
  rw [← distance_interval_Ico_zero k hp ⟨J, d⟩ hab hJ,
    ← distance_interval_Ioc_zero k hq ⟨K, d⟩ hce hK]
  apply distance_eq_sup_deletions_of_hom_eq_zero k
  intro r f
  obtain ⟨L, hL, ⟨iso⟩⟩ := exists_intervalSheaf_T_Ico (k := k) hp J r.coe_nonneg hab hJ
  let hl := strictMono_sortedBreakpoints (bandBreakpoints p (r : ℝ))
  exact hom_eq_zero_of_interval_hom_eq_zero k hl hq
    (by simpa only [zero_add] using convGradedIso k hp ⟨J, d⟩ iso) (Iso.refl _)
    (hom_extension_eq_zero_Ico_Ioc k hl hq (by linarith) hce hL hK) f

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))] in
private theorem isLE_T_interval_of_outSet1_eq_empty (hp : StrictMono p) (J : GradedInterval m)
    {r : ℝ} (hr : 0 ≤ r) (h : outSet1 r (intervalSet p J.interval) = ∅) :
    ((T k r).obj (J.obj k hp)).IsLE J.degree := by
  let C := (T k r).obj (J.obj k hp)
  rcases (outSet0 r (intervalSet p J.interval)).eq_empty_or_nonempty with hz | hne
  · have hzero := isZero_T_interval (k := k) hp J.interval hr hz h
    let S := shiftFunctor D⁺ (-J.degree)
    let e := (T k r).mapIso (by simpa only [zero_add] using
      (shiftSingleIso k ISh[hp,J.interval] 0 J.degree).symm) ≪≫
        ((T k r).commShiftIso (-J.degree)).app ((Single 0).obj ISh[hp,J.interval])
    have hC : IsZero C := (S.map_isZero hzero).of_iso e
    exact Plus.TStructure.t.isLE_of_iso (hC.isoZero).symm J.degree
  · obtain ⟨L, hL⟩ := exists_intervalSet_outSet0 hp J.interval hr hne
    obtain ⟨e⟩ := nonempty_iso_T_interval_zero (k := k) hp J.interval hr
      (strictMono_sortedBreakpoints (bandBreakpoints p r)) L hL
    simpa only [zero_add] using Plus.TStructure.t.isLE_of_iso (convGradedIso k hp J e).symm
      (0 + J.degree)

/-- If the lower degree is far enough below the upper one, or its interval has no
degree-one output, the pair cost is the larger of the two deletion costs. -/
theorem distance_interval_of_degree_lt (hp : StrictMono p) (hq : StrictMono q)
    (J : GradedInterval m) (K : GradedInterval n) (E F : IntervalEndpoints)
    (hJ : intervalSet p J.interval = E.support) (hK : intervalSet q K.interval = F.support)
    (hd : J.degree < K.degree)
    (h : J.degree + 1 < K.degree ∨ E.hasDegreeOneOutput = false) :
    distance (J.obj k hp) (K.obj k hq) = E.deletionCost ⊔ F.deletionCost := by
  rw [← E.distance_zero_eq k hp J hJ, ← F.distance_zero_eq k hq K hK]
  apply distance_eq_sup_deletions_of_hom_eq_zero k
  intro r f
  have hKge : (K.obj k hq).IsGE K.degree := by
    change ((Single K.degree).obj ISh[hq,K.interval]).IsGE K.degree
    infer_instance
  rcases h with hgap | hout
  · have : (J.obj k hp).IsLE J.degree := by
      change ((Single J.degree).obj ISh[hp,J.interval]).IsLE J.degree
      infer_instance
    exact Plus.TStructure.t.zero_of_isLE_of_isGE f (J.degree + 1) K.degree hgap
      (isLE_T_obj k r (J.obj k hp) J.degree) hKge
  · exact Plus.TStructure.t.zero_of_isLE_of_isGE f J.degree K.degree hd
      (isLE_T_interval_of_outSet1_eq_empty k hp J r.coe_nonneg
        (hJ.symm ▸ E.outSet1_eq_empty r.coe_nonneg hout)) hKge

namespace IntervalEndpoints

private def isBoundedClosed : IntervalEndpoints → Bool
  | .icc .. => true
  | _ => false

private theorem not_boundedClosed_of_isBoundedClosed_eq_false (E : IntervalEndpoints)
    (h : E.isBoundedClosed = false) :
    ¬ (IsClosed E.support ∧ BddBelow E.support ∧ BddAbove E.support) := by
  rintro ⟨hc, hl, hr⟩
  cases E with
  | icc => cases h
  | ico _ _ hab => exact hab.not_ge (isClosed_Ico_iff.mp hc)
  | ioc _ _ hab => exact hab.not_ge (isClosed_Ioc_iff.mp hc)
  | ioo _ _ hab => exact hab.not_ge (isClosed_Ioo_iff.mp hc)
  | ici a => exact not_bddAbove_Ici a hr
  | iic b => exact not_bddBelow_Iic b hl
  | ioi a => exact not_bddAbove_Ioi a hr
  | iio b => exact not_bddBelow_Iio b hl
  | univ => exact not_bddAbove_univ hr

private def pairCostOfLt (E F : IntervalEndpoints) (i j : ℤ) : ℝ≥0∞ :=
  if i + 1 < j ∨ E.hasDegreeOneOutput = false then E.deletionCost ⊔ F.deletionCost
  else
    match E, F with
    | .ioo a b _, .icc c e _ => ENNReal.ofReal (max (b - c) (e - a))
    | _, _ => ⊤

private theorem distance_eq_pairCostOfLt (hp : StrictMono p) (hq : StrictMono q)
    (J : GradedInterval m) (K : GradedInterval n) (E F : IntervalEndpoints)
    (hJ : intervalSet p J.interval = E.support) (hK : intervalSet q K.interval = F.support)
    (hd : J.degree < K.degree) :
    distance (J.obj k hp) (K.obj k hq) = E.pairCostOfLt F J.degree K.degree := by
  unfold pairCostOfLt
  split
  · exact distance_interval_of_degree_lt k hp hq J K E F hJ hK hd ‹_›
  · rename_i h
    have hdeg : K.degree = J.degree + 1 := by
      have hh : ¬ J.degree + 1 < K.degree := fun hg => h (Or.inl hg)
      omega
    have hout : E.hasDegreeOneOutput ≠ false := fun he => h (Or.inr he)
    rcases J with ⟨J, i⟩
    rcases K with ⟨K, j⟩
    dsimp only at hdeg
    subst j
    cases E <;> try exact (hout rfl).elim
    rename_i a b hab
    cases F with
    | icc x y hxy => exact distance_interval_Ioo_Icc_succ k hp hq J K i hab hxy hJ hK
    | _ =>
      all_goals
        apply distance_interval_Ioo_succ_eq_top k hp hq J K i hab hJ
        rw [hK]
        exact not_boundedClosed_of_isBoundedClosed_eq_false _ rfl

/-- The numeric pair cost for different degrees, bounded closed pairs in a common degree,
and opposite half-open types in a common degree. -/
def pairCost (E F : IntervalEndpoints) (i j : ℤ) : Option ℝ≥0∞ :=
  if i < j then some (E.pairCostOfLt F i j)
  else if j < i then some (F.pairCostOfLt E j i)
  else
    match E, F with
    | .icc a b _, .icc c e _ => some (ENNReal.ofReal (max |a - c| |b - e|))
    | .ico a b _, .ioc c e _ | .ioc a b _, .ico c e _ =>
      some (ENNReal.ofReal ((b - a) / 2) ⊔ ENNReal.ofReal ((e - c) / 2))
    | _, _ => none

/-- Every returned pair entry is the band distance used by graded matchings. -/
theorem distance_eq_of_pairCost (hp : StrictMono p) (hq : StrictMono q)
    (J : GradedInterval m) (K : GradedInterval n) (E F : IntervalEndpoints)
    (hJ : intervalSet p J.interval = E.support) (hK : intervalSet q K.interval = F.support)
    {c : ℝ≥0∞} (hc : E.pairCost F J.degree K.degree = some c) :
    distance (J.obj k hp) (K.obj k hq) = c := by
  unfold pairCost at hc
  split at hc
  · exact (distance_eq_pairCostOfLt k hp hq J K E F hJ hK ‹_›).trans (Option.some.inj hc)
  split at hc
  · rw [distance_comm]
    exact (distance_eq_pairCostOfLt k hq hp K J F E hK hJ ‹_›).trans (Option.some.inj hc)
  · have hdeg : J.degree = K.degree := le_antisymm (le_of_not_gt ‹_›) (le_of_not_gt ‹_›)
    rcases J with ⟨J, i⟩
    rcases K with ⟨K, j⟩
    dsimp only at hdeg
    subst j
    split at hc
    · exact (distance_interval_Icc_Icc k hp hq J K i (by assumption) (by assumption) hJ hK).trans
        (Option.some.inj hc)
    · exact (distance_interval_Ico_Ioc k hp hq J K i (by assumption) (by assumption) hJ hK).trans
        (Option.some.inj hc)
    · rw [distance_comm]
      exact (distance_interval_Ico_Ioc k hq hp K J i (by assumption) (by assumption) hK hJ).trans
        ((sup_comm _ _).trans (Option.some.inj hc))
    · contradiction

end IntervalEndpoints

/-- Rewrite a matching cost bound by numeric pair and deletion entries for its occurrences. -/
theorem GradedMatching.cost_le_iff_of_pairCost {I L : Type} (M : GradedMatching I L)
    (hp : StrictMono p) (hq : StrictMono q)
    (J : I → GradedInterval m) (K : L → GradedInterval n)
    (E : I → IntervalEndpoints) (F : L → IntervalEndpoints)
    (hJ : ∀ i, intervalSet p (J i).interval = (E i).support)
    (hK : ∀ j, intervalSet q (K j).interval = (F j).support) (c : I → L → ℝ≥0∞)
    (hc : ∀ i j, M.finite i = some j →
      (E i).pairCost (F j) (J i).degree (K j).degree = some (c i j)) {r : ℝ≥0∞} :
    M.cost (fun i => (J i).obj k hp) (fun j => (K j).obj k hq) ≤ r ↔
      (∀ i j, M.finite i = some j → c i j ≤ r) ∧
      (∀ i, M.finite i = none → (E i).deletionCost ≤ r) ∧
      (∀ j, (¬ ∃ i, M.finite i = some j) → (F j).deletionCost ≤ r) := by
  rw [M.cost_le_iff]
  simp only [fun i => IntervalEndpoints.distance_zero_eq k hp (J i) (E i) (hJ i),
    fun j => IntervalEndpoints.distance_zero_eq k hq (K j) (F j) (hK j)]
  constructor <;> rintro ⟨h, hleft, hright⟩ <;> refine ⟨?_, hleft, hright⟩
  · intro i j hij
    simpa only [(E i).distance_eq_of_pairCost k hp hq (J i) (K j) (F j)
      (hJ i) (hK j) (hc i j hij)] using h i j hij
  · intro i j hij
    simpa only [(E i).distance_eq_of_pairCost k hp hq (J i) (K j) (F j)
      (hJ i) (hK j) (hc i j hij)] using h i j hij

end TDA.Sheaf.BandConvolution
