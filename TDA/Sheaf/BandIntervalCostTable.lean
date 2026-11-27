import TDA.Sheaf.BandMatchingIntervalCosts
import TDA.Sheaf.BandDirectImageStability

/-!
# Numeric band costs for graded interval sheaves

Deletion costs are determined by the endpoint types. A bounded half-open interval
has deletion cost equal to half its length. Every other interval has infinite
deletion cost. The pair table computes the distance for all endpoint types
and cohomological degrees.
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

private def intervalMove (a b c e x : ℝ) : ℝ :=
  if x ≤ a then x - a + c else if b ≤ x then x - b + e
  else c + (x - a) * ((e - c) / (b - a))

private theorem intervalMove_strictMono {a b c e : ℝ} (hab : a < b) (hce : c < e) :
    StrictMono (intervalMove a b c e) := by
  have hs : 0 < (e - c) / (b - a) := div_pos (sub_pos.mpr hce) (sub_pos.mpr hab)
  have he : (b - a) * ((e - c) / (b - a)) = e - c := by
    field_simp [sub_ne_zero.mpr hab.ne']
  intro x y hxy
  unfold intervalMove
  split_ifs <;> nlinarith [mul_pos (sub_pos.mpr hxy) hs]

private theorem intervalMove_surjective {a b c e : ℝ} (hab : a < b) (hce : c < e) :
    Function.Surjective (intervalMove a b c e) := by
  intro y
  by_cases hl : y ≤ c
  · refine ⟨y - c + a, ?_⟩
    unfold intervalMove
    rw [ite_eq_left (by linarith)]
    ring
  by_cases hr : e ≤ y
  · refine ⟨y - e + b, ?_⟩
    unfold intervalMove
    rw [ite_eq_right (by linarith), ite_eq_left (by linarith)]
    ring
  have hs : 0 < (b - a) / (e - c) := div_pos (sub_pos.mpr hab) (sub_pos.mpr hce)
  have he : (e - c) * ((b - a) / (e - c)) = b - a := by
    field_simp [sub_ne_zero.mpr hce.ne']
  refine ⟨a + (y - c) * ((b - a) / (e - c)), ?_⟩
  unfold intervalMove
  rw [ite_eq_right (by nlinarith [mul_pos (sub_pos.mpr (lt_of_not_ge hl)) hs]),
    ite_eq_right (by nlinarith [mul_pos (sub_pos.mpr (lt_of_not_ge hr)) hs])]
  field_simp [sub_ne_zero.mpr hce.ne', sub_ne_zero.mpr hab.ne']
  ring

private def intervalMoveIso {a b c e : ℝ} (hab : a < b) (hce : c < e) : ℝ ≃o ℝ :=
  (intervalMove_strictMono hab hce).orderIsoOfSurjective _ (intervalMove_surjective hab hce)

private theorem intervalMoveIso_le {a b c e : ℝ} (hab : a < b) (hce : c < e) (x : ℝ) :
    |x - intervalMoveIso hab hce x| ≤ max |a - c| |b - e| := by
  change |x - intervalMove a b c e x| ≤ _
  unfold intervalMove
  split_ifs with h₁ h₂
  · simpa only [show x - (x - a + c) = a - c by ring] using
      le_max_left |a - c| |b - e|
  · simpa only [show x - (x - b + e) = b - e by ring] using
      le_max_right |a - c| |b - e|
  let w := (x - a) / (b - a)
  have hw : 0 ≤ w := div_nonneg (by linarith) (sub_nonneg.mpr hab.le)
  have hw' : w ≤ 1 := (div_le_one (sub_pos.mpr hab)).2 (by linarith)
  have hx : x - (c + (x - a) * ((e - c) / (b - a))) =
      (1 - w) * (a - c) + w * (b - e) := by
    dsimp [w]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  rw [hx]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hw'), abs_of_nonneg hw]
  calc
    _ ≤ (1 - w) * max |a - c| |b - e| + w * max |a - c| |b - e| :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hw'))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hw)
    _ = _ := by ring

private theorem mem_star_orderIso (u : ℝ ≃o ℝ) (v : Fin (2 * m + 1)) (x : ℝ) :
    u x ∈ star (u ∘ p) v ↔ x ∈ star p v := by
  change (∀ i : Fin m, (2 * i.val + 1 < v.val → u (p i) < u x) ∧
    (v.val < 2 * i.val + 1 → u x < u (p i))) ↔
      ∀ i : Fin m, (2 * i.val + 1 < v.val → p i < x) ∧ (v.val < 2 * i.val + 1 → x < p i)
  simp only [OrderIso.lt_iff_lt]

private abbrev orderHomeoHom (u : ℝ ≃o ℝ) : realLine ⟶ realLine :=
  (TopCat.isoOfHomeo u.toHomeomorph).hom

omit [HasDerivedCategory Sh] [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc a b)).Sheaf (ModuleCat k))] in
private def pushforwardIntervalIso (u : ℝ ≃o ℝ) (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) :
    (TopCat.Sheaf.pushforward (ModuleCat k) (orderHomeoHom u)).obj ISh[hp,J] ≅
      ISh[u.strictMono.comp hp,J] := by
  let f := orderHomeoHom u
  let F := ISh[hp,J]
  let G := (TopCat.Sheaf.pushforward (ModuleCat k) f).obj F
  let q' := u ∘ p
  let hq' := u.strictMono.comp hp
  let pre := f.frameHom
  have hm (V : TopologicalSpace.Opens realLine) (x : ℝ) : x ∈ pre V ↔ u x ∈ V := Iff.rfl
  have hb (x : ℝ) : x ∈ breakpoints p ↔ u x ∈ breakpoints q' := by
    simp only [q', mem_breakpoints, Function.comp_apply, EquivLike.apply_eq_iff_eq]
  have hbasic {V : TopologicalSpace.Opens realLine} (hV : IsBasicOpen (breakpoints q') V) :
      IsBasicOpen (breakpoints p) (pre V) := by
    obtain ⟨x, hx⟩ := hV.1
    exact ⟨⟨u.symm x, (hm _ _).2 (by simpa only [OrderIso.apply_symm_apply])⟩,
      hV.2.1.preimage_mono u.monotone,
      fun x hx y hy => u.injective (hV.2.2 ⟨(hm _ _).1 hx.1, (hb _).1 hx.2⟩
        ⟨(hm _ _).1 hy.1, (hb _).1 hy.2⟩)⟩
  have hF := (isConstructible_iff (k := k)).1 (isConstructible_extension k hp
    (M := interval (orient m) J) fun _ => inferInstance)
  have hG : IsConstructible (breakpoints q') G := by
    apply (isConstructible_iff (k := k)).2
    refine ⟨?_, fun V hV => hF.2 _ (hbasic hV)⟩
    intro U V hUV hU hV h
    exact hF.1 (OrderHomClass.mono pre hUV) (hbasic hU) (hbasic hV) (by
      ext x
      change (x ∈ pre U ∧ x ∈ breakpoints p) ↔ (x ∈ pre V ∧ x ∈ breakpoints p)
      have he := Set.ext_iff.1 h (u x)
      change (u x ∈ U ∧ u x ∈ breakpoints q') ↔ (u x ∈ V ∧ u x ∈ breakpoints q') at he
      simpa only [hm, hb] using he)
  have hstar (v : Fin (2 * m + 1)) : pre (star q' v) = star p v := by
    ext x
    change x ∈ pre (star q' v) ↔ x ∈ star p v
    exact (hm _ _).trans (mem_star_orderIso u v x)
  let secIso : (sections k q').obj G ≅ (sections k p).obj F :=
    isoMk (fun v => F.presheaf.mapIso (eqToIso (congrArg Opposite.op (hstar v))))
      (fun e => by
        rw [sections_map_gen, sections_map_gen]
        change F.presheaf.map (homOfLE (OrderHomClass.mono pre (star_le_star_of_arrow q' e))).op ≫
          F.presheaf.map _ = F.presheaf.map _ ≫
            F.presheaf.map (homOfLE (star_le_star_of_arrow p e)).op
        exact (F.presheaf.map_comp _ _).symm.trans
          ((congrArg F.presheaf.map (Subsingleton.elim _ _)).trans (F.presheaf.map_comp _ _)))
  exact (sectionsExtensionIso k hq').app ⟨G, hG⟩ ≪≫ (extension k hq').mapIso
    (secIso ≪≫ (extensionSectionsIso k hp).app _)

private theorem intervalSet_orderIso (u : ℝ ≃o ℝ) (J : FiniteInterval (2 * m + 1)) :
    intervalSet (u ∘ p) J = u '' intervalSet p J := by
  rw [u.image_eq_preimage_symm]
  ext x
  obtain ⟨y, rfl⟩ := u.surjective x
  rw [Set.mem_preimage, u.symm_apply_apply]
  constructor
  · intro hy
    obtain ⟨v, hv, hz⟩ := mem_intervalSet.mp hy
    exact mem_intervalSet.mpr ⟨v, hv, (mem_star_orderIso u v y).mp hz.1,
      fun i hi => u.injective (hz.2 i hi)⟩
  · intro hy
    obtain ⟨v, hv, hz⟩ := mem_intervalSet.mp hy
    exact mem_intervalSet.mpr ⟨v, hv, (mem_star_orderIso u v y).mpr hz.1,
      fun i hi => congrArg u (hz.2 i hi)⟩

private theorem distance_le_of_orderIso (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    (u : ℝ ≃o ℝ) {r : ℝ} (hr : 0 ≤ r) (hu : ∀ x, |x - u x| ≤ r)
    (h : u '' intervalSet p J = intervalSet q K) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) ≤
      ENNReal.ofReal r := by
  let f := orderHomeoHom u
  have : IsIso f :=
    (TopCat.isoOfHomeo (X := realLine) (Y := realLine) u.toHomeomorph).isIso_hom
  obtain ⟨i⟩ := nonempty_iso_intervalSheaf_of_intervalSet_eq k (u.strictMono.comp hp) hq
    ((intervalSet_orderIso u J).trans h)
  let ex := rightDerivedFunctorPlusSingleIso
    (TopCat.Sheaf.pushforward (ModuleCat k) (𝟙 realLine)) d ISh[hp,J]
  let ey := rightDerivedFunctorPlusSingleIso (TopCat.Sheaf.pushforward (ModuleCat k) f)
    d ISh[hp,J] ≪≫ (Single d).mapIso (pushforwardIntervalIso k u hp J ≪≫ i)
  exact ((directImageWitness k hr (𝟙 realLine) f (fun x => by
      change dist x (u x) ≤ r
      rw [Real.dist_eq]
      exact hu x) ((Single d).obj ISh[hp,J])).congr ex ey).distance_le

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

/-- A lower endpoint, allowing a set that is unbounded below. -/
private inductive LowerCut
  | closed (a : ℝ)
  | unbounded
  | open' (a : ℝ)

private def LowerCut.mem : LowerCut → ℝ → Prop
  | .closed a, x => a ≤ x
  | .unbounded, _ => True
  | .open' a, x => a < x

private theorem LowerCut.mono (L : LowerCut) {x y : ℝ} (h : x ≤ y)
    (hx : L.mem x) : L.mem y := by
  cases L <;> simp only [LowerCut.mem] at * <;> linarith

private def LowerCut.closedAt : LowerCut → ℝ → Prop
  | .closed a, x => a ≤ x
  | .unbounded, _ => True
  | .open' a, x => a ≤ x

private theorem LowerCut.isClosed (L : LowerCut) : IsClosed {x | L.closedAt x} := by
  cases L
  · exact isClosed_Ici
  · exact isClosed_univ
  · exact isClosed_Ici

private theorem LowerCut.mem_closedAt (L : LowerCut) {x : ℝ} (hx : L.mem x) :
    L.closedAt x := by
  cases L <;> simp only [LowerCut.mem, LowerCut.closedAt] at * <;> first | assumption | exact hx.le

private def LowerCut.allows : LowerCut → LowerCut → Prop
  | .closed a, .closed b => a ≤ b
  | .closed _, .unbounded | .closed _, .open' _ | .unbounded, .open' _ => False
  | .open' a, .open' b => b ≤ a
  | _, _ => True

private def IntervalEndpoints.lower : IntervalEndpoints → LowerCut
  | .icc a .. | .ico a .. | .ici a => .closed a
  | .ioc a .. | .ioo a .. | .ioi a => .open' a
  | _ => .unbounded

private def IntervalEndpoints.upper : IntervalEndpoints → LowerCut
  | .icc _ b _ | .ioc _ b _ | .iic b => .closed (-b)
  | .ico _ b _ | .ioo _ b _ | .iio b => .open' (-b)
  | _ => .unbounded

private theorem IntervalEndpoints.mem_support_iff (E : IntervalEndpoints) (x : ℝ) :
    x ∈ E.support ↔ E.lower.mem x ∧ E.upper.mem (-x) := by
  cases E <;> simp [IntervalEndpoints.support, IntervalEndpoints.lower,
    IntervalEndpoints.upper, LowerCut.mem]

omit [HasDerivedCategory Sh] [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc a b)).Sheaf (ModuleCat k))] in
/-- On a window where the source is relatively closed, a zero source stalk at a target
point or an excluded target boundary forces the morphism to vanish at a common point. -/
private theorem stalk_hom_zero_of_window (hp : StrictMono p) (hq : StrictMono q)
    {J : FiniteInterval (2 * m + 1)} {K : FiniteInterval (2 * n + 1)}
    (f : ISh[hp,J] ⟶ ISh[hq,K]) {U : TopologicalSpace.Opens realLine}
    (hU : (U : Set ℝ).OrdConnected) {x y : ℝ}
    (hx : x ∈ U) (hxJ : x ∈ intervalSet p J)
    (hJ : closure (intervalSet p J) ∩ (U : Set ℝ) ⊆ intervalSet p J) (hy : y ∈ U)
    (hyK : (y ∈ intervalSet q K ∧ y ∉ intervalSet p J) ∨
      (y ∈ closure (intervalSet q K) ∧ y ∉ intervalSet q K)) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat k) (X := realLine) x).map f.hom = 0 := by
  let F : Sh := ISh[hp,J]
  let G : Sh := ISh[hq,K]
  let st (z : ℝ) := TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) z
  have htop : f.hom.app (Opposite.op U) = 0 := by
    rcases hyK with ⟨hyK, hyJ⟩ | ⟨hyK, hnyK⟩
    · let g := G.presheaf.germ U y hy
      have : Mono g := (ModuleCat.mono_iff_injective g).2
        (injective_germ_extension_interval k hq K hU hy hyK)
      have hg : F.presheaf.germ U y hy = 0 :=
        (isZero_stalk_extension_interval k hp hyJ).eq_of_tgt _ _
      apply (cancel_mono g).mp
      rw [zero_comp, ← TopCat.Presheaf.stalkFunctor_map_germ U y hy f.hom]
      change F.presheaf.germ U y hy ≫ (st y).map f.hom = 0
      rw [hg]
      exact zero_comp
    · exact (isZero_sections_extension_interval_of_mem_closure k hq K hU hy hyK hnyK).eq_of_tgt _ _
  have := isIso_germ_extension_interval k hp J hU hJ hx hxJ
  change (st x).map f.hom = 0
  apply (cancel_epi (F.presheaf.germ U x hx)).mp
  refine (TopCat.Presheaf.stalkFunctor_map_germ U x hx f.hom).trans ?_
  rw [htop, zero_comp]
  exact (comp_zero (f := F.presheaf.germ U x hx)).symm

private theorem LowerCut.mem_of_open_limit (R : LowerCut) {x : ℝ} (h : R.closedAt (-x))
    (hr : ∀ b, R = .open' b → x < -b) : R.mem (-x) := by
  cases R with
  | closed | unbounded => exact h
  | open' b =>
    change b < -x
    linarith [hr b rfl]

private theorem LowerCut.exists_right_limit (R : LowerCut) {x : ℝ} (hx : R.mem (-x)) :
    ∃ t > x, ∀ b, R = .open' b → t ≤ -b := by
  cases R with
  | closed | unbounded => exact ⟨x + 1, by linarith, fun _ h => by cases h⟩
  | open' b =>
    change b < -x at hx
    exact ⟨-b, by linarith, fun _ h => by cases h; exact le_rfl⟩

private theorem LowerCut.exists_left_obstruction (L M : LowerCut) {x : ℝ}
    (hx : L.mem x) (hy : M.mem x) (h : ¬ L.allows M) :
    ∃ l y : ℝ, l < y ∧ y ≤ x ∧
      (∀ z, l < z → L.closedAt z → L.mem z) ∧
      ((M.mem y ∧ ¬ L.mem y) ∨ ∃ b, M = .open' b ∧ y = b ∧ y < x) := by
  cases L <;> cases M <;> simp only [LowerCut.allows, LowerCut.mem, LowerCut.closedAt] at *
  case closed.closed a b =>
    exact ⟨b - 1, b, by linarith, hy, fun _ _ hz => hz, Or.inl ⟨le_rfl, h⟩⟩
  case closed.unbounded a =>
    exact ⟨a - 2, a - 1, by linarith, by linarith, fun _ _ hz => hz,
      Or.inl ⟨trivial, by linarith⟩⟩
  case closed.open' a b =>
    exact ⟨b - 1, b, by linarith, hy.le, fun _ _ hz => hz, Or.inr ⟨b, rfl, rfl, hy⟩⟩
  case unbounded.open' b =>
    exact ⟨b - 1, b, by linarith, hy.le, fun _ _ _ => trivial, Or.inr ⟨b, rfl, rfl, hy⟩⟩
  case open'.open' a b =>
    exact ⟨a, b, lt_of_not_ge h, hy.le, fun _ hz _ => hz, Or.inr ⟨b, rfl, rfl, hy⟩⟩
  all_goals exact (h trivial).elim

omit [HasDerivedCategory Sh] [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc a b)).Sheaf (ModuleCat k))] in
private theorem hom_eq_zero_of_lowerCut (hp : StrictMono p) (hq : StrictMono q)
    {J : FiniteInterval (2 * m + 1)} {K : FiniteInterval (2 * n + 1)}
    (u : ℝ ≃ₜ ℝ) (hu : Monotone u ∨ Antitone u)
    (L R M S : LowerCut)
    (hJ : ∀ x, x ∈ intervalSet p J ↔ L.mem (u x) ∧ R.mem (-u x))
    (hK : ∀ x, x ∈ intervalSet q K ↔ M.mem (u x) ∧ S.mem (-u x))
    (h : ¬ L.allows M) (f : ISh[hp,J] ⟶ ISh[hq,K]) : f = 0 := by
  apply hom_extension_eq_zero_of_stalk k hp hq f
  intro x hxJ hxK
  obtain ⟨hxL, hxR⟩ := (hJ x).1 hxJ
  obtain ⟨hxM, hxS⟩ := (hK x).1 hxK
  obtain ⟨t, ht, htR⟩ := LowerCut.exists_right_limit R hxR
  obtain ⟨l, y, hly, hyx, hL, hy⟩ := LowerCut.exists_left_obstruction L M hxL hxM h
  let U : TopologicalSpace.Opens realLine :=
    ⟨u ⁻¹' Set.Ioo l t, isOpen_Ioo.preimage u.continuous⟩
  have hU : (U : Set ℝ).OrdConnected :=
    hu.elim (Set.ordConnected_Ioo.preimage_mono) (Set.ordConnected_Ioo.preimage_anti)
  have hyU : u.symm y ∈ U := by
    change u (u.symm y) ∈ Set.Ioo l t
    rw [u.apply_symm_apply]
    exact ⟨hly, hyx.trans_lt ht⟩
  refine stalk_hom_zero_of_window k hp hq f hU ⟨hly.trans_le hyx, ht⟩ hxJ ?_ hyU ?_
  · intro z hz
    have hl : L.closedAt (u z) :=
      closure_minimal (fun s hs => L.mem_closedAt ((hJ s).mp hs).1)
        (L.isClosed.preimage u.continuous) hz.1
    have hr : R.closedAt (-u z) :=
      closure_minimal (fun s hs => R.mem_closedAt ((hJ s).mp hs).2)
        (R.isClosed.preimage u.continuous.neg) hz.1
    exact (hJ z).2
      ⟨hL _ hz.2.1 hl, R.mem_of_open_limit hr fun b hb => hz.2.2.trans_le (htR b hb)⟩
  rcases hy with ⟨hyM, hyL⟩ | ⟨b, hb, hyb, hbx⟩
  · left
    rw [hK, hJ, u.apply_symm_apply]
    exact ⟨⟨hyM, S.mono (neg_le_neg hyx) hxS⟩, fun hz => hyL hz.1⟩
  · right
    subst y
    refine ⟨?_, fun hz => ?_⟩
    · have hs : u ⁻¹' Set.Ioo b (u x) ⊆ intervalSet q K := by
        intro z hz
        exact (hK z).2 ⟨by simpa only [hb, LowerCut.mem] using hz.1,
          S.mono (neg_le_neg hz.2.le) hxS⟩
      apply closure_mono hs
      rw [← u.preimage_closure, closure_Ioo hbx.ne]
      change u (u.symm b) ∈ Set.Icc b (u x)
      rw [u.apply_symm_apply]
      exact ⟨le_rfl, hbx.le⟩
    have hz' := ((hK _).1 hz).1
    rw [hb, u.apply_symm_apply] at hz'
    exact lt_irrefl _ hz'

omit [HasDerivedCategory Sh] [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc a b)).Sheaf (ModuleCat k))] in
private theorem hom_eq_zero_of_cut_conflict (hp : StrictMono p) (hq : StrictMono q)
    {J : FiniteInterval (2 * m + 1)} {K : FiniteInterval (2 * n + 1)} (E F : IntervalEndpoints)
    (hJ : intervalSet p J = E.support) (hK : intervalSet q K = F.support)
    (h : ¬ E.lower.allows F.lower ∨ ¬ E.upper.allows F.upper)
    (f : ISh[hp,J] ⟶ ISh[hq,K]) : f = 0 := by
  rcases h with h | h
  · exact hom_eq_zero_of_lowerCut k hp hq (Homeomorph.refl ℝ) (Or.inl monotone_id)
      E.lower E.upper F.lower F.upper
      (fun x => hJ ▸ E.mem_support_iff x) (fun x => hK ▸ F.mem_support_iff x) h f
  · let neg := (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toHomeomorph
    refine hom_eq_zero_of_lowerCut k hp hq neg (Or.inr fun _ _ h' => neg_le_neg h')
      E.upper E.lower F.upper F.lower ?_ ?_ h f
    · intro x
      rw [hJ, E.mem_support_iff]
      change _ ↔ E.upper.mem (-x) ∧ E.lower.mem (- -x)
      rw [neg_neg, and_comm]
    · intro x
      rw [hK, F.mem_support_iff]
      change _ ↔ F.upper.mem (-x) ∧ F.lower.mem (- -x)
      rw [neg_neg, and_comm]

private theorem distance_le_sup_deletions {X Y : D⁺} :
    distance X Y ≤ distance X 0 ⊔ distance Y 0 := by
  apply ENNReal.le_of_forall_pos_le_add
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

private def IntervalEndpoints.convolved (E : IntervalEndpoints) (r : ℝ) (hr : 0 ≤ r) :
    IntervalEndpoints :=
  match E with
  | .icc a b h => .icc (a - r) (b + r) (by linarith)
  | .ico a b h => .ico (a - r) (b - r) (by linarith)
  | .ioc a b h => .ioc (a + r) (b + r) (by linarith)
  | .ioo a b h => .ioo a b h
  | .ici a => .ici (a - r)
  | .iic b => .iic (b + r)
  | .ioi a => .ioi (a + r)
  | .iio b => .iio (b - r)
  | .univ => .univ

private theorem IntervalEndpoints.outSet0_eq_convolved (E : IntervalEndpoints) {r : ℝ}
    (hr : 0 ≤ r) (h : E.hasDegreeOneOutput = false) :
    outSet0 r E.support = (E.convolved r hr).support := by
  cases E with
  | icc a b hab => exact outSet0_Icc hr hab
  | ico a b hab => exact outSet0_Ico hr hab
  | ioc a b hab => exact outSet0_Ioc hr hab
  | ioo => cases h
  | ici a => exact outSet0_Ici hr a
  | iic b => exact outSet0_Iic hr b
  | ioi a => exact outSet0_Ioi hr a
  | iio b => exact outSet0_Iio hr b
  | univ => exact outSet0_univ hr

private theorem IntervalEndpoints.support_nonempty (E : IntervalEndpoints) :
    E.support.Nonempty := by
  cases E <;> first
    | exact Set.nonempty_Icc.mpr ‹_›
    | exact Set.nonempty_Ico.mpr ‹_›
    | exact Set.nonempty_Ioc.mpr ‹_›
    | exact Set.nonempty_Ioo.mpr ‹_›
    | exact Set.nonempty_Ici
    | exact Set.nonempty_Iic
    | exact Set.nonempty_Ioi
    | exact Set.nonempty_Iio
    | exact Set.univ_nonempty

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))] in
private theorem exists_iso_convolved_endpoints (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) (d : ℤ) {r : ℝ} (hr : 0 ≤ r) (E : IntervalEndpoints)
    (hE : E.hasDegreeOneOutput = false) (hJ : intervalSet p J = E.support) :
    ∃ L : FiniteInterval (2 * (bandBreakpoints p r).card + 1),
      intervalSet (sortedBreakpoints (bandBreakpoints p r)) L = (E.convolved r hr).support ∧
      Nonempty ((T k r).obj ((GradedInterval.mk J d).obj k hp) ≅
        (GradedInterval.mk L d).obj k (strictMono_sortedBreakpoints (bandBreakpoints p r))) := by
  have hout : outSet0 r (intervalSet p J) = (E.convolved r hr).support :=
    hJ ▸ E.outSet0_eq_convolved hr hE
  obtain ⟨L, hL⟩ := exists_intervalSet_outSet0 hp J hr
    (hout.symm ▸ (E.convolved r hr).support_nonempty)
  obtain ⟨i⟩ := nonempty_iso_T_interval_zero (k := k) hp J hr
    (strictMono_sortedBreakpoints (bandBreakpoints p r)) L hL
  let hl := strictMono_sortedBreakpoints (bandBreakpoints p r)
  refine ⟨L, hL.trans hout, ⟨?_⟩⟩
  change _ ≅ (Single d).obj ISh[hl,L]
  simpa only [zero_add] using convGradedIso k hp ⟨J, d⟩ i

private theorem Witness.sup_deletions_le_of_hom_zero {X Y : D⁺} {r : ℝ≥0}
    (w : Witness k r.coe_nonneg X Y) (h : w.hom = 0) :
    distance X 0 ⊔ distance Y 0 ≤ (r : ℝ≥0∞) := by
  obtain ⟨u⟩ := (nonempty_witness_zero_iff (hε := r.coe_nonneg)).mpr
    (w.aug_eq_zero_of_hom_eq_zero k h)
  obtain ⟨v⟩ := (nonempty_witness_zero_iff (hε := r.coe_nonneg)).mpr
    (w.aug_target_eq_zero_of_hom_eq_zero k h)
  exact sup_le (by simpa only [ENNReal.ofReal_coe_nnreal] using u.distance_le)
    (by simpa only [ENNReal.ofReal_coe_nnreal] using v.distance_le)

private theorem witness_cut_allows (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ) (r : ℝ≥0)
    (E F : IntervalEndpoints) (hE : E.hasDegreeOneOutput = false)
    (hJ : intervalSet p J = E.support) (hK : intervalSet q K = F.support)
    (w : Witness k r.coe_nonneg ((GradedInterval.mk J d).obj k hp)
      ((GradedInterval.mk K d).obj k hq)) (hw : w.hom ≠ 0) :
    (E.convolved r r.coe_nonneg).lower.allows F.lower ∧
      (E.convolved r r.coe_nonneg).upper.allows F.upper := by
  obtain ⟨L, hL, ⟨i⟩⟩ := exists_iso_convolved_endpoints k hp J d r.coe_nonneg E hE hJ
  constructor <;> by_contra h <;>
    exact hw (hom_eq_zero_of_interval_hom_eq_zero k _ hq i (Iso.refl _)
      (hom_eq_zero_of_cut_conflict k _ hq _ F hL hK (by first | exact Or.inl h | exact Or.inr h))
      w.hom)

private theorem distance_eq_inf_deletions {X Y : D⁺} {c : ℝ≥0∞}
    (hdirect : distance X Y ≤ c)
    (hlower : ∀ (r : ℝ≥0), Nonempty (Witness k r.coe_nonneg X Y) →
      (r : ℝ≥0∞) < distance X 0 ⊔ distance Y 0 → c ≤ r) :
    distance X Y = c ⊓ (distance X 0 ⊔ distance Y 0) := by
  refine le_antisymm (le_inf hdirect (distance_le_sup_deletions k)) ?_
  apply le_distance_iff.mpr
  intro r hw
  rcases lt_or_ge (r : ℝ≥0∞) (distance X 0 ⊔ distance Y 0) with h | h
  · exact inf_le_left.trans (hlower r hw h)
  · exact inf_le_right.trans h

private theorem distance_convolved_le {X Y X' Y' : D⁺} {s : ℝ} (hs : 0 ≤ s)
    (ex : (T k s).obj X ≅ X') (ey : (T k s).obj Y ≅ Y') :
    distance X' Y' ≤ distance X Y := by
  apply le_distance_iff.mpr
  rintro r ⟨w⟩
  simpa only [ENNReal.ofReal_coe_nnreal] using ((w.convolve hs).congr ex ey).distance_le

private theorem distance_eq_sup_deletions_of_hom_eq_zero {X Y : D⁺}
    (h : ∀ r : ℝ≥0, ∀ f : (T k r).obj X ⟶ Y, f = 0) :
    distance X Y = distance X 0 ⊔ distance Y 0 := by
  refine le_antisymm (distance_le_sup_deletions k) (le_distance_iff.mpr ?_)
  rintro r ⟨w⟩
  exact w.sup_deletions_le_of_hom_zero k (h r w.hom)

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

private theorem intervalMoveIso_left {a b c e : ℝ} (hab : a < b) (hce : c < e) :
    intervalMoveIso hab hce a = c := by
  change intervalMove a b c e a = c
  simp [intervalMove]

private theorem intervalMoveIso_right {a b c e : ℝ} (hab : a < b) (hce : c < e) :
    intervalMoveIso hab hce b = e := by
  change intervalMove a b c e b = e
  simp [intervalMove, hab.not_ge]

private theorem witness_both_cut_allows (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ) (r : ℝ≥0)
    (E F : IntervalEndpoints)
    (hE : E.hasDegreeOneOutput = false) (hF : F.hasDegreeOneOutput = false)
    (hJ : intervalSet p J = E.support) (hK : intervalSet q K = F.support)
    (w : Witness k r.coe_nonneg ((GradedInterval.mk J d).obj k hp)
      ((GradedInterval.mk K d).obj k hq))
    (hr : (r : ℝ≥0∞) < distance ((GradedInterval.mk J d).obj k hp) 0 ⊔
      distance ((GradedInterval.mk K d).obj k hq) 0) :
    ((E.convolved r r.coe_nonneg).lower.allows F.lower ∧
      (E.convolved r r.coe_nonneg).upper.allows F.upper) ∧
    ((F.convolved r r.coe_nonneg).lower.allows E.lower ∧
      (F.convolved r r.coe_nonneg).upper.allows E.upper) := by
  constructor
  · exact witness_cut_allows k hp hq J K d r E F hE hJ hK w
      (fun hz => hr.not_ge (w.sup_deletions_le_of_hom_zero k hz))
  · exact witness_cut_allows k hq hp K J d r F E hF hK hJ w.symm
      (fun hz => hr.not_ge (by simpa only [sup_comm] using
        w.symm.sup_deletions_le_of_hom_zero k hz))


/-- Two bounded intervals closed on the left have the smaller of the endpoint
and joint deletion costs in a common degree. -/
theorem distance_interval_Ico_Ico (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hJ : intervalSet p J = Set.Ico a b) (hK : intervalSet q K = Set.Ico c e) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      ENNReal.ofReal (max |a - c| |b - e|) ⊓
        ENNReal.ofReal (max ((b - a) / 2) ((e - c) / 2)) := by
  have hupper := distance_le_of_orderIso k hp hq J K d (intervalMoveIso hab hce)
    ((abs_nonneg (a - c)).trans (le_max_left _ _)) (intervalMoveIso_le hab hce)
    (by rw [hJ, hK, OrderIso.image_Ico, intervalMoveIso_left, intervalMoveIso_right])
  rw [ENNReal.ofReal_max ((b - a) / 2) ((e - c) / 2),
    ← distance_interval_Ico_zero k hp ⟨J, d⟩ hab hJ,
    ← distance_interval_Ico_zero k hq ⟨K, d⟩ hce hK]
  apply distance_eq_inf_deletions k hupper
  rintro r ⟨w⟩ hr
  obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ :=
    witness_both_cut_allows k hp hq J K d r (.ico a b hab) (.ico c e hce) rfl rfl hJ hK w hr
  simp only [IntervalEndpoints.convolved, IntervalEndpoints.lower, IntervalEndpoints.upper,
    LowerCut.allows] at h₁ h₂ h₃ h₄
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩))


/-- Two bounded intervals closed on the right have the smaller of the endpoint
and joint deletion costs in a common degree. -/
theorem distance_interval_Ioc_Ioc (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hJ : intervalSet p J = Set.Ioc a b) (hK : intervalSet q K = Set.Ioc c e) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      ENNReal.ofReal (max |a - c| |b - e|) ⊓
        ENNReal.ofReal (max ((b - a) / 2) ((e - c) / 2)) := by
  have hupper := distance_le_of_orderIso k hp hq J K d (intervalMoveIso hab hce)
    ((abs_nonneg (a - c)).trans (le_max_left _ _)) (intervalMoveIso_le hab hce)
    (by rw [hJ, hK, OrderIso.image_Ioc, intervalMoveIso_left, intervalMoveIso_right])
  rw [ENNReal.ofReal_max ((b - a) / 2) ((e - c) / 2),
    ← distance_interval_Ioc_zero k hp ⟨J, d⟩ hab hJ,
    ← distance_interval_Ioc_zero k hq ⟨K, d⟩ hce hK]
  apply distance_eq_inf_deletions k hupper
  rintro r ⟨w⟩ hr
  obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ :=
    witness_both_cut_allows k hp hq J K d r (.ioc a b hab) (.ioc c e hce) rfl rfl hJ hK w hr
  simp only [IntervalEndpoints.convolved, IntervalEndpoints.lower, IntervalEndpoints.upper,
    LowerCut.allows] at h₁ h₂ h₃ h₄
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩))


/-- Two bounded open intervals in a common degree have cost equal to the larger
of the absolute endpoint differences. -/
theorem distance_interval_Ioo_Ioo (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hJ : intervalSet p J = Set.Ioo a b) (hK : intervalSet q K = Set.Ioo c e) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      ENNReal.ofReal (max |a - c| |b - e|) := by
  have hupper := distance_le_of_orderIso k hp hq J K d (intervalMoveIso hab hce)
    ((abs_nonneg (a - c)).trans (le_max_left _ _)) (intervalMoveIso_le hab hce)
    (by rw [hJ, hK, OrderIso.image_Ioo, intervalMoveIso_left, intervalMoveIso_right])
  let s := max (b - a) (e - c)
  have hs : 0 ≤ s := (sub_nonneg.mpr hab.le).trans (le_max_left _ _)
  have hsJ : b - a < 2 * s := by linarith [le_max_left (b - a) (e - c)]
  have hsK : e - c < 2 * s := by linarith [le_max_right (b - a) (e - c)]
  obtain ⟨L, hL, ⟨i⟩⟩ := exists_intervalSheaf_T_Ioo_above (k := k) hp J hs hab hsJ hJ
  obtain ⟨M, hM, ⟨j⟩⟩ := exists_intervalSheaf_T_Ioo_above (k := k) hq K hs hce hsK hK
  let hl := strictMono_sortedBreakpoints (bandBreakpoints p s)
  let hm := strictMono_sortedBreakpoints (bandBreakpoints q s)
  have hdist := distance_convolved_le k hs
    (convGradedIso k hp ⟨J, d⟩ i) (convGradedIso k hq ⟨K, d⟩ j)
  have hcost := distance_interval_Icc_Icc k hl hm L M (1 + d)
    (by linarith) (by linarith) hL hM
  change distance ((GradedInterval.mk L (1 + d)).obj k hl)
    ((GradedInterval.mk M (1 + d)).obj k hm) ≤ _ at hdist
  rw [hcost, show b - s - (e - s) = b - e by ring,
    show a + s - (c + s) = a - c by ring, max_comm] at hdist
  exact le_antisymm hupper hdist

/-- Two closed right rays in a common degree cost the absolute endpoint difference. -/
theorem distance_interval_Ici_Ici (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b : ℝ} (hJ : intervalSet p J = Set.Ici a) (hK : intervalSet q K = Set.Ici b) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      ENNReal.ofReal |a - b| := by
  refine le_antisymm ?_ (le_distance_iff.mpr ?_)
  · refine distance_le_of_orderIso k hp hq J K d (OrderIso.addRight (b - a))
      (abs_nonneg _) (fun x => ?_) ?_
    · change |x - (x + (b - a))| ≤ _
      rw [show x - (x + (b - a)) = a - b by ring]
    · rw [hJ, hK, OrderIso.image_Ici]
      exact congrArg Set.Ici (show a + (b - a) = b by ring)
  rintro r ⟨w⟩
  have hr : (r : ℝ≥0∞) < distance ((GradedInterval.mk J d).obj k hp) 0 ⊔
      distance ((GradedInterval.mk K d).obj k hq) 0 := by
    rw [distance_interval_Ici_zero k hp ⟨J, d⟩ hJ, top_sup_eq]
    exact ENNReal.coe_lt_top
  obtain ⟨h₁, h₂⟩ :=
    witness_both_cut_allows k hp hq J K d r (.ici a) (.ici b) rfl rfl hJ hK w hr
  simp only [IntervalEndpoints.convolved, IntervalEndpoints.lower, IntervalEndpoints.upper,
    LowerCut.allows, and_true] at h₁ h₂
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Two closed left rays in a common degree cost the absolute endpoint difference. -/
theorem distance_interval_Iic_Iic (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b : ℝ} (hJ : intervalSet p J = Set.Iic a) (hK : intervalSet q K = Set.Iic b) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      ENNReal.ofReal |a - b| := by
  refine le_antisymm ?_ (le_distance_iff.mpr ?_)
  · refine distance_le_of_orderIso k hp hq J K d (OrderIso.addRight (b - a))
      (abs_nonneg _) (fun x => ?_) ?_
    · change |x - (x + (b - a))| ≤ _
      rw [show x - (x + (b - a)) = a - b by ring]
    · rw [hJ, hK, OrderIso.image_Iic]
      exact congrArg Set.Iic (show a + (b - a) = b by ring)
  rintro r ⟨w⟩
  have hr : (r : ℝ≥0∞) < distance ((GradedInterval.mk J d).obj k hp) 0 ⊔
      distance ((GradedInterval.mk K d).obj k hq) 0 := by
    rw [distance_interval_Iic_zero k hp ⟨J, d⟩ hJ, top_sup_eq]
    exact ENNReal.coe_lt_top
  obtain ⟨h₁, h₂⟩ :=
    witness_both_cut_allows k hp hq J K d r (.iic a) (.iic b) rfl rfl hJ hK w hr
  simp only [IntervalEndpoints.convolved, IntervalEndpoints.lower, IntervalEndpoints.upper,
    LowerCut.allows, true_and] at h₁ h₂
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Two open right rays in a common degree cost the absolute endpoint difference. -/
theorem distance_interval_Ioi_Ioi (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b : ℝ} (hJ : intervalSet p J = Set.Ioi a) (hK : intervalSet q K = Set.Ioi b) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      ENNReal.ofReal |a - b| := by
  refine le_antisymm ?_ (le_distance_iff.mpr ?_)
  · refine distance_le_of_orderIso k hp hq J K d (OrderIso.addRight (b - a))
      (abs_nonneg _) (fun x => ?_) ?_
    · change |x - (x + (b - a))| ≤ _
      rw [show x - (x + (b - a)) = a - b by ring]
    · rw [hJ, hK, OrderIso.image_Ioi]
      exact congrArg Set.Ioi (show a + (b - a) = b by ring)
  rintro r ⟨w⟩
  have hr : (r : ℝ≥0∞) < distance ((GradedInterval.mk J d).obj k hp) 0 ⊔
      distance ((GradedInterval.mk K d).obj k hq) 0 := by
    rw [distance_interval_Ioi_zero k hp ⟨J, d⟩ hJ, top_sup_eq]
    exact ENNReal.coe_lt_top
  obtain ⟨h₁, h₂⟩ :=
    witness_both_cut_allows k hp hq J K d r (.ioi a) (.ioi b) rfl rfl hJ hK w hr
  simp only [IntervalEndpoints.convolved, IntervalEndpoints.lower, IntervalEndpoints.upper,
    LowerCut.allows, and_true] at h₁ h₂
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Two open left rays in a common degree cost the absolute endpoint difference. -/
theorem distance_interval_Iio_Iio (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b : ℝ} (hJ : intervalSet p J = Set.Iio a) (hK : intervalSet q K = Set.Iio b) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      ENNReal.ofReal |a - b| := by
  refine le_antisymm ?_ (le_distance_iff.mpr ?_)
  · refine distance_le_of_orderIso k hp hq J K d (OrderIso.addRight (b - a))
      (abs_nonneg _) (fun x => ?_) ?_
    · change |x - (x + (b - a))| ≤ _
      rw [show x - (x + (b - a)) = a - b by ring]
    · rw [hJ, hK, OrderIso.image_Iio]
      exact congrArg Set.Iio (show a + (b - a) = b by ring)
  rintro r ⟨w⟩
  have hr : (r : ℝ≥0∞) < distance ((GradedInterval.mk J d).obj k hp) 0 ⊔
      distance ((GradedInterval.mk K d).obj k hq) 0 := by
    rw [distance_interval_Iio_zero k hp ⟨J, d⟩ hJ, top_sup_eq]
    exact ENNReal.coe_lt_top
  obtain ⟨h₁, h₂⟩ :=
    witness_both_cut_allows k hp hq J K d r (.iio a) (.iio b) rfl rfl hJ hK w hr
  simp only [IntervalEndpoints.convolved, IntervalEndpoints.lower, IntervalEndpoints.upper,
    LowerCut.allows, true_and] at h₁ h₂
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Two whole-line interval sheaves in a common degree have distance zero. -/
theorem distance_interval_univ_univ (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    (hJ : intervalSet p J = Set.univ) (hK : intervalSet q K = Set.univ) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) = 0 := by
  obtain ⟨i⟩ := nonempty_iso_intervalSheaf_of_intervalSet_eq k hp hq (hJ.trans hK.symm)
  exact (distance_congr (Iso.refl _) ((Single d).mapIso i).symm).trans (distance_self _)

private def LowerCut.sameType : LowerCut → LowerCut → Bool
  | .closed _, .closed _ | .unbounded, .unbounded | .open' _, .open' _ => true
  | _, _ => false

private theorem LowerCut.sameType_of_allows (L L' M M' : LowerCut)
    (hL : L.sameType L' = true) (hM : M.sameType M' = true)
    (h : L'.allows M) (h' : M'.allows L) : L.sameType M = true := by
  cases L <;> cases L' <;> cases M <;> cases M' <;>
    simp_all only [LowerCut.sameType, LowerCut.allows, Bool.false_eq_true]

/-- Whether both intervals have the same open, closed or unbounded status at each endpoint. -/
def IntervalEndpoints.sameType (E F : IntervalEndpoints) : Bool :=
  E.lower.sameType F.lower && E.upper.sameType F.upper

private theorem distance_interval_Ioo_nonopen (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    {a b : ℝ} (hab : a < b) (hJ : intervalSet p J = Set.Ioo a b)
    (F : IntervalEndpoints) (hF : F.hasDegreeOneOutput = false)
    (hK : intervalSet q K = F.support) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) = ⊤ := by
  let s := b - a
  have hs : 0 ≤ s := sub_nonneg.mpr hab.le
  obtain ⟨L, hL, ⟨i⟩⟩ := exists_intervalSheaf_T_Ioo_above (k := k) hp J hs hab
    (by dsimp [s]; linarith) hJ
  obtain ⟨M, hM, ⟨j⟩⟩ := exists_iso_convolved_endpoints k hq K d hs F hF hK
  let hl := strictMono_sortedBreakpoints (bandBreakpoints p s)
  let hm := strictMono_sortedBreakpoints (bandBreakpoints q s)
  have hdist := distance_convolved_le k hs (convGradedIso k hp ⟨J, d⟩ i) j
  change distance ((GradedInterval.mk L (1 + d)).obj k hl)
    ((GradedInterval.mk M d).obj k hm) ≤ _ at hdist
  have hFo : (F.convolved s hs).hasDegreeOneOutput = false := by cases F <;> exact hF
  have hcost := distance_interval_of_degree_lt k hm hl ⟨M, d⟩ ⟨L, 1 + d⟩
    (F.convolved s hs) (.icc (b - s) (a + s) (by dsimp [s]; linarith)) hM hL
    (by dsimp; omega) (Or.inr hFo)
  rw [distance_comm, hcost] at hdist
  exact top_le_iff.mp (by simpa [IntervalEndpoints.deletionCost] using hdist)

/-- In a common degree, intervals of different endpoint types cost the larger deletion cost. -/
theorem distance_interval_of_different_endpoint_types (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (d : ℤ)
    (E F : IntervalEndpoints) (hJ : intervalSet p J = E.support)
    (hK : intervalSet q K = F.support) (hEF : E.sameType F = false) :
    distance ((GradedInterval.mk J d).obj k hp) ((GradedInterval.mk K d).obj k hq) =
      E.deletionCost ⊔ F.deletionCost := by
  by_cases hE : E.hasDegreeOneOutput = false
  · by_cases hF : F.hasDegreeOneOutput = false
    · rw [← E.distance_zero_eq k hp ⟨J, d⟩ hJ, ← F.distance_zero_eq k hq ⟨K, d⟩ hK]
      refine le_antisymm (distance_le_sup_deletions k) (le_distance_iff.mpr ?_)
      rintro r ⟨w⟩
      by_contra! hr
      obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ :=
        witness_both_cut_allows k hp hq J K d r E F hE hF hJ hK w hr
      have hl (G : IntervalEndpoints) :
          G.lower.sameType (G.convolved r r.coe_nonneg).lower = true := by cases G <;> rfl
      have hu (G : IntervalEndpoints) :
          G.upper.sameType (G.convolved r r.coe_nonneg).upper = true := by cases G <;> rfl
      simp only [IntervalEndpoints.sameType,
        LowerCut.sameType_of_allows _ _ _ _ (hl E) (hl F) h₁ h₃,
        LowerCut.sameType_of_allows _ _ _ _ (hu E) (hu F) h₂ h₄] at hEF
      cases hEF
    · cases F <;> try exact (hF rfl).elim
      rw [distance_comm, distance_interval_Ioo_nonopen k hq hp K J d (by assumption) hK E hE hJ]
      exact (sup_top_eq _).symm
  · cases E <;> try exact (hE rfl).elim
    have hF : F.hasDegreeOneOutput = false := by
      cases F <;> first | rfl | contradiction
    rw [distance_interval_Ioo_nonopen k hp hq J K d (by assumption) hJ F hF hK]
    exact (top_sup_eq _).symm

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

private def pairCostOfEq (E F : IntervalEndpoints) : ℝ≥0∞ :=
  match E, F with
  | .icc a b _, .icc c e _ | .ioo a b _, .ioo c e _ => ENNReal.ofReal (max |a - c| |b - e|)
  | .ico a b _, .ico c e _ | .ioc a b _, .ioc c e _ =>
    ENNReal.ofReal (max |a - c| |b - e|) ⊓ ENNReal.ofReal (max ((b - a) / 2) ((e - c) / 2))
  | .ici a, .ici b | .iic a, .iic b | .ioi a, .ioi b | .iio a, .iio b => ENNReal.ofReal |a - b|
  | .univ, .univ => 0
  | _, _ => E.deletionCost ⊔ F.deletionCost

private theorem distance_eq_pairCostOfEq (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1)) (i : ℤ)
    (E F : IntervalEndpoints) (hJ : intervalSet p J = E.support)
    (hK : intervalSet q K = F.support) :
    distance ((GradedInterval.mk J i).obj k hp) ((GradedInterval.mk K i).obj k hq) =
      E.pairCostOfEq F := by
  by_cases ht : E.sameType F = false
  · have hcost : E.pairCostOfEq F = E.deletionCost ⊔ F.deletionCost := by
      cases E <;> cases F <;> first | rfl | contradiction
    rw [hcost]
    exact distance_interval_of_different_endpoint_types k hp hq J K i E F hJ hK ht
  · have ht := Bool.eq_true_of_not_eq_false ht
    cases E <;> cases F <;>
      simp only [IntervalEndpoints.sameType, IntervalEndpoints.lower, IntervalEndpoints.upper,
        LowerCut.sameType, Bool.false_and, Bool.and_false, Bool.true_and,
        Bool.false_eq_true] at ht <;> first
      | exact distance_interval_Icc_Icc k hp hq J K i (by assumption) (by assumption) hJ hK
      | exact distance_interval_Ico_Ico k hp hq J K i (by assumption) (by assumption) hJ hK
      | exact distance_interval_Ioc_Ioc k hp hq J K i (by assumption) (by assumption) hJ hK
      | exact distance_interval_Ioo_Ioo k hp hq J K i (by assumption) (by assumption) hJ hK
      | exact distance_interval_Ici_Ici k hp hq J K i hJ hK
      | exact distance_interval_Iic_Iic k hp hq J K i hJ hK
      | exact distance_interval_Ioi_Ioi k hp hq J K i hJ hK
      | exact distance_interval_Iio_Iio k hp hq J K i hJ hK
      | exact distance_interval_univ_univ k hp hq J K i hJ hK

private theorem exists_support_eq (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) :
    ∃ E : IntervalEndpoints, intervalSet p J = E.support := by
  have hbd := J.birth_lt_death
  have hdmax := J.death_le_size
  have hl : J.birth = 0 ∨ (∃ i : Fin m, J.birth = 2 * i.val + 1) ∨
      (∃ i : Fin m, J.birth = 2 * i.val + 2) := by
    rcases Nat.even_or_odd' J.birth with ⟨i, hi | hi⟩
    · by_cases h : i = 0
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr ⟨⟨i - 1, by omega⟩, by simp; omega⟩)
    · exact Or.inr (Or.inl ⟨⟨i, by omega⟩, hi⟩)
  have hr : J.death = 2 * m + 1 ∨ (∃ j : Fin m, J.death = 2 * j.val + 1) ∨
      (∃ j : Fin m, J.death = 2 * j.val + 2) := by
    rcases Nat.even_or_odd' J.death with ⟨j, hj | hj⟩
    · exact Or.inr (Or.inr ⟨⟨j - 1, by omega⟩, by simp; omega⟩)
    · by_cases h : j = m
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl ⟨⟨j, by omega⟩, hj⟩)
  rcases hl with hb | ⟨i, hb⟩ | ⟨i, hb⟩ <;> rcases hr with hd | ⟨j, hd⟩ | ⟨j, hd⟩
  · exact ⟨.univ, intervalSet_eq_univ hp hb hd⟩
  · exact ⟨.iio (p j), intervalSet_eq_Iio hp hb hd⟩
  · exact ⟨.iic (p j), intervalSet_eq_Iic hp hb hd⟩
  · exact ⟨.ici (p i), intervalSet_eq_Ici hp hb hd⟩
  · exact ⟨.ico (p i) (p j) (hp (Fin.lt_def.mpr (by omega))), intervalSet_eq_Ico hp hb hd⟩
  · exact ⟨.icc (p i) (p j) (hp.monotone (Fin.le_def.mpr (by omega))),
      intervalSet_eq_Icc hp hb hd⟩
  · exact ⟨.ioi (p i), intervalSet_eq_Ioi hp hb hd⟩
  · exact ⟨.ioo (p i) (p j) (hp (Fin.lt_def.mpr (by omega))), intervalSet_eq_Ioo hp hb hd⟩
  · exact ⟨.ioc (p i) (p j) (hp (Fin.lt_def.mpr (by omega))), intervalSet_eq_Ioc hp hb hd⟩

/-- Endpoint data for the interval set of a finite strata interval. -/
def ofInterval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) : IntervalEndpoints :=
  (exists_support_eq hp J).choose

/-- The endpoint data of a strata interval describe its real support. -/
theorem support_ofInterval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) :
    intervalSet p J = (ofInterval hp J).support :=
  (exists_support_eq hp J).choose_spec

/-- The band cost of two endpoint data in the specified cohomological degrees. -/
def totalPairCost (E F : IntervalEndpoints) (i j : ℤ) : ℝ≥0∞ :=
  if i < j then E.pairCostOfLt F i j
  else if j < i then F.pairCostOfLt E j i
  else E.pairCostOfEq F

/-- The numeric band cost in option form. -/
def pairCost (E F : IntervalEndpoints) (i j : ℤ) : Option ℝ≥0∞ :=
  some (E.totalPairCost F i j)

/-- The total numeric pair cost computes the distance of the graded interval sheaves. -/
theorem distance_eq_totalPairCost (hp : StrictMono p) (hq : StrictMono q)
    (J : GradedInterval m) (K : GradedInterval n) (E F : IntervalEndpoints)
    (hJ : intervalSet p J.interval = E.support) (hK : intervalSet q K.interval = F.support) :
    distance (J.obj k hp) (K.obj k hq) = E.totalPairCost F J.degree K.degree := by
  unfold totalPairCost
  split
  · exact distance_eq_pairCostOfLt k hp hq J K E F hJ hK ‹_›
  split
  · rw [distance_comm]
    exact distance_eq_pairCostOfLt k hq hp K J F E hK hJ ‹_›
  · have hdeg : J.degree = K.degree := le_antisymm (le_of_not_gt ‹_›) (le_of_not_gt ‹_›)
    rcases J with ⟨J, i⟩
    rcases K with ⟨K, j⟩
    dsimp only at hdeg
    subst j
    exact distance_eq_pairCostOfEq k hp hq J K i E F hJ hK

/-- Every returned pair entry is the band distance used by graded matchings. -/
theorem distance_eq_of_pairCost (hp : StrictMono p) (hq : StrictMono q)
    (J : GradedInterval m) (K : GradedInterval n) (E F : IntervalEndpoints)
    (hJ : intervalSet p J.interval = E.support) (hK : intervalSet q K.interval = F.support)
    {c : ℝ≥0∞} (hc : E.pairCost F J.degree K.degree = some c) :
    distance (J.obj k hp) (K.obj k hq) = c :=
  (E.distance_eq_totalPairCost k hp hq J K F hJ hK).trans (Option.some.inj hc)

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
