import TDA.Persistence.IndexDiagram
import TDA.Persistence.GradeHomologyBarcode
import TDA.Persistence.RankBarcodeIso

set_option autoImplicit false

universe u w
namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration CategoryTheory

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TDA.Simplicial.TotalFace K)]

/-- The value-labelled rank diagram of homology at the attained critical grades. -/
noncomputable def dgm
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ) :
    Diagram α :=
  ofIndexBars f.criticalValue f.criticalValue.strictMono
    (gradeHomologyBarcode k f n)

/-- Every point of the sublevel diagram has birth strictly before death. -/
theorem dgm_isPositive
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ) :
    (dgm k f n).IsPositive :=
  ofIndexBars_isPositive _ _ _

private instance sublevelFiniteDimensional
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ) (r : α) :
    FiniteDimensional k (simplicialHomology (f.sublevel r) k n) := by
  letI : Finite (Face K n) := faceFiniteOfTotalFinite K n
  letI : Finite (Face (f.sublevel r) n) :=
    Finite.of_injective (faceIncl (f.sublevel_le r) n) (by
      intro a b hab
      exact Subtype.ext (congrArg (fun t : Face K n => t.1) hab))
  infer_instance

private theorem bottomHomology_subsingleton (n : ℕ) :
    Subsingleton (simplicialHomology (⊥ : PreAbstractSimplicialComplex V) k n) := by
  letI : Subsingleton (Chain (⊥ : PreAbstractSimplicialComplex V) k n) :=
    ⟨fun a b => (emptyChain_eq_zero k n a).trans (emptyChain_eq_zero k n b).symm⟩
  letI : Subsingleton (simplicialCycles (⊥ : PreAbstractSimplicialComplex V) k n) :=
    inferInstance
  letI : HasQuotient (simplicialCycles (⊥ : PreAbstractSimplicialComplex V) k n)
      (Submodule k (simplicialCycles (⊥ : PreAbstractSimplicialComplex V) k n)) :=
    Submodule.hasQuotient (R := k)
      (M := simplicialCycles (⊥ : PreAbstractSimplicialComplex V) k n)
  letI : Subsingleton (simplicialCycles (⊥ : PreAbstractSimplicialComplex V) k n ⧸
      simplicialBoundaries (⊥ : PreAbstractSimplicialComplex V) k n) := inferInstance
  letI : Subsingleton
      (↑(ModuleCat.of k (LinearMap.ker
        ((simplicialChainComplex (⊥ : PreAbstractSimplicialComplex V) k).sc n).g.hom ⧸
        LinearMap.range ((simplicialChainComplex
          (⊥ : PreAbstractSimplicialComplex V) k).sc n).moduleCatToCycles))) := by
    change Subsingleton (simplicialCycles (⊥ : PreAbstractSimplicialComplex V) k n ⧸
      simplicialBoundaries (⊥ : PreAbstractSimplicialComplex V) k n)
    infer_instance
  let e := (homologyKernelQuotient.{u,u,u} k
    (simplicialChainComplex (⊥ : PreAbstractSimplicialComplex V) k) n).toLinearEquiv
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

private theorem bottomMapRank_zero (n : ℕ) {L : PreAbstractSimplicialComplex V}
    (h : (⊥ : PreAbstractSimplicialComplex V) ≤ L) :
    Module.finrank k (LinearMap.range (simplicialHomologyIncl k h n).hom) = 0 := by
  letI := bottomHomology_subsingleton k (V := V) n
  have hz : (simplicialHomologyIncl k h n).hom = 0 := by
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  rw [hz, LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton (R := k)

private theorem cut_of_grade (f : TDA.Filtration.FilterFunction K α)
    (r : α) (i : Fin f.criticalValues.card)
    (hr : f.sublevel r = f.gradeFiltration i) (j : Fin f.criticalValues.card) :
    f.criticalValue j ≤ r ↔ j ≤ i := by
  constructor
  · intro hj
    obtain ⟨σ, hσ⟩ := (f.mem_criticalValues _).1 (f.criticalValue_mem j)
    have hmem : σ.val ∈ f.gradeFiltration i := by
      rw [← hr]
      exact (f.mem_sublevel_iff_of_mem r σ).2 (hσ ▸ hj)
    have hle : f.criticalValue j ≤ f.criticalValue i := by
      rw [f.gradeFiltration_apply] at hmem
      exact hσ ▸ (f.mem_sublevel_iff_of_mem _ σ).1 hmem
    exact f.criticalValue.le_iff_le.mp hle
  · intro hji
    have hi : f.criticalValue i ≤ r := by
      obtain ⟨σ, hσ⟩ := (f.mem_criticalValues _).1 (f.criticalValue_mem i)
      have hm : σ.val ∈ f.gradeFiltration i := by
        rw [f.gradeFiltration_apply]
        exact (f.mem_sublevel_iff_of_mem _ σ).2 (le_of_eq hσ)
      rw [← hr] at hm
      exact hσ ▸ (f.mem_sublevel_iff_of_mem _ σ).1 hm
    exact (f.criticalValue.monotone hji).trans hi

private theorem cut_of_bot (f : TDA.Filtration.FilterFunction K α)
    (r : α) (hr : f.sublevel r = ⊥) (j : Fin f.criticalValues.card) :
    r < f.criticalValue j := by
  apply lt_of_not_ge
  intro hj
  obtain ⟨σ, hσ⟩ := (f.mem_criticalValues _).1 (f.criticalValue_mem j)
  have hm : σ.val ∈ f.sublevel r :=
    (f.mem_sublevel_iff_of_mem r σ).2 (hσ ▸ hj)
  rw [hr] at hm
  exact (TDA.Filtration.mem_bot_iff σ.val).mp hm

private theorem incl_eq_square {A B A' B' : PreAbstractSimplicialComplex V}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') (n : ℕ) :
    simplicialHomologyIncl k h n ≫
        CategoryTheory.eqToHom
          (congrArg (fun C => simplicialHomology C k n) hB) =
      CategoryTheory.eqToHom
          (congrArg (fun C => simplicialHomology C k n) hA) ≫
        simplicialHomologyIncl k h' n := by
  subst A'
  subst B'
  simp

private theorem incl_rank_congr {A B A' B' : PreAbstractSimplicialComplex V}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') (n : ℕ) :
    Module.finrank k (LinearMap.range (simplicialHomologyIncl k h n).hom) =
      Module.finrank k (LinearMap.range (simplicialHomologyIncl k h' n).hom) := by
  subst A'
  subst B'
  rfl

private theorem same_stage_identity (f : TDA.Filtration.FilterFunction K α)
    (n : ℕ) (r s : α) (hrs : r ≤ s)
    (C : PreAbstractSimplicialComplex V)
    (hr : f.sublevel r = C) (hs : f.sublevel s = C) :
    simplicialHomologyIncl k (f.sublevel_mono hrs) n ≫
        eqToHom (congrArg (fun D => simplicialHomology D k n) hs) =
      eqToHom (congrArg (fun D => simplicialHomology D k n) hr) := by
  simpa only [simplicialHomologyIncl_id, Category.comp_id] using
    incl_eq_square k hr hs (f.sublevel_mono hrs) (le_refl C) n

private theorem last_tail_identity (f : TDA.Filtration.FilterFunction K α)
    (n : ℕ) (hN : 0 < f.criticalValues.card)
    (r s : α) (hrs : r ≤ s)
    (hr : f.criticalValue
      ⟨f.criticalValues.card - 1, Nat.sub_lt hN (by decide)⟩ ≤ r) :
    simplicialHomologyIncl k (f.sublevel_mono hrs) n ≫
        eqToHom (congrArg (fun D => simplicialHomology D k n)
          (f.sublevel_eq_self_of_last_le hN s (hr.trans hrs))) =
      eqToHom (congrArg (fun D => simplicialHomology D k n)
        (f.sublevel_eq_self_of_last_le hN r hr)) := by
  exact same_stage_identity k f n r s hrs K
    (f.sublevel_eq_self_of_last_le hN r hr)
    (f.sublevel_eq_self_of_last_le hN s (hr.trans hrs))

private theorem threshold_two_step (f : TDA.Filtration.FilterFunction K α)
    (n : ℕ) (r s t : α) (hrs : r ≤ s) (hst : s ≤ t) :
    simplicialHomologyIncl k (f.sublevel_mono (hrs.trans hst)) n =
      simplicialHomologyIncl k (f.sublevel_mono hrs) n ≫
        simplicialHomologyIncl k (f.sublevel_mono hst) n := by
  exact simplicialHomologyIncl_comp k (f.sublevel_mono hrs)
    (f.sublevel_mono hst) n

private def point {N : ℕ} (v : Fin N → α) (I : FiniteInterval N) : α × WithTop α :=
  (v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
   if hd : I.death < N then
     (v ⟨I.death, hd⟩ : WithTop α)
   else
     (⊤ : WithTop α))

private theorem indexPoint_slice_threshold (f : TDA.Filtration.FilterFunction K α)
    (I : FiniteInterval f.criticalValues.card) (r s : α)
    (i j : Fin f.criticalValues.card)
    (hri : ∀ b : Fin f.criticalValues.card,
      f.criticalValue b ≤ r ↔ b ≤ i)
    (hsj : ∀ d : Fin f.criticalValues.card,
      f.criticalValue d ≤ s ↔ d ≤ j) :
    (point f.criticalValue I).1 ≤ r ∧
        (s : WithTop α) < (point f.criticalValue I).2 ↔
      I.birth ≤ i.val ∧ j.val < I.death := by
  constructor
  · rintro ⟨hb, hd⟩
    have hb' := (hri ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩).1 hb
    constructor
    · exact hb'
    · by_cases hdeath : I.death < f.criticalValues.card
      · have hd' : s < f.criticalValue ⟨I.death, hdeath⟩ := by
          simpa [point, hdeath] using hd
        have hnot : ¬ (⟨I.death, hdeath⟩ : Fin f.criticalValues.card) ≤ j := by
          intro h
          exact (not_lt_of_ge ((hsj _).2 h)) hd'
        exact Fin.lt_def.mp (lt_of_not_ge hnot)
      · omega
  · rintro ⟨hb, hd⟩
    constructor
    · exact (hri ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩).2 hb
    · by_cases hdeath : I.death < f.criticalValues.card
      · have hjd : j < (⟨I.death, hdeath⟩ : Fin f.criticalValues.card) := by
          exact Fin.lt_def.mpr hd
        have hsnot : ¬ f.criticalValue ⟨I.death, hdeath⟩ ≤ s := by
          intro h
          exact (not_le_of_gt hjd) ((hsj _).1 h)
        simpa [point, hdeath] using lt_of_not_ge hsnot
      · simp [point, hdeath]

private theorem countP_threshold_grades (f : TDA.Filtration.FilterFunction K α)
    (n : ℕ) (r s : α) (i j : Fin f.criticalValues.card)
    (hri : ∀ b : Fin f.criticalValues.card,
      f.criticalValue b ≤ r ↔ b ≤ i)
    (hsj : ∀ d : Fin f.criticalValues.card,
      f.criticalValue d ≤ s ↔ d ≤ j) :
    (dgm k f n).points.countP
        (fun p => p.1 ≤ r ∧ (s : WithTop α) < p.2) =
      (gradeHomologyBarcode k f n).countP
        (fun I => I.birth ≤ i.val ∧ j.val < I.death) := by
  classical
  change ((gradeHomologyBarcode k f n).map (point f.criticalValue)).countP _ = _
  rw [Multiset.countP_map, ← Multiset.countP_eq_card_filter]
  refine Multiset.countP_congr rfl ?_
  intro I _
  exact propext (indexPoint_slice_threshold f I r s i j hri hsj)

/-- The rank of the sublevel inclusion at arbitrary ordered thresholds is its
diagram slice count, with inclusive birth and strict death. -/
theorem rank_sublevelHomologyMap
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ)
    (r s : α) (hrs : r ≤ s) :
    Module.finrank k
      (LinearMap.range
        (TDA.Simplicial.simplicialHomologyIncl k
          (f.sublevel_mono hrs) n).hom) =
      (dgm k f n).points.countP
        (fun p => p.1 ≤ r ∧ (s : WithTop α) < p.2) := by
  classical
  rcases f.sublevel_eq_bot_or_grade r with hr | ⟨i, _, hr⟩
  · rw [incl_rank_congr k hr rfl (f.sublevel_mono hrs)
        (bot_le : (⊥ : PreAbstractSimplicialComplex V) ≤ f.sublevel s) n,
      bottomMapRank_zero k n]
    have hzero : (dgm k f n).points.countP
        (fun p => p.1 ≤ r ∧ (s : WithTop α) < p.2) = 0 := by
      change ((gradeHomologyBarcode k f n).map (point f.criticalValue)).countP _ = 0
      apply Multiset.countP_eq_zero.mpr
      intro p hp hpred
      obtain ⟨I, _, rfl⟩ := Multiset.mem_map.mp hp
      have hb := (cut_of_bot f r hr
        (⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩ :
          Fin f.criticalValues.card))
      exact (not_lt_of_ge hpred.1) hb
    exact hzero.symm
  · rcases f.sublevel_eq_bot_or_grade s with hs | ⟨j, _, hs⟩
    · have hbot : f.sublevel r = ⊥ :=
        le_antisymm (by simpa [hs] using f.sublevel_mono hrs) bot_le
      have hcontra : False := by
        have := cut_of_bot f r hbot i
        exact (not_lt_of_ge ((cut_of_grade f r i hr i).2 le_rfl)) this
      exact hcontra.elim
    · have hij : i ≤ j :=
        (cut_of_grade f s j hs i).1
          (((cut_of_grade f r i hr i).2 le_rfl).trans hrs)
      rw [incl_rank_congr k hr hs (f.sublevel_mono hrs)
        (f.gradeFiltration.monotone hij) n,
        rank_gradeHomologyMap k f n i j hij]
      exact (countP_threshold_grades k f n r s i j
        (cut_of_grade f r i hr) (cut_of_grade f s j hs)).symm

private theorem same_stage_rank (f : FilterFunction K α)
    (n : ℕ) (r s : α) (hrs : r ≤ s)
    (C : PreAbstractSimplicialComplex V)
    (hr : f.sublevel r = C) (hs : f.sublevel s = C) :
    Module.finrank k (LinearMap.range
      (simplicialHomologyIncl k (f.sublevel_mono hrs) n).hom) =
      Module.finrank k (simplicialHomology C k n) := by
  rw [incl_rank_congr k hr hs (f.sublevel_mono hrs) (le_refl C) n,
    simplicialHomologyIncl_id]
  change Module.finrank k (LinearMap.range
    (LinearMap.id : simplicialHomology C k n →ₗ[k] simplicialHomology C k n)) = _
  rw [LinearMap.range_id]
  exact finrank_top k (simplicialHomology C k n)

private theorem same_gap_identity (f : FilterFunction K α)
    (n : ℕ) (i : Fin f.criticalValues.card) (r s : α) (hrs : r ≤ s)
    (hr : f.criticalValue i ≤ r)
    (hs : ∀ j : Fin f.criticalValues.card, i < j → s < f.criticalValue j) :
    simplicialHomologyIncl k (f.sublevel_mono hrs) n ≫
        eqToHom (congrArg (fun C => simplicialHomology C k n)
          (f.sublevel_eq_grade_of_gap i s (hr.trans hrs) hs)) =
      eqToHom (congrArg (fun C => simplicialHomology C k n)
        (f.sublevel_eq_grade_of_gap i r hr
          (fun j hij => hrs.trans_lt (hs j hij)))) := by
  exact same_stage_identity k f n r s hrs (f.gradeFiltration i)
    (f.sublevel_eq_grade_of_gap i r hr (fun j hij => hrs.trans_lt (hs j hij)))
    (f.sublevel_eq_grade_of_gap i s (hr.trans hrs) hs)

private theorem same_gap_rank (f : FilterFunction K α)
    (n : ℕ) (i : Fin f.criticalValues.card) (r s : α) (hrs : r ≤ s)
    (hr : f.criticalValue i ≤ r)
    (hs : ∀ j : Fin f.criticalValues.card, i < j → s < f.criticalValue j) :
    Module.finrank k (LinearMap.range
      (simplicialHomologyIncl k (f.sublevel_mono hrs) n).hom) =
      Module.finrank k (simplicialHomology (f.gradeFiltration i) k n) := by
  exact same_stage_rank k f n r s hrs (f.gradeFiltration i)
    (f.sublevel_eq_grade_of_gap i r hr (fun j hij => hrs.trans_lt (hs j hij)))
    (f.sublevel_eq_grade_of_gap i s (hr.trans hrs) hs)

private theorem last_tail_rank (f : FilterFunction K α)
    (n : ℕ) (hN : 0 < f.criticalValues.card)
    (r s : α) (hrs : r ≤ s)
    (hr : f.criticalValue
      ⟨f.criticalValues.card - 1, Nat.sub_lt hN (by decide)⟩ ≤ r) :
    Module.finrank k (LinearMap.range
      (simplicialHomologyIncl k (f.sublevel_mono hrs) n).hom) =
      Module.finrank k (simplicialHomology K k n) := by
  exact same_stage_rank k f n r s hrs K
    (f.sublevel_eq_self_of_last_le hN r hr)
    (f.sublevel_eq_self_of_last_le hN s (hr.trans hrs))

private theorem threshold_grade_square (f : FilterFunction K α)
    (n : ℕ) (r s : α) (hrs : r ≤ s)
    (i j : Fin f.criticalValues.card) (hij : i ≤ j)
    (hr : f.sublevel r = f.gradeFiltration i)
    (hs : f.sublevel s = f.gradeFiltration j) :
    simplicialHomologyIncl k (f.sublevel_mono hrs) n ≫
        eqToHom (congrArg (fun C => simplicialHomology C k n) hs) =
      eqToHom (congrArg (fun C => simplicialHomology C k n) hr) ≫
        simplicialHomologyIncl k (f.gradeFiltration.monotone hij) n := by
  exact incl_eq_square k hr hs (f.sublevel_mono hrs)
    (f.gradeFiltration.monotone hij) n

private theorem threshold_grade_two_step (f : FilterFunction K α)
    (n : ℕ) (r s t : α) (hrs : r ≤ s) (hst : s ≤ t)
    (i j l : Fin f.criticalValues.card) (hij : i ≤ j) (hjl : j ≤ l)
    (hr : f.sublevel r = f.gradeFiltration i)
    (hs : f.sublevel s = f.gradeFiltration j)
    (ht : f.sublevel t = f.gradeFiltration l) :
    simplicialHomologyIncl k (f.sublevel_mono (hrs.trans hst)) n ≫
        eqToHom (congrArg (fun C => simplicialHomology C k n) ht) =
      eqToHom (congrArg (fun C => simplicialHomology C k n) hr) ≫
        (simplicialHomologyIncl k (f.gradeFiltration.monotone hij) n ≫
          simplicialHomologyIncl k (f.gradeFiltration.monotone hjl) n) := by
  rw [threshold_two_step k f n r s t hrs hst, Category.assoc,
    threshold_grade_square k f n s t hst j l hjl hs ht,
    ← Category.assoc, threshold_grade_square k f n r s hrs i j hij hr hs,
    Category.assoc]

private theorem essential_total (f : FilterFunction K α)
    (n : ℕ) (hN : 0 < f.criticalValues.card) :
    (dgm k f n).points.countP (fun p => p.2 = (⊤ : WithTop α)) =
      Module.finrank k (simplicialHomology K k n) := by
  classical
  let last : Fin f.criticalValues.card :=
    ⟨f.criticalValues.card - 1, Nat.sub_lt hN (by decide)⟩
  have hlast (i : Fin f.criticalValues.card) : i ≤ last := by
    apply Fin.le_def.mpr
    have hi := i.isLt
    dsimp [last]
    omega
  have hcount : (dgm k f n).points.countP (fun p => p.2 = (⊤ : WithTop α)) =
      (dgm k f n).points.countP
        (fun p => p.1 ≤ f.criticalValue last ∧
          (f.criticalValue last : WithTop α) < p.2) := by
    apply Multiset.countP_congr rfl
    intro p hp
    change p ∈ (gradeHomologyBarcode k f n).map (point f.criticalValue) at hp
    obtain ⟨I, _, rfl⟩ := Multiset.mem_map.mp hp
    have hb := f.criticalValue.monotone
      (hlast ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩)
    by_cases hd : I.death < f.criticalValues.card
    · have hdeath := f.criticalValue.monotone (hlast ⟨I.death, hd⟩)
      simp [point, hd, not_lt_of_ge hdeath]
    · simp [point, hd, hb]
  rw [hcount, ← rank_sublevelHomologyMap k f n
    (f.criticalValue last) (f.criticalValue last) le_rfl]
  exact last_tail_rank k f n hN _ _ le_rfl le_rfl

/-- Agreement with a barcode is conditional on a supplied natural isomorphism of the
critical-grade homology module. -/
theorem dgm_eq_ofIndexBars_of_iso
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ)
    (B : Multiset (FiniteInterval f.criticalValues.card))
    (e : simplicialHomologyPModule k f.gradeFiltration n ≅
      barcodeModule (k := k) B) :
    dgm k f n =
      ofIndexBars f.criticalValue f.criticalValue.strictMono B := by
  unfold dgm gradeHomologyBarcode
  rw [rankBarcode_eq_of_iso_barcodeModule B e]

end TDA.Persistence
