import TDA.Filtration.CompatibleOrderPrefix
import TDA.Filtration.CompatibleOrderTransfer
import TDA.Persistence.SublevelDiagram
import TDA.Persistence.RankReindex
import TDA.Persistence.DiagramLaws

set_option autoImplicit false

/-!
A fixed compatible enumeration supplies a value-independent prefix homology barcode.
The comparison with attained grades uses actual inclusion maps between the equal
subcomplexes, including when several faces have one grade.
-/

universe u w
namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration CategoryTheory

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TotalFace K)]
variable {f : FilterFunction K α}

/-- The number of actual nonempty faces of a simplicial complex. -/
abbrev faceCount (K : PreAbstractSimplicialComplex V) [Fintype (TotalFace K)] :=
  Fintype.card (TotalFace K)

/-- Actual homology of the first `t` faces, including the empty stage `t = 0`. -/
noncomputable def facePrefixModule (e : CompatibleOrder f) (n : ℕ) :
    PModule.{u,0,u} k (Fin (faceCount K + 1)) :=
  simplicialHomologyPModule k
    (TDA.Filtration.reindex (⟨Fin.val, fun _ _ h => h⟩ : Fin (faceCount K + 1) →o ℕ)
      e.prefixFiltration) n

noncomputable instance facePrefix_finiteDimensional
    (e : CompatibleOrder f) (n : ℕ) (i : Fin (faceCount K + 1)) :
    FiniteDimensional k ((facePrefixModule k e n).obj i) := by
  have hsub : e.prefixComplex i.val ≤ K := by
    intro s hs
    exact ((e.mem_prefixComplex _ s).mp hs).1
  letI : Finite (Face K n) := faceFiniteOfTotalFinite K n
  letI : Finite (Face (e.prefixComplex i.val) n) :=
    Finite.of_injective (faceIncl hsub n) (by
      intro a b hab
      exact Subtype.ext (congrArg (fun t : Face K n => t.1) hab))
  change FiniteDimensional k (simplicialHomology (e.prefixComplex i.val) k n)
  infer_instance

/-- Canonical barcode of actual prefix homology. It depends on the enumeration,
coefficient field and homological degree, and has `m + 1` stages. -/
noncomputable def facePrefixBarcode (e : CompatibleOrder f) (n : ℕ) :
    Multiset (FiniteInterval (faceCount K + 1)) :=
  rankBarcode (facePrefixModule k e n)

private theorem empty_homology_subsingleton (n : ℕ) :
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
  let eqv := (homologyKernelQuotient.{u,u,u} k
    (simplicialChainComplex (⊥ : PreAbstractSimplicialComplex V) k) n).toLinearEquiv
  exact ⟨fun a b => eqv.injective (Subsingleton.elim _ _)⟩

/-- No canonical prefix interval is born at stage zero, since it has actual zero homology. -/
theorem facePrefixBarcode_birth_pos (e : CompatibleOrder f) (n : ℕ)
    (I : FiniteInterval (faceCount K + 1))
    (hI : I ∈ facePrefixBarcode k e n) : 0 < I.birth := by
  let z : Fin (faceCount K + 1) := ⟨0, Nat.succ_pos _⟩
  have hzero : structureMapRank (facePrefixModule k e n) z z le_rfl = 0 := by
    have hsub : Subsingleton ((facePrefixModule k e n).obj z) := by
      change Subsingleton (simplicialHomology (e.prefixComplex 0) k n)
      rw [e.prefixComplex_zero]
      exact empty_homology_subsingleton k n
    unfold structureMapRank
    have hm : structureMapLinear (facePrefixModule k e n) (le_refl z) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    rw [hm, LinearMap.range_zero]
    exact Module.finrank_zero_of_subsingleton (R := k)
  have hcount : (facePrefixBarcode k e n).countP
      (fun J => J.birth ≤ z.val ∧ z.val < J.death) = 0 := by
    rw [← rank_barcodeMap (k := k) (facePrefixBarcode k e n) z z le_rfl]
    change structureMapRank
      (barcodeModule (k := k) (rankBarcode (facePrefixModule k e n))) z z le_rfl = 0
    rw [structureMapRank_rankBarcode]
    exact hzero
  have hnot := (Multiset.countP_eq_zero.mp hcount) I hI
  by_contra hb
  have hb0 : I.birth = 0 := Nat.eq_zero_of_not_pos hb
  exact hnot ⟨by change I.birth ≤ 0; omega,
    by change 0 < I.death; rw [← hb0]; exact I.birth_lt_death⟩

private theorem inclusion_rank_congr {A B C D : PreAbstractSimplicialComplex V}
    (hA : A = C) (hB : B = D) (hab : A ≤ B) (hcd : C ≤ D) (n : ℕ) :
    Module.finrank k (LinearMap.range (simplicialHomologyIncl k hab n).hom) =
      Module.finrank k (LinearMap.range (simplicialHomologyIncl k hcd n).hom) := by
  subst C
  subst D
  rfl

/-- A critical grade is sampled at the number of faces at or below that grade. -/
def faceGradeSample (e : CompatibleOrder f) :
    Fin f.criticalValues.card →o Fin (faceCount K + 1) where
  toFun i := ⟨e.sublevelCount (f.criticalValue i),
    Nat.lt_succ_of_le (e.sublevelCount_le_card _)⟩
  monotone' := by
    intro i j hij
    exact Fin.le_def.mpr (e.sublevelCount_mono (f.criticalValue.monotone hij))

/-- A sampled prefix homology map has the rank of the corresponding actual grade
homology inclusion. The two endpoint identifications commute with inclusion. -/
theorem faceGradeSample_map_rank (e : CompatibleOrder f) (n : ℕ)
    (i j : Fin f.criticalValues.card) (hij : i ≤ j) :
    structureMapRank (reindex (faceGradeSample e) (facePrefixModule k e n)) i j hij =
      structureMapRank (simplicialHomologyPModule k f.gradeFiltration n) i j hij := by
  rw [structureMapRank_reindex]
  unfold structureMapRank
  change Module.finrank k (LinearMap.range
      (simplicialHomologyIncl k (e.prefixComplex_mono
        (e.sublevelCount_mono (f.criticalValue.monotone hij))) n).hom) =
    Module.finrank k (LinearMap.range
      (simplicialHomologyIncl k (f.gradeFiltration.monotone hij) n).hom)
  have hi : e.prefixComplex (e.sublevelCount (f.criticalValue i)) = f.gradeFiltration i := by
    exact (e.sublevel_eq_prefixComplex _).symm.trans (f.gradeFiltration_apply i).symm
  have hj : e.prefixComplex (e.sublevelCount (f.criticalValue j)) = f.gradeFiltration j := by
    exact (e.sublevel_eq_prefixComplex _).symm.trans (f.gradeFiltration_apply j).symm
  exact inclusion_rank_congr k hi hj _ _ n

/-- The actual attained-grade barcode is the restriction of the fixed prefix barcode. -/
theorem gradeHomologyBarcode_eq_reindex_facePrefixBarcode
    (e : CompatibleOrder f) (n : ℕ) :
    gradeHomologyBarcode k f n =
      reindexBarcode (faceGradeSample e) (facePrefixBarcode k e n) := by
  change rankBarcode (simplicialHomologyPModule k f.gradeFiltration n) =
    reindexBarcode (faceGradeSample e) (rankBarcode (facePrefixModule k e n))
  rw [← rankBarcode_reindex]
  apply (rankBarcode_eq_iff
    (simplicialHomologyPModule k f.gradeFiltration n)
    (reindex (faceGradeSample e) (facePrefixModule k e n))).2
  intro i j hij
  exact (faceGradeSample_map_rank k e n i j hij).symm

private def birthFaceIndex (I : FiniteInterval (faceCount K + 1))
    (hb : 0 < I.birth) : Fin (faceCount K) :=
  ⟨I.birth - 1, by have := I.birth_lt_death; have := I.death_le_size; omega⟩

private def deathFaceIndex (I : FiniteInterval (faceCount K + 1))
    (hd : I.death ≤ faceCount K) : Fin (faceCount K) :=
  ⟨I.death - 1, by have := I.birth_lt_death; omega⟩

/-- The fixed finite index-pair multiset, with stages shifted to entering faces. -/
noncomputable def faceTemplatePairs (e : CompatibleOrder f) (n : ℕ) :
    Multiset (Fin (faceCount K) × Fin (faceCount K)) :=
  (facePrefixBarcode k e n).filterMap fun I =>
    if hb : 0 < I.birth then
      if hd : I.death ≤ faceCount K then
        some (birthFaceIndex I hb, deathFaceIndex I hd)
      else none
    else none

/-- The fixed essential birth-index multiset. -/
noncomputable def faceTemplateEssential (e : CompatibleOrder f) (n : ℕ) :
    Multiset (Fin (faceCount K)) :=
  (facePrefixBarcode k e n).filterMap fun I =>
    if hb : 0 < I.birth then
      if I.death ≤ faceCount K then none
      else some (birthFaceIndex I hb)
    else none

/-- The stage-to-face shift is increasing for every finite template pair. -/
theorem faceTemplatePairs_lt (e : CompatibleOrder f) (n : ℕ)
    (p : Fin (faceCount K) × Fin (faceCount K))
    (hp : p ∈ faceTemplatePairs k e n) : p.1 < p.2 := by
  obtain ⟨I, _, hI⟩ := (Multiset.mem_filterMap _ _).mp hp
  split_ifs at hI with hb hd
  · cases hI
    apply Fin.lt_def.mpr
    change I.birth - 1 < I.death - 1
    have := I.birth_lt_death
    omega

/-- The empty face set produces no prefix intervals and hence an empty template. -/
theorem facePrefixBarcode_empty (e : CompatibleOrder f) (n : ℕ)
    (hm : faceCount K = 0) : facePrefixBarcode k e n = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro I hI
  have hb := facePrefixBarcode_birth_pos k e n I hI
  have hlt := I.birth_lt_death
  have hle := I.death_le_size
  omega

theorem faceTemplatePairs_empty (e : CompatibleOrder f) (n : ℕ)
    (hm : faceCount K = 0) : faceTemplatePairs k e n = 0 := by
  simp [faceTemplatePairs, facePrefixBarcode_empty k e n hm]

theorem faceTemplateEssential_empty (e : CompatibleOrder f) (n : ℕ)
    (hm : faceCount K = 0) : faceTemplateEssential k e n = 0 := by
  simp [faceTemplateEssential, facePrefixBarcode_empty k e n hm]

/-- With one face there can be no finite pair; any degree-zero class is essential. -/
theorem faceTemplatePairs_one_face (e : CompatibleOrder f) (n : ℕ)
    (hm : faceCount K = 1) : faceTemplatePairs k e n = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro p hp
  obtain ⟨I, hI, hpoint⟩ := (Multiset.mem_filterMap _ _).mp hp
  have hb := facePrefixBarcode_birth_pos k e n I hI
  split_ifs at hpoint with hb' hd
  · have hlt := I.birth_lt_death
    omega

/-- The prefix endpoint cut at stage `t` is the attained-grade index of face `t - 1`. -/
theorem faceGradeSample_endpoint (e : CompatibleOrder f) (t : ℕ)
    (ht : 0 < t) (hm : t ≤ faceCount K) :
    ∃ q : Fin f.criticalValues.card,
      f.criticalValue q = f.value (e.enum ⟨t - 1, by dsimp [faceCount] at hm ⊢; omega⟩) ∧
      sampledEndpoint (faceGradeSample e) t = q.val := by
  let b : Fin (faceCount K) := ⟨t - 1, by dsimp [faceCount] at hm ⊢; omega⟩
  obtain ⟨q, hq⟩ := f.exists_criticalValue_eq (e.enum b)
  refine ⟨q, by simpa [b] using hq, ?_⟩
  unfold sampledEndpoint
  have hs : (Finset.univ.filter (fun j : Fin f.criticalValues.card =>
      ((faceGradeSample e) j).val < t)) = Finset.Iio q := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    have hinc := e.value_le_iff_index_lt_sublevelCount (f.criticalValue j) b
    have heq : ((faceGradeSample e) j).val = e.sublevelCount (f.criticalValue j) := rfl
    rw [heq]
    have hc : e.sublevelCount (f.criticalValue j) < t ↔
        f.criticalValue j < f.value (e.enum b) := by
      constructor
      · intro hsmall
        by_contra hn
        have hle := hinc.mp (le_of_not_gt hn)
        have hbval : b.val = t - 1 := rfl
        omega
      · intro hlt
        by_contra hn
        have hlarge : b.val < e.sublevelCount (f.criticalValue j) := by
          have hbval : b.val = t - 1 := rfl
          omega
        exact (not_le_of_gt hlt) (hinc.mpr hlarge)
    rw [hc, ← hq]
    exact f.criticalValue.lt_iff_lt.trans Fin.lt_def
  rw [hs, Fin.card_Iio]

/-- Evaluate a finite pair of face indices at the corresponding two face values. -/
def pairValues {β : Type*} [LinearOrder β] (g : FilterFunction K β)
    (e : CompatibleOrder f) (p : Fin (faceCount K) × Fin (faceCount K)) : β × β :=
  (g.value (e.enum p.1), g.value (e.enum p.2))

/-- Evaluate one essential birth index at its entering face value. -/
def birthValue {β : Type*} [LinearOrder β] (g : FilterFunction K β)
    (e : CompatibleOrder f) (i : Fin (faceCount K)) : β :=
  g.value (e.enum i)

private def gradePoint {N : ℕ} {β : Type*} [LinearOrder β]
    (v : Fin N → β) (I : FiniteInterval N) : β × WithTop β :=
  (v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
    if hd : I.death < N then (v ⟨I.death, hd⟩ : WithTop β) else ⊤)

private def facePoint (e : CompatibleOrder f)
    (I : FiniteInterval (faceCount K + 1)) : Option (α × WithTop α) :=
  if hb : 0 < I.birth then
    if hd : I.death ≤ faceCount K then
      let b := f.value (e.enum (birthFaceIndex I hb))
      let d := f.value (e.enum (deathFaceIndex I hd))
      if b = d then none else some (b, (d : WithTop α))
    else some (f.value (e.enum (birthFaceIndex I hb)), ⊤)
  else none

/-- A prefix bar evaluates to its sampled bar, or disappears exactly at a tied
finite endpoint. -/
private theorem facePoint_restrictAlong (e : CompatibleOrder f)
    (I : FiniteInterval (faceCount K + 1)) (hb : 0 < I.birth) :
    facePoint e I = (I.restrictAlong (faceGradeSample e)).map
      (gradePoint f.criticalValue) := by
  have hbm : I.birth ≤ faceCount K := by
    have h1 := I.birth_lt_death
    have h2 := I.death_le_size
    omega
  obtain ⟨qb, hqb, hcutb⟩ := faceGradeSample_endpoint e I.birth hb hbm
  have hbidx : (⟨I.birth - 1, by omega⟩ : Fin (faceCount K)) =
      birthFaceIndex I hb := rfl
  have hbirth : f.criticalValue qb = f.value (e.enum (birthFaceIndex I hb)) := by
    simpa [hbidx] using hqb
  by_cases hd : I.death ≤ faceCount K
  · obtain ⟨qd, hqd, hcutd⟩ := faceGradeSample_endpoint e I.death
      (lt_trans hb I.birth_lt_death) hd
    have hdidx : (⟨I.death - 1, by omega⟩ : Fin (faceCount K)) =
        deathFaceIndex I hd := rfl
    have hdeath : f.criticalValue qd = f.value (e.enum (deathFaceIndex I hd)) := by
      simpa [hdidx] using hqd
    have hle : qb ≤ qd := by
      apply f.criticalValue.le_iff_le.mp
      rw [hbirth, hdeath]
      apply e.monotone
      apply Fin.le_def.mpr
      change I.birth - 1 ≤ I.death - 1
      have := I.birth_lt_death
      omega
    by_cases heq : qb = qd
    · have hv : f.value (e.enum (birthFaceIndex I hb)) =
          f.value (e.enum (deathFaceIndex I hd)) := by
        rw [← hbirth, ← hdeath, heq]
      have hc : ¬ sampledEndpoint (faceGradeSample e) I.birth <
          sampledEndpoint (faceGradeSample e) I.death := by
        rw [hcutb, hcutd, heq]
        exact lt_irrefl _
      simp [facePoint, hb, hd, hv, FiniteInterval.restrictAlong, hc]
    · have hlt : qb < qd := lt_of_le_of_ne hle heq
      have hc : sampledEndpoint (faceGradeSample e) I.birth <
          sampledEndpoint (faceGradeSample e) I.death := by
        rw [hcutb, hcutd]
        exact hlt
      have hv : f.value (e.enum (birthFaceIndex I hb)) ≠
          f.value (e.enum (deathFaceIndex I hd)) := by
        rw [← hbirth, ← hdeath]
        exact f.criticalValue.injective.ne heq
      simp [facePoint, hb, hd, hv, FiniteInterval.restrictAlong, hc,
        gradePoint, hcutb, hcutd, hbirth, hdeath, qd.isLt]
      exact hlt
  · have hterminal : I.death = faceCount K + 1 := by
      have := I.death_le_size
      omega
    have hsize : sampledEndpoint (faceGradeSample e) I.death = f.criticalValues.card := by
      rw [hterminal]
      unfold sampledEndpoint
      have hfull : (Finset.univ.filter (fun j : Fin f.criticalValues.card =>
          ((faceGradeSample e) j).val < faceCount K + 1)) = Finset.univ := by
        apply Finset.filter_eq_self.mpr
        intro j _
        exact Nat.lt_succ_of_le (e.sublevelCount_le_card (f.criticalValue j))
      rw [hfull]
      simp
    have hc : sampledEndpoint (faceGradeSample e) I.birth <
        sampledEndpoint (faceGradeSample e) I.death := by
      rw [hcutb, hsize]
      exact qb.isLt
    simp [facePoint, hb, hd, FiniteInterval.restrictAlong, hc,
      gradePoint, hcutb, hsize, hbirth]

/-- Evaluate the fixed face-index multisets at another filter monotone along the
same face enumeration. Equal finite endpoints disappear, with multiplicity retained. -/
noncomputable def evaluateFaceTemplate {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hg : Monotone (g.value ∘ e.enum)) (n : ℕ) : Diagram β where
  points :=
    (((faceTemplatePairs k e n).map (pairValues g e)).filter
      (fun p => p.1 ≠ p.2)).map (fun p => (p.1, (p.2 : WithTop β))) +
    ((faceTemplateEssential k e n).map (birthValue g e)).map
      (fun b => (b, (⊤ : WithTop β)))
  offDiagonal := by
    intro p hp
    rcases Multiset.mem_add.mp hp with hp | hp
    · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hp
      simpa using (Multiset.mem_filter.mp hv).2
    · obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hp
      simp

/-- A monotone evaluation has only strictly positive diagram points. -/
theorem evaluateFaceTemplate_isPositive {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hg : Monotone (g.value ∘ e.enum)) (n : ℕ) :
    (evaluateFaceTemplate k e g hg n).IsPositive := by
  intro p hp
  change p ∈ (((faceTemplatePairs k e n).map (pairValues g e)).filter
      (fun q => q.1 ≠ q.2)).map (fun q => (q.1, (q.2 : WithTop β))) +
    ((faceTemplateEssential k e n).map (birthValue g e)).map
      (fun b => (b, (⊤ : WithTop β))) at hp
  rcases Multiset.mem_add.mp hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_filter.mp hq).1
    have hle := hg (faceTemplatePairs_lt k e n r hr).le
    have hne := (Multiset.mem_filter.mp hq).2
    exact WithTop.coe_lt_coe.mpr (lt_of_le_of_ne hle hne)
  · obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
    simp

/-- If every face is tied, all finite pairs vanish in the evaluation. -/
theorem evaluateFaceTemplate_constant_points {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hg : Monotone (g.value ∘ e.enum)) (n : ℕ) (c : β)
    (hc : ∀ s : TotalFace K, g.value s = c) :
    (evaluateFaceTemplate k e g hg n).points =
      (faceTemplateEssential k e n).map
        (fun _ => (c, (⊤ : WithTop β))) := by
  simp [evaluateFaceTemplate, pairValues, birthValue, hc]
  intro a b x y _ hca hcb
  exact hca.symm.trans hcb

/-- Any enumerations of the two multisets give the same ordered representative. -/
theorem evaluateFaceTemplate_eq_orderedQ {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hg : Monotone (g.value ∘ e.enum)) (n : ℕ) :
    let P := (faceTemplatePairs k e n).map (pairValues g e)
    let U := (faceTemplateEssential k e n).map (birthValue g e)
    evaluateFaceTemplate k e g hg n =
      orderedQ P.toList.length U.toList.length (P.toList.get, U.toList.get) := by
  intro P U
  apply Diagram.ext
  simp only [evaluateFaceTemplate, orderedQ, List.ofFn_get, Multiset.coe_toList]
  rfl

/-- The ordered representative may use any enumeration of the evaluated
finite and essential multisets. -/
theorem evaluateFaceTemplate_eq_orderedQ_of_enumerations
    {β : Type*} [LinearOrder β] (e : CompatibleOrder f)
    (g : FilterFunction K β) (hg : Monotone (g.value ∘ e.enum)) (n : ℕ)
    (m l : ℕ) (x : Fin m → β × β) (y : Fin l → β)
    (hx : Multiset.ofList (List.ofFn x) =
      (faceTemplatePairs k e n).map (pairValues g e))
    (hy : Multiset.ofList (List.ofFn y) =
      (faceTemplateEssential k e n).map (birthValue g e)) :
    evaluateFaceTemplate k e g hg n = orderedQ m l (x, y) := by
  let P := (faceTemplatePairs k e n).map (pairValues g e)
  let U := (faceTemplateEssential k e n).map (birthValue g e)
  rw [evaluateFaceTemplate_eq_orderedQ]
  apply (orderedQ_eq_iff P.toList.length U.toList.length m l
    (P.toList.get, U.toList.get) (x, y)).mpr
  constructor
  · simpa only [List.ofFn_get, Multiset.coe_toList] using
      congrArg (Multiset.filter (fun p : β × β => p.1 ≠ p.2)) hx.symm
  · simpa only [List.ofFn_get, Multiset.coe_toList] using hy.symm

private theorem evaluateFaceTemplate_points_filterMap
    (e : CompatibleOrder f) (n : ℕ) :
    (evaluateFaceTemplate k e f e.monotone n).points =
      (facePrefixBarcode k e n).filterMap (facePoint e) := by
  classical
  let B := facePrefixBarcode k e n
  have hpos : ∀ I ∈ B, 0 < I.birth := by
    intro I hI
    exact facePrefixBarcode_birth_pos k e n I hI
  change (((B.filterMap fun I =>
      if hb : 0 < I.birth then
        if hd : I.death ≤ faceCount K then
          some (birthFaceIndex I hb, deathFaceIndex I hd)
        else none
      else none).map (pairValues f e)).filter
      (fun p => p.1 ≠ p.2)).map (fun p => (p.1, (p.2 : WithTop α))) +
    ((B.filterMap fun I =>
      if hb : 0 < I.birth then
        if I.death ≤ faceCount K then none
        else some (birthFaceIndex I hb)
      else none).map (birthValue f e)).map
      (fun b => (b, (⊤ : WithTop α))) = B.filterMap (facePoint e)
  revert hpos
  induction B using Multiset.induction_on with
  | empty => simp
  | @cons I B ih =>
    intro hpos
    have hb : 0 < I.birth := hpos I (Multiset.mem_cons_self I B)
    have hposB : ∀ J ∈ B, 0 < J.birth := by
      intro J hJ
      exact hpos J (Multiset.mem_cons_of_mem hJ)
    specialize ih hposB
    by_cases hd : I.death ≤ faceCount K
    · by_cases hv : f.value (e.enum (birthFaceIndex I hb)) =
          f.value (e.enum (deathFaceIndex I hd))
      · simp [Multiset.filterMap_cons, hb, hd, hv, facePoint,
          pairValues, birthValue, ih, add_assoc]
        simpa only [Multiset.map_map, Function.comp_def, ne_eq] using ih
      · simp [Multiset.filterMap_cons, hb, hd, hv, facePoint,
          pairValues, birthValue, ih, add_assoc]
        simpa only [Multiset.map_map, Function.comp_def, ne_eq] using ih
    · simp [Multiset.filterMap_cons, hb, hd, facePoint,
        pairValues, birthValue, ih, add_assoc]
      simpa only [Multiset.map_map, Function.comp_def, ne_eq] using ih

private theorem filterMap_congr_mem {X Y : Type*} (B : Multiset X)
    (a b : X → Option Y) (h : ∀ x ∈ B, a x = b x) :
    B.filterMap a = B.filterMap b := by
  revert h
  induction B using Multiset.induction_on with
  | empty => intro _; simp
  | @cons x B ih =>
    intro h
    have hx := h x (Multiset.mem_cons_self x B)
    have hB : ∀ y ∈ B, a y = b y := by
      intro y hy
      exact h y (Multiset.mem_cons_of_mem hy)
    simp [Multiset.filterMap_cons, hx, ih hB]

/-- Evaluation agrees with the actual sublevel persistence diagram for every
filter monotone along the fixed enumeration. -/
theorem evaluateFaceTemplate_eq_dgm {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hg : Monotone (g.value ∘ e.enum)) (n : ℕ) :
    evaluateFaceTemplate k e g hg n = dgm k g n := by
  let eg : CompatibleOrder g := e.transfer hg
  have htemplate : evaluateFaceTemplate k e g hg n =
      evaluateFaceTemplate k eg g eg.monotone n := by
    rfl
  rw [htemplate]
  apply Diagram.ext
  rw [evaluateFaceTemplate_points_filterMap]
  have hreindex := gradeHomologyBarcode_eq_reindex_facePrefixBarcode k eg n
  change (facePrefixBarcode k eg n).filterMap (facePoint eg) =
    (gradeHomologyBarcode k g n).map (gradePoint g.criticalValue)
  rw [hreindex]
  change (facePrefixBarcode k eg n).filterMap (facePoint eg) =
    ((facePrefixBarcode k eg n).filterMap
      (FiniteInterval.restrictAlong (faceGradeSample eg))).map
        (gradePoint g.criticalValue)
  classical
  rw [Multiset.map_filterMap]
  apply filterMap_congr_mem
  intro I hI
  exact facePoint_restrictAlong eg I (facePrefixBarcode_birth_pos k eg n I hI)

/-- Changing the compatible reference filter while retaining the enumeration does
not change the actual prefix barcode. -/
theorem facePrefixBarcode_transfer {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hg : Monotone (g.value ∘ e.enum)) (n : ℕ) :
    facePrefixBarcode k (e.transfer hg) n = facePrefixBarcode k e n := by
  rfl

theorem faceTemplatePairs_transfer {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hg : Monotone (g.value ∘ e.enum)) (n : ℕ) :
    faceTemplatePairs k (e.transfer hg) n = faceTemplatePairs k e n := by
  rfl

theorem faceTemplateEssential_transfer {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hg : Monotone (g.value ∘ e.enum)) (n : ℕ) :
    faceTemplateEssential k (e.transfer hg) n = faceTemplateEssential k e n := by
  rfl

/-- Any two compatible witnesses with the same enumeration give the same
actual prefix barcode, regardless of their reference filters. -/
theorem facePrefixBarcode_sameEnumeration {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) {g : FilterFunction K β}
    (e' : CompatibleOrder g) (henum : e.enum = e'.enum) (n : ℕ) :
    facePrefixBarcode k e n = facePrefixBarcode k e' n := by
  have hg : Monotone (g.value ∘ e.enum) := by
    simpa only [henum] using e'.monotone
  have he : e.transfer hg = e' := by
    cases e with
    | mk enum face_lt monotone =>
      cases e' with
      | mk enum' face_lt' monotone' =>
        dsimp at henum
        cases henum
        rfl
  rw [← he]
  exact (facePrefixBarcode_transfer k e g hg n).symm

/-- Finite template pairs depend only on the face enumeration. -/
theorem faceTemplatePairs_sameEnumeration {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) {g : FilterFunction K β}
    (e' : CompatibleOrder g) (henum : e.enum = e'.enum) (n : ℕ) :
    faceTemplatePairs k e n = faceTemplatePairs k e' n := by
  have hg : Monotone (g.value ∘ e.enum) := by
    simpa only [henum] using e'.monotone
  have he : e.transfer hg = e' := by
    cases e with
    | mk enum face_lt monotone =>
      cases e' with
      | mk enum' face_lt' monotone' =>
        dsimp at henum
        cases henum
        rfl
  rw [← he]
  exact (faceTemplatePairs_transfer k e g hg n).symm

/-- Essential template indices depend only on the face enumeration. -/
theorem faceTemplateEssential_sameEnumeration {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) {g : FilterFunction K β}
    (e' : CompatibleOrder g) (henum : e.enum = e'.enum) (n : ℕ) :
    faceTemplateEssential k e n = faceTemplateEssential k e' n := by
  have hg : Monotone (g.value ∘ e.enum) := by
    simpa only [henum] using e'.monotone
  have he : e.transfer hg = e' := by
    cases e with
    | mk enum face_lt monotone =>
      cases e' with
      | mk enum' face_lt' monotone' =>
        dsimp at henum
        cases henum
        rfl
  rw [← he]
  exact (faceTemplateEssential_transfer k e g hg n).symm

/-- Ordering-equivalent filters select the same finite index pairs with strict
endpoints. The selected multiset retains repeated pairs. -/
theorem faceTemplatePairs_strict_orderingEquivalent {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hfg : OrderingEquivalent f g) (n : ℕ) :
    (faceTemplatePairs k e n).filter
        (fun p => f.value (e.enum p.1) < f.value (e.enum p.2)) =
      (faceTemplatePairs k e n).filter
        (fun p => g.value (e.enum p.1) < g.value (e.enum p.2)) := by
  classical
  apply Multiset.filter_congr
  intro p _
  simpa only [lt_iff_not_ge] using
    (not_congr (hfg (e.enum p.2) (e.enum p.1)))

/-- Ordering equivalence preserves the tied index pairs, which disappear in
both value evaluations. -/
theorem faceTemplatePairs_tied_orderingEquivalent {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hfg : OrderingEquivalent f g) (n : ℕ) :
    (faceTemplatePairs k e n).filter
        (fun p => f.value (e.enum p.1) = f.value (e.enum p.2)) =
      (faceTemplatePairs k e n).filter
        (fun p => g.value (e.enum p.1) = g.value (e.enum p.2)) := by
  classical
  apply Multiset.filter_congr
  intro p _
  exact hfg.value_eq_iff (e.enum p.1) (e.enum p.2)

/-- Two face-compatible orders for one filter can have different index templates,
but evaluate to the same actual diagram. -/
theorem evaluateFaceTemplate_order_independent {β : Type*} [LinearOrder β]
    (g : FilterFunction K β) (e₁ e₂ : CompatibleOrder g) (n : ℕ) :
    evaluateFaceTemplate k e₁ g e₁.monotone n =
      evaluateFaceTemplate k e₂ g e₂.monotone n := by
  rw [evaluateFaceTemplate_eq_dgm, evaluateFaceTemplate_eq_dgm]

end TDA.Persistence
