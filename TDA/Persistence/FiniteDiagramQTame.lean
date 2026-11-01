import TDA.Persistence.LocallyFiniteDiagramBottleneck

/-!
# Canonical multiplicities from finite barcode ranks

The four-rank rectangle formula and stabilized essential strips identify the
canonical decorated diagram of a module whose ranks are represented by a positive
finite diagram. Multiplicities count occurrences, including repeated and essential bars.
-/

universe u
namespace TDA.Persistence.FiniteDiagramQTame
open TDA.Persistence.RectangleMeasure
open scoped Classical
variable {k : Type u} [Field k] (M : PModule.{u,0,u} k ℝ) (hQ : M.QTame)
    (D : Diagram ℝ)
    (hrank : ∀ (s t : ℝ) (h : s ≤ t), Module.finrank k (persistenceImage M h) =
      D.points.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2))
    (hD : D.IsPositive)

/-- The decorated endpoint of one occurrence in a finite real persistence diagram.
Finite deaths are recorded by their minus cuts, and essential deaths by `infinityCut`. -/
noncomputable abbrev diagramOccurrence := diagramDecoratedPoint

@[simp] theorem diagramOccurrence_finite (b d : ℝ) :
    diagramOccurrence (b, (d : WithTop ℝ)) = (minusCut b, minusCut d) := rfl

@[simp] theorem diagramOccurrence_essential (b : ℝ) :
    diagramOccurrence (b, (⊤ : WithTop ℝ)) = (minusCut b, infinityCut) := rfl

private theorem diagramOccurrence_mem_rectangleCell (p : ℝ × WithTop ℝ)
    (a b c d : ℝ) :
    diagramOccurrence p ∈ rectangleCell a b c d ↔
      a < p.1 ∧ p.1 ≤ b ∧ c < p.2 ∧ p.2 ≤ (d : WithTop ℝ) := by
  rcases p with ⟨birth, death⟩
  cases death with
  | top => simp [diagramOccurrence, rectangleCell, infinityCut_not_mem_cutCell]
  | coe death =>
      simp [diagramOccurrence, rectangleCell, cutCell, minusCut, and_assoc]

private theorem countP_fourRank_eq_rectangle (s : Multiset (ℝ × WithTop ℝ))
    (a b c d : ℝ) (_hab : a < b) (_hbc : b < c) (_hcd : c < d) :
    ((s.countP (fun p => p.1 ≤ b ∧ (c : WithTop ℝ) < p.2) : ℤ) -
      (s.countP (fun p => p.1 ≤ a ∧ (c : WithTop ℝ) < p.2) : ℤ) -
      (s.countP (fun p => p.1 ≤ b ∧ (d : WithTop ℝ) < p.2) : ℤ) +
      (s.countP (fun p => p.1 ≤ a ∧ (d : WithTop ℝ) < p.2) : ℤ)) =
    (s.countP (fun p => a < p.1 ∧ p.1 ≤ b ∧
      (c : WithTop ℝ) < p.2 ∧ p.2 ≤ (d : WithTop ℝ)) : ℤ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons p s ih =>
      simp only [Multiset.countP_cons, Nat.cast_add, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]
      have hp :
          ((if p.1 ≤ b ∧ (c : WithTop ℝ) < p.2 then (1 : ℤ) else 0) -
            (if p.1 ≤ a ∧ (c : WithTop ℝ) < p.2 then 1 else 0) -
            (if p.1 ≤ b ∧ (d : WithTop ℝ) < p.2 then 1 else 0) +
            (if p.1 ≤ a ∧ (d : WithTop ℝ) < p.2 then 1 else 0)) =
          (if a < p.1 ∧ p.1 ≤ b ∧ (c : WithTop ℝ) < p.2 ∧
              p.2 ≤ (d : WithTop ℝ) then 1 else 0) := by
        rcases p with ⟨birth, death⟩
        cases death with
        | top => simp
        | coe death =>
            by_cases h₁ : birth ≤ a
            · have h₂ : birth ≤ b := h₁.trans _hab.le
              by_cases h₃ : c < death
              · by_cases h₄ : d < death
                · have hnot : ¬ death ≤ d := not_le_of_gt h₄
                  simp [h₁, h₂, h₃, h₄, hnot]
                · have h₅ : death ≤ d := le_of_not_gt h₄
                  simp [h₁, h₂, h₃, h₄, h₅]
              · by_cases h₄ : d < death
                · exact (h₃ (_hcd.trans h₄)).elim
                · simp [h₁, h₂, h₃, h₄]
            · have h₁' : a < birth := lt_of_not_ge h₁
              by_cases h₂ : birth ≤ b
              · by_cases h₃ : c < death
                · by_cases h₄ : d < death
                  · have hnot : ¬ death ≤ d := not_le_of_gt h₄
                    simp [h₁, h₁', h₂, h₃, h₄, hnot]
                  · have h₅ : death ≤ d := le_of_not_gt h₄
                    simp [h₁, h₁', h₂, h₃, h₄, h₅]
                · by_cases h₄ : d < death
                  · exact (h₃ (_hcd.trans h₄)).elim
                  · simp [h₁, h₁', h₂, h₃, h₄]
              · simp [h₁, h₂]
      linear_combination ih + hp

private theorem diagramOccurrence_count_rectangle (D : Diagram ℝ)
    (a b c d : ℝ) (_hab : a < b) (_hbc : b < c) (_hcd : c < d) :
    (D.points.map diagramOccurrence).countP (fun p => p ∈ rectangleCell a b c d) =
      D.points.countP (fun p => a < p.1 ∧ p.1 ≤ b ∧
        (c : WithTop ℝ) < p.2 ∧ p.2 ≤ (d : WithTop ℝ)) := by
  rw [Multiset.countP_map]
  rw [← Multiset.countP_eq_card_filter]
  apply Multiset.countP_congr rfl
  intro p _
  exact propext (diagramOccurrence_mem_rectangleCell p a b c d)

include hQ hrank in
private theorem persistenceMeasure_eq_rectangleCount
    (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    persistenceMeasureValue M hab.le hbc.le hcd.le =
      (D.points.map diagramOccurrence).countP (fun p => p ∈ rectangleCell a b c d) := by
  classical
  let _ : FiniteDimensional k (persistenceImage M hbc.le) := hQ b c hbc
  have hfour := persistenceMeasureValue_four_rank M hab.le hbc.le hcd.le
  have hrBC := hrank b c hbc.le
  have hrAC := hrank a c (hab.trans hbc).le
  have hrBD := hrank b d (hbc.trans hcd).le
  have hrAD := hrank a d (hab.trans (hbc.trans hcd)).le
  rw [hrBC, hrAC, hrBD, hrAD] at hfour
  have hcounts := countP_fourRank_eq_rectangle D.points a b c d hab hbc hcd
  have hcounts' := diagramOccurrence_count_rectangle D a b c d hab hbc hcd
  rw [hcounts] at hfour
  rw [← hcounts'] at hfour
  exact_mod_cast hfour

private noncomputable def diagramFiniteDeathBound (D : Diagram ℝ) : ℝ :=
  let deaths := insert 0 (D.points.toFinset.image fun p =>
    match p.2 with | (d : ℝ) => d | ⊤ => 0)
  deaths.max' (by simp [deaths])

private theorem diagramFiniteDeath_lt_bound (D : Diagram ℝ) {p : ℝ × WithTop ℝ}
    (hp : p ∈ D.points) {d : ℝ} (hpd : p.2 = d) :
    d < diagramFiniteDeathBound D + 1 := by
  let deaths := insert 0 (D.points.toFinset.image fun q =>
    match q.2 with | (x : ℝ) => x | ⊤ => 0)
  have hmem : d ∈ deaths := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨p, Multiset.mem_toFinset.mpr hp, ?_⟩
    rw [hpd]
  have hle' : d ≤ deaths.max' ⟨d, hmem⟩ := Finset.le_max' deaths d hmem
  have hle : d ≤ deaths.max' ⟨0, Finset.mem_insert_self 0 _⟩ := by
    convert hle'
  have hEq : deaths.max' ⟨0, Finset.mem_insert_self 0 _⟩ = diagramFiniteDeathBound D := by
    simp [diagramFiniteDeathBound, deaths]
  rw [hEq] at hle
  linarith

private theorem countP_tail_split_aux (points : Multiset (ℝ × WithTop ℝ))
    {a b C : ℝ} (hab : a ≤ b)
    (hfinite : ∀ p ∈ points, ∀ d : ℝ, p.2 = d → d < C) :
    points.countP (fun p => p.1 ≤ b ∧ (C : WithTop ℝ) < p.2) =
      points.countP (fun p => p.1 ≤ a ∧ (C : WithTop ℝ) < p.2) +
        points.countP (fun p => a < p.1 ∧ p.1 ≤ b ∧ p.2 = ⊤) := by
  classical
  induction points using Multiset.induction_on with
  | empty => simp
  | @cons p points ih =>
      simp only [Multiset.countP_cons]
      have hp :
          (if p.1 ≤ b ∧ (C : WithTop ℝ) < p.2 then 1 else 0) =
            (if p.1 ≤ a ∧ (C : WithTop ℝ) < p.2 then 1 else 0) +
              (if a < p.1 ∧ p.1 ≤ b ∧ p.2 = ⊤ then 1 else 0) := by
        rcases p with ⟨birth, death⟩
        cases death with
        | top =>
            simp only [WithTop.coe_lt_top, and_true]
            by_cases hA : birth ≤ a
            · have hB : birth ≤ b := hA.trans hab
              simp [hA, hB]
            · have hA' : a < birth := lt_of_not_ge hA
              by_cases hB : birth ≤ b
              · simp [hA, hA', hB]
              · simp [hA, hA', hB]
        | coe d =>
            have hdC : d < C := hfinite (birth, d) (by simp) d rfl
            have hCnot : ¬ C < (d : WithTop ℝ) := by exact not_lt_of_ge (show (d : WithTop ℝ) ≤ C from WithTop.coe_le_coe.mpr hdC.le)
            simp [hCnot]
      have hfiniteTail : ∀ q ∈ points, ∀ d : ℝ, q.2 = d → d < C := by
        intro q hq d hqd
        exact hfinite q (by simp [hq]) d hqd
      rw [hp, ih hfiniteTail]
      omega

private theorem countP_tail_split (D : Diagram ℝ) {a b C : ℝ} (hab : a ≤ b)
    (hfinite : ∀ p ∈ D.points, ∀ d : ℝ, p.2 = d → d < C) :
    D.points.countP (fun p => p.1 ≤ b ∧ (C : WithTop ℝ) < p.2) =
      D.points.countP (fun p => p.1 ≤ a ∧ (C : WithTop ℝ) < p.2) +
        D.points.countP (fun p => a < p.1 ∧ p.1 ≤ b ∧ p.2 = ⊤) :=
  countP_tail_split_aux D.points hab hfinite

include hQ hrank in
private theorem essentialMeasureValue_eq_essentialBirthCount {a b : ℝ} (hab : a ≤ b) :
    essentialMeasureValue M hab =
      D.points.countP (fun p => a < p.1 ∧ p.1 ≤ b ∧ p.2 = ⊤) := by
  classical
  obtain ⟨c₀, hbc₀, hstable⟩ := PModule.QTame.essentialMeasureValue_eventually M hQ hab
  let C := max c₀ (max (b + 1) (diagramFiniteDeathBound D + 1))
  have h₀C : c₀ ≤ C := le_max_left _ _
  have hbC : b < C := by
    dsimp [C]
    exact (lt_add_one b).trans_le
      ((le_max_left _ _).trans (le_max_right _ _))
  have hbcC : b < C := hbC
  have htail :
      persistenceTailMeasureValue M hab hbcC.le = essentialMeasureValue M hab := by
    exact hstable C h₀C
  let _ : FiniteDimensional k (persistenceImage M hbcC.le) := hQ b C hbcC
  have htailRank := persistenceTailMeasureValue_add_image M hab hbcC.le
  have hrankBC := hrank b C hbcC.le
  have hrankAC := hrank a C (hab.trans hbcC.le)
  have hfinite : ∀ p ∈ D.points, ∀ d : ℝ, p.2 = d → d < C := by
    intro p hp d hpd
    have hbound := diagramFiniteDeath_lt_bound D hp hpd
    dsimp [C]
    exact lt_of_lt_of_le hbound
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hsplit := countP_tail_split D hab hfinite
  have hEq := htailRank
  rw [hrankBC, hrankAC, hsplit] at hEq
  rw [htail] at hEq
  simpa using (by omega : essentialMeasureValue M hab =
    D.points.countP (fun p => a < p.1 ∧ p.1 ≤ b ∧ p.2 = ⊤))

private noncomputable def diagramEssentialBirths (D : Diagram ℝ) : Multiset (Cut ℝ) :=
  (D.points.filter (fun p => p.2 = ⊤)).map (fun p => minusCut p.1)

private theorem diagramEssentialBirths_count_cell (D : Diagram ℝ) (a b : ℝ) :
    (diagramEssentialBirths D).countP (fun birth => birth ∈ cutCell a b) =
      D.points.countP (fun p => a < p.1 ∧ p.1 ≤ b ∧ p.2 = ⊤) := by
  classical
  rw [diagramEssentialBirths, Multiset.countP_map]
  rw [← Multiset.countP_eq_card_filter]
  rw [Multiset.countP_filter]
  apply Multiset.countP_congr rfl
  intro p _
  apply propext
  simp [cutCell, minusCut, and_assoc]

include hQ hrank in
private theorem rectangleContent_eq_count
    (a b c d : ℝ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    moduleRectangleContent
      M hQ (rectangleCell a b c d) =
    ((D.points.map diagramOccurrence).filter
      (· ∈ rectangleCell a b c d)).card := by
  classical
  rw [moduleRectangleContent_apply _ _ a b c d hab hbc hcd]
  rw [persistenceMeasure_eq_rectangleCount M hQ D hrank a b c d hab hbc hcd]
  rw [Multiset.countP_eq_card_filter]

private theorem count_decEq_irrel {α : Type*} (a : α) (s : Multiset α)
    [DecidableEq α] :
    @Multiset.count α (Classical.decEq α) a s = Multiset.count a s := by
  have hdec : Classical.decEq α = (inferInstance : DecidableEq α) := Subsingleton.elim _ _
  rw [hdec]

include hQ hrank in
private theorem essentialCutContent_eq_count
    (a b : ℝ) (hab : a ≤ b) :
    essentialCutContent
      M hQ
      (cutCell a b) = (diagramEssentialBirths D).countP
        (fun birth => birth ∈ cutCell a b) := by
  rw [essentialCutContent_apply _ _ hab]
  rw [essentialMeasureValue_eq_essentialBirthCount M hQ D hrank hab]
  exact (diagramEssentialBirths_count_cell D a b).symm

include hQ hrank hD in
private theorem moduleDiagramMultiplicity_eq_occurrenceCount
    (p : Cut ℝ × Cut ℝ)
    (hpInf : p.2 ≠ infinityCut) :
    moduleDiagramMultiplicity
        M hQ p =
      (D.points.map diagramOccurrence).count p := by
  classical
  let points := D.points.map diagramOccurrence
  by_cases hVis : ∃ U ∈ separatedRectangleCells, p ∈ U
  · obtain ⟨K, hK, hpK⟩ := hVis
    rcases hK with rfl | ⟨a, b, c, d, hab, hbc, hcd, rfl⟩
    · exact hpK.elim
    · change contentMultiplicity (moduleRectangleContent M hQ) p = points.count p
      have hrepr : ∀ U ∈ separatedRectangleCells, U ⊆ rectangleCell a b c d →
          moduleRectangleContent M hQ U = (points.filter (· ∈ U)).card := by
        intro U hU hUK
        rcases hU with rfl | ⟨a', b', c', d', ha'b', hb'c', hc'd', rfl⟩
        · simp
        · exact rectangleContent_eq_count M hQ D hrank a' b' c' d'
            ha'b' hb'c' hc'd'
      have hcount := contentMultiplicity_eq_count isSetSemiring_separatedRectangleCells
        (fun q hpq => exists_rectangleCell_separating hpq hbc hpK)
        (moduleRectangleContent M hQ) (rectangleCell_mem_separatedRectangleCells a b c d hbc)
        points hrepr hpK
      exact hcount.trans (count_decEq_irrel p points)
  · have hzero := moduleDiagramMultiplicity_eq_zero_of_not_visible M hQ p hVis
    rw [hzero]
    apply Eq.symm
    apply Multiset.count_eq_zero.mpr
    intro hp
    obtain ⟨q, hq, hqp⟩ := Multiset.mem_map.mp hp
    rcases q with ⟨birth, death⟩
    cases death with
    | top =>
        have htop : p.2 = infinityCut := by
          rw [← hqp]
          simp [diagramOccurrence]
        exact hpInf htop
    | coe d =>
        have hbirth : birth < d :=
          WithTop.coe_lt_coe.mp (hD (birth, (d : WithTop ℝ)) hq)
        let c := (birth + d) / 2
        have hmidlow : (birth + d) / 2 < d := by linarith
        have hmidhigh : d ≤ d + 1 := by linarith
        have hcell : diagramOccurrence (birth, (d : WithTop ℝ)) ∈
            rectangleCell (birth - 1) birth c (d + 1) := by
          apply (diagramOccurrence_mem_rectangleCell
            (birth, (d : WithTop ℝ)) (birth - 1) birth c (d + 1)).2
          exact ⟨by linarith, le_rfl, WithTop.coe_lt_coe.mpr (by simpa [c] using hmidlow),
            WithTop.coe_le_coe.mpr hmidhigh⟩
        have hpCell := hqp ▸ hcell
        have hsep := rectangleCell_mem_separatedRectangleCells
          (birth - 1) birth c (d + 1) (by dsimp [c]; linarith)
        exact hVis ⟨_, hsep, hpCell⟩

include hQ hrank in
private theorem moduleEssentialMultiplicity_eq_birthCount
    (birth : Cut ℝ) :
    moduleEssentialMultiplicity
        M hQ birth =
      (diagramEssentialBirths D).count birth := by
  classical
  let points := diagramEssentialBirths D
  by_cases hVis : ∃ U ∈ cutCells, birth ∈ U
  · obtain ⟨K, hK, hbK⟩ := hVis
    obtain ⟨a, b, hab, rfl⟩ := hK
    change contentMultiplicity (essentialCutContent M hQ) birth = points.count birth
    refine contentMultiplicity_eq_count isSetSemiring_cutCells
      (fun y hby => by
        obtain ⟨a', b', _, _, hb', hy'⟩ := exists_subcell_separating_cuts hby hbK
        exact ⟨cutCell a' b', cutCell_mem_cutCells a' b', hb', hy'⟩)
      (essentialCutContent M hQ) (cutCell_mem_cutCells a b) points ?_ hbK
    intro U hU hUK
    obtain ⟨a', b', hab', rfl⟩ := hU
    rw [essentialCutContent_eq_count M hQ D hrank a' b' hab']
    rw [Multiset.countP_eq_card_filter]
  ·
    have hzero' : moduleEssentialMultiplicity M hQ birth = 0 := by
      by_contra hn
      have hpos : 0 < moduleEssentialMultiplicity M hQ birth := Nat.pos_of_ne_zero hn
      obtain ⟨U, hU, hbU⟩ := moduleEssentialMultiplicity_visible_of_pos M hQ hpos
      exact hVis ⟨U, hU, hbU⟩
    rw [hzero']
    apply Eq.symm
    apply Multiset.count_eq_zero.mpr
    intro hb
    obtain ⟨q, hq, hqBirth⟩ := Multiset.mem_map.mp hb
    rcases q with ⟨x, death⟩
    have hbirthEq : minusCut x = birth := hqBirth
    have hxCell : minusCut x ∈ cutCell (x - 1) x := by
      simp [cutCell, minusCut]
    exact hVis ⟨cutCell (x - 1) x, cutCell_mem_cutCells _ _, by
      rw [← hbirthEq]
      exact hxCell⟩

private theorem diagramOccurrence_infinity_count (D : Diagram ℝ) (birth : Cut ℝ) :
    (D.points.map diagramOccurrence).count (birth, infinityCut) =
      (diagramEssentialBirths D).count birth := by
  classical
  rw [Multiset.count_map, diagramEssentialBirths, Multiset.count_map]
  rw [Multiset.filter_filter]
  congr 1
  apply Multiset.filter_congr
  intro p _
  rcases p with ⟨x, death⟩
  cases death with
  | top =>
      simp [diagramOccurrence, and_comm]
  | coe d =>
      simp [diagramOccurrence]
      intro _ hEq
      have hdTop : d ∈ infinityCut.lower := by simp
      rw [hEq] at hdTop
      simp [minusCut] at hdTop

include hrank hD in
/-- A positive finite diagram with the module's rank semantics records every canonical
multiplicity, including essential occurrences. -/
theorem moduleExtendedDiagramMultiplicity_eq_count (p : Cut ℝ × Cut ℝ) :
    moduleExtendedDiagramMultiplicity M hQ p =
      (D.points.map diagramOccurrence).count p := by
  classical
  by_cases hInf : p.2 = infinityCut
  · have hess := moduleEssentialMultiplicity_eq_birthCount M hQ D hrank p.1
    have hmap := diagramOccurrence_infinity_count D p.1
    have hpEq : p = (p.1, infinityCut) := Prod.ext rfl hInf
    simp only [moduleExtendedDiagramMultiplicity, if_pos hInf]
    rw [hess]
    rw [hpEq.symm] at hmap
    simpa only [count_decEq_irrel] using hmap.symm
  · simp only [moduleExtendedDiagramMultiplicity, if_neg hInf]
    exact moduleDiagramMultiplicity_eq_occurrenceCount M hQ D hrank hD p hInf


include hrank in
/-- The canonical diagram agrees with the finite diagram embedding on every occurrence. -/
theorem ofQModule_eq_toLocallyFinite :
    LocallyFiniteDecoratedDiagram.ofQModule hQ = D.toLocallyFinite hD := by
  apply LocallyFiniteDecoratedDiagram.ext
  funext p
  simpa only [LocallyFiniteDecoratedDiagram.ofQModule, Diagram.toLocallyFinite,
    diagramOccurrence, count_decEq_irrel] using
    moduleExtendedDiagramMultiplicity_eq_count M hQ D hrank hD p

end TDA.Persistence.FiniteDiagramQTame
