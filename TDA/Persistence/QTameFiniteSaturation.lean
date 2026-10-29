import TDA.Persistence.RealInterleavingInterpolation
import TDA.Persistence.LocallyFiniteDiagramBottleneck
import TDA.Persistence.PersistenceMeasureWindowMatching
import TDA.Persistence.PersistenceMeasureBox
import TDA.Persistence.PersistenceMeasureEssentialBox

/-!
# Finite saturation for q-tame interleavings

The finite-window lemmas in this module support the passage from an actual
interleaving of q-tame modules to finite occurrence matchings.  The infinite
matching and metric-stability consequences are stated separately from these
finite constructions.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence

open RectangleMeasure
open scoped NNReal Classical

noncomputable section

private def finiteWindowPoint (R h : ℝ) (p : ℝ × ℝ) : Prop :=
  |p.1| < R ∧ |p.2| < R ∧ h < p.2 - p.1

private def finiteWindowTokens (D : LocallyFiniteDecoratedDiagram) (R h : ℝ) :=
  {o : D.finiteOccurrences // finiteWindowPoint R h (D.finitePoint o)}

private def finiteWindowPointMap (D : LocallyFiniteDecoratedDiagram) (R h : ℝ)
    (o : finiteWindowTokens D R h) : ℝ × ℝ :=
  D.finitePoint o.1

private def finiteWindowExit (R h : ℝ) (p : ℝ × ℝ) : ℝ :=
  min (R - |p.1|) (min (R - |p.2|) ((p.2 - p.1 - h) / 2))

private def finiteWindowCompact (R h : ℝ) : Set (ℝ × ℝ) :=
  (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) ∩ {p | h ≤ p.2 - p.1}

private def finiteWindowNeighborhood (h : ℝ) (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo (p.1 - h / 4) (p.1 + h / 4) ×ˢ Set.Ioo (p.2 - h / 4) (p.2 + h / 4)

private theorem exists_small_radius_of_finite {ι : Type*} [Fintype ι]
    (y : ι → ℝ × ℝ) (p : ℝ × ℝ) (r ρ : ℝ) (hρ : 0 < ρ) :
    ∃ t, 0 < t ∧ t < ρ ∧ ∀ i, dist (y i) p ≤ r + t → dist (y i) p ≤ r := by
  classical
  have aux : ∀ s : Finset ι, ∃ t, 0 < t ∧ t < ρ ∧
      ∀ i ∈ s, dist (y i) p ≤ r + t → dist (y i) p ≤ r := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨ρ / 2, by positivity, by linarith, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨t, ht, htρ, hts⟩ := ih
      by_cases hd : dist (y i) p ≤ r
      · refine ⟨t, ht, htρ, ?_⟩
        intro j hj hjr
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hd
        · exact hts j hj hjr
      · have hd' : r < dist (y i) p := lt_of_not_ge hd
        refine ⟨min t ((dist (y i) p - r) / 2), lt_min ht (by linarith),
          lt_of_le_of_lt (min_le_left _ _) htρ, ?_⟩
        intro j hj hjr
        rcases Finset.mem_insert.mp hj with rfl | hj
        · have := min_le_right t ((dist (y j) p - r) / 2)
          linarith
        · exact hts j hj (hjr.trans (add_le_add le_rfl (min_le_left _ _)))
  obtain ⟨t, ht, htρ, hts⟩ := aux Finset.univ
  exact ⟨t, ht, htρ, fun i => hts i (Finset.mem_univ _)⟩

private theorem pointBall_card_eq_subtype {ι : Type*} [Fintype ι]
    (x : ι → ℝ × ℝ) (p : ℝ × ℝ) (r : ℝ) :
    (PersistenceMeasureWindowMatching.pointBall x p r).card =
      Fintype.card {i : ι // dist (x i) p ≤ r} := by
  classical
  simp [PersistenceMeasureWindowMatching.pointBall, Fintype.card_subtype]

private theorem cut_mem_cell_of_endpoint_inside {c : Cut ℝ} {a b : ℝ}
    (hc : ∃ x y, c ∈ cutCell x y) (ha : a < cutEndpoint c) (hb : cutEndpoint c < b) :
    c ∈ cutCell a b := by
  obtain ⟨x, y, hcell⟩ := hc
  rcases cut_eq_minus_or_plus_of_mem_cutCell hcell with hminus | hplus
  · rw [hminus]
    change a ∈ (minusCut (cutEndpoint c)).lower ∧ b ∈ (minusCut (cutEndpoint c)).upper
    exact ⟨by simpa [minusCut] using ha, by simpa [minusCut] using hb.le⟩
  · rw [hplus]
    change a ∈ (plusCut (cutEndpoint c)).lower ∧ b ∈ (plusCut (cutEndpoint c)).upper
    exact ⟨by simpa [plusCut] using ha.le, by simpa [plusCut] using hb⟩

/-- Every bounded off-diagonal finite occurrence window of a locally finite
decorated diagram is finite.  Compactness of the closed numeric region and a finite
cover by separated rectangles reduce this to the defining rectangle local-finiteness
property. -/
private theorem finiteWindowTokens_finite
    (D : LocallyFiniteDecoratedDiagram) {R h : ℝ} (hR : 0 < R) (hh : 0 < h) :
    Finite (finiteWindowTokens D R h) := by
  classical
  let K := finiteWindowCompact R h
  have hbox : IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  have hclosed : IsClosed {p : ℝ × ℝ | h ≤ p.2 - p.1} :=
    isClosed_le continuous_const (continuous_snd.sub continuous_fst)
  have hK : IsCompact K := by
    exact hbox.inter_right hclosed
  let V : K → Set (ℝ × ℝ) := fun p => finiteWindowNeighborhood h p.1
  have hVo : ∀ p, IsOpen (V p) := by
    intro p
    exact isOpen_Ioo.prod isOpen_Ioo
  have hcover : K ⊆ ⋃ p : K, V p := by
    intro q hq
    let p : K := ⟨q, hq⟩
    refine Set.mem_iUnion.mpr ⟨p, ?_⟩
    change q ∈ finiteWindowNeighborhood h q
    change q.1 ∈ Set.Ioo (q.1 - h / 4) (q.1 + h / 4) ∧
      q.2 ∈ Set.Ioo (q.2 - h / 4) (q.2 + h / 4)
    simp only [Set.mem_Ioo]
    constructor <;> constructor <;> linarith
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover V hVo hcover
  let T : K → Set (Cut ℝ × Cut ℝ) := fun z =>
    {p | p ∈ rectangleCell (z.1.1 - h / 4) (z.1.1 + h / 4)
        (z.1.2 - h / 4) (z.1.2 + h / 4) ∧ 0 < D.multiplicity p}
  have hT : ∀ z, (T z).Finite := by
    intro z
    have hz : h ≤ z.1.2 - z.1.1 := z.2.2
    have hab : z.1.1 - h / 4 < z.1.1 + h / 4 := by linarith
    have hbc : z.1.1 + h / 4 < z.1.2 - h / 4 := by linarith
    have hcd : z.1.2 - h / 4 < z.1.2 + h / 4 := by linarith
    exact D.locallyFiniteRectangle _ _ _ _ hab hbc hcd
  let U : Finset (Cut ℝ × Cut ℝ) := S.biUnion fun z => (hT z).toFinset
  have hwindowSupport : ∀ o : D.finiteOccurrences,
      finiteWindowPoint R h (D.finitePoint o) → o.1.1 ∈ U := by
    intro o ho
    let q : ℝ × ℝ := D.finitePoint o
    let z : ℝ × ℝ := (cutEndpoint o.1.1.1, cutEndpoint o.1.1.2)
    rcases ho with ⟨hb, hd, hlen⟩
    have hb' : |cutEndpoint o.1.1.1| < R := by
      simpa [LocallyFiniteDecoratedDiagram.finitePoint] using hb
    have hd' : |cutEndpoint o.1.1.2| < R := by
      simpa [LocallyFiniteDecoratedDiagram.finitePoint] using hd
    have hlen' : h < cutEndpoint o.1.1.2 - cutEndpoint o.1.1.1 := by
      simpa [LocallyFiniteDecoratedDiagram.finitePoint] using hlen
    have hzK : z ∈ K := by
      change (z.1 ∈ Set.Icc (-R) R ∧ z.2 ∈ Set.Icc (-R) R) ∧ h ≤ z.2 - z.1
      rcases abs_lt.mp hb' with ⟨hbL, hbR⟩
      rcases abs_lt.mp hd' with ⟨hdL, hdR⟩
      exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, hlen'.le⟩
    have hmemV : q ∈ ⋃ z' ∈ S, V z' := hS (by simpa [z, q, LocallyFiniteDecoratedDiagram.finitePoint] using hzK)
    obtain ⟨z', hz'S, hqV⟩ := Set.mem_iUnion₂.mp hmemV
    have hqV' : q.1 ∈ Set.Ioo (z'.1.1 - h / 4) (z'.1.1 + h / 4) ∧
        q.2 ∈ Set.Ioo (z'.1.2 - h / 4) (z'.1.2 + h / 4) := by
      simpa [V, finiteWindowNeighborhood] using hqV
    have hcoord1 : z'.1.1 - h / 4 < cutEndpoint o.1.1.1 ∧
        cutEndpoint o.1.1.1 < z'.1.1 + h / 4 := by
      simpa [q, LocallyFiniteDecoratedDiagram.finitePoint] using hqV'.1
    have hcoord2 : z'.1.2 - h / 4 < cutEndpoint o.1.1.2 ∧
        cutEndpoint o.1.1.2 < z'.1.2 + h / 4 := by
      simpa [q, LocallyFiniteDecoratedDiagram.finitePoint] using hqV'.2
    have hfin : o.1.1.2 ≠ infinityCut := o.1.2.2
    have hpos : 0 < D.multiplicity o.1.1 := o.1.2.1
    have hend := D.finiteEndpoints o.1.1 hpos hfin
    have hcell1 := cut_mem_cell_of_endpoint_inside hend.1 hcoord1.1 hcoord1.2
    have hcell2 := cut_mem_cell_of_endpoint_inside hend.2 hcoord2.1 hcoord2.2
    have hpT : o.1.1 ∈ T z' := by
      exact ⟨⟨hcell1, hcell2⟩, hpos⟩
    have hpU : o.1.1 ∈ U := by
      apply Finset.mem_biUnion.mpr
      exact ⟨z', hz'S, (hT z').mem_toFinset.mpr hpT⟩
    exact hpU
  let P := {p : Cut ℝ × Cut ℝ // p ∈ U ∧ 0 < D.multiplicity p ∧ p.2 ≠ infinityCut}
  letI : Fintype {p : Cut ℝ × Cut ℝ // p ∈ U} := inferInstance
  have hPfinite : Finite P := Finite.of_injective
    (fun p : P => (⟨p.1, p.2.1⟩ : {p : Cut ℝ × Cut ℝ // p ∈ U})) (by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : {p : Cut ℝ × Cut ℝ // p ∈ U} => z.1) hab))
  letI : Finite P := hPfinite
  letI : Fintype P := Fintype.ofFinite P
  let V : Type := Σ p : P, Fin (D.multiplicity p.1)
  letI : Fintype V := inferInstance
  let emb : finiteWindowTokens D R h → V := fun o =>
    ⟨⟨o.1.1.1, ⟨hwindowSupport o.1 o.2, o.1.1.2.1, o.1.1.2.2⟩⟩, o.1.2⟩
  have hemb : Function.Injective emb := by
    intro a b hab
    apply Subtype.ext
    have h := Sigma.ext_iff.mp hab
    apply Sigma.ext
    · apply Subtype.ext
      exact congrArg (fun z : V => z.1.1) hab
    · exact h.2
  exact Finite.of_injective emb hemb

private def essentialWindowTokens (D : LocallyFiniteDecoratedDiagram) (R : ℝ) :=
  {o : D.essentialOccurrences // |cutEndpoint o.1.1| < R}

private def essentialWindowBirthMap (D : LocallyFiniteDecoratedDiagram) (R : ℝ)
    (o : essentialWindowTokens D R) : ℝ :=
  cutEndpoint o.1.1

private theorem essentialWindowTokens_finite
    {k : Type u} [Field k] {M : PModule.{u,0,w} k ℝ} (hM : M.QTame)
    {R : ℝ} (hR : 0 < R) :
    Finite (essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R) := by
  classical
  let D := LocallyFiniteDecoratedDiagram.ofQModule hM
  let a := -R - 1
  let b := R + 1
  have hab : a ≤ b := by dsimp [a, b]; linarith
  obtain ⟨S, hS, _⟩ := moduleExtendedDiagramMultiplicity_essential_counts M hM hab
  let P : Type := {birth : Cut ℝ // birth ∈ S}
  letI : Fintype P := by
    dsimp [P]
    exact Fintype.ofFinset S (by simp)
  let V : Type := Σ birth : P, Fin (D.multiplicity (birth.1, infinityCut))
  letI : Fintype V := inferInstance
  let emb : essentialWindowTokens D R → V := fun o => by
    let birth := o.1.1.1
    have hpos : 0 < D.multiplicity (birth, infinityCut) := o.1.1.2
    have hcell' : birth ∈ cutCell a b :=
      cut_mem_cell_of_endpoint_inside (D.essentialBirthEndpoint birth hpos)
        (by dsimp [a]; have := abs_lt.mp o.2; linarith)
        (by dsimp [b]; have := abs_lt.mp o.2; linarith)
    exact ⟨⟨birth, (hS birth).mpr ⟨hcell', hpos⟩⟩, o.1.2⟩
  have hemb : Function.Injective emb := by
    intro x y hxy
    rcases x with ⟨⟨⟨birth, hbirth⟩, idx⟩, hxwin⟩
    rcases y with ⟨⟨⟨birth', hbirth'⟩, idx'⟩, hywin⟩
    have hb : birth = birth' := by
      have h := congrArg (fun z : V => z.1.1) hxy
      simpa [emb] using h
    subst birth'
    have hi : (idx : ℕ) = idx' := by
      have h := congrArg (fun z : V => (z.2 : ℕ)) hxy
      simpa [emb] using h
    have hi' : idx = idx' := Fin.ext hi
    subst idx'
    rfl
  exact Finite.of_injective emb hemb

private def essentialWindowIntervalTokens (D : LocallyFiniteDecoratedDiagram)
    (R a b : ℝ) :=
  {o : essentialWindowTokens D R // o.1.1.1 ∈ cutCell a b}

/-- Essential tokens in a finite numeric birth interval count the actual essential
quotient measure. The interval is contained in the fixed finite birth window, and
the decorated cut cell retains both endpoint conventions. -/
private theorem essentialWindowIntervalTokens_card_eq_measure
    {k : Type u} [Field k] {M : PModule.{u,0,w} k ℝ} (hM : M.QTame)
    {R a b : ℝ} (ha : -R < a) (hb : b < R) (hab : a ≤ b)
    [FW : Fintype (essentialWindowTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R)]
    (FB : Fintype (essentialWindowIntervalTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R a b)) :
    @Fintype.card (essentialWindowIntervalTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R a b) FB =
      essentialMeasureValue M hab := by
  classical
  let D : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hM
  let I := essentialWindowTokens D R
  letI : Fintype I := FW
  obtain ⟨S, hS, hcount⟩ := moduleExtendedDiagramMultiplicity_essential_counts M hM hab
  let P : Type := {birth : Cut ℝ // birth ∈ S}
  let T : Type := Σ birth : P, Fin (D.multiplicity (birth.1, infinityCut))
  let B := essentialWindowIntervalTokens D R a b
  letI : Fintype B := FB
  letI : Fintype P := by
    dsimp [P]
    exact Fintype.ofFinset S (by simp)
  letI : Fintype T := inferInstance
  let e : B ≃ T := {
    toFun := fun o => by
      let birth := o.1.1.1.1
      have hpos : 0 < D.multiplicity (birth, infinityCut) := o.1.1.1.2
      exact ⟨⟨birth, (hS birth).mpr ⟨o.2, hpos⟩⟩, o.1.1.2⟩
    invFun := fun z => by
      let birth := z.1.1
      have hmem := (hS birth).mp z.1.2
      have hpos : 0 < D.multiplicity (birth, infinityCut) := hmem.2
      let o : D.essentialOccurrences := ⟨⟨birth, hpos⟩, z.2⟩
      have hbounds := cutEndpoint_bounds hmem.1
      have hwindow : |cutEndpoint birth| < R := by
        rw [abs_lt]
        constructor <;> linarith
      exact ⟨⟨o, hwindow⟩, hmem.1⟩
    left_inv := by
      intro o
      apply Subtype.ext
      apply Subtype.ext
      apply Sigma.ext
      · apply Subtype.ext
        rfl
      · rfl
    right_inv := by
      intro z
      apply Sigma.ext
      · apply Subtype.ext
        rfl
      · rfl
  }
  calc
    @Fintype.card B FB = Fintype.card T := Fintype.card_congr e
    _ = ∑ birth ∈ S, D.multiplicity (birth, infinityCut) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      change (∑ birth : P, D.multiplicity (birth.1, infinityCut)) = _
      exact (Finset.sum_subtype (s := S) (p := fun birth => birth ∈ S)
        (by intro birth; rfl) (fun birth => D.multiplicity (birth, infinityCut))).symm
    _ = essentialMeasureValue M hab := by
      simpa [D, LocallyFiniteDecoratedDiagram.ofQModule] using hcount.symm

private def essentialWindowPointPairMap (D : LocallyFiniteDecoratedDiagram) (R : ℝ)
    (o : essentialWindowTokens D R) : ℝ × ℝ :=
  (essentialWindowBirthMap D R o, essentialWindowBirthMap D R o)

private def essentialWindowExit (R : ℝ) (p : ℝ × ℝ) : ℝ := R - |p.1|

private theorem essentialPair_dist_eq_abs (x y : ℝ) :
    dist (x, x) (y, y) = |x - y| := by
  simp [Prod.dist_eq, Real.dist_eq]

private theorem essentialWindow_ball_to_interval
    (D : LocallyFiniteDecoratedDiagram) {R a b : ℝ}
    [FW : Fintype (essentialWindowTokens D R)]
    (center r : ℝ) (ha : a < center - r) (hb : center + r < b)
    (FB : Fintype (essentialWindowIntervalTokens D R a b)) :
    (PersistenceMeasureWindowMatching.pointBall
      (essentialWindowPointPairMap D R) (center, center) r).card ≤
      Fintype.card (essentialWindowIntervalTokens D R a b) := by
  classical
  let I := essentialWindowTokens D R
  let B := essentialWindowIntervalTokens D R a b
  letI : Fintype I := FW
  letI : Fintype B := FB
  let A := {o : I // dist (essentialWindowPointPairMap D R o) (center, center) ≤ r}
  let f : A → B := fun o => by
    have hdist : |essentialWindowBirthMap D R o.1 - center| ≤ r := by
      simpa [essentialWindowPointPairMap, essentialPair_dist_eq_abs] using o.2
    have hcell0 := D.essentialBirthEndpoint o.1.1.1.1 o.1.1.1.2
    have hdist' : |cutEndpoint o.1.1.1.1 - center| ≤ r := by
      simpa [essentialWindowBirthMap] using hdist
    have hcoords := abs_le.mp hdist'
    have hcell : o.1.1.1.1 ∈ cutCell a b :=
      cut_mem_cell_of_endpoint_inside hcell0
        (by linarith [ha, hcoords.1])
        (by linarith [hb, hcoords.2])
    exact ⟨o.1, hcell⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hv := congrArg (fun z : B => z.1) hxy
    simpa [f] using hv
  have hcard : Fintype.card A =
      (PersistenceMeasureWindowMatching.pointBall
        (essentialWindowPointPairMap D R) (center, center) r).card :=
    (pointBall_card_eq_subtype _ _ _).symm
  rw [← hcard]
  exact Fintype.card_le_of_injective f hf

private theorem essentialWindow_interval_to_ball
    (D : LocallyFiniteDecoratedDiagram) {R : ℝ}
    [FW : Fintype (essentialWindowTokens D R)]
    (center s ρ τ : ℝ) (hτ : τ < ρ)
    (hsmall : ∀ o : essentialWindowIntervalTokens D R
        (center - (s + ρ)) (center + (s + ρ)),
      dist (essentialWindowPointPairMap D R o.1) (center, center) ≤ s + τ →
        dist (essentialWindowPointPairMap D R o.1) (center, center) ≤ s)
    (FB : Fintype (essentialWindowIntervalTokens D R
      (center - (s + τ)) (center + (s + τ)))) :
    Fintype.card (essentialWindowIntervalTokens D R
      (center - (s + τ)) (center + (s + τ))) ≤
      (PersistenceMeasureWindowMatching.pointBall
        (essentialWindowPointPairMap D R) (center, center) s).card := by
  classical
  let I := essentialWindowTokens D R
  let O := essentialWindowIntervalTokens D R
      (center - (s + ρ)) (center + (s + ρ))
  let B := essentialWindowIntervalTokens D R
      (center - (s + τ)) (center + (s + τ))
  let A := {o : I // dist (essentialWindowPointPairMap D R o) (center, center) ≤ s}
  letI : Fintype I := FW
  letI : Fintype B := FB
  let f : B → A := fun o => by
    have hinner := o.2
    change center - (s + τ) ∈ o.1.1.1.1.lower ∧
      center + (s + τ) ∈ o.1.1.1.1.upper at hinner
    have houter : o.1.1.1.1 ∈ cutCell (center - (s + ρ)) (center + (s + ρ)) := by
      exact ⟨Cut.lower_of_le (by linarith) hinner.1,
        Cut.upper_of_le (by linarith) hinner.2⟩
    have hbounds := cutEndpoint_bounds hinner
    have hclose : dist (essentialWindowPointPairMap D R o.1) (center, center) ≤ s + τ := by
      have hnum : |essentialWindowBirthMap D R o.1 - center| ≤ s + τ := by
        change |cutEndpoint o.1.1.1.1 - center| ≤ s + τ
        rw [abs_le]
        constructor <;> linarith
      simpa [essentialWindowPointPairMap, essentialPair_dist_eq_abs] using hnum
    let outerToken : O := ⟨o.1, houter⟩
    exact ⟨o.1, hsmall outerToken hclose⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : A => z.1) hxy
  have hcard : Fintype.card A =
      (PersistenceMeasureWindowMatching.pointBall
        (essentialWindowPointPairMap D R) (center, center) s).card :=
    (pointBall_card_eq_subtype _ _ _).symm
  rw [← hcard]
  exact Fintype.card_le_of_injective f hf

/-- An actual q-tame interleaving compares the exact closed birth balls in a finite
essential window.  The essential boundary box inequality first compares slightly
expanded intervals; finite support lets us shrink the target interval back to the
closed ball without a shell error. -/
private theorem essentialWindow_interleaving_ball_count
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) (hN : N.QTame) (i : RealInterleaving ε M N)
    {R : ℝ} (hR : 0 < R)
    [FM : Fintype (essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R)]
    [FN : Fintype (essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R)]
    (center r : ℝ) (hr : 0 ≤ r)
    (hmarg : r + (ε : ℝ) < essentialWindowExit R (center, center)) :
    (PersistenceMeasureWindowMatching.pointBall
      (essentialWindowPointPairMap
        (LocallyFiniteDecoratedDiagram.ofQModule hM) R) (center, center) r).card ≤
    (PersistenceMeasureWindowMatching.pointBall
      (essentialWindowPointPairMap
        (LocallyFiniteDecoratedDiagram.ofQModule hN) R) (center, center)
      (r + (ε : ℝ))).card := by
  classical
  let Dₘ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hM
  let Dₙ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hN
  letI : Fintype (essentialWindowTokens Dₘ R) := FM
  letI : Fintype (essentialWindowTokens Dₙ R) := FN
  let δ : ℝ := (ε : ℝ)
  let s : ℝ := r + δ
  have hδ : 0 ≤ δ := ε.coe_nonneg
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hslack : 0 < essentialWindowExit R (center, center) - s := by
    dsimp [s, δ]
    linarith
  let ρ : ℝ := (essentialWindowExit R (center, center) - s) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsρ : s + ρ < essentialWindowExit R (center, center) := by
    dsimp [ρ]
    linarith
  let O := essentialWindowIntervalTokens Dₙ R
    (center - (s + ρ)) (center + (s + ρ))
  letI : Finite O := Finite.of_injective (fun o : O => o.1) Subtype.val_injective
  letI : Fintype O := Fintype.ofFinite O
  obtain ⟨τ, hτ0, hτρ, hsmall⟩ :=
    exists_small_radius_of_finite
      (fun o : O => essentialWindowPointPairMap Dₙ R o.1)
      (center, center) s ρ hρ
  let a : ℝ := center - (r + τ)
  let b : ℝ := center + (r + τ)
  let a' : ℝ := center - (s + τ)
  let b' : ℝ := center + (s + τ)
  let A := essentialWindowIntervalTokens Dₘ R a b
  let B := essentialWindowIntervalTokens Dₙ R a' b'
  letI : Finite A := Finite.of_injective (fun o : A => o.1) Subtype.val_injective
  letI : Finite B := Finite.of_injective (fun o : B => o.1) Subtype.val_injective
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have hxt : r + τ < essentialWindowExit R (center, center) := by
    have hlt : r + τ ≤ s + ρ := by dsimp [s, δ]; linarith
    exact lt_of_le_of_lt hlt hsρ
  have hyt : s + τ < essentialWindowExit R (center, center) := by
    exact lt_trans (by linarith [hτρ]) hsρ
  have hgeom (x : ℝ) (hx : 0 ≤ x)
      (hxe : x < essentialWindowExit R (center, center)) :
      -R < center - x ∧ center + x < R := by
    have habs : |center| < R - x := by
      dsimp [essentialWindowExit] at hxe
      linarith
    have hcenter := abs_lt.mp habs
    constructor <;> linarith
  have hsourceGeom := hgeom (r + τ) (by linarith [hr, hτ0]) hxt
  have htargetGeom := hgeom (s + τ) (by linarith [hs, hτ0]) hyt
  have hsourceOrder : a < b := by dsimp [a, b]; linarith
  have htargetOrder : a' < b' := by dsimp [a', b']; linarith
  have hMcount : Fintype.card A = essentialMeasureValue M
      (show a ≤ b from hsourceOrder.le) := by
    exact essentialWindowIntervalTokens_card_eq_measure hM
      hsourceGeom.1 hsourceGeom.2 hsourceOrder.le (FB := inferInstance)
  have hNcount : Fintype.card B = essentialMeasureValue N
      (show a' ≤ b' from htargetOrder.le) := by
    exact essentialWindowIntervalTokens_card_eq_measure hN
      htargetGeom.1 htargetGeom.2 htargetOrder.le (FB := inferInstance)
  have hbox := i.essentialMeasureValue_box_le_of_qTame hN
    (show a ≤ b from hsourceOrder.le)
  have hbox' : essentialMeasureValue M (show a ≤ b from hsourceOrder.le) ≤
      essentialMeasureValue N (show a' ≤ b' from htargetOrder.le) := by
    convert hbox using 1 <;> congr 1 <;> dsimp [a, b, a', b', s, δ] <;> ring
  have hballA := essentialWindow_ball_to_interval Dₘ (R := R) (center := center)
    (r := r) (a := a) (b := b)
    (by dsimp [a]; linarith [hτ0]) (by dsimp [b]; linarith [hτ0])
    (FB := inferInstance)
  have hballB := essentialWindow_interval_to_ball Dₙ (R := R)
    (center := center) (s := s) (ρ := ρ) (τ := τ) hτρ
    (by
      intro o ho
      exact hsmall o ho)
    (FB := inferInstance)
  calc
    (PersistenceMeasureWindowMatching.pointBall
      (essentialWindowPointPairMap Dₘ R) (center, center) r).card ≤
        Fintype.card A := hballA
    _ = essentialMeasureValue M (show a ≤ b from hsourceOrder.le) := hMcount
    _ ≤ essentialMeasureValue N (show a' ≤ b' from htargetOrder.le) := hbox'
    _ = Fintype.card B := hNcount.symm
    _ ≤ (PersistenceMeasureWindowMatching.pointBall
      (essentialWindowPointPairMap Dₙ R) (center, center) s).card := hballB

private theorem essentialWindow_interleaving_reverse_ball_count
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) (hN : N.QTame) (i : RealInterleaving ε M N)
    {R : ℝ} (hR : 0 < R)
    [FM : Fintype (essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R)]
    [FN : Fintype (essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R)]
    (center : ℝ)
    (hexit : (ε : ℝ) < essentialWindowExit R (center, center)) :
    (PersistenceMeasureWindowMatching.pointBall
      (essentialWindowPointPairMap
        (LocallyFiniteDecoratedDiagram.ofQModule hN) R) (center, center) 0).card ≤
    (PersistenceMeasureWindowMatching.pointBall
      (essentialWindowPointPairMap
        (LocallyFiniteDecoratedDiagram.ofQModule hM) R) (center, center)
      (ε : ℝ)).card := by
  have h := essentialWindow_interleaving_ball_count hN hM i.symm hR center 0
    (by norm_num) (by simpa using hexit)
  simpa using h

/-- An actual q-tame interleaving gives the exact local closed-ball comparisons
needed to Hall-match essential occurrence tokens.  Source births have a `2ε` window
margin and distinct source birth values are separated by `2ε`; target values need no
separation. -/
private theorem essentialWindow_interleaving_matching
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) (hN : N.QTame) (i : RealInterleaving ε M N)
    {R : ℝ} (hR : 0 < R)
    [FM : Fintype (essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R)]
    [FN : Fintype (essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R)]
    (hmargin : ∀ x : essentialWindowTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R,
        2 * (ε : ℝ) < essentialWindowExit R
          (essentialWindowPointPairMap
            (LocallyFiniteDecoratedDiagram.ofQModule hM) R x))
    (hsep : ∀ x x' : essentialWindowTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R,
        essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hM) R x ≠
            essentialWindowPointPairMap
              (LocallyFiniteDecoratedDiagram.ofQModule hM) R x' →
        2 * (ε : ℝ) < dist
          (essentialWindowPointPairMap
            (LocallyFiniteDecoratedDiagram.ofQModule hM) R x)
          (essentialWindowPointPairMap
            (LocallyFiniteDecoratedDiagram.ofQModule hM) R x')) :
    ∃ f : essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R →
        essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R,
      Function.Injective f ∧
      (∀ x, dist
        (essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hM) R x)
        (essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hN) R (f x)) ≤ (ε : ℝ)) ∧
      (∀ y, (ε : ℝ) < essentialWindowExit R
        (essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hN) R y) →
        ∃ x, f x = y) := by
  classical
  let Dₘ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hM
  let Dₙ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hN
  letI : Fintype (essentialWindowTokens Dₘ R) := FM
  letI : Fintype (essentialWindowTokens Dₙ R) := FN
  let x : essentialWindowTokens Dₘ R → ℝ × ℝ := essentialWindowPointPairMap Dₘ R
  let y : essentialWindowTokens Dₙ R → ℝ × ℝ := essentialWindowPointPairMap Dₙ R
  let δ : ℝ := (ε : ℝ)
  have hxy0 : ∀ z,
      (PersistenceMeasureWindowMatching.pointBall x (x z) 0).card ≤
      (PersistenceMeasureWindowMatching.pointBall y (x z) δ).card := by
    intro z
    have hm := hmargin z
    have hm' : 2 * (ε : ℝ) < R -
        |essentialWindowBirthMap Dₘ R z| := by
      simpa [essentialWindowExit, essentialWindowPointPairMap,
        essentialWindowBirthMap] using hm
    have hz := essentialWindow_interleaving_ball_count hM hN i hR
      (essentialWindowBirthMap Dₘ R z) 0 (by norm_num)
      (by
        dsimp [essentialWindowExit]
        linarith)
    simpa [x, y, δ, essentialWindowPointPairMap, essentialWindowBirthMap] using hz
  have hyxδ : ∀ z,
      (PersistenceMeasureWindowMatching.pointBall y (x z) δ).card ≤
      (PersistenceMeasureWindowMatching.pointBall x (x z) (2 * δ)).card := by
    intro z
    have hz := essentialWindow_interleaving_ball_count hN hM i.symm hR
      (essentialWindowBirthMap Dₘ R z) δ (by dsimp [δ]; positivity)
      (by
        have hm' : 2 * (ε : ℝ) < R -
            |essentialWindowBirthMap Dₘ R z| := by
          simpa [essentialWindowExit, essentialWindowPointPairMap,
            essentialWindowBirthMap] using hmargin z
        dsimp [δ, essentialWindowExit]
        linarith)
    simpa [x, y, δ, essentialWindowPointPairMap, essentialWindowBirthMap, two_mul] using hz
  have hyx0 : ∀ z, δ < essentialWindowExit R (y z) →
      (PersistenceMeasureWindowMatching.pointBall y (y z) 0).card ≤
      (PersistenceMeasureWindowMatching.pointBall x (y z) δ).card := by
    intro z hz
    have hz' := essentialWindow_interleaving_reverse_ball_count hM hN i hR
      (essentialWindowBirthMap Dₙ R z) (by simpa [y, δ, essentialWindowPointPairMap,
        essentialWindowBirthMap, essentialWindowExit] using hz)
    simpa [x, y, δ, essentialWindowPointPairMap, essentialWindowBirthMap] using hz'
  have hsep' : ∀ z z', x z ≠ x z' → 2 * δ < dist (x z) (x z') := by
    intro z z' hne
    simpa [x, δ] using hsep z z' hne
  obtain ⟨f, hf, hclose, hcover⟩ :=
    PersistenceMeasureWindowMatching.exists_finite_window_matching_of_center_counts
      x y (essentialWindowExit R) (by dsimp [δ]; positivity)
      hsep' hxy0 hyxδ hyx0
  refine ⟨f, hf, ?_, ?_⟩
  · intro z
    simpa [x, y, δ] using hclose z
  · intro z hz
    exact hcover z (by simpa [y, δ] using hz)

private def finiteWindowRectangleTokens (D : LocallyFiniteDecoratedDiagram)
    (R h a b c d : ℝ) :=
  {o : finiteWindowTokens D R h // o.1.1.1 ∈ rectangleCell a b c d}

/-- The tokens of a separated rectangle inside a finite window have cardinality equal
to its actual q-tame persistence-measure value. The proof retains both endpoint
decorations and uses the exact decorated rectangle count. -/
private theorem finiteWindowRectangleTokens_card_eq_measure
    {k : Type u} [Field k] {M : PModule.{u,0,w} k ℝ} (hM : M.QTame)
    {R h a b c d : ℝ} (hh : 0 < h) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : -R < a) (hb : b < R) (hc : -R < c) (hd : d < R) (hgap : h < c - b)
    [FW : Fintype (finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R h)]
    (FB : Fintype (finiteWindowRectangleTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R h a b c d)) :
    @Fintype.card (finiteWindowRectangleTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R h a b c d) FB =
      persistenceMeasureValue M hab.le hbc.le hcd.le := by
  classical
  let D : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hM
  let I := finiteWindowTokens D R h
  letI : Fintype I := inferInstance
  obtain ⟨S, hS, hcount⟩ := moduleExtendedDiagramMultiplicity_rectangle_counts
    M hM a b c d hab hbc hcd
  let P : Type := {p : Cut ℝ × Cut ℝ // p ∈ S}
  let T : Type := Σ p : P, Fin (D.multiplicity p.1)
  let B := finiteWindowRectangleTokens D R h a b c d
  letI : Fintype B := FB
  let e : B ≃ T := {
    toFun := fun o => by
      have hpos : 0 < D.multiplicity o.1.1.1.1 := o.1.1.1.2.1
      exact ⟨⟨o.1.1.1.1, (hS o.1.1.1.1).mpr ⟨o.2, by
        simpa [D, LocallyFiniteDecoratedDiagram.ofQModule] using hpos⟩⟩, o.1.1.2⟩
    invFun := fun z => by
      let p := z.1.1
      have hpS := (hS p).mp z.1.2
      have hfinite : p.2 ≠ infinityCut := by
        intro hInf
        exact infinityCut_not_mem_cutCell c d (hInf ▸ hpS.1.2)
      have hpos : 0 < D.multiplicity p := by
        simpa [D, LocallyFiniteDecoratedDiagram.ofQModule] using hpS.2
      let o : D.finiteOccurrences := ⟨⟨p, ⟨hpos, hfinite⟩⟩, z.2⟩
      have hbirth := cutEndpoint_bounds hpS.1.1
      have hdeath := cutEndpoint_bounds hpS.1.2
      have hcoords : |cutEndpoint p.1| < R ∧ |cutEndpoint p.2| < R := by
        constructor
        · rw [abs_lt]
          constructor <;> linarith
        · rw [abs_lt]
          constructor <;> linarith
      have hlen : h < cutEndpoint p.2 - cutEndpoint p.1 := by linarith
      have hwindow : finiteWindowPoint R h (D.finitePoint o) := by
        simpa [LocallyFiniteDecoratedDiagram.finitePoint] using
          ⟨hcoords.1, hcoords.2, hlen⟩
      exact ⟨⟨o, hwindow⟩, hpS.1⟩
    left_inv := by
      intro o
      apply Subtype.ext
      apply Subtype.ext
      apply Sigma.ext
      · apply Subtype.ext
        rfl
      · rfl
    right_inv := by
      intro z
      cases z with
      | mk p n =>
        apply Sigma.ext
        · apply Subtype.ext
          rfl
        · rfl
  }
  calc
    @Fintype.card B FB = Fintype.card T := Fintype.card_congr e
    _ = ∑ p ∈ S, D.multiplicity p := by
      simpa [T, P, Fintype.card_sigma, Finset.sum_attach]
    _ = persistenceMeasureValue M hab.le hbc.le hcd.le := by
      simpa [D, LocallyFiniteDecoratedDiagram.ofQModule] using hcount.symm

private theorem finiteWindow_ball_to_rectangle
    (D : LocallyFiniteDecoratedDiagram) {R h a b c d : ℝ}
    [FW : Fintype (finiteWindowTokens D R h)]
    (center : ℝ × ℝ) (r : ℝ)
    (ha : a < center.1 - r) (hb : center.1 + r < b)
    (hc : c < center.2 - r) (hd : center.2 + r < d)
    (FB : Fintype (finiteWindowRectangleTokens D R h a b c d)) :
    (PersistenceMeasureWindowMatching.pointBall (finiteWindowPointMap D R h)
      center r).card ≤ Fintype.card (finiteWindowRectangleTokens D R h a b c d) := by
  classical
  let I := finiteWindowTokens D R h
  let B := finiteWindowRectangleTokens D R h a b c d
  letI : Fintype I := inferInstance
  letI : Fintype B := FB
  let A := {o : I // dist (finiteWindowPointMap D R h o) center ≤ r}
  let f : A → B := fun o => by
    let q := o.1.1.1.1
    have hdist : max
        |cutEndpoint q.1 - center.1| |cutEndpoint q.2 - center.2| ≤ r := by
      simpa [finiteWindowPointMap, LocallyFiniteDecoratedDiagram.finitePoint,
        Prod.dist_eq, Real.dist_eq] using o.2
    have hdists := max_le_iff.mp hdist
    have hbounds := abs_le.mp hdists.1
    have hdbounds := abs_le.mp hdists.2
    have hbirth := D.finiteEndpoints q o.1.1.1.2.1 o.1.1.1.2.2
    have hdeath := D.finiteEndpoints q o.1.1.1.2.1 o.1.1.1.2.2
    have hbirthLower : center.1 - r ≤ cutEndpoint q.1 := by linarith [hbounds.1]
    have hbirthUpper : cutEndpoint q.1 ≤ center.1 + r := by linarith [hbounds.2]
    have hdeathLower : center.2 - r ≤ cutEndpoint q.2 := by linarith [hdbounds.1]
    have hdeathUpper : cutEndpoint q.2 ≤ center.2 + r := by linarith [hdbounds.2]
    have hbirthCell : q.1 ∈ cutCell a b :=
      cut_mem_cell_of_endpoint_inside (c := q.1) (a := a) (b := b) hbirth.1
        (by linarith) (by linarith)
    have hdeathCell : q.2 ∈ cutCell c d :=
      cut_mem_cell_of_endpoint_inside (c := q.2) (a := c) (b := d) hdeath.2
        (by linarith) (by linarith)
    exact ⟨o.1, ⟨hbirthCell, hdeathCell⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hv : x.1 = y.1 := by
      have hval := congrArg (fun z : B => z.1) hxy
      dsimp [f] at hval
      exact hval
    exact Subtype.ext hv
  have hcard : Fintype.card A =
      (PersistenceMeasureWindowMatching.pointBall (finiteWindowPointMap D R h)
        center r).card :=
    (pointBall_card_eq_subtype _ _ _).symm
  rw [← hcard]
  exact Fintype.card_le_of_injective f hf

private def finiteCutPoint (p : Cut ℝ × Cut ℝ) : ℝ × ℝ :=
  (cutEndpoint p.1, cutEndpoint p.2)

private theorem finiteRectangle_dist_le {p : Cut ℝ × Cut ℝ} {center : ℝ × ℝ}
    {r : ℝ} (hp : p ∈ rectangleCell (center.1 - r) (center.1 + r)
      (center.2 - r) (center.2 + r)) :
    dist (finiteCutPoint p) center ≤ r := by
  have hb := cutEndpoint_bounds hp.1
  have hd := cutEndpoint_bounds hp.2
  have hb' : |cutEndpoint p.1 - center.1| ≤ r := by
    rw [abs_le]
    constructor <;> linarith
  have hd' : |cutEndpoint p.2 - center.2| ≤ r := by
    rw [abs_le]
    constructor <;> linarith
  have hmax : max |cutEndpoint p.1 - center.1| |cutEndpoint p.2 - center.2| ≤ r :=
    max_le hb' hd'
  simpa [finiteCutPoint, Prod.dist_eq, Real.dist_eq] using hmax

private theorem finiteWindow_rectangle_to_ball
    (D : LocallyFiniteDecoratedDiagram) {R h : ℝ}
    [FW : Fintype (finiteWindowTokens D R h)]
    (center : ℝ × ℝ) (s ρ τ : ℝ) (hτ : τ < ρ)
    (hsmall : ∀ o : finiteWindowRectangleTokens D R h
        (center.1 - (s + ρ)) (center.1 + (s + ρ))
        (center.2 - (s + ρ)) (center.2 + (s + ρ)),
      dist (finiteWindowPointMap D R h o.1) center ≤ s + τ →
        dist (finiteWindowPointMap D R h o.1) center ≤ s)
    (FB : Fintype (finiteWindowRectangleTokens D R h
      (center.1 - (s + τ)) (center.1 + (s + τ))
      (center.2 - (s + τ)) (center.2 + (s + τ)))) :
    @Fintype.card (finiteWindowRectangleTokens D R h
      (center.1 - (s + τ)) (center.1 + (s + τ))
      (center.2 - (s + τ)) (center.2 + (s + τ))) FB ≤
      (PersistenceMeasureWindowMatching.pointBall (finiteWindowPointMap D R h)
        center s).card := by
  classical
  let I := finiteWindowTokens D R h
  let O := finiteWindowRectangleTokens D R h
      (center.1 - (s + ρ)) (center.1 + (s + ρ))
      (center.2 - (s + ρ)) (center.2 + (s + ρ))
  let B := finiteWindowRectangleTokens D R h
      (center.1 - (s + τ)) (center.1 + (s + τ))
      (center.2 - (s + τ)) (center.2 + (s + τ))
  let A := {o : I // dist (finiteWindowPointMap D R h o) center ≤ s}
  letI : Fintype I := inferInstance
  letI : Fintype B := FB
  let f : B → A := fun o => by
    have hinner := o.2
    have houter : o.1.1.1.1 ∈ rectangleCell
        (center.1 - (s + ρ)) (center.1 + (s + ρ))
        (center.2 - (s + ρ)) (center.2 + (s + ρ)) := by
      change (center.1 - (s + τ) ∈ o.1.1.1.1.1.lower ∧
        center.1 + (s + τ) ∈ o.1.1.1.1.1.upper) ∧
        (center.2 - (s + τ) ∈ o.1.1.1.1.2.lower ∧
        center.2 + (s + τ) ∈ o.1.1.1.1.2.upper) at hinner
      change (center.1 - (s + ρ) ∈ o.1.1.1.1.1.lower ∧
        center.1 + (s + ρ) ∈ o.1.1.1.1.1.upper) ∧
        (center.2 - (s + ρ) ∈ o.1.1.1.1.2.lower ∧
        center.2 + (s + ρ) ∈ o.1.1.1.1.2.upper)
      exact ⟨⟨Cut.lower_of_le (by linarith) hinner.1.1,
        Cut.upper_of_le (by linarith) hinner.1.2⟩,
        ⟨Cut.lower_of_le (by linarith) hinner.2.1,
        Cut.upper_of_le (by linarith) hinner.2.2⟩⟩
    have hclose : dist (finiteWindowPointMap D R h o.1) center ≤ s + τ := by
      have hnum := finiteRectangle_dist_le hinner
      simpa [finiteWindowPointMap, LocallyFiniteDecoratedDiagram.finitePoint,
        finiteCutPoint] using hnum
    let outerToken : O := ⟨o.1, houter⟩
    exact ⟨o.1, hsmall outerToken hclose⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : A => z.1) hxy
  have hcard : Fintype.card A =
      (PersistenceMeasureWindowMatching.pointBall (finiteWindowPointMap D R h)
        center s).card :=
    (pointBall_card_eq_subtype _ _ _).symm
  rw [← hcard]
  exact Fintype.card_le_of_injective f hf

private theorem finiteWindowExit_box_bounds {R h : ℝ} {p : ℝ × ℝ} {x : ℝ}
    (hx : x < finiteWindowExit R h p) :
    -R < p.1 - x ∧ p.1 + x < R ∧
      -R < p.2 - x ∧ p.2 + x < R ∧ h < p.2 - p.1 - 2 * x := by
  have hmin := lt_min_iff.mp hx
  have hx1 : x < R - |p.1| := hmin.1
  have hmin' := lt_min_iff.mp hmin.2
  have hx2 : x < R - |p.2| := hmin'.1
  have hx3 : x < (p.2 - p.1 - h) / 2 := hmin'.2
  have hp1 := abs_nonneg p.1
  have hp1lo : -|p.1| ≤ p.1 := neg_abs_le p.1
  have hp1hi : p.1 ≤ |p.1| := le_abs_self p.1
  have hp2lo : -|p.2| ≤ p.2 := neg_abs_le p.2
  have hp2hi : p.2 ≤ |p.2| := le_abs_self p.2
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

private theorem finiteWindowExit_le_add_dist {R h : ℝ} (p q : ℝ × ℝ) :
    finiteWindowExit R h p ≤ finiteWindowExit R h q + dist p q := by
  have hp1 : |p.1 - q.1| ≤ dist p q := by
    have h := le_max_left |p.1 - q.1| |p.2 - q.2|
    simpa [Prod.dist_eq, Real.dist_eq] using h
  have hp2 : |p.2 - q.2| ≤ dist p q := by
    have h := le_max_right |p.1 - q.1| |p.2 - q.2|
    simpa [Prod.dist_eq, Real.dist_eq] using h
  have hbirth : |q.1| ≤ |p.1| + dist p q := by
    calc
      |q.1| = |p.1 + (q.1 - p.1)| := by congr 1 <;> ring
      _ ≤ |p.1| + |q.1 - p.1| := abs_add_le _ _
      _ ≤ |p.1| + dist p q := by simpa [abs_sub_comm] using add_le_add_left hp1 |p.1|
  have hdeath : |q.2| ≤ |p.2| + dist p q := by
    calc
      |q.2| = |p.2 + (q.2 - p.2)| := by congr 1 <;> ring
      _ ≤ |p.2| + |q.2 - p.2| := abs_add_le _ _
      _ ≤ |p.2| + dist p q := by simpa [abs_sub_comm] using add_le_add_left hp2 |p.2|
  have hgap : p.2 - p.1 ≤ q.2 - q.1 + 2 * dist p q := by
    have h := (sub_le_iff_le_add.mpr (show p.2 - q.2 + (q.1 - p.1) ≤
        |p.2 - q.2| + |q.1 - p.1| from
          add_le_add (le_abs_self _) (le_abs_self _)))
    have hq1 : |q.1 - p.1| = |p.1 - q.1| := abs_sub_comm _ _
    rw [hq1] at h
    rw [show p.2 - p.1 = (q.2 - q.1) + (p.2 - q.2) + (q.1 - p.1) by ring]
    calc
      q.2 - q.1 + (p.2 - q.2) + (q.1 - p.1) ≤
          q.2 - q.1 + (|p.2 - q.2| + |p.1 - q.1|) := by linarith [h]
      _ ≤ q.2 - q.1 + (dist p q + dist p q) := by linarith
      _ = q.2 - q.1 + 2 * dist p q := by ring
  have hdiag : (p.2 - p.1 - h) / 2 ≤
      (q.2 - q.1 - h) / 2 + dist p q := by linarith
  unfold finiteWindowExit
  calc
    min (R - |p.1|) (min (R - |p.2|) ((p.2 - p.1 - h) / 2)) ≤
        min (R - |q.1| + dist p q)
          (min (R - |q.2| + dist p q)
            ((q.2 - q.1 - h) / 2 + dist p q)) :=
      min_le_min (by linarith) (min_le_min (by linarith) hdiag)
    _ = min (R - |q.1|) (min (R - |q.2|) ((q.2 - q.1 - h) / 2)) + dist p q := by
      simp [min_add_add_right, add_assoc]

private structure WindowPartialMatching {I J : Type*}
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (exit : ℝ × ℝ → ℝ) (δ : ℝ) where
  map : I → Option J
  injective : ∀ {i i' j}, map i = some j → map i' = some j → i = i'
  edge : ∀ {i j}, map i = some j → dist (x i) (y j) ≤ δ
  sourceUnmatched : ∀ i, map i = none → exit (x i) ≤ δ
  targetUnmatched : ∀ j, (∀ i, map i ≠ some j) → exit (y j) ≤ δ

private theorem optionBind_eq_some_iff {I J K : Type*}
    (f : I → Option J) (g : J → Option K) (i : I) (k : K) :
    (f i).bind g = some k ↔ ∃ j, f i = some j ∧ g j = some k := by
  cases h : f i <;> simp [h]

private noncomputable def WindowPartialMatching.pullbackMap
    {I J K : Type*} {x : I → ℝ × ℝ} {y : J → ℝ × ℝ} {z : K → ℝ × ℝ}
    {exit : ℝ × ℝ → ℝ} {a b : ℝ}
    (f : WindowPartialMatching x y exit a)
    (g : WindowPartialMatching z y exit b) (i : I) : Option K := by
  classical
  exact (f.map i).bind fun j =>
    if h : ∃ k, g.map k = some j then some (Classical.choose h) else none

private theorem WindowPartialMatching.pullbackMap_eq_some_iff
    {I J K : Type*} {x : I → ℝ × ℝ} {y : J → ℝ × ℝ} {z : K → ℝ × ℝ}
    {exit : ℝ × ℝ → ℝ} {a b : ℝ}
    (f : WindowPartialMatching x y exit a)
    (g : WindowPartialMatching z y exit b) (i : I) (k : K) :
    f.pullbackMap g i = some k ↔ ∃ j, f.map i = some j ∧ g.map k = some j := by
  classical
  unfold WindowPartialMatching.pullbackMap
  cases hfi : f.map i with
  | none => simp [hfi]
  | some j =>
    by_cases hpre : ∃ k', g.map k' = some j
    · simp only [hfi, Option.bind_some, dif_pos hpre, Option.some.injEq]
      constructor
      · intro hk
        refine ⟨j, rfl, ?_⟩
        rw [← hk]
        exact Classical.choose_spec hpre
      · rintro ⟨j', hfj, hj'k⟩
        have hj : j' = j := by simpa using hfj.symm
        subst j'
        exact g.injective (Classical.choose_spec hpre) hj'k
    · simp only [hfi, Option.bind_some, dif_neg hpre]
      constructor
      · intro h
        cases h
      · rintro ⟨j', hfj, hj'k⟩
        have hj : j' = j := by simpa using hfj.symm
        subst j'
        exact (hpre ⟨k, hj'k⟩).elim

private def WindowPartialMatching.pullback
    {I J K : Type*} {x : I → ℝ × ℝ} {y : J → ℝ × ℝ} {z : K → ℝ × ℝ}
    {exit : ℝ × ℝ → ℝ} {a b : ℝ}
    (f : WindowPartialMatching x y exit a)
    (g : WindowPartialMatching z y exit b)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hExitLip : ∀ p q, exit p ≤ exit q + dist p q) :
    WindowPartialMatching x z exit (a + b) := by
  classical
  refine ⟨f.pullbackMap g, ?_, ?_, ?_, ?_⟩
  · intro i i' k hik hik'
    obtain ⟨j, hfi, hkj⟩ := (f.pullbackMap_eq_some_iff g i k).mp hik
    obtain ⟨j', hfi', hkj'⟩ := (f.pullbackMap_eq_some_iff g i' k).mp hik'
    have hjj' : j = j' := Option.some.inj (hkj.symm.trans hkj')
    subst j'
    exact f.injective hfi hfi'
  · intro i k hik
    obtain ⟨j, hfi, hkj⟩ := (f.pullbackMap_eq_some_iff g i k).mp hik
    have h₁ := f.edge hfi
    have h₂ := g.edge hkj
    have h₂' : dist (y j) (z k) ≤ b := by simpa [dist_comm] using h₂
    have htri := dist_triangle (x i) (y j) (z k)
    linarith
  · intro i hi
    change f.pullbackMap g i = none at hi
    cases hfi : f.map i with
    | none => exact (f.sourceUnmatched i hfi).trans (by linarith)
    | some j =>
      have hjnone : ∀ k, g.map k ≠ some j := by
        intro k hjk
        have heq : f.pullbackMap g i = some k :=
          (f.pullbackMap_eq_some_iff g i k).2 ⟨j, hfi, hjk⟩
        rw [hi] at heq
        cases heq
      have hy := g.targetUnmatched j hjnone
      have hxy := f.edge hfi
      have hlip := hExitLip (x i) (y j)
      linarith
  · intro k hk
    cases hgk : g.map k with
    | none => exact (g.sourceUnmatched k hgk).trans (by linarith)
    | some j =>
      have hjnone : ∀ i, f.map i ≠ some j := by
        intro i hfi
        have heq : f.pullbackMap g i = some k :=
          (f.pullbackMap_eq_some_iff g i k).2 ⟨j, hfi, hgk⟩
        exact hk i heq
      have hy := f.targetUnmatched j hjnone
      have hzy := g.edge hgk
      have hlip := hExitLip (z k) (y j)
      have hdist : dist (z k) (y j) ≤ b := hzy
      linarith

private def WindowPartialMatching.comp
    {I J K : Type*} {x : I → ℝ × ℝ} {y : J → ℝ × ℝ} {z : K → ℝ × ℝ}
    {exit : ℝ × ℝ → ℝ} {a b : ℝ}
    (f : WindowPartialMatching x y exit a)
    (g : WindowPartialMatching y z exit b)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hExitLip : ∀ p q, exit p ≤ exit q + dist p q) :
    WindowPartialMatching x z exit (a + b) := by
  classical
  refine ⟨fun i => (f.map i).bind g.map, ?_, ?_, ?_, ?_⟩
  · intro i i' k hik hik'
    obtain ⟨j, hij, hjk⟩ := (optionBind_eq_some_iff f.map g.map i k).mp hik
    obtain ⟨j', hij', hj'k⟩ := (optionBind_eq_some_iff f.map g.map i' k).mp hik'
    have hjj' : j = j' := g.injective hjk hj'k
    subst j'
    exact f.injective hij hij'
  · intro i k hik
    obtain ⟨j, hij, hjk⟩ := (optionBind_eq_some_iff f.map g.map i k).mp hik
    have h₁ := f.edge hij
    have h₂ := g.edge hjk
    have htri := dist_triangle (x i) (y j) (z k)
    linarith
  · intro i hi
    cases hfi : f.map i with
    | none => exact (f.sourceUnmatched i hfi).trans (by linarith)
    | some j =>
      have hgj : g.map j = none := by
        cases hgj : g.map j with
        | none => rfl
        | some k =>
          have : (f.map i).bind g.map = some k := by simp [hfi, hgj]
          simp [this] at hi
      have hy := g.sourceUnmatched j hgj
      have hxy := f.edge hfi
      have hlip := hExitLip (x i) (y j)
      linarith
  · intro k hk
    by_cases hpre : ∃ j, g.map j = some k
    · obtain ⟨j, hjk⟩ := hpre
      have hjnone : ∀ i, f.map i ≠ some j := by
        intro i hfi
        apply hk i
        exact (optionBind_eq_some_iff f.map g.map i k).2 ⟨j, hfi, hjk⟩
      have hy := f.targetUnmatched j hjnone
      have hzy := g.edge hjk
      have hlip := hExitLip (z k) (y j)
      have hdist : dist (z k) (y j) ≤ b := by simpa [dist_comm] using hzy
      linarith
    · have hn := g.targetUnmatched k (by
        intro j hjk
        exact hpre ⟨j, hjk⟩)
      linarith

private theorem exists_global_window_partial_matching
    {ε : ℝ≥0} {ι : RealInterleaving.InterpolationTime ε → Type v}
    (point : ∀ s, ι s → ℝ × ℝ) (exit : ℝ × ℝ → ℝ)
    (hExitLip : ∀ p q, exit p ≤ exit q + dist p q)
    (hlocal : ∀ s, ∃ ρ, 0 < ρ ∧ ∀ r,
      (nndist s.1 r.1 : ℝ) < ρ → Nonempty (WindowPartialMatching
        (point s) (point r) exit (nndist s.1 r.1 : ℝ))) :
    Nonempty (WindowPartialMatching
      (point (⟨0, le_rfl, ε.coe_nonneg⟩ : RealInterleaving.InterpolationTime ε))
      (point (⟨(ε : ℝ), ε.coe_nonneg, le_rfl⟩ : RealInterleaving.InterpolationTime ε))
      exit (ε : ℝ)) := by
  classical
  let T := RealInterleaving.InterpolationTime ε
  let first : T := ⟨0, le_rfl, ε.coe_nonneg⟩
  let last : T := ⟨(ε : ℝ), ε.coe_nonneg, le_rfl⟩
  let Reach (s : T) : Prop := Nonempty (WindowPartialMatching
    (point first) (point s) exit s.1)
  let Prefix (s : T) : Prop := ∀ r, r.1 ≤ s.1 → Reach r
  let S : Set ℝ := {x | ∃ s : T, s.1 = x ∧ Prefix s}
  have hfirst : Prefix first := by
    intro r hr
    have hr0 : r.1 = 0 := le_antisymm (by simpa [first] using hr) r.2.1
    have hre : r = first := Subtype.ext hr0
    subst r
    refine ⟨?_⟩
    refine ⟨fun i => some i, ?_, ?_, ?_, ?_⟩
    · intro i i' j hij hij'
      exact (Option.some.inj hij).trans (Option.some.inj hij').symm
    · intro i j hij
      have hji : i = j := Option.some.inj hij
      subst j
      simpa [dist_self] using first.2.1
    · intro i hi
      simp at hi
    · intro j hj
      exact (hj j (by simp)).elim
  have hS_ne : S.Nonempty := ⟨0, ⟨first, by simp [first], hfirst⟩⟩
  have hS_bdd : BddAbove S := ⟨(ε : ℝ), by
    rintro x ⟨s, rfl, _⟩
    exact s.2.2⟩
  let b := sSup S
  have hb0 : 0 ≤ b := le_csSup hS_bdd
    (show (0 : ℝ) ∈ S from ⟨first, by simp [first], hfirst⟩)
  have hbε : b ≤ (ε : ℝ) := csSup_le hS_ne (by
    rintro x ⟨s, rfl, _⟩
    exact s.2.2)
  let bTime : T := ⟨b, hb0, hbε⟩
  have hReachB : Reach bTime := by
    obtain ⟨ρ, hρ, hlocalB⟩ := hlocal bTime
    have hbelow : b - ρ / 2 < b := by linarith
    obtain ⟨x, hxS, hxb⟩ := (lt_csSup_iff hS_bdd hS_ne).mp hbelow
    rcases hxS with ⟨s, hs, hpre⟩
    have hxMem : x ∈ S := ⟨s, hs, hpre⟩
    have hle : s.1 ≤ b := by
      have hxle : x ≤ b := le_csSup hS_bdd hxMem
      simpa [hs] using hxle
    have hdist : (nndist b s.1 : ℝ) = b - s.1 := by
      rw [coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
    have hsmall : (nndist b s.1 : ℝ) < ρ := by
      rw [hdist]
      linarith
    obtain ⟨g⟩ := hlocalB s hsmall
    obtain ⟨f⟩ := hpre s le_rfl
    have hbudget : s.1 + (nndist b s.1 : ℝ) = b := by
      rw [hdist]
      ring
    have hbudgetDist : s.1 + dist b s.1 = b := by
      simpa only [coe_nndist] using hbudget
    have hmatched := f.pullback g s.2.1
      (show 0 ≤ (nndist b s.1 : ℝ) from NNReal.coe_nonneg _)
      hExitLip
    refine ⟨?_⟩
    simpa [Reach, bTime, hbudgetDist] using hmatched
  have hPrefixB : Prefix bTime := by
    intro r hr
    by_cases hlt : r.1 < b
    · obtain ⟨x, hxS, hrx⟩ := (lt_csSup_iff hS_bdd hS_ne).mp hlt
      rcases hxS with ⟨s, hs, hpre⟩
      have hrs : r.1 ≤ s.1 := (le_of_lt hrx).trans_eq hs.symm
      exact hpre r hrs
    · have hrb : r.1 = b := le_antisymm hr (le_of_not_gt hlt)
      have hre : r = bTime := Subtype.ext hrb
      subst r
      exact hReachB
  have hb_eq : b = (ε : ℝ) := by
    apply le_antisymm hbε
    by_contra hne
    have hb_lt : b < (ε : ℝ) := lt_of_not_ge hne
    obtain ⟨ρ, hρ, hlocalB⟩ := hlocal bTime
    let step := min (ρ / 2) (((ε : ℝ) - b) / 2)
    have hstep : 0 < step := lt_min (by linarith) (by linarith)
    let t : T := ⟨b + step, by linarith, by
      have hright : step ≤ ((ε : ℝ) - b) / 2 := min_le_right _ _
      linarith⟩
    have hbt : b < t.1 := by dsimp [t]; linarith
    have hstepρ : t.1 - b < ρ := by
      dsimp [t]
      have := min_le_left (ρ / 2) (((ε : ℝ) - b) / 2)
      linarith
    have hpreT : Prefix t := by
      intro r hr
      by_cases hle : r.1 ≤ b
      · exact hPrefixB r hle
      · have hbr : b < r.1 := lt_of_not_ge hle
        have hdist : (nndist bTime.1 r.1 : ℝ) = r.1 - b := by
          rw [coe_nndist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (le_of_lt hbr))]
          ring
        have hrs : (nndist bTime.1 r.1 : ℝ) < ρ := by
          rw [hdist]
          have hrt : r.1 ≤ t.1 := hr
          dsimp [bTime] at *
          linarith
        obtain ⟨g⟩ := hlocalB r hrs
        obtain ⟨f⟩ := hReachB
        have hbudget : b + (nndist bTime.1 r.1 : ℝ) = r.1 := by
          rw [hdist]
          ring
        have hbudgetDist : b + dist b r.1 = r.1 := by
          simpa only [coe_nndist] using hbudget
        have hmatched := f.comp g hb0
          (show 0 ≤ (nndist bTime.1 r.1 : ℝ) from NNReal.coe_nonneg _)
          hExitLip
        refine ⟨?_⟩
        simpa [Reach, bTime, hbudgetDist] using hmatched
    have hmem : t.1 ∈ S := ⟨t, rfl, hpreT⟩
    have htle : t.1 ≤ b := le_csSup hS_bdd hmem
    linarith
  have hEnd : bTime = last := Subtype.ext hb_eq
  have hReachEnd : Reach last := by simpa [hEnd] using hReachB
  simpa [Reach, first, last] using hReachEnd

/-- The actual q-tame rectangle inequality gives the first local closed-ball
comparison needed by finite Hall matching.  All counts are restricted to the fixed
finite off-diagonal window: a slightly enlarged source ball lies in a strict
decorated rectangle, the q-tame box inequality compares its measure with the
thickened target rectangle, and finite-support shrinking puts that rectangle back
inside the target closed ball. -/
private theorem finiteWindow_interleaving_ball_count
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) (hN : N.QTame) (i : RealInterleaving ε M N)
    {R h : ℝ} (hR : 0 < R) (hh : 0 < h)
    [FM : Fintype (finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R h)]
    [FN : Fintype (finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R h)]
    (center : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hmarg : r + (ε : ℝ) < finiteWindowExit R h center) :
    (PersistenceMeasureWindowMatching.pointBall
      (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h)
      center r).card ≤
    (PersistenceMeasureWindowMatching.pointBall
      (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R h)
      center (r + (ε : ℝ))).card := by
  classical
  let Dₘ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hM
  let Dₙ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hN
  letI : Fintype (finiteWindowTokens Dₘ R h) := FM
  letI : Fintype (finiteWindowTokens Dₙ R h) := FN
  let δ := (ε : ℝ)
  let s := r + δ
  have hδ : 0 ≤ δ := ε.coe_nonneg
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hslack : 0 < finiteWindowExit R h center - s := by
    dsimp [s, δ]
    linarith
  let ρ := (finiteWindowExit R h center - s) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsρ : s + ρ < finiteWindowExit R h center := by
    dsimp [ρ]
    linarith
  let O := finiteWindowRectangleTokens Dₙ R h
      (center.1 - (s + ρ)) (center.1 + (s + ρ))
      (center.2 - (s + ρ)) (center.2 + (s + ρ))
  letI : Finite O := Finite.of_injective (fun o : O => o.1) Subtype.val_injective
  letI : Fintype O := Fintype.ofFinite O
  obtain ⟨τ, hτ0, hτρ, hsmall⟩ :=
    exists_small_radius_of_finite (fun o : O => finiteWindowPointMap Dₙ R h o.1)
      center s ρ hρ
  let a := center.1 - (r + τ)
  let b := center.1 + (r + τ)
  let c := center.2 - (r + τ)
  let d := center.2 + (r + τ)
  let A := finiteWindowRectangleTokens Dₘ R h a b c d
  let a' := center.1 - (s + τ)
  let b' := center.1 + (s + τ)
  let c' := center.2 - (s + τ)
  let d' := center.2 + (s + τ)
  let B := finiteWindowRectangleTokens Dₙ R h a' b' c' d'
  letI : Finite A := Finite.of_injective (fun o : A => o.1) Subtype.val_injective
  letI : Finite B := Finite.of_injective (fun o : B => o.1) Subtype.val_injective
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have hxt : r + τ < finiteWindowExit R h center := by
    have hlt : r + τ ≤ s + ρ := by dsimp [s, δ]; linarith
    exact lt_of_le_of_lt hlt hsρ
  have hyt : s + τ < finiteWindowExit R h center := by
    exact lt_trans (by linarith [hτρ]) hsρ
  have hgeom : ∀ x : ℝ, 0 < x → x < finiteWindowExit R h center →
      -R < center.1 - x ∧ center.1 + x < R ∧
        -R < center.2 - x ∧ center.2 + x < R ∧ h < center.2 - center.1 - 2*x := by
    intro x hx hxe
    exact finiteWindowExit_box_bounds hxe
  have hsourceGeom := hgeom (r + τ) (by linarith) hxt
  have htargetGeom := hgeom (s + τ) (by dsimp [s]; linarith) hyt
  have hsourceOrder : a < b ∧ b < c ∧ c < d := by
    dsimp [a, b, c, d]
    constructor <;> [linarith; constructor <;> linarith]
  have htargetOrder : a' < b' ∧ b' < c' ∧ c' < d' := by
    dsimp [a', b', c', d']
    constructor <;> [linarith; constructor <;> linarith]
  have hsourceSeparated : h < c - b := by
    dsimp [b, c]
    linarith [hsourceGeom.2.2.2.2]
  have htargetSeparated : h < c' - b' := by
    dsimp [b', c']
    linarith [htargetGeom.2.2.2.2]
  have hboxGap : 2 * δ < c - b := by
    dsimp [b, c, δ]
    linarith [hsourceGeom.2.2.2.2, hh]
  have hMcount : Fintype.card A = persistenceMeasureValue M
      (show a ≤ b from hsourceOrder.1.le)
      (show b ≤ c from hsourceOrder.2.1.le)
      (show c ≤ d from hsourceOrder.2.2.le) := by
    exact finiteWindowRectangleTokens_card_eq_measure hM hh
      hsourceOrder.1 hsourceOrder.2.1 hsourceOrder.2.2
      hsourceGeom.1 hsourceGeom.2.1 hsourceGeom.2.2.1 hsourceGeom.2.2.2.1
      hsourceSeparated (FB := inferInstance)
  have hNcount : Fintype.card B = persistenceMeasureValue N
      (show a' ≤ b' from htargetOrder.1.le)
      (show b' ≤ c' from htargetOrder.2.1.le)
      (show c' ≤ d' from htargetOrder.2.2.le) := by
    exact finiteWindowRectangleTokens_card_eq_measure hN hh
      htargetOrder.1 htargetOrder.2.1 htargetOrder.2.2
      htargetGeom.1 htargetGeom.2.1 htargetGeom.2.2.1 htargetGeom.2.2.2.1
      htargetSeparated (FB := inferInstance)
  have hbox := i.persistenceMeasureValue_box_le_of_qTame hN
      (show a ≤ b from hsourceOrder.1.le)
      (show c ≤ d from hsourceOrder.2.2.le) hboxGap
  have hbox' : persistenceMeasureValue M
        (show a ≤ b from hsourceOrder.1.le)
        (show b ≤ c by have := δ; dsimp [a, b, c, δ] at *; linarith)
        (show c ≤ d from hsourceOrder.2.2.le) ≤
      persistenceMeasureValue N
        (show a' ≤ b' from htargetOrder.1.le)
        (show b' ≤ c' from htargetOrder.2.1.le)
        (show c' ≤ d' from htargetOrder.2.2.le) := by
    convert hbox using 1 <;> congr 1 <;> ring
  have hballA := finiteWindow_ball_to_rectangle Dₘ (R := R) (h := h) center r
      (a := a) (b := b) (c := c) (d := d)
      (by dsimp [a]; linarith [hτ0])
      (by dsimp [b]; linarith [hτ0])
      (by dsimp [c]; linarith [hτ0])
      (by dsimp [d]; linarith [hτ0])
      (FB := inferInstance)
  have hballB := finiteWindow_rectangle_to_ball Dₙ (R := R) (h := h) center s ρ τ hτρ
      (by
        intro o ho
        exact hsmall o ho)
      (FB := inferInstance)
  calc
    (PersistenceMeasureWindowMatching.pointBall
      (finiteWindowPointMap Dₘ R h) center r).card ≤ Fintype.card A := hballA
    _ = persistenceMeasureValue M
        (show a ≤ b from hsourceOrder.1.le)
        (show b ≤ c from hsourceOrder.2.1.le)
        (show c ≤ d from hsourceOrder.2.2.le) := hMcount
    _ ≤ persistenceMeasureValue N
        (show a' ≤ b' from htargetOrder.1.le)
        (show b' ≤ c' from htargetOrder.2.1.le)
        (show c' ≤ d' from htargetOrder.2.2.le) := hbox'
    _ = Fintype.card B := hNcount.symm
    _ ≤ (PersistenceMeasureWindowMatching.pointBall
      (finiteWindowPointMap Dₙ R h) center s).card := hballB

private theorem finiteWindow_interleaving_reverse_ball_count
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) (hN : N.QTame) (i : RealInterleaving ε M N)
    {R h : ℝ} (hR : 0 < R) (hh : 0 < h)
    [FM : Fintype (finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R h)]
    [FN : Fintype (finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R h)]
    (center : ℝ × ℝ) (hexit : (ε : ℝ) < finiteWindowExit R h center) :
    (PersistenceMeasureWindowMatching.pointBall
      (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R h)
      center 0).card ≤
    (PersistenceMeasureWindowMatching.pointBall
      (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h)
      center (ε : ℝ)).card := by
  have h := finiteWindow_interleaving_ball_count hN hM i.symm hR hh
    center 0 (by norm_num) (by simpa using hexit)
  simpa using h

/-- An actual q-tame interleaving yields the exact three localized count bounds
used by sharp finite Hall matching. The source margin and source-point separation
are the only local small-step conditions; target point values may split at arbitrary
distances. -/
private theorem finiteWindow_interleaving_matching
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) (hN : N.QTame) (i : RealInterleaving ε M N)
    {R h : ℝ} (hR : 0 < R) (hh : 0 < h)
    [FM : Fintype (finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R h)]
    [FN : Fintype (finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R h)]
    (hmargin : ∀ x : finiteWindowTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R h,
        2 * (ε : ℝ) < finiteWindowExit R h
          (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x))
    (hsep : ∀ x x' : finiteWindowTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R h,
        finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x ≠
          finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x' →
        2 * (ε : ℝ) < dist
          (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x)
          (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x')) :
    ∃ f : finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R h →
        finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R h,
      Function.Injective f ∧
      (∀ x, dist
        (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x)
        (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R h (f x)) ≤
          (ε : ℝ)) ∧
      (∀ y, (ε : ℝ) < finiteWindowExit R h
        (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R h y) →
        ∃ x, f x = y) := by
  classical
  let Dₘ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hM
  let Dₙ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hN
  letI : Fintype (finiteWindowTokens Dₘ R h) := FM
  letI : Fintype (finiteWindowTokens Dₙ R h) := FN
  let x : finiteWindowTokens Dₘ R h → ℝ × ℝ := finiteWindowPointMap Dₘ R h
  let y : finiteWindowTokens Dₙ R h → ℝ × ℝ := finiteWindowPointMap Dₙ R h
  let δ : ℝ := (ε : ℝ)
  have hxy0 : ∀ z, (PersistenceMeasureWindowMatching.pointBall x (x z) 0).card ≤
      (PersistenceMeasureWindowMatching.pointBall y (x z) δ).card := by
    intro z
    have hz := finiteWindow_interleaving_ball_count hM hN i hR hh
      (x z) 0 (by norm_num) (by have hm := hmargin z; have hε := ε.coe_nonneg; linarith)
    simpa [x, y, Dₘ, Dₙ, δ] using hz
  have hyxδ : ∀ z,
      (PersistenceMeasureWindowMatching.pointBall y (x z) δ).card ≤
      (PersistenceMeasureWindowMatching.pointBall x (x z) (2 * δ)).card := by
    intro z
    have hz := finiteWindow_interleaving_ball_count hN hM i.symm hR hh
      (x z) δ (by dsimp [δ]; positivity)
      (by simpa [δ, two_mul] using hmargin z)
    simpa [x, y, Dₘ, Dₙ, δ, two_mul] using hz
  have hyx0 : ∀ z, δ < finiteWindowExit R h (y z) →
      (PersistenceMeasureWindowMatching.pointBall y (y z) 0).card ≤
      (PersistenceMeasureWindowMatching.pointBall x (y z) δ).card := by
    intro z hz
    have hz' := finiteWindow_interleaving_reverse_ball_count hM hN i hR hh
      (y z) (by simpa [δ] using hz)
    simpa [x, y, Dₘ, Dₙ, δ] using hz'
  have hsep' : ∀ z z', x z ≠ x z' → 2 * δ < dist (x z) (x z') := by
    intro z z' hne
    simpa [x, δ, two_mul] using hsep z z' hne
  obtain ⟨f, hf, hclose, hcover⟩ :=
    PersistenceMeasureWindowMatching.exists_finite_window_matching_of_center_counts
      x y (finiteWindowExit R h) (by dsimp [δ]; positivity) hsep' hxy0 hyxδ hyx0
  refine ⟨f, hf, ?_, ?_⟩
  · intro z
    simpa [x, y, δ] using hclose z
  · intro z hz
    exact hcover z (by simpa [y, δ] using hz)

private theorem exists_positive_half_bound {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (hg : ∀ i, 0 < g i) :
    ∃ ρ, 0 < ρ ∧ ∀ i, 2 * ρ < g i := by
  classical
  have aux : ∀ s : Finset ι, ∃ ρ, 0 < ρ ∧ ∀ i ∈ s, 2 * ρ < g i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ρ, hρ, hρs⟩ := ih
      refine ⟨min ρ (g i / 4),
        (lt_min_iff.mpr ⟨hρ, div_pos (hg i) (by norm_num)⟩), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · rw [hji]
        have hle := min_le_right ρ (g i / 4)
        nlinarith [hg i]
      · have hle := min_le_left ρ (g i / 4)
        nlinarith [hρs j hj]
  obtain ⟨ρ, hρ, hρu⟩ := aux Finset.univ
  exact ⟨ρ, hρ, fun i => hρu i (Finset.mem_univ _)⟩

private theorem exists_local_matching_radius {I : Type*} [Fintype I]
    (x : I → ℝ × ℝ) (exit : ℝ × ℝ → ℝ)
    (hExit : ∀ i, 0 < exit (x i)) :
    ∃ ρ, 0 < ρ ∧ ∀ i j,
      2 * ρ < if x i = x j then exit (x i) else dist (x i) (x j) := by
  classical
  let gap : I × I → ℝ := fun ij =>
    if x ij.1 = x ij.2 then exit (x ij.1) else dist (x ij.1) (x ij.2)
  have hgap : ∀ ij, 0 < gap ij := by
    rintro ⟨i, j⟩
    by_cases h : x i = x j
    · simpa [gap, h] using hExit i
    · simpa [gap, h] using (dist_pos.mpr h)
  obtain ⟨ρ, hρ, hρgap⟩ := exists_positive_half_bound gap hgap
  refine ⟨ρ, hρ, ?_⟩
  intro i j
  simpa [gap] using hρgap (i, j)

private theorem finiteWindowExit_pos_of_mem {D : LocallyFiniteDecoratedDiagram}
    {R h : ℝ} {x : finiteWindowTokens D R h} :
    0 < finiteWindowExit R h (finiteWindowPointMap D R h x) := by
  have hx := x.2
  change |(finiteWindowPointMap D R h x).1| < R ∧
    |(finiteWindowPointMap D R h x).2| < R ∧
    h < (finiteWindowPointMap D R h x).2 - (finiteWindowPointMap D R h x).1 at hx
  rcases hx with ⟨hb, hd, hgap⟩
  have hbirth : 0 < R - |(finiteWindowPointMap D R h x).1| := sub_pos.mpr hb
  have hdeath : 0 < R - |(finiteWindowPointMap D R h x).2| := sub_pos.mpr hd
  have hdiag : 0 < ((finiteWindowPointMap D R h x).2 -
      (finiteWindowPointMap D R h x).1 - h) / 2 := by linarith
  unfold finiteWindowExit
  exact lt_min_iff.mpr ⟨hbirth, lt_min_iff.mpr ⟨hdeath, hdiag⟩⟩

private theorem essentialWindowExit_pos_of_mem {D : LocallyFiniteDecoratedDiagram}
    {R : ℝ} {x : essentialWindowTokens D R} :
    0 < essentialWindowExit R (essentialWindowPointPairMap D R x) := by
  simpa [essentialWindowExit, essentialWindowPointPairMap,
    essentialWindowBirthMap] using (sub_pos.mpr x.2)

private theorem finiteWindow_interpolating_local_partial
    {k : Type u} [Field k] {ε : ℝ≥0}
    (F : RealInterleaving.InterpolationTime ε → PModule.{u,0,w} k ℝ)
    (hqt : ∀ s, (F s).QTame)
    (hInter : ∀ s r, Nonempty
      (RealInterleaving (nndist s.1 r.1) (F s) (F r)))
    {R h : ℝ} (hR : 0 < R) (hh : 0 < h)
    (s : RealInterleaving.InterpolationTime ε) :
    ∃ ρ, 0 < ρ ∧ ∀ r, (nndist s.1 r.1 : ℝ) < ρ →
      Nonempty (WindowPartialMatching
        (finiteWindowPointMap
          (LocallyFiniteDecoratedDiagram.ofQModule (hqt s)) R h)
        (finiteWindowPointMap
          (LocallyFiniteDecoratedDiagram.ofQModule (hqt r)) R h)
        (finiteWindowExit R h) (nndist s.1 r.1 : ℝ)) := by
  classical
  let Dₛ : LocallyFiniteDecoratedDiagram :=
    LocallyFiniteDecoratedDiagram.ofQModule (hqt s)
  let I := finiteWindowTokens Dₛ R h
  letI : Finite I := finiteWindowTokens_finite Dₛ hR hh
  letI : Fintype I := Fintype.ofFinite I
  let x : I → ℝ × ℝ := finiteWindowPointMap Dₛ R h
  have hxexit : ∀ z, 0 < finiteWindowExit R h (x z) := by
    intro z
    exact finiteWindowExit_pos_of_mem
  let gap : I × I → ℝ := fun ij =>
    if x ij.1 = x ij.2 then finiteWindowExit R h (x ij.1)
    else dist (x ij.1) (x ij.2)
  have hgap : ∀ ij, 0 < gap ij := by
    rintro ⟨z, z'⟩
    by_cases heq : x z = x z'
    · simpa [gap, heq] using hxexit z
    · simpa [gap, heq] using (dist_pos.mpr heq)
  obtain ⟨ρ, hρ, hρgap⟩ := exists_positive_half_bound gap hgap
  refine ⟨ρ, hρ, ?_⟩
  intro r hr
  let Dᵣ : LocallyFiniteDecoratedDiagram :=
    LocallyFiniteDecoratedDiagram.ofQModule (hqt r)
  let J := finiteWindowTokens Dᵣ R h
  letI : Finite J := finiteWindowTokens_finite Dᵣ hR hh
  letI : Fintype J := Fintype.ofFinite J
  let y : J → ℝ × ℝ := finiteWindowPointMap Dᵣ R h
  let δ : ℝ := (nndist s.1 r.1 : ℝ)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have h2δ : 2 * δ < 2 * ρ := by nlinarith
  have hmargin : ∀ z : I, 2 * δ < finiteWindowExit R h (x z) := by
    intro z
    simpa [gap, x] using (lt_trans h2δ (hρgap (z, z)))
  have hsep : ∀ z z' : I, x z ≠ x z' →
      2 * δ < dist (x z) (x z') := by
    intro z z' hne
    simpa [gap, hne, x] using (lt_trans h2δ (hρgap (z, z')))
  obtain ⟨j⟩ := hInter s r
  obtain ⟨f, hf, hclose, hcover⟩ :=
    finiteWindow_interleaving_matching (hqt s) (hqt r) j hR hh
      (by intro z; simpa [δ, x] using hmargin z)
      (by intro z z' hne; simpa [δ, x] using hsep z z' hne)
  exact ⟨{
    map := fun z => some (f z)
    injective := by
      intro z z' y' hzy hzy'
      apply hf
      exact (Option.some.inj hzy).trans (Option.some.inj hzy').symm
    edge := by
      intro z y' hzy
      have hval : f z = y' := Option.some.inj hzy
      subst y'
      simpa [x, y, δ] using hclose z
    sourceUnmatched := by
      intro z hz
      have hsome : (some (f z) : Option J) ≠ none := by simp
      exact (hsome hz).elim
    targetUnmatched := by
      intro y' hy
      by_contra hnot
      have hexit : δ < finiteWindowExit R h (y y') := lt_of_not_ge hnot
      obtain ⟨z, hzy⟩ := hcover y' (by simpa [δ, y] using hexit)
      apply hy z
      simp [hzy]
  }⟩

private theorem essentialWindow_interpolating_local_partial
    {k : Type u} [Field k] {ε : ℝ≥0}
    (F : RealInterleaving.InterpolationTime ε → PModule.{u,0,w} k ℝ)
    (hqt : ∀ s, (F s).QTame)
    (hInter : ∀ s r, Nonempty
      (RealInterleaving (nndist s.1 r.1) (F s) (F r)))
    {R : ℝ} (hR : 0 < R)
    (s : RealInterleaving.InterpolationTime ε) :
    ∃ ρ, 0 < ρ ∧ ∀ r, (nndist s.1 r.1 : ℝ) < ρ →
      Nonempty (WindowPartialMatching
        (essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule (hqt s)) R)
        (essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule (hqt r)) R)
        (essentialWindowExit R) (nndist s.1 r.1 : ℝ)) := by
  classical
  let Dₛ : LocallyFiniteDecoratedDiagram :=
    LocallyFiniteDecoratedDiagram.ofQModule (hqt s)
  let I := essentialWindowTokens Dₛ R
  letI : Finite I := essentialWindowTokens_finite (hqt s) hR
  letI : Fintype I := Fintype.ofFinite I
  let x : I → ℝ × ℝ := essentialWindowPointPairMap Dₛ R
  have hxexit : ∀ z, 0 < essentialWindowExit R (x z) := by
    intro z
    exact essentialWindowExit_pos_of_mem
  let gap : I × I → ℝ := fun ij =>
    if x ij.1 = x ij.2 then essentialWindowExit R (x ij.1)
    else dist (x ij.1) (x ij.2)
  have hgap : ∀ ij, 0 < gap ij := by
    rintro ⟨z, z'⟩
    by_cases heq : x z = x z'
    · simpa [gap, heq] using hxexit z
    · simpa [gap, heq] using (dist_pos.mpr heq)
  obtain ⟨ρ, hρ, hρgap⟩ := exists_positive_half_bound gap hgap
  refine ⟨ρ, hρ, ?_⟩
  intro r hr
  let Dᵣ : LocallyFiniteDecoratedDiagram :=
    LocallyFiniteDecoratedDiagram.ofQModule (hqt r)
  let J := essentialWindowTokens Dᵣ R
  letI : Finite J := essentialWindowTokens_finite (hqt r) hR
  letI : Fintype J := Fintype.ofFinite J
  let y : J → ℝ × ℝ := essentialWindowPointPairMap Dᵣ R
  let δ : ℝ := (nndist s.1 r.1 : ℝ)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have h2δ : 2 * δ < 2 * ρ := by nlinarith
  have hmargin : ∀ z : I, 2 * δ < essentialWindowExit R (x z) := by
    intro z
    simpa [gap, x] using (lt_trans h2δ (hρgap (z, z)))
  have hsep : ∀ z z' : I, x z ≠ x z' →
      2 * δ < dist (x z) (x z') := by
    intro z z' hne
    simpa [gap, hne, x] using (lt_trans h2δ (hρgap (z, z')))
  obtain ⟨j⟩ := hInter s r
  obtain ⟨f, hf, hclose, hcover⟩ :=
    essentialWindow_interleaving_matching (hqt s) (hqt r) j hR
      (by intro z; simpa [δ, x] using hmargin z)
      (by intro z z' hne; simpa [δ, x] using hsep z z' hne)
  refine ⟨{
    map := fun z => some (f z)
    injective := by
      intro z z' y' hzy hzy'
      apply hf
      exact (Option.some.inj hzy).trans (Option.some.inj hzy').symm
    edge := by
      intro z y' hzy
      have hval : f z = y' := Option.some.inj hzy
      subst y'
      simpa [x, y, δ] using hclose z
    sourceUnmatched := by
      intro z hz
      have hsome : (some (f z) : Option J) ≠ none := by simp
      exact (hsome hz).elim
    targetUnmatched := by
      intro y' hy
      by_contra hnot
      have hexit : δ < essentialWindowExit R (y y') := lt_of_not_ge hnot
      obtain ⟨z, hzy⟩ := hcover y' (by simpa [δ, y] using hexit)
      apply hy z
      simp [hzy]
  }⟩

private theorem essentialWindowExit_le_add_dist {R : ℝ} (p q : ℝ × ℝ) :
    essentialWindowExit R p ≤ essentialWindowExit R q + dist p q := by
  have hcoord : |p.1 - q.1| ≤ dist p q := by
    have h := le_max_left |p.1 - q.1| |p.2 - q.2|
    simpa [Prod.dist_eq, Real.dist_eq] using h
  have habs : |q.1| ≤ |p.1| + dist p q := by
    calc
      |q.1| = |p.1 + (q.1 - p.1)| := by congr 1 <;> ring
      _ ≤ |p.1| + |q.1 - p.1| := abs_add_le _ _
      _ ≤ |p.1| + dist p q := by
        simpa [abs_sub_comm] using add_le_add_left hcoord |p.1|
  unfold essentialWindowExit
  linarith

private theorem finiteWindow_interpolating_global_partial
    {k : Type u} [Field k] {ε : ℝ≥0}
    (F : RealInterleaving.InterpolationTime ε → PModule.{u,0,w} k ℝ)
    (hqt : ∀ s, (F s).QTame)
    (hInter : ∀ s r, Nonempty
      (RealInterleaving (nndist s.1 r.1) (F s) (F r)))
    {R h : ℝ} (hR : 0 < R) (hh : 0 < h) :
    Nonempty (WindowPartialMatching
      (finiteWindowPointMap
        (LocallyFiniteDecoratedDiagram.ofQModule
          (hqt (⟨0, le_rfl, ε.coe_nonneg⟩ : RealInterleaving.InterpolationTime ε))) R h)
      (finiteWindowPointMap
        (LocallyFiniteDecoratedDiagram.ofQModule
          (hqt (⟨(ε : ℝ), ε.coe_nonneg, le_rfl⟩ : RealInterleaving.InterpolationTime ε))) R h)
      (finiteWindowExit R h) (ε : ℝ)) := by
  let point := fun s =>
    finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule (hqt s)) R h
  exact exists_global_window_partial_matching point (finiteWindowExit R h)
    finiteWindowExit_le_add_dist
    (by
      intro s
      exact finiteWindow_interpolating_local_partial F hqt hInter hR hh s)

private theorem essentialWindow_interpolating_global_partial
    {k : Type u} [Field k] {ε : ℝ≥0}
    (F : RealInterleaving.InterpolationTime ε → PModule.{u,0,w} k ℝ)
    (hqt : ∀ s, (F s).QTame)
    (hInter : ∀ s r, Nonempty
      (RealInterleaving (nndist s.1 r.1) (F s) (F r)))
    {R : ℝ} (hR : 0 < R) :
    Nonempty (WindowPartialMatching
      (essentialWindowPointPairMap
        (LocallyFiniteDecoratedDiagram.ofQModule
          (hqt (⟨0, le_rfl, ε.coe_nonneg⟩ : RealInterleaving.InterpolationTime ε))) R)
      (essentialWindowPointPairMap
        (LocallyFiniteDecoratedDiagram.ofQModule
          (hqt (⟨(ε : ℝ), ε.coe_nonneg, le_rfl⟩ : RealInterleaving.InterpolationTime ε))) R)
      (essentialWindowExit R) (ε : ℝ)) := by
  let point := fun s =>
    essentialWindowPointPairMap (LocallyFiniteDecoratedDiagram.ofQModule (hqt s)) R
  exact exists_global_window_partial_matching point (essentialWindowExit R)
    essentialWindowExit_le_add_dist
    (by
      intro s
      exact essentialWindow_interpolating_local_partial F hqt hInter hR s)

private theorem finiteWindow_iso_bijection
    {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) (hN : N.QTame) (e : M ≅ N)
    {R h : ℝ} (hR : 0 < R) (hh : 0 < h)
    [FM : Fintype (finiteWindowTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R h)]
    [FN : Fintype (finiteWindowTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hN) R h)] :
    ∃ f : finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R h →
        finiteWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R h,
      Function.Bijective f ∧
      ∀ x, finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x =
        finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R h (f x) := by
  classical
  obtain ⟨f, hf, hclose, hcover⟩ := finiteWindow_interleaving_matching hM hN
    (RealInterleaving.ofIso e) hR hh
    (by intro x; simpa using finiteWindowExit_pos_of_mem (D :=
      LocallyFiniteDecoratedDiagram.ofQModule hM) (x := x))
    (by intro x y hne; simpa using (dist_pos.mpr hne))
  have hsurj : Function.Surjective f := by
    intro y
    have hyexit : 0 < finiteWindowExit R h
        (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R h y) :=
      finiteWindowExit_pos_of_mem
    obtain ⟨x, hxy⟩ := hcover y (by simpa using hyexit)
    exact ⟨x, hxy⟩
  have hpoint : ∀ x,
      finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x =
        finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R h (f x) := by
    intro x
    have hdist : dist
        (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x)
        (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R h (f x)) ≤ 0 :=
      by simpa using hclose x
    have hzero : dist
        (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R h x)
        (finiteWindowPointMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R h (f x)) = 0 :=
      le_antisymm hdist (dist_nonneg)
    exact dist_eq_zero.mp hzero
  exact ⟨f, ⟨hf, hsurj⟩, hpoint⟩

private theorem essentialWindow_iso_bijection
    {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) (hN : N.QTame) (e : M ≅ N)
    {R : ℝ} (hR : 0 < R)
    [FM : Fintype (essentialWindowTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hM) R)]
    [FN : Fintype (essentialWindowTokens
      (LocallyFiniteDecoratedDiagram.ofQModule hN) R)] :
    ∃ f : essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hM) R →
        essentialWindowTokens (LocallyFiniteDecoratedDiagram.ofQModule hN) R,
      Function.Bijective f ∧
      ∀ x, essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hM) R x =
        essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hN) R (f x) := by
  classical
  obtain ⟨f, hf, hclose, hcover⟩ := essentialWindow_interleaving_matching hM hN
    (RealInterleaving.ofIso e) hR
    (by intro x; simpa using essentialWindowExit_pos_of_mem (D :=
      LocallyFiniteDecoratedDiagram.ofQModule hM) (x := x))
    (by intro x y hne; simpa using (dist_pos.mpr hne))
  have hsurj : Function.Surjective f := by
    intro y
    have hyexit : 0 < essentialWindowExit R
        (essentialWindowPointPairMap (LocallyFiniteDecoratedDiagram.ofQModule hN) R y) :=
      essentialWindowExit_pos_of_mem
    obtain ⟨x, hxy⟩ := hcover y (by simpa using hyexit)
    exact ⟨x, hxy⟩
  have hpoint : ∀ x,
      essentialWindowPointPairMap (LocallyFiniteDecoratedDiagram.ofQModule hM) R x =
        essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hN) R (f x) := by
    intro x
    have hdist : dist
        (essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hM) R x)
        (essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hN) R (f x)) ≤ 0 :=
      by simpa using hclose x
    have hzero : dist
        (essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hM) R x)
        (essentialWindowPointPairMap
          (LocallyFiniteDecoratedDiagram.ofQModule hN) R (f x)) = 0 :=
      le_antisymm hdist (dist_nonneg)
    exact dist_eq_zero.mp hzero
  exact ⟨f, ⟨hf, hsurj⟩, hpoint⟩

private theorem exists_finset_real_upper_bound {α : Type*}
    (s : Finset α) (f : α → ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ x ∈ s, f x ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert a s has ih =>
    obtain ⟨B, hB0, hB⟩ := ih
    refine ⟨max (f a) B, le_trans hB0 (le_max_right _ _), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hx
    · rw [hxa]
      exact le_max_left _ _
    · exact (hB x hx).trans (le_max_right _ _)

private theorem exists_positive_half_bound_finset {α : Type*}
    (s : Finset α) (g : α → ℝ) (hg : ∀ x ∈ s, 0 < g x) :
    ∃ ρ, 0 < ρ ∧ ∀ x ∈ s, 2 * ρ < g x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s has ih =>
    obtain ⟨ρ, hρ, hρs⟩ := ih (by
      intro x hx
      exact hg x (Finset.mem_insert_of_mem hx))
    have hga : 0 < g a := hg a (by simp)
    refine ⟨min ρ (g a / 4), lt_min hρ (by positivity), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hx
    · rw [hxa]
      have hle := min_le_right ρ (g a / 4)
      nlinarith
    · have hle := min_le_left ρ (g a / 4)
      nlinarith [hρs x hx]

private theorem finitePairCost_le_of_dist {p q : ℝ × ℝ} {δ : ℝ}
    (h : dist p q ≤ δ) :
    finitePairCost p q ≤ ENNReal.ofReal δ := by
  have hreal : max |p.1 - q.1| |p.2 - q.2| ≤ δ := by
    simpa [Prod.dist_eq, Real.dist_eq] using h
  simpa [finitePairCost] using ENNReal.ofReal_le_ofReal hreal

private theorem essentialPairCost_le_of_birth_dist {b c δ : ℝ}
    (h : |b - c| ≤ δ) :
    essentialPairCost b c ≤ ENNReal.ofReal δ := by
  exact ENNReal.ofReal_le_ofReal h

/-- The concrete finite-edge-set conclusion of finite saturation: both edge sets
are injective on each side, have the stated bottleneck costs, and cover the
prescribed finite tokens on both diagrams. -/
def FiniteSaturatingMatching (ε : ℝ≥0) (Dₘ Dₙ : LocallyFiniteDecoratedDiagram)
    (Fₘ : Finset Dₘ.finiteOccurrences) (Fₙ : Finset Dₙ.finiteOccurrences)
    (Eₘ : Finset Dₘ.essentialOccurrences) (Eₙ : Finset Dₙ.essentialOccurrences) :
    Prop :=
  ∃ FEdges : Finset (Dₘ.finiteOccurrences × Dₙ.finiteOccurrences),
    (∀ a b c, (a, b) ∈ FEdges → (a, c) ∈ FEdges → b = c) ∧
    (∀ a b c, (a, b) ∈ FEdges → (c, b) ∈ FEdges → a = c) ∧
    (∀ a b, (a, b) ∈ FEdges →
      finitePairCost (Dₘ.finitePoint a) (Dₙ.finitePoint b) ≤ ENNReal.ofReal (ε : ℝ)) ∧
    (∀ a, a ∈ Fₘ → ∃ b, (a, b) ∈ FEdges) ∧
    (∀ b, b ∈ Fₙ → ∃ a, (a, b) ∈ FEdges) ∧
    ∃ EEdges : Finset (Dₘ.essentialOccurrences × Dₙ.essentialOccurrences),
      (∀ a b c, (a, b) ∈ EEdges → (a, c) ∈ EEdges → b = c) ∧
      (∀ a b c, (a, b) ∈ EEdges → (c, b) ∈ EEdges → a = c) ∧
      (∀ a b, (a, b) ∈ EEdges →
        essentialPairCost (Dₘ.essentialBirth a) (Dₙ.essentialBirth b) ≤
          ENNReal.ofReal (ε : ℝ)) ∧
      (∀ a, a ∈ Eₘ → ∃ b, (a, b) ∈ EEdges) ∧
      (∀ b, b ∈ Eₙ → ∃ a, (a, b) ∈ EEdges)

/-- An actual q-tame interleaving admits finite partial matching edge sets that
saturate any prescribed finite set of finite-death tokens longer than 2ε and
any prescribed finite set of essential tokens on each side. The edge sets are
injective in both coordinates; finite-pair and essential-birth costs are at most
ε. No matching or decomposition hypothesis is part of the input. -/
theorem RealInterleaving.exists_finite_saturating_matching
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (i : RealInterleaving ε M N) (hM : M.QTame) (hN : N.QTame)
    (F_M : Finset ((LocallyFiniteDecoratedDiagram.ofQModule hM).finiteOccurrences))
    (F_N : Finset ((LocallyFiniteDecoratedDiagram.ofQModule hN).finiteOccurrences))
    (hLongM : ∀ x ∈ F_M, 2 * (ε : ℝ) <
      ((LocallyFiniteDecoratedDiagram.ofQModule hM).finitePoint x).2 -
        ((LocallyFiniteDecoratedDiagram.ofQModule hM).finitePoint x).1)
    (hLongN : ∀ x ∈ F_N, 2 * (ε : ℝ) <
      ((LocallyFiniteDecoratedDiagram.ofQModule hN).finitePoint x).2 -
        ((LocallyFiniteDecoratedDiagram.ofQModule hN).finitePoint x).1)
    (E_M : Finset ((LocallyFiniteDecoratedDiagram.ofQModule hM).essentialOccurrences))
    (E_N : Finset ((LocallyFiniteDecoratedDiagram.ofQModule hN).essentialOccurrences)) :
    FiniteSaturatingMatching ε
      (LocallyFiniteDecoratedDiagram.ofQModule hM)
      (LocallyFiniteDecoratedDiagram.ofQModule hN) F_M F_N E_M E_N := by
  classical
  let Dₘ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hM
  let Dₙ : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hN
  let bm := fun x : Dₘ.finiteOccurrences =>
    max |(Dₘ.finitePoint x).1| |(Dₘ.finitePoint x).2|
  let bn := fun x : Dₙ.finiteOccurrences =>
    max |(Dₙ.finitePoint x).1| |(Dₙ.finitePoint x).2|
  let em := fun x : Dₘ.essentialOccurrences => |Dₘ.essentialBirth x|
  let en := fun x : Dₙ.essentialOccurrences => |Dₙ.essentialBirth x|
  obtain ⟨Bₘ, hBₘ0, hBₘ⟩ := exists_finset_real_upper_bound F_M bm
  obtain ⟨Bₙ, hBₙ0, hBₙ⟩ := exists_finset_real_upper_bound F_N bn
  obtain ⟨Cₘ, hCₘ0, hCₘ⟩ := exists_finset_real_upper_bound E_M em
  obtain ⟨Cₙ, hCₙ0, hCₙ⟩ := exists_finset_real_upper_bound E_N en
  let B := max Bₘ (max Bₙ (max Cₘ Cₙ))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact le_trans hBₘ0 (le_max_left _ _)
  have hBₘle : Bₘ ≤ B := by
    dsimp [B]
    exact le_max_left _ _
  have hBₙle : Bₙ ≤ B := by
    dsimp [B]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hCₘle : Cₘ ≤ B := by
    dsimp [B]
    calc
      Cₘ ≤ max Cₘ Cₙ := le_max_left _ _
      _ ≤ max Bₙ (max Cₘ Cₙ) := le_max_right _ _
      _ ≤ B := le_max_right _ _
  have hCₙle : Cₙ ≤ B := by
    dsimp [B]
    calc
      Cₙ ≤ max Cₘ Cₙ := le_max_right _ _
      _ ≤ max Bₙ (max Cₘ Cₙ) := le_max_right _ _
      _ ≤ B := le_max_right _ _
  let R := B + (ε : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; linarith
  let gₘ := fun x : Dₘ.finiteOccurrences =>
    (Dₘ.finitePoint x).2 - (Dₘ.finitePoint x).1 - 2 * (ε : ℝ)
  let gₙ := fun x : Dₙ.finiteOccurrences =>
    (Dₙ.finitePoint x).2 - (Dₙ.finitePoint x).1 - 2 * (ε : ℝ)
  obtain ⟨ρₘ, hρₘ, hgapₘ⟩ :=
    exists_positive_half_bound_finset F_M gₘ (by
      intro x hx
      dsimp [gₘ]
      linarith [hLongM x hx])
  obtain ⟨ρₙ, hρₙ, hgapₙ⟩ :=
    exists_positive_half_bound_finset F_N gₙ (by
      intro x hx
      dsimp [gₙ]
      linarith [hLongN x hx])
  let h := min ρₘ ρₙ
  have hh : 0 < h := lt_min hρₘ hρₙ
  have hgapM (x : Dₘ.finiteOccurrences) (hx : x ∈ F_M) :
      h < gₘ x := by
    have hle : h ≤ ρₘ := min_le_left _ _
    have hg := hgapₘ x hx
    dsimp [gₘ]
    linarith
  have hgapN (x : Dₙ.finiteOccurrences) (hx : x ∈ F_N) :
      h < gₙ x := by
    have hle : h ≤ ρₙ := min_le_right _ _
    have hg := hgapₙ x hx
    dsimp [gₙ]
    linarith
  have hwinM (x : Dₘ.finiteOccurrences) (hx : x ∈ F_M) :
      finiteWindowPoint R h (Dₘ.finitePoint x) := by
    have hBM := hBₘ x hx
    have hbR : |(Dₘ.finitePoint x).1| < R := by
      have hle : |(Dₘ.finitePoint x).1| ≤ Bₘ :=
        (le_max_left _ _).trans hBM
      dsimp [R]
      linarith
    have hdR : |(Dₘ.finitePoint x).2| < R := by
      have hle : |(Dₘ.finitePoint x).2| ≤ Bₘ :=
        (le_max_right _ _).trans hBM
      dsimp [R]
      linarith
    have hlen : h < (Dₘ.finitePoint x).2 - (Dₘ.finitePoint x).1 := by
      have := hgapM x hx
      dsimp [gₘ] at this
      linarith
    exact ⟨hbR, hdR, hlen⟩
  have hwinN (x : Dₙ.finiteOccurrences) (hx : x ∈ F_N) :
      finiteWindowPoint R h (Dₙ.finitePoint x) := by
    have hBN := hBₙ x hx
    have hbR : |(Dₙ.finitePoint x).1| < R := by
      have hle : |(Dₙ.finitePoint x).1| ≤ Bₙ :=
        (le_max_left _ _).trans hBN
      dsimp [R]
      linarith
    have hdR : |(Dₙ.finitePoint x).2| < R := by
      have hle : |(Dₙ.finitePoint x).2| ≤ Bₙ :=
        (le_max_right _ _).trans hBN
      dsimp [R]
      linarith
    have hlen : h < (Dₙ.finitePoint x).2 - (Dₙ.finitePoint x).1 := by
      have := hgapN x hx
      dsimp [gₙ] at this
      linarith
    exact ⟨hbR, hdR, hlen⟩
  have hwinEM (x : Dₘ.essentialOccurrences) (hx : x ∈ E_M) :
      |Dₘ.essentialBirth x| < R := by
    have hle : |Dₘ.essentialBirth x| ≤ Cₘ := hCₘ x hx
    dsimp [R]
    linarith [le_trans hle hCₘle]
  have hwinEN (x : Dₙ.essentialOccurrences) (hx : x ∈ E_N) :
      |Dₙ.essentialBirth x| < R := by
    have hle : |Dₙ.essentialBirth x| ≤ Cₙ := hCₙ x hx
    dsimp [R]
    linarith [le_trans hle hCₙle]
  have hExitFM (x : Dₘ.finiteOccurrences) (hx : x ∈ F_M) :
      (ε : ℝ) < finiteWindowExit R h (Dₘ.finitePoint x) := by
    have hxwin := hwinM x hx
    have hb : (ε : ℝ) < R - |(Dₘ.finitePoint x).1| := by
      have hpoint : |(Dₘ.finitePoint x).1| ≤ B := by
        exact (le_max_left _ _).trans ((hBₘ x hx).trans hBₘle)
      dsimp [R]
      linarith
    have hd : (ε : ℝ) < R - |(Dₘ.finitePoint x).2| := by
      have hpoint : |(Dₘ.finitePoint x).2| ≤ B := by
        exact (le_max_right _ _).trans ((hBₘ x hx).trans hBₘle)
      dsimp [R]
      linarith
    have hg : (ε : ℝ) <
        ((Dₘ.finitePoint x).2 - (Dₘ.finitePoint x).1 - h) / 2 := by
      have hmargin := hgapM x hx
      dsimp [gₘ] at hmargin
      linarith
    unfold finiteWindowExit
    exact lt_min_iff.mpr ⟨hb, lt_min_iff.mpr ⟨hd, hg⟩⟩
  have hExitFN (x : Dₙ.finiteOccurrences) (hx : x ∈ F_N) :
      (ε : ℝ) < finiteWindowExit R h (Dₙ.finitePoint x) := by
    have hxwin := hwinN x hx
    have hb : (ε : ℝ) < R - |(Dₙ.finitePoint x).1| := by
      have hpoint : |(Dₙ.finitePoint x).1| ≤ B := by
        exact (le_max_left _ _).trans ((hBₙ x hx).trans hBₙle)
      dsimp [R]
      linarith
    have hd : (ε : ℝ) < R - |(Dₙ.finitePoint x).2| := by
      have hpoint : |(Dₙ.finitePoint x).2| ≤ B := by
        exact (le_max_right _ _).trans ((hBₙ x hx).trans hBₙle)
      dsimp [R]
      linarith
    have hg : (ε : ℝ) <
        ((Dₙ.finitePoint x).2 - (Dₙ.finitePoint x).1 - h) / 2 := by
      have hmargin := hgapN x hx
      dsimp [gₙ] at hmargin
      linarith
    unfold finiteWindowExit
    exact lt_min_iff.mpr ⟨hb, lt_min_iff.mpr ⟨hd, hg⟩⟩
  have hExitEM (x : Dₘ.essentialOccurrences) (hx : x ∈ E_M) :
      (ε : ℝ) < essentialWindowExit R
        (essentialWindowPointPairMap Dₘ R ⟨x, hwinEM x hx⟩) := by
    have hpoint : |Dₘ.essentialBirth x| ≤ B := (hCₘ x hx).trans hCₘle
    have hcoord : (ε : ℝ) < R - |Dₘ.essentialBirth x| := by
      dsimp [R]
      linarith
    have hcoord' : (ε : ℝ) <
        R - |cutEndpoint x.1.1| := by
      simpa [LocallyFiniteDecoratedDiagram.essentialBirth] using hcoord
    simpa [essentialWindowExit, essentialWindowPointPairMap,
      essentialWindowBirthMap] using hcoord'
  have hExitEN (x : Dₙ.essentialOccurrences) (hx : x ∈ E_N) :
      (ε : ℝ) < essentialWindowExit R
        (essentialWindowPointPairMap Dₙ R ⟨x, hwinEN x hx⟩) := by
    have hpoint : |Dₙ.essentialBirth x| ≤ B := (hCₙ x hx).trans hCₙle
    have hcoord : (ε : ℝ) < R - |Dₙ.essentialBirth x| := by
      dsimp [R]
      linarith
    have hcoord' : (ε : ℝ) <
        R - |cutEndpoint x.1.1| := by
      simpa [LocallyFiniteDecoratedDiagram.essentialBirth] using hcoord
    simpa [essentialWindowExit, essentialWindowPointPairMap,
      essentialWindowBirthMap] using hcoord'
  let s₀ : RealInterleaving.InterpolationTime ε := ⟨0, le_rfl, ε.coe_nonneg⟩
  let s₁ : RealInterleaving.InterpolationTime ε := ⟨(ε : ℝ), ε.coe_nonneg, le_rfl⟩
  obtain ⟨F, hStart, hEnd, hqt, hInter⟩ :=
    RealInterleaving.exists_qTame_interpolating_family i hM hN
  obtain ⟨eStart⟩ := hStart
  obtain ⟨eEnd⟩ := hEnd
  let D₀ : LocallyFiniteDecoratedDiagram :=
    LocallyFiniteDecoratedDiagram.ofQModule (hqt s₀)
  let D₁ : LocallyFiniteDecoratedDiagram :=
    LocallyFiniteDecoratedDiagram.ofQModule (hqt s₁)
  let IM := finiteWindowTokens Dₘ R h
  let IN := finiteWindowTokens Dₙ R h
  let I₀ := finiteWindowTokens D₀ R h
  let I₁ := finiteWindowTokens D₁ R h
  let JM := essentialWindowTokens Dₘ R
  let JN := essentialWindowTokens Dₙ R
  let J₀ := essentialWindowTokens D₀ R
  let J₁ := essentialWindowTokens D₁ R
  letI : Finite IM := finiteWindowTokens_finite Dₘ hR hh
  letI : Fintype IM := Fintype.ofFinite IM
  letI : Finite IN := finiteWindowTokens_finite Dₙ hR hh
  letI : Fintype IN := Fintype.ofFinite IN
  letI : Finite I₀ := finiteWindowTokens_finite D₀ hR hh
  letI : Fintype I₀ := Fintype.ofFinite I₀
  letI : Finite I₁ := finiteWindowTokens_finite D₁ hR hh
  letI : Fintype I₁ := Fintype.ofFinite I₁
  letI : Finite JM := essentialWindowTokens_finite hM hR
  letI : Fintype JM := Fintype.ofFinite JM
  letI : Finite JN := essentialWindowTokens_finite hN hR
  letI : Fintype JN := Fintype.ofFinite JN
  letI : Finite J₀ := essentialWindowTokens_finite (hqt s₀) hR
  letI : Fintype J₀ := Fintype.ofFinite J₀
  letI : Finite J₁ := essentialWindowTokens_finite (hqt s₁) hR
  letI : Fintype J₁ := Fintype.ofFinite J₁
  obtain ⟨f₀, hbij₀, hpoint₀⟩ :=
    finiteWindow_iso_bijection hM (hqt s₀) eStart.symm hR hh
  obtain ⟨f₁, hbij₁, hpoint₁⟩ :=
    finiteWindow_iso_bijection (hqt s₁) hN eEnd hR hh
  let u₀ : IM ≃ I₀ := Equiv.ofBijective f₀ hbij₀
  let u₁ : I₁ ≃ IN := Equiv.ofBijective f₁ hbij₁
  have hpoint₀' (x : IM) :
      finiteWindowPointMap Dₘ R h x =
        finiteWindowPointMap D₀ R h (u₀ x) := by
    simpa [u₀] using hpoint₀ x
  have hpoint₁' (x : I₁) :
      finiteWindowPointMap D₁ R h x =
        finiteWindowPointMap Dₙ R h (u₁ x) := by
    simpa [u₁] using hpoint₁ x
  obtain ⟨g₀, hessbij₀, hesspoint₀⟩ :=
    essentialWindow_iso_bijection hM (hqt s₀) eStart.symm hR
  obtain ⟨g₁, hessbij₁, hesspoint₁⟩ :=
    essentialWindow_iso_bijection (hqt s₁) hN eEnd hR
  let v₀ : JM ≃ J₀ := Equiv.ofBijective g₀ hessbij₀
  let v₁ : J₁ ≃ JN := Equiv.ofBijective g₁ hessbij₁
  have hesspoint₀' (x : JM) :
      essentialWindowPointPairMap Dₘ R x =
        essentialWindowPointPairMap D₀ R (v₀ x) := by
    simpa [v₀] using hesspoint₀ x
  have hesspoint₁' (x : J₁) :
      essentialWindowPointPairMap D₁ R x =
        essentialWindowPointPairMap Dₙ R (v₁ x) := by
    simpa [v₁] using hesspoint₁ x
  obtain ⟨mF⟩ := finiteWindow_interpolating_global_partial F hqt hInter hR hh
  obtain ⟨mE⟩ := essentialWindow_interpolating_global_partial F hqt hInter hR
  let fF : IM → Option IN := fun x => (mF.map (u₀ x)).map u₁
  let fE : JM → Option JN := fun x => (mE.map (v₀ x)).map v₁
  let FWindowEdges : Finset (IM × IN) :=
    (Finset.univ : Finset (IM × IN)).filter fun p => fF p.1 = some p.2
  let FEdges : Finset (Dₘ.finiteOccurrences × Dₙ.finiteOccurrences) :=
    FWindowEdges.image fun p => (p.1.1, p.2.1)
  let EWindowEdges : Finset (JM × JN) :=
    (Finset.univ : Finset (JM × JN)).filter fun p => fE p.1 = some p.2
  let EEdges : Finset (Dₘ.essentialOccurrences × Dₙ.essentialOccurrences) :=
    EWindowEdges.image fun p => (p.1.1, p.2.1)
  have hFSpec (x : IM) (y : IN) :
      fF x = some y ↔ ∃ z : I₁, mF.map (u₀ x) = some z ∧ u₁ z = y := by
    dsimp [fF]
    cases hz : mF.map (u₀ x) <;> simp [hz]
  have hFInjective : ∀ x x' y, fF x = some y → fF x' = some y → x = x' := by
    intro x x' y hx hx'
    obtain ⟨z, hzx, hzy⟩ := (hFSpec x y).mp hx
    obtain ⟨z', hzx', hzy'⟩ := (hFSpec x' y).mp hx'
    have hzz' : z = z' := u₁.injective (hzy.trans hzy'.symm)
    subst z'
    exact u₀.injective (mF.injective hzx hzx')
  have hFEdgeMem (x : IM) (y : IN) (hxy : fF x = some y) :
      (x.1, y.1) ∈ FEdges := by
    apply Finset.mem_image.mpr
    refine ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩
  have hFEdgeOut {p : Dₘ.finiteOccurrences × Dₙ.finiteOccurrences}
      (hab : p ∈ FEdges) :
      ∃ x : IM, ∃ y : IN, x.1 = p.1 ∧ y.1 = p.2 ∧ fF x = some y := by
    obtain ⟨p, hp, hpair⟩ := Finset.mem_image.mp hab
    rcases p with ⟨x, y⟩
    have hxy : fF x = some y := (Finset.mem_filter.mp hp).2
    exact ⟨x, y, congrArg Prod.fst hpair, congrArg Prod.snd hpair, hxy⟩
  have hFEdgeCost (x : IM) (y : IN) (hxy : fF x = some y) :
      finitePairCost (Dₘ.finitePoint x.1) (Dₙ.finitePoint y.1) ≤
        ENNReal.ofReal (ε : ℝ) := by
    obtain ⟨z, hz, hzy⟩ := (hFSpec x y).mp hxy
    have hedge := mF.edge hz
    have hmetric : dist (finiteWindowPointMap Dₘ R h x)
        (finiteWindowPointMap Dₙ R h y) ≤ (ε : ℝ) := by
      calc
        _ = dist (finiteWindowPointMap D₀ R h (u₀ x))
            (finiteWindowPointMap D₁ R h z) := by
              rw [← hzy, ← hpoint₀' x, ← hpoint₁' z]
        _ ≤ (ε : ℝ) := hedge
    have hdist : dist (Dₘ.finitePoint x.1) (Dₙ.finitePoint y.1) ≤ (ε : ℝ) := by
      simpa [finiteWindowPointMap] using hmetric
    exact finitePairCost_le_of_dist hdist
  have hFSourceCover (x : Dₘ.finiteOccurrences) (hx : x ∈ F_M) :
      ∃ y, (x, y) ∈ FEdges := by
    let xw : IM := ⟨x, hwinM x hx⟩
    have hExit : (ε : ℝ) <
        finiteWindowExit R h (finiteWindowPointMap D₀ R h (u₀ xw)) := by
      rw [← hpoint₀' xw]
      simpa [finiteWindowPointMap] using hExitFM x hx
    have hnot : mF.map (u₀ xw) ≠ none := by
      intro hnone
      have hbad := mF.sourceUnmatched (u₀ xw) hnone
      linarith
    obtain ⟨z, hmap⟩ : ∃ z : I₁, mF.map (u₀ xw) = some z := by
      cases hz : mF.map (u₀ xw) with
      | none => exact (hnot hz).elim
      | some z => exact ⟨z, rfl⟩
    have hxy : fF xw = some (u₁ z) := by simp [fF, hmap]
    exact ⟨(u₁ z).1, by simpa [xw] using hFEdgeMem xw (u₁ z) hxy⟩
  have hFTargetCover (y : Dₙ.finiteOccurrences) (hy : y ∈ F_N) :
      ∃ x, (x, y) ∈ FEdges := by
    let yw : IN := ⟨y, hwinN y hy⟩
    have hExit : (ε : ℝ) <
        finiteWindowExit R h (finiteWindowPointMap D₁ R h (u₁.symm yw)) := by
      have hp := hpoint₁' (u₁.symm yw)
      have hback : u₁ (u₁.symm yw) = yw := u₁.apply_symm_apply _
      have hp' : finiteWindowPointMap D₁ R h (u₁.symm yw) =
          finiteWindowPointMap Dₙ R h yw := by simpa [hback] using hp
      rw [hp']
      simpa [finiteWindowPointMap] using hExitFN y hy
    have hhit : ∃ z : I₀, mF.map z = some (u₁.symm yw) := by
      by_contra hnone
      have hmiss : ∀ z : I₀, mF.map z ≠ some (u₁.symm yw) := by
        intro z hz
        exact hnone ⟨z, hz⟩
      have hbad := mF.targetUnmatched (u₁.symm yw) hmiss
      linarith
    obtain ⟨z, hz⟩ := hhit
    let xw : IM := u₀.symm z
    have hxy : fF xw = some yw := by
      simp [fF, xw, hz]
    exact ⟨xw.1, by simpa [yw] using hFEdgeMem xw yw hxy⟩
  have hFLeftInj : ∀ a b c, (a, b) ∈ FEdges → (a, c) ∈ FEdges → b = c := by
    intro a b c hab hac
    obtain ⟨x, y, hxa, hyb, hxy⟩ := hFEdgeOut hab
    obtain ⟨x', z, hxa', hzc, hxz⟩ := hFEdgeOut hac
    have hxx : x = x' := Subtype.ext (hxa.trans hxa'.symm)
    subst x'
    have hyz : y = z := Option.some.inj (hxy.symm.trans hxz)
    calc
      b = y.1 := hyb.symm
      _ = z.1 := congrArg Subtype.val hyz
      _ = c := hzc
  have hFRightInj : ∀ a b c, (a, b) ∈ FEdges → (c, b) ∈ FEdges → a = c := by
    intro a b c hab hcb
    obtain ⟨x, y, hxa, hyb, hxy⟩ := hFEdgeOut hab
    obtain ⟨z, y', hzc, hyb', hzy⟩ := hFEdgeOut hcb
    have hyy : y = y' := Subtype.ext (hyb.trans hyb'.symm)
    subst y'
    have hxz : x = z := hFInjective x z y hxy hzy
    calc
      a = x.1 := hxa.symm
      _ = z.1 := congrArg Subtype.val hxz
      _ = c := hzc
  have hESpec (x : JM) (y : JN) :
      fE x = some y ↔ ∃ z : J₁, mE.map (v₀ x) = some z ∧ v₁ z = y := by
    dsimp [fE]
    cases hz : mE.map (v₀ x) <;> simp [hz]
  have hEInjective : ∀ x x' y, fE x = some y → fE x' = some y → x = x' := by
    intro x x' y hx hx'
    obtain ⟨z, hzx, hzy⟩ := (hESpec x y).mp hx
    obtain ⟨z', hzx', hzy'⟩ := (hESpec x' y).mp hx'
    have hzz' : z = z' := v₁.injective (hzy.trans hzy'.symm)
    subst z'
    exact v₀.injective (mE.injective hzx hzx')
  have hEEdgeMem (x : JM) (y : JN) (hxy : fE x = some y) :
      (x.1, y.1) ∈ EEdges := by
    apply Finset.mem_image.mpr
    refine ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩
  have hEEdgeOut {p : Dₘ.essentialOccurrences × Dₙ.essentialOccurrences}
      (hab : p ∈ EEdges) :
      ∃ x : JM, ∃ y : JN, x.1 = p.1 ∧ y.1 = p.2 ∧ fE x = some y := by
    obtain ⟨p, hp, hpair⟩ := Finset.mem_image.mp hab
    rcases p with ⟨x, y⟩
    have hxy : fE x = some y := (Finset.mem_filter.mp hp).2
    exact ⟨x, y, congrArg Prod.fst hpair, congrArg Prod.snd hpair, hxy⟩
  have hEEdgeCost (x : JM) (y : JN) (hxy : fE x = some y) :
      essentialPairCost (Dₘ.essentialBirth x.1) (Dₙ.essentialBirth y.1) ≤
        ENNReal.ofReal (ε : ℝ) := by
    obtain ⟨z, hz, hzy⟩ := (hESpec x y).mp hxy
    have hedge := mE.edge hz
    have hmetric : dist (essentialWindowPointPairMap Dₘ R x)
        (essentialWindowPointPairMap Dₙ R y) ≤ (ε : ℝ) := by
        calc
          _ = dist (essentialWindowPointPairMap D₀ R (v₀ x))
              (essentialWindowPointPairMap D₁ R z) := by
                rw [← hzy, ← hesspoint₀' x, ← hesspoint₁' z]
          _ ≤ (ε : ℝ) := hedge
    have habs : |Dₘ.essentialBirth x.1 - Dₙ.essentialBirth y.1| ≤ (ε : ℝ) := by
      simpa [essentialWindowPointPairMap, essentialWindowBirthMap,
        LocallyFiniteDecoratedDiagram.essentialBirth, essentialPair_dist_eq_abs] using hmetric
    exact essentialPairCost_le_of_birth_dist habs
  have hESourceCover (x : Dₘ.essentialOccurrences) (hx : x ∈ E_M) :
      ∃ y, (x, y) ∈ EEdges := by
    let xw : JM := ⟨x, hwinEM x hx⟩
    have hExit : (ε : ℝ) <
        essentialWindowExit R
          (essentialWindowPointPairMap D₀ R (v₀ xw)) := by
      rw [← hesspoint₀' xw]
      simpa [xw] using hExitEM x hx
    have hnot : mE.map (v₀ xw) ≠ none := by
      intro hnone
      have hbad := mE.sourceUnmatched (v₀ xw) hnone
      linarith
    obtain ⟨z, hmap⟩ : ∃ z : J₁, mE.map (v₀ xw) = some z := by
      cases hz : mE.map (v₀ xw) with
      | none => exact (hnot hz).elim
      | some z => exact ⟨z, rfl⟩
    have hxy : fE xw = some (v₁ z) := by simp [fE, hmap]
    exact ⟨(v₁ z).1, by simpa [xw] using hEEdgeMem xw (v₁ z) hxy⟩
  have hETargetCover (y : Dₙ.essentialOccurrences) (hy : y ∈ E_N) :
      ∃ x, (x, y) ∈ EEdges := by
    let yw : JN := ⟨y, hwinEN y hy⟩
    have hExit : (ε : ℝ) <
        essentialWindowExit R
          (essentialWindowPointPairMap D₁ R (v₁.symm yw)) := by
      have hp := hesspoint₁' (v₁.symm yw)
      have hback : v₁ (v₁.symm yw) = yw := v₁.apply_symm_apply _
      have hp' : essentialWindowPointPairMap D₁ R (v₁.symm yw) =
          essentialWindowPointPairMap Dₙ R yw := by simpa [hback] using hp
      rw [hp']
      simpa [yw] using hExitEN y hy
    have hhit : ∃ z : J₀, mE.map z = some (v₁.symm yw) := by
      by_contra hnone
      have hmiss : ∀ z : J₀, mE.map z ≠ some (v₁.symm yw) := by
        intro z hz
        exact hnone ⟨z, hz⟩
      have hbad := mE.targetUnmatched (v₁.symm yw) hmiss
      linarith
    obtain ⟨z, hz⟩ := hhit
    let xw : JM := v₀.symm z
    have hxy : fE xw = some yw := by simp [fE, xw, hz]
    exact ⟨xw.1, by simpa [yw] using hEEdgeMem xw yw hxy⟩
  have hELeftInj : ∀ a b c, (a, b) ∈ EEdges → (a, c) ∈ EEdges → b = c := by
    intro a b c hab hac
    obtain ⟨x, y, hxa, hyb, hxy⟩ := hEEdgeOut hab
    obtain ⟨x', z, hxa', hzc, hxz⟩ := hEEdgeOut hac
    have hxx : x = x' := Subtype.ext (hxa.trans hxa'.symm)
    subst x'
    have hyz : y = z := Option.some.inj (hxy.symm.trans hxz)
    calc
      b = y.1 := hyb.symm
      _ = z.1 := congrArg Subtype.val hyz
      _ = c := hzc
  have hERightInj : ∀ a b c, (a, b) ∈ EEdges → (c, b) ∈ EEdges → a = c := by
    intro a b c hab hcb
    obtain ⟨x, y, hxa, hyb, hxy⟩ := hEEdgeOut hab
    obtain ⟨z, y', hzc, hyb', hzy⟩ := hEEdgeOut hcb
    have hyy : y = y' := Subtype.ext (hyb.trans hyb'.symm)
    subst y'
    have hxz : x = z := hEInjective x z y hxy hzy
    calc
      a = x.1 := hxa.symm
      _ = z.1 := congrArg Subtype.val hxz
      _ = c := hzc
  refine ⟨FEdges, hFLeftInj, hFRightInj, ?_, hFSourceCover, hFTargetCover,
    ⟨EEdges, hELeftInj, hERightInj, ?_, hESourceCover, hETargetCover⟩⟩
  · intro a b hab
    obtain ⟨x, y, hxa, hyb, hxy⟩ := hFEdgeOut hab
    change x.1 = a at hxa
    change y.1 = b at hyb
    subst a
    subst b
    exact hFEdgeCost x y hxy
  · intro a b hab
    obtain ⟨x, y, hxa, hyb, hxy⟩ := hEEdgeOut hab
    change x.1 = a at hxa
    change y.1 = b at hyb
    subst a
    subst b
    exact hEEdgeCost x y hxy

end

end TDA.Persistence
