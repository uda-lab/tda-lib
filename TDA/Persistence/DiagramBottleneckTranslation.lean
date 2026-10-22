import TDA.Persistence.DiagramBottleneckLaws
import TDA.Persistence.SublevelDiagramTransport

set_option autoImplicit false

namespace TDA.Persistence

open scoped ENNReal
universe u

/-- Translate both coordinates of a finite-or-essential diagram point by `c`.
The top death sentinel remains top. -/
def translateDiagramPoint (c : ℝ) (p : ℝ × WithTop ℝ) : ℝ × WithTop ℝ :=
  (p.1 + c, WithTop.map (fun x => x + c) p.2)

/-- Translate every occurrence of a finite diagram, preserving its multiplicity. -/
def translateDiagram (D : Diagram ℝ) (c : ℝ) : Diagram ℝ where
  points := D.points.map (translateDiagramPoint c)
  offDiagonal := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    intro heq
    cases hd : q.2 with
    | top => simp [translateDiagramPoint, hd] at heq
    | coe d =>
      have hreal : q.1 + c = d + c := by
        exact_mod_cast (by simpa [translateDiagramPoint, hd] using heq)
      have hbirth : q.1 = d := add_right_cancel hreal
      exact D.offDiagonal q hq (by rw [hd, hbirth])

private theorem finitePart_map_translate (s : Multiset (ℝ × WithTop ℝ)) (c : ℝ) :
    finitePart (s.map (translateDiagramPoint c)) =
      (finitePart s).map (fun p => (p.1 + c, p.2 + c)) := by
  simp only [finitePart, Multiset.filterMap_map, Multiset.map_filterMap]
  apply congrArg (fun f : (ℝ × WithTop ℝ) → Option (ℝ × ℝ) => s.filterMap f)
  funext p
  obtain ⟨b, d⟩ := p
  cases d <;> rfl

private theorem essentialPart_map_translate (s : Multiset (ℝ × WithTop ℝ)) (c : ℝ) :
    essentialPart (s.map (translateDiagramPoint c)) =
      (essentialPart s).map (fun b => b + c) := by
  simp only [essentialPart, Multiset.filterMap_map, Multiset.map_filterMap]
  apply congrArg (fun f : (ℝ × WithTop ℝ) → Option ℝ => s.filterMap f)
  funext p
  obtain ⟨b, d⟩ := p
  cases d <;> rfl

private theorem finitePart_translateDiagram (D : Diagram ℝ) (c : ℝ) :
    finitePart (translateDiagram D c).points =
      (finitePart D.points).map (fun p => (p.1 + c, p.2 + c)) := by
  exact finitePart_map_translate D.points c

private theorem essentialPart_translateDiagram (D : Diagram ℝ) (c : ℝ) :
    essentialPart (translateDiagram D c).points =
      (essentialPart D.points).map (fun b => b + c) := by
  exact essentialPart_map_translate D.points c

private theorem finitePairCost_translate (p : ℝ × ℝ) (c : ℝ) :
    finitePairCost p (p.1 + c, p.2 + c) = ENNReal.ofReal |c| := by
  have h₁ : p.1 - (p.1 + c) = -c := by ring
  have h₂ : p.2 - (p.2 + c) = -c := by ring
  simp [finitePairCost, h₁, h₂]

private theorem essentialPairCost_translate (b c : ℝ) :
    essentialPairCost b (b + c) = ENNReal.ofReal |c| := by
  have h : b - (b + c) = -c := by ring
  simp [essentialPairCost, h]

private theorem finiteTranslation_multiset (D : Diagram ℝ) (c : ℝ) :
    (Finset.univ : Finset D.finiteOccurrences).val.map
        (fun p => (p.1.1 + c, p.1.2 + c)) =
      (Finset.univ : Finset (translateDiagram D c).finiteOccurrences).val.map
        (fun p => p.1) := by
  calc
    _ = (finitePart D.points).map (fun p => (p.1 + c, p.2 + c)) :=
      Multiset.map_univ _ _
    _ = finitePart (translateDiagram D c).points := by
      exact (finitePart_translateDiagram D c).symm
    _ = _ := (Multiset.map_univ_coe _).symm

private theorem essentialTranslation_multiset (D : Diagram ℝ) (c : ℝ) :
    (Finset.univ : Finset D.essentialOccurrences).val.map (fun b => b.1 + c) =
      (Finset.univ : Finset (translateDiagram D c).essentialOccurrences).val.map
        (fun b => b.1) := by
  calc
    _ = (essentialPart D.points).map (fun b => b + c) :=
      Multiset.map_univ _ _
    _ = essentialPart (translateDiagram D c).points := by
      exact (essentialPart_translateDiagram D c).symm
    _ = _ := (Multiset.map_univ_coe _).symm

/-- Translate finite occurrence labels bijectively, retaining repeated endpoint pairs. -/
noncomputable def finiteTranslationEquiv (D : Diagram ℝ) (c : ℝ) :
    D.finiteOccurrences ≃ (translateDiagram D c).finiteOccurrences := by
  classical
  exact (presentationEquiv
    (fun p : D.finiteOccurrences => (p.1.1 + c, p.1.2 + c))
    (fun p : (translateDiagram D c).finiteOccurrences => p.1)
    (finiteTranslation_multiset D c)).1

/-- Both finite endpoints move by the declared translation. -/
theorem finiteTranslationEquiv_value (D : Diagram ℝ) (c : ℝ)
    (p : D.finiteOccurrences) :
    (finiteTranslationEquiv D c p).1 = (p.1.1 + c, p.1.2 + c) := by
  classical
  exact (presentationEquiv
    (fun q : D.finiteOccurrences => (q.1.1 + c, q.1.2 + c))
    (fun q : (translateDiagram D c).finiteOccurrences => q.1)
    (finiteTranslation_multiset D c)).2 p

/-- Translate essential occurrence labels bijectively; their deaths remain top. -/
noncomputable def essentialTranslationEquiv (D : Diagram ℝ) (c : ℝ) :
    D.essentialOccurrences ≃ (translateDiagram D c).essentialOccurrences := by
  classical
  exact (presentationEquiv
    (fun b : D.essentialOccurrences => b.1 + c)
    (fun b : (translateDiagram D c).essentialOccurrences => b.1)
    (essentialTranslation_multiset D c)).1

/-- Essential translation changes only the birth. -/
theorem essentialTranslationEquiv_value (D : Diagram ℝ) (c : ℝ)
    (b : D.essentialOccurrences) :
    (essentialTranslationEquiv D c b).1 = b.1 + c := by
  classical
  exact (presentationEquiv
    (fun a : D.essentialOccurrences => a.1 + c)
    (fun a : (translateDiagram D c).essentialOccurrences => a.1)
    (essentialTranslation_multiset D c)).2 b

/-- The complete occurrence matching supplied by translation, without an existence input. -/
noncomputable def translatedMatching (D : Diagram ℝ) (c : ℝ) :
    OccurrenceMatching D.finiteOccurrences (translateDiagram D c).finiteOccurrences
      D.essentialOccurrences (translateDiagram D c).essentialOccurrences := by
  let e := finiteTranslationEquiv D c
  refine ⟨fun i => some (e i), ?_, essentialTranslationEquiv D c⟩
  intro i i' j hi hi'
  exact e.injective ((Option.some.inj hi).trans (Option.some.inj hi').symm)

/-- The complete translation matching costs at most the displacement; an empty
matching has zero cost. -/
theorem translatedMatching_cost_le (D : Diagram ℝ) (c : ℝ) :
    (translatedMatching D c).cost (fun p => p.1) (fun p => p.1)
      (fun b => b.1) (fun b => b.1) ≤ ENNReal.ofReal |c| := by
  classical
  let M := translatedMatching D c
  apply M.cost_le_of
  · intro p
    change finitePairCost p.1 ((finiteTranslationEquiv D c p).1) ≤ _
    rw [finiteTranslationEquiv_value]
    exact le_of_eq (finitePairCost_translate p.1 c)
  · intro q
    have hmatched : ∃ p, M.finite p = some q := by
      refine ⟨(finiteTranslationEquiv D c).symm q, ?_⟩
      simp [M, translatedMatching]
    simp [hmatched]
  · intro b
    change essentialPairCost b.1 ((essentialTranslationEquiv D c b).1) ≤ _
    rw [essentialTranslationEquiv_value]
    exact le_of_eq (essentialPairCost_translate b.1 c)

/-- Translating all occurrences by `c` gives the usual matching upper bound. Equal
points remain distinct occurrences, and finite pairs are not assumed to be ordered. -/
theorem bottleneck_translate_le (D : Diagram ℝ) (c : ℝ) :
    bottleneck D (translateDiagram D c) ≤ ENNReal.ofReal |c| :=
  (bottleneck_le_matching D (translateDiagram D c) (translatedMatching D c)).trans
    (translatedMatching_cost_le D c)

private theorem bottleneck_translate_lower_of_min (D : Diagram ℝ) (c : ℝ)
    (M : OccurrenceMatching D.finiteOccurrences (translateDiagram D c).finiteOccurrences
      D.essentialOccurrences (translateDiagram D c).essentialOccurrences)
    (b : D.essentialOccurrences)
    (hmin : ∀ a : D.essentialOccurrences, b.1 ≤ a.1) (hc : 0 ≤ c) :
    ENNReal.ofReal |c| ≤
      M.cost (fun p => p.1) (fun p => p.1) (fun a => a.1) (fun a => a.1) := by
  let e := essentialTranslationEquiv D c
  let b' := M.essential b
  let a := e.symm b'
  have htranslate : b'.1 = a.1 + c := by
    have hback : e a = b' := e.apply_symm_apply b'
    rw [← hback]
    exact essentialTranslationEquiv_value D c a
  have horder : b.1 ≤ a.1 := hmin a
  have habs : c ≤ |b.1 - b'.1| := by
    rw [htranslate, abs_sub_comm]
    have hnonneg : 0 ≤ a.1 + c - b.1 := by linarith
    rw [abs_of_nonneg hnonneg]
    linarith
  have hpair : ENNReal.ofReal |c| ≤ essentialPairCost b.1 b'.1 := by
    unfold essentialPairCost
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonneg hc]
    exact habs
  exact hpair.trans (M.essential_le_cost
    (fun p => p.1) (fun p => p.1) (fun a => a.1) (fun a => a.1) b)

private theorem bottleneck_translate_lower_of_max (D : Diagram ℝ) (c : ℝ)
    (M : OccurrenceMatching D.finiteOccurrences (translateDiagram D c).finiteOccurrences
      D.essentialOccurrences (translateDiagram D c).essentialOccurrences)
    (b : D.essentialOccurrences)
    (hmax : ∀ a : D.essentialOccurrences, a.1 ≤ b.1) (hc : c ≤ 0) :
    ENNReal.ofReal |c| ≤
      M.cost (fun p => p.1) (fun p => p.1) (fun a => a.1) (fun a => a.1) := by
  let e := essentialTranslationEquiv D c
  let b' := M.essential b
  let a := e.symm b'
  have htranslate : b'.1 = a.1 + c := by
    have hback : e a = b' := e.apply_symm_apply b'
    rw [← hback]
    exact essentialTranslationEquiv_value D c a
  have horder : a.1 ≤ b.1 := hmax a
  have habs : -c ≤ |b.1 - b'.1| := by
    rw [htranslate]
    have hnonneg : 0 ≤ b.1 - (a.1 + c) := by linarith
    rw [abs_of_nonneg hnonneg]
    linarith
  have hpair : ENNReal.ofReal |c| ≤ essentialPairCost b.1 b'.1 := by
    unfold essentialPairCost
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonpos hc]
    exact habs
  exact hpair.trans (M.essential_le_cost
    (fun p => p.1) (fun p => p.1) (fun a => a.1) (fun a => a.1) b)

/-- Every admissible occurrence matching has cost at least `|c|` when the finite
essential-birth multiset is nonempty. The proof uses its minimum for `c ≥ 0` and
its maximum for `c ≤ 0`, so repeated extrema and arbitrary multiplicities are allowed. -/
theorem bottleneck_translate_ge_of_essential (D : Diagram ℝ) (c : ℝ)
    (hne : essentialPart D.points ≠ 0) :
    ENNReal.ofReal |c| ≤ bottleneck D (translateDiagram D c) := by
  classical
  have hcard : 0 < Fintype.card D.essentialOccurrences := by
    simpa only [Multiset.card_coe] using (Multiset.card_pos.mpr hne)
  have hocc : Nonempty D.essentialOccurrences := Fintype.card_pos_iff.mp hcard
  obtain ⟨bmin, _, hmin⟩ := Finset.univ.exists_min_image
    (fun b : D.essentialOccurrences => b.1) (Finset.univ_nonempty_iff.mpr hocc)
  obtain ⟨bmax, _, hmax⟩ := Finset.univ.exists_max_image
    (fun b : D.essentialOccurrences => b.1) (Finset.univ_nonempty_iff.mpr hocc)
  unfold bottleneck
  apply le_iInf
  intro M
  by_cases hc : 0 ≤ c
  · exact bottleneck_translate_lower_of_min D c M bmin
      (fun b => hmin b (Finset.mem_univ b)) hc
  · exact bottleneck_translate_lower_of_max D c M bmax
      (fun b => hmax b (Finset.mem_univ b)) (le_of_lt (lt_of_not_ge hc))

/-- Exact bottleneck displacement under a common translation, provided an essential
occurrence exists. This holds for arbitrary finite parts, including reversed pairs. -/
theorem bottleneck_translate_eq_of_essential (D : Diagram ℝ) (c : ℝ)
    (hne : essentialPart D.points ≠ 0) :
    bottleneck D (translateDiagram D c) = ENNReal.ofReal |c| :=
  le_antisymm (bottleneck_translate_le D c)
    (bottleneck_translate_ge_of_essential D c hne)

/-- Add a constant to every face value of a finite-complex filter. -/
def translateFilterFunction {V : Type*} [LinearOrder V]
    {K : PreAbstractSimplicialComplex V}
    (f : TDA.Filtration.FilterFunction K ℝ) (c : ℝ) :
    TDA.Filtration.FilterFunction K ℝ where
  value σ := f.value σ + c
  mono h := by simpa [add_comm] using add_le_add_right (f.mono h) c

/-- The attained-grade diagram transport theorem identifies the shifted diagram
with the pointwise translation of the original one. -/
theorem dgm_translateFilterFunction (k : Type u) [Field k]
    {V : Type u} [LinearOrder V]
    {K : PreAbstractSimplicialComplex V}
    [Fintype (TDA.Simplicial.TotalFace K)]
    (f : TDA.Filtration.FilterFunction K ℝ) (n : ℕ) (c : ℝ) :
    dgm k (translateFilterFunction f c) n = translateDiagram (dgm k f n) c := by
  apply Diagram.ext
  let φ : ℝ → ℝ := fun a => a + c
  have hφ : StrictMonoOn φ (Set.range f.value) := by
    intro a ha b hb hab
    dsimp [φ]
    linarith
  have hvalue : ∀ σ : TDA.Simplicial.TotalFace K,
      (translateFilterFunction f c).value σ = φ (f.value σ) := by
    intro σ
    rfl
  change (dgm k (translateFilterFunction f c) n).points =
    (dgm k f n).points.map
      (fun p => (p.1 + c, WithTop.map (fun a : ℝ => a + c) p.2))
  exact dgm_points_map_of_strictMonoOn k f (translateFilterFunction f c)
    φ hφ hvalue n

/-- The constant-shift bottleneck bound for any finite-complex diagram. -/
theorem bottleneck_dgm_translateFilterFunction_le (k : Type u) [Field k]
    {V : Type u} [LinearOrder V]
    {K : PreAbstractSimplicialComplex V}
    [Fintype (TDA.Simplicial.TotalFace K)]
    (f : TDA.Filtration.FilterFunction K ℝ) (n : ℕ) (c : ℝ) :
    bottleneck (dgm k f n) (dgm k (translateFilterFunction f c) n) ≤
      ENNReal.ofReal |c| := by
  rw [dgm_translateFilterFunction]
  exact bottleneck_translate_le (dgm k f n) c

/-- Exact constant-shift displacement for a degree diagram whenever it has an
essential occurrence. -/
theorem bottleneck_dgm_translateFilterFunction_eq_of_essential (k : Type u) [Field k]
    {V : Type u} [LinearOrder V]
    {K : PreAbstractSimplicialComplex V}
    [Fintype (TDA.Simplicial.TotalFace K)]
    (f : TDA.Filtration.FilterFunction K ℝ) (n : ℕ) (c : ℝ)
    (hne : essentialPart (dgm k f n).points ≠ 0) :
    bottleneck (dgm k f n) (dgm k (translateFilterFunction f c) n) =
      ENNReal.ofReal |c| := by
  rw [dgm_translateFilterFunction]
  exact bottleneck_translate_eq_of_essential (dgm k f n) c hne

/-- Zero translation fixes the diagram, without selecting occurrence labels. -/
@[simp] theorem translateDiagram_zero (D : Diagram ℝ) : translateDiagram D 0 = D := by
  apply Diagram.ext
  change D.points.map (translateDiagramPoint 0) = D.points
  have h : translateDiagramPoint 0 = id := by
    funext p
    rcases p with ⟨b, d⟩
    cases d <;> simp [translateDiagramPoint]
  rw [h, Multiset.map_id]

/-- Successive endpoint translations add, including essential deaths. -/
theorem translateDiagram_add (D : Diagram ℝ) (a b : ℝ) :
    translateDiagram (translateDiagram D a) b = translateDiagram D (a + b) := by
  apply Diagram.ext
  change (D.points.map (translateDiagramPoint a)).map (translateDiagramPoint b) = _
  rw [Multiset.map_map]
  congr 1
  funext p
  rcases p with ⟨x, d⟩
  cases d with
  | top => exact Prod.ext (add_assoc x a b) rfl
  | coe d =>
    change ((x + a) + b, (((d + a) + b : ℝ) : WithTop ℝ)) =
      (x + (a + b), ((d + (a + b) : ℝ) : WithTop ℝ))
    simp only [add_assoc]

/-- The inverse finite translation adds back the displacement, without merging labels. -/
theorem finiteTranslationEquiv_symm_value (D : Diagram ℝ) (a : ℝ)
    (p : (translateDiagram D a).finiteOccurrences) :
    ((finiteTranslationEquiv D a).symm p).1 = (p.1.1 - a, p.1.2 - a) := by
  have h := finiteTranslationEquiv_value D a ((finiteTranslationEquiv D a).symm p)
  simp only [Equiv.apply_symm_apply] at h
  apply Prod.ext
  · have := congrArg Prod.fst h
    dsimp at this ⊢
    linarith
  · have := congrArg Prod.snd h
    dsimp at this ⊢
    linarith

/-- The inverse essential translation adds back the birth displacement. -/
theorem essentialTranslationEquiv_symm_value (D : Diagram ℝ) (a : ℝ)
    (p : (translateDiagram D a).essentialOccurrences) :
    ((essentialTranslationEquiv D a).symm p).1 = p.1 - a := by
  have h := essentialTranslationEquiv_value D a ((essentialTranslationEquiv D a).symm p)
  simp only [Equiv.apply_symm_apply] at h
  linarith

namespace OccurrenceMatching

variable {D E : Diagram ℝ}

/-- Return a translated target to its original occurrence labels. This operation
uses a supplied matching and makes no existence or cost claim about it. -/
noncomputable def untranslateTarget (a : ℝ)
    (A : OccurrenceMatching D.finiteOccurrences (translateDiagram E a).finiteOccurrences
      D.essentialOccurrences (translateDiagram E a).essentialOccurrences) :
    OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences :=
  A.relabel (Equiv.refl _) (finiteTranslationEquiv E a)
    (Equiv.refl _) (essentialTranslationEquiv E a)

/-- A selected target is exactly its translated occurrence before relabelling. -/
theorem untranslateTarget_finite_eq_some_iff (a : ℝ)
    (A : OccurrenceMatching D.finiteOccurrences (translateDiagram E a).finiteOccurrences
      D.essentialOccurrences (translateDiagram E a).essentialOccurrences)
    (i : D.finiteOccurrences) (j : E.finiteOccurrences) :
    (A.untranslateTarget a).finite i = some j ↔
      A.finite i = some (finiteTranslationEquiv E a j) := by
  change (A.finite i).map (finiteTranslationEquiv E a).symm = some j ↔ _
  cases h : A.finite i with
  | none => simp
  | some q => simp only [Option.map_some, Option.some.injEq]; exact Equiv.symm_apply_eq _

/-- Relabelling the target keeps exactly the same unmatched sources. -/
theorem untranslateTarget_finite_eq_none_iff (a : ℝ)
    (A : OccurrenceMatching D.finiteOccurrences (translateDiagram E a).finiteOccurrences
      D.essentialOccurrences (translateDiagram E a).essentialOccurrences)
    (i : D.finiteOccurrences) :
    (A.untranslateTarget a).finite i = none ↔ A.finite i = none := by
  change (A.finite i).map _ = none ↔ _
  exact Option.map_eq_none_iff

/-- Relabelling preserves the selected target range by the same occurrence bijection. -/
theorem untranslateTarget_mem_range_iff (a : ℝ)
    (A : OccurrenceMatching D.finiteOccurrences (translateDiagram E a).finiteOccurrences
      D.essentialOccurrences (translateDiagram E a).essentialOccurrences)
    (j : E.finiteOccurrences) :
    (∃ i, (A.untranslateTarget a).finite i = some j) ↔
      ∃ i, A.finite i = some (finiteTranslationEquiv E a j) := by
  exact exists_congr fun i => untranslateTarget_finite_eq_some_iff a A i j

/-- The essential target's birth is returned by subtracting the translation. -/
theorem untranslateTarget_essential_value (a : ℝ)
    (A : OccurrenceMatching D.finiteOccurrences (translateDiagram E a).finiteOccurrences
      D.essentialOccurrences (translateDiagram E a).essentialOccurrences)
    (i : D.essentialOccurrences) :
    ((A.untranslateTarget a).essential i).1 = (A.essential i).1 - a :=
  essentialTranslationEquiv_symm_value E a (A.essential i)

end OccurrenceMatching


end TDA.Persistence
