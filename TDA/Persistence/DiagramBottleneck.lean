import TDA.Persistence.DiagramLaws

/-! Bottleneck geometry for finite persistence diagrams. Occurrences, rather than point
values, are the labels of a matching. In particular equal points remain distinct. -/

namespace TDA.Persistence

open scoped ENNReal

/-- The distance from a finite pair to the diagonal in the maximum norm. -/
noncomputable def diagonalCost (p : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal (|p.2 - p.1| / 2)

/-- The maximum-norm cost of matching two finite pairs. -/
def finitePairCost (p q : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (max |p.1 - q.1| |p.2 - q.2|)

/-- The cost of matching two essential births. -/
def essentialPairCost (b c : ℝ) : ℝ≥0∞ := ENNReal.ofReal |b - c|

theorem diagonalCost_le_max (b d a : ℝ) :
    |d - b| / 2 ≤ max |b - a| |d - a| := by
  have h := abs_sub_le d a b
  rw [abs_sub_comm a b] at h
  have h₁ : |b - a| ≤ max |b - a| |d - a| := le_max_left _ _
  have h₂ : |d - a| ≤ max |b - a| |d - a| := le_max_right _ _
  linarith

theorem diagonalCost_midpoint (b d : ℝ) :
    |d - b| / 2 = max |b - (b + d) / 2| |d - (b + d) / 2| := by
  have h₁ : b - (b + d) / 2 = (b - d) / 2 := by ring
  have h₂ : d - (b + d) / 2 = (d - b) / 2 := by ring
  rw [h₁, h₂, abs_div, abs_div, abs_sub_comm b d]
  simp

/-- A partial injection on finite occurrences and a total bijection on essential
occurrences. The finite map's unselected source and target labels go to the diagonal. -/
structure OccurrenceMatching (F₁ F₂ E₁ E₂ : Type*) where
  finite : F₁ → Option F₂
  finite_injective : ∀ i i' j, finite i = some j → finite i' = some j → i = i'
  essential : E₁ ≃ E₂

namespace OccurrenceMatching

variable {F₁ F₂ E₁ E₂ : Type*}
variable [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]

@[ext] theorem ext {M N : OccurrenceMatching F₁ F₂ E₁ E₂}
    (hf : M.finite = N.finite) (he : M.essential = N.essential) : M = N := by
  cases M
  cases N
  cases hf
  cases he
  rfl

/-- Reindex both sides of a matching by occurrence-label equivalences. -/
def relabel {F₁' F₂' E₁' E₂' : Type*}
    (u : F₁' ≃ F₁) (v : F₂' ≃ F₂)
    (s : E₁' ≃ E₁) (t : E₂' ≃ E₂)
    (M : OccurrenceMatching F₁ F₂ E₁ E₂) :
    OccurrenceMatching F₁' F₂' E₁' E₂' where
  finite i := (M.finite (u i)).map v.symm
  finite_injective := by
    intro i i' j hi hi'
    have hb (k : F₁') (hk : (M.finite (u k)).map v.symm = some j) :
        M.finite (u k) = some (v j) := by
      cases h : M.finite (u k) with
      | none => simp [h] at hk
      | some q =>
        simp only [h, Option.map_some, Option.some.injEq] at hk
        simpa [h, hk] using (v.apply_symm_apply q).symm
    exact u.injective (M.finite_injective (u i) (u i') (v j) (hb i hi) (hb i' hi'))
  essential := (s.trans M.essential).trans t.symm

private theorem sup_univ_reindex {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ≥0∞) :
    (Finset.univ : Finset A).sup (fun a => f (e a)) =
      (Finset.univ : Finset B).sup f := by
  classical
  apply le_antisymm
  · exact Finset.sup_le fun a _ => Finset.le_sup (Finset.mem_univ (e a))
  · apply Finset.sup_le
    intro b _
    simpa using (Finset.le_sup (s := (Finset.univ : Finset A))
      (f := fun a => f (e a)) (Finset.mem_univ (e.symm b)))

/-- The maximum of all matched and unmatched occurrence costs, with empty maximum zero. -/
noncomputable def cost (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) : ℝ≥0∞ :=
  letI := Classical.decEq F₁
  letI := Classical.decEq F₂
  max ((Finset.univ : Finset F₁).sup fun i =>
      match M.finite i with
      | some j => finitePairCost (x i) (y j)
      | none => diagonalCost (x i))
    (max ((Finset.univ : Finset F₂).sup fun j =>
      if ∃ i, M.finite i = some j then 0 else diagonalCost (y j))
      ((Finset.univ : Finset E₁).sup fun k => essentialPairCost (b k) (c (M.essential k))))

/-- Reindexing all four occurrence sets preserves the matching cost. -/
theorem cost_relabel {F₁' F₂' E₁' E₂' : Type*}
    [Fintype F₁'] [Fintype F₂'] [Fintype E₁'] [Fintype E₂']
    (u : F₁' ≃ F₁) (v : F₂' ≃ F₂)
    (s : E₁' ≃ E₁) (t : E₂' ≃ E₂)
    (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) :
    (M.relabel u v s t).cost (x ∘ u) (y ∘ v) (b ∘ s) (c ∘ t) =
      M.cost x y b c := by
  classical
  unfold cost
  congr 1
  · have hf (i : F₁') :
        (match (M.relabel u v s t).finite i with
          | some j => finitePairCost (x (u i)) (y (v j))
          | none => diagonalCost (x (u i))) =
        (match M.finite (u i) with
          | some j => finitePairCost (x (u i)) (y j)
          | none => diagonalCost (x (u i))) := by
        cases h : M.finite (u i) with
        | none => simp [relabel, h]
        | some j => simp [relabel, h]
    have h := sup_univ_reindex u
        (fun i => match M.finite i with
          | some j => finitePairCost (x i) (y j)
          | none => diagonalCost (x i))
    calc
      _ = (Finset.univ : Finset F₁').sup (fun i =>
          match M.finite (u i) with
          | some j => finitePairCost (x (u i)) (y j)
          | none => diagonalCost (x (u i))) := by
            apply Finset.sup_congr rfl
            intro i _
            simpa only [Function.comp_apply] using hf i
      _ = _ := h
  · congr 1
    · have hh (j : F₂') :
          (∃ i : F₁', (M.relabel u v s t).finite i = some j) ↔
            ∃ i : F₁, M.finite i = some (v j) := by
        constructor
        · rintro ⟨i, hi⟩
          refine ⟨u i, ?_⟩
          cases h : M.finite (u i) with
          | none => simp [relabel, h] at hi
          | some k =>
            simp [relabel, h] at hi
            have hk : k = v j := by simpa using congrArg v hi
            simpa [hk] using h
        · rintro ⟨i, hi⟩
          exact ⟨u.symm i, by simp [relabel, hi]⟩
      have hv := sup_univ_reindex v
        (fun j => if ∃ i : F₁, M.finite i = some j then 0 else diagonalCost (y j))
      simpa only [Function.comp_apply, hh] using hv
    · have hs := sup_univ_reindex s
        (fun i => essentialPairCost (b i) (c (M.essential i)))
      simpa [relabel, Function.comp_apply] using hs

/-- Relabelling is a bijection of admissible matchings. -/
noncomputable def relabelEquiv {F₁' F₂' E₁' E₂' : Type*}
    [Fintype F₁'] [Fintype F₂'] [Fintype E₁'] [Fintype E₂']
    (u : F₁' ≃ F₁) (v : F₂' ≃ F₂)
    (s : E₁' ≃ E₁) (t : E₂' ≃ E₂) :
    OccurrenceMatching F₁ F₂ E₁ E₂ ≃ OccurrenceMatching F₁' F₂' E₁' E₂' where
  toFun := relabel u v s t
  invFun := relabel u.symm v.symm s.symm t.symm
  left_inv := by
    intro M
    apply ext
    · funext i
      cases h : M.finite i with
      | none => simp [relabel, h]
      | some j => simp [relabel, h]
    · ext i
      simp [relabel]
  right_inv := by
    intro M
    apply ext
    · funext i
      cases h : M.finite i with
      | none => simp [relabel, h]
      | some j => simp [relabel, h]
    · ext i
      simp [relabel]

noncomputable instance : Fintype (OccurrenceMatching F₁ F₂ E₁ E₂) := by
  classical
  have hi : Function.Injective
      (fun M : OccurrenceMatching F₁ F₂ E₁ E₂ => (M.finite, M.essential)) := by
    intro M N h
    cases M with
    | mk mf mi me =>
      cases N with
      | mk nf ni ne =>
        cases h
        rfl
  exact Fintype.ofInjective _ hi

end OccurrenceMatching

/-- A finite type labels the occurrences of the multiset of its values. -/
noncomputable def fintypeOccurrenceEquiv {A B : Type*} [Fintype A]
    [DecidableEq A] [DecidableEq B] (f : A → B) :
    A ≃ ((Finset.univ : Finset A).val.map f) :=
  (show A ≃ (Finset.univ : Finset A).val from {
    toFun := fun a => ⟨a, ⟨0, by simp⟩⟩
    invFun := fun a => a.1
    left_inv := by intro a; rfl
    right_inv := by
      rintro ⟨a, ⟨i, hi⟩⟩
      have hz : i = 0 := by simpa using hi
      subst i
      rfl
  }).trans ((Finset.univ : Finset A).val.mapEquiv f)

@[simp] theorem fintypeOccurrenceEquiv_value {A B : Type*}
    [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : A → B) (a : A) :
    ((fintypeOccurrenceEquiv f a : ((Finset.univ : Finset A).val.map f)) : B) = f a := by
  exact Multiset.mapEquiv_apply _ _ _

private theorem occurrenceCast_value {B : Type*} [DecidableEq B]
    {s t : Multiset B} (h : s = t) (p : s) :
    ((Equiv.cast (congrArg Multiset.ToType h) p : t) : B) =
      (p : B) := by
  cases h
  rfl

/-- Equality of value multisets yields a bijection of occurrence labels that
preserves every value, including repeated values. -/
noncomputable def presentationEquiv {A C B : Type*}
    [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C] [DecidableEq B]
    (f : A → B) (g : C → B)
    (h : (Finset.univ : Finset A).val.map f =
      (Finset.univ : Finset C).val.map g) :
    { e : A ≃ C // ∀ a, g (e a) = f a } := by
  let ef := fintypeOccurrenceEquiv f
  let eg := fintypeOccurrenceEquiv g
  let ec := Equiv.cast (congrArg Multiset.ToType h)
  let e : A ≃ C := (ef.trans ec).trans eg.symm
  refine ⟨e, ?_⟩
  intro a
  have hf := fintypeOccurrenceEquiv_value f a
  have hg := fintypeOccurrenceEquiv_value g (e a)
  have he : eg (e a) = ec (ef a) := by simp [e]
  calc
    g (e a) = (eg (e a) : B) := hg.symm
    _ = (ec (ef a) : B) := by rw [he]
    _ = (ef a : B) := occurrenceCast_value h (ef a)
    _ = f a := hf

theorem occurrenceMatching_nonempty_iff {F₁ F₂ E₁ E₂ : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂] :
    Nonempty (OccurrenceMatching F₁ F₂ E₁ E₂) ↔ Fintype.card E₁ = Fintype.card E₂ := by
  constructor
  · rintro ⟨M⟩
    exact Fintype.card_congr M.essential
  · intro h
    let e : E₁ ≃ E₂ := Fintype.equivOfCardEq h
    exact ⟨⟨fun _ => none, by simp, e⟩⟩

/-- Infimum over all finite-occurrence partial injections and essential bijections.
It is infinity when no essential bijection exists. -/
noncomputable def presentationBottleneck {F₁ F₂ E₁ E₂ : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) : ℝ≥0∞ :=
  ⨅ M : OccurrenceMatching F₁ F₂ E₁ E₂, M.cost x y b c

theorem presentationBottleneck_relabel {F₁ F₂ E₁ E₂ F₁' F₂' E₁' E₂' : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    [Fintype F₁'] [Fintype F₂'] [Fintype E₁'] [Fintype E₂']
    (u : F₁' ≃ F₁) (v : F₂' ≃ F₂)
    (s : E₁' ≃ E₁) (t : E₂' ≃ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) :
    presentationBottleneck (x ∘ u) (y ∘ v) (b ∘ s) (c ∘ t) =
      presentationBottleneck x y b c := by
  unfold presentationBottleneck
  let e := OccurrenceMatching.relabelEquiv u v s t
  calc
    (⨅ M : OccurrenceMatching F₁' F₂' E₁' E₂',
      M.cost (x ∘ u) (y ∘ v) (b ∘ s) (c ∘ t)) =
        ⨅ M : OccurrenceMatching F₁ F₂ E₁ E₂,
          (e M).cost (x ∘ u) (y ∘ v) (b ∘ s) (c ∘ t) :=
            (e.surjective.iInf_comp _).symm
    _ = ⨅ M : OccurrenceMatching F₁ F₂ E₁ E₂, M.cost x y b c := by
      apply iInf_congr
      intro M
      exact OccurrenceMatching.cost_relabel u v s t M x y b c

theorem presentationBottleneck_eq_of_multiset_eq
    {F₁ F₂ E₁ E₂ F₁' F₂' E₁' E₂' : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    [Fintype F₁'] [Fintype F₂'] [Fintype E₁'] [Fintype E₂']
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ)
    (x' : F₁' → ℝ × ℝ) (y' : F₂' → ℝ × ℝ)
    (b' : E₁' → ℝ) (c' : E₂' → ℝ)
    (hx : (Finset.univ : Finset F₁).val.map x =
      (Finset.univ : Finset F₁').val.map x')
    (hy : (Finset.univ : Finset F₂).val.map y =
      (Finset.univ : Finset F₂').val.map y')
    (hb : (Finset.univ : Finset E₁).val.map b =
      (Finset.univ : Finset E₁').val.map b')
    (hc : (Finset.univ : Finset E₂).val.map c =
      (Finset.univ : Finset E₂').val.map c') :
    presentationBottleneck x' y' b' c' = presentationBottleneck x y b c := by
  classical
  let u := (presentationEquiv x' x hx.symm).1
  let v := (presentationEquiv y' y hy.symm).1
  let s := (presentationEquiv b' b hb.symm).1
  let t := (presentationEquiv c' c hc.symm).1
  have hu : x ∘ u = x' := funext (presentationEquiv x' x hx.symm).2
  have hv : y ∘ v = y' := funext (presentationEquiv y' y hy.symm).2
  have hs : b ∘ s = b' := funext (presentationEquiv b' b hb.symm).2
  have ht : c ∘ t = c' := funext (presentationEquiv c' c hc.symm).2
  simpa only [hu, hv, hs, ht] using
    presentationBottleneck_relabel u v s t x y b c

/-- Canonical finite occurrence labels retain multiplicities, even for equal pairs. -/
abbrev Diagram.finiteOccurrences (D : Diagram ℝ) : Type := finitePart D.points

/-- Canonical essential occurrence labels retain repeated births. -/
abbrev Diagram.essentialOccurrences (D : Diagram ℝ) : Type := essentialPart D.points

noncomputable instance (D : Diagram ℝ) : Fintype D.finiteOccurrences := by
  unfold Diagram.finiteOccurrences
  infer_instance

noncomputable instance (D : Diagram ℝ) : Fintype D.essentialOccurrences := by
  unfold Diagram.essentialOccurrences
  infer_instance

/-- Bottleneck quantity on the existing `Diagram ℝ` domain. -/
noncomputable def bottleneck (D E : Diagram ℝ) : ℝ≥0∞ :=
  presentationBottleneck
    (fun p : D.finiteOccurrences => p.1)
    (fun p : E.finiteOccurrences => p.1)
    (fun b : D.essentialOccurrences => b.1)
    (fun b : E.essentialOccurrences => b.1)

theorem bottleneck_eq_presentation (D E : Diagram ℝ)
    {F₁ F₂ E₁ E₂ : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ)
    (hx : (Finset.univ : Finset F₁).val.map x = finitePart D.points)
    (hy : (Finset.univ : Finset F₂).val.map y = finitePart E.points)
    (hb : (Finset.univ : Finset E₁).val.map b = essentialPart D.points)
    (hc : (Finset.univ : Finset E₂).val.map c = essentialPart E.points) :
    bottleneck D E = presentationBottleneck x y b c := by
  classical
  unfold bottleneck
  apply (presentationBottleneck_eq_of_multiset_eq
    (fun p : D.finiteOccurrences => p.1)
    (fun p : E.finiteOccurrences => p.1)
    (fun p : D.essentialOccurrences => p.1)
    (fun p : E.essentialOccurrences => p.1)
    x y b c ?_ ?_ ?_ ?_).symm
  · exact (Multiset.map_univ_coe _).trans hx.symm
  · exact (Multiset.map_univ_coe _).trans hy.symm
  · exact (Multiset.map_univ_coe _).trans hb.symm
  · exact (Multiset.map_univ_coe _).trans hc.symm

theorem bottleneck_le_matching (D E : Diagram ℝ)
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) :
    bottleneck D E ≤
      M.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) := by
  exact iInf_le _ M

/-- Every admissible matching gives an upper bound. -/
theorem presentationBottleneck_le_cost {F₁ F₂ E₁ E₂ : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ)
    (M : OccurrenceMatching F₁ F₂ E₁ E₂) :
    presentationBottleneck x y b c ≤ M.cost x y b c := by
  exact iInf_le _ M

theorem occurrenceMatching_cost_lt_top {F₁ F₂ E₁ E₂ : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ)
    (M : OccurrenceMatching F₁ F₂ E₁ E₂) : M.cost x y b c < ⊤ := by
  classical
  unfold OccurrenceMatching.cost
  simp only [max_lt_iff, Finset.sup_lt_iff (show (0 : ℝ≥0∞) < ⊤ by simp),
    Finset.mem_univ, forall_const, true_implies]
  constructor
  · intro i
    split <;> simp [finitePairCost, diagonalCost]
  constructor
  · intro j
    split <;> simp [diagonalCost]
  · intro k
    simp [essentialPairCost]

theorem presentationBottleneck_optimal_iff {F₁ F₂ E₁ E₂ : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) :
    (∃ M : OccurrenceMatching F₁ F₂ E₁ E₂,
      M.cost x y b c = presentationBottleneck x y b c) ↔
      Fintype.card E₁ = Fintype.card E₂ := by
  classical
  constructor
  · rintro ⟨M, _⟩
    exact occurrenceMatching_nonempty_iff.mp ⟨M⟩
  · intro h
    letI : Nonempty (OccurrenceMatching F₁ F₂ E₁ E₂) :=
      occurrenceMatching_nonempty_iff.mpr h
    exact exists_eq_ciInf_of_finite

theorem presentationBottleneck_lt_top_iff {F₁ F₂ E₁ E₂ : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) :
    presentationBottleneck x y b c < ⊤ ↔
      Fintype.card E₁ = Fintype.card E₂ := by
  classical
  constructor
  · intro h
    by_contra hc
    have hempty : IsEmpty (OccurrenceMatching F₁ F₂ E₁ E₂) :=
      not_nonempty_iff.mp (fun hm => hc (occurrenceMatching_nonempty_iff.mp hm))
    simp [presentationBottleneck] at h
  · intro h
    obtain ⟨M, hm⟩ := (presentationBottleneck_optimal_iff x y b c).mpr h
    rw [← hm]
    exact occurrenceMatching_cost_lt_top x y b c M

theorem bottleneck_lt_top_iff (D E : Diagram ℝ) :
    bottleneck D E < ⊤ ↔
      (essentialPart D.points).card = (essentialPart E.points).card := by
  simpa only [bottleneck, Multiset.card_coe] using
    (presentationBottleneck_lt_top_iff
      (fun p : D.finiteOccurrences => p.1)
      (fun p : E.finiteOccurrences => p.1)
      (fun b : D.essentialOccurrences => b.1)
      (fun b : E.essentialOccurrences => b.1))

theorem bottleneck_optimal_iff (D E : Diagram ℝ) :
    (∃ M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
        D.essentialOccurrences E.essentialOccurrences,
      M.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) =
        bottleneck D E) ↔
      (essentialPart D.points).card = (essentialPart E.points).card := by
  simpa only [bottleneck, Multiset.card_coe] using
    (presentationBottleneck_optimal_iff
      (fun p : D.finiteOccurrences => p.1)
      (fun p : E.finiteOccurrences => p.1)
      (fun b : D.essentialOccurrences => b.1)
      (fun b : E.essentialOccurrences => b.1))

theorem bottleneck_eq_top_iff (D E : Diagram ℝ) :
    bottleneck D E = ⊤ ↔
      (essentialPart D.points).card ≠ (essentialPart E.points).card := by
  constructor
  · intro h hc
    have hl := (bottleneck_lt_top_iff D E).mpr hc
    simp [h] at hl
  · intro h
    by_contra hn
    have hl : bottleneck D E < ⊤ := lt_top_iff_ne_top.mpr hn
    exact h ((bottleneck_lt_top_iff D E).mp hl)

/-- Non-diagonal ordered coordinates, indexed before quotienting to a multiset. -/
abbrev NonDiagonalIndices (m : ℕ) (x : Fin m → ℝ × ℝ) :=
  { i : Fin m // (x i).1 ≠ (x i).2 }

theorem orderedQ_finite_occurrences (m n : ℕ)
    (z : (Fin m → ℝ × ℝ) × (Fin n → ℝ)) :
    (Finset.univ : Finset (NonDiagonalIndices m z.1)).val.map
      (fun i => z.1 i.1) = finitePart (orderedQ m n z).points := by
  classical
  calc
    _ = ((Finset.univ : Finset (Fin m)).filter
          (fun i => (z.1 i).1 ≠ (z.1 i).2)).val.map z.1 := by
        simpa only [Subtype.restrict_def, Function.comp_apply] using
          (Finset.univ_val_map_subtype_restrict z.1
            (fun i => (z.1 i).1 ≠ (z.1 i).2))
    _ = finitePart (orderedQ m n z).points := by
      rw [finitePart_orderedQ]
      rw [Finset.filter_val, List.ofFn_eq_map]
      change ((Finset.univ : Finset (Fin m)).val.filter
          (fun i => (z.1 i).1 ≠ (z.1 i).2)).map z.1 =
        (((List.finRange m : List (Fin m)) : Multiset (Fin m)).map z.1).filter
          (fun p => p.1 ≠ p.2)
      rw [← Finset.val_univ_fin, Multiset.filter_map]
      rfl

theorem orderedQ_essential_occurrences (m n : ℕ)
    (z : (Fin m → ℝ × ℝ) × (Fin n → ℝ)) :
    (Finset.univ : Finset (Fin n)).val.map z.2 =
      essentialPart (orderedQ m n z).points := by
  rw [essentialPart_orderedQ, List.ofFn_eq_map]
  change (Finset.univ : Finset (Fin n)).val.map z.2 =
    ((List.finRange n : List (Fin n)) : Multiset (Fin n)).map z.2
  rw [← Finset.val_univ_fin]

/-- Match exactly the indices whose finite pairs survive on both sides. -/
noncomputable def orderedOccurrenceMatching (m n : ℕ)
    (z w : (Fin m → ℝ × ℝ) × (Fin n → ℝ)) :
    OccurrenceMatching (NonDiagonalIndices m z.1) (NonDiagonalIndices m w.1)
      (Fin n) (Fin n) where
  finite i := if h : (w.1 i.1).1 ≠ (w.1 i.1).2 then some ⟨i.1, h⟩ else none
  finite_injective := by
    intro i i' j hi hi'
    by_cases h : (w.1 i.1).1 ≠ (w.1 i.1).2
    · by_cases h' : (w.1 i'.1).1 ≠ (w.1 i'.1).2
      · simp [h] at hi
        simp [h'] at hi'
        have hk : i.1 = i'.1 :=
          congrArg (fun q : NonDiagonalIndices m w.1 => q.1) (hi.trans hi'.symm)
        exact Subtype.ext hk
      · simp [h'] at hi'
    · simp [h] at hi
  essential := Equiv.refl (Fin n)

private theorem orderedQ_birth_difference_le_norm {m n : ℕ}
    (z w : (Fin m → ℝ × ℝ) × (Fin n → ℝ)) (i : Fin m) :
    |(z.1 i).1 - (w.1 i).1| ≤ ‖z - w‖ := by
  have h₁ := norm_fst_le (z.1 i - w.1 i)
  have h₂ := norm_le_pi_norm (z.1 - w.1) i
  have h₃ := norm_fst_le (z - w)
  simpa [Pi.sub_apply, Prod.fst_sub, Real.norm_eq_abs] using h₁.trans (h₂.trans h₃)

private theorem orderedQ_death_difference_le_norm {m n : ℕ}
    (z w : (Fin m → ℝ × ℝ) × (Fin n → ℝ)) (i : Fin m) :
    |(z.1 i).2 - (w.1 i).2| ≤ ‖z - w‖ := by
  have h₁ := norm_snd_le (z.1 i - w.1 i)
  have h₂ := norm_le_pi_norm (z.1 - w.1) i
  have h₃ := norm_fst_le (z - w)
  simpa [Pi.sub_apply, Prod.snd_sub, Real.norm_eq_abs] using h₁.trans (h₂.trans h₃)

private theorem orderedQ_essential_difference_le_norm {m n : ℕ}
    (z w : (Fin m → ℝ × ℝ) × (Fin n → ℝ)) (i : Fin n) :
    |z.2 i - w.2 i| ≤ ‖z - w‖ := by
  have h₁ := norm_le_pi_norm (z.2 - w.2) i
  have h₂ := norm_snd_le (z - w)
  simpa [Pi.sub_apply, Prod.snd_sub, Real.norm_eq_abs] using h₁.trans h₂

theorem orderedOccurrenceMatching_cost_le (m n : ℕ)
    (z w : (Fin m → ℝ × ℝ) × (Fin n → ℝ)) :
    (orderedOccurrenceMatching m n z w).cost
      (fun i => z.1 i.1) (fun i => w.1 i.1) z.2 w.2 ≤
      ENNReal.ofReal ‖z - w‖ := by
  classical
  unfold OccurrenceMatching.cost
  apply max_le_iff.mpr
  constructor
  · apply Finset.sup_le
    intro i _
    by_cases hw : (w.1 i.1).1 ≠ (w.1 i.1).2
    · simp only [orderedOccurrenceMatching, dif_pos hw, Option.map_some]
      apply ENNReal.ofReal_le_ofReal
      exact max_le (orderedQ_birth_difference_le_norm z w i.1)
        (orderedQ_death_difference_le_norm z w i.1)
    · have heq : (w.1 i.1).1 = (w.1 i.1).2 := of_not_not hw
      simp only [orderedOccurrenceMatching, dif_neg hw]
      apply ENNReal.ofReal_le_ofReal
      have hd := diagonalCost_le_max (z.1 i.1).1 (z.1 i.1).2 (w.1 i.1).1
      apply hd.trans
      apply max_le
      · exact orderedQ_birth_difference_le_norm z w i.1
      · simpa only [← heq] using orderedQ_death_difference_le_norm z w i.1
  · apply max_le_iff.mpr
    constructor
    · apply Finset.sup_le
      intro j _
      by_cases hm : ∃ i, (orderedOccurrenceMatching m n z w).finite i = some j
      · simp [hm]
      · have hz : (z.1 j.1).1 = (z.1 j.1).2 := by
          by_contra hn
          apply hm
          refine ⟨⟨j.1, hn⟩, ?_⟩
          simp [orderedOccurrenceMatching, j.2]
        simp only [if_neg hm]
        apply ENNReal.ofReal_le_ofReal
        have hd := diagonalCost_le_max (w.1 j.1).1 (w.1 j.1).2 (z.1 j.1).1
        apply hd.trans
        apply max_le
        · simpa only [abs_sub_comm] using orderedQ_birth_difference_le_norm z w j.1
        · simpa only [hz, abs_sub_comm] using orderedQ_death_difference_le_norm z w j.1
    · apply Finset.sup_le
      intro k _
      apply ENNReal.ofReal_le_ofReal
      exact orderedQ_essential_difference_le_norm z w k

/-- The standard maximum norm on the ordered finite-pair and essential-birth
coordinates bounds the bottleneck value, including zero-length coordinates. -/
theorem bottleneck_orderedQ_le_norm (m n : ℕ)
    (z w : (Fin m → ℝ × ℝ) × (Fin n → ℝ)) :
    bottleneck (orderedQ m n z) (orderedQ m n w) ≤
      ENNReal.ofReal ‖z - w‖ := by
  rw [bottleneck_eq_presentation (orderedQ m n z) (orderedQ m n w)
    (fun i : NonDiagonalIndices m z.1 => z.1 i.1)
    (fun i : NonDiagonalIndices m w.1 => w.1 i.1)
    z.2 w.2
    (orderedQ_finite_occurrences m n z)
    (orderedQ_finite_occurrences m n w)
    (orderedQ_essential_occurrences m n z)
    (orderedQ_essential_occurrences m n w)]
  exact (presentationBottleneck_le_cost _ _ _ _
    (orderedOccurrenceMatching m n z w)).trans
      (orderedOccurrenceMatching_cost_le m n z w)

/-- Ordered representatives may have different finite lengths or include arbitrary
diagonal coordinates; equality of their Diagram values is enough. -/
theorem bottleneck_orderedQ_eq_of_eq
    {m n m' n' k l k' l' : ℕ}
    {z : (Fin m → ℝ × ℝ) × (Fin n → ℝ)}
    {z' : (Fin m' → ℝ × ℝ) × (Fin n' → ℝ)}
    {w : (Fin k → ℝ × ℝ) × (Fin l → ℝ)}
    {w' : (Fin k' → ℝ × ℝ) × (Fin l' → ℝ)}
    (hz : orderedQ m n z = orderedQ m' n' z')
    (hw : orderedQ k l w = orderedQ k' l' w') :
    bottleneck (orderedQ m n z) (orderedQ k l w) =
      bottleneck (orderedQ m' n' z') (orderedQ k' l' w') := by
  rw [hz, hw]

theorem presentationBottleneck_singleton_empty (p : ℝ × ℝ) :
    presentationBottleneck (fun _ : Fin 1 => p)
      (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) = diagonalCost p := by
  classical
  have hc (M : OccurrenceMatching (Fin 1) (Fin 0) (Fin 0) (Fin 0)) :
      M.cost (fun _ : Fin 1 => p) Fin.elim0 Fin.elim0 Fin.elim0 = diagonalCost p := by
    have hf : M.finite = fun _ => none := by
      funext i
      cases h : M.finite i with
      | none => rfl
      | some j => exact Fin.elim0 j
    simp [OccurrenceMatching.cost, hf]
  have hM : Nonempty (OccurrenceMatching (Fin 1) (Fin 0) (Fin 0) (Fin 0)) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  simp [presentationBottleneck, hc]

theorem presentationBottleneck_constant_empty {F : Type*}
    [Fintype F] [Nonempty F] (p : ℝ × ℝ) :
    presentationBottleneck (fun _ : F => p)
      (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) = diagonalCost p := by
  classical
  have hc (M : OccurrenceMatching F (Fin 0) (Fin 0) (Fin 0)) :
      M.cost (fun _ : F => p) Fin.elim0 Fin.elim0 Fin.elim0 = diagonalCost p := by
    have hf : M.finite = fun _ => none := by
      funext i
      cases h : M.finite i with
      | none => rfl
      | some j => exact Fin.elim0 j
    simp [OccurrenceMatching.cost, hf, Finset.sup_const]
  have hM : Nonempty (OccurrenceMatching F (Fin 0) (Fin 0) (Fin 0)) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  simp [presentationBottleneck, hc]

theorem presentationBottleneck_finite_empty {F : Type*}
    [Fintype F] (x : F → ℝ × ℝ) :
    presentationBottleneck x (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) =
      (Finset.univ : Finset F).sup (fun i => diagonalCost (x i)) := by
  classical
  have hc (M : OccurrenceMatching F (Fin 0) (Fin 0) (Fin 0)) :
      M.cost x Fin.elim0 Fin.elim0 Fin.elim0 =
        (Finset.univ : Finset F).sup (fun i => diagonalCost (x i)) := by
    have hf : M.finite = fun _ => none := by
      funext i
      cases h : M.finite i with
      | none => rfl
      | some j => exact Fin.elim0 j
    simp [OccurrenceMatching.cost, hf]
  have hM : Nonempty (OccurrenceMatching F (Fin 0) (Fin 0) (Fin 0)) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  simp [presentationBottleneck, hc]

theorem presentationBottleneck_essential_singletons (b c : ℝ) :
    presentationBottleneck (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (fun _ : Fin 1 => b) (fun _ : Fin 1 => c) = essentialPairCost b c := by
  classical
  have hc (M : OccurrenceMatching (Fin 0) (Fin 0) (Fin 1) (Fin 1)) :
      M.cost Fin.elim0 Fin.elim0 (fun _ : Fin 1 => b) (fun _ : Fin 1 => c) =
        essentialPairCost b c := by
    simp [OccurrenceMatching.cost]
  have hM : Nonempty (OccurrenceMatching (Fin 0) (Fin 0) (Fin 1) (Fin 1)) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  simp [presentationBottleneck, hc]

theorem presentationBottleneck_two_equal_vs_one (p : ℝ × ℝ) :
    presentationBottleneck (fun _ : Fin 2 => p) (fun _ : Fin 1 => p)
      (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) = diagonalCost p := by
  classical
  let M₀ : OccurrenceMatching (Fin 2) (Fin 1) (Fin 0) (Fin 0) :=
    ⟨fun _ => none, by simp, Equiv.refl _⟩
  have h₀ : M₀.cost (fun _ : Fin 2 => p) (fun _ : Fin 1 => p)
      Fin.elim0 Fin.elim0 = diagonalCost p := by
    simp [OccurrenceMatching.cost, M₀]
  apply le_antisymm
  · exact (presentationBottleneck_le_cost _ _ _ _ M₀).trans_eq h₀
  · apply le_iInf
    intro M
    have hu : ∃ i : Fin 2, M.finite i = none := by
      by_cases h₁ : M.finite 0 = none
      · exact ⟨0, h₁⟩
      · by_cases h₂ : M.finite 1 = none
        · exact ⟨1, h₂⟩
        · have h₁' : M.finite 0 = some 0 := by
            cases hh : M.finite 0 with
            | none => exact (h₁ hh).elim
            | some j => fin_cases j; simpa using hh
          have h₂' : M.finite 1 = some 0 := by
            cases hh : M.finite 1 with
            | none => exact (h₂ hh).elim
            | some j => fin_cases j; simpa using hh
          have he := M.finite_injective 0 1 0 h₁' h₂'
          exact (by decide : (0 : Fin 2) ≠ 1) he |>.elim
    obtain ⟨i, hi⟩ := hu
    unfold OccurrenceMatching.cost
    apply le_trans ?_ (le_max_left _ _)
    have hle := (Finset.le_sup (s := (Finset.univ : Finset (Fin 2)))
      (f := fun i => match M.finite i with
        | some j => finitePairCost ((fun _ : Fin 2 => p) i) ((fun _ : Fin 1 => p) j)
        | none => diagonalCost ((fun _ : Fin 2 => p) i)) (Finset.mem_univ i))
    convert hle using 1
    · simp [hi]
    · apply Finset.sup_congr
      · ext j
        simp
      · intro j _
        cases h : M.finite j <;> simp [h]

/-- A finite-only diagram compared with the empty diagram has precisely the
largest of its diagonal deletion costs. -/
theorem bottleneck_finite_only_empty (D : Diagram ℝ)
    (he : essentialPart D.points = 0) :
    bottleneck D (orderedQ 0 0
      ((Fin.elim0 : Fin 0 → ℝ × ℝ), (Fin.elim0 : Fin 0 → ℝ))) =
        (Finset.univ : Finset D.finiteOccurrences).sup
          (fun p => diagonalCost p.1) := by
  classical
  have hf : (Finset.univ : Finset D.finiteOccurrences).val.map
      (fun p : D.finiteOccurrences => p.1) = finitePart D.points :=
    Multiset.map_univ_coe _
  have hz : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ × ℝ) =
        finitePart (orderedQ 0 0
          ((Fin.elim0 : Fin 0 → ℝ × ℝ), (Fin.elim0 : Fin 0 → ℝ))).points := by
    simp [finitePart_orderedQ]
  have hd : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ) = essentialPart D.points := by simp [he]
  have he' : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ) =
        essentialPart (orderedQ 0 0
          ((Fin.elim0 : Fin 0 → ℝ × ℝ), (Fin.elim0 : Fin 0 → ℝ))).points := by
    simp [essentialPart_orderedQ]
  rw [bottleneck_eq_presentation D
    (orderedQ 0 0 ((Fin.elim0 : Fin 0 → ℝ × ℝ), (Fin.elim0 : Fin 0 → ℝ)))
    (fun p : D.finiteOccurrences => p.1)
    (Fin.elim0 : Fin 0 → ℝ × ℝ)
    (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ)
    hf hz hd he']
  exact presentationBottleneck_finite_empty _

end TDA.Persistence
