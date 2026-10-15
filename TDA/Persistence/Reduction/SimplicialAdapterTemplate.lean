import TDA.Persistence.Reduction.SimplicialAdapterBarcode

/-! The reducer's zero-based face pairs and essential births form the canonical
face template, and their monotone grade evaluation is the actual diagram. -/

set_option maxHeartbeats 800000

universe u w

namespace TDA.Persistence.Reduction

open TDA.Persistence TDA.Simplicial TDA.Filtration

variable {V : Type u} [LinearOrder V]
variable {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TotalFace K)]
variable {f : FilterFunction K α}
variable (k : Type u) [Field k] [DecidableEq k]

/-- The reducer's finite row/death-column pairs are exactly the fixed face
template, with their zero-based indices and occurrence multiplicities. -/
theorem faceTemplatePairs_eq_pivotIndexPairs (e : CompatibleOrder f) (p : ℕ) :
    faceTemplatePairs k e p =
      pivotIndexPairs (faceDegree e) (actualReducedBoundary k e) p := by
  let h := actualReduction_normalForm k e
  unfold faceTemplatePairs
  rw [← actualPivotBarcode_eq_facePrefixBarcode k e p]
  change (actualPivotBarcode k e p).filterMap finiteIndexPair = _
  exact pivotBarcode_pairs (faceDegree e) (actualReducedBoundary k e)
    h.2.2.2.1 p

/-- Essential template indices are the reducer's unpaired zero columns. -/
theorem faceTemplateEssential_eq_pivotEssentialIndices
    (e : CompatibleOrder f) (p : ℕ) :
    faceTemplateEssential k e p =
      pivotEssentialIndices (faceDegree e) (actualReducedBoundary k e) p := by
  let h := actualReduction_normalForm k e
  unfold faceTemplateEssential
  rw [← actualPivotBarcode_eq_facePrefixBarcode k e p]
  change (actualPivotBarcode k e p).filterMap essentialIndex = _
  exact pivotBarcode_essential (faceDegree e) (actualReducedBoundary k e)
    h.2.2.2.1 p

/-- Evaluate the reducer's fixed face-index occurrences at a monotone grade.
Only finite pairs with equal grade endpoints disappear. -/
noncomputable def evaluatePivotTemplate {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (_hg : Monotone (g.value ∘ e.enum)) (p : ℕ) : Diagram β where
  points :=
    (((pivotIndexPairs (faceDegree e) (actualReducedBoundary k e) p).map
      (pairValues g e)).filter (fun q => q.1 ≠ q.2)).map
      (fun q => (q.1, (q.2 : WithTop β))) +
    ((pivotEssentialIndices (faceDegree e) (actualReducedBoundary k e) p).map
      (birthValue g e)).map (fun b => (b, (⊤ : WithTop β)))
  offDiagonal := by
    intro q hq
    rcases Multiset.mem_add.mp hq with hq | hq
    · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hq
      simpa using (Multiset.mem_filter.mp hv).2
    · obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hq
      simp

/-- Monotone evaluation of actual reducer pairs gives the actual sublevel
persistence diagram, including the justified constant tail after all faces. -/
theorem evaluatePivotTemplate_eq_dgm {β : Type*} [LinearOrder β]
    (e : CompatibleOrder f) (g : FilterFunction K β)
    (hg : Monotone (g.value ∘ e.enum)) (p : ℕ) :
    evaluatePivotTemplate k e g hg p = dgm k g p := by
  rw [← evaluateFaceTemplate_eq_dgm k e g hg p]
  apply Diagram.ext
  change (((pivotIndexPairs (faceDegree e) (actualReducedBoundary k e) p).map
      (pairValues g e)).filter (fun q => q.1 ≠ q.2)).map
      (fun q => (q.1, (q.2 : WithTop β))) +
    ((pivotEssentialIndices (faceDegree e) (actualReducedBoundary k e) p).map
      (birthValue g e)).map (fun b => (b, (⊤ : WithTop β))) = _
  rw [← faceTemplatePairs_eq_pivotIndexPairs k e p,
    ← faceTemplateEssential_eq_pivotEssentialIndices k e p]
  rfl

/-- Compatible reorderings may have different index pairs, but they yield the
same grade-level diagram for a common monotone filter. -/
theorem evaluatePivotTemplate_order_independent {β : Type*} [LinearOrder β]
    (e₁ e₂ : CompatibleOrder f) (g : FilterFunction K β)
    (h₁ : Monotone (g.value ∘ e₁.enum))
    (h₂ : Monotone (g.value ∘ e₂.enum)) (p : ℕ) :
    evaluatePivotTemplate k e₁ g h₁ p =
      evaluatePivotTemplate k e₂ g h₂ p := by
  rw [evaluatePivotTemplate_eq_dgm k e₁ g h₁ p,
    evaluatePivotTemplate_eq_dgm k e₂ g h₂ p]

end TDA.Persistence.Reduction
