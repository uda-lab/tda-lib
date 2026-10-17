import TDA.Persistence.DiagramMap
import TDA.Persistence.DiagramBottleneckTranslation
import Mathlib.Algebra.Order.Group.OrderIso

set_option autoImplicit false

/-!
# Positive scaling of real diagrams and bottleneck distances

Multiplying every finite coordinate of a real diagram by `c > 0` is the diagram map along
`OrderIso.mulLeft₀ c hc`. Every finite pair cost, diagonal cost and essential cost is
multiplied by `c`, hence so is the cost of every occurrence matching, the presentation
bottleneck and the diagram bottleneck. The bottleneck law holds for all real diagrams,
including reversed finite pairs, and includes the value `⊤` for unequal essential counts.
The merged translation operations are diagram and filter maps along `OrderIso.addRight c`.

These are library extensions proved from the merged definitions; no external theorem is
translated. The factor `c = 0` is excluded, since it sends every finite pair to the
diagonal.
-/

namespace TDA.Persistence

open scoped ENNReal
open TDA.Filtration

universe u

/-- Multiply every finite coordinate of a real diagram by a positive constant. -/
noncomputable def Diagram.scale (D : Diagram ℝ) (c : ℝ) (hc : 0 < c) : Diagram ℝ :=
  D.map (OrderIso.mulLeft₀ c hc).toOrderEmbedding

private theorem mulLeft₀_one_toOrderEmbedding :
    (OrderIso.mulLeft₀ (1 : ℝ) one_pos).toOrderEmbedding = RelEmbedding.refl (· ≤ ·) := by
  ext x
  simp

theorem Diagram.scale_one (D : Diagram ℝ) : D.scale 1 one_pos = D := by
  rw [Diagram.scale, mulLeft₀_one_toOrderEmbedding, Diagram.map_refl]

theorem Diagram.scale_scale (D : Diagram ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (D.scale a ha).scale b hb = D.scale (b * a) (mul_pos hb ha) := by
  rw [Diagram.scale, Diagram.scale, Diagram.scale, Diagram.map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Multiply both coordinates of a finite pair by `c`. -/
def scaleFinitePair (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (c * p.1, c * p.2)

private theorem finitePart_scale_points (D : Diagram ℝ) {c : ℝ} (hc : 0 < c) :
    finitePart (D.scale c hc).points = (finitePart D.points).map (scaleFinitePair c) := by
  rw [Diagram.scale, finitePart_map_points]
  rfl

private theorem essentialPart_scale_points (D : Diagram ℝ) {c : ℝ} (hc : 0 < c) :
    essentialPart (D.scale c hc).points = (essentialPart D.points).map (fun b => c * b) := by
  rw [Diagram.scale, essentialPart_map_points]
  rfl

private theorem abs_mul_sub_mul {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    |c * u - c * v| = c * |u - v| := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]

theorem finitePairCost_scale (p q : ℝ × ℝ) {c : ℝ} (hc : 0 ≤ c) :
    finitePairCost (scaleFinitePair c p) (scaleFinitePair c q) =
      ENNReal.ofReal c * finitePairCost p q := by
  unfold finitePairCost scaleFinitePair
  rw [abs_mul_sub_mul hc, abs_mul_sub_mul hc, ← mul_max_of_nonneg _ _ hc,
    ENNReal.ofReal_mul hc]

theorem diagonalCost_scale (p : ℝ × ℝ) {c : ℝ} (hc : 0 ≤ c) :
    diagonalCost (scaleFinitePair c p) = ENNReal.ofReal c * diagonalCost p := by
  unfold diagonalCost scaleFinitePair
  rw [abs_mul_sub_mul hc, mul_div_assoc, ENNReal.ofReal_mul hc]

theorem essentialPairCost_scale (b b' : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    essentialPairCost (c * b) (c * b') = ENNReal.ofReal c * essentialPairCost b b' := by
  unfold essentialPairCost
  rw [abs_mul_sub_mul hc, ENNReal.ofReal_mul hc]

namespace OccurrenceMatching

variable {F₁ F₂ E₁ E₂ : Type*}
variable [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]

private theorem cost_scale_le (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ) (b : E₁ → ℝ) (b' : E₂ → ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    M.cost (scaleFinitePair c ∘ x) (scaleFinitePair c ∘ y)
        (fun i => c * b i) (fun j => c * b' j) ≤
      ENNReal.ofReal c * M.cost x y b b' := by
  apply M.cost_le_of
  · intro i
    have h := M.source_le_cost x y b b' i
    revert h
    cases M.finite i with
    | none =>
      intro h
      change diagonalCost (scaleFinitePair c (x i)) ≤ _
      rw [diagonalCost_scale _ hc]
      exact mul_le_mul_right h _
    | some j =>
      intro h
      change finitePairCost (scaleFinitePair c (x i)) (scaleFinitePair c (y j)) ≤ _
      rw [finitePairCost_scale _ _ hc]
      exact mul_le_mul_right h _
  · intro j
    by_cases hj : ∃ i, M.finite i = some j
    · rw [if_pos hj]
      exact zero_le
    · rw [if_neg hj]
      have h := M.target_le_cost x y b b' j
      rw [if_neg hj] at h
      change diagonalCost (scaleFinitePair c (y j)) ≤ _
      rw [diagonalCost_scale _ hc]
      exact mul_le_mul_right h _
  · intro k
    rw [essentialPairCost_scale _ _ hc]
    exact mul_le_mul_right (M.essential_le_cost x y b b' k) _

/-- Positive scaling multiplies the cost of every occurrence matching by `c`. -/
theorem cost_scale (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ) (b : E₁ → ℝ) (b' : E₂ → ℝ)
    {c : ℝ} (hc : 0 < c) :
    M.cost (scaleFinitePair c ∘ x) (scaleFinitePair c ∘ y)
        (fun i => c * b i) (fun j => c * b' j) =
      ENNReal.ofReal c * M.cost x y b b' := by
  apply le_antisymm (cost_scale_le M x y b b' hc.le)
  have h := cost_scale_le M (scaleFinitePair c ∘ x) (scaleFinitePair c ∘ y)
    (fun i => c * b i) (fun j => c * b' j) (inv_nonneg.2 hc.le)
  have hpair : ∀ p : ℝ × ℝ, scaleFinitePair c⁻¹ (scaleFinitePair c p) = p := by
    intro p
    simp [scaleFinitePair, inv_mul_cancel_left₀ hc.ne']
  have hx : scaleFinitePair c⁻¹ ∘ (scaleFinitePair c ∘ x) = x := funext fun i => hpair (x i)
  have hy : scaleFinitePair c⁻¹ ∘ (scaleFinitePair c ∘ y) = y := funext fun j => hpair (y j)
  have hb : (fun i => c⁻¹ * (c * b i)) = b := funext fun i => inv_mul_cancel_left₀ hc.ne' _
  have hb' : (fun j => c⁻¹ * (c * b' j)) = b' :=
    funext fun j => inv_mul_cancel_left₀ hc.ne' _
  simp only [hx, hy, hb, hb'] at h
  calc
    ENNReal.ofReal c * M.cost x y b b' ≤
        ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * M.cost (scaleFinitePair c ∘ x)
          (scaleFinitePair c ∘ y) (fun i => c * b i) (fun j => c * b' j)) :=
      mul_le_mul_right h _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
        ENNReal.ofReal_one, one_mul]

end OccurrenceMatching

/-- Positive scaling multiplies the presentation bottleneck by `c`, including `⊤`. -/
theorem presentationBottleneck_scale {F₁ F₂ E₁ E₂ : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ) (b : E₁ → ℝ) (b' : E₂ → ℝ)
    {c : ℝ} (hc : 0 < c) :
    presentationBottleneck (scaleFinitePair c ∘ x) (scaleFinitePair c ∘ y)
        (fun i => c * b i) (fun j => c * b' j) =
      ENNReal.ofReal c * presentationBottleneck x y b b' := by
  unfold presentationBottleneck
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top]
  exact iInf_congr fun M => M.cost_scale x y b b' hc

/-- Positive scaling multiplies the bottleneck distance of any two real diagrams by `c`.
No essential-count hypothesis is needed: both sides are `⊤` when the counts differ. -/
theorem bottleneck_scale (D E : Diagram ℝ) {c : ℝ} (hc : 0 < c) :
    bottleneck (D.scale c hc) (E.scale c hc) = ENNReal.ofReal c * bottleneck D E := by
  rw [bottleneck_eq_presentation (D.scale c hc) (E.scale c hc)
    (scaleFinitePair c ∘ fun p : D.finiteOccurrences => p.1)
    (scaleFinitePair c ∘ fun p : E.finiteOccurrences => p.1)
    (fun i : D.essentialOccurrences => c * i.1)
    (fun j : E.essentialOccurrences => c * j.1)
    ((Multiset.map_univ _ _).trans (finitePart_scale_points D hc).symm)
    ((Multiset.map_univ _ _).trans (finitePart_scale_points E hc).symm)
    ((Multiset.map_univ _ _).trans (essentialPart_scale_points D hc).symm)
    ((Multiset.map_univ _ _).trans (essentialPart_scale_points E hc).symm)]
  unfold bottleneck
  exact presentationBottleneck_scale _ _ _ _ hc

section Actual

variable {V : Type u} [LinearOrder V] (k : Type u) [Field k]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TDA.Simplicial.TotalFace K)]

/-- The actual diagram of a positively scaled filter is the scaled actual diagram. -/
theorem dgm_scale (f : FilterFunction K ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    dgm k (f.scale c hc) n = (dgm k f n).scale c hc :=
  dgm_map k f _ n

/-- Positive scaling of two filters multiplies the bottleneck distance of their actual
diagrams by `c`. -/
theorem bottleneck_dgm_scale (f g : FilterFunction K ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    bottleneck (dgm k (f.scale c hc) n) (dgm k (g.scale c hc) n) =
      ENNReal.ofReal c * bottleneck (dgm k f n) (dgm k g n) := by
  rw [dgm_scale, dgm_scale]
  exact bottleneck_scale _ _ hc

end Actual

/-- The merged filter translation is the reparametrization along `x ↦ x + c`. -/
theorem translateFilterFunction_eq_map {V : Type*} [LinearOrder V]
    {K : PreAbstractSimplicialComplex V} (f : FilterFunction K ℝ) (c : ℝ) :
    translateFilterFunction f c = f.map (OrderIso.addRight c).toOrderEmbedding := by
  ext s
  rfl

/-- The merged diagram translation is the diagram map along `x ↦ x + c`. -/
theorem translateDiagram_eq_map (D : Diagram ℝ) (c : ℝ) :
    translateDiagram D c = D.map (OrderIso.addRight c).toOrderEmbedding := by
  apply Diagram.ext
  change D.points.map (translateDiagramPoint c) = D.points.map _
  congr 1

end TDA.Persistence
