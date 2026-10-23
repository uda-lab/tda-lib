import TDA.Persistence.PersistenceImageMatching
import TDA.Persistence.FiniteMatchingCostBottleneck

/-!
# Persistence images of the finite part of a diagram

Canonical occurrence labels preserve multiplicity. Essential bars are omitted from
this feature, without replacing their deaths by a finite value. A finite full
bottleneck bounds the finite first-order cost with an explicit occurrence-count
factor, and hence bounds the existing Gaussian pixel ℓ¹ image.
-/

namespace TDA.Persistence

/-- Positive diagrams give strictly positive lengths at every finite occurrence. -/
theorem Diagram.IsPositive.finiteOccurrence {D : Diagram ℝ} (hD : D.IsPositive)
    (p : D.finiteOccurrences) : p.1.1 < p.1.2 := by
  have hp : p.1 ∈ finitePart D.points := Multiset.coe_mem (x := p)
  obtain ⟨⟨b, d⟩, hbd, he⟩ := (Multiset.mem_filterMap _ _).mp hp
  cases d with
  | top => simp at he
  | coe d =>
    have hpos := hD (b, (d : WithTop ℝ)) hbd
    simp at he
    rw [← he]
    simpa using hpos

namespace PersistenceImage

open MeasureTheory Set

/-- Gaussian pixel image of the finite occurrences only, retaining their multiplicity.
Essential bars contribute no pixel feature. -/
noncomputable def finiteDiagramImage {K : Type*} [Fintype K] {A B : ℝ}
    (σ : ℝ) (w : Weight A B) (P : K → Set (ℝ × ℝ)) (D : Diagram ℝ) :
    PiLp 1 (fun _ : K => ℝ) :=
  image σ w P (fun p : D.finiteOccurrences => p.1)

/-- Empty finite parts, including essential-only diagrams, have zero image. -/
theorem finiteDiagramImage_eq_zero_of_finitePart_eq_zero
    {K : Type*} [Fintype K] {A B : ℝ} (σ : ℝ) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (D : Diagram ℝ) (hD : finitePart D.points = 0) :
    finiteDiagramImage σ w P D = 0 := by
  have : IsEmpty D.finiteOccurrences := by
    change IsEmpty (finitePart D.points)
    rw [hD]
    infer_instance
  exact finiteFeatureSum_empty _ _

/-- Count-dependent bottleneck stability for finite-diagram Gaussian images.
Both the finite bottleneck and positive-length hypotheses are explicit. -/
theorem norm_finiteDiagramImage_sub_le_card_mul_bottleneck
    {K : Type*} [Fintype K] {σ A B : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ k, MeasurableSet (P k))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (D E : Diagram ℝ) (hD : D.IsPositive) (hE : E.IsPositive)
    (hfinite : bottleneck D E < ⊤) :
    ‖finiteDiagramImage σ w P D - finiteDiagramImage σ w P E‖ ≤
      stabilityConstant σ A B *
        ((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck D E).toReal := by
  calc
    _ ≤ stabilityConstant σ A B * finiteFirstOrderMatchingCost
        (fun p : D.finiteOccurrences => p.1) (fun p : E.finiteOccurrences => p.1) :=
      norm_image_sub_le_finiteFirstOrderMatchingCost hσ hA hB w P hm hd _ _
        hD.finiteOccurrence hE.finiteOccurrence
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (finiteFirstOrderMatchingCost_le_card_mul_bottleneck D E hfinite)
        (stabilityConstant_nonneg hσ hA hB)

end PersistenceImage
end TDA.Persistence
