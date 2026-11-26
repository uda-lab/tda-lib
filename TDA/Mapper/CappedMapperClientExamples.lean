import TDA.Mapper.RefinementHomologyOrderFree

/-!
# Client statements of the capped centred Mapper bounds

Regression fixtures for #1272, family 9 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
no order on component indices appears.

* A graph on `Fin 4` with two vertex-height functions within `ε` at every vertex: the
  degree-`1` capped centred diagrams over `ZMod 2` are at bottleneck distance at most `ε + μ`
  on a grid of mesh at most `μ`, and at most `ε` on a uniform grid whose spacing divides `ε`.
* The same diagrams for any supplied families of component orders, through
  `cappedCentredDiagramOrderFree_eq`.
-/

namespace TDA.Mapper.CappedMapperClientExamples

/-- The graph-PL perturbation bound on `Fin 4`, with no component order. -/
theorem fin_four_bottleneck_le (G : SimpleGraph (Fin 4)) (h₁ h₂ : Fin 4 → ℝ)
    (ε μ : NNReal)
    (hh : ∀ v, |h₁ v - h₂ v| ≤ ε) (ℓ : Fin 3 → ℤ) {m : ℕ} (c : Fin m ↪o ℝ)
    (hgap : ∀ i j : Fin m, j.val = i.val + 1 → c j ≤ c i + μ) :
    TDA.Persistence.bottleneck
        (TDA.Mapper.cappedCentredDiagramOrderFree (ZMod 2)
          (TDA.Reeb.GraphPL.plHeight G h₁) 0 1 ℓ c 1)
        (TDA.Mapper.cappedCentredDiagramOrderFree (ZMod 2)
          (TDA.Reeb.GraphPL.plHeight G h₂) 0 1 ℓ c 1) ≤
      (ε : ENNReal) + μ :=
  TDA.Mapper.bottleneck_cappedCentredDiagramOrderFree_plHeight_le (ZMod 2) G 0 1 ℓ 1 hh
    hgap

/-- The uniform-grid bound on `Fin 4`, with no component order. -/
theorem fin_four_uniformGrid_bottleneck_le (G : SimpleGraph (Fin 4)) (h₁ h₂ : Fin 4 → ℝ)
    (ε : NNReal) (hh : ∀ v, |h₁ v - h₂ v| ≤ ε) (ℓ : Fin 3 → ℤ) (x₀ h : ℝ) (hpos : 0 < h)
    (m p : ℕ) (hε : (ε : ℝ) = p * h) :
    TDA.Persistence.bottleneck
        (TDA.Mapper.cappedCentredDiagramOrderFree (ZMod 2)
          (TDA.Reeb.GraphPL.plHeight G h₁) 0 1 ℓ (TDA.Mapper.uniformGrid x₀ h hpos m) 1)
        (TDA.Mapper.cappedCentredDiagramOrderFree (ZMod 2)
          (TDA.Reeb.GraphPL.plHeight G h₂) 0 1 ℓ (TDA.Mapper.uniformGrid x₀ h hpos m) 1) ≤
      ε :=
  TDA.Mapper.bottleneck_cappedCentredDiagramOrderFree_plHeight_uniformGrid_le (ZMod 2) G 0 1
    ℓ 1 hh x₀ h hpos m p hε

/-- With supplied component orders on both sides, the same bound holds for
`cappedCentredDiagram`. -/
theorem fin_four_bottleneck_le_of_orders (G : SimpleGraph (Fin 4)) (h₁ h₂ : Fin 4 → ℝ)
    (ε μ : NNReal) (hh : ∀ v, |h₁ v - h₂ v| ≤ ε) (ℓ : Fin 3 → ℤ) {m : ℕ} (c : Fin m ↪o ℝ)
    (hgap : ∀ i j : Fin m, j.val = i.val + 1 → c j ≤ c i + μ)
    [∀ i, LinearOrder (TDA.Mapper.ComponentIndex (TDA.Reeb.GraphPL.plHeight G h₁)
      fun w =>
      (TDA.Mapper.cappedCentredCover 0 1 ℓ c i w : Set ℝ))]
    [∀ i, LinearOrder (TDA.Mapper.ComponentIndex (TDA.Reeb.GraphPL.plHeight G h₂)
      fun w =>
      (TDA.Mapper.cappedCentredCover 0 1 ℓ c i w : Set ℝ))] :
    TDA.Persistence.bottleneck
        (TDA.Mapper.cappedCentredDiagram (ZMod 2) (TDA.Reeb.GraphPL.plHeight G h₁) 0 1 ℓ c
          1)
        (TDA.Mapper.cappedCentredDiagram (ZMod 2) (TDA.Reeb.GraphPL.plHeight G h₂) 0 1 ℓ c
          1) ≤
      (ε : ENNReal) + μ := by
  rw [← TDA.Mapper.cappedCentredDiagramOrderFree_eq,
    ← TDA.Mapper.cappedCentredDiagramOrderFree_eq]
  exact fin_four_bottleneck_le G h₁ h₂ ε μ hh ℓ c hgap

end TDA.Mapper.CappedMapperClientExamples
