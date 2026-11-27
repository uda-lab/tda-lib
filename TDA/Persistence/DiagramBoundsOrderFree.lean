import TDA.Persistence.TotalPersistenceRipsCech
import TDA.Persistence.AlphaRadiusStability
import TDA.Persistence.RipsGromovHausdorff
import TDA.Persistence.CechHausdorff
import TDA.Persistence.SublevelDiagramVertexMap

set_option autoImplicit false

/-!
# Diagram bounds without a supplied vertex order

The statements about `dgm` of the Rips and Čech filters take the vertex labels and the
coefficient field in one universe and a linear order on the labels.  The diagrams do not depend
on either: a finite label type is enumerated by `Fintype.equivFin`, and the enumeration
`ULift.{v} (Fin (Fintype.card V))` lies in the universe `v` of the coefficient field, which
carries its own linear order.

* `Rips.totalPersistence_diagram_le` bounds the total persistence of `Rips.diagram`.
* `Cech.diagram` is the Čech diagram of a finite labelled configuration in a pseudometric
  space, for labels in any universe and any coefficient field; `Cech.diagram_eq_dgm`
  identifies it with `dgm` of `Cech.filter` for every supplied linear order.
* `Cech.totalPersistence_diagram_le_diameter` and
  `Cech.bottleneck_rips_cech_diagram_le_half_diameter_real` are the total-persistence and
  half-diameter bounds for these diagrams.
* `alphaRadiusDiagramOrderFree` is the radius α diagram with the same enumeration;
  `alphaRadiusDiagramOrderFree_eq_alphaRadiusDiagram` identifies it with
  `alphaRadiusDiagram`, and `bottleneck_alphaRadiusDiagramOrderFree_le_displacement` is the
  displacement bound.

The diameter and the displacement of the enumerated labels equal those of the original labels
(`Rips.diameter_induced_equiv`, `Cech.displacement_comp_equiv`), so every bound is the bound of
the ordered statement.
-/

universe u v w

namespace TDA.Persistence

open TDA.Simplicial TDA.Filtration

noncomputable section

/-- Enumeration of a finite label type by labels in an arbitrary universe. -/
private def enumLabels (V : Type u) [Fintype V] : ULift.{v} (Fin (Fintype.card V)) ≃ V :=
  Equiv.ulift.trans (Fintype.equivFin V).symm

section Transport

variable {V W : Type*} [Fintype V] [Fintype W]

/-- The diameter is invariant under an equivalence of the carrier with the pulled-back metric. -/
theorem Rips.diameter_induced_equiv (e : W ≃ V) (d : MetricSpace V) :
    Rips.diameter (MetricSpace.induced e e.injective d) Finset.univ =
      Rips.diameter d Finset.univ := by
  unfold Rips.diameter
  apply le_antisymm
  · rw [Finset.fold_max_le]
    refine ⟨(Finset.le_fold_max 0).mpr (Or.inl le_rfl), fun x _ => ?_⟩
    exact (Finset.le_fold_max _).mpr
      (Or.inr ⟨(e x.1, e x.2), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        le_rfl⟩)
  · rw [Finset.fold_max_le]
    refine ⟨(Finset.le_fold_max 0).mpr (Or.inl le_rfl), fun x _ => ?_⟩
    exact (Finset.le_fold_max _).mpr
      (Or.inr ⟨(e.symm x.1, e.symm x.2),
        Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, by
          change d.dist x.1 x.2 ≤ d.dist (e (e.symm x.1)) (e (e.symm x.2))
          simp⟩)

/-- The displacement of two configurations is invariant under relabelling by an equivalence. -/
theorem Cech.displacement_comp_equiv {X : Type*} [PseudoMetricSpace X] (e : W ≃ V)
    (p q : V → X) :
    TDA.Filtration.Cech.displacement (p ∘ e) (q ∘ e) =
      TDA.Filtration.Cech.displacement p q := by
  unfold TDA.Filtration.Cech.displacement
  apply le_antisymm
  · rw [Finset.fold_max_le]
    refine ⟨(Finset.le_fold_max 0).mpr (Or.inl le_rfl), fun x _ => ?_⟩
    exact (Finset.le_fold_max _).mpr (Or.inr ⟨e x, Finset.mem_univ _, le_rfl⟩)
  · rw [Finset.fold_max_le]
    refine ⟨(Finset.le_fold_max 0).mpr (Or.inl le_rfl), fun x _ => ?_⟩
    exact (Finset.le_fold_max _).mpr (Or.inr ⟨e.symm x, Finset.mem_univ _, by simp⟩)

end Transport

section Rips

variable (k : Type v) [Field k] (X : Type u) [Fintype X] [MetricSpace X] (n : ℕ)

private theorem ripsDiagram_eq (k : Type v) [Field k] (X : Type u) [Fintype X] [MetricSpace X]
    (n : ℕ) :
    Rips.diagram k X n =
      dgm k (Rips.filter (MetricSpace.induced (enumLabels.{u, v} X) (enumLabels X).injective
        (inferInstance : MetricSpace X))) n := rfl

/-- The total-persistence bound of `Rips.totalPersistence_dgm_le` for the order-free Rips
diagram: finite metric space, coefficient field in any universe, no vertex order. -/
theorem Rips.totalPersistence_diagram_le (p : ℕ) :
    (Rips.diagram k X n).totalPersistence p ≤
      (Nat.choose (Fintype.card X) (n + 2) : ℝ) *
        Rips.diameter (inferInstance : MetricSpace X) Finset.univ ^ p := by
  rw [ripsDiagram_eq]
  have h := Rips.totalPersistence_dgm_le (V := ULift.{v} (Fin (Fintype.card X))) k
    (MetricSpace.induced (enumLabels.{u, v} X) (enumLabels X).injective
      (inferInstance : MetricSpace X)) n p
  rwa [Rips.diameter_induced_equiv, Fintype.card_ulift, Fintype.card_fin] at h

end Rips

section Cech

variable {X : Type w} [PseudoMetricSpace X]

/-- The Čech diagram of a finite labelled configuration in a pseudometric space, for labels in
any universe and any coefficient field, with no vertex order: the existing diagram `dgm` of the
configuration enumerated by `Fintype.equivFin`, with labels `ULift.{v} (Fin (Fintype.card V))`
in the universe of the coefficient field.  `Cech.diagram_eq_dgm` identifies it with `dgm` for
every supplied linear order. -/
def Cech.diagram (k : Type v) [Field k] {V : Type u} [Fintype V] (p : V → X) (n : ℕ) :
    Diagram ℝ :=
  dgm k (TDA.Filtration.Cech.filter
    (fun i : ULift.{v} (Fin (Fintype.card V)) => p ((Fintype.equivFin V).symm i.down))) n

private theorem radiusAt_comp_equiv {V W : Type*} [DecidableEq V] (e : W ≃ V) (p : V → X) (x : X)
    (s : Finset W) :
    TDA.Filtration.Cech.radiusAt (p ∘ e) x s =
      TDA.Filtration.Cech.radiusAt p x (s.image e) := by
  unfold TDA.Filtration.Cech.radiusAt
  rw [Finset.fold_image (fun a _ b _ h => e.injective h)]
  rfl

private theorem mem_sublevel_comp_equiv {V W : Type*} [DecidableEq V] (e : W ≃ V) (p : V → X) (r : ℝ)
    (s : Finset W) :
    s ∈ (TDA.Filtration.Cech.filter (p ∘ e)).sublevel r ↔
      s.image e ∈ (TDA.Filtration.Cech.filter p).sublevel r := by
  rw [FilterFunction.mem_sublevel_iff, FilterFunction.mem_sublevel_iff]
  have hne : s ∈ Rips.fullComplex W ↔ s.image e ∈ Rips.fullComplex V := by
    simp only [Rips.mem_fullComplex_iff, Finset.image_nonempty]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨hne.1 hs, ?_⟩
    simpa only [TDA.Filtration.Cech.filter_value, radiusAt_comp_equiv] using h
  · rintro ⟨hs, h⟩
    refine ⟨hne.2 hs, ?_⟩
    simpa only [TDA.Filtration.Cech.filter_value, radiusAt_comp_equiv] using h

/-- The order-free Čech diagram equals the diagram of `Cech.filter` for every supplied linear
order on the labels. -/
theorem Cech.diagram_eq_dgm (k : Type u) [Field k] {V : Type u} [Fintype V] [LinearOrder V]
    (p : V → X) (n : ℕ) :
    Cech.diagram k p n = dgm k (TDA.Filtration.Cech.filter p) n := by
  refine dgm_eq_of_vertexMaps k _ _ (enumLabels.{u, u} V) (enumLabels.{u, u} V).symm ?_ ?_ ?_ ?_ n
  · intro r s hs
    exact (mem_sublevel_comp_equiv (enumLabels.{u, u} V) p r s).1 hs
  · intro r t ht
    apply (mem_sublevel_comp_equiv (enumLabels.{u, u} V) p r _).2
    simpa [Finset.image_image] using ht
  · intro s _ v _
    exact (enumLabels.{u, u} V).symm_apply_apply v
  · intro t _ w _
    exact (enumLabels.{u, u} V).apply_symm_apply w

/-- The Čech total-persistence bound of `Cech.totalPersistence_dgm_le_diameter` for the
order-free diagram: labels in any universe, coefficient field in any universe. -/
theorem Cech.totalPersistence_diagram_le_diameter (k : Type v) [Field k] {V : Type u}
    [Fintype V] (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n q : ℕ) :
    (Cech.diagram k p n).totalPersistence q ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) * Rips.diameter d Finset.univ ^ q := by
  have h := Cech.totalPersistence_dgm_le_diameter (V := ULift.{v} (Fin (Fintype.card V))) k
    (MetricSpace.induced (enumLabels.{u, v} V) (enumLabels V).injective d)
    (fun i => p (enumLabels V i)) (fun a b => hd _ _) n q
  rw [Rips.diameter_induced_equiv, Fintype.card_ulift, Fintype.card_fin] at h
  exact h

/-- On the line, the Rips and Čech diagrams of one configuration are at bottleneck distance at
most half the carrier diameter, with labels and coefficient field in any universes and no
vertex order. -/
theorem Cech.bottleneck_rips_cech_diagram_le_half_diameter_real (k : Type v) [Field k]
    {V : Type u} [Fintype V] (d : MetricSpace V) (q : V → ℝ)
    (hd : ∀ v w, d.dist v w = dist (q v) (q w)) (n : ℕ) :
    bottleneck (@Rips.diagram.{u, v} k _ V _ d n) (Cech.diagram k q n) ≤
      ENNReal.ofReal (Rips.diameter d Finset.univ / 2) := by
  have h := Cech.bottleneck_rips_cech_dgm_le_half_diameter_real
    (V := ULift.{v} (Fin (Fintype.card V))) k
    (MetricSpace.induced (enumLabels.{u, v} V) (enumLabels V).injective d)
    (fun i => q (enumLabels V i)) (fun a b => hd _ _) n
  rw [Rips.diameter_induced_equiv] at h
  exact h

end Cech

section Alpha

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The radius α diagram of a finite labelled configuration in a finite-dimensional real inner
product space, for labels in any universe and any coefficient field, with no vertex order: the
diagram `alphaRadiusDiagram` of the configuration enumerated by `Fintype.equivFin`.
`alphaRadiusDiagramOrderFree_eq_alphaRadiusDiagram` identifies it with `alphaRadiusDiagram` for
every supplied linear order. -/
def alphaRadiusDiagramOrderFree (k : Type v) [Field k] {V : Type u} [Fintype V] (p : V → E)
    (n : ℕ) : Diagram ℝ :=
  alphaRadiusDiagram k
    (fun i : ULift.{v} (Fin (Fintype.card V)) => p ((Fintype.equivFin V).symm i.down)) n

/-- The order-free radius α diagram equals `alphaRadiusDiagram` for every supplied linear order
on the labels. -/
theorem alphaRadiusDiagramOrderFree_eq_alphaRadiusDiagram (k : Type u) [Field k] {V : Type u}
    [Fintype V] [LinearOrder V] (p : V → E) (n : ℕ) :
    alphaRadiusDiagramOrderFree k p n = alphaRadiusDiagram k p n := by
  unfold alphaRadiusDiagramOrderFree
  rw [alphaRadiusDiagram_eq_cech, alphaRadiusDiagram_eq_cech]
  exact Cech.diagram_eq_dgm k p n

/-- Moving matched labels in a common Euclidean space changes the order-free radius α diagrams
by at most the largest site displacement, in every degree, for labels in any universe and any
coefficient field. -/
theorem bottleneck_alphaRadiusDiagramOrderFree_le_displacement (k : Type v) [Field k]
    {V : Type u} [Fintype V] (p q : V → E) (n : ℕ) :
    bottleneck (alphaRadiusDiagramOrderFree k p n) (alphaRadiusDiagramOrderFree k q n) ≤
      ENNReal.ofReal (TDA.Filtration.Cech.displacement p q) := by
  have h := bottleneck_alphaRadiusDiagram_le_displacement (V := ULift.{v} (Fin (Fintype.card V)))
    k (p ∘ enumLabels V) (q ∘ enumLabels V) n
  rw [Cech.displacement_comp_equiv] at h
  exact h

end Alpha

end

end TDA.Persistence
