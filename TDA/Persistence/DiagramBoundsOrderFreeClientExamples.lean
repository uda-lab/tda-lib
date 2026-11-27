import TDA.Persistence.DiagramBoundsOrderFree

set_option autoImplicit false

/-!
# Client statements of the order-free diagram bounds

Regression fixtures for #1300, family 16 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
no linear order on the vertex type of a finite subset of the plane appears.

* The total-persistence bounds of the Rips and Čech diagrams of a finite subset of the plane
  over `ZMod 2`.
* The half-diameter bound between the Rips and Čech diagrams of a finite subset of the line.
* The displacement bound of the radius α diagrams of two configurations indexed by a finite
  subset of the plane.
* Labels and coefficient field in different universes.
-/

namespace TDA.Persistence.DiagramBoundsOrderFreeClientExamples

/-- The Rips total-persistence bound for a finite subset of the plane. -/
theorem plane_rips_totalPersistence_le (S : Finset (EuclideanSpace ℝ (Fin 2))) (n p : ℕ) :
    (Rips.diagram (ZMod 2) S n).totalPersistence p ≤
      (Nat.choose (Fintype.card S) (n + 2) : ℝ) *
        TDA.Filtration.Rips.diameter (inferInstance : MetricSpace S) Finset.univ ^ p :=
  Rips.totalPersistence_diagram_le (ZMod 2) S n p

/-- The Čech total-persistence bound for a finite subset of the plane. -/
theorem plane_cech_totalPersistence_le (S : Finset (EuclideanSpace ℝ (Fin 2))) (n p : ℕ) :
    (Cech.diagram (ZMod 2) (fun x : S => (x : EuclideanSpace ℝ (Fin 2))) n).totalPersistence p ≤
      (Nat.choose (Fintype.card S) (n + 2) : ℝ) *
        TDA.Filtration.Rips.diameter (inferInstance : MetricSpace S) Finset.univ ^ p :=
  Cech.totalPersistence_diagram_le_diameter (ZMod 2) _ (fun x : S => (x : EuclideanSpace ℝ (Fin 2)))
    (fun _ _ => rfl) n p

/-- The half-diameter bound between the Rips and Čech diagrams of a finite subset of the line. -/
theorem line_bottleneck_rips_cech_le (S : Finset ℝ) (n : ℕ) :
    bottleneck (Rips.diagram (ZMod 2) S n) (Cech.diagram (ZMod 2) (fun x : S => (x : ℝ)) n) ≤
      ENNReal.ofReal
        (TDA.Filtration.Rips.diameter (inferInstance : MetricSpace S) Finset.univ / 2) :=
  Cech.bottleneck_rips_cech_diagram_le_half_diameter_real (ZMod 2) _ (fun x : S => (x : ℝ))
    (fun _ _ => rfl) n

/-- The displacement bound of the radius α diagrams of two configurations in the plane indexed
by a finite subset of the plane. -/
theorem plane_alpha_bottleneck_le (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (p q : S → EuclideanSpace ℝ (Fin 2)) (n : ℕ) :
    bottleneck (alphaRadiusDiagramOrderFree (ZMod 2) p n)
        (alphaRadiusDiagramOrderFree (ZMod 2) q n) ≤
      ENNReal.ofReal (TDA.Filtration.Cech.displacement p q) :=
  bottleneck_alphaRadiusDiagramOrderFree_le_displacement (ZMod 2) p q n

/-- The Rips bound for a field in `Type 1` and a finite subset of the plane. -/
theorem plane_field_type_one_rips_le (k : Type 1) [Field k]
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (n p : ℕ) :
    (Rips.diagram k S n).totalPersistence p ≤
      (Nat.choose (Fintype.card S) (n + 2) : ℝ) *
        TDA.Filtration.Rips.diameter (inferInstance : MetricSpace S) Finset.univ ^ p :=
  Rips.totalPersistence_diagram_le k S n p

/-- The Čech bound for labels in `Type 1` and the field `ZMod 2` in `Type`. -/
theorem labels_type_one_cech_le (V : Type 1) [Fintype V] (d : MetricSpace V)
    (x : V → EuclideanSpace ℝ (Fin 2)) (hd : ∀ v w, d.dist v w = dist (x v) (x w))
    (n q : ℕ) :
    (Cech.diagram (ZMod 2) x n).totalPersistence q ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) * TDA.Filtration.Rips.diameter d Finset.univ ^ q :=
  Cech.totalPersistence_diagram_le_diameter (ZMod 2) d x hd n q

/-- The order-free Čech diagram equals the diagram of every supplied order on a finite subset of
the plane. -/
theorem plane_cech_diagram_eq_dgm (S : Finset (EuclideanSpace ℝ (Fin 2))) [LinearOrder S]
    (n : ℕ) :
    Cech.diagram (ZMod 2) (fun x : S => (x : EuclideanSpace ℝ (Fin 2))) n =
      dgm (ZMod 2) (TDA.Filtration.Cech.filter (fun x : S => (x : EuclideanSpace ℝ (Fin 2)))) n :=
  Cech.diagram_eq_dgm (ZMod 2) _ n

end TDA.Persistence.DiagramBoundsOrderFreeClientExamples
