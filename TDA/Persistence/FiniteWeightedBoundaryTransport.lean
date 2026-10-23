import TDA.Persistence.FinitePBoundaryTransport
import Mathlib.Topology.Order.Compact

/-!
# Boundary transport of finite real masses

Each source and target label carries a nonnegative real mass. A plan may split
that mass between labels; the remaining source and target masses are charged to
the diagonal. Geometric distances use the existing maximum norm. Raising a
distance to a real exponent never raises its mass coefficient to that exponent.

The feasible matrices form a closed subset of a finite coordinate box. A
continuous linear objective therefore attains its minimum, without requiring
integral masses or equal total masses. The construction is a finite reservoir
model of the three cost families in Divol--Lacombe's boundary transport. It does
not identify the model with all Radon couplings.
-/

noncomputable section

universe u v

namespace TDA.Persistence

open scoped Classical NNReal

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- All nonnegative matrices whose marginals are bounded by the prescribed masses. -/
def weightedBoundaryMatrices (w : I → ℝ≥0) (v : J → ℝ≥0) : Set (I → J → ℝ) :=
  {a | (∀ i j, 0 ≤ a i j) ∧ (∀ i, ∑ j, a i j ≤ w i) ∧
    (∀ j, ∑ i, a i j ≤ v j)}

/-- A finite real plan, with unused mass supplied to or absorbed by the diagonal. -/
structure FiniteWeightedBoundaryPlan (w : I → ℝ≥0) (v : J → ℝ≥0) where
  mass : I → J → ℝ
  nonneg : ∀ i j, 0 ≤ mass i j
  row_le : ∀ i, ∑ j, mass i j ≤ w i
  col_le : ∀ j, ∑ i, mass i j ≤ v j

namespace FiniteWeightedBoundaryPlan

variable {w : I → ℝ≥0} {v : J → ℝ≥0}

/-- The plan using only the boundary is feasible for every pair of mass families. -/
def zero (w : I → ℝ≥0) (v : J → ℝ≥0) : FiniteWeightedBoundaryPlan w v where
  mass _ _ := 0
  nonneg _ _ := le_rfl
  row_le i := by simp
  col_le j := by simp

instance : Nonempty (FiniteWeightedBoundaryPlan w v) := ⟨zero w v⟩

theorem mass_mem (a : FiniteWeightedBoundaryPlan w v) :
    a.mass ∈ weightedBoundaryMatrices w v :=
  ⟨a.nonneg, a.row_le, a.col_le⟩

/-- A matrix satisfying the marginal inequalities defines a plan. -/
def ofMass (a : I → J → ℝ) (ha : a ∈ weightedBoundaryMatrices w v) :
    FiniteWeightedBoundaryPlan w v :=
  ⟨a, ha.1, ha.2.1, ha.2.2⟩

/-- Source mass not transported to a target label. -/
def deletionMass (a : FiniteWeightedBoundaryPlan w v) (i : I) : ℝ :=
  w i - ∑ j, a.mass i j

/-- Target mass supplied from the boundary. -/
def insertionMass (a : FiniteWeightedBoundaryPlan w v) (j : J) : ℝ :=
  v j - ∑ i, a.mass i j

theorem deletionMass_nonneg (a : FiniteWeightedBoundaryPlan w v) (i : I) :
    0 ≤ a.deletionMass i := sub_nonneg.mpr (a.row_le i)

theorem insertionMass_nonneg (a : FiniteWeightedBoundaryPlan w v) (j : J) :
    0 ≤ a.insertionMass j := sub_nonneg.mpr (a.col_le j)

theorem source_balance (a : FiniteWeightedBoundaryPlan w v) (i : I) :
    (∑ j, a.mass i j) + a.deletionMass i = w i := by simp [deletionMass]

theorem target_balance (a : FiniteWeightedBoundaryPlan w v) (j : J) :
    (∑ i, a.mass i j) + a.insertionMass j = v j := by simp [insertionMass]

end FiniteWeightedBoundaryPlan

/-- The feasible set includes the boundary-only matrix, even when either type is empty. -/
theorem weightedBoundaryMatrices_nonempty (w : I → ℝ≥0) (v : J → ℝ≥0) :
    (weightedBoundaryMatrices w v).Nonempty :=
  ⟨_, (FiniteWeightedBoundaryPlan.zero w v).mass_mem⟩

private theorem isClosed_weightedBoundaryMatrices (w : I → ℝ≥0) (v : J → ℝ≥0) :
    IsClosed (weightedBoundaryMatrices w v) := by
  have hnonneg : IsClosed {a : I → J → ℝ | ∀ i j, 0 ≤ a i j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (by fun_prop)
  have hrow : IsClosed {a : I → J → ℝ | ∀ i, ∑ j, a i j ≤ (w i : ℝ)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hcol : IsClosed {a : I → J → ℝ | ∀ j, ∑ i, a i j ≤ (v j : ℝ)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  exact hnonneg.inter (hrow.inter hcol)

/-- Every feasible entry lies in a fixed compact coordinate box. No positive-mass
or nonempty-label hypothesis is needed. -/
theorem isCompact_weightedBoundaryMatrices (w : I → ℝ≥0) (v : J → ℝ≥0) :
    IsCompact (weightedBoundaryMatrices w v) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : I → J → ℝ)
    (fun i _ => (w i : ℝ)))).of_isClosed_subset (isClosed_weightedBoundaryMatrices w v)
  intro a ha
  refine ⟨fun i j => ha.1 i j, fun i j => ?_⟩
  exact (Finset.single_le_sum (fun k _ => ha.1 i k) (Finset.mem_univ j)).trans (ha.2.1 i)

/-- An affine objective on matrices, with separate pair, deletion and insertion costs. -/
def weightedBoundaryLinearObjective (w : I → ℝ≥0) (v : J → ℝ≥0)
    (c : I → J → ℝ) (d : I → ℝ) (e : J → ℝ) (a : I → J → ℝ) : ℝ :=
  (∑ i, ∑ j, a i j * c i j) +
    (∑ i, ((w i : ℝ) - ∑ j, a i j) * d i) +
    ∑ j, ((v j : ℝ) - ∑ i, a i j) * e j

theorem continuous_weightedBoundaryLinearObjective (w : I → ℝ≥0) (v : J → ℝ≥0)
    (c : I → J → ℝ) (d : I → ℝ) (e : J → ℝ) :
    Continuous (weightedBoundaryLinearObjective w v c d e) := by
  unfold weightedBoundaryLinearObjective
  fun_prop

namespace FiniteWeightedBoundaryPlan

variable {w : I → ℝ≥0} {v : J → ℝ≥0}

/-- The plan's full linear charge, including both boundary residuals. -/
def linearCost (a : FiniteWeightedBoundaryPlan w v)
    (c : I → J → ℝ) (d : I → ℝ) (e : J → ℝ) : ℝ :=
  weightedBoundaryLinearObjective w v c d e a.mass

theorem linearCost_nonneg (a : FiniteWeightedBoundaryPlan w v)
    (c : I → J → ℝ) (d : I → ℝ) (e : J → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hd : ∀ i, 0 ≤ d i) (he : ∀ j, 0 ≤ e j) :
    0 ≤ a.linearCost c d e := by
  exact add_nonneg
    (add_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (a.nonneg i j) (hc i j))
      (Finset.sum_nonneg fun i _ => mul_nonneg (a.deletionMass_nonneg i) (hd i)))
    (Finset.sum_nonneg fun j _ => mul_nonneg (a.insertionMass_nonneg j) (he j))

/-- Power only the geometric coefficients; all real masses remain linear. -/
def powerCost (a : FiniteWeightedBoundaryPlan w v) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  a.linearCost (fun i j => (finitePairCost (x i) (y j)).toReal ^ p)
    (fun i => (diagonalCost (x i)).toReal ^ p)
    (fun j => (diagonalCost (y j)).toReal ^ p)

theorem powerCost_nonneg (a : FiniteWeightedBoundaryPlan w v) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ a.powerCost p x y :=
  a.linearCost_nonneg _ _ _ (fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)

end FiniteWeightedBoundaryPlan

/-- Powered transport over every feasible real matrix with the prescribed masses. -/
def weightedPowerBoundaryTransportCost (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  ⨅ a : FiniteWeightedBoundaryPlan w v, a.powerCost p x y

/-- The reciprocal-power root is taken after optimization. -/
def weightedPBoundaryTransportCost (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  weightedPowerBoundaryTransportCost p w v x y ^ p⁻¹

theorem weightedPowerBoundaryTransportCost_nonneg (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    0 ≤ weightedPowerBoundaryTransportCost p w v x y :=
  le_ciInf fun a => a.powerCost_nonneg p x y

theorem weightedPowerBoundaryTransportCost_le_plan (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (a : FiniteWeightedBoundaryPlan w v) :
    weightedPowerBoundaryTransportCost p w v x y ≤ a.powerCost p x y :=
  ciInf_le ⟨0, by rintro _ ⟨b, rfl⟩; exact b.powerCost_nonneg p x y⟩ a

/-- For each fixed exponent a genuine feasible plan realizes the powered infimum.
The minimizing plan is allowed to change with the exponent. -/
theorem exists_minimizing_weightedPowerBoundaryPlan (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ a : FiniteWeightedBoundaryPlan w v,
      a.powerCost p x y = weightedPowerBoundaryTransportCost p w v x y := by
  let c := fun i j => (finitePairCost (x i) (y j)).toReal ^ p
  let d := fun i => (diagonalCost (x i)).toReal ^ p
  let e := fun j => (diagonalCost (y j)).toReal ^ p
  obtain ⟨m, hm, hmin⟩ := (isCompact_weightedBoundaryMatrices w v).exists_isMinOn
    (weightedBoundaryMatrices_nonempty w v)
    (continuous_weightedBoundaryLinearObjective w v c d e).continuousOn
  let a := FiniteWeightedBoundaryPlan.ofMass m hm
  refine ⟨a, le_antisymm ?_ (weightedPowerBoundaryTransportCost_le_plan p w v x y a)⟩
  exact le_ciInf fun b => hmin b.mass_mem

theorem weightedPBoundaryTransportCost_le_plan {p : ℝ} (hp : 1 ≤ p)
    (w : I → ℝ≥0) (v : J → ℝ≥0) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (a : FiniteWeightedBoundaryPlan w v) :
    weightedPBoundaryTransportCost p w v x y ≤ a.powerCost p x y ^ p⁻¹ :=
  Real.rpow_le_rpow (weightedPowerBoundaryTransportCost_nonneg p w v x y)
    (weightedPowerBoundaryTransportCost_le_plan p w v x y a)
    (inv_nonneg.mpr (le_trans zero_le_one hp))

/-- The powered minimizer also minimizes the rooted objective at that exponent. -/
theorem exists_minimizing_weightedPBoundaryPlan {p : ℝ} (hp : 1 ≤ p)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ a : FiniteWeightedBoundaryPlan w v,
      a.powerCost p x y ^ p⁻¹ = weightedPBoundaryTransportCost p w v x y := by
  obtain ⟨a, ha⟩ := exists_minimizing_weightedPowerBoundaryPlan p w v x y
  refine ⟨a, le_antisymm ?_ (weightedPBoundaryTransportCost_le_plan hp w v x y a)⟩
  rw [ha]
  exact le_rfl

theorem weightedPBoundaryTransportCost_eq_iInf {p : ℝ} (hp : 1 ≤ p)
    (w : I → ℝ≥0) (v : J → ℝ≥0) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPBoundaryTransportCost p w v x y =
      ⨅ a : FiniteWeightedBoundaryPlan w v, a.powerCost p x y ^ p⁻¹ := by
  have hbd : BddBelow (Set.range fun a : FiniteWeightedBoundaryPlan w v =>
      a.powerCost p x y ^ p⁻¹) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Real.rpow_nonneg (a.powerCost_nonneg p x y) _
  apply le_antisymm
  · exact le_ciInf fun a => weightedPBoundaryTransportCost_le_plan hp w v x y a
  · obtain ⟨a, ha⟩ := exists_minimizing_weightedPBoundaryPlan hp w v x y
    exact (ciInf_le hbd a).trans_eq ha

namespace FiniteWeightedBoundaryPlan

variable {w : I → ℝ≥0} {v : J → ℝ≥0}

/-- Reverse the transported mass and exchange deletion with insertion. -/
def transpose (a : FiniteWeightedBoundaryPlan w v) : FiniteWeightedBoundaryPlan v w where
  mass j i := a.mass i j
  nonneg j i := a.nonneg i j
  row_le j := a.col_le j
  col_le i := a.row_le i

theorem powerCost_transpose (a : FiniteWeightedBoundaryPlan w v) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    a.transpose.powerCost p y x = a.powerCost p x y := by
  simp only [powerCost, linearCost, weightedBoundaryLinearObjective, transpose,
    finitePairCost_comm]
  rw [Finset.sum_comm]
  ring

/-- Relabel every matrix entry while carrying both marginal masses along. -/
def reindex {I' : Type*} {J' : Type*} [Fintype I'] [Fintype J']
    (a : FiniteWeightedBoundaryPlan w v) (e : I' ≃ I) (f : J' ≃ J) :
    FiniteWeightedBoundaryPlan (w ∘ e) (v ∘ f) where
  mass i j := a.mass (e i) (f j)
  nonneg i j := a.nonneg (e i) (f j)
  row_le i := by simpa only [Equiv.sum_comp, Function.comp_apply] using a.row_le (e i)
  col_le j := by
    rw [e.sum_comp (fun i => a.mass i (f j))]
    exact a.col_le (f j)

theorem powerCost_reindex {I' : Type*} {J' : Type*} [Fintype I'] [Fintype J']
    (a : FiniteWeightedBoundaryPlan w v) (e : I' ≃ I) (f : J' ≃ J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (a.reindex e f).powerCost p (x ∘ e) (y ∘ f) = a.powerCost p x y := by
  let c := fun i j => (finitePairCost (x i) (y j)).toReal ^ p
  let d := fun i => (diagonalCost (x i)).toReal ^ p
  let b := fun j => (diagonalCost (y j)).toReal ^ p
  have hr (i : I') : (∑ j, a.mass (e i) (f j)) = ∑ j, a.mass (e i) j :=
    f.sum_comp (a.mass (e i))
  have hc (j : J') : (∑ i, a.mass (e i) (f j)) = ∑ i, a.mass i (f j) :=
    e.sum_comp (fun i => a.mass i (f j))
  change (∑ i, ∑ j, a.mass (e i) (f j) * c (e i) (f j)) +
      (∑ i, ((w (e i) : ℝ) - ∑ j, a.mass (e i) (f j)) * d (e i)) +
      (∑ j, ((v (f j) : ℝ) - ∑ i, a.mass (e i) (f j)) * b (f j)) = _
  simp_rw [hr, hc]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · calc
        _ = ∑ i, ∑ j, a.mass (e i) j * c (e i) j := by
          apply Finset.sum_congr rfl
          intro i _
          exact f.sum_comp (fun j => a.mass (e i) j * c (e i) j)
        _ = _ := e.sum_comp (fun i => ∑ j, a.mass i j * c i j)
    · exact e.sum_comp (fun i => ((w i : ℝ) - ∑ j, a.mass i j) * d i)
  · exact f.sum_comp (fun j => ((v j : ℝ) - ∑ i, a.mass i j) * b j)

/-- A unit-occurrence plan is already a weighted plan with constant masses one. -/
def ofUnitPlan (a : FiniteBoundaryPlan I J) :
    FiniteWeightedBoundaryPlan (fun _ : I => 1) (fun _ : J => 1) where
  mass := a.mass
  nonneg := a.nonneg
  row_le i := by simpa only [NNReal.coe_one] using a.row_le_one i
  col_le j := by simpa only [NNReal.coe_one] using a.col_le_one j

/-- Every weighted plan with unit marginals is an existing unit-occurrence plan. -/
def toUnitPlan (a : FiniteWeightedBoundaryPlan (fun _ : I => 1) (fun _ : J => 1)) :
    FiniteBoundaryPlan I J where
  mass := a.mass
  nonneg := a.nonneg
  row_le_one i := by simpa only [NNReal.coe_one] using a.row_le i
  col_le_one j := by simpa only [NNReal.coe_one] using a.col_le j

theorem powerCost_ofUnitPlan (a : FiniteBoundaryPlan I J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (ofUnitPlan a).powerCost p x y = a.powerCost p x y := rfl

theorem powerCost_toUnitPlan
    (a : FiniteWeightedBoundaryPlan (fun _ : I => 1) (fun _ : J => 1)) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    a.toUnitPlan.powerCost p x y = a.powerCost p x y := rfl

theorem powerCost_of_isEmpty_right [IsEmpty J] (a : FiniteWeightedBoundaryPlan w v)
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    a.powerCost p x y = ∑ i, (w i : ℝ) * (diagonalCost (x i)).toReal ^ p := by
  simp [powerCost, linearCost, weightedBoundaryLinearObjective]

theorem powerCost_of_isEmpty_left [IsEmpty I] (a : FiniteWeightedBoundaryPlan w v)
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    a.powerCost p x y = ∑ j, (v j : ℝ) * (diagonalCost (y j)).toReal ^ p := by
  simp [powerCost, linearCost, weightedBoundaryLinearObjective]

end FiniteWeightedBoundaryPlan

theorem weightedPowerBoundaryTransportCost_symm (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPowerBoundaryTransportCost p w v x y =
      weightedPowerBoundaryTransportCost p v w y x := by
  apply le_antisymm
  · apply le_ciInf
    intro a
    exact (weightedPowerBoundaryTransportCost_le_plan p w v x y a.transpose).trans_eq
      (a.powerCost_transpose p y x)
  · apply le_ciInf
    intro a
    exact (weightedPowerBoundaryTransportCost_le_plan p v w y x a.transpose).trans_eq
      (a.powerCost_transpose p x y)

theorem weightedPBoundaryTransportCost_symm (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPBoundaryTransportCost p w v x y = weightedPBoundaryTransportCost p v w y x := by
  simp only [weightedPBoundaryTransportCost, weightedPowerBoundaryTransportCost_symm p w v x y]

theorem weightedPowerBoundaryTransportCost_unit (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPowerBoundaryTransportCost p (fun _ => 1) (fun _ => 1) x y =
      finitePowerBoundaryTransportCost p x y := by
  apply le_antisymm
  · apply le_ciInf
    intro a
    exact (weightedPowerBoundaryTransportCost_le_plan p _ _ x y
      (FiniteWeightedBoundaryPlan.ofUnitPlan a)).trans_eq
      (FiniteWeightedBoundaryPlan.powerCost_ofUnitPlan a p x y)
  · apply le_ciInf
    intro a
    exact (finitePowerBoundaryTransportCost_le_plan p x y a.toUnitPlan).trans_eq
      (a.powerCost_toUnitPlan p x y)

theorem weightedPBoundaryTransportCost_unit (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPBoundaryTransportCost p (fun _ => 1) (fun _ => 1) x y =
      finitePBoundaryTransportCost p x y := by
  simp only [weightedPBoundaryTransportCost, weightedPowerBoundaryTransportCost_unit,
    finitePBoundaryTransportCost]

theorem weightedPowerBoundaryTransportCost_reindex
    {I' : Type*} {J' : Type*} [Fintype I'] [Fintype J']
    (e : I' ≃ I) (f : J' ≃ J) (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPowerBoundaryTransportCost p (w ∘ e) (v ∘ f) (x ∘ e) (y ∘ f) =
      weightedPowerBoundaryTransportCost p w v x y := by
  apply le_antisymm
  · apply le_ciInf
    intro a
    exact (weightedPowerBoundaryTransportCost_le_plan p _ _ _ _ (a.reindex e f)).trans_eq
      (a.powerCost_reindex e f p x y)
  · apply le_ciInf
    intro a
    have h := (weightedPowerBoundaryTransportCost_le_plan p _ _ _ _
      (a.reindex e.symm f.symm)).trans_eq
      (a.powerCost_reindex e.symm f.symm p (x ∘ e) (y ∘ f))
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using h

theorem weightedPBoundaryTransportCost_reindex
    {I' : Type*} {J' : Type*} [Fintype I'] [Fintype J']
    (e : I' ≃ I) (f : J' ≃ J) (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPBoundaryTransportCost p (w ∘ e) (v ∘ f) (x ∘ e) (y ∘ f) =
      weightedPBoundaryTransportCost p w v x y := by
  rw [weightedPBoundaryTransportCost, weightedPowerBoundaryTransportCost_reindex]
  rfl

theorem weightedPBoundaryTransportCost_nonneg (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    0 ≤ weightedPBoundaryTransportCost p w v x y :=
  Real.rpow_nonneg (weightedPowerBoundaryTransportCost_nonneg p w v x y) _

theorem weightedPowerBoundaryTransportCost_zero (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPowerBoundaryTransportCost p (fun _ => 0) (fun _ => 0) x y = 0 := by
  apply le_antisymm
  · simpa [FiniteWeightedBoundaryPlan.powerCost, FiniteWeightedBoundaryPlan.linearCost,
      weightedBoundaryLinearObjective, FiniteWeightedBoundaryPlan.zero] using
      weightedPowerBoundaryTransportCost_le_plan p (fun _ => 0) (fun _ => 0) x y
        (FiniteWeightedBoundaryPlan.zero _ _)
  · exact weightedPowerBoundaryTransportCost_nonneg p _ _ x y

theorem weightedPBoundaryTransportCost_zero {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPBoundaryTransportCost p (fun _ => 0) (fun _ => 0) x y = 0 := by
  rw [weightedPBoundaryTransportCost, weightedPowerBoundaryTransportCost_zero]
  exact Real.zero_rpow (inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)))

theorem weightedPowerBoundaryTransportCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPowerBoundaryTransportCost p w v x y =
      ∑ i, (w i : ℝ) * (diagonalCost (x i)).toReal ^ p := by
  simp only [weightedPowerBoundaryTransportCost, FiniteWeightedBoundaryPlan.powerCost_of_isEmpty_right,
    ciInf_const]

theorem weightedPowerBoundaryTransportCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPowerBoundaryTransportCost p w v x y =
      ∑ j, (v j : ℝ) * (diagonalCost (y j)).toReal ^ p := by
  simp only [weightedPowerBoundaryTransportCost, FiniteWeightedBoundaryPlan.powerCost_of_isEmpty_left,
    ciInf_const]

theorem weightedPBoundaryTransportCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPBoundaryTransportCost p w v x y =
      (∑ i, (w i : ℝ) * (diagonalCost (x i)).toReal ^ p) ^ p⁻¹ := by
  rw [weightedPBoundaryTransportCost, weightedPowerBoundaryTransportCost_of_isEmpty_right]

theorem weightedPBoundaryTransportCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (w : I → ℝ≥0) (v : J → ℝ≥0) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    weightedPBoundaryTransportCost p w v x y =
      (∑ j, (v j : ℝ) * (diagonalCost (y j)).toReal ^ p) ^ p⁻¹ := by
  rw [weightedPBoundaryTransportCost, weightedPowerBoundaryTransportCost_of_isEmpty_left]

/-- A positive finite diagram with arbitrary real atom masses and no essential bars. -/
abbrev FiniteWeightedDiagram := {z : ℝ × ℝ // z.1 < z.2} →₀ ℝ≥0

namespace FiniteWeightedDiagram

/-- Only nonzero atom masses provide labels for a weighted diagram's transport. -/
abbrev supportLabels (D : FiniteWeightedDiagram) := ↥D.support

def coordinates (D : FiniteWeightedDiagram) (i : D.supportLabels) : ℝ × ℝ := i.1.1

def weights (D : FiniteWeightedDiagram) (i : D.supportLabels) : ℝ≥0 := D i.1

/-- The finite weighted diagram's powered optimum on its positive support. -/
def powerBoundaryTransportCost (p : ℝ) (D E : FiniteWeightedDiagram) : ℝ :=
  weightedPowerBoundaryTransportCost p D.weights E.weights D.coordinates E.coordinates

/-- Rooted boundary transport of two finite positive weighted diagrams. -/
def pBoundaryTransportCost (p : ℝ) (D E : FiniteWeightedDiagram) : ℝ :=
  weightedPBoundaryTransportCost p D.weights E.weights D.coordinates E.coordinates

theorem exists_minimizing_powerPlan (p : ℝ) (D E : FiniteWeightedDiagram) :
    ∃ a : FiniteWeightedBoundaryPlan D.weights E.weights,
      a.powerCost p D.coordinates E.coordinates = powerBoundaryTransportCost p D E :=
  exists_minimizing_weightedPowerBoundaryPlan p D.weights E.weights D.coordinates E.coordinates

theorem exists_minimizing_pPlan {p : ℝ} (hp : 1 ≤ p) (D E : FiniteWeightedDiagram) :
    ∃ a : FiniteWeightedBoundaryPlan D.weights E.weights,
      a.powerCost p D.coordinates E.coordinates ^ p⁻¹ = pBoundaryTransportCost p D E :=
  exists_minimizing_weightedPBoundaryPlan hp D.weights E.weights D.coordinates E.coordinates

theorem pBoundaryTransportCost_eq_iInf {p : ℝ} (hp : 1 ≤ p) (D E : FiniteWeightedDiagram) :
    pBoundaryTransportCost p D E =
      ⨅ a : FiniteWeightedBoundaryPlan D.weights E.weights,
        a.powerCost p D.coordinates E.coordinates ^ p⁻¹ :=
  weightedPBoundaryTransportCost_eq_iInf hp D.weights E.weights D.coordinates E.coordinates

theorem powerBoundaryTransportCost_symm (p : ℝ) (D E : FiniteWeightedDiagram) :
    powerBoundaryTransportCost p D E = powerBoundaryTransportCost p E D :=
  weightedPowerBoundaryTransportCost_symm p D.weights E.weights D.coordinates E.coordinates

theorem pBoundaryTransportCost_symm (p : ℝ) (D E : FiniteWeightedDiagram) :
    pBoundaryTransportCost p D E = pBoundaryTransportCost p E D :=
  weightedPBoundaryTransportCost_symm p D.weights E.weights D.coordinates E.coordinates

private theorem isEmpty_zero_supportLabels : IsEmpty ((0 : FiniteWeightedDiagram).supportLabels) := by
  change IsEmpty ↥(0 : FiniteWeightedDiagram).support
  rw [Finsupp.support_zero]
  infer_instance

theorem powerBoundaryTransportCost_zero_right (p : ℝ) (D : FiniteWeightedDiagram) :
    powerBoundaryTransportCost p D 0 =
      ∑ i, (D.weights i : ℝ) * (diagonalCost (D.coordinates i)).toReal ^ p := by
  letI := isEmpty_zero_supportLabels
  exact weightedPowerBoundaryTransportCost_of_isEmpty_right p _ _ _ _

theorem powerBoundaryTransportCost_zero_left (p : ℝ) (D : FiniteWeightedDiagram) :
    powerBoundaryTransportCost p 0 D =
      ∑ i, (D.weights i : ℝ) * (diagonalCost (D.coordinates i)).toReal ^ p := by
  rw [powerBoundaryTransportCost_symm, powerBoundaryTransportCost_zero_right]

theorem pBoundaryTransportCost_zero_right (p : ℝ) (D : FiniteWeightedDiagram) :
    pBoundaryTransportCost p D 0 =
      (∑ i, (D.weights i : ℝ) * (diagonalCost (D.coordinates i)).toReal ^ p) ^ p⁻¹ := by
  change powerBoundaryTransportCost p D 0 ^ p⁻¹ = _
  rw [powerBoundaryTransportCost_zero_right]

theorem pBoundaryTransportCost_zero_left (p : ℝ) (D : FiniteWeightedDiagram) :
    pBoundaryTransportCost p 0 D =
      (∑ i, (D.weights i : ℝ) * (diagonalCost (D.coordinates i)).toReal ^ p) ^ p⁻¹ := by
  rw [pBoundaryTransportCost_symm, pBoundaryTransportCost_zero_right]

@[simp] theorem powerBoundaryTransportCost_zero (p : ℝ) :
    powerBoundaryTransportCost p (0 : FiniteWeightedDiagram) 0 = 0 := by
  letI := isEmpty_zero_supportLabels
  simp [powerBoundaryTransportCost_zero_right]

@[simp] theorem pBoundaryTransportCost_zero {p : ℝ} (hp : 1 ≤ p) :
    pBoundaryTransportCost p (0 : FiniteWeightedDiagram) 0 = 0 := by
  change powerBoundaryTransportCost p 0 0 ^ p⁻¹ = 0
  rw [powerBoundaryTransportCost_zero]
  exact Real.zero_rpow (inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)))

end FiniteWeightedDiagram

end TDA.Persistence
