import TDA.Persistence.RipsSampling
import TDA.Persistence.SimplicialMultivaluedInterleaving

/-!
# The homology of a tuple pseudometric and its metric sample

The tuple indices carry a pseudometric when values repeat. Their closed-diameter
filtration is defined directly, without installing an invalid metric instance.
The zero-shift canonical relation to the finite range produces a natural
isomorphism of homology persistence modules, at every degree and over every ring.
-/

noncomputable section

universe u v
namespace TDA.Persistence.Rips

open TDA.Filtration TDA.Persistence
open scoped NNReal

variable {X : Type u} [MetricSpace X] {n : ℕ}

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- Indices lifted into the metric sample's universe. -/
abbrev TupleVertex (t : Fin n → X) := ULift.{u} (Fin n)

/-- The quotient projection from an index to its sampled value. -/
def tupleProjection (t : Fin n → X) (i : TupleVertex t) : Sample t :=
  sampleProjection t i.down

theorem tupleProjection_surjective (t : Fin n → X) :
    Function.Surjective (tupleProjection t) := by
  intro x
  obtain ⟨i, rfl⟩ := sampleProjection_surjective t x
  exact ⟨ULift.up i, rfl⟩

/-- Distance between quotient images is the tuple's pseudodistance. -/
@[simp] theorem dist_tupleProjection (t : Fin n → X) (i j : TupleVertex t) :
    dist (tupleProjection t i) (tupleProjection t j) = dist (t i.down) (t j.down) := rfl

/-- Diameter on an index face is the diameter of its image in the metric
quotient. This is a genuine filtration even when the projection has fibers. -/
def tupleFilter (t : Fin n → X) :
    FilterFunction (TDA.Filtration.Rips.fullComplex (TupleVertex t)) ℝ := by
  classical
  exact {
    value := fun s => TDA.Filtration.Rips.diameter
      (inferInstance : MetricSpace (Sample t)) (s.val.image (tupleProjection t))
    mono := by
      intro τ σ h
      exact TDA.Filtration.Rips.diameter_mono _
        (Finset.image_mono (tupleProjection t) h) }

/-- A tuple-index face exists exactly when its projected face exists in the
ordinary Rips filtration on the finite metric sample. -/
theorem mem_tupleFilter_iff (t : Fin n → X) (r : ℝ)
    (σ : Finset (TupleVertex t)) :
    σ ∈ (tupleFilter t).sublevel r ↔
      σ.Nonempty ∧ σ.image (tupleProjection t) ∈
        (TDA.Filtration.Rips.filter (inferInstance : MetricSpace (Sample t))).sublevel r := by
  classical
  rw [FilterFunction.mem_sublevel_iff]
  change (∃ hs : σ.Nonempty, TDA.Filtration.Rips.diameter
      (inferInstance : MetricSpace (Sample t)) (σ.image (tupleProjection t)) ≤ r) ↔ _
  rw [FilterFunction.mem_sublevel_iff]
  change (∃ hs : σ.Nonempty, TDA.Filtration.Rips.diameter
      (inferInstance : MetricSpace (Sample t)) (σ.image (tupleProjection t)) ≤ r) ↔
    σ.Nonempty ∧ (∃ hs : (σ.image (tupleProjection t)).Nonempty,
      TDA.Filtration.Rips.diameter (inferInstance : MetricSpace (Sample t))
        (σ.image (tupleProjection t)) ≤ r)
  constructor
  · rintro ⟨hs, hr⟩
    exact ⟨hs, ⟨Finset.image_nonempty.mpr hs, hr⟩⟩
  · rintro ⟨hs, ⟨_, hr⟩⟩
    exact ⟨hs, hr⟩

private def quotientRelation (t : Fin n → X) : SetRel (TupleVertex t) (Sample t) :=
  Function.graph (tupleProjection t)

private theorem quotientRelation_leftTotal (t : Fin n → X) :
    Relator.LeftTotal (fun i x => (i, x) ∈ quotientRelation t) := by
  intro i
  exact ⟨tupleProjection t i, rfl⟩

private theorem quotientRelation_rightTotal (t : Fin n → X) :
    Relator.LeftTotal (fun x i => (x, i) ∈ (quotientRelation t).inv) := by
  intro x
  obtain ⟨i, rfl⟩ := tupleProjection_surjective t x
  exact ⟨i, rfl⟩

private theorem quotientRelation_forward (t : Fin n → X) :
    IsShiftedSimplicialRelation (tupleFilter t).sublevelFiltration
      (TDA.Filtration.Rips.filter (inferInstance : MetricSpace (Sample t))).sublevelFiltration
      (0 : ℝ) (quotientRelation t) := by
  classical
  intro r σ hσ τ hτ hsub
  have himg : τ ⊆ σ.image (tupleProjection t) := by
    intro y hy
    obtain ⟨i, hi, hiy⟩ := hsub hy
    change tupleProjection t i = y at hiy
    exact hiy ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hface := ((mem_tupleFilter_iff t r σ).mp hσ).2
  change τ ∈ ((TDA.Filtration.Rips.filter
    (inferInstance : MetricSpace (Sample t))).sublevel (r + (0 : ℝ))).faces
  simpa only [add_zero] using
    (((TDA.Filtration.Rips.filter (inferInstance : MetricSpace (Sample t))).sublevel r).isRelLowerSet_faces
      hface).2 himg hτ

private theorem quotientRelation_backward (t : Fin n → X) :
    IsShiftedSimplicialRelation
      (TDA.Filtration.Rips.filter (inferInstance : MetricSpace (Sample t))).sublevelFiltration
      (tupleFilter t).sublevelFiltration (0 : ℝ) (quotientRelation t).inv := by
  classical
  intro r τ hτ σ hσ hsub
  have himg : σ.image (tupleProjection t) ⊆ τ := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, hxi⟩ := hsub hi
    change tupleProjection t i = x at hxi
    change x ∈ τ at hx
    simpa only [hxi] using hx
  have hface :=
    (((TDA.Filtration.Rips.filter (inferInstance : MetricSpace (Sample t))).sublevel r).isRelLowerSet_faces
      hτ).2 himg (Finset.image_nonempty.mpr hσ)
  change σ ∈ (tupleFilter t).sublevel (r + (0 : ℝ))
  simpa only [add_zero] using (mem_tupleFilter_iff t r σ).mpr ⟨hσ, hface⟩

/-- The canonical quotient relation gives a natural isomorphism of persistence
modules, for every homology degree and coefficient ring. -/
def tupleHomologyIso (R : Type v) [Ring R] (t : Fin n → X)
    [LinearOrder (Sample t)] (degree : ℕ) :
    simplicialHomologyPModule R (tupleFilter t).sublevelFiltration degree ≅
      simplicialHomologyPModule R
        (TDA.Filtration.Rips.filter (inferInstance : MetricSpace (Sample t))).sublevelFiltration
        degree := by
  classical
  exact (multivaluedSimplicialHomologyConverseInterleaving R
    (ε := (0 : ℝ≥0)) (quotientRelation_leftTotal t) (quotientRelation_rightTotal t)
    (quotientRelation_forward t) (quotientRelation_backward t) degree).toIso

end TDA.Persistence.Rips
