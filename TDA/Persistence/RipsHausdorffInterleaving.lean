import TDA.Persistence.RipsRelationInterleaving
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Rips module stability for arbitrary ambient images

Isometric images at finite Hausdorff distance give a Rips homology interleaving
at every parameter strictly greater than twice that distance. Near points are
chosen with positive slack, so neither closedness nor compactness of the images
is required. Passing to the infimum gives a module distance bound, over every
ring and in every degree. Nonempty totally bounded images satisfy the required
finiteness condition.

The extended-distance version also handles infinite Hausdorff distance without
using the real-valued convention at infinity. These are module statements;
locally finite persistence diagrams and their algebraic stability are separate
foundations. The geometry is the correspondence mechanism of Chazal--de
Silva--Oudot, arXiv:1207.3885v3, §4.2 and Lemma 4.3. Closed diameter thresholds
and the empty negative tail are the library's conventions.
-/

universe u v w

namespace TDA.Persistence.Rips

open TDA.Filtration Set Metric
open scoped NNReal ENNReal

noncomputable section

/-- At every strict allowance above twice the finite Hausdorff distance,
near points give a total bounded-distortion relation. The images may be nonclosed. -/
theorem exists_relation_distortion_le_of_hausdorffDist_lt
    {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {f : X → Z} {g : Y → Z} (hf : Isometry f) (hg : Isometry g)
    (hfin : hausdorffEDist (range f) (range g) ≠ ⊤)
    {ε : ℝ≥0} (hε : 2 * hausdorffDist (range f) (range g) < (ε : ℝ)) :
    ∃ C : SetRel X Y,
      Relator.LeftTotal (fun x y => (x, y) ∈ C) ∧
      Relator.LeftTotal (fun y x => (y, x) ∈ C.inv) ∧
      ∀ x x' y y', (x, y) ∈ C → (x', y') ∈ C →
        |dist x x' - dist y y'| ≤ (ε : ℝ) := by
  have hr : hausdorffDist (range f) (range g) < (ε : ℝ) / 2 := by linarith
  let C : SetRel X Y := {p | dist (f p.1) (g p.2) < (ε : ℝ) / 2}
  refine ⟨C, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ :=
      exists_dist_lt_of_hausdorffDist_lt (mem_range_self x) hr hfin
    exact ⟨y, hy⟩
  · intro y
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ :=
      exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y) hr hfin
    exact ⟨x, hx⟩
  · intro x x' y y' hxy hx'y'
    change dist (f x) (g y) < (ε : ℝ) / 2 at hxy
    change dist (f x') (g y') < (ε : ℝ) / 2 at hx'y'
    rw [← hf.dist_eq, ← hg.dist_eq]
    have h := dist_dist_dist_le (f x) (f x') (g y) (g y')
    rw [Real.dist_eq] at h
    exact h.trans (by linarith)

section Modules

variable {X Y : Type u} [LinearOrder X] [LinearOrder Y]
  [MetricSpace X] [MetricSpace Y]
variable (R : Type v) [Ring R]

/-- The actual canonical Rips interleaving from Hausdorff near points with positive slack.
The auxiliary vertex orders need not be preserved by the isometries. -/
def hausdorffInterleavingOfLt {Z : Type w} [MetricSpace Z]
    {f : X → Z} {g : Y → Z} (hf : Isometry f) (hg : Isometry g)
    (hfin : hausdorffEDist (range f) (range g) ≠ ⊤)
    {ε : ℝ≥0} (hε : 2 * hausdorffDist (range f) (range g) < (ε : ℝ)) (n : ℕ) :
    RealInterleaving ε (sublevelModule R (Rips.filter (inferInstance : MetricSpace X)) n)
      (sublevelModule R (Rips.filter (inferInstance : MetricSpace Y)) n) := by
  let C := Classical.choose (exists_relation_distortion_le_of_hausdorffDist_lt hf hg hfin hε)
  have hC := Classical.choose_spec
    (exists_relation_distortion_le_of_hausdorffDist_lt hf hg hfin hε)
  exact relationInterleaving R inferInstance inferInstance (C := C) hC.1 hC.2.1 hC.2.2 n

/-- The infimum of the genuine slack interleavings is at most twice the finite
ambient Hausdorff distance. No minimizing near point or correspondence is assumed. -/
theorem realInterleavingDistance_le_two_mul_hausdorffDist_of_ne_top
    {Z : Type w} [MetricSpace Z] {f : X → Z} {g : Y → Z}
    (hf : Isometry f) (hg : Isometry g)
    (hfin : hausdorffEDist (range f) (range g) ≠ ⊤) (n : ℕ) :
    realInterleavingDistance (sublevelModule R (Rips.filter (inferInstance : MetricSpace X)) n)
      (sublevelModule R (Rips.filter (inferInstance : MetricSpace Y)) n) ≤
      ENNReal.ofReal (2 * hausdorffDist (range f) (range g)) := by
  let δ : ℝ≥0 := ⟨2 * hausdorffDist (range f) (range g),
    mul_nonneg (by norm_num) hausdorffDist_nonneg⟩
  calc
    _ ≤ (δ : ℝ≥0∞) := by
      apply ENNReal.le_of_forall_pos_le_add
      intro η hη _
      have hε : 2 * hausdorffDist (range f) (range g) < ((δ + η : ℝ≥0) : ℝ) := by
        change 2 * hausdorffDist (range f) (range g) <
          2 * hausdorffDist (range f) (range g) + (η : ℝ)
        exact lt_add_of_pos_right _ hη
      simpa only [ENNReal.coe_add] using
        (hausdorffInterleavingOfLt R hf hg hfin hε n).distance_le
    _ = _ := ENNReal.coe_nnreal_eq δ

/-- Extended Hausdorff distance controls the module distance for arbitrary
isometric images, including unbounded images and empty-space boundary cases. -/
theorem realInterleavingDistance_le_two_mul_hausdorffEDist
    {Z : Type w} [MetricSpace Z] {f : X → Z} {g : Y → Z}
    (hf : Isometry f) (hg : Isometry g) (n : ℕ) :
    realInterleavingDistance (sublevelModule R (Rips.filter (inferInstance : MetricSpace X)) n)
      (sublevelModule R (Rips.filter (inferInstance : MetricSpace Y)) n) ≤
      (2 : ℝ≥0∞) * hausdorffEDist (range f) (range g) := by
  by_cases hfin : hausdorffEDist (range f) (range g) = ⊤
  · simp [hfin]
  · have h := realInterleavingDistance_le_two_mul_hausdorffDist_of_ne_top R hf hg hfin n
    have heq : ENNReal.ofReal (2 * hausdorffDist (range f) (range g)) =
        (2 : ℝ≥0∞) * hausdorffEDist (range f) (range g) := by
      rw [ENNReal.ofReal_mul (by norm_num), hausdorffDist, ENNReal.ofReal_toReal hfin]
      norm_num
    exact h.trans_eq heq

/-- Nonempty totally bounded ambient images have finite Hausdorff distance and
satisfy the diameter-scale factor-two module bound, without closedness or completeness. -/
theorem realInterleavingDistance_le_two_mul_hausdorffDist_of_totallyBounded
    [Nonempty X] [Nonempty Y] {Z : Type w} [MetricSpace Z]
    {f : X → Z} {g : Y → Z} (hf : Isometry f) (hg : Isometry g)
    (hX : TotallyBounded (range f)) (hY : TotallyBounded (range g)) (n : ℕ) :
    realInterleavingDistance (sublevelModule R (Rips.filter (inferInstance : MetricSpace X)) n)
      (sublevelModule R (Rips.filter (inferInstance : MetricSpace Y)) n) ≤
      ENNReal.ofReal (2 * hausdorffDist (range f) (range g)) :=
  realInterleavingDistance_le_two_mul_hausdorffDist_of_ne_top R hf hg
    (hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      hX.isBounded hY.isBounded) n

end Modules
end
end TDA.Persistence.Rips
