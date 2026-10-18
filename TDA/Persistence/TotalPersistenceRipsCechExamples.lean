import TDA.Persistence.TotalPersistenceRipsCech
import TDA.Persistence.LogScaleDiagramComparisonExamples
import TDA.Persistence.SublevelConstructibleExamples
import TDA.Filtration.CechExamples

set_option autoImplicit false

/-!
# Fixtures for total persistence of finite Rips and Čech diagrams

These fixtures test the sharp two-point bound, the triangle and repeated-label bounds, positive
scaling, the essential-bar count, and the exponent-zero bar-count interpretation.
-/

namespace TDA.Persistence.TotalPersistenceRipsCechExamples

open CategoryTheory CategoryTheory.Limits TDA.Simplicial TDA.Filtration TDA.Persistence
open TDA.Persistence.Examples
open TDA.Persistence.FiniteConstructible
open TDA.Persistence.SublevelConstructibleExamples
open TDA.Persistence.LogScaleDiagramExamples
open TDA.Persistence.LogScaleDiagramComparisonExamples
open TDA.Persistence.Reduction.Examples
open TDA.Filtration.Cech.Examples
open scoped NNReal ENNReal

private theorem twoPoints_diameter :
    Rips.diameter TwoPoints.metric (Finset.univ : Finset (Fin 2)) = 2 := by
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
    ext v
    fin_cases v <;> simp
  rw [huniv, Rips.diameter_pair, TwoPoints.metric_dist, TwoPoints.dist_pts]

private theorem twoPoints_rips_finitePart :
    finitePart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points = {(0, 2)} := by
  rw [twoPoints_rips_dgm_zero]
  rfl

private theorem twoPoints_cech_finitePart :
    finitePart (dgm (ZMod 2) (Cech.filter TwoPoints.pts) 0).points = {(0, 1)} := by
  rw [twoPoints_cech_dgm_zero]
  rfl

/-- The two-point Rips diagram attains the degree-`p` total-persistence bound. -/
theorem twoPoints_rips_totalPersistence (p : ℕ) :
    (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).totalPersistence p = 2 ^ p := by
  rw [Diagram.totalPersistence, twoPoints_rips_finitePart]
  norm_num

/-- The two-point Rips right-hand side is exactly its total persistence. -/
theorem twoPoints_rips_bound_attained (p : ℕ) :
    (Nat.choose (Fintype.card (Fin 2)) (0 + 2) : ℝ) *
        Rips.diameter TwoPoints.metric Finset.univ ^ p = 2 ^ p := by
  rw [twoPoints_diameter]
  norm_num [Nat.choose]

/-- The Rips total-persistence bound `Rips.totalPersistence_dgm_le` is attained with equality on this fixture. -/
theorem twoPoints_rips_totalPersistence_eq_bound (p : ℕ) :
    (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).totalPersistence p =
      (Nat.choose (Fintype.card (Fin 2)) (0 + 2) : ℝ) *
        Rips.diameter TwoPoints.metric Finset.univ ^ p := by
  rw [twoPoints_rips_totalPersistence, twoPoints_rips_bound_attained]

/-- The Rips total-persistence bound `Rips.totalPersistence_dgm_le` holds for the two-point fixture. -/
theorem twoPoints_rips_totalPersistence_le_bound (p : ℕ) :
    (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).totalPersistence p ≤
      (Nat.choose (Fintype.card (Fin 2)) (0 + 2) : ℝ) *
        Rips.diameter TwoPoints.metric Finset.univ ^ p := by
  exact Rips.totalPersistence_dgm_le (k := ZMod 2) TwoPoints.metric 0 p

/-- The two-point Čech diagram has one finite bar of length one. -/
theorem twoPoints_cech_totalPersistence (p : ℕ) :
    (dgm (ZMod 2) (Cech.filter TwoPoints.pts) 0).totalPersistence p = 1 := by
  rw [Diagram.totalPersistence, twoPoints_cech_finitePart]
  norm_num

private theorem triangle_cech_radius_le_three :
    Cech.radiusAt Triangle.pts (Triangle.pts 0) Finset.univ ≤ 3 := by
  rw [Cech.radiusAt_le_iff]
  constructor
  · norm_num
  · intro v hv
    fin_cases v
    · simp
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [Triangle.pts, Triangle.pts_zero, Triangle.pts_one])
    · exact Triangle.dist_le_of_sq_le (by norm_num)
        (by norm_num [Triangle.pts, Triangle.pts_zero, Triangle.pts_one, Triangle.pts_two])

/-- The triangle Čech degree-one finite-bar count is bounded by one. -/
theorem triangle_cech_card_finitePart_one_le :
    (finitePart (dgm (ZMod 2) (Cech.filter Triangle.pts) 1).points).card ≤ 1 := by
  calc
    (finitePart (dgm (ZMod 2) (Cech.filter Triangle.pts) 1).points).card ≤
        Nat.card (Face (Rips.fullComplex (Fin 3)) (1 + 1)) :=
      card_finitePart_dgm_le (ZMod 2) (Cech.filter Triangle.pts) 1
    _ = Nat.choose (Fintype.card (Fin 3)) ((1 + 1) + 1) :=
      card_face_fullComplex (V := Fin 3) (n := 1 + 1)
    _ = 1 := by norm_num [Nat.choose]

/-- The triangle Rips degree-one finite-bar count is bounded by one. -/
theorem triangle_rips_card_finitePart_one_le :
    (finitePart (dgm (ZMod 2) (Rips.filter Triangle.metric) 1).points).card ≤ 1 := by
  calc
    (finitePart (dgm (ZMod 2) (Rips.filter Triangle.metric) 1).points).card ≤
        Nat.card (Face (Rips.fullComplex (Fin 3)) (1 + 1)) :=
      card_finitePart_dgm_le (ZMod 2) (Rips.filter Triangle.metric) 1
    _ = Nat.choose (Fintype.card (Fin 3)) ((1 + 1) + 1) :=
      card_face_fullComplex (V := Fin 3) (n := 1 + 1)
    _ = 1 := by norm_num [Nat.choose]

/-- The triangle Čech degree-one total persistence is bounded by three. -/
theorem triangle_cech_totalPersistence_one_le :
    (dgm (ZMod 2) (Cech.filter Triangle.pts) 1).totalPersistence 1 ≤ 3 := by
  have htotal := Cech.totalPersistence_dgm_le_radiusAt
    (k := ZMod 2) Triangle.pts (Triangle.pts 0) 1 1
  norm_num [Nat.choose] at htotal
  exact htotal.trans triangle_cech_radius_le_three

/-- In degree two, the triangle has no finite Čech or Rips bars by the face count. -/
theorem triangle_card_finitePart_two_eq_zero :
    (finitePart (dgm (ZMod 2) (Cech.filter Triangle.pts) 2).points).card = 0 ∧
      (finitePart (dgm (ZMod 2) (Rips.filter Triangle.metric) 2).points).card = 0 := by
  have hcech :
      (finitePart (dgm (ZMod 2) (Cech.filter Triangle.pts) 2).points).card ≤ 0 := by
    calc
      (finitePart (dgm (ZMod 2) (Cech.filter Triangle.pts) 2).points).card ≤
          Nat.card (Face (Rips.fullComplex (Fin 3)) (2 + 1)) :=
        card_finitePart_dgm_le (ZMod 2) (Cech.filter Triangle.pts) 2
      _ = Nat.choose (Fintype.card (Fin 3)) ((2 + 1) + 1) :=
        card_face_fullComplex (V := Fin 3) (n := 2 + 1)
      _ = 0 := by norm_num [Nat.choose]
  have hrips :
      (finitePart (dgm (ZMod 2) (Rips.filter Triangle.metric) 2).points).card ≤ 0 := by
    calc
      (finitePart (dgm (ZMod 2) (Rips.filter Triangle.metric) 2).points).card ≤
          Nat.card (Face (Rips.fullComplex (Fin 3)) (2 + 1)) :=
        card_finitePart_dgm_le (ZMod 2) (Rips.filter Triangle.metric) 2
      _ = Nat.choose (Fintype.card (Fin 3)) ((2 + 1) + 1) :=
        card_face_fullComplex (V := Fin 3) (n := 2 + 1)
      _ = 0 := by norm_num [Nat.choose]
  exact ⟨Nat.eq_zero_of_le_zero hcech, Nat.eq_zero_of_le_zero hrips⟩

private theorem repeated_cech_radius_zero :
    Cech.radiusAt Repeated.pts (0 : ℝ) (Finset.univ : Finset (Fin 2)) = 0 := by
  apply le_antisymm
  · rw [Cech.radiusAt_le_iff]
    constructor
    · norm_num
    · intro v hv
      simp [Repeated.pts]
  · exact Cech.radiusAt_nonneg Repeated.pts 0 Finset.univ

/-- Repeated labels have no finite Čech bars in any degree; no label metric is used. -/
theorem repeated_cech_finitePart_eq_zero (n : ℕ) :
    finitePart (dgm (ZMod 2) (Cech.filter Repeated.pts) n).points = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro x hx
  have hcoord := (Cech.dgm_coordinates_le_radiusAt
    (k := ZMod 2) Repeated.pts (0 : ℝ) n).1 x hx
  rw [repeated_cech_radius_zero] at hcoord
  linarith [hcoord.1, hcoord.2.1, hcoord.2.2]

/-- Repeated labels give zero total persistence in every degree and exponent. -/
theorem repeated_cech_totalPersistence (n p : ℕ) :
    (dgm (ZMod 2) (Cech.filter Repeated.pts) n).totalPersistence p = 0 := by
  apply totalPersistence_empty
  exact repeated_cech_finitePart_eq_zero n

/-- The transported filled-triangle degree-one diagram is the single bar `(1,2)`. -/
theorem filledReal_dgm_one :
    (dgm (ZMod 2) filledReal 1).points =
      {((1 : ℝ), ((2 : ℝ) : WithTop ℝ))} := by
  rw [← moduleDiagram_sublevelModule]
  exact filledReal_moduleDiagram_one

private theorem filledReal_finitePart_one :
    finitePart (dgm (ZMod 2) filledReal 1).points = {((1 : ℝ), (2 : ℝ))} := by
  rw [filledReal_dgm_one]
  rfl

/-- The filled-triangle degree-one diagram has first-order total persistence one. -/
theorem filledReal_totalPersistence_one :
    (dgm (ZMod 2) filledReal 1).totalPersistence 1 = 1 := by
  rw [Diagram.totalPersistence, filledReal_finitePart_one]
  norm_num

private theorem filledReal_totalPersistence_two :
    (dgm (ZMod 2) filledReal 1).totalPersistence 2 = 1 := by
  rw [Diagram.totalPersistence, filledReal_finitePart_one]
  norm_num

/-- Scaling the filled-triangle filter by two doubles its first-order total persistence. -/
theorem filledReal_scale_totalPersistence_one :
    (dgm (ZMod 2) (filledReal.scale 2 two_pos) 1).totalPersistence 1 = 2 := by
  rw [dgm_scale, totalPersistence_scale, filledReal_totalPersistence_one]
  norm_num

/-- Scaling the filled-triangle filter by two quadruples its second-order total persistence. -/
theorem filledReal_scale_totalPersistence_two :
    (dgm (ZMod 2) (filledReal.scale 2 two_pos) 1).totalPersistence 2 = 4 := by
  rw [dgm_scale, totalPersistence_scale, filledReal_totalPersistence_two]
  norm_num

/-- The two-point Rips degree-zero diagram has one essential bar. -/
theorem twoPoints_rips_card_essentialPart :
    (essentialPart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points).card = 1 := by
  rw [twoPoints_rips_dgm_zero]
  rfl

/-- The two-point essential-bar count satisfies the general face-count bound, non-sharply. -/
theorem twoPoints_rips_card_essentialPart_le :
    (essentialPart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points).card ≤
      Nat.choose 2 1 := by
  calc
    (essentialPart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points).card ≤
        Nat.card (Face (Rips.fullComplex (Fin 2)) 0) :=
      card_essentialPart_dgm_le (ZMod 2) (Rips.filter TwoPoints.metric) 0
    _ = Nat.choose (Fintype.card (Fin 2)) (0 + 1) :=
      card_face_fullComplex (V := Fin 2) (n := 0)
    _ = Nat.choose 2 1 := by norm_num

/-- On the sharp two-point fixture, exponent zero records the finite-bar count. -/
theorem twoPoints_rips_totalPersistence_zero :
    (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).totalPersistence 0 = 1 ∧
      (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).totalPersistence 0 =
        Fintype.card (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).finiteOccurrences := by
  constructor
  · simpa using twoPoints_rips_totalPersistence 0
  · exact totalPersistence_zero _

end TDA.Persistence.TotalPersistenceRipsCechExamples
