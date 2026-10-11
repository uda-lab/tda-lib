import TDA.Reeb.GraphPLHeight
import TDA.Reeb.CriticalValues
import TDA.Reeb.GraphRealizationExamples

/-!
# Fixtures for piecewise-linear heights on graph realizations

Acceptance fixtures for `TDA.Reeb.GraphPLHeight`, on the single edge `false — true` of
`⊤ : SimpleGraph Bool` with its dart `d₀ : false → true` from
`TDA.Reeb.Examples.GraphRealization`:

* **Reversal formulas.** With heights `0` and `2`, `dartHeight h02 d₀ t = 2t` and
  `dartHeight h02 d₀.symm t = 2 - 2t` for every `t`, and the reversal equation holds at every `t`.
  At `t = 1/4` the two orientations have different heights; at the midpoint they agree, so a
  witness at `1/2` alone cannot discriminate orientation.
* **Support.** The edge is active over `(1/4, 3/4)` although neither endpoint height lies in it,
  the midpoint is not a witness there, and the reversed dart supports the same edge at the reversed
  parameter. Over `(-∞, 1/2)` one endpoint survives, the other does not, and the edge is active,
  with an interior witness obtained from the endpoint parameter by openness. Over `(3, ∞)` the edge
  is inactive. Activity passes from `(1/4, 3/4)` to `(0, 2)`.
* **Horizontal edge.** With constant height `1`, the edge is active over `I` exactly when `1 ∈ I`:
  active over `(0, 2)` and inactive over `(2, 3)`.

The short names `quarter` and `coe_quarter` also occur in `TDA.Reeb.Examples.ConstructibleSmoothing`,
and `support_mono` as `TDA.Filtration.support_mono`.
-/

open SimpleGraph Topology Set CategoryTheory

/-- The reversal of the unit interval; `open unitInterval` would make `I` a token. -/
local notation "σ" => unitInterval.symm

namespace TDA.Reeb.Examples.GraphPL

open TDA.Reeb.GraphRealization TDA.Reeb.GraphPL TDA.Reeb.OpenInterval
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ edgeGraph_dart half edge_param_injective)

noncomputable section

theorem coe_half : (half : ℝ) = 1 / 2 := rfl

/-- The parameter `1/4`, which distinguishes the two orientations of a dart. -/
def quarter : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩

theorem coe_quarter : (quarter : ℝ) = 1 / 4 := rfl

/-- Heights `0` and `2` on the single edge `false — true`. -/
def h02 : Bool → ℝ
  | false => 0
  | true => 2

theorem dartHeight_d₀ (t : unitInterval) : dartHeight h02 d₀ t = 2 * t := by
  show (1 - (t : ℝ)) * h02 false + (t : ℝ) * h02 true = 2 * t
  simp only [h02]
  ring

theorem dartHeight_d₀_symm (t : unitInterval) : dartHeight h02 d₀.symm t = 2 - 2 * t := by
  show (1 - (t : ℝ)) * h02 true + (t : ℝ) * h02 false = 2 - 2 * t
  simp only [h02]
  ring

/-- Reversal of the two darts at an arbitrary parameter. -/
theorem d₀_reversal (t : unitInterval) :
    dartHeight h02 d₀.symm (σ t) = dartHeight h02 d₀ t :=
  dartHeight_symm h02 d₀ t

theorem d₀_quarter : dartHeight h02 d₀ quarter = 1 / 2 := by
  rw [dartHeight_d₀, coe_quarter]; norm_num

theorem d₀_symm_quarter : dartHeight h02 d₀.symm quarter = 3 / 2 := by
  rw [dartHeight_d₀_symm, coe_quarter]; norm_num

/-- At the parameter `1/4` the two orientations have different heights. -/
theorem orientation_quarter_ne : dartHeight h02 d₀ quarter ≠ dartHeight h02 d₀.symm quarter := by
  rw [d₀_quarter, d₀_symm_quarter]; norm_num

/-- At the midpoint the two orientations agree, so a witness at `1/2` alone cannot discriminate
orientation. -/
theorem orientation_half_eq : dartHeight h02 d₀ half = dartHeight h02 d₀.symm half := by
  rw [dartHeight_d₀, dartHeight_d₀_symm, coe_half]; norm_num

/-- The single edge is the only element of the edge set. -/
theorem edgeGraph_edge_eq (e : edgeGraph.edgeSet) : e = dartEdge d₀ := by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
  rcases edgeGraph_dart d with rfl | rfl
  · rfl
  · exact dartEdge_symm d₀

/-- Interior-only support: neither endpoint height lies in `(1/4, 3/4)`, yet the edge is active. -/
theorem support_interior_active : EdgeActive edgeGraph h02 (ioo (1 / 4) (3 / 4)) (dartEdge d₀) :=
  edgeActive_dartEdge_of_mem (t := quarter) (by rw [d₀_quarter, mem_ioo]; norm_num)

theorem support_interior_no_endpoint :
    h02 false ∉ ioo (1 / 4) (3 / 4) ∧ h02 true ∉ ioo (1 / 4) (3 / 4) := by
  constructor <;> (rw [mem_ioo]; norm_num [h02])

/-- The midpoint is not a support witness there. -/
theorem support_half_not_witness : dartHeight h02 d₀ half ∉ ioo (1 / 4) (3 / 4) := by
  rw [dartHeight_d₀, coe_half, mem_ioo]; norm_num

/-- The reversed dart supports the same edge at the reversed parameter. -/
theorem support_reversed_witness : dartHeight h02 d₀.symm (σ quarter) ∈ ioo (1 / 4) (3 / 4) := by
  rw [d₀_reversal, d₀_quarter, mem_ioo]; norm_num

/-- One surviving endpoint: the incident edge is active. -/
theorem support_endpoint_active : EdgeActive edgeGraph h02 (iio (1 / 2)) (dartEdge d₀) :=
  edgeActive_of_mem (fst_mem_dartEdge d₀) (by show (0 : ℝ) < 1 / 2; norm_num)

theorem support_endpoint_other_out : h02 true ∉ iio (1 / 2) := by
  rw [mem_iio]; norm_num [h02]

/-- From the endpoint parameter `0`, openness yields an interior support witness. -/
theorem support_endpoint_interior :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h02 d₀ t ∈ iio (1 / 2) :=
  exists_interior_of_mem (t := 0) (by rw [dartHeight_zero]; show (0 : ℝ) < 1 / 2; norm_num)

/-- No endpoint and no interior point: the edge is inactive. -/
theorem support_inactive : ¬ EdgeActive edgeGraph h02 (ioi 3) (dartEdge d₀) := by
  rw [edgeActive_dartEdge_iff_nonempty]
  rintro ⟨t, ht⟩
  rw [dartHeight_d₀, mem_ioi] at ht
  linarith [unitInterval.le_one t]

/-- Monotonicity in the interval. -/
theorem support_mono : EdgeActive edgeGraph h02 (ioo 0 2) (dartEdge d₀) :=
  support_interior_active.mono (OpenInterval.le_iff_subset.2 fun x hx => by
    obtain ⟨h₁, h₂⟩ := hx
    show (0 : ℝ) < x ∧ x < 2
    constructor <;> linarith)

/-- Constant height `1`: a horizontal edge. -/
def hconst : Bool → ℝ := fun _ => 1

theorem horizontal_active_iff (I : OpenInterval) :
    EdgeActive edgeGraph hconst I (dartEdge d₀) ↔ (1 : ℝ) ∈ I :=
  edgeActive_dartEdge_iff_of_eq rfl

theorem horizontal_inside_active : EdgeActive edgeGraph hconst (ioo 0 2) (dartEdge d₀) :=
  (horizontal_active_iff _).2 (by rw [mem_ioo]; norm_num)

theorem horizontal_outside_inactive : ¬ EdgeActive edgeGraph hconst (ioo 2 3) (dartEdge d₀) :=
  fun he => by
    have h1 := (horizontal_active_iff _).1 he
    rw [mem_ioo] at h1
    norm_num at h1

end

end TDA.Reeb.Examples.GraphPL
