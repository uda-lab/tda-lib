import TDA.Filtration.Alpha
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsor

set_option autoImplicit false

/-!
# Closed alpha complexes on the line and on a square

Midpoints witness the entry of an edge. Three ordered sites exclude the outer edge,
while the center of a square witnesses all four vertices at the same grade.
-/

namespace TDA.Filtration.Alpha.Examples

/-- A one-site configuration has its full simplex exactly from grade zero. -/
theorem singleton_stage (sites : Fin 1 ↪ ℝ) (t : ℝ) :
    Finset.univ ∈ complex sites t ↔ 0 ≤ t := by
  rw [show (Finset.univ : Finset (Fin 1)) = {0} by decide]
  exact singleton_mem_complex_iff sites 0 t

/-- The edge between two distinct sites enters at their squared half-distance. -/
theorem two_site_edge_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sites : Fin 2 ↪ E) (t : ℝ) :
    Finset.univ ∈ complex sites t ↔ (dist (sites 0) (sites 1) / 2) ^ 2 ≤ t := by
  rw [mem_complex_iff sites (Finset.mem_univ 0)]
  constructor
  · rintro ⟨x, hx, hxt⟩
    have heq := dist_eq_of_mem_commonCells sites (Finset.mem_univ 1) (Finset.mem_univ 0) hx
    have h := dist_triangle_left (sites 0) (sites 1) x
    rw [heq] at h
    exact ((sq_le_sq₀ (by positivity) dist_nonneg).2 (by linarith)).trans hxt
  · intro ht
    let m := midpoint ℝ (sites 0) (sites 1)
    have hd (v : Fin 2) : dist m (sites v) = dist (sites 0) (sites 1) / 2 := by
      fin_cases v <;> simp [m, div_eq_inv_mul]
    exact ⟨m, fun v _ w => (hd v).trans_le (hd w).symm.le, (hd 0) ▸ ht⟩

/-- The intervening site excludes the outer pair from the full closed Voronoi nerve. -/
theorem collinear_outer_pair_not_mem (sites : Fin 3 ↪ ℝ)
    (h₀₁ : sites 0 < sites 1) (h₁₂ : sites 1 < sites 2) :
    ({0, 2} : Finset (Fin 3)) ∉ carrier sites := by
  rintro ⟨_, x, hx⟩
  rcases le_total x (sites 1) with h | h
  · have h₂ := hx 2 (by simp) 1
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (h.trans h₁₂.le)),
      abs_of_nonpos (sub_nonpos.mpr h)] at h₂
    linarith
  · have h₀ := hx 0 (by simp) 1
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (h₀₁.le.trans h)),
      abs_of_nonneg (sub_nonneg.mpr h)] at h₀
    linarith

/-- The midpoint of the first two collinear sites lies in both closed cells and
witnesses their edge at equality in the squared cutoff. -/
theorem collinear_midpoint_edge (sites : Fin 3 ↪ ℝ)
    (h₀₁ : sites 0 < sites 1) (h₁₂ : sites 1 < sites 2) :
    ({0, 1} : Finset (Fin 3)) ∈ complex sites ((dist (sites 0) (sites 1) / 2) ^ 2) := by
  let m := (sites 0 + sites 1) / 2
  have hm₀ : sites 0 ≤ m := by dsimp [m]; linarith
  have hm₁ : m ≤ sites 1 := by dsimp [m]; linarith
  have hd₀ : dist m (sites 0) = dist (sites 0) (sites 1) / 2 := by
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hm₀),
      abs_of_nonpos (sub_nonpos.mpr h₀₁.le)]
    dsimp [m]
    ring
  have htie : dist m (sites 0) = dist m (sites 1) := by
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hm₀),
      abs_of_nonpos (sub_nonpos.mpr hm₁)]
    dsimp [m]
    ring
  have hfar : dist m (sites 1) ≤ dist m (sites 2) := by
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hm₁),
      abs_of_nonpos (sub_nonpos.mpr (hm₁.trans h₁₂.le))]
    linarith
  refine (mem_complex_iff sites (v := 0) (by simp) _).2 ⟨m, ?_, by rw [hd₀]⟩
  intro v hv w
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> fin_cases w <;>
    first | exact le_rfl | exact htie.le | exact htie.symm.le | exact hfar | exact htie.trans_le hfar

private noncomputable def corners : Fin 4 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0], !₂[2, 0], !₂[0, 2], !₂[2, 2]]

/-- The four labelled corners of the square of side two. -/
noncomputable def squareSites : Fin 4 ↪ EuclideanSpace ℝ (Fin 2) where
  toFun := corners
  inj' := by
    intro i j h
    have h₀ := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
    have h₁ := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h
    have heq := And.intro h₀ h₁
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [corners] at heq

/-- The common center of all four closed cells gives a four-vertex simplex at grade two. -/
theorem square_four_vertex_simplex : Finset.univ ∈ complex squareSites 2 := by
  let c : EuclideanSpace ℝ (Fin 2) := !₂[1, 1]
  have hd (v : Fin 4) : dist c (squareSites v) ^ 2 = 2 := by
    change dist c (corners v) ^ 2 = 2
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
    fin_cases v <;> norm_num [Real.dist_eq, corners, c]
  refine (mem_complex_iff squareSites (Finset.mem_univ 0) 2).2 ⟨c, ?_, (hd 0).le⟩
  intro v _ w
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).1 ((hd v).trans_le (hd w).symm.le)

end TDA.Filtration.Alpha.Examples
