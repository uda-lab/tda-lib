import TDA.Filtration.RationalAlpha.Candidates
import TDA.Filtration.Alpha
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Completeness of the rational planar centers

At a nearest point of a common closed cell, displacement from a face site is
orthogonal to every direction tangent to the active bisectors. Their normals
have rank zero, one or two, determining a site, midpoint or circumcenter.
-/

namespace TDA.Filtration.RationalAlpha

open Filter _root_.Topology
open scoped Matrix

abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def point (x y : ℝ) : Plane := !₂[x, y]

def castPoint (p : Point) : Plane := point p.1 p.2

/-- The first real coordinate of a cast rational point. -/
theorem castPoint_apply_zero (p : Point) : castPoint p 0 = (p.1 : ℝ) := by
  simp [castPoint, point]

/-- The second real coordinate of a cast rational point. -/
theorem castPoint_apply_one (p : Point) : castPoint p 1 = (p.2 : ℝ) := by
  simp [castPoint, point]

theorem distSq_coordinates (c p : Plane) :
    dist c p ^ 2 = (c 0 - p 0)^2 + (c 1 - p 1)^2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

theorem distSq_cast (c p : Point) : dist (castPoint c) (castPoint p) ^ 2 = (sqDist c p : ℝ) := by
  rw [distSq_coordinates]
  simp [castPoint, point, sqDist]

theorem castPoint_injective : Function.Injective castPoint := by
  intro p q h
  apply Prod.ext
  · have hc := congrArg (fun c : Plane => c 0) h
    simp [castPoint, point] at hc
    exact_mod_cast hc
  · have hc := congrArg (fun c : Plane => c 1) h
    simp [castPoint, point] at hc
    exact_mod_cast hc

/-- Cast a labelled rational site embedding into the real plane. -/
def castSites {V : Type*} (p : V ↪ Point) : V ↪ Plane :=
  p.trans ⟨castPoint, castPoint_injective⟩

@[simp] theorem castSites_apply {V : Type*} (p : V ↪ Point) (v : V) :
    castSites p v = castPoint (p v) := rfl

variable {n : ℕ}

def realSites (p : Fin n ↪ Point) : Fin n ↪ Plane :=
  castSites p

/-- Evaluation of a rational linear form on the real plane. -/
def linearForm (u : Point) (x : Plane) : ℝ := u.1 * x 0 + u.2 * x 1

private theorem dist_le_iff (p q : Point) (x : Plane) :
    dist x (castPoint p) ≤ dist x (castPoint q) ↔
      linearForm (normal p q) x ≤ (offset p q : ℝ) := by
  rw [← sq_le_sq₀ dist_nonneg dist_nonneg, distSq_coordinates, distSq_coordinates]
  simp [castPoint, point, linearForm, normal, offset]
  constructor <;> intro h <;> nlinarith only [h]

private theorem dist_eq_iff (p q : Point) (x : Plane) :
    dist x (castPoint p) = dist x (castPoint q) ↔
      linearForm (normal p q) x = (offset p q : ℝ) := by
  rw [le_antisymm_iff, dist_le_iff, dist_le_iff]
  simp [linearForm, normal, offset]
  constructor
  · rintro ⟨h, k⟩
    linarith
  · intro h
    constructor <;> linarith

/-- Common closed cells are cut out by rational affine inequalities, with
equality on every site of the face. -/
theorem mem_commonCells_iff (p : Fin n ↪ Point) {s : Finset (Fin n)} {v : Fin n}
    (hv : v ∈ s) (x : Plane) :
    x ∈ Alpha.commonCells (realSites p) s ↔
      (∀ j, linearForm (normal (p v) (p j)) x ≤ (offset (p v) (p j) : ℝ)) ∧
      ∀ j ∈ s, linearForm (normal (p v) (p j)) x = (offset (p v) (p j) : ℝ) := by
  constructor
  · intro h
    exact ⟨fun j => (dist_le_iff _ _ _).1 (h v hv j),
      fun j hj => (dist_eq_iff _ _ _).1 (Alpha.dist_eq_of_mem_commonCells _ hv hj h)⟩
  · rintro ⟨hl, he⟩ j hj k
    exact ((dist_eq_iff _ _ _).2 (he j hj)).symm.le.trans ((dist_le_iff _ _ _).2 (hl k))

private theorem local_feasible_line {I : Type*} [Finite I]
    (a b k : I → ℝ) (x y u v : ℝ)
    (feasible : ∀ i, a i * x + b i * y ≤ k i)
    (tangent : ∀ i, a i * x + b i * y = k i → a i * u + b i * v = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i * (x + t * u) + b i * (y + t * v) ≤ k i := by
  apply Filter.eventually_all.2
  intro i
  by_cases hi : a i * x + b i * y = k i
  · exact Filter.Eventually.of_forall fun t => le_of_eq (calc
      a i * (x + t * u) + b i * (y + t * v) =
          (a i * x + b i * y) + t * (a i * u + b i * v) := by ring
      _ = k i := by rw [hi, tangent i hi, mul_zero, add_zero])
  · have hc : Continuous (fun t : ℝ => a i * (x + t * u) + b i * (y + t * v)) := by
      fun_prop
    have hopen : IsOpen {t : ℝ | a i * (x + t * u) + b i * (y + t * v) < k i} :=
      isOpen_lt hc continuous_const
    have hzero : (0 : ℝ) ∈ {t : ℝ | a i * (x + t * u) + b i * (y + t * v) < k i} := by
      simpa using lt_of_le_of_ne (feasible i) hi
    filter_upwards [hopen.mem_nhds hzero] with t ht
    exact le_of_lt ht

-- In rank zero both coordinate directions are tangent.
private theorem eq_site_of_all_tangent (x y px py : ℝ)
    (h : ∀ u v : ℝ, (x - px) * u + (y - py) * v = 0) : x = px ∧ y = py := by
  constructor <;> linarith [h 1 0, h 0 1]

-- In rank one the bisector and perpendicular-line identities pin the midpoint.
private theorem eq_midpoint_of_bisector_and_tangent (x y px py qx qy : ℝ)
    (hne : px ≠ qx ∨ py ≠ qy)
    (heq : (x-px)^2 + (y-py)^2 = (x-qx)^2 + (y-qy)^2)
    (hortho : (x-px) * (-(qy-py)) + (y-py) * (qx-px) = 0) :
    x = (px + qx)/2 ∧ y = (py + qy)/2 := by
  have hden : (qx-px)^2 + (qy-py)^2 ≠ 0 := by
    rcases hne with h | h
    · have hpos := sq_pos_of_ne_zero (sub_ne_zero.mpr h.symm)
      linarith [sq_nonneg (qy-py)]
    · have hpos := sq_pos_of_ne_zero (sub_ne_zero.mpr h.symm)
      linarith [sq_nonneg (qx-px)]
  have hdot : (x-(px+qx)/2) * (qx-px) + (y-(py+qy)/2) * (qy-py) = 0 := by
    nlinarith only [heq]
  have hcross : (x-(px+qx)/2) * (-(qy-py)) + (y-(py+qy)/2) * (qx-px) = 0 := by
    nlinarith only [hortho]
  have hx : (x-(px+qx)/2) * ((qx-px)^2 + (qy-py)^2) = 0 := by
    linear_combination (qx-px) * hdot - (qy-py) * hcross
  have hy : (y-(py+qy)/2) * ((qx-px)^2 + (qy-py)^2) = 0 := by
    linear_combination (qy-py) * hdot + (qx-px) * hcross
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right hden),
    sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right hden)⟩

-- In rank two the intersection of the two active bisectors is given by Cramer's rule.
private theorem eq_cramer_of_independent_lines (a b c d e f x y : ℝ)
    (hdet : a*d-b*c ≠ 0) (hx : a*x+b*y=e) (hy : c*x+d*y=f) :
    x = (e*d-b*f)/(a*d-b*c) ∧ y = (a*f-e*c)/(a*d-b*c) := by
  constructor <;> apply (eq_div_iff hdet).2
  · linear_combination d * hx - b * hy
  · linear_combination a * hy - c * hx

/-- Every real minimizer on a nonempty common cell occurs in the rational list. -/
theorem minimizer_mem_centers (p : Fin n ↪ Point) {s : Finset (Fin n)} {v : Fin n}
    (hv : v ∈ s) (x : Plane) (hx : x ∈ Alpha.commonCells (realSites p) s)
    (hmin : ∀ y ∈ Alpha.commonCells (realSites p) s,
      dist x (realSites p v)^2 ≤ dist y (realSites p v)^2) :
    ∃ c ∈ centers p, castPoint c = x := by
  let u (j : Fin n) := normal (p v) (p j)
  let k (j : Fin n) : ℝ := offset (p v) (p j)
  let active (j : Fin n) := linearForm (u j) x = k j
  obtain ⟨hfeas, hface⟩ := (mem_commonCells_iff p hv x).1 hx
  have orthogonal (a b : ℝ)
      (ht : ∀ j, active j → (u j).1 * a + (u j).2 * b = 0) :
      (x 0 - (p v).1) * a + (x 1 - (p v).2) * b = 0 := by
    let f := fun t : ℝ => (x 0 + t * a - (p v).1)^2 + (x 1 + t * b - (p v).2)^2
    have hm : IsLocalMin f 0 := by
      apply (local_feasible_line (fun j => (u j).1) (fun j => (u j).2) k
        (x 0) (x 1) a b hfeas ht).mono
      intro t h
      let y := point (x 0 + t * a) (x 1 + t * b)
      have hy : y ∈ Alpha.commonCells (realSites p) s := by
        apply (mem_commonCells_iff p hv _).2
        refine ⟨fun j => ?_, fun j hj => ?_⟩
        · simpa [linearForm, y, point, u, k] using h j
        · have he : (u j).1 * x 0 + (u j).2 * x 1 = k j := hface j hj
          have htj := ht j he
          change (u j).1 * (x 0 + t * a) + (u j).2 * (x 1 + t * b) = k j
          linear_combination he + t * htj
      simpa [f, distSq_coordinates, y, point, realSites, castPoint] using hmin y hy
    have ha : HasDerivAt (fun t : ℝ => x 0 + t * a - (p v).1) a 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const a |>.const_add (x 0)).sub_const ((p v).1 : ℝ)
    have hb : HasDerivAt (fun t : ℝ => x 1 + t * b - (p v).2) b 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const b |>.const_add (x 1)).sub_const ((p v).2 : ℝ)
    have hd : HasDerivAt f (2 * (x 0 - (p v).1) * a + 2 * (x 1 - (p v).2) * b) 0 := by
      convert (ha.pow 2).add (hb.pow 2) using 1
      simp
    linarith [hm.hasDerivAt_eq_zero hd]
  have coords (c : Point) (h : x 0 = (c.1 : ℝ) ∧ x 1 = (c.2 : ℝ)) : castPoint c = x := by
    ext i
    fin_cases i
    · exact h.1.symm
    · exact h.2.symm
  by_cases hn : ∃ j, active j ∧ p j ≠ p v
  · obtain ⟨j, hj, hne⟩ := hn
    by_cases hd : ∃ l, active l ∧ det (u j) (u l) ≠ 0
    · obtain ⟨l, hl, hdet⟩ := hd
      have hdet' : ((u j).1 : ℝ) * (u l).2 - (u j).2 * (u l).1 ≠ 0 := by
        exact_mod_cast hdet
      have he := eq_cramer_of_independent_lines _ _ _ _ _ _ _ _ hdet' hj hl
      let c : Point := ((offset (p v) (p j) * (u l).2 - (u j).2 * offset (p v) (p l)) /
          det (u j) (u l),
        ((u j).1 * offset (p v) (p l) - offset (p v) (p j) * (u l).1) / det (u j) (u l))
      refine ⟨c, (mem_centers_iff _ _).2 (.inr (.inr ⟨v, j, l, ?_⟩)), coords c ?_⟩
      · change (if det (u j) (u l) = 0 then none else some c) = some c
        exact ite_eq_right hdet
      · simpa [c, det, k] using he
    · have ht := orthogonal (-((u j).2 : ℝ)) (u j).1 (by
        intro l hl
        have hz : det (u j) (u l) = 0 := by
          by_contra hh
          exact hd ⟨l, hl, hh⟩
        have hr : ((u j).1 : ℝ) * (u l).2 - (u j).2 * (u l).1 = 0 := by exact_mod_cast hz
        linarith only [hr])
      have hxy : ((p v).1 : ℝ) ≠ (p j).1 ∨ ((p v).2 : ℝ) ≠ (p j).2 := by
        by_contra! h
        exact hne (Prod.ext (by exact_mod_cast h.1.symm) (by exact_mod_cast h.2.symm))
      have he := congrArg (fun z : ℝ => z^2) ((dist_eq_iff _ _ _).2 hj)
      simp only [distSq_coordinates, castPoint, point] at he
      have hm := eq_midpoint_of_bisector_and_tangent _ _ _ _ _ _ hxy he (by
        simpa [u, normal] using ht)
      exact ⟨_, (mem_centers_iff _ _).2 (.inr (.inl ⟨v, j, rfl⟩)),
        coords (midpoint (p v) (p j)) (by simpa [midpoint] using hm)⟩
  · have he := eq_site_of_all_tangent _ _ _ _ fun a b => orthogonal a b (by
      intro j hj
      have hsame : p j = p v := by
        by_contra h
        exact hn ⟨j, hj, h⟩
      simp [u, normal, hsame])
    exact ⟨_, (mem_centers_iff _ _).2 (.inl ⟨v, rfl⟩), coords _ he⟩

end TDA.Filtration.RationalAlpha
