import TDA.Filtration.RationalAlpha

set_option autoImplicit false

/-!
# Exact planar alpha grades

The tables use the entire emitted carrier. Labels follow the order of the
coordinates in each configuration.
-/

namespace TDA.Filtration.RationalAlpha.Examples

open scoped Matrix

private def sites {n : ℕ} (p : Fin n → Point) (h : ∀ i j, p i = p j → i = j) :
    Fin n ↪ Point := ⟨p, fun _ _ => h _ _⟩

def two : Fin 2 ↪ Point := sites ![(0,0), (2,0)] (by decide +kernel)
def collinear : Fin 3 ↪ Point := sites ![(0,0), (2,0), (4,0)] (by decide +kernel)
def obtuse : Fin 3 ↪ Point := sites ![(0,0), (4,0), (1,1)] (by decide +kernel)
def square : Fin 4 ↪ Point := sites ![(0,0), (2,0), (0,2), (2,2)] (by decide +kernel)

theorem two_grades : gradedFaces two =
    {({0}, 0), ({1}, 0), ({0,1}, 1)} := by decide +kernel

theorem collinear_grades : gradedFaces collinear =
    {({0}, 0), ({1}, 0), ({2}, 0), ({0,1}, 1), ({1,2}, 1)} := by
  decide +kernel

theorem collinear_missing : entry? collinear {0,2} = none ∧
    entry? collinear {0,1,2} = none := by decide +kernel

theorem obtuse_grades : gradedFaces obtuse =
    {({0}, 0), ({1}, 0), ({2}, 0), ({0,2}, 1/2), ({1,2}, 5/2),
      ({0,1}, 5), ({0,1,2}, 5)} := by decide +kernel

theorem obtuse_long_edge_record :
    entry? obtuse {0,1} = some ⟨(2,-1), 5, {0,1,2}⟩ := by decide +kernel

theorem square_grades : gradedFaces square =
    {({0}, 0), ({1}, 0), ({2}, 0), ({3}, 0),
      ({0,1}, 1), ({0,2}, 1), ({1,3}, 1), ({2,3}, 1),
      ({0,3}, 2), ({1,2}, 2), ({0,1,2}, 2), ({0,1,3}, 2),
      ({0,2,3}, 2), ({1,2,3}, 2), ({0,1,2,3}, 2)} := by decide +kernel

theorem square_full_tie :
    entry? square {0,1,2,3} = some ⟨(1,1), 2, {0,1,2,3}⟩ := by decide +kernel

theorem obtuse_alpha_long_edge (t : ℝ) :
    ({0,1} : Finset (Fin 3)) ∈ Alpha.complex (realSites obtuse) t ↔ 5 ≤ t := by
  simp [mem_complex_iff, obtuse_long_edge_record]

theorem obtuse_cech_long_edge (r : ℝ) :
    ({0,1} : Finset (Fin 3)) ∈ Cech.complex (realSites obtuse) r ↔ 2 ≤ r := by
  have h0 : (0 : Fin 3) ∈ ({0,1} : Finset (Fin 3)) := by decide
  have h1 : (1 : Fin 3) ∈ ({0,1} : Finset (Fin 3)) := by decide
  have hdist : dist (realSites obtuse 0) (realSites obtuse 1) = 4 := by
    suffices h : dist (realSites obtuse 0) (realSites obtuse 1) ^ 2 = 16 by
      nlinarith [dist_nonneg (x := realSites obtuse 0) (y := realSites obtuse 1)]
    change dist (castPoint (obtuse 0)) (castPoint (obtuse 1)) ^ 2 = 16
    rw [distSq_cast]
    exact_mod_cast (show sqDist (obtuse 0) (obtuse 1) = 16 by decide +kernel)
  rw [Cech.mem_complex_iff]
  constructor
  · rintro ⟨_, c, hc⟩
    have h := dist_triangle_left (realSites obtuse 0) (realSites obtuse 1) c
    rw [hdist] at h
    linarith [hc 0 h0, hc 1 h1]
  · intro hr
    refine ⟨⟨0,h0⟩, castPoint (2,0), ?_⟩
    intro i hi
    have hd : dist (castPoint (2,0)) (realSites obtuse i) ^ 2 = 4 := by
      change dist (castPoint (2,0)) (castPoint (obtuse i)) ^ 2 = 4
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [distSq_cast]
      suffices h : sqDist (2,0) (obtuse i) = 4 by exact_mod_cast h
      rcases hi with rfl | rfl <;> decide +kernel
    have hrad : dist (castPoint (2,0)) (realSites obtuse i) ≤ 2 := by
      nlinarith [dist_nonneg (x := castPoint (2,0)) (y := realSites obtuse i)]
    exact hrad.trans hr

end TDA.Filtration.RationalAlpha.Examples
