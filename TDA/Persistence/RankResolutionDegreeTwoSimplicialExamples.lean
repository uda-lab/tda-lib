import TDA.Persistence.RankResolutionDegreeTwoSimplicial
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Consumers of the simplicial degree-two realization

These examples use the actual inclusion-induced degree-one homology maps. They
exercise the supported maps and cap deaths on the finite grid, and the same
behavior at real grades between grid values and below the grid.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicialExamples

open CategoryTheory TDA.Persistence TDA.Filtration TDA.Simplicial
open CategoryTheory.Limits
open RankResolutionDegreeTwo
open TDA.Persistence.RankResolutionDegreeTwoSimplicial
open scoped TDA.Persistence

private noncomputable abbrev finiteHomology (k : Type u) [Field k] :=
  grid.embedding.monotone.functor ⋙ finiteSimplicialHomology k boundaryTetrahedronGrading 1

private noncomputable abbrev realHomology (k : Type u) [Field k] :=
  finiteSimplicialHomology k boundaryTetrahedronGrading 1

private def exampleCoordinate (i : Fin 3) : {x : ℝ // x ∈ gridValues} :=
  ⟨(i.val : ℝ), by fin_cases i <;> norm_num [gridValues]⟩

private def exampleGridPoint (i j : Fin 3) : grid.Point := fun t =>
  if h : t.val = 0 then by simpa [grid] using exampleCoordinate i
  else by simpa [grid] using exampleCoordinate j

private def oa : grid.Point := exampleGridPoint 0 1
private def ob : grid.Point := exampleGridPoint 1 0
private def oc : grid.Point := exampleGridPoint 1 1
private def od : grid.Point := exampleGridPoint 0 2
private def oe : grid.Point := exampleGridPoint 2 0
private def of : grid.Point := exampleGridPoint 1 2
private def og : grid.Point := exampleGridPoint 2 1

private theorem oa_eq_a : oa = a := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> rfl

private theorem ob_eq_b : ob = b := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> rfl

private theorem oc_eq_c : oc = c := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> rfl

private theorem od_eq_d : od = d := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> rfl

private theorem oe_eq_e : oe = e := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> rfl

private theorem of_eq_f : of = f := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> rfl

private theorem og_eq_g : og = g := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> rfl

private theorem a_le_c : a ≤ c := by
  rw [← oa_eq_a, ← oc_eq_c]
  intro i
  fin_cases i <;> norm_num [oa, oc, exampleGridPoint, exampleCoordinate, grid]

private theorem b_le_c : b ≤ c := by
  rw [← ob_eq_b, ← oc_eq_c]
  intro i
  fin_cases i <;> norm_num [ob, oc, exampleGridPoint, exampleCoordinate, grid]

private theorem a_le_d : a ≤ d := by
  rw [← oa_eq_a, ← od_eq_d]
  intro i
  fin_cases i <;> norm_num [oa, od, exampleGridPoint, exampleCoordinate, grid]

private theorem b_le_e : b ≤ e := by
  rw [← ob_eq_b, ← oe_eq_e]
  intro i
  fin_cases i <;> norm_num [ob, oe, exampleGridPoint, exampleCoordinate, grid]

private theorem c_le_f : c ≤ f := by
  rw [← oc_eq_c, ← of_eq_f]
  intro i
  fin_cases i <;> norm_num [oc, of, exampleGridPoint, exampleCoordinate, grid]

private theorem c_le_g : c ≤ g := by
  rw [← oc_eq_c, ← og_eq_g]
  intro i
  fin_cases i <;> norm_num [oc, og, exampleGridPoint, exampleCoordinate, grid]

private theorem supportOrdConnected : support.OrdConnected where
  out' := by
    intro x hx z hz y hy
    refine ⟨?_, hy.2.trans hz.2⟩
    rcases hx.1 with hax | hbx
    · exact Or.inl (hax.trans hy.1)
    · exact Or.inr (hbx.trans hy.1)

private theorem a_mem_support : a ∈ support :=
  show (a ≤ a ∨ b ≤ a) ∧ a ≤ c from ⟨Or.inl le_rfl, a_le_c⟩

private theorem b_mem_support : b ∈ support :=
  show (a ≤ b ∨ b ≤ b) ∧ b ≤ c from ⟨Or.inr le_rfl, b_le_c⟩

private theorem c_mem_support : c ∈ support :=
  show (a ≤ c ∨ b ≤ c) ∧ c ≤ c from ⟨Or.inl a_le_c, le_rfl⟩

private theorem d_not_support : d ∉ support := by
  intro hd
  have hdc := hd.2 1
  have hdc' : (od 1).val ≤ (oc 1).val := hdc
  norm_num [od, oc, exampleGridPoint, exampleCoordinate, grid] at hdc'

private theorem e_not_support : e ∉ support := by
  intro he
  have hec := he.2 0
  have hec' : (oe 0).val ≤ (oc 0).val := hec
  norm_num [oe, oc, exampleGridPoint, exampleCoordinate, grid] at hec'

private theorem f_not_support : f ∉ support := by
  intro hf
  have hfc := hf.2 1
  have hfc' : (of 1).val ≤ (oc 1).val := hfc
  norm_num [of, oc, exampleGridPoint, exampleCoordinate, grid] at hfc'

private theorem g_not_support : g ∉ support := by
  intro hg
  have hgc := hg.2 0
  have hgc' : (og 0).val ≤ (oc 0).val := hgc
  norm_num [og, oc, exampleGridPoint, exampleCoordinate, grid] at hgc'

private noncomputable def aUnit (k : Type u) [Field k] : (finiteModule (k := k)).obj a :=
  SupportInterval.one support a_mem_support

private noncomputable def bUnit (k : Type u) [Field k] : (finiteModule (k := k)).obj b :=
  SupportInterval.one support b_mem_support

private theorem finite_map_a_c_ne_zero (k : Type u) [Field k] :
    structureMapLinear (finiteModule (k := k)) a_le_c ≠ 0 := by
  intro hz
  have hzero := congrArg (fun f => (f (aUnit k) : k)) hz
  have hval := SupportInterval.structureMap_val support supportOrdConnected
    a_le_c (aUnit k)
  rw [if_pos c_mem_support] at hval
  have hone :
      (structureMapLinear (finiteModule (k := k)) a_le_c (aUnit k) : k) = 1 := by
    simpa [finiteModule, aUnit, SupportInterval.one] using hval
  exact one_ne_zero (hone.symm.trans hzero)

private theorem finite_map_b_c_ne_zero (k : Type u) [Field k] :
    structureMapLinear (finiteModule (k := k)) b_le_c ≠ 0 := by
  intro hz
  have hzero := congrArg (fun f => (f (bUnit k) : k)) hz
  have hval := SupportInterval.structureMap_val support supportOrdConnected
    b_le_c (bUnit k)
  rw [if_pos c_mem_support] at hval
  have hone :
      (structureMapLinear (finiteModule (k := k)) b_le_c (bUnit k) : k) = 1 := by
    simpa [finiteModule, bUnit, SupportInterval.one] using hval
  exact one_ne_zero (hone.symm.trans hzero)

private theorem finite_map_a_d_zero (k : Type u) [Field k] :
    structureMapLinear (finiteModule (k := k)) a_le_d = 0 := by
  change structureMapLinear (SupportInterval.module support supportOrdConnected) a_le_d = 0
  exact SupportInterval.structureMap_eq_zero_of_not_mem support supportOrdConnected
    a_le_d (by intro h; exact d_not_support h.2)

private theorem finite_map_b_e_zero (k : Type u) [Field k] :
    structureMapLinear (finiteModule (k := k)) b_le_e = 0 := by
  change structureMapLinear (SupportInterval.module support supportOrdConnected) b_le_e = 0
  exact SupportInterval.structureMap_eq_zero_of_not_mem support supportOrdConnected
    b_le_e (by intro h; exact e_not_support h.2)

private theorem finite_map_c_f_zero (k : Type u) [Field k] :
    structureMapLinear (finiteModule (k := k)) c_le_f = 0 := by
  change structureMapLinear (SupportInterval.module support supportOrdConnected) c_le_f = 0
  exact SupportInterval.structureMap_eq_zero_of_not_mem support supportOrdConnected
    c_le_f (by intro h; exact f_not_support h.2)

private theorem finite_map_c_g_zero (k : Type u) [Field k] :
    structureMapLinear (finiteModule (k := k)) c_le_g = 0 := by
  change structureMapLinear (SupportInterval.module support supportOrdConnected) c_le_g = 0
  exact SupportInterval.structureMap_eq_zero_of_not_mem support supportOrdConnected
    c_le_g (by intro h; exact g_not_support h.2)

private theorem finite_map_nonzero_of_support (k : Type u) [Field k]
    {p q : grid.Point} (hpq : p ≤ q) (hp : p ∈ support) (hq : q ∈ support) :
    structureMapLinear (finiteModule (k := k)) hpq ≠ 0 := by
  intro hz
  let up : (finiteModule (k := k)).obj p := SupportInterval.one support hp
  have hzero := congrArg (fun f => (f up : k)) hz
  have hval := SupportInterval.structureMap_val support supportOrdConnected hpq up
  rw [if_pos hq] at hval
  have hone :
      (structureMapLinear (finiteModule (k := k)) hpq up : k) = 1 := by
    simpa [finiteModule, up, SupportInterval.one] using hval
  exact one_ne_zero (hone.symm.trans hzero)

private theorem finite_map_zero_of_target_not_support (k : Type u) [Field k]
    {p q : grid.Point} (hpq : p ≤ q) (hq : q ∉ support) :
    structureMapLinear (finiteModule (k := k)) hpq = 0 := by
  change structureMapLinear (SupportInterval.module support supportOrdConnected) hpq = 0
  exact SupportInterval.structureMap_eq_zero_of_not_mem support supportOrdConnected hpq
    (by intro h; exact hq h.2)

private theorem finiteModule_map_ne_zero (k : Type u) [Field k]
    {p q : grid.Point} (hpq : p ≤ q)
    (hM : structureMapLinear (finiteModule (k := k)) hpq ≠ 0) :
    structureMap (finiteModule (k := k)) hpq ≠ 0 := by
  intro hz
  apply hM
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun f => f.hom x) hz
  simpa [structureMapLinear] using hx

private theorem finiteModule_map_zero (k : Type u) [Field k]
    {p q : grid.Point} (hpq : p ≤ q)
    (hM : structureMapLinear (finiteModule (k := k)) hpq = 0) :
    structureMap (finiteModule (k := k)) hpq = 0 := by
  apply ModuleCat.hom_ext
  exact hM

private theorem finite_homology_map_ne_zero (k : Type u) [Field k]
    {p q : grid.Point} (hpq : p ≤ q)
    (hM : structureMap (finiteModule (k := k)) hpq ≠ 0) :
    structureMap (finiteHomology k) hpq ≠ 0 := by
  intro hH
  have hn := (finiteIso k).hom.naturality (homOfLE hpq)
  change structureMap (finiteHomology k) hpq ≫ (finiteIso k).hom.app q =
    (finiteIso k).hom.app p ≫ structureMap (finiteModule (k := k)) hpq at hn
  have hcomp : (finiteIso k).hom.app p ≫ structureMap (finiteModule (k := k)) hpq = 0 := by
    calc
      _ = structureMap (finiteHomology k) hpq ≫ (finiteIso k).hom.app q := hn.symm
      _ = 0 := by rw [hH, zero_comp]
  have hM0 : structureMap (finiteModule (k := k)) hpq = 0 :=
    (cancel_epi ((finiteIso k).hom.app p)).mp (by
      calc
        _ = 0 := hcomp
        _ = (finiteIso k).hom.app p ≫ (0 : (finiteModule (k := k)).obj p ⟶
          (finiteModule (k := k)).obj q) := by rw [comp_zero])
  exact hM hM0

private theorem finite_homology_map_zero (k : Type u) [Field k]
    {p q : grid.Point} (hpq : p ≤ q)
    (hM : structureMap (finiteModule (k := k)) hpq = 0) :
    structureMap (finiteHomology k) hpq = 0 := by
  have hn := (finiteIso k).hom.naturality (homOfLE hpq)
  change structureMap (finiteHomology k) hpq ≫ (finiteIso k).hom.app q =
    (finiteIso k).hom.app p ≫ structureMap (finiteModule (k := k)) hpq at hn
  have hcomp : structureMap (finiteHomology k) hpq ≫ (finiteIso k).hom.app q = 0 := by
    calc
      _ = (finiteIso k).hom.app p ≫ structureMap (finiteModule (k := k)) hpq := hn
      _ = 0 := by rw [hM, comp_zero]
  exact (cancel_mono ((finiteIso k).hom.app q)).mp (by
    calc
      _ = 0 := hcomp
      _ = (0 : (finiteHomology k).obj p ⟶ (finiteHomology k).obj q) ≫
        (finiteIso k).hom.app q := by rw [zero_comp])

/-- The real-coordinate grade of the first supported grid arm `(0,1)`. -/
noncomputable def simplicialGradeA : Fin 2 → ℝ := grid.embedding a

/-- The real-coordinate grade of the second supported grid arm `(1,0)`. -/
noncomputable def simplicialGradeB : Fin 2 → ℝ := grid.embedding b

/-- The real-coordinate grade of the supported join `(1,1)`. -/
noncomputable def simplicialGradeC : Fin 2 → ℝ := grid.embedding c

/-- The real-coordinate grade of the first cap `(0,2)`. -/
noncomputable def simplicialGradeD : Fin 2 → ℝ := grid.embedding d

/-- The real-coordinate grade of the second cap `(2,0)`. -/
noncomputable def simplicialGradeE : Fin 2 → ℝ := grid.embedding e

/-- The real-coordinate first-arm death stage `(1,2)`. -/
noncomputable def simplicialGradeF : Fin 2 → ℝ := grid.embedding f

/-- The real-coordinate second-arm death stage `(2,1)`. -/
noncomputable def simplicialGradeG : Fin 2 → ℝ := grid.embedding g

theorem simplicialGradeA_le_C : simplicialGradeA ≤ simplicialGradeC :=
  grid.embedding.monotone a_le_c

theorem simplicialGradeB_le_C : simplicialGradeB ≤ simplicialGradeC :=
  grid.embedding.monotone b_le_c

theorem simplicialGradeA_le_D : simplicialGradeA ≤ simplicialGradeD :=
  grid.embedding.monotone a_le_d

theorem simplicialGradeB_le_E : simplicialGradeB ≤ simplicialGradeE :=
  grid.embedding.monotone b_le_e

theorem simplicialGradeC_le_F : simplicialGradeC ≤ simplicialGradeF :=
  grid.embedding.monotone c_le_f

theorem simplicialGradeC_le_G : simplicialGradeC ≤ simplicialGradeG :=
  grid.embedding.monotone c_le_g

/-- On the actual finite-coordinate restriction, the inclusion-induced H₁ map
from the first supported arm to the join is nonzero over every field. -/
theorem actualFinite_a_to_c_nonzero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      simplicialGradeA_le_C ≠ 0 := by
  change structureMap (finiteHomology k) a_le_c ≠ 0
  exact finite_homology_map_ne_zero k a_le_c
    (finiteModule_map_ne_zero k a_le_c (finite_map_a_c_ne_zero k))

/-- On the actual finite-coordinate restriction, the inclusion-induced H₁ map
from the second supported arm to the join is nonzero over every field. -/
theorem actualFinite_b_to_c_nonzero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      simplicialGradeB_le_C ≠ 0 := by
  change structureMap (finiteHomology k) b_le_c ≠ 0
  exact finite_homology_map_ne_zero k b_le_c
    (finiteModule_map_ne_zero k b_le_c (finite_map_b_c_ne_zero k))

theorem actualFinite_a_to_d_zero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      simplicialGradeA_le_D = 0 := by
  change structureMap (finiteHomology k) a_le_d = 0
  exact finite_homology_map_zero k a_le_d
    (finiteModule_map_zero k a_le_d (finite_map_a_d_zero k))

theorem actualFinite_b_to_e_zero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      simplicialGradeB_le_E = 0 := by
  change structureMap (finiteHomology k) b_le_e = 0
  exact finite_homology_map_zero k b_le_e
    (finiteModule_map_zero k b_le_e (finite_map_b_e_zero k))

theorem actualFinite_c_to_f_zero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      simplicialGradeC_le_F = 0 := by
  change structureMap (finiteHomology k) c_le_f = 0
  exact finite_homology_map_zero k c_le_f
    (finiteModule_map_zero k c_le_f (finite_map_c_f_zero k))

theorem actualFinite_c_to_g_zero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      simplicialGradeC_le_G = 0 := by
  change structureMap (finiteHomology k) c_le_g = 0
  exact finite_homology_map_zero k c_le_g
    (finiteModule_map_zero k c_le_g (finite_map_c_g_zero k))

/-- A real grade between `a` and `b` in the first coordinate, above `a` in
the second coordinate. -/
noncomputable def betweenLeft : Fin 2 → ℝ := fun i => if i = 0 then 1 / 4 else 5 / 4

/-- The symmetric real grade between `a` and `b` in the second coordinate. -/
noncomputable def betweenRight : Fin 2 → ℝ := fun i => if i = 0 then 5 / 4 else 1 / 4

/-- A real grade between the finite coordinate values in both directions. -/
noncomputable def betweenJoin : Fin 2 → ℝ := fun _ => 5 / 4

/-- The first real cap-death grade above `betweenJoin`. -/
noncomputable def betweenFirstDeath : Fin 2 → ℝ := fun i => if i = 0 then 5 / 4 else 2

/-- The second real cap-death grade above `betweenJoin`. -/
noncomputable def betweenSecondDeath : Fin 2 → ℝ := fun i => if i = 0 then 2 else 5 / 4

/-- A real grade below the finite grid in its first coordinate. -/
noncomputable def belowGrid : Fin 2 → ℝ := fun i => if i = 0 then -(1 / 4) else 5 / 4

theorem betweenLeft_le_betweenJoin : betweenLeft ≤ betweenJoin := by
  intro i
  fin_cases i <;> norm_num [betweenLeft, betweenJoin]

theorem betweenRight_le_betweenJoin : betweenRight ≤ betweenJoin := by
  intro i
  fin_cases i <;> norm_num [betweenRight, betweenJoin]

theorem betweenJoin_le_betweenFirstDeath : betweenJoin ≤ betweenFirstDeath := by
  intro i
  fin_cases i <;> norm_num [betweenJoin, betweenFirstDeath]

theorem betweenJoin_le_betweenSecondDeath : betweenJoin ≤ betweenSecondDeath := by
  intro i
  fin_cases i <;> norm_num [betweenJoin, betweenSecondDeath]

private theorem gridCoordinate_cases (q : grid.Point) (i : Fin 2) :
    (q i).val = 0 ∨ (q i).val = 1 ∨ (q i).val = 2 := by
  have h : (q i).val ∈ gridValues := by simp [grid]
  simpa only [gridValues, Finset.mem_insert, Finset.mem_singleton] using h

private theorem q_le_oa_of_le_betweenLeft (q : grid.Point)
    (hq : grid.embedding q ≤ betweenLeft) : q ≤ oa := by
  intro i
  change (q i).val ≤ (oa i).val
  fin_cases i
  all_goals first
    | change (q (0 : Fin 2)).val ≤ (oa (0 : Fin 2)).val
    | change (q (1 : Fin 2)).val ≤ (oa (1 : Fin 2)).val
  · have hqi : (q 0).val ≤ (1 / 4 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenLeft] using hq 0
    rcases gridCoordinate_cases q 0 with h0 | h1 | h2
    · norm_num [oa, exampleGridPoint, exampleCoordinate, grid, h0]
    · rw [h1] at hqi
      norm_num at hqi
    · rw [h2] at hqi
      norm_num at hqi
  · have hqi : (q 1).val ≤ (5 / 4 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenLeft] using hq 1
    rcases gridCoordinate_cases q 1 with h0 | h1 | h2
    · norm_num [oa, exampleGridPoint, exampleCoordinate, grid, h0]
    · norm_num [oa, exampleGridPoint, exampleCoordinate, grid, h1]
    · rw [h2] at hqi
      norm_num at hqi

private theorem q_le_ob_of_le_betweenRight (q : grid.Point)
    (hq : grid.embedding q ≤ betweenRight) : q ≤ ob := by
  intro i
  change (q i).val ≤ (ob i).val
  fin_cases i
  all_goals first
    | change (q (0 : Fin 2)).val ≤ (ob (0 : Fin 2)).val
    | change (q (1 : Fin 2)).val ≤ (ob (1 : Fin 2)).val
  · have hqi : (q 0).val ≤ (5 / 4 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenRight] using hq 0
    rcases gridCoordinate_cases q 0 with h0 | h1 | h2
    · norm_num [ob, exampleGridPoint, exampleCoordinate, grid, h0]
    · norm_num [ob, exampleGridPoint, exampleCoordinate, grid, h1]
    · rw [h2] at hqi
      norm_num at hqi
  · have hqi : (q 1).val ≤ (1 / 4 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenRight] using hq 1
    rcases gridCoordinate_cases q 1 with h0 | h1 | h2
    · norm_num [ob, exampleGridPoint, exampleCoordinate, grid, h0]
    · rw [h1] at hqi
      norm_num at hqi
    · rw [h2] at hqi
      norm_num at hqi

private theorem q_le_oc_of_le_betweenJoin (q : grid.Point)
    (hq : grid.embedding q ≤ betweenJoin) : q ≤ oc := by
  intro i
  change (q i).val ≤ (oc i).val
  fin_cases i
  all_goals first
    | change (q (0 : Fin 2)).val ≤ (oc (0 : Fin 2)).val
    | change (q (1 : Fin 2)).val ≤ (oc (1 : Fin 2)).val
  · have hqi : (q 0).val ≤ (5 / 4 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenJoin] using hq 0
    rcases gridCoordinate_cases q 0 with h0 | h1 | h2
    · norm_num [oc, exampleGridPoint, exampleCoordinate, grid, h0]
    · norm_num [oc, exampleGridPoint, exampleCoordinate, grid, h1]
    · rw [h2] at hqi
      norm_num at hqi
  · have hqi : (q 1).val ≤ (5 / 4 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenJoin] using hq 1
    rcases gridCoordinate_cases q 1 with h0 | h1 | h2
    · norm_num [oc, exampleGridPoint, exampleCoordinate, grid, h0]
    · norm_num [oc, exampleGridPoint, exampleCoordinate, grid, h1]
    · rw [h2] at hqi
      norm_num at hqi

private theorem q_le_of_of_le_betweenFirstDeath (q : grid.Point)
    (hq : grid.embedding q ≤ betweenFirstDeath) : q ≤ of := by
  intro i
  change (q i).val ≤ (of i).val
  fin_cases i
  all_goals first
    | change (q (0 : Fin 2)).val ≤ (of (0 : Fin 2)).val
    | change (q (1 : Fin 2)).val ≤ (of (1 : Fin 2)).val
  · have hqi : (q 0).val ≤ (5 / 4 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenFirstDeath] using hq 0
    rcases gridCoordinate_cases q 0 with h0 | h1 | h2
    · norm_num [of, exampleGridPoint, exampleCoordinate, grid, h0]
    · norm_num [of, exampleGridPoint, exampleCoordinate, grid, h1]
    · rw [h2] at hqi
      norm_num at hqi
  · have hqi : (q 1).val ≤ (2 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenFirstDeath] using hq 1
    rcases gridCoordinate_cases q 1 with h0 | h1 | h2
    · norm_num [of, exampleGridPoint, exampleCoordinate, grid, h0]
    · norm_num [of, exampleGridPoint, exampleCoordinate, grid, h1]
    · norm_num [of, exampleGridPoint, exampleCoordinate, grid, h2]

private theorem q_le_og_of_le_betweenSecondDeath (q : grid.Point)
    (hq : grid.embedding q ≤ betweenSecondDeath) : q ≤ og := by
  intro i
  change (q i).val ≤ (og i).val
  fin_cases i
  all_goals first
    | change (q (0 : Fin 2)).val ≤ (og (0 : Fin 2)).val
    | change (q (1 : Fin 2)).val ≤ (og (1 : Fin 2)).val
  · have hqi : (q 0).val ≤ (2 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenSecondDeath] using hq 0
    rcases gridCoordinate_cases q 0 with h0 | h1 | h2
    · norm_num [og, exampleGridPoint, exampleCoordinate, grid, h0]
    · norm_num [og, exampleGridPoint, exampleCoordinate, grid, h1]
    · norm_num [og, exampleGridPoint, exampleCoordinate, grid, h2]
  · have hqi : (q 1).val ≤ (5 / 4 : ℝ) := by
      simpa [CoordinateGrid.embedding_apply, betweenSecondDeath] using hq 1
    rcases gridCoordinate_cases q 1 with h0 | h1 | h2
    · norm_num [og, exampleGridPoint, exampleCoordinate, grid, h0]
    · norm_num [og, exampleGridPoint, exampleCoordinate, grid, h1]
    · rw [h2] at hqi
      norm_num at hqi

private theorem embedding_oa :
    grid.embedding oa = fun i => if i = 0 then 0 else 1 := by
  funext i
  fin_cases i <;>
    norm_num [CoordinateGrid.embedding_apply, oa, exampleGridPoint, exampleCoordinate, grid]

private theorem embedding_ob :
    grid.embedding ob = fun i => if i = 0 then 1 else 0 := by
  funext i
  fin_cases i <;>
    norm_num [CoordinateGrid.embedding_apply, ob, exampleGridPoint, exampleCoordinate, grid]

private theorem embedding_oc :
    grid.embedding oc = fun _ => 1 := by
  funext i
  fin_cases i <;>
    norm_num [CoordinateGrid.embedding_apply, oc, exampleGridPoint, exampleCoordinate, grid]

private theorem embedding_of :
    grid.embedding of = fun i => if i = 0 then 1 else 2 := by
  funext i
  fin_cases i <;>
    norm_num [CoordinateGrid.embedding_apply, of, exampleGridPoint, exampleCoordinate, grid]

private theorem embedding_og :
    grid.embedding og = fun i => if i = 0 then 2 else 1 := by
  funext i
  fin_cases i <;>
    norm_num [CoordinateGrid.embedding_apply, og, exampleGridPoint, exampleCoordinate, grid]

private theorem betweenLeft_hasLowerPoint : grid.HasLowerPoint betweenLeft := by
  refine ⟨oa, ?_⟩
  rw [embedding_oa]
  intro i
  fin_cases i <;> norm_num [betweenLeft]

private theorem betweenRight_hasLowerPoint : grid.HasLowerPoint betweenRight := by
  refine ⟨ob, ?_⟩
  rw [embedding_ob]
  intro i
  fin_cases i <;> norm_num [betweenRight]

private theorem betweenJoin_hasLowerPoint : grid.HasLowerPoint betweenJoin := by
  refine ⟨oc, ?_⟩
  rw [embedding_oc]
  intro i
  fin_cases i <;> norm_num [betweenJoin]

private theorem betweenFirstDeath_hasLowerPoint : grid.HasLowerPoint betweenFirstDeath := by
  refine ⟨of, ?_⟩
  rw [embedding_of]
  intro i
  fin_cases i <;> norm_num [betweenFirstDeath]

private theorem betweenSecondDeath_hasLowerPoint : grid.HasLowerPoint betweenSecondDeath := by
  refine ⟨og, ?_⟩
  rw [embedding_og]
  intro i
  fin_cases i <;> norm_num [betweenSecondDeath]

private theorem floor_betweenLeft :
    grid.floor betweenLeft betweenLeft_hasLowerPoint = oa := by
  apply (grid.floor_eq_iff betweenLeft betweenLeft_hasLowerPoint oa).2
  constructor
  · intro i
    rw [embedding_oa]
    fin_cases i <;> norm_num [betweenLeft]
  · intro q hq
    exact q_le_oa_of_le_betweenLeft q hq

private theorem floor_betweenRight :
    grid.floor betweenRight betweenRight_hasLowerPoint = ob := by
  apply (grid.floor_eq_iff betweenRight betweenRight_hasLowerPoint ob).2
  constructor
  · intro i
    rw [embedding_ob]
    fin_cases i <;> norm_num [betweenRight]
  · intro q hq
    exact q_le_ob_of_le_betweenRight q hq

private theorem floor_betweenJoin :
    grid.floor betweenJoin betweenJoin_hasLowerPoint = oc := by
  apply (grid.floor_eq_iff betweenJoin betweenJoin_hasLowerPoint oc).2
  constructor
  · intro i
    rw [embedding_oc]
    fin_cases i <;> norm_num [betweenJoin]
  · intro q hq
    exact q_le_oc_of_le_betweenJoin q hq

private theorem floor_betweenFirstDeath :
    grid.floor betweenFirstDeath betweenFirstDeath_hasLowerPoint = of := by
  apply (grid.floor_eq_iff betweenFirstDeath betweenFirstDeath_hasLowerPoint of).2
  constructor
  · intro i
    rw [embedding_of]
    fin_cases i <;> norm_num [betweenFirstDeath]
  · intro q hq
    exact q_le_of_of_le_betweenFirstDeath q hq

private theorem floor_betweenSecondDeath :
    grid.floor betweenSecondDeath betweenSecondDeath_hasLowerPoint = og := by
  apply (grid.floor_eq_iff betweenSecondDeath betweenSecondDeath_hasLowerPoint og).2
  constructor
  · intro i
    rw [embedding_og]
    fin_cases i <;> norm_num [betweenSecondDeath]
  · intro q hq
    exact q_le_og_of_le_betweenSecondDeath q hq

private theorem lan_map_ne_zero_of_floor (k : Type u) [Field k] {a b : Fin 2 → ℝ}
    (hab : a ≤ b) (ha : grid.HasLowerPoint a) (hb : grid.HasLowerPoint b)
    (hfloor : structureMap (finiteModule (k := k))
      (grid.floor_mono hab ha hb) ≠ 0) :
    structureMap (grid.lan.obj (finiteModule (k := k))) hab ≠ 0 := by
  intro hz
  have hn := grid.appIso_structureMap (finiteModule (k := k)) hab ha hb
  have hcomp : (grid.appIso (finiteModule (k := k)) a ha).hom ≫
      structureMap (finiteModule (k := k)) (grid.floor_mono hab ha hb) = 0 := by
    rw [← hn, hz, zero_comp]
  apply hfloor
  exact (cancel_epi (grid.appIso (finiteModule (k := k)) a ha).hom).mp (by
    calc
      _ = 0 := hcomp
      _ = (grid.appIso (finiteModule (k := k)) a ha).hom ≫ 0 := by rw [comp_zero])

private theorem lan_map_zero_of_floor (k : Type u) [Field k] {a b : Fin 2 → ℝ}
    (hab : a ≤ b) (ha : grid.HasLowerPoint a) (hb : grid.HasLowerPoint b)
    (hfloor : structureMap (finiteModule (k := k))
      (grid.floor_mono hab ha hb) = 0) :
    structureMap (grid.lan.obj (finiteModule (k := k))) hab = 0 := by
  have hn := grid.appIso_structureMap (finiteModule (k := k)) hab ha hb
  have hcomp : structureMap (grid.lan.obj (finiteModule (k := k))) hab ≫
      (grid.appIso (finiteModule (k := k)) b hb).hom = 0 := by
    rw [hn, hfloor, comp_zero]
  exact (cancel_mono (grid.appIso (finiteModule (k := k)) b hb).hom).mp (by
    calc
      _ = 0 := hcomp
      _ = 0 ≫ (grid.appIso (finiteModule (k := k)) b hb).hom := by rw [zero_comp])

private theorem real_map_ne_zero_of_lan (k : Type u) [Field k] {a b : Fin 2 → ℝ}
    (hab : a ≤ b)
    (hLan : structureMap (grid.lan.obj (finiteModule (k := k))) hab ≠ 0) :
    structureMap (realHomology k) hab ≠ 0 := by
  intro hz
  have hn := (realIso k).hom.naturality (homOfLE hab)
  change structureMap (realHomology k) hab ≫ (realIso k).hom.app b =
    (realIso k).hom.app a ≫ structureMap (grid.lan.obj (finiteModule (k := k))) hab at hn
  have hcomp : (realIso k).hom.app a ≫
      structureMap (grid.lan.obj (finiteModule (k := k))) hab = 0 := by
    calc
      _ = structureMap (realHomology k) hab ≫ (realIso k).hom.app b := hn.symm
      _ = 0 := by rw [hz, zero_comp]
  have hzero : structureMap (grid.lan.obj (finiteModule (k := k))) hab = 0 :=
    (cancel_epi ((realIso k).hom.app a)).mp (by
      calc
        _ = 0 := hcomp
        _ = (realIso k).hom.app a ≫ 0 := by rw [comp_zero])
  exact hLan hzero

private theorem real_map_zero_of_lan (k : Type u) [Field k] {a b : Fin 2 → ℝ}
    (hab : a ≤ b)
    (hLan : structureMap (grid.lan.obj (finiteModule (k := k))) hab = 0) :
    structureMap (realHomology k) hab = 0 := by
  have hn := (realIso k).hom.naturality (homOfLE hab)
  change structureMap (realHomology k) hab ≫ (realIso k).hom.app b =
    (realIso k).hom.app a ≫ structureMap (grid.lan.obj (finiteModule (k := k))) hab at hn
  have hcomp : structureMap (realHomology k) hab ≫ (realIso k).hom.app b = 0 := by
    calc
      _ = (realIso k).hom.app a ≫ structureMap (grid.lan.obj (finiteModule (k := k))) hab := hn
      _ = 0 := by rw [hLan, comp_zero]
  exact (cancel_mono ((realIso k).hom.app b)).mp (by
    calc
      _ = 0 := hcomp
      _ = 0 ≫ (realIso k).hom.app b := by rw [zero_comp])

/-- Between grid coordinates, the actual real H₁ map from the first arm to its
join is nonzero over every field. -/
theorem actualReal_betweenLeft_toJoin_nonzero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      betweenLeft_le_betweenJoin ≠ 0 := by
  let hu := betweenLeft_hasLowerPoint
  let hw := betweenJoin_hasLowerPoint
  have hgrid : structureMap (finiteModule (k := k))
      (grid.floor_mono betweenLeft_le_betweenJoin hu hw) ≠ 0 := by
    have hp : grid.floor betweenLeft hu ∈ support := by
      rw [floor_betweenLeft, oa_eq_a]
      exact a_mem_support
    have hq : grid.floor betweenJoin hw ∈ support := by
      rw [floor_betweenJoin, oc_eq_c]
      exact c_mem_support
    exact finiteModule_map_ne_zero k (grid.floor_mono betweenLeft_le_betweenJoin hu hw)
      (finite_map_nonzero_of_support k
        (grid.floor_mono betweenLeft_le_betweenJoin hu hw) hp hq)
  exact real_map_ne_zero_of_lan k betweenLeft_le_betweenJoin
    (lan_map_ne_zero_of_floor k betweenLeft_le_betweenJoin hu hw hgrid)

/-- The symmetric real-coordinate map from the second arm to the join is
nonzero over every field. -/
theorem actualReal_betweenRight_toJoin_nonzero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      betweenRight_le_betweenJoin ≠ 0 := by
  let hv := betweenRight_hasLowerPoint
  let hw := betweenJoin_hasLowerPoint
  have hgrid : structureMap (finiteModule (k := k))
      (grid.floor_mono betweenRight_le_betweenJoin hv hw) ≠ 0 := by
    have hp : grid.floor betweenRight hv ∈ support := by
      rw [floor_betweenRight, ob_eq_b]
      exact b_mem_support
    have hq : grid.floor betweenJoin hw ∈ support := by
      rw [floor_betweenJoin, oc_eq_c]
      exact c_mem_support
    exact finiteModule_map_ne_zero k (grid.floor_mono betweenRight_le_betweenJoin hv hw)
      (finite_map_nonzero_of_support k
        (grid.floor_mono betweenRight_le_betweenJoin hv hw) hp hq)
  exact real_map_ne_zero_of_lan k betweenRight_le_betweenJoin
    (lan_map_ne_zero_of_floor k betweenRight_le_betweenJoin hv hw hgrid)

/-- The first cap kills the actual real H₁ map from the join to its death
stage. -/
theorem actualReal_betweenJoin_toFirstDeath_zero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      betweenJoin_le_betweenFirstDeath = 0 := by
  let hw := betweenJoin_hasLowerPoint
  let hf := betweenFirstDeath_hasLowerPoint
  have hgrid : structureMap (finiteModule (k := k))
      (grid.floor_mono betweenJoin_le_betweenFirstDeath hw hf) = 0 := by
    have hq : grid.floor betweenFirstDeath hf ∉ support := by
      rw [floor_betweenFirstDeath, of_eq_f]
      exact f_not_support
    exact finiteModule_map_zero k (grid.floor_mono betweenJoin_le_betweenFirstDeath hw hf)
      (finite_map_zero_of_target_not_support k
        (grid.floor_mono betweenJoin_le_betweenFirstDeath hw hf) hq)
  exact real_map_zero_of_lan k betweenJoin_le_betweenFirstDeath
    (lan_map_zero_of_floor k betweenJoin_le_betweenFirstDeath hw hf hgrid)

/-- The second cap kills the actual real H₁ map from the join to its death
stage. -/
theorem actualReal_betweenJoin_toSecondDeath_zero (k : Type u) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      betweenJoin_le_betweenSecondDeath = 0 := by
  let hw := betweenJoin_hasLowerPoint
  let hg := betweenSecondDeath_hasLowerPoint
  have hgrid : structureMap (finiteModule (k := k))
      (grid.floor_mono betweenJoin_le_betweenSecondDeath hw hg) = 0 := by
    have hq : grid.floor betweenSecondDeath hg ∉ support := by
      rw [floor_betweenSecondDeath, og_eq_g]
      exact g_not_support
    exact finiteModule_map_zero k (grid.floor_mono betweenJoin_le_betweenSecondDeath hw hg)
      (finite_map_zero_of_target_not_support k
        (grid.floor_mono betweenJoin_le_betweenSecondDeath hw hg) hq)
  exact real_map_zero_of_lan k betweenJoin_le_betweenSecondDeath
    (lan_map_zero_of_floor k betweenJoin_le_betweenSecondDeath hw hg hgrid)

private theorem belowGrid_noLowerPoint : ¬ grid.HasLowerPoint belowGrid := by
  rintro ⟨q, hq⟩
  have hq0 : (q 0).val ≤ (-(1 / 4 : ℝ)) := by
    simpa [CoordinateGrid.embedding_apply, belowGrid] using hq 0
  rcases gridCoordinate_cases q 0 with h0 | h1 | h2
  · rw [h0] at hq0
    norm_num at hq0
  · rw [h1] at hq0
    norm_num at hq0
  · rw [h2] at hq0
    norm_num at hq0

/-- Below the finite coordinate grid, the actual real H₁ fiber vanishes. -/
theorem actualReal_belowGrid_isZero (k : Type u) [Field k] :
    IsZero ((finiteSimplicialHomology k boundaryTetrahedronGrading 1).obj belowGrid) := by
  apply IsZero.of_iso
    (grid.isZero_obj_of_not_hasLowerPoint (finiteModule (k := k)) belowGrid
      belowGrid_noLowerPoint)
    ((realIso k).app belowGrid)

/-- Ordinary-import field-generic consumers expose the actual real map result
at arbitrary coefficient universes. -/
theorem arbitraryUniverse_real_arm_map (k : Type v) [Field k] :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      betweenLeft_le_betweenJoin ≠ 0 :=
  actualReal_betweenLeft_toJoin_nonzero k

example : structureMap (finiteSimplicialHomology ℚ boundaryTetrahedronGrading 1)
    simplicialGradeA_le_C ≠ 0 := actualFinite_a_to_c_nonzero ℚ

example : structureMap (finiteSimplicialHomology (ZMod 2) boundaryTetrahedronGrading 1)
    simplicialGradeB_le_C ≠ 0 := actualFinite_b_to_c_nonzero (ZMod 2)

example : structureMap (finiteSimplicialHomology ℚ boundaryTetrahedronGrading 1)
    betweenLeft_le_betweenJoin ≠ 0 := actualReal_betweenLeft_toJoin_nonzero ℚ

example : structureMap (finiteSimplicialHomology (ZMod 2) boundaryTetrahedronGrading 1)
    betweenRight_le_betweenJoin ≠ 0 := actualReal_betweenRight_toJoin_nonzero (ZMod 2)

example : IsZero ((finiteSimplicialHomology ℚ boundaryTetrahedronGrading 1).obj belowGrid) :=
  actualReal_belowGrid_isZero ℚ

example : GradedFree.FinitelyPresented.{0,0,0} (R := ℚ) (P := Fin 2 → ℝ)
    (finiteSimplicialHomology ℚ boundaryTetrahedronGrading 1) :=
  homology_finitelyPresented ℚ


end TDA.Persistence.RankResolutionDegreeTwoSimplicialExamples
