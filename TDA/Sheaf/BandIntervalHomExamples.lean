import TDA.Sheaf.BandIntervalCostTable

/-! Morphisms between the open and closed intervals with endpoints zero and two. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory TDA.Persistence TDA.Sheaf.AlternatingDiagram
open TDA.Sheaf.RealConstructible TDA.Sheaf.RealStratification

namespace TDA.Sheaf.BandConvolution.Examples

private def p : Fin 2 → ℝ := ![0, 2]
private def q : Fin 3 → ℝ := ![0, 1, 2]

private theorem hp : StrictMono p := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  norm_num [p]

private theorem hq : StrictMono q := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i <;> norm_num [q]

private def J : FiniteInterval 5 := ⟨2, 3, by decide, by decide⟩
private def K : FiniteInterval 7 := ⟨1, 6, by decide, by decide⟩

private def A : IntervalEndpoints := .ioo 0 2 (by norm_num)
private def B : IntervalEndpoints := .icc 0 2 (by norm_num)

private theorem hJ : intervalSet p J = A.support := by
  rw [intervalSet_eq_Ioo hp (i := 0) (j := 1) rfl rfl]
  simp [p, A, IntervalEndpoints.support]

private theorem hK : intervalSet q K = B.support := by
  rw [intervalSet_eq_Icc hq (i := 0) (j := 2) rfl rfl]
  simp [q, B, IntervalEndpoints.support]

variable (k : Type) [Field k]

local notation "F" => Functor.obj (extension k hp) (interval (orient 2) J)
local notation "G" => Functor.obj (extension k hq) (interval (orient 3) K)

example (f : G ⟶ F) : f = 0 :=
  B.hom_eq_zero_of_not_homAllowed k hq hp A hK hJ (fun h => h.2.1) f

example : Function.Bijective (fun f : F ⟶ G =>
    (TopCat.Presheaf.stalkFunctor (ModuleCat k) (X := realLine) (1 : ℝ)).map f.hom) := by
  have hx : (1 : ℝ) ∈ A.support ∩ B.support :=
    ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  exact A.bijective_stalkMap_of_homAllowed k hp hq B hJ hK ⟨⟨1, hx⟩, trivial, trivial⟩ hx

example (f : G ⟶ F) (g : F ⟶ G) : f ≫ g = 0 :=
  B.hom_comp_eq_zero_of_different_type k hq hp hq A B hK hJ hK rfl rfl f g

end TDA.Sheaf.BandConvolution.Examples
