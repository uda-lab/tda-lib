import TDA.Filtration.RationalAlpha.Predicates

set_option autoImplicit false

/-!
# Exact fixtures for rational planar predicates
-/

namespace TDA.Filtration.RationalAlpha.PredicatesExamples

def A : Point := (0, 0)
def B : Point := (4, 0)
def C : Point := (3, 2)
def D : Point := (0, 2)

theorem quad_predicates :
    orient A B C = 8 ∧ orient A C D = 6 ∧ orient A B D = 8 ∧ orient B C D = 6 ∧
    incircle A B C D = -24 ∧ incircle A C D B = -24 ∧
    incircle A B D C = 24 ∧ incircle B C D A = 24 := by decide +kernel

theorem swapped_predicates :
    orient B A C = -8 ∧ incircle B A C D = 24 := by decide +kernel

theorem collinear_orientation : orient A (1, 0) B = 0 := by decide +kernel

theorem cocircular_incircle :
    orient A B (4, 4) = 16 ∧ incircle A B (4, 4) (0, 4) = 0 := by decide +kernel

end TDA.Filtration.RationalAlpha.PredicatesExamples
