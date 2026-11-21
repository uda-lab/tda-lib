import TDA.Persistence.F2GridHomologyIso
import TDA.Persistence.F2GridHomologyInputExamples

/-!
# The triangle fixtures compute their homology

The isomorphism between the Kan extension of a generated representation and the actual homology,
and its consequences, instantiated on the fixtures of `F2GridHomologyInputExamples` without
evaluating any generated dimension, rank or matrix:

* the isomorphism for the triangle in degree one;
* erosion between the generated triangle and its translate by `(1/2, 0)` is erosion between their
  actual degree-one homology modules;
* the isomorphism for the empty input on no vertices, in every degree;
* the generated dimension of the triangle at `(1, 1)` is the actual first Betti number there.
-/

set_option autoImplicit false

namespace TDA.Persistence.F2GridHomologyIsoExamples

open CategoryTheory TDA.Persistence RatGradedInput RatGrid F2GridHomologyInputExamples

/-- The triangle fixture: the Kan extension of its generated representation is its actual
degree-one homology. -/
noncomputable def triangle_lanIso :
    (toF2GridRep triangle 1).grid.lan.obj
        ((toF2GridRep triangle 1).toModule (toF2GridRep_valid triangle_valid 1)) ≅
      homology triangle triangle_valid 1 :=
  toF2GridRep_lanIso triangle_valid 1

/-- Erosion between the generated triangle fixtures is erosion between their actual degree-one
homology modules. -/
theorem triangle_rankErosion_iff (ε : NNReal) :
    RankErosion ε ((toF2GridRep triangle 1).grid.lan.obj
        ((toF2GridRep triangle 1).toModule (toF2GridRep_valid triangle_valid 1)))
      ((toF2GridRep shiftedTriangle 1).grid.lan.obj
        ((toF2GridRep shiftedTriangle 1).toModule (toF2GridRep_valid shiftedTriangle_valid 1))) ↔
      RankErosion ε (homology triangle triangle_valid 1)
        (homology shiftedTriangle shiftedTriangle_valid 1) :=
  rankErosion_lan_toF2GridRep_iff triangle_valid shiftedTriangle_valid 1 ε

/-- The isomorphism also covers input with no vertices. -/
noncomputable def empty_lanIso (p : ℕ) :
    (toF2GridRep ([] : RatGradedInput 0 2) p).grid.lan.obj
        ((toF2GridRep ([] : RatGradedInput 0 2) p).toModule (toF2GridRep_valid empty_valid p)) ≅
      homology ([] : RatGradedInput 0 2) empty_valid p :=
  toF2GridRep_lanIso empty_valid p

/-- The generated triangle dimension at the hollow grade is the actual first Betti number of
the hollow triangle. -/
theorem triangle_dim_hollow :
    (toF2GridRep triangle 1).dim (![1, 1] : Fin 2 → ℚ) =
      Module.finrank (ZMod 2)
        ((homology triangle triangle_valid 1).obj (realGrade (![1, 1] : Fin 2 → ℚ))) :=
  toF2GridRep_dim triangle_valid 1 _

end TDA.Persistence.F2GridHomologyIsoExamples
