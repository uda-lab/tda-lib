import TDA.Persistence.Simplicial

/-! The vertex-birth filtration evaluated with actual degree-zero homology. -/

namespace TDA.Persistence.SimplicialExamples

open CategoryTheory TDA.Simplicial

private noncomputable def birthModule (x : Fin 3) :
    PModule.{0,0,0} ℤ (Fin 2) :=
  simplicialHomologyPModule ℤ (Filtration.vertexBirth x) 0

private theorem birthSource_zero (x : Fin 3) (z : (birthModule x).obj 0) : z = 0 := by
  change simplicialHomology (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 0 at z
  exact simplicialHomology_bot_zero ℤ z

private noncomputable def birthTargetEquiv (x : Fin 3) :
    (birthModule x).obj 1 ≃ₗ[ℤ] ℤ := by
  change simplicialHomology (Filtration.singletonFace x) ℤ 0 ≃ₗ[ℤ] ℤ
  exact simplicialSingletonH0Equiv ℤ x

private theorem birthTarget_nonzero (x : Fin 3) :
    (birthTargetEquiv x).symm 1 ≠ 0 := by
  exact simplicialSingletonH0Equiv_symm_one_ne_zero ℤ x

private theorem birthTransition_zero (x : Fin 3) :
    structureMapLinear (birthModule x) (show (0 : Fin 2) ≤ 1 by decide) = 0 := by
  apply LinearMap.ext
  intro z
  have hz := birthSource_zero x z
  subst z
  simp

private theorem birthTransition_is_actual_inclusion (x : Fin 3) :
    structureMap (birthModule x) (show (0 : Fin 2) ≤ 1 by decide) =
      simplicialHomologyIncl ℤ
        ((Filtration.vertexBirth x).monotone (show (0 : Fin 2) ≤ 1 by decide)) 0 :=
  simplicialHomologyPModule_structureMap ℤ (Filtration.vertexBirth x) 0 _

private theorem birthSelf_zero (x : Fin 3) :
    structureMap (birthModule x) (le_refl (0 : Fin 2)) = 𝟙 ((birthModule x).obj 0) :=
  structureMap_self _ _

private theorem birthSelf_one (x : Fin 3) :
    structureMap (birthModule x) (le_refl (1 : Fin 2)) = 𝟙 ((birthModule x).obj 1) :=
  structureMap_self _ _

private noncomputable def matrixBirth :
    PModule.{0,0,0} (Matrix (Fin 2) (Fin 2) ℤ) (Fin 2) :=
  simplicialHomologyPModule (Matrix (Fin 2) (Fin 2) ℤ)
    (Filtration.vertexBirth (0 : Fin 3)) 0

private noncomputable def charTwoBirth : PModule.{0,0,0} (ZMod 2) (Fin 2) :=
  simplicialHomologyPModule (ZMod 2) (Filtration.vertexBirth (0 : Fin 3)) 0

private noncomputable def zeroRingBirth : PModule.{0,0,0} (ZMod 1) (Fin 2) :=
  simplicialHomologyPModule (ZMod 1) (Filtration.vertexBirth (0 : Fin 3)) 0

#print axioms birthModule
#print axioms birthSource_zero
#print axioms birthTargetEquiv
#print axioms birthTarget_nonzero
#print axioms birthTransition_zero
#print axioms birthTransition_is_actual_inclusion
#print axioms birthSelf_zero
#print axioms birthSelf_one
#print axioms matrixBirth
#print axioms charTwoBirth
#print axioms zeroRingBirth

end TDA.Persistence.SimplicialExamples
