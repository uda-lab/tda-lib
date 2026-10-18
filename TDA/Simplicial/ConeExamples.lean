import TDA.Simplicial.Cone
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-!
# Apex-cone fixtures

Concrete triangle computations check the full-simplex homology ranks, the ordered boundary
signs in the cone identity, and the two ways the apex-cone hypotheses can fail.
-/

namespace TDA.Simplicial.ConeExamples

open TDA.Simplicial
open CategoryTheory.Limits

/-! ### Full-simplex homology -/

/-- The full three-vertex simplex has zero integral homology in degree one. -/
theorem isZero_simplicialHomology_triangle_one :
    IsZero (simplicialHomology (⊤ : PreAbstractSimplicialComplex (Fin 3)) ℤ 1) := by
  exact TDA.Simplicial.isZero_simplicialHomology_top_succ (V := Fin 3) ℤ 0

/-- The full three-vertex simplex has zero integral homology in degree two. -/
theorem isZero_simplicialHomology_triangle_two :
    IsZero (simplicialHomology (⊤ : PreAbstractSimplicialComplex (Fin 3)) ℤ 2) := by
  exact TDA.Simplicial.isZero_simplicialHomology_top_succ (V := Fin 3) ℤ 1

/-- The degree-zero homology of the full three-vertex simplex has F₂-rank one. -/
theorem finrank_simplicialHomology_triangle_zero :
    Module.finrank (ZMod 2)
        (simplicialHomology (⊤ : PreAbstractSimplicialComplex (Fin 3)) (ZMod 2) 0) = 1 := by
  simpa using (TDA.Simplicial.finrank_simplicialHomology_top_zero
    (V := Fin 3) (ZMod 2))

/-! ### Concrete signed boundary computation -/

/-- The cone operator kills the top face containing its apex. -/
theorem coneOperator_triangle_face_eq_zero :
    (isApexCone_top (0 : Fin 3) (fun w => Fin.zero_le w)).coneOperator ℤ 2
        (Finsupp.single
          (⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide,
            by decide⟩ : Face (⊤ : PreAbstractSimplicialComplex (Fin 3)) 2) 1) = 0 := by
  let hK : IsApexCone (⊤ : PreAbstractSimplicialComplex (Fin 3)) 0 :=
    isApexCone_top 0 (fun w => Fin.zero_le w)
  let σ : Face (⊤ : PreAbstractSimplicialComplex (Fin 3)) 2 :=
    ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩
  change hK.coneOperator ℤ 2 (Finsupp.single σ 1) = 0
  simp [IsApexCone.coneOperator, σ]

/-- The concrete triangle boundary has the sign convention expected by the cone identity. -/
theorem boundary_coneOperator_triangle_face :
    (isApexCone_top (0 : Fin 3) (fun w => Fin.zero_le w)).coneOperator ℤ 1
        (boundary (⊤ : PreAbstractSimplicialComplex (Fin 3)) ℤ 1
          (Finsupp.single
            (⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide,
              by decide⟩ : Face (⊤ : PreAbstractSimplicialComplex (Fin 3)) 2) 1)) =
      Finsupp.single
        (⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide,
          by decide⟩ : Face (⊤ : PreAbstractSimplicialComplex (Fin 3)) 2) 1 := by
  let hK : IsApexCone (⊤ : PreAbstractSimplicialComplex (Fin 3)) 0 :=
    isApexCone_top 0 (fun w => Fin.zero_le w)
  let σ : Face (⊤ : PreAbstractSimplicialComplex (Fin 3)) 2 :=
    ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩
  let edge01 : Face (⊤ : PreAbstractSimplicialComplex (Fin 3)) 1 :=
    ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty; decide, by decide⟩
  let edge02 : Face (⊤ : PreAbstractSimplicialComplex (Fin 3)) 1 :=
    ⟨{0, 2}, by change ({0, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩
  let edge12 : Face (⊤ : PreAbstractSimplicialComplex (Fin 3)) 1 :=
    ⟨{1, 2}, by change ({1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩
  change hK.coneOperator ℤ 1
      (boundary (⊤ : PreAbstractSimplicialComplex (Fin 3)) ℤ 1
        (Finsupp.single σ 1)) = Finsupp.single σ 1
  have horder : σ.1.orderEmbOfFin σ.2.2 =
      (OrderIso.refl (Fin 3)).toOrderEmbedding := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    fin_cases i <;> simp [σ]
  have hboundary :
      boundary (⊤ : PreAbstractSimplicialComplex (Fin 3)) ℤ 1
          (Finsupp.single σ 1) =
        Finsupp.single edge12 1 - Finsupp.single edge02 1 +
          Finsupp.single edge01 1 := by
    rw [boundary_single]
    simp only [Fin.sum_univ_succ, deletedFace, horder]
    simp [σ, edge01, edge02, edge12, sub_eq_add_neg]
    abel
  have h01 : (0 : Fin 3) ∈ edge01.1 := by simp [edge01]
  have h02 : (0 : Fin 3) ∈ edge02.1 := by simp [edge02]
  have h12 : (0 : Fin 3) ∉ edge12.1 := by simp [edge12]
  have hcone12 : hK.coneFace edge12 h12 = σ := by
    apply Subtype.ext
    simp [IsApexCone.coneFace, edge12, σ]
  rw [hboundary, map_add, map_sub,
    hK.coneOperator_single_of_notMem ℤ edge12 1 h12,
    hK.coneOperator_single_of_mem ℤ edge02 1 h02,
    hK.coneOperator_single_of_mem ℤ edge01 1 h01, hcone12]
  simp

/-! ### Failed apex hypotheses -/

/-- The vertex `1` is not an apex of the full three-vertex simplex. -/
theorem not_isApexCone_top_one :
    ¬ IsApexCone (⊤ : PreAbstractSimplicialComplex (Fin 3)) 1 := by
  intro hK
  have hle := hK.apex_le ({0} : Finset (Fin 3))
    (by change ({0} : Finset (Fin 3)).Nonempty; decide) 0 (by simp)
  norm_num at hle

/-- The empty complex has no apex because it has no singleton faces. -/
theorem not_isApexCone_bot_zero :
    ¬ IsApexCone (⊥ : PreAbstractSimplicialComplex (Fin 3)) 0 := by
  intro hK
  exact (TDA.Filtration.mem_bot_iff _).mp hK.apex_mem

end TDA.Simplicial.ConeExamples
