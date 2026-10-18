import TDA.Reeb.GeometricDistanceBounds

/-!
# Interval-local component obstructions

This module records interval-local injectivity and cardinality obstructions to interleavings of
Type-valued interval precosheaves, their transport to geometric interleavings, and the resulting
distance lower bound.  These are library statements proved from the existing interleaving,
constructible-cosheaf and geometric interleaving APIs.  The corresponding mathematical
conventions are documented in `docs/math/reeb-geometric-interleaving-equivalence.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

universe v

namespace TDA.Reeb

noncomputable section

namespace Interleaving

open OpenInterval

variable {ε : ℝ≥0} {F G : OpenInterval ⥤ Type v}

/-- An injective double-thickening restriction makes the first interleaving map injective. -/
theorem φ_app_injective (j : Interleaving ε F G) {I : OpenInterval}
    (h : Function.Injective
      (F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I)))))) :
    Function.Injective (j.φ.app I) := by
  have h' := h
  rw [← j.φ_ψ_app I] at h'
  exact Function.Injective.of_comp (by simpa only [types_comp] using h')

/-- A nontrivial source value and a subsingleton shifted target forbid an interleaving. -/
theorem isEmpty_of_injective_of_subsingleton {I : OpenInterval}
    (h : Function.Injective
      (F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))))
    [Nontrivial (F.obj I)] [Subsingleton (G.obj (thicken ε I))] :
    IsEmpty (Interleaving ε F G) := by
  refine ⟨fun j => ?_⟩
  have hφ : Function.Injective (j.φ.app I) := j.φ_app_injective h
  exact (@false_of_nontrivial_of_subsingleton _ hφ.nontrivial
    (inferInstance : Subsingleton _)).elim

/-- A finite shifted target with smaller cardinality forbids an interleaving. -/
theorem isEmpty_of_injective_of_card_lt {I : OpenInterval}
    (h : Function.Injective
      (F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))))
    [Finite (G.obj (thicken ε I))]
    (hc : Nat.card (G.obj (thicken ε I)) < Nat.card (F.obj I)) :
    IsEmpty (Interleaving ε F G) := by
  refine ⟨fun j => ?_⟩
  have hφ : Function.Injective (j.φ.app I) := j.φ_app_injective h
  have hcard := Nat.card_le_card_of_injective (j.φ.app I) hφ
  exact (not_le_of_gt hc hcard).elim

end Interleaving

namespace RGraph

open OpenInterval

variable {ε : ℝ≥0}

/-- A nontrivial source graph value and a subsingleton shifted target graph value forbid a
geometric interleaving. -/
theorem isEmpty_geometricInterleaving_of_injective_of_subsingleton {A B : RGraphCat}
    {I : OpenInterval}
    (h : Function.Injective ((cosheafFunctor.obj A).obj.map
      (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))))
    [Nontrivial ((cosheafFunctor.obj A).obj.obj I)]
    [Subsingleton ((cosheafFunctor.obj B).obj.obj (thicken ε I))] :
    IsEmpty (GeometricInterleaving ε A B) := by
  refine ⟨fun i => ?_⟩
  exact (Interleaving.isEmpty_of_injective_of_subsingleton h).false i.toCosheaf

/-- A finite shifted target graph value with smaller cardinality forbids a geometric interleaving.
-/
theorem isEmpty_geometricInterleaving_of_injective_of_card_lt {A B : RGraphCat}
    {I : OpenInterval}
    (h : Function.Injective ((cosheafFunctor.obj A).obj.map
      (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))))
    [Finite ((cosheafFunctor.obj B).obj.obj (thicken ε I))]
    (hc : Nat.card ((cosheafFunctor.obj B).obj.obj (thicken ε I)) <
      Nat.card ((cosheafFunctor.obj A).obj.obj I)) :
    IsEmpty (GeometricInterleaving ε A B) := by
  refine ⟨fun i => ?_⟩
  exact (Interleaving.isEmpty_of_injective_of_card_lt h hc).false i.toCosheaf

/-- If every parameter below `r` is obstructed, then `r` is a lower bound for geometric distance.
-/
theorem le_geometricInterleavingDistance_of_isEmpty {A B : RGraphCat} {r : ℝ≥0}
    (h : ∀ ε : ℝ≥0, ε < r → IsEmpty (GeometricInterleaving ε A B)) :
    (r : ℝ≥0∞) ≤ geometricInterleavingDistance A B := by
  rw [le_geometricInterleavingDistance_iff]
  intro ε hε
  by_contra hnot
  have hεr : (ε : ℝ≥0) < r :=
    ENNReal.coe_lt_coe.mp (lt_of_not_ge hnot)
  obtain ⟨i⟩ := hε
  exact (h ε hεr).false i

end RGraph

end

end TDA.Reeb
