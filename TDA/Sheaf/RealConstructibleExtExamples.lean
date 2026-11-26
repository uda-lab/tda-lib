import TDA.Sheaf.RealConstructibleExt
import TDA.Sheaf.RealConstructibleExamples

/-!
# Fixtures for the `Ext` comparison on the real line

One breakpoint at `0` (`p₁`), strata `0 ← 1 → 2` with stars `(-∞, 0)`, `ℝ` and `(0, ∞)`,
coefficients `ℚ`.

* `nontrivial_ext_one_point_rightCell`: on the diagram side, `Ext¹` from the point interval
  `[1, 1]` (`pointDiagram`) to the right cell interval `[2, 2]` (`rightCell`) is nonzero. The
  class is the image of a morphism `L ⟶ interval [2, 2]` out of the first term of the standard
  resolution `0 → L → P → [1, 1] → 0` under the connecting map; it is nonzero because the
  morphism is nonzero on the slot of the arrow `1 → 2` while every morphism
  `P ⟶ interval [2, 2]` vanishes.
* `nontrivial_ext_one_pointSheaf_rightOpen`: through the comparison
  `mapExt_bijective_extension`, `Ext¹` from the field at the point `0` (`pointSheaf`) to the
  field on the open half-line `(0, ∞)` (`rightOpen`) is nonzero, in all sheaves of
  `ℚ`-modules on `ℝ`.
* `ext_two_sky_rightClosed_eq_zero`: `Ext²` from Mathlib's skyscraper sheaf at `0` to the field
  on `[0, ∞)` vanishes (`ext_constructible_eq_zero_of_two_le`).
-/

namespace TDA.Sheaf.RealConstructibleExtExamples

open CategoryTheory Limits Abelian TDA.Persistence TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.RealStratification TDA.Sheaf.RealConstructible TDA.Sheaf.RealStratificationExamples
  TDA.Sheaf.RealConstructibleExamples

/-- The right cell `[2, 2]` of `0 ← 1 → 2`. -/
def rightCell : FiniteInterval 3 := ⟨2, 3, by decide, by decide⟩

/-- The field on the open half-line `(0, ∞)`: the sheaf of the right cell. -/
noncomputable abbrev rightOpen : TopCat.Sheaf (ModuleCat.{0} ℚ) realLine :=
  intervalSheaf ℚ rightCell

section Diagram

variable (k : Type) [Field k]

/-- The map between the fibres of two intervals at two vertices: the identity of the field when
the first vertex lies in the first interval and the second in the second, and zero otherwise. -/
private def crossMap {n : ℕ} (J J' : FiniteInterval (n + 1)) (i j : Fin (n + 1)) :
    J.fiber (k := k) i →ₗ[k] J'.fiber (k := k) j :=
  if h : J.alive i ∧ J'.alive j then
    Submodule.inclusion (by simp [FiniteInterval.fiber, h.1, h.2]) else 0

/-- The morphism from the first term `L = ⊕_(a : i → j) P_j ⊗ [1, 1]_i` of the standard
resolution of `[1, 1]` to `[2, 2]`: the identity of the field on the slot of the arrow
`1 → 2`. -/
private noncomputable def edgeMap :
    resolutionLeft (pointDiagram k) ⟶ interval (k := k) (orient 1) rightCell :=
  sumTensorDesc (fun e : Edge (orient 1) => e.1.2)
    (fun e => (pointDiagram k).obj (vtx (orient 1) e.1.1)) _
    (fun e => ModuleCat.ofHom (crossMap k pointSegment rightCell e.1.1 e.1.2))

/-- The fibre of an interval at a vertex outside it is zero. -/
private theorem subsingleton_fiber {J : FiniteInterval 3} {j : Fin 3} (hj : ¬J.alive j) :
    Subsingleton (J.fiber (k := k) j) :=
  ⟨fun a b => Subtype.ext ((fiber_val_eq_zero hj a).trans (fiber_val_eq_zero hj b).symm)⟩

/-- Morphisms out of the middle term `P = ⊕_i P_i ⊗ [1, 1]_i` of the resolution to `[2, 2]`
vanish: `[1, 1]` and `[2, 2]` have no common vertex. -/
private theorem resolutionMiddle_hom_eq_zero
    (x : resolutionMiddle (pointDiagram k) ⟶ interval (k := k) (orient 1) rightCell) : x = 0 := by
  refine biproduct.hom_ext' (f := fun j : Fin 3 =>
      (pathTensor k (orient 1) j).obj ((pointDiagram k).obj (vtx (orient 1) j))) x 0
    fun j => ((pathTensorAdjunction k (orient 1) j).homEquiv _ _).injective ?_
  have hsub : ∀ {A B : ModuleCat.{0} k}, Subsingleton A ∨ Subsingleton B →
      Subsingleton (A ⟶ B) := fun h => ⟨fun f g => ModuleCat.hom_ext (LinearMap.ext fun a => by
    rcases h with h | h
    · rw [Subsingleton.elim a 0, map_zero, map_zero]
    · exact Subsingleton.elim _ _)⟩
  refine @Subsingleton.elim _ (hsub ?_) _ _
  by_cases hj : j = 1
  · subst hj
    exact Or.inr (subsingleton_fiber k (J := rightCell) (j := 1) (by decide))
  · exact Or.inl (subsingleton_fiber k (J := pointSegment) (j := j) (fun h => hj (Fin.ext (by
      change 1 ≤ j.val ∧ j.val < 2 at h
      change j.val = 1
      omega))))

/-- `edgeMap` is nonzero: on the slot of the arrow `1 → 2` it is the identity of the field. -/
private theorem edgeMap_ne_zero : edgeMap k ≠ 0 := by
  intro h
  let e₀ : Edge (orient 1) := ⟨(1, 2), arrow_one_two⟩
  have hs := sumSlot_sumTensorDesc_app (fun e : Edge (orient 1) => e.1.2)
    (fun e => (pointDiagram k).obj (vtx (orient 1) e.1.1)) (interval (k := k) (orient 1) rightCell)
    (fun e => ModuleCat.ofHom (crossMap k pointSegment rightCell e.1.1 e.1.2)) e₀ (𝟙 _)
  change _ ≫ (edgeMap k).app _ = _ at hs
  simp only [h, NatTrans.app_zero, CategoryTheory.Functor.map_id] at hs
  have h1 : (1 : k) ∈ pointSegment.fiber (k := k) 1 := by
    simp [FiniteInterval.fiber, show pointSegment.alive 1 from by decide]
  have := congrArg Subtype.val (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hs) ⟨1, h1⟩)
  have hc : pointSegment.alive 1 ∧ rightCell.alive 2 := by decide
  simp only [crossMap, e₀, hc] at this
  exact one_ne_zero this.symm

/-- The class in `Ext¹([1, 1], [2, 2])` of `edgeMap` under the connecting map of the standard
resolution is nonzero. -/
private theorem extClass_comp_edgeMap_ne_zero [HasExt.{0} (Diagram k (orient 1))] :
    (resolution_shortExact (pointDiagram k)).extClass.comp (Ext.mk₀ (edgeMap k)) (add_zero 1) ≠
      0 := by
  intro h
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ (resolution_shortExact (pointDiagram k))
    _ (Ext.mk₀ (edgeMap k)) (add_zero 1) h
  obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
  rw [Ext.mk₀_comp_mk₀] at hx₂
  have he := ((Ext.mk₀_bijective _ _).1 hx₂).symm
  rw [resolutionMiddle_hom_eq_zero k x] at he
  exact edgeMap_ne_zero k (he.trans (by simp))

end Diagram

/-- **A nonzero `Ext¹` of diagrams.** `Ext¹` from the point interval `[1, 1]` to the right cell
interval `[2, 2]` of `0 ← 1 → 2` is nontrivial (the arrow `1 → 2`). -/
theorem nontrivial_ext_one_point_rightCell [HasExt.{0} (Diagram ℚ (orient 1))] :
    Nontrivial (Ext (pointDiagram ℚ) (interval (k := ℚ) (orient 1) rightCell) 1) :=
  ⟨⟨_, 0, extClass_comp_edgeMap_ne_zero ℚ⟩⟩

/-- **A nonzero `Ext¹` between constructible sheaves on `ℝ`.** `Ext¹` from the field at the
point `0` to the field on the open half-line `(0, ∞)` is nontrivial, in all sheaves of
`ℚ`-modules on `ℝ`: the image of the diagram class under `mapExt_bijective_extension`. -/
theorem nontrivial_ext_one_pointSheaf_rightOpen
    [HasExt.{0} (TopCat.Sheaf (ModuleCat.{0} ℚ) realLine)] :
    Nontrivial (Ext (pointSheaf ℚ) rightOpen 1) := by
  have := hasExt_diagram ℚ (orient 1)
  exact ⟨⟨_, 0, fun h => extClass_comp_edgeMap_ne_zero ℚ
    ((mapExt_bijective_extension ℚ p₁_strictMono _ _ 1).1 (h.trans (map_zero _).symm))⟩⟩

/-- **`Ext²` between constructible sheaves on `ℝ` vanishes.** `Ext²` from Mathlib's skyscraper
sheaf at `0` to the field on `[0, ∞)` is zero, in all sheaves of `ℚ`-modules on `ℝ`. -/
theorem ext_two_sky_rightClosed_eq_zero [HasExt.{0} (TopCat.Sheaf (ModuleCat.{0} ℚ) realLine)]
    (e : Ext (sky ℚ) (rightClosed ℚ) 2) : e = 0 :=
  ext_constructible_eq_zero_of_two_le ℚ p₁_strictMono ⟨sky ℚ, isConstructible_sky ℚ⟩
    ⟨rightClosed ℚ, isConstructible_intervalSheaf ℚ segRight⟩ le_rfl e

end TDA.Sheaf.RealConstructibleExtExamples
