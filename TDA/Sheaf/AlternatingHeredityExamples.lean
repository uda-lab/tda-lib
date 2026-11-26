import TDA.Sheaf.AlternatingDiagramExamples
import TDA.Sheaf.AlternatingHeredity

/-!
# Fixtures for heredity of alternating diagrams

On the three-vertex fork `0 → 1 ← 2`, the whole interval `[0, 2]` has the standard projective
resolution `0 → ⊕_(a : i → j) P_j ⊗ M_i → ⊕_i P_i ⊗ M_i → [0, 2] → 0`, which is short exact
with projective terms; the sign `−M(a)` in the differential is what makes it a complex at all.
Consequently `Ext²` between interval diagrams vanishes, and so does every Yoneda product of two
`Ext¹` classes. The representable `P_0` reaches the sink: the path `0 → 1` gives a nonzero
vector of `(P_0)_1`.
-/

universe u w

namespace TDA.Sheaf.AlternatingHeredityExamples

open CategoryTheory Limits Abelian TDA.Persistence TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.AlternatingDiagramExamples

variable {k : Type u} [Field k]

/-- The standard resolution of `[0, 2]` on the fork is short exact. -/
theorem resolution_whole_shortExact :
    (resolution (interval (k := k) fork whole)).ShortExact :=
  resolution_shortExact _

/-- Both terms of the standard resolution of `[0, 2]` are projective. -/
theorem projective_resolution_whole :
    Projective (resolution (interval (k := k) fork whole)).X₁ ∧
      Projective (resolution (interval (k := k) fork whole)).X₂ := by
  rw [resolution_X₁, resolution_X₂]
  exact ⟨inferInstance, inferInstance⟩

/-- `Ext²([0, 2], {1}) = 0` on the fork. -/
theorem subsingleton_ext_two_whole_middle [HasExt.{w} (Diagram k fork)] :
    Subsingleton (Ext.{w} (interval (k := k) fork whole) (interval fork middle) 2) :=
  subsingleton_ext _ _ le_rfl

/-- The Yoneda product of `Ext¹([0, 2], {1})` and `Ext¹({1}, [0, 1])` vanishes, since it lies in
`Ext²([0, 2], [0, 1]) = 0`. -/
theorem ext_one_comp_ext_one_eq_zero [HasExt.{w} (Diagram k fork)]
    (α : Ext.{w} (interval (k := k) fork whole) (interval fork middle) 1)
    (β : Ext.{w} (interval (k := k) fork middle) (interval fork leftEdge) 1) :
    α.comp β (show 1 + 1 = 2 from rfl) = 0 :=
  ext_eq_zero _ _ le_rfl _

/-- The path `0 → 1` gives a nonzero vector of `P_0` at the sink. -/
theorem pathSlot_zero_one_ne_zero :
    (pathSlot 0 (ModuleCat.of k k) (gen arrow_zero_one)).hom (1 : k) ≠ 0 := by
  intro h
  have := congrArg (pathTensorObjEquiv 0 (ModuleCat.of k k) (vtx fork 1)) h
  rw [pathTensorObjEquiv_pathSlot, map_zero, Finsupp.single_eq_zero] at this
  exact one_ne_zero this

end TDA.Sheaf.AlternatingHeredityExamples
