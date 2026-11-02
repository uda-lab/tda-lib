import TDA.Persistence.LocallyFiniteMatchingCompactness
import TDA.Persistence.RealInterleavingDistance

/-!
# Stability and isomorphism invariance of q-tame diagrams

The finite-birth decorated diagram extracted from a q-tame real persistence module
is invariant under natural isomorphism. Its bottleneck distance is bounded by the
extended real interleaving distance, without assuming finite distance or attainment.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open MeasureTheory RectangleMeasure
open scoped ENNReal

noncomputable section

private theorem contentMultiplicity_eq_of_values_eq
    {X : Type*} {C : Set (Set X)} {m₁ m₂ : AddContent ℕ C}
    (hval : ∀ U ∈ C, m₁ U = m₂ U) (x : X) :
    contentMultiplicity m₁ x = contentMultiplicity m₂ x := by
  unfold contentMultiplicity
  congr 1
  ext n
  constructor
  · rintro ⟨U, hU, hxU, hn⟩
    exact ⟨U, hU, hxU, (hval U hU).symm.trans hn⟩
  · rintro ⟨U, hU, hxU, hn⟩
    exact ⟨U, hU, hxU, (hval U hU).trans hn⟩

private theorem persistenceMeasureValue_eq_of_interleavingIso
    {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) :
    persistenceMeasureValue M hab hbc.le hcd =
      persistenceMeasureValue N hab hbc.le hcd := by
  let i := RealInterleaving.ofIso e
  have hMN := i.persistenceMeasureValue_box_le_of_qTame hN hab hcd
    (by simpa using (sub_pos.mpr hbc))
  have hNM := i.symm.persistenceMeasureValue_box_le_of_qTame hM hab hcd
    (by simpa using (sub_pos.mpr hbc))
  exact le_antisymm (by simpa using hMN) (by simpa using hNM)

private theorem essentialMeasureValue_eq_of_interleavingIso
    {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    {a b : ℝ} (hab : a ≤ b) :
    essentialMeasureValue M hab = essentialMeasureValue N hab := by
  let i := RealInterleaving.ofIso e
  have hMN := i.essentialMeasureValue_box_le_of_qTame hN hab
  have hNM := i.symm.essentialMeasureValue_box_le_of_qTame hM hab
  exact le_antisymm (by simpa using hMN) (by simpa using hNM)

private theorem moduleRectangleValue_eq_of_interleavingIso
    {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    (U : Set (Cut ℝ × Cut ℝ)) :
    moduleRectangleValue M U = moduleRectangleValue N U := by
  by_cases hU : U = ∅
  · simp [moduleRectangleValue, hU]
  · simp only [moduleRectangleValue, if_neg hU]
    let I := rectangleCellBox U
    by_cases hsep : I.upper 0 < I.lower 1
    · rw [persistenceBoxValue_of_separated M I hsep,
        persistenceBoxValue_of_separated N I hsep]
      have hMN := (RealInterleaving.ofIso e).persistenceMeasureValue_box_le_of_qTame
        hN (I.lower_lt_upper 0).le (I.lower_lt_upper 1).le
        (by simpa using (sub_pos.mpr hsep))
      have hNM := (RealInterleaving.ofIso e).symm.persistenceMeasureValue_box_le_of_qTame
        hM (I.lower_lt_upper 0).le (I.lower_lt_upper 1).le
        (by simpa using (sub_pos.mpr hsep))
      exact le_antisymm (by simpa using hMN) (by simpa using hNM)
    · simp [persistenceBoxValue, I, hsep]

private theorem moduleDiagramMultiplicity_eq_of_interleavingIso
    {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    (p : Cut ℝ × Cut ℝ) :
    moduleDiagramMultiplicity M hM p = moduleDiagramMultiplicity N hN p := by
  apply contentMultiplicity_eq_of_values_eq
  intro U hU
  change moduleRectangleValue M U = moduleRectangleValue N U
  exact moduleRectangleValue_eq_of_interleavingIso e hM hN U

private theorem moduleEssentialMultiplicity_eq_of_interleavingIso
    {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    (birth : Cut ℝ) :
    moduleEssentialMultiplicity M hM birth = moduleEssentialMultiplicity N hN birth := by
  apply contentMultiplicity_eq_of_values_eq
  intro U hU
  obtain ⟨a, b, hab, rfl⟩ := hU
  rw [essentialCutContent_apply M hM hab, essentialCutContent_apply N hN hab]
  exact essentialMeasureValue_eq_of_interleavingIso e hM hN hab

namespace LocallyFiniteDecoratedDiagram

/-- The finite-birth decorated diagram extracted from a q-tame real module is invariant
under a natural isomorphism. The proof preserves both finite-death rectangle contents
and the essential birth-boundary multiplicities. -/
theorem ofQModule_eq_of_iso
    {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame) :
    ofQModule hM = ofQModule hN := by
  apply LocallyFiniteDecoratedDiagram.ext
  funext p
  by_cases hInf : p.2 = infinityCut
  · have hess := moduleEssentialMultiplicity_eq_of_interleavingIso e hM hN p.1
    simp [LocallyFiniteDecoratedDiagram.ofQModule, moduleExtendedDiagramMultiplicity,
      hInf, hess]
  · have hfin := moduleDiagramMultiplicity_eq_of_interleavingIso e hM hN p
    simp [LocallyFiniteDecoratedDiagram.ofQModule, moduleExtendedDiagramMultiplicity,
      hInf, hfin]

/-- For q-tame real persistence modules over any field, the bottleneck distance of the
finite-birth decorated diagrams is bounded by the extended real interleaving distance.
The proof takes the infimum of the bound for actual interleavings, so it needs neither a
finite distance nor an attained minimizer. -/
theorem qTame_bottleneck_le_realInterleavingDistance
    {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) (hN : N.QTame) :
    (ofQModule hM).bottleneck (ofQModule hN) ≤
      realInterleavingDistance M N := by
  refine (le_realInterleavingDistance_iff).2 ?_
  intro ε hε
  obtain ⟨i⟩ := hε
  simpa only [ENNReal.ofReal_coe_nnreal] using
    (qTame_bottleneck_le_of_realInterleaving i hM hN)

end LocallyFiniteDecoratedDiagram

end
end TDA.Persistence
