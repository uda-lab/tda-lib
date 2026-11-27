import TDA.Sheaf.RealIntervalSetsExamples

/-!
# Fixtures for local constancy on the real line

The constant sheaf with value `ℚ` is interval-locally constant on the whole line. The closed
left ray sheaf is locally isomorphic to a constant sheaf on the punctured line. Its stalks at
`-1` and `1` have dimensions one and zero, which rules out one constant sheaf on the entire
punctured line.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace TDA.Sheaf.LocalSystemConstantExamples

open LocalSystem RealConstructible RealConstructibleExamples RealStratificationExamples
  RealIntervalSetsExamples

example :
    IsLocallyConstantOn
      ((constantSheaf (Opens.grothendieckTopology realLine) (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ ℚ)) Set.univ := by
  apply (isLocallyConstantOn_iff_locally_iso_constantSheaf _ _).mpr
  intro x _
  exact ⟨⊤, trivial, Set.subset_univ _, _, ⟨(pullbackConstantSheafIso ℚ _).app _⟩⟩

private def puncturedLine : Opens realLine := ⟨({0} : Set ℝ)ᶜ, isOpen_compl_singleton⟩

example : ¬ _root_.IsPreconnected (puncturedLine : Set ℝ) := by
  intro hc
  have hm : (-1 : ℝ) ∈ puncturedLine := by norm_num [puncturedLine]
  have hp : (1 : ℝ) ∈ puncturedLine := by norm_num [puncturedLine]
  have hz := hc.ordConnected.out hm hp (show (0 : ℝ) ∈ Set.Icc (-1) 1 by norm_num)
  exact hz rfl

example (x : ℝ) (hx : x ∈ puncturedLine) :
    ∃ N : Opens realLine, x ∈ N ∧ N ≤ puncturedLine ∧
      ∃ M : ModuleCat.{0} ℚ,
        Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) N.inclusion').obj (leftClosed ℚ) ≅
          (constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat realLine).obj N))
            (ModuleCat.{0} ℚ)).obj M) := by
  have h := (isConstructible_intervalSheaf ℚ segLeft).1
  rw [breakpoints_p₁, Finset.coe_singleton] at h
  exact (isLocallyConstantOn_iff_locally_iso_constantSheaf _ _).mp h x hx

example :
    ¬ ∃ M : ModuleCat.{0} ℚ,
      Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) puncturedLine.inclusion').obj
        (leftClosed ℚ) ≅ (constantSheaf
          (Opens.grothendieckTopology ((Opens.toTopCat realLine).obj puncturedLine))
          (ModuleCat.{0} ℚ)).obj M) := by
  rintro ⟨M, ⟨e⟩⟩
  let X := (Opens.toTopCat realLine).obj puncturedLine
  let N : pt.Sheaf (ModuleCat.{0} ℚ) :=
    (constantSheaf (Opens.grothendieckTopology pt) (ModuleCat.{0} ℚ)).obj M
  let e' := e ≪≫ ((pullbackConstantSheafIso ℚ (toPt X)).app M).symm
  let stalkIso (x : X) : (leftClosed ℚ).presheaf.stalk x.val ≅ N.presheaf.stalk PUnit.unit :=
    stalkPullbackSheafIso ℚ puncturedLine.inclusion' (leftClosed ℚ) x ≪≫
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).mapIso
        ((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X).mapIso e') ≪≫
      (stalkPullbackSheafIso ℚ (toPt X) N x).symm
  let negativePoint : X := ⟨-1, by norm_num [puncturedLine]⟩
  let positivePoint : X := ⟨1, by norm_num [puncturedLine]⟩
  have hm := finrank_stalk_extension_interval_of_mem ℚ p₁_strictMono (J := segLeft)
    (x := -1) (by rw [intervalSet_segLeft]; norm_num)
  have hp := finrank_stalk_extension_interval_of_notMem ℚ p₁_strictMono (J := segLeft)
    (x := 1) (by rw [intervalSet_segLeft]; norm_num)
  have he := ((stalkIso negativePoint) ≪≫ (stalkIso positivePoint).symm).toLinearEquiv.finrank_eq
  exact one_ne_zero (hm.symm.trans (he.trans hp))

end TDA.Sheaf.LocalSystemConstantExamples
