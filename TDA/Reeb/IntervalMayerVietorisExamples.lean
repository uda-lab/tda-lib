import TDA.Reeb.IntervalMayerVietoris

/-!
# Examples for Mayer–Vietoris sequences of interval squares

* `exampleSquare` is the endpoint square with `(a, b) = (1, 1)` and `(a', b') = (2, 3)`: its
  corners are `SW = (-1, 1)`, `left = (-2, 1)`, `right = (-1, 3)` and `NE = (-2, 3)`
  (`exampleSquare_corners`).
* For the identity function of `ℝ` over `ℚ`, its Mayer–Vietoris sequence is exact at the three
  places (`exampleSquare_exact`).
* Increasing `b` from `1` to `2` is a morphism of squares to `exampleSquare'`
  (`exampleSquare_hom`), and the connecting map is natural for it
  (`exampleSquare_intervalMVδ_naturality`).
* For `g x = x + 1/2`, the bound `|x - g x| ≤ 1/2` holds, the thickened square is the endpoint
  square of `(3/2, 3/2)` and `(5/2, 7/2)` (`exampleSquare_thickenEndpoints`), and the connecting
  map commutes with E2's witness `φ` (`exampleSquare_intervalMVδ_comp_interleaving_φ`).
-/

namespace TDA.Reeb.Examples.IntervalMayerVietoris

open CategoryTheory Limits TDA.Reeb TDA.Reeb.OpenInterval
open scoped NNReal

noncomputable section

/-- The endpoint square of `(a, b) = (1, 1)` and `(a', b') = (2, 3)`. -/
def exampleSquare : IntervalMVSquare :=
  IntervalMVSquare.ofEndpoints 1 1 2 3 (by norm_num) (by norm_num) (by norm_num)

/-- The endpoint square of `(a, b) = (1, 2)` and `(a', b') = (2, 3)`. -/
def exampleSquare' : IntervalMVSquare :=
  IntervalMVSquare.ofEndpoints 1 2 2 3 (by norm_num) (by norm_num) (by norm_num)

/-- The corners of `exampleSquare`. -/
theorem exampleSquare_corners :
    exampleSquare.sw = ioo (-1) 1 ∧ exampleSquare.left = ioo (-2) 1 ∧
      exampleSquare.right = ioo (-1) 3 ∧ exampleSquare.ne = ioo (-2) 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The Mayer–Vietoris sequence of `exampleSquare`** for the identity function of `ℝ`, over
`ℚ`, is exact at `H_n((-1, 1))`, at `H_n((-2, 1)) ⊞ H_n((-1, 3))` and at `H_{n+1}((-2, 3))`. -/
theorem exampleSquare_exact (n : ℕ) :
    (ShortComplex.mk _ _
        (intervalMVδ_comp_intervalMVInterMap (ContinuousMap.id ℝ) exampleSquare ℚ n)).Exact ∧
      (ShortComplex.mk _ _
        (intervalMVInterMap_comp_intervalMVSumMap (ContinuousMap.id ℝ) exampleSquare ℚ n)).Exact ∧
      (ShortComplex.mk _ _
        (intervalMVSumMap_comp_intervalMVδ (ContinuousMap.id ℝ) exampleSquare ℚ n)).Exact :=
  ⟨intervalMV_exact_inter _ _ _ n, intervalMV_exact_sum _ _ _ n, intervalMV_exact_ne _ _ _ n⟩

/-- Increasing `b` from `1` to `2` is a morphism of squares. -/
theorem exampleSquare_hom : IntervalMVSquare.Hom exampleSquare exampleSquare' :=
  IntervalMVSquare.hom_ofEndpoints _ _ _ _ _ _ le_rfl (by norm_num) le_rfl le_rfl

/-- **Naturality in `(a, b)`.** The connecting map of `exampleSquare` commutes with the maps of
`intervalSingularHomology` induced by the inclusions into `exampleSquare'`. -/
theorem exampleSquare_intervalMVδ_naturality (n : ℕ) :
    intervalMVδ (ContinuousMap.id ℝ) exampleSquare ℚ n ≫
        (intervalSingularHomology ℚ n (ContinuousMap.id ℝ)).map (homOfLE exampleSquare_hom.sw) =
      (intervalSingularHomology ℚ (n + 1) (ContinuousMap.id ℝ)).map
          (homOfLE exampleSquare_hom.ne) ≫
        intervalMVδ (ContinuousMap.id ℝ) exampleSquare' ℚ n :=
  intervalMVδ_naturality ℚ n _ exampleSquare_hom

/-- The shifted function `x ↦ x + 1/2`. -/
def shiftHalf : C(ℝ, ℝ) := ⟨fun x => x + 1 / 2, by fun_prop⟩

/-- The identity and `shiftHalf` differ by at most `1/2`. -/
theorem abs_sub_shiftHalf_le (x : ℝ) :
    |ContinuousMap.id ℝ x - shiftHalf x| ≤ ((1 / 2 : ℝ≥0) : ℝ) := by
  simp [shiftHalf]

/-- The thickening of `exampleSquare` by `1/2` is the endpoint square of `(3/2, 3/2)` and
`(5/2, 7/2)`. -/
theorem exampleSquare_thickenEndpoints :
    IntervalMVSquare.thickenEndpoints 1 1 2 3 (by norm_num) (by norm_num) (by norm_num)
        (1 / 2) =
      IntervalMVSquare.ofEndpoints (3 / 2) (3 / 2) (5 / 2) (7 / 2) (by norm_num) (by norm_num)
        (by norm_num) := by
  rw [IntervalMVSquare.thickenEndpoints_eq]
  congr 1 <;> push_cast <;> norm_num

/-- **Compatibility with the thickening witness.** The connecting map of `exampleSquare` for the
identity commutes with the witness `φ` of the `1/2`-interleaving of the identity and
`shiftHalf`. -/
theorem exampleSquare_intervalMVδ_comp_interleaving_φ (n : ℕ) :
    intervalMVδ (ContinuousMap.id ℝ) exampleSquare ℚ n ≫
        (intervalSingularHomologyInterleaving (k := ℚ) (n := n) abs_sub_shiftHalf_le).φ.app
          (intervalAB 1 1) =
      (intervalSingularHomologyInterleaving (k := ℚ) (n := n + 1) abs_sub_shiftHalf_le).φ.app
          (intervalAB 2 3) ≫
        intervalMVδ shiftHalf
          (IntervalMVSquare.thickenEndpoints 1 1 2 3 (by norm_num) (by norm_num) (by norm_num)
            (1 / 2)) ℚ n :=
  intervalMVδ_comp_interleaving_φ ℚ n abs_sub_shiftHalf_le 1 1 2 3 _ _ _

end

end TDA.Reeb.Examples.IntervalMayerVietoris
