import TDA.Sheaf.BandIntervalConvolution
import TDA.Sheaf.RealIntervalSectionsExamples

/-!
# Threshold augmentation over the rationals

At radius one the convolution of the open interval `(0, 2)` is the midpoint sheaf
in degree one. Its augmentation is nonzero, represents an `Ext¹` class, and
induces zero on every cohomology sheaf.
-/

noncomputable section

open CategoryTheory DerivedCategory TDA.Persistence TDA.Sheaf TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.BandConvolution TDA.Sheaf.RealConstructible TDA.Sheaf.RealStratification
open TDA.Sheaf.RealIntervalSectionsExamples (Joo)

attribute [local instance] HasDerivedCategory.standard hasExt_sheaf_realLine

private def breaks : Fin 2 → ℝ := ![0, 2]

private theorem strictMono_breaks : StrictMono breaks := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  norm_num [breaks]

private theorem open_interval : intervalSet breaks Joo = Set.Ioo 0 2 := by
  rw [intervalSet_eq_Ioo strictMono_breaks (i := 0) (j := 1) rfl rfl]
  simp [breaks]

local notation "F" => Functor.obj (extension ℚ strictMono_breaks) (interval (orient 2) Joo)

example :=
  aug_interval_Ioo_threshold_ne_zero (k := ℚ) strictMono_breaks Joo
    (ε := 1) zero_le_one (a := 0) (b := 2) (by norm_num) (by norm_num) open_interval

example (i : ℤ) :=
  homologyFunctor_map_aug_interval_Ioo_threshold (k := ℚ) strictMono_breaks Joo
    (ε := 1) zero_le_one (a := 0) (b := 2) (by norm_num) (by norm_num) open_interval i

example :
    ∃ K : FiniteInterval (2 * (bandBreakpoints breaks 1).card + 1),
      intervalSet (sortedBreakpoints (bandBreakpoints breaks 1)) K = {1} ∧
      ∃ ξ : Abelian.Ext
          ((extension ℚ (strictMono_sortedBreakpoints (bandBreakpoints breaks 1))).obj
            (interval _ K)) F 1, ξ ≠ 0 := by
  obtain ⟨K, hK, _, ξ, hξ, _⟩ :=
    exists_ext_one_aug_interval_Ioo_threshold (k := ℚ) strictMono_breaks Joo
      (ε := 1) zero_le_one (a := 0) (b := 2) (by norm_num) (by norm_num) open_interval
  exact ⟨K, by simpa using hK, ξ, hξ⟩
