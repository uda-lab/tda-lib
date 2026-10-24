import TDA.Persistence.PersistenceMeasure
import Mathlib.Analysis.BoxIntegral.Partition.Additive
import Mathlib.Tactic

/-!
# Finite box partitions of the module persistence measure

The actual quotient dimensions of a q-tame module give a box-additive map on subboxes of
every rectangle strictly above the diagonal. Mathlib upgrades the two proved coordinate
split identities to arbitrary finite partitions. The total box function is zero outside
the separated region; no measure property across the diagonal is asserted.
-/

universe u w

namespace TDA.Persistence.RectangleMeasure

open BoxIntegral Set

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- The module rectangle value on separated two-dimensional boxes, zero elsewhere. -/
noncomputable def persistenceBoxValue (I : Box (Fin 2)) : ℕ :=
  if h : I.upper 0 < I.lower 1 then
    persistenceMeasureValue M (I.lower_lt_upper 0).le h.le (I.lower_lt_upper 1).le
  else 0

/-- The box function is the actual image-and-kernel quotient dimension above the diagonal. -/
theorem persistenceBoxValue_of_separated (I : Box (Fin 2)) (hI : I.upper 0 < I.lower 1) :
    persistenceBoxValue M I =
      persistenceMeasureValue M (I.lower_lt_upper 0).le hI.le (I.lower_lt_upper 1).le := by
  simp only [persistenceBoxValue, dif_pos hI]

/-- Q-tameness and the proved quotient split laws imply additivity on every finite partition
of every subbox of a separated outer rectangle. -/
noncomputable def persistenceBoxAdditiveMap (hM : M.QTame) (I : Box (Fin 2))
    (hI : I.upper 0 < I.lower 1) : BoxAdditiveMap (Fin 2) ℕ I :=
  BoxAdditiveMap.ofMapSplitAdd (persistenceBoxValue M) I (by
    intro J hJ i x hx
    have hbounds := Box.le_iff_bounds.mp (WithTop.coe_le_coe.mp hJ)
    have hsep : J.upper 0 < J.lower 1 :=
      (hbounds.2 0).trans_lt (hI.trans_le (hbounds.1 1))
    let : FiniteDimensional k (persistenceImage M hsep.le) := hM _ _ hsep
    fin_cases i
    · simp only [Box.splitLower_def hx, Box.splitUpper_def hx,
        ← WithBot.some_eq_coe, Option.elim']
      have hleft : x < J.lower 1 := hx.2.trans hsep
      simpa [persistenceBoxValue, hleft, hsep] using
        (persistenceMeasureValue_split_birth M hx.1.le hx.2.le hsep.le
          (J.lower_lt_upper 1).le).symm
    · simp only [Box.splitLower_def hx, Box.splitUpper_def hx,
        ← WithBot.some_eq_coe, Option.elim']
      have hright : J.upper 0 < x := hsep.trans hx.1
      simpa [persistenceBoxValue, hright, hsep] using
        (persistenceMeasureValue_split_death M (J.lower_lt_upper 0).le hsep.le
          hx.1.le hx.2.le).symm)

/-- The bundled box-additive map retains the module's actual rectangle values. -/
theorem persistenceBoxAdditiveMap_apply (hM : M.QTame) (I : Box (Fin 2))
    (hI : I.upper 0 < I.lower 1) (J : Box (Fin 2)) :
    persistenceBoxAdditiveMap M hM I hI J = persistenceBoxValue M J := rfl

/-- Arbitrary finite box tilings of a separated rectangle preserve its persistence count. -/
theorem persistenceBoxValue_sum_partition (hM : M.QTame) (I : Box (Fin 2))
    (hI : I.upper 0 < I.lower 1) (π : Prepartition I) (hπ : π.IsPartition) :
    ∑ J ∈ π.boxes, persistenceBoxValue M J = persistenceBoxValue M I :=
  (persistenceBoxAdditiveMap M hM I hI).sum_partition_boxes le_rfl hπ

end TDA.Persistence.RectangleMeasure
