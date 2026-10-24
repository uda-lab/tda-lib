import TDA.Reeb.IntervalScaling
import TDA.Reeb.RGraphTranslation
import TDA.Mapper.GraphPLReebMergeHeight

/-!
# Scaling graph-PL Reeb distances

For any simple graph and real vertex heights, `plHeight_smul` identifies scaling the vertex
heights with scaling the continuous PL height. For finite graphs, possibly different, a common
nonzero multiplier scales the geometric interleaving distance of their Reeb quotients by its
absolute value. Reflection preserves this distance, and a common affine change has the same
homogeneity law.

`splitHeights a M` reflects the merge heights `(0, 0, a, M)`. For `0 < a < b ≤ 2a` and `b ≤ M`
the split-tree distance is `b - a`. For all `0 < a < b ≤ M`, the merge-tree and split-tree
distances are at least `min (b - a) (b / 2)`. When `2a < b`, they lie between `b / 2` and
`b - a`; neither endpoint is asserted to be the exact value.

These are library specializations of interval-precosheaf scaling and the component-count
obstruction. De Silva–Munch–Patel, Definition 4.4 and Theorem 4.6(i), supply the distance and
perturbation-bound context. No scaling functor on graph objects, comparison map between graphs,
or scaling of Mapper covers or persistence modules is constructed.
-/

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.RGraph TDA.Reeb.OpenInterval
open scoped NNReal ENNReal

namespace TDA.Reeb.GraphPL

/-- Scaling all vertex heights scales the continuous piecewise-linear height. -/
theorem plHeight_smul {V : Type*} (G : SimpleGraph V) (h : V → ℝ) (s : ℝ) :
    plHeight G (fun v => s * h v) = s • plHeight G h :=
  (plHeight_unique G _ _ (fun v => by simp) fun d t => by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, plHeight_edgePoint, dartHeight]
    ring).symm

end TDA.Reeb.GraphPL

namespace TDA.Mapper.GraphPL

/-- A common nonzero scale multiplies the distance, also across different finite graphs. -/
theorem geometricInterleavingDistance_graphPLReebGraph_smul {V V' : Type}
    [Finite V] [Finite V'] (G : SimpleGraph V) (h : V → ℝ) (G' : SimpleGraph V') (h' : V' → ℝ)
    {s : ℝ} (hs : s ≠ 0) :
    geometricInterleavingDistance (graphPLReebGraph G (fun v => s * h v))
      (graphPLReebGraph G' (fun v => s * h' v)) =
      ENNReal.ofReal |s| * geometricInterleavingDistance (graphPLReebGraph G h)
        (graphPLReebGraph G' h') := by
  rw [geometricInterleavingDistance_graphPLReebGraph,
    geometricInterleavingDistance_graphPLReebGraph, plHeight_smul, plHeight_smul,
    interleavingDistance_intervalComponents_smul hs]
  exact congrArg (fun r : ℝ≥0∞ => r * _) (Real.enorm_eq_ofReal_abs s)

/-- Reflection of both height functions preserves the distance. -/
theorem geometricInterleavingDistance_graphPLReebGraph_neg {V V' : Type}
    [Finite V] [Finite V'] (G : SimpleGraph V) (h : V → ℝ) (G' : SimpleGraph V') (h' : V' → ℝ) :
    geometricInterleavingDistance (graphPLReebGraph G (fun v => -h v))
      (graphPLReebGraph G' (fun v => -h' v)) =
      geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G' h') := by
  simpa using geometricInterleavingDistance_graphPLReebGraph_smul G h G' h'
    (by norm_num : (-1 : ℝ) ≠ 0)

/-- A common affine change with nonzero slope multiplies the distance by its absolute slope. -/
theorem geometricInterleavingDistance_graphPLReebGraph_affine {V V' : Type}
    [Finite V] [Finite V'] (G : SimpleGraph V) (h : V → ℝ) (G' : SimpleGraph V') (h' : V' → ℝ)
    {s : ℝ} (hs : s ≠ 0) (c : ℝ) :
    geometricInterleavingDistance (graphPLReebGraph G (fun v => s * h v + c))
      (graphPLReebGraph G' (fun v => s * h' v + c)) =
      ENNReal.ofReal |s| * geometricInterleavingDistance (graphPLReebGraph G h)
        (graphPLReebGraph G' h') := by
  rw [geometricInterleavingDistance_graphPLReebGraph, plHeight_add_const, plHeight_add_const,
    intervalComponents_add_const, intervalComponents_add_const, interleavingDistance_translatePre,
    ← geometricInterleavingDistance_graphPLReebGraph]
  exact geometricInterleavingDistance_graphPLReebGraph_smul G h G' h' hs

/-- The reflected merge tree, with two leaves at `0`, branch height `-a` and bottom height `-M`. -/
def splitHeights (a M : ℝ) : Fin 4 → ℝ := fun v => -mergeHeights a M v

/-- The split-tree branch-height distance in the exact merge-height range. -/
theorem geometricInterleavingDistance_splitY {a b M : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b ≤ 2 * a) (hbM : b ≤ M) :
    geometricInterleavingDistance (graphPLReebGraph mergeY (splitHeights a M))
      (graphPLReebGraph mergeY (splitHeights b M)) = ENNReal.ofReal (b - a) := by
  unfold splitHeights
  rw [geometricInterleavingDistance_graphPLReebGraph_neg]
  exact geometricInterleavingDistance_mergeY ha hab hb hbM

/-- The component-count obstruction below both the apex displacement and half the higher apex. -/
theorem ofReal_min_le_geometricInterleavingDistance_mergeY {a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hbM : b ≤ M) :
    ENNReal.ofReal (min (b - a) (b / 2)) ≤
      geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
        (graphPLReebGraph mergeY (mergeHeights b M)) := by
  rw [geometricInterleavingDistance_graphPLReebGraph,
    interleavingDistance_congr (intervalComponentsIso _ _) (intervalComponentsIso _ _)]
  refine le_interleavingDistance_of_forall_exists_card_lt_symm fun ε hε => ?_
  rw [← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_lt_ofReal_iff (by apply lt_min <;> linarith)] at hε
  obtain ⟨hεa, hεb⟩ := lt_min_iff.1 hε
  have hc : 0 < b - 2 * ε := by linarith
  have hthick (x : ℝ) : x ∈ thicken ε (ioo 0 (b - 2 * ε)) ↔ -ε < x ∧ x < b - ε := by
    rw [thicken_ioo hc, mem_ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hthick₂ (x : ℝ) (hx : x ∈ thicken ε (thicken ε (ioo 0 (b - 2 * ε)))) : x < b := by
    rw [thicken_ioo hc, thicken_ioo (by linarith), mem_ioo] at hx
    linarith [hx.2]
  refine ⟨ioo 0 (b - 2 * ε),
    injective_cellComponentFunctor_mergeHeights_map hc hbM _ hthick₂,
    by change Finite (cellGraph _ _ _).ConnectedComponent; infer_instance, ?_⟩
  change Nat.card (cellGraph mergeY (mergeHeights a M) _).ConnectedComponent <
    Nat.card (cellGraph mergeY (mergeHeights b M) _).ConnectedComponent
  have hε₀ : (0 : ℝ) ≤ ε := ε.coe_nonneg
  rw [card_cellComponents_mergeHeights_eq_one ((hthick a).2 ⟨by linarith, by linarith⟩),
    card_cellComponents_mergeHeights_ioo hc (by linarith) hbM]
  decide

/-- Beyond `b = 2a`, the merge-height distance lies in `[b/2, b-a]`. -/
theorem geometricInterleavingDistance_mergeY_bounds {a b M : ℝ}
    (ha : 0 < a) (hb : 2 * a < b) (hbM : b ≤ M) :
    ENNReal.ofReal (b / 2) ≤
        geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
          (graphPLReebGraph mergeY (mergeHeights b M)) ∧
      geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
          (graphPLReebGraph mergeY (mergeHeights b M)) ≤ ENNReal.ofReal (b - a) := by
  have hab : a < b := by linarith
  refine ⟨?_, ?_⟩
  · simpa only [min_eq_right (by linarith : b / 2 ≤ b - a)] using
      ofReal_min_le_geometricInterleavingDistance_mergeY ha hab hbM
  · rw [← edist_mergeHeights hab.le]
    exact geometricInterleavingDistance_graphPLReebGraph_le_edist mergeY _ _

/-- Reflection gives the same component-count lower bound for the split tree. -/
theorem ofReal_min_le_geometricInterleavingDistance_splitY {a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hbM : b ≤ M) :
    ENNReal.ofReal (min (b - a) (b / 2)) ≤
      geometricInterleavingDistance (graphPLReebGraph mergeY (splitHeights a M))
        (graphPLReebGraph mergeY (splitHeights b M)) := by
  unfold splitHeights
  rw [geometricInterleavingDistance_graphPLReebGraph_neg]
  exact ofReal_min_le_geometricInterleavingDistance_mergeY ha hab hbM

/-- Beyond `b = 2a`, the split-height distance lies in `[b/2, b-a]`. -/
theorem geometricInterleavingDistance_splitY_bounds {a b M : ℝ}
    (ha : 0 < a) (hb : 2 * a < b) (hbM : b ≤ M) :
    ENNReal.ofReal (b / 2) ≤
        geometricInterleavingDistance (graphPLReebGraph mergeY (splitHeights a M))
          (graphPLReebGraph mergeY (splitHeights b M)) ∧
      geometricInterleavingDistance (graphPLReebGraph mergeY (splitHeights a M))
          (graphPLReebGraph mergeY (splitHeights b M)) ≤ ENNReal.ofReal (b - a) := by
  unfold splitHeights
  rw [geometricInterleavingDistance_graphPLReebGraph_neg]
  exact geometricInterleavingDistance_mergeY_bounds ha hb hbM

end TDA.Mapper.GraphPL
