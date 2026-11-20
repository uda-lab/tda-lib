import TDA.Persistence.Enclosure.Gram

/-!
# Executed enclosures of Gaussian Gram sums and squared RKHS distances

Each interval fixture states the complete value of `gramEnclosure?` or `sqDistEnclosure?`.
Unless stated otherwise the bandwidth is `1`, the cap is `1` and the tolerance is `1 / 100`.

* `weights`, `exponents`, `terms`: executed weights, total weights, Gaussian exponents and
  two terms, one of them skipped for a zero weight.
* `gram_cross`, `gram_self`, `gram_cross_fine`, `gram_cross_refines`, `gram_permuted`: the
  Gram sums of a two-bar and a one-bar list, at two tolerances, and of a permuted list.
* `gram_repeated`, `gram_empty`, `gram_negative`, `gram_separated`, `gram_tiny_bandwidth`,
  `gram_larger`: repeated atoms, empty and weightless lists, negative coordinates, separated
  points, the bandwidth `1 / 1000`, and six terms with cap `3`.
* `sqDist_cross`, `sqDist_cross_fine`, `sqDist_cross_refines`, `sqDist_identical`,
  `sqDist_empty`, `sqDist_repeated`, `sqDist_negative`, `sqDist_separated`,
  `sqDist_tiny_bandwidth`: the same cases for the squared distance.
* `rejected`: nonpositive bandwidth, cap and tolerance.
* `linearKernel_bounds`, `linearKernel_bounds_one`, `gram_width`, `linearKernel_weightless`,
  `sqDist_bounds`, `sqDist_identical_bound`, `diagram_sqDist_bounds`: consumers of the
  containment and width theorems at executed intervals, for the library `linearKernel`, the
  RKHS norm of `embedding` and of `diagramEmbedding`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Enclosure.GramExamples

open TDA.Persistence.Enclosure TDA.Persistence.WeightedKernel
open scoped InnerProductSpace

/-- Two bars: persistence `1` and persistence `2`, capped at `1`. -/
def pair : List (ℚ × ℚ) := [(0, 1), (1, 3)]

/-- One bar. -/
def single : List (ℚ × ℚ) := [(0, 2)]

/-- A diagonal pair and a reversed pair: both have weight zero. -/
def weightless : List (ℚ × ℚ) := [(1, 1), (3, 2)]

/-- Bars with negative coordinates. -/
def negative : List (ℚ × ℚ) := [(-3, -1), (-1 / 2, 1 / 2)]

/-! ## Weights and exponents -/

theorem weights :
    (pointWeight 1 (0, 1), pointWeight 1 (1, 3), pointWeight 1 (1, 1), pointWeight 1 (3, 2),
      pointWeight (1 / 2) (0, 2), totalWeight 1 pair, totalWeight 1 weightless) =
      (1, 1, 0, 0, 1 / 2, 2, 0) := by
  decide +kernel

theorem exponents :
    (gaussExponent 1 (0, 1) (0, 2), gaussExponent 1 (1, 3) (0, 2),
      gaussExponent (1 / 10) (0, 1) (1 / 2, 2), gaussExponent 1 (-3, -1) (-2, 1)) =
      (-1 / 2, -1, -125 / 2, -5 / 2) := by
  decide +kernel

/-- One term, and one term skipped because a weight is zero. -/
theorem terms :
    gramTerm 1 1 (1 / 100) (0, 1) (0, 2) = (155 / 256, 623 / 1024) ∧
      gramTerm 1 1 (1 / 100) (1, 1) (0, 2) = (0, 0) := by
  decide +kernel

/-! ## Gram sums -/

theorem gram_cross :
    gramEnclosure? 1 1 (1 / 100) pair single = some (1993 / 2048, 1999 / 2048) := by
  decide +kernel

theorem gram_self : gramEnclosure? 1 1 (1 / 100) pair pair = some (17723 / 8192, 8865 / 4096) := by
  decide +kernel

/-- Precision refinement. -/
theorem gram_cross_fine :
    gramEnclosure? 1 1 (1 / 10 ^ 6) pair single = some (8173943 / 8388608, 4086973 / 4194304) := by
  decide +kernel

/-- The interval at tolerance `1 / 10 ^ 6` lies inside the one at `1 / 100`. -/
theorem gram_cross_refines :
    (gramEnclosure 1 1 (1 / 100) pair single).1 ≤ (gramEnclosure 1 1 (1 / 10 ^ 6) pair single).1 ∧
      (gramEnclosure 1 1 (1 / 10 ^ 6) pair single).2 ≤
        (gramEnclosure 1 1 (1 / 100) pair single).2 := by
  decide +kernel

/-- A permuted list gives the same interval: the sums are exact. -/
theorem gram_permuted :
    gramEnclosure? 1 1 (1 / 100) pair.reverse single = some (1993 / 2048, 1999 / 2048) := by
  decide +kernel

/-- Repeated atoms are summed: the value is exactly `2`, and the interval contains it. -/
theorem gram_repeated :
    gramEnclosure? 1 1 (1 / 100) [(0, 2), (0, 2)] single = some (2047 / 1024, 2) := by
  decide +kernel

/-- Empty lists and lists of zero total weight give the exact value `0`. -/
theorem gram_empty :
    gramEnclosure? 1 1 (1 / 100) [] pair = some (0, 0) ∧
      gramEnclosure? 1 1 (1 / 100) [] [] = some (0, 0) ∧
      gramEnclosure? 1 1 (1 / 100) weightless pair = some (0, 0) := by
  decide +kernel

/-- Negative coordinates, cap `2`. -/
theorem gram_negative :
    gramEnclosure? 1 2 (1 / 100) negative [(-2, 1)] = some (1845 / 2048, 7387 / 8192) := by
  decide +kernel

/-- Separated points. -/
theorem gram_separated :
    gramEnclosure? 1 1 (1 / 100) [(0, 1)] [(10, 12)] = some (0, 1 / 2 ^ 17) := by
  decide +kernel

/-- A tiny bandwidth: points at distance `1` and points at distance `1 / 1000`. -/
theorem gram_tiny_bandwidth :
    gramEnclosure? (1 / 1000) 1 (1 / 100) [(0, 1)] [(0, 2)] = some (0, 1 / 2 ^ 29) ∧
      gramEnclosure? (1 / 1000) 1 (1 / 100) [(0, 1)] [(0, 1001 / 1000)] =
        some (155 / 256, 623 / 1024) := by
  decide +kernel

/-- Three and two bars with cap `3`: six terms, total weights `6` and `5`. -/
theorem gram_larger :
    gramEnclosure? 1 3 (1 / 100) [(0, 1), (1, 3), (2, 7)] [(0, 2), (1, 5)] =
      some (1110281 / 262144, 2221147 / 524288) := by
  decide +kernel

/-! ## Squared distances -/

theorem sqDist_cross :
    sqDistEnclosure? 1 1 (1 / 100) pair single = some (19895 / 16384, 39853 / 32768) := by
  decide +kernel

theorem sqDist_cross_fine :
    sqDistEnclosure? 1 1 (1 / 10 ^ 6) pair single =
      some (326242939 / 268435456, 163121501 / 134217728) := by
  decide +kernel

/-- The interval at tolerance `1 / 10 ^ 6` lies inside the one at `1 / 100`. -/
theorem sqDist_cross_refines :
    (sqDistEnclosure 1 1 (1 / 100) pair single).1 ≤
        (sqDistEnclosure 1 1 (1 / 10 ^ 6) pair single).1 ∧
      (sqDistEnclosure 1 1 (1 / 10 ^ 6) pair single).2 ≤
        (sqDistEnclosure 1 1 (1 / 100) pair single).2 := by
  decide +kernel

/-- Identical and permuted lists: the value is `0`, and the lower endpoint is `0`. -/
theorem sqDist_identical :
    sqDistEnclosure? 1 1 (1 / 100) pair pair = some (0, 7 / 16384) ∧
      sqDistEnclosure? 1 1 (1 / 100) pair pair.reverse = some (0, 7 / 16384) := by
  decide +kernel

theorem sqDist_empty :
    sqDistEnclosure? 1 1 (1 / 100) [] [] = some (0, 0) ∧
      sqDistEnclosure? 1 1 (1 / 100) weightless [(2, 2)] = some (0, 0) ∧
      sqDistEnclosure? 1 1 (1 / 100) [] pair = some (35455 / 16384, 70917 / 32768) := by
  decide +kernel

theorem sqDist_repeated :
    sqDistEnclosure? 1 1 (1 / 100) [(0, 2), (0, 2)] single = some (2047 / 2048, 2049 / 2048) := by
  decide +kernel

theorem sqDist_negative :
    sqDistEnclosure? 1 2 (1 / 100) negative [(-2, 1)] = some (118845 / 16384, 29715 / 4096) := by
  decide +kernel

theorem sqDist_separated :
    sqDistEnclosure? 1 1 (1 / 100) [(0, 1)] [(10, 12)] = some (524159 / 262144, 2) := by
  decide +kernel

theorem sqDist_tiny_bandwidth :
    sqDistEnclosure? (1 / 1000) 1 (1 / 100) [(0, 1)] [(0, 2)] =
        some (2146959359 / 1073741824, 2) ∧
      sqDistEnclosure? (1 / 1000) 1 (1 / 100) [(0, 1)] [(0, 1001 / 1000)] =
        some (1609 / 2048, 1613 / 2048) := by
  decide +kernel

/-! ## Rejected requests -/

theorem rejected :
    gramEnclosure? 0 1 (1 / 100) pair single = none ∧
      gramEnclosure? (-1) 1 (1 / 100) pair single = none ∧
      gramEnclosure? 1 0 (1 / 100) pair single = none ∧
      gramEnclosure? 1 (-1) (1 / 100) pair single = none ∧
      gramEnclosure? 1 1 0 pair single = none ∧
      gramEnclosure? 1 1 (-1 / 100) pair single = none ∧
      sqDistEnclosure? 0 1 (1 / 100) pair single = none ∧
      sqDistEnclosure? 1 0 (1 / 100) pair single = none ∧
      sqDistEnclosure? 1 1 0 pair single = none := by
  decide +kernel

/-! ## Consumers: the actual kernel sum, the actual RKHS distance and diagrams -/

/-- Bounds for the library linear kernel of the two occurrence families, at the real
bandwidth `((1 : ℚ) : ℝ)` and the weight with cap `1`. -/
theorem linearKernel_bounds :
    (1993 / 2048 : ℝ) ≤ linearKernel ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one)
        (realPoints pair) (realPoints single) ∧
      linearKernel ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints pair)
        (realPoints single) ≤ 1999 / 2048 := by
  have h := (gramEnclosure?_spec zero_le_one gram_cross).1
  exact ⟨le_trans (by norm_num) h.1, h.2.trans (by norm_num)⟩

/-- The same bounds with the bandwidth written as the real number `1`. -/
theorem linearKernel_bounds_one :
    (1993 / 2048 : ℝ) ≤
        linearKernel 1 (capWeight 1 zero_le_one) (realPoints pair) (realPoints single) ∧
      linearKernel 1 (capWeight 1 zero_le_one) (realPoints pair) (realPoints single) ≤
        1999 / 2048 := by
  simpa using linearKernel_bounds

/-- The width bound of the theorem at an executed interval. -/
theorem gram_width : (1999 / 2048 - 1993 / 2048 : ℚ) ≤ 1 / 100 :=
  (gramEnclosure?_spec zero_le_one gram_cross).2

/-- Weightless occurrences: the library linear kernel is exactly `0`. -/
theorem linearKernel_weightless :
    linearKernel ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints weightless)
      (realPoints pair) = 0 := by
  have h := (gramEnclosure?_spec zero_le_one gram_empty.2.2).1
  exact le_antisymm (h.2.trans (by norm_num)) (le_trans (by norm_num) h.1)

/-- Bounds for the squared RKHS distance of the two embeddings, which are therefore
distinct. -/
theorem sqDist_bounds :
    (19895 / 16384 : ℝ) ≤ ‖embedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints pair) -
        embedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints single)‖ ^ 2 ∧
      ‖embedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints pair) -
        embedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints single)‖ ^ 2 ≤
          39853 / 32768 ∧
      embedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints pair) ≠
        embedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints single) := by
  have h := (sqDistEnclosure?_spec zero_le_one sqDist_cross).1
  have h1 : (19895 / 16384 : ℝ) ≤ _ := le_trans (by norm_num) h.1
  refine ⟨h1, h.2.trans (by norm_num), fun e => ?_⟩
  rw [e, sub_self, norm_zero] at h1
  norm_num at h1

/-- Identical lists: the squared distance is at most the upper endpoint, with no assumption
that it vanishes. -/
theorem sqDist_identical_bound :
    ‖embedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints pair) -
      embedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) (realPoints pair.reverse)‖ ^ 2 ≤
        7 / 16384 :=
  ((sqDistEnclosure?_spec zero_le_one sqDist_identical.2).1.2).trans (by norm_num)

/-- The diagram with the finite bars of `pair` and one essential bar. -/
def pairDiagram : Diagram ℝ where
  points := {((0 : ℝ), ((1 : ℝ) : WithTop ℝ)), (1, ((3 : ℝ) : WithTop ℝ)), (0, ⊤)}
  offDiagonal := by simp

/-- The diagram with the one bar of `single`. -/
def singleDiagram : Diagram ℝ where
  points := {((0 : ℝ), ((2 : ℝ) : WithTop ℝ))}
  offDiagonal := by simp

theorem pairDiagram_finitePart :
    finitePart pairDiagram.points = ((pair.map realPoint : List (ℝ × ℝ)) : Multiset (ℝ × ℝ)) := by
  have h : finitePart pairDiagram.points = {((0 : ℝ), (1 : ℝ)), (1, 3)} := rfl
  rw [h]
  simp [pair, realPoint]
  rfl

theorem singleDiagram_finitePart :
    finitePart singleDiagram.points =
      ((single.map realPoint : List (ℝ × ℝ)) : Multiset (ℝ × ℝ)) := by
  have h : finitePart singleDiagram.points = {((0 : ℝ), (2 : ℝ))} := rfl
  rw [h]
  simp [single, realPoint]

/-- The squared RKHS distance of the two diagram embeddings; the essential bar plays no
role. -/
theorem diagram_sqDist_bounds :
    (19895 / 16384 : ℝ) ≤
        ‖diagramEmbedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) pairDiagram -
          diagramEmbedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) singleDiagram‖ ^ 2 ∧
      ‖diagramEmbedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) pairDiagram -
          diagramEmbedding ((1 : ℚ) : ℝ) (capWeight 1 zero_le_one) singleDiagram‖ ^ 2 ≤
        39853 / 32768 := by
  rw [diagramEmbedding_eq_embedding_realPoints _ _ _ _ pairDiagram_finitePart,
    diagramEmbedding_eq_embedding_realPoints _ _ _ _ singleDiagram_finitePart]
  exact ⟨sqDist_bounds.1, sqDist_bounds.2.1⟩

end TDA.Persistence.Enclosure.GramExamples
