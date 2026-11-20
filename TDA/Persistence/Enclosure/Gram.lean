import TDA.Persistence.Enclosure.Exp
import TDA.Persistence.WeightedKernel

/-!
# Rational enclosures of Gaussian Gram sums and of the squared RKHS distance

The input is two lists `x`, `y` of rational birth–death pairs, a rational bandwidth `σ`, a
rational cap `c` and a rational tolerance `δ`. The weight is `capWeight c`, the function
`u ↦ min c (max 0 u.2)` of birth–persistence coordinates, a `PersistenceImage.Weight 1 c`.

* `gramEnclosure σ c δ x y` is a pair of rational numbers. For `0 ≤ c` it encloses the library
  value `WeightedKernel.linearKernel σ (capWeight c) (realPoints x) (realPoints y)`
  (`gramEnclosure_mem`), and for `0 < δ` its width is at most `δ` (`gramEnclosure_width`).
* `sqDistEnclosure σ c δ x y` does the same for the squared RKHS distance
  `‖embedding σ w (realPoints x) - embedding σ w (realPoints y)‖ ^ 2` of the two weighted
  kernel embeddings (`sqDistEnclosure_mem`, `sqDistEnclosure_width`).
* `gramEnclosure?` and `sqDistEnclosure?` return these pairs when `0 < σ`, `0 < c` and
  `0 < δ`, and `none` otherwise.
* `diagramEmbedding_eq_embedding_realPoints` transfers the statements to
  `WeightedKernel.diagramEmbedding` of a diagram whose finite part is listed by `x`.

`realPoints x` is the occurrence family indexed by the positions of `x`: repeated pairs are
repeated occurrences, and no pair is removed.

## Algorithm

1. `pointWeight c (b, d) = min c (max 0 (d - b))` is the exact rational weight of a pair; its
   cast is the library weight of the real point (`capWeight_realPoint`). Pairs with `d ≤ b`
   have weight `0`.
2. `gaussExponent σ p q = -((b₁ - b₂)² + (d₁ - d₂)²) / (2σ²)` is the exact rational exponent,
   and the library kernel at the two real points is `Real.exp` of it (`kernel_realPoint`).
3. `gramTerm σ c ε p q` multiplies `expEnclosure (gaussExponent σ p q) ε` by the product `w`
   of the two weights. For `w = 0` it is `(0, 0)` and no exponential is computed.
4. `gramSum σ c ε x y` adds the terms over all pairs of positions. Its width is at most
   `ε * (W x * W y)`, where `W = totalWeight c` (`gramSum_width`).
5. `gramEnclosure` uses the scalar tolerance `ε = δ / max 1 (W x * W y)`, so the width is at
   most `δ`. If a total weight is `0`, every term is `(0, 0)` and the result is `(0, 0)`.
6. `sqDistEnclosure` combines the Gram enclosures of `(x, x)`, `(y, y)` and `(x, y)` at
   tolerance `δ / 4` as `K(x, x) + K(y, y) - 2 K(x, y)`, by `norm_embedding_sub_sq`; the three
   widths add up to at most `δ / 4 + δ / 4 + 2 (δ / 4)`. A negative lower endpoint is replaced
   by `0`, which the squared norm never undercuts.

## Cost

The cross Gram sum makes one call of `expEnclosure` for each of the `m n` pairs of positions
with nonzero weights, and the squared distance makes `m² + n² + m n` calls at most; the
symmetry of `K(x, x)` is not used. Each Gram sum has its own scalar tolerance, computed from
its own pair of total weights: `δ / max 1 (W x * W y)` for `gramEnclosure σ c δ x y`, and
`(δ / 4) / max 1 (W x * W x)`, `(δ / 4) / max 1 (W y * W y)` and `(δ / 4) / max 1 (W x * W y)`
for the three Gram sums of `sqDistEnclosure σ c δ x y`. Each call has the cost described in
`TDA.Persistence.Enclosure.Exp`, at the exponent `gaussExponent σ p q` and the scalar tolerance
of its Gram sum: it grows with the logarithm of the squared distance of the two points divided
by `2σ²`, with the number of digits of the scalar tolerance, and with the size of the
denominator of the exponent, which is built from the denominators of the coordinates and of
`σ`. A small bandwidth therefore costs through the halvings of the exponent, and large total
weights cost through the scalar tolerance. The sums are exact rational sums of dyadic numbers
times weights. No bound on the bit complexity is proved; these counts are documented and are
not theorems.

The executable definitions use rational arithmetic and comparison of rational numbers only:
no decision by `Classical` and no real-number comparison. `capWeight`, `realPoint` and
`realPoints` are the noncomputable real objects of the statements and are not on the runtime
path.

## Scope

The widths are absolute. An enclosure decides no equality: for identical lists the squared
distance is `0` and the result is an interval `(0, u)` with `u ≤ δ`. Essential bars are not
part of the input. A list containing a pair with `d = b` is not the finite part of any
`Diagram ℝ`; such pairs have weight `0` in the occurrence family. Pairs with `d < b` also
have weight `0`, and a `Diagram ℝ` may contain them, so the transfer to diagrams covers lists
with such pairs. Gaussian pixel integrals, the `PiLp 1` persistence-image norm and the RKHS
distance itself (a square root) are not enclosed here.

These are elementary library results, not attributed to a source. See
`docs/math/kernel-enclosure.md`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Enclosure

open TDA.Persistence.WeightedKernel
open scoped InnerProductSpace

/-! ## The capped persistence weight -/

/-- The weight `u ↦ min c (max 0 u.2)` in birth–persistence coordinates, for a rational cap
`0 ≤ c`: persistence truncated at `0` below and at `c` above. -/
noncomputable def capWeight (c : ℚ) (hc : 0 ≤ c) : PersistenceImage.Weight 1 (c : ℝ) where
  toFun u := min (c : ℝ) (max 0 u.2)
  nonneg u := le_min (Rat.cast_nonneg.2 hc) (le_max_left _ _)
  bounded u := min_le_left _ _
  lipschitz u v := by
    calc |min (c : ℝ) (max 0 u.2) - min (c : ℝ) (max 0 v.2)|
        ≤ max |(c : ℝ) - c| |max 0 u.2 - max 0 v.2| := abs_min_sub_min_le_max _ _ _ _
      _ = |max 0 u.2 - max 0 v.2| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
      _ ≤ max |(0 : ℝ) - 0| |u.2 - v.2| := abs_max_sub_max_le_max _ _ _ _
      _ = |u.2 - v.2| := by rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
      _ ≤ 1 * ‖u - v‖ := by
        simpa only [one_mul, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
          using le_max_right |u.1 - v.1| |u.2 - v.2|
  zero_persistence b := by simp [hc]

@[simp] theorem capWeight_apply (c : ℚ) (hc : 0 ≤ c) (u : ℝ × ℝ) :
    capWeight c hc u = min (c : ℝ) (max 0 u.2) := rfl

/-! ## Rational points, weights and exponents -/

/-- The real birth–death point of a rational birth–death pair. -/
noncomputable def realPoint (p : ℚ × ℚ) : ℝ × ℝ := (p.1, p.2)

/-- The occurrence family of a list of rational birth–death pairs: one label for each
position of the list, so repeated pairs are repeated occurrences. -/
noncomputable def realPoints (x : List (ℚ × ℚ)) : Fin x.length → ℝ × ℝ :=
  fun i => realPoint x[i]

/-- The weight `min c (max 0 (d - b))` of the rational birth–death pair `(b, d)`. -/
def pointWeight (c : ℚ) (p : ℚ × ℚ) : ℚ := min c (max 0 (p.2 - p.1))

/-- The sum of the weights of the pairs of a list. -/
def totalWeight (c : ℚ) (x : List (ℚ × ℚ)) : ℚ := (x.map (pointWeight c)).sum

/-- The exponent `-((b₁ - b₂)² + (d₁ - d₂)²) / (2σ²)` of the Gaussian kernel at two rational
birth–death pairs. -/
def gaussExponent (σ : ℚ) (p q : ℚ × ℚ) : ℚ :=
  -((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) / (2 * σ ^ 2)

/-- The executed rational weight is the library weight of the real point. -/
theorem capWeight_realPoint (c : ℚ) (hc : 0 ≤ c) (p : ℚ × ℚ) :
    capWeight c hc (birthPersistence (realPoint p)) = (pointWeight c p : ℝ) := by
  simp [birthPersistence, realPoint, pointWeight]

theorem pointWeight_nonneg {c : ℚ} (hc : 0 ≤ c) (p : ℚ × ℚ) : 0 ≤ pointWeight c p :=
  le_min hc (le_max_left _ _)

theorem totalWeight_nonneg {c : ℚ} (hc : 0 ≤ c) (x : List (ℚ × ℚ)) : 0 ≤ totalWeight c x :=
  List.sum_nonneg fun a ha => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
    exact pointWeight_nonneg hc p

theorem gaussExponent_nonpos (σ : ℚ) (p q : ℚ × ℚ) : gaussExponent σ p q ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by positivity)

/-- The library kernel at two real points of rational pairs is the exponential of the executed
rational exponent, for every rational bandwidth. -/
theorem kernel_realPoint (σ : ℚ) (p q : ℚ × ℚ) :
    kernel (σ : ℝ) (realPoint p) (realPoint q) = Real.exp ((gaussExponent σ p q : ℚ) : ℝ) := by
  simp [kernel, realPoint, gaussExponent]

/-! ## The Gram sum -/

/-- One term of the Gram sum at scalar tolerance `ε`: the product `w` of the two weights times
the enclosure of the exponential at the Gaussian exponent, and `(0, 0)` without any
exponential when `w = 0`. -/
def gramTerm (σ c ε : ℚ) (p q : ℚ × ℚ) : ℚ × ℚ :=
  let w := pointWeight c p * pointWeight c q
  if w = 0 then (0, 0)
  else
    let E := expEnclosure (gaussExponent σ p q) ε
    (w * E.1, w * E.2)

/-- The sum of the terms `gramTerm σ c ε p q` over all pairs of positions of the two lists,
lower and upper endpoints separately. -/
def gramSum (σ c ε : ℚ) (x y : List (ℚ × ℚ)) : ℚ × ℚ :=
  (x.map fun p => (y.map fun q => gramTerm σ c ε p q).sum).sum

/-- A rational interval for the linear kernel of the two lists, of width at most `δ` for
`0 ≤ c` and `0 < δ`: the Gram sum at the scalar tolerance `δ / max 1 (W x * W y)`, where
`W` is the total weight. -/
def gramEnclosure (σ c δ : ℚ) (x y : List (ℚ × ℚ)) : ℚ × ℚ :=
  gramSum σ c (δ / max 1 (totalWeight c x * totalWeight c y)) x y

/-- The Gram enclosure for an admissible request: `none` unless `0 < σ`, `0 < c` and
`0 < δ`. -/
def gramEnclosure? (σ c δ : ℚ) (x y : List (ℚ × ℚ)) : Option (ℚ × ℚ) :=
  if 0 < σ ∧ 0 < c ∧ 0 < δ then some (gramEnclosure σ c δ x y) else none

private theorem gramTerm_spec {c : ℚ} (hc : 0 ≤ c) (σ ε : ℚ) (p q : ℚ × ℚ) :
    ((gramTerm σ c ε p q).1 : ℝ) ≤
        capWeight c hc (birthPersistence (realPoint p)) *
          capWeight c hc (birthPersistence (realPoint q)) *
          kernel σ (realPoint p) (realPoint q) ∧
      capWeight c hc (birthPersistence (realPoint p)) *
          capWeight c hc (birthPersistence (realPoint q)) *
          kernel σ (realPoint p) (realPoint q) ≤ ((gramTerm σ c ε p q).2 : ℝ) := by
  rw [capWeight_realPoint, capWeight_realPoint, kernel_realPoint, ← Rat.cast_mul]
  have hw : 0 ≤ pointWeight c p * pointWeight c q :=
    mul_nonneg (pointWeight_nonneg hc p) (pointWeight_nonneg hc q)
  have hwr : (0 : ℝ) ≤ ((pointWeight c p * pointWeight c q : ℚ) : ℝ) := Rat.cast_nonneg.2 hw
  obtain ⟨h1, h2⟩ := expEnclosure_mem (gaussExponent_nonpos σ p q) ε
  simp only [gramTerm]
  split_ifs with h0
  · simp [h0]
  · simp only [Rat.cast_mul] at hwr ⊢
    exact ⟨mul_le_mul_of_nonneg_left h1 hwr, mul_le_mul_of_nonneg_left h2 hwr⟩

private theorem gramTerm_width {c ε : ℚ} (hc : 0 ≤ c) (hε : 0 < ε) (σ : ℚ) (p q : ℚ × ℚ) :
    (gramTerm σ c ε p q).2 - (gramTerm σ c ε p q).1 ≤
      ε * (pointWeight c p * pointWeight c q) := by
  have hw : 0 ≤ pointWeight c p * pointWeight c q :=
    mul_nonneg (pointWeight_nonneg hc p) (pointWeight_nonneg hc q)
  have h := expEnclosure_width (gaussExponent_nonpos σ p q) hε
  simp only [gramTerm]
  split_ifs with h0
  · simp [h0]
  · rw [← mul_sub, mul_comm ε]
    exact mul_le_mul_of_nonneg_left h hw

private theorem fst_sum_map {α : Type*} (l : List α) (f : α → ℚ × ℚ) :
    (l.map f).sum.1 = (l.map fun a => (f a).1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem snd_sum_map {α : Type*} (l : List α) (f : α → ℚ × ℚ) :
    (l.map f).sum.2 = (l.map fun a => (f a).2).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem gramSum_fst (σ c ε : ℚ) (x y : List (ℚ × ℚ)) :
    (gramSum σ c ε x y).1 =
      (x.map fun p => (y.map fun q => (gramTerm σ c ε p q).1).sum).sum := by
  simp only [gramSum, fst_sum_map]

theorem gramSum_snd (σ c ε : ℚ) (x y : List (ℚ × ℚ)) :
    (gramSum σ c ε x y).2 =
      (x.map fun p => (y.map fun q => (gramTerm σ c ε p q).2).sum).sum := by
  simp only [gramSum, snd_sum_map]

private theorem linearKernel_realPoints {A B : ℝ} (σ : ℝ) (w : PersistenceImage.Weight A B)
    (x y : List (ℚ × ℚ)) :
    linearKernel σ w (realPoints x) (realPoints y) =
      (x.map fun p => (y.map fun q =>
        w (birthPersistence (realPoint p)) * w (birthPersistence (realPoint q)) *
          kernel σ (realPoint p) (realPoint q)).sum).sum := by
  rw [linearKernel, ← Fin.sum_univ_fun_getElem x fun p => (y.map fun q =>
    w (birthPersistence (realPoint p)) * w (birthPersistence (realPoint q)) *
      kernel σ (realPoint p) (realPoint q)).sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_fun_getElem y fun q =>
    w (birthPersistence (realPoint x[i.1])) * w (birthPersistence (realPoint q)) *
      kernel σ (realPoint x[i.1]) (realPoint q)]
  rfl

private theorem cast_sum_map {α : Type*} (l : List α) (f : α → ℚ) :
    (((l.map f).sum : ℚ) : ℝ) = (l.map fun a => (f a : ℝ)).sum := by
  rw [Rat.cast_list_sum, List.map_map]
  rfl

/-- The Gram sum encloses the actual linear kernel of the two occurrence families, for every
bandwidth and every scalar tolerance. -/
theorem gramSum_mem {c : ℚ} (hc : 0 ≤ c) (σ ε : ℚ) (x y : List (ℚ × ℚ)) :
    ((gramSum σ c ε x y).1 : ℝ) ≤
        linearKernel (σ : ℝ) (capWeight c hc) (realPoints x) (realPoints y) ∧
      linearKernel (σ : ℝ) (capWeight c hc) (realPoints x) (realPoints y) ≤
        ((gramSum σ c ε x y).2 : ℝ) := by
  rw [linearKernel_realPoints, gramSum_fst, gramSum_snd, cast_sum_map, cast_sum_map]
  simp only [cast_sum_map]
  constructor
  · exact List.sum_le_sum fun p _ => List.sum_le_sum fun q _ => (gramTerm_spec hc σ ε p q).1
  · exact List.sum_le_sum fun p _ => List.sum_le_sum fun q _ => (gramTerm_spec hc σ ε p q).2

/-- The width of the Gram sum is at most the scalar tolerance times the product of the total
weights. -/
theorem gramSum_width {c ε : ℚ} (hc : 0 ≤ c) (hε : 0 < ε) (σ : ℚ) (x y : List (ℚ × ℚ)) :
    (gramSum σ c ε x y).2 - (gramSum σ c ε x y).1 ≤
      ε * (totalWeight c x * totalWeight c y) := by
  have h : (x.map fun p => (y.map fun q => (gramTerm σ c ε p q).2).sum).sum ≤
      (x.map fun p => (y.map fun q =>
        (gramTerm σ c ε p q).1 + ε * (pointWeight c p * pointWeight c q)).sum).sum :=
    List.sum_le_sum fun p _ => List.sum_le_sum fun q _ => by
      linarith [gramTerm_width hc hε σ p q]
  have e : (x.map fun p => (y.map fun q =>
        (gramTerm σ c ε p q).1 + ε * (pointWeight c p * pointWeight c q)).sum).sum =
      (x.map fun p => (y.map fun q => (gramTerm σ c ε p q).1).sum).sum +
        ε * (totalWeight c x * totalWeight c y) := by
    simp only [List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_right, totalWeight]
  rw [gramSum_fst, gramSum_snd]
  linarith

/-- The interval contains the actual linear kernel, for every bandwidth and tolerance. -/
theorem gramEnclosure_mem {c : ℚ} (hc : 0 ≤ c) (σ δ : ℚ) (x y : List (ℚ × ℚ)) :
    ((gramEnclosure σ c δ x y).1 : ℝ) ≤
        linearKernel (σ : ℝ) (capWeight c hc) (realPoints x) (realPoints y) ∧
      linearKernel (σ : ℝ) (capWeight c hc) (realPoints x) (realPoints y) ≤
        ((gramEnclosure σ c δ x y).2 : ℝ) :=
  gramSum_mem hc σ _ x y

/-- The width is at most the requested tolerance, for all lists. -/
theorem gramEnclosure_width {c δ : ℚ} (hc : 0 ≤ c) (hδ : 0 < δ) (σ : ℚ)
    (x y : List (ℚ × ℚ)) :
    (gramEnclosure σ c δ x y).2 - (gramEnclosure σ c δ x y).1 ≤ δ := by
  set W := totalWeight c x * totalWeight c y with hW
  have hW0 : 0 ≤ W := mul_nonneg (totalWeight_nonneg hc x) (totalWeight_nonneg hc y)
  have hm : (0 : ℚ) < max 1 W := lt_max_of_lt_left one_pos
  refine (gramSum_width hc (div_pos hδ hm) σ x y).trans ?_
  rw [← hW, div_mul_eq_mul_div, div_le_iff₀ hm]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le

theorem gramEnclosure_fst_le_snd {c : ℚ} (hc : 0 ≤ c) (σ δ : ℚ) (x y : List (ℚ × ℚ)) :
    (gramEnclosure σ c δ x y).1 ≤ (gramEnclosure σ c δ x y).2 := by
  have h := (gramEnclosure_mem hc σ δ x y).1.trans (gramEnclosure_mem hc σ δ x y).2
  exact_mod_cast h

theorem gramEnclosure?_eq_some_iff {σ c δ : ℚ} {x y : List (ℚ × ℚ)} {I : ℚ × ℚ} :
    gramEnclosure? σ c δ x y = some I ↔
      (0 < σ ∧ 0 < c ∧ 0 < δ) ∧ I = gramEnclosure σ c δ x y := by
  unfold gramEnclosure?
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem gramEnclosure?_eq_none_iff {σ c δ : ℚ} {x y : List (ℚ × ℚ)} :
    gramEnclosure? σ c δ x y = none ↔ ¬ (0 < σ ∧ 0 < c ∧ 0 < δ) := by
  unfold gramEnclosure?
  split_ifs with h <;> simp [h]

/-- Every returned interval contains the actual linear kernel and has width at most `δ`. -/
theorem gramEnclosure?_spec {σ c δ : ℚ} {x y : List (ℚ × ℚ)} {I : ℚ × ℚ} (hc : 0 ≤ c)
    (h : gramEnclosure? σ c δ x y = some I) :
    ((I.1 : ℝ) ≤ linearKernel (σ : ℝ) (capWeight c hc) (realPoints x) (realPoints y) ∧
        linearKernel (σ : ℝ) (capWeight c hc) (realPoints x) (realPoints y) ≤ (I.2 : ℝ)) ∧
      I.2 - I.1 ≤ δ := by
  obtain ⟨⟨-, -, hδ⟩, rfl⟩ := gramEnclosure?_eq_some_iff.1 h
  exact ⟨gramEnclosure_mem hc σ δ x y, gramEnclosure_width hc hδ σ x y⟩

/-! ## The squared RKHS distance -/

/-- A rational interval for the squared RKHS distance of the embeddings of the two lists, of
width at most `δ` for `0 ≤ c` and `0 < δ`: `K(x, x) + K(y, y) - 2 K(x, y)` with the three
Gram enclosures at tolerance `δ / 4`, the lower endpoint raised to `0` when negative. -/
def sqDistEnclosure (σ c δ : ℚ) (x y : List (ℚ × ℚ)) : ℚ × ℚ :=
  let A := gramEnclosure σ c (δ / 4) x x
  let B := gramEnclosure σ c (δ / 4) y y
  let C := gramEnclosure σ c (δ / 4) x y
  (max 0 (A.1 + B.1 - 2 * C.2), A.2 + B.2 - 2 * C.1)

/-- The squared-distance enclosure for an admissible request: `none` unless `0 < σ`, `0 < c`
and `0 < δ`. -/
def sqDistEnclosure? (σ c δ : ℚ) (x y : List (ℚ × ℚ)) : Option (ℚ × ℚ) :=
  if 0 < σ ∧ 0 < c ∧ 0 < δ then some (sqDistEnclosure σ c δ x y) else none

/-- The interval contains the actual squared RKHS distance of the two embeddings, for every
bandwidth and tolerance. -/
theorem sqDistEnclosure_mem {c : ℚ} (hc : 0 ≤ c) (σ δ : ℚ) (x y : List (ℚ × ℚ)) :
    ((sqDistEnclosure σ c δ x y).1 : ℝ) ≤
        ‖embedding (σ : ℝ) (capWeight c hc) (realPoints x) -
          embedding (σ : ℝ) (capWeight c hc) (realPoints y)‖ ^ 2 ∧
      ‖embedding (σ : ℝ) (capWeight c hc) (realPoints x) -
          embedding (σ : ℝ) (capWeight c hc) (realPoints y)‖ ^ 2 ≤
        ((sqDistEnclosure σ c δ x y).2 : ℝ) := by
  obtain ⟨a1, a2⟩ := gramEnclosure_mem hc σ (δ / 4) x x
  obtain ⟨b1, b2⟩ := gramEnclosure_mem hc σ (δ / 4) y y
  obtain ⟨c1, c2⟩ := gramEnclosure_mem hc σ (δ / 4) x y
  rw [norm_embedding_sub_sq]
  simp only [sqDistEnclosure, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_add,
    Rat.cast_mul, Rat.cast_ofNat]
  refine ⟨max_le ?_ (by linarith), by linarith⟩
  rw [← norm_embedding_sub_sq]
  positivity

/-- The width is at most the requested tolerance, for all lists. -/
theorem sqDistEnclosure_width {c δ : ℚ} (hc : 0 ≤ c) (hδ : 0 < δ) (σ : ℚ)
    (x y : List (ℚ × ℚ)) :
    (sqDistEnclosure σ c δ x y).2 - (sqDistEnclosure σ c δ x y).1 ≤ δ := by
  have hδ4 : 0 < δ / 4 := by positivity
  have a := gramEnclosure_width hc hδ4 σ x x
  have b := gramEnclosure_width hc hδ4 σ y y
  have d := gramEnclosure_width hc hδ4 σ x y
  have hmax := le_max_right 0
    ((gramEnclosure σ c (δ / 4) x x).1 + (gramEnclosure σ c (δ / 4) y y).1 -
      2 * (gramEnclosure σ c (δ / 4) x y).2)
  simp only [sqDistEnclosure]
  linarith

theorem sqDistEnclosure_fst_nonneg (σ c δ : ℚ) (x y : List (ℚ × ℚ)) :
    0 ≤ (sqDistEnclosure σ c δ x y).1 := le_max_left _ _

theorem sqDistEnclosure_fst_le_snd {c : ℚ} (hc : 0 ≤ c) (σ δ : ℚ) (x y : List (ℚ × ℚ)) :
    (sqDistEnclosure σ c δ x y).1 ≤ (sqDistEnclosure σ c δ x y).2 := by
  have h := (sqDistEnclosure_mem hc σ δ x y).1.trans (sqDistEnclosure_mem hc σ δ x y).2
  exact_mod_cast h

theorem sqDistEnclosure?_eq_some_iff {σ c δ : ℚ} {x y : List (ℚ × ℚ)} {I : ℚ × ℚ} :
    sqDistEnclosure? σ c δ x y = some I ↔
      (0 < σ ∧ 0 < c ∧ 0 < δ) ∧ I = sqDistEnclosure σ c δ x y := by
  unfold sqDistEnclosure?
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem sqDistEnclosure?_eq_none_iff {σ c δ : ℚ} {x y : List (ℚ × ℚ)} :
    sqDistEnclosure? σ c δ x y = none ↔ ¬ (0 < σ ∧ 0 < c ∧ 0 < δ) := by
  unfold sqDistEnclosure?
  split_ifs with h <;> simp [h]

/-- Every returned interval contains the actual squared RKHS distance and has width at most
`δ`. -/
theorem sqDistEnclosure?_spec {σ c δ : ℚ} {x y : List (ℚ × ℚ)} {I : ℚ × ℚ} (hc : 0 ≤ c)
    (h : sqDistEnclosure? σ c δ x y = some I) :
    ((I.1 : ℝ) ≤ ‖embedding (σ : ℝ) (capWeight c hc) (realPoints x) -
          embedding (σ : ℝ) (capWeight c hc) (realPoints y)‖ ^ 2 ∧
        ‖embedding (σ : ℝ) (capWeight c hc) (realPoints x) -
          embedding (σ : ℝ) (capWeight c hc) (realPoints y)‖ ^ 2 ≤ (I.2 : ℝ)) ∧
      I.2 - I.1 ≤ δ := by
  obtain ⟨⟨-, -, hδ⟩, rfl⟩ := sqDistEnclosure?_eq_some_iff.1 h
  exact ⟨sqDistEnclosure_mem hc σ δ x y, sqDistEnclosure_width hc hδ σ x y⟩

/-! ## Diagrams -/

/-- The embedding of a diagram whose finite part is listed by `x` is the embedding of the
occurrence family of `x`; essential bars of the diagram play no role. -/
theorem diagramEmbedding_eq_embedding_realPoints {A B : ℝ} (σ : ℝ)
    (w : PersistenceImage.Weight A B) (D : Diagram ℝ) (x : List (ℚ × ℚ))
    (h : finitePart D.points = ((x.map realPoint : List (ℝ × ℝ)) : Multiset (ℝ × ℝ))) :
    diagramEmbedding σ w D = embedding σ w (realPoints x) := by
  rw [diagramEmbedding_eq_sum, h, Multiset.map_coe, Multiset.sum_coe, List.map_map, embedding,
    finiteFeatureSum]
  exact (Fin.sum_univ_fun_getElem x fun p =>
    w (birthPersistence (realPoint p)) • featureAt σ (realPoint p)).symm

end TDA.Persistence.Enclosure
