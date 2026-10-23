import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Uniform packing from a metric doubling bound

A doubling bound covers each closed ball of positive radius by at most `Λ`
closed balls of half that radius, with centers in the ambient space. Iterating
`h` times gives `Λ ^ h` balls. If their diameters are smaller than the separation
of a finite set, each covering ball contains at most one point. The resulting
bound depends on the doubling constant and radius ratio, and not on cardinality
or metric spread.
-/

namespace TDA.Filtration.SparseRips

open scoped BigOperators

variable {V : Type*} [MetricSpace V]

/-- The closed-ball doubling convention with centers in the original metric space. -/
def ClosedBallDoubling (Λ : ℕ) : Prop :=
  1 ≤ Λ ∧ ∀ p : V, ∀ R : ℝ, 0 < R → ∃ C : Finset V,
    C.card ≤ Λ ∧ ∀ x, dist p x ≤ R → ∃ q ∈ C, dist q x ≤ R / 2

/-- Iterate the stated doubling hypothesis, keeping an explicit bound on all centers. -/
theorem ClosedBallDoubling.iterated_cover {Λ : ℕ} (hd : ClosedBallDoubling (V := V) Λ)
    (p : V) {R : ℝ} (hR : 0 < R) (h : ℕ) :
    ∃ C : Finset V, C.card ≤ Λ ^ h ∧
      ∀ x, dist p x ≤ R → ∃ q ∈ C, dist q x ≤ R / (2 : ℝ) ^ h := by
  classical
  induction h with
  | zero => exact ⟨{p}, by simp, fun x hx => ⟨p, by simp, by simpa using hx⟩⟩
  | succ h ih =>
    obtain ⟨A, hA, hcover⟩ := ih
    have hrad : 0 < R / (2 : ℝ) ^ h := div_pos hR (by positivity)
    choose C hC hCcover using fun q : V => hd.2 q (R / (2 : ℝ) ^ h) hrad
    refine ⟨A.biUnion C, ?_, ?_⟩
    · calc
        (A.biUnion C).card ≤ ∑ q ∈ A, (C q).card := Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ A, Λ := Finset.sum_le_sum fun q _ => hC q
        _ = A.card * Λ := by simp
        _ ≤ Λ ^ h * Λ := Nat.mul_le_mul_right Λ hA
        _ = Λ ^ (h + 1) := (pow_succ Λ h).symm
    · intro x hx
      obtain ⟨q, hq, hqx⟩ := hcover x hx
      obtain ⟨z, hz, hzx⟩ := hCcover q x hqx
      refine ⟨z, Finset.mem_biUnion.mpr ⟨q, hq, hz⟩, ?_⟩
      convert hzx using 1
      rw [pow_succ]
      ring

/-- Uniform cardinality bound for separated points in one closed ball. -/
theorem ClosedBallDoubling.packing_bound {Λ : ℕ} (hd : ClosedBallDoubling (V := V) Λ)
    (p : V) {R δ : ℝ} (hR : 0 < R) (h : ℕ)
    (hratio : 2 * (R / (2 : ℝ) ^ h) < δ) (P : Finset V)
    (hball : ∀ x ∈ P, dist p x ≤ R)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y) :
    P.card ≤ Λ ^ h := by
  classical
  obtain ⟨C, hC, hcover⟩ := hd.iterated_cover p hR h
  let f (x : V) : V := if hx : x ∈ P then Classical.choose (hcover x (hball x hx)) else p
  have hf (x : V) (hx : x ∈ P) : f x ∈ C ∧ dist (f x) x ≤ R / (2 : ℝ) ^ h := by
    dsimp [f]
    rw [dif_pos hx]
    exact Classical.choose_spec (hcover x (hball x hx))
  apply (Finset.card_le_card_of_injOn f (fun x hx => (hf x hx).1) ?_).trans hC
  intro x hx y hy heq
  by_contra hxy
  have hsep' := hsep x hx y hy hxy
  have hfx := (hf x hx).2
  have hfy := (hf y hy).2
  have htri := dist_triangle x (f x) y
  rw [heq] at hfx
  rw [dist_comm x (f x), heq] at htri
  linarith

/-- Every metric subspace of the real line has the same closed-ball doubling bound,
with all four centers chosen in the subspace itself. -/
theorem ClosedBallDoubling.of_isometry_real (f : V → ℝ) (hf : Isometry f) :
    ClosedBallDoubling (V := V) 4 := by
  classical
  refine ⟨by norm_num, ?_⟩
  intro p R hR
  let bucket (k : Fin 4) (x : V) : Prop :=
    f p - R + (k.val : ℝ) * (R / 2) ≤ f x ∧
      f x ≤ f p - R + ((k.val : ℝ) + 1) * (R / 2)
  let q (k : Fin 4) : V := if h : ∃ x, bucket k x then Classical.choose h else p
  have hq (k : Fin 4) (x : V) (hx : bucket k x) : bucket k (q k) := by
    dsimp [q]
    rw [dif_pos (show ∃ x, bucket k x from ⟨x, hx⟩)]
    exact Classical.choose_spec (show ∃ x, bucket k x from ⟨x, hx⟩)
  refine ⟨Finset.univ.image q, (Finset.card_image_le).trans (by simp), ?_⟩
  intro x hx
  have hdist : |f p - f x| ≤ R := by
    rw [← Real.dist_eq, hf.dist_eq]
    exact hx
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdist
  have hbucket : ∃ k : Fin 4, bucket k x := by
    by_cases h₀ : f x ≤ f p - R / 2
    · exact ⟨0, by dsimp [bucket]; norm_num; constructor <;> linarith⟩
    · by_cases h₁ : f x ≤ f p
      · exact ⟨1, by dsimp [bucket]; norm_num; constructor <;> linarith⟩
      · by_cases h₂ : f x ≤ f p + R / 2
        · exact ⟨2, by dsimp [bucket]; norm_num; constructor <;> linarith⟩
        · exact ⟨3, by dsimp [bucket]; norm_num; constructor <;> linarith⟩
  obtain ⟨k, hk⟩ := hbucket
  refine ⟨q k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩, ?_⟩
  rw [← hf.dist_eq, Real.dist_eq]
  apply abs_le.mpr
  have hqk := hq k x hk
  dsimp [bucket] at hk hqk
  constructor <;> linarith

end TDA.Filtration.SparseRips
