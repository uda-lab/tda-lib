import TDA.Filtration.SparseRips.Relaxed
import TDA.Filtration.SparseRips.Packing
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset

/-!
# Uniform neighbor bounds for the union over all sparse scales

An edge is counted whenever it appears at any scale. Orient it toward the vertex
inserted earlier by the greedy permutation; its deletion time is at least as large.
All such neighbors of a vertex lie in the closed ball at that vertex's deletion
time and have separation at least its insertion radius. The doubling packing bound
therefore controls their number uniformly over the entire filtration.
-/

namespace TDA.Filtration.SparseRips

open GreedyNet
open scoped BigOperators

noncomputable section

variable {V : Type*} [MetricSpace V] [Fintype V]

local instance sparsityDecidableEq : DecidableEq V := Classical.decEq V

/-- A packing depth can be chosen from the approximation parameter alone. -/
theorem exists_packing_depth {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3) :
    ∃ h : ℕ, 2 / (2 : ℝ) ^ h < η * (1 - 2 * η) := by
  have hp : 0 < η * (1 - 2 * η) / 2 := by
    have : 0 < 1 - 2 * η := by linarith
    positivity
  obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨h, ?_⟩
  have heq : 2 / (2 : ℝ) ^ h = 2 * (1 / 2 : ℝ) ^ h := by
    simp only [div_pow, one_pow]
    ring
  rw [heq]
  linarith

/-- The carrier consists of precisely the faces occurring at some nonnegative scale. -/
def sparseCarrier (seed : V) (η : ℝ) : PreAbstractSimplicialComplex V where
  faces := {σ | ∃ a, 0 ≤ a ∧ σ ∈ closedActiveComplex seed η a}
  isRelLowerSet_faces := by
    rintro σ ⟨a, ha, hσ⟩
    exact ⟨hσ.1.1, fun τ hτσ hτ =>
      ⟨a, ha, (closedActiveComplex seed η a).isRelLowerSet_faces hσ |>.2 hτσ hτ⟩⟩

@[simp] theorem mem_sparseCarrier (seed : V) (η : ℝ) (σ : Finset V) :
    σ ∈ sparseCarrier seed η ↔ ∃ a, 0 ≤ a ∧ σ ∈ closedActiveComplex seed η a := Iff.rfl

theorem mem_sparseCarrier_iff (seed : V) (η : ℝ) (σ : Finset V) :
    σ ∈ sparseCarrier seed η ↔ ∃ r, σ ∈ sparseFiltration seed η r := by
  constructor
  · rintro ⟨a, ha, hσ⟩
    exact ⟨a, a, ha, le_rfl, hσ⟩
  · rintro ⟨r, a, ha, _, hσ⟩
    exact ⟨a, ha, hσ⟩

/-- Neighbors over all scales, with ties ordered by their actual greedy insertion indices. -/
def laterNeighbors (seed : V) (η : ℝ) (p : V) : Finset V := by
  classical
  exact Finset.univ.filter fun q => insertionIndex seed q < insertionIndex seed p ∧
    ({p, q} : Finset V) ∈ sparseCarrier seed η

@[simp] theorem mem_laterNeighbors (seed : V) (η : ℝ) (p q : V) :
    q ∈ laterNeighbors seed η p ↔ insertionIndex seed q < insertionIndex seed p ∧
      ({p, q} : Finset V) ∈ sparseCarrier seed η := by
  classical
  simp [laterNeighbors]

@[simp] theorem laterNeighbors_seed (seed : V) (η : ℝ) : laterNeighbors seed η seed = ∅ := by
  ext q
  simp

theorem laterNeighbors_subset_prefix (seed : V) (η : ℝ) (p : V) :
    laterNeighbors seed η p ⊆ greedyPrefix seed (insertionIndex seed p - 1) := by
  intro q hq
  have hi := ((mem_laterNeighbors seed η p q).mp hq).1
  exact prefix_mono seed (by omega) (mem_insertionIndex seed q)

/-- A later neighbor stays within the finite deletion ball, even if the edge first
appears at an earlier scale than the vertex's deletion time. -/
theorem laterNeighbor_dist_le (seed : V) {η : ℝ} (hη : 0 < η) (p : V)
    (hp : p ≠ seed) {q : V} (hq : q ∈ laterNeighbors seed η p) :
    dist p q ≤ radius seed (insertionIndex seed p - 1) / (η * (1 - 2 * η)) := by
  obtain ⟨a, _, hface⟩ := ((mem_laterNeighbors seed η p q).mp hq).2
  have hdist := ((Rips.mem_sublevel_iff _ _ _).mp
    (relaxedComplex_le_rips hη.le _ hface.1)).2 p (by simp) q (by simp)
  have hactive := hface.2 p (by simp)
  rw [deletionTime_of_ne seed η hp] at hactive
  exact hdist.trans hactive

/-- The greedy orientation agrees with ordering by deletion time; ties use insertion index. -/
theorem laterNeighbor_closedActive_at_time (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (p : V) {q : V}
    (hq : q ∈ laterNeighbors seed η p) :
    ClosedActive (deletionTime seed η q)
      (radius seed (insertionIndex seed p - 1) / (η * (1 - 2 * η))) := by
  by_cases hqs : q = seed
  · subst q; simp
  · rw [deletionTime_of_ne seed η hqs]
    have hi := ((mem_laterNeighbors seed η p q).mp hq).1
    have hrad := radius_antitone seed (show insertionIndex seed q - 1 ≤
      insertionIndex seed p - 1 by omega)
    exact div_le_div_of_nonneg_right hrad (mul_nonneg hη.le (by linarith))

/-- The number of later neighbors over all scales is independent of spread and input size. -/
theorem laterNeighbors_card_le (seed : V) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {Λ : ℕ} (hd : ClosedBallDoubling (V := V) Λ) (h : ℕ)
    (hsmall : 2 / (2 : ℝ) ^ h < η * (1 - 2 * η)) (p : V) :
    (laterNeighbors seed η p).card ≤ Λ ^ h := by
  by_cases hp : p = seed
  · subst p; simp
  · let ρ := radius seed (insertionIndex seed p - 1)
    let t := ρ / (η * (1 - 2 * η))
    have hρ : 0 < ρ := insertionRadius_pos seed p hp
    have hfactor : 0 < η * (1 - 2 * η) := mul_pos hη (by linarith)
    have ht : 0 < t := div_pos hρ hfactor
    have hcancel : t * (η * (1 - 2 * η)) = ρ := div_mul_cancel₀ _ (ne_of_gt hfactor)
    apply hd.packing_bound p ht h (δ := ρ) ?_ (laterNeighbors seed η p)
      (fun q hq => laterNeighbor_dist_le seed hη p hp hq) ?_
    · have hmul := mul_lt_mul_of_pos_left hsmall ht
      rw [hcancel] at hmul
      calc
        2 * (t / (2 : ℝ) ^ h) = t * (2 / (2 : ℝ) ^ h) := by ring
        _ < ρ := hmul
    · intro x hx y hy hxy
      exact separation seed (insertionIndex seed p - 1)
        (laterNeighbors_subset_prefix seed η p hx) (laterNeighbors_subset_prefix seed η p hy) hxy

/-- A directed edge records its earlier-deleted endpoint first. -/
def orientedEdges (seed : V) (η : ℝ) : Finset (V × V) :=
  Finset.univ.biUnion fun p => (laterNeighbors seed η p).image (fun q => (p, q))

@[simp] theorem mem_orientedEdges (seed : V) (η : ℝ) (p q : V) :
    (p, q) ∈ orientedEdges seed η ↔ insertionIndex seed q < insertionIndex seed p ∧
      ({p, q} : Finset V) ∈ sparseCarrier seed η := by
  classical
  simp [orientedEdges]

/-- Every distinct sparse edge is counted once in one of its two orientations. -/
theorem pair_mem_carrier_iff_oriented (seed : V) (η : ℝ) {p q : V} (hpq : p ≠ q) :
    ({p, q} : Finset V) ∈ sparseCarrier seed η ↔
      (p, q) ∈ orientedEdges seed η ∨ (q, p) ∈ orientedEdges seed η := by
  classical
  constructor
  · intro hface
    rcases lt_trichotomy (insertionIndex seed q) (insertionIndex seed p) with h | h | h
    · exact Or.inl ((mem_orientedEdges seed η p q).mpr ⟨h, hface⟩)
    · exact (hpq (insertionIndex_injective seed h.symm)).elim
    · exact Or.inr ((mem_orientedEdges seed η q p).mpr ⟨h, by simpa [Finset.pair_comm] using hface⟩)
  · rintro (h | h)
    · exact ((mem_orientedEdges seed η p q).mp h).2
    · simpa [Finset.pair_comm] using ((mem_orientedEdges seed η q p).mp h).2

/-- Uniform linear bound on directed edges in the full sparse carrier. -/
theorem orientedEdges_card_le (seed : V) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {Λ : ℕ} (hd : ClosedBallDoubling (V := V) Λ) (h : ℕ)
    (hsmall : 2 / (2 : ℝ) ^ h < η * (1 - 2 * η)) :
    (orientedEdges seed η).card ≤ Fintype.card V * Λ ^ h := by
  calc
    (orientedEdges seed η).card ≤ ∑ p : V,
        ((laterNeighbors seed η p).image (fun q => (p, q))).card := Finset.card_biUnion_le
    _ ≤ ∑ p : V, (laterNeighbors seed η p).card :=
      Finset.sum_le_sum fun p _ => Finset.card_image_le
    _ ≤ ∑ _p : V, Λ ^ h :=
      Finset.sum_le_sum fun p _ => laterNeighbors_card_le seed hη hη' hd h hsmall p
    _ = Fintype.card V * Λ ^ h := by simp

/-- Each face is assigned to its largest greedy insertion index. All other vertices
are among that vertex's uniformly bounded neighbors. -/
theorem exists_assigned_vertex (seed : V) (η : ℝ) {σ : Finset V}
    (hσ : σ ∈ sparseCarrier seed η) :
    ∃ p ∈ σ, σ.erase p ⊆ laterNeighbors seed η p := by
  classical
  have hne := (sparseCarrier seed η).isRelLowerSet_faces hσ |>.1
  obtain ⟨p, hp, hmax⟩ := σ.exists_max_image (insertionIndex seed) hne
  refine ⟨p, hp, ?_⟩
  intro q hq
  obtain ⟨hqp, hqσ⟩ := Finset.mem_erase.mp hq
  apply (mem_laterNeighbors seed η p q).mpr
  refine ⟨lt_of_le_of_ne (hmax q hqσ) (fun h => hqp (insertionIndex_injective seed h)), ?_⟩
  apply (sparseCarrier seed η).isRelLowerSet_faces hσ |>.2 ?_ (by simp)
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hp
  · simpa only [Finset.mem_singleton.mp hx] using hqσ

/-- All distinct `j`-simplices ever occurring, rather than faces at one chosen scale. -/
def facesOfDimension (seed : V) (η : ℝ) (j : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun σ => σ ∈ sparseCarrier seed η ∧ σ.card = j + 1

private def assignedCandidates (seed : V) (η : ℝ) (j : ℕ) : Finset (Finset V) :=
  Finset.univ.biUnion fun p => ((laterNeighbors seed η p).powersetCard j).image (insert p)

private theorem faces_subset_candidates (seed : V) (η : ℝ) (j : ℕ) :
    facesOfDimension seed η j ⊆ assignedCandidates seed η j := by
  classical
  intro σ hσ
  have hσ' : σ ∈ sparseCarrier seed η ∧ σ.card = j + 1 := by
    simpa [facesOfDimension] using hσ
  obtain ⟨p, hp, hsub⟩ := exists_assigned_vertex seed η hσ'.1
  apply Finset.mem_biUnion.mpr
  refine ⟨p, Finset.mem_univ p, Finset.mem_image.mpr ?_⟩
  refine ⟨σ.erase p, Finset.mem_powersetCard.mpr ⟨hsub, ?_⟩, Finset.insert_erase hp⟩
  rw [Finset.card_erase_of_mem hp, hσ'.2]
  omega

/-- The uniform linear-size bound in each fixed dimension counts the union over all scales. -/
theorem facesOfDimension_card_le (seed : V) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {Λ : ℕ} (hd : ClosedBallDoubling (V := V) Λ) (h : ℕ)
    (hsmall : 2 / (2 : ℝ) ^ h < η * (1 - 2 * η)) (j : ℕ) :
    (facesOfDimension seed η j).card ≤ Fintype.card V * (Λ ^ h) ^ j := by
  calc
    (facesOfDimension seed η j).card ≤ (assignedCandidates seed η j).card :=
      Finset.card_le_card (faces_subset_candidates seed η j)
    _ ≤ ∑ p : V, (((laterNeighbors seed η p).powersetCard j).image (insert p)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p : V, ((laterNeighbors seed η p).powersetCard j).card :=
      Finset.sum_le_sum fun p _ => Finset.card_image_le
    _ = ∑ p : V, (laterNeighbors seed η p).card.choose j := by simp only [Finset.card_powersetCard]
    _ ≤ ∑ p : V, (Λ ^ h) ^ j := by
      apply Finset.sum_le_sum
      intro p _
      exact (Nat.choose_le_pow _ _).trans
        (Nat.pow_le_pow_left (laterNeighbors_card_le seed hη hη' hd h hsmall p) j)
    _ = Fintype.card V * (Λ ^ h) ^ j := by simp

/-- The finite skeleton of the carrier includes every face ever appearing in that dimension range. -/
def skeletonFaces (seed : V) (η : ℝ) (m : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun σ => σ ∈ sparseCarrier seed η ∧ σ.card ≤ m + 1

/-- Fixed-dimensional skeletons have a linear bound with the explicit constant in the statement. -/
theorem skeletonFaces_card_le (seed : V) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {Λ : ℕ} (hd : ClosedBallDoubling (V := V) Λ) (h : ℕ)
    (hsmall : 2 / (2 : ℝ) ^ h < η * (1 - 2 * η)) (m : ℕ) :
    (skeletonFaces seed η m).card ≤ Fintype.card V * ∑ j ∈ Finset.range (m + 1), (Λ ^ h) ^ j := by
  classical
  have hsub : skeletonFaces seed η m ⊆
      (Finset.range (m + 1)).biUnion (facesOfDimension seed η) := by
    intro σ hσ
    have hσ' : σ ∈ sparseCarrier seed η ∧ σ.card ≤ m + 1 := by
      simpa [skeletonFaces] using hσ
    have hpos := Finset.card_pos.mpr ((sparseCarrier seed η).isRelLowerSet_faces hσ'.1 |>.1)
    apply Finset.mem_biUnion.mpr
    refine ⟨σ.card - 1, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [facesOfDimension, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hσ'.1, by omega⟩
  calc
    (skeletonFaces seed η m).card ≤
        ((Finset.range (m + 1)).biUnion (facesOfDimension seed η)).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (m + 1), (facesOfDimension seed η j).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (m + 1), Fintype.card V * (Λ ^ h) ^ j :=
      Finset.sum_le_sum fun j _ => facesOfDimension_card_le seed hη hη' hd h hsmall j
    _ = Fintype.card V * ∑ j ∈ Finset.range (m + 1), (Λ ^ h) ^ j := by rw [Finset.mul_sum]

end

end TDA.Filtration.SparseRips
