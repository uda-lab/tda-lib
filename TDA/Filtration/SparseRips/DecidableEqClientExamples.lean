import TDA.Filtration.SparseRips.UnionDeletion
import TDA.Filtration.SparseRips.Sparsity

/-!
# Client statements of the sparse Rips face formulas

Regression fixtures for #1286, family 12 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance. The
client holds a decidable equality on the finite metric space of vertices (a hypothesis of the
statement) and writes finite images, erasures and pairs of vertices with it; every proof is a
direct application of a library theorem.

* The greedy net: the prefix after one more insertion.
* The sparse carrier: later neighbours, oriented edges and the assignment of a face to its last
  inserted vertex.
* The deletion maps: the image of a face under a deletion map.
* The union of a face with its projected vertices in a relaxed complex.
-/

namespace TDA.Filtration.SparseRips.DecidableEqClientExamples

variable {V : Type*} [MetricSpace V] [Fintype V] [DecidableEq V]

/-- The greedy prefix after one more insertion. -/
theorem prefix_succ (seed : V) (n : ℕ) :
    GreedyNet.greedyPrefix seed (n + 1) =
      insert (GreedyNet.next seed (GreedyNet.greedyPrefix seed n))
        (GreedyNet.greedyPrefix seed n) :=
  GreedyNet.prefix_succ seed n

/-- The later neighbours of a vertex. -/
theorem mem_laterNeighbors (seed : V) (η : ℝ) (p q : V) :
    q ∈ laterNeighbors seed η p ↔
      GreedyNet.insertionIndex seed q < GreedyNet.insertionIndex seed p ∧
        ({p, q} : Finset V) ∈ sparseCarrier seed η :=
  TDA.Filtration.SparseRips.mem_laterNeighbors seed η p q

/-- The oriented edges of the sparse carrier. -/
theorem mem_orientedEdges (seed : V) (η : ℝ) (p q : V) :
    (p, q) ∈ orientedEdges seed η ↔
      GreedyNet.insertionIndex seed q < GreedyNet.insertionIndex seed p ∧
        ({p, q} : Finset V) ∈ sparseCarrier seed η :=
  TDA.Filtration.SparseRips.mem_orientedEdges seed η p q

/-- Every distinct sparse edge occurs in one of its two orientations. -/
theorem pair_mem_carrier_iff_oriented (seed : V) (η : ℝ) {p q : V} (hpq : p ≠ q) :
    ({p, q} : Finset V) ∈ sparseCarrier seed η ↔
      (p, q) ∈ orientedEdges seed η ∨ (q, p) ∈ orientedEdges seed η :=
  TDA.Filtration.SparseRips.pair_mem_carrier_iff_oriented seed η hpq

/-- Every face of the sparse carrier has a vertex whose remaining vertices are later
neighbours. -/
theorem exists_assigned_vertex (seed : V) (η : ℝ) {σ : Finset V}
    (hσ : σ ∈ sparseCarrier seed η) :
    ∃ p ∈ σ, σ.erase p ⊆ laterNeighbors seed η p :=
  TDA.Filtration.SparseRips.exists_assigned_vertex seed η hσ

/-- A deletion map fixes every face of a later closed active complex. -/
theorem deletionMap_image_later (seed : V) {η r s : ℝ} (hη : 0 ≤ η) (hr : 0 ≤ r)
    (hrs : r < s) {σ : Finset V} (hσ : σ ∈ closedActiveComplex seed η s) :
    σ.image (deletionMap seed η r hη hr) = σ :=
  TDA.Filtration.SparseRips.deletionMap_image_later seed hη hr hrs hσ

/-- A deletion map sends a face of the closed active complex to one of the next stage when no
deletion occurs between the two scales. -/
theorem image_mem_later_of_noDeletion (seed : V) {η r s : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hgap : NoDeletionBetween seed η r s) {σ : Finset V}
    (hσ : σ ∈ closedActiveComplex seed η r) :
    σ.image (deletionMap seed η r hη.le hr) ∈ closedActiveComplex seed η s :=
  TDA.Filtration.SparseRips.image_mem_later_of_noDeletion seed hη hη' hr hrs hgap hσ

/-- A face together with its projected vertices is a relaxed face. -/
theorem image_union_mem_relaxedComplex {η r : ℝ} (time : V → Option ℝ) (f : V → V)
    (hf : ∀ x, dist x (f x) ≤ weight η (time x) r - weight η (time (f x)) r) {σ : Finset V}
    (hσ : σ ∈ relaxedComplex η time r) : σ.image f ∪ σ ∈ relaxedComplex η time r :=
  TDA.Filtration.SparseRips.image_union_mem_relaxedComplex time f hf hσ

end TDA.Filtration.SparseRips.DecidableEqClientExamples
