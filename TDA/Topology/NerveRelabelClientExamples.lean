import TDA.Topology.MultiNerveMap
import TDA.Topology.MulticoverCover

/-!
# Client statements of the nerve relabelling lemmas

Regression fixtures for #1281, family 11 of the downstream-use audit (#1207). Each statement
is written as a downstream client writes it: the file opens no scope and declares no instance,
and the finite images `Finset.image` on `Fin 3`, `Bool` and `Fin 4` are elaborated with the
decidable equality of the index type; every proof is a direct application of a library
theorem.

* Relabelling the index set of a cover family by an equivalence of `Fin 3` and of `Bool`.
* The inclusion of intersections, the support, the faces and the projection of the multinerve
  map of a selected refinement on `Fin 3`.
* The nerve of the large-face cover of a planar point cloud on `Fin 4`.
-/

namespace TDA.Topology.NerveRelabelClientExamples

/-- Relabelling a cover family of the line by an equivalence of `Fin 3`. -/
theorem fin_three_mem_nerve_relabel (U : CoverFamily ℝ (Fin 3)) (e : Fin 3 ≃ Fin 3)
    (s : Finset (Fin 3)) :
    s ∈ nerve (fun i => U (e i)) ↔ s.image e ∈ nerve U :=
  mem_nerve_relabel_iff e U s

/-- Relabelling a cover family by an equivalence of `Bool`. -/
theorem bool_mem_nerve_relabel {X : Type} (U : CoverFamily X Bool) (e : Bool ≃ Bool)
    (s : Finset Bool) :
    s ∈ nerve (fun i => U (e i)) ↔ s.image e ∈ nerve U :=
  mem_nerve_relabel_iff e U s

/-- The intersection over a finite index set lies in the intersection over its image under a
selected refinement of cover families indexed by `Fin 3`. -/
theorem fin_three_interMember_image_subset {X : Type} (U V : CoverFamily X (Fin 3))
    (R : Refinement U V) (σ : Finset (Fin 3)) :
    interMember U σ ⊆ interMember V (σ.image R.selector) :=
  interMember_image_subset R σ

/-- The support of the image of a multinerve cell is the image of its support. -/
theorem fin_three_support_multiNerveMap (U V : CoverFamily ℝ (Fin 3))
    (R : Refinement U V) (a : MultiNerveCell U) :
    (multiNerveMap R a).support = a.support.image R.selector :=
  support_multiNerveMap_eq_image R a

/-- The multinerve map sends the face over `τ` to the face over `τ.image R.selector`. -/
theorem fin_three_multiNerveMap_face (U V : CoverFamily ℝ (Fin 3)) (R : Refinement U V)
    (a : MultiNerveCell U) (τ : Finset (Fin 3)) (hτ : τ.Nonempty) (hτa : τ ⊆ a.support) :
    multiNerveMap R (a.face τ hτ hτa) =
      (multiNerveMap R a).face (τ.image R.selector) (hτ.image _)
        (by
          rw [support_multiNerveMap_eq_image]
          exact Finset.image_subset_image hτa) :=
  multiNerveMap_face_image R a τ hτ hτa

/-- The projection of the image of a multinerve cell is the image of the projected face under
the nerve map. -/
theorem fin_three_projection_multiNerveMap (U V : CoverFamily ℝ (Fin 3)) (R : Refinement U V)
    (a : MultiNerveCell U) :
    (projection V (multiNerveMap R a)).1 = (projection U a).1.image (nerveMap R) :=
  projection_multiNerveMap_eq_image R a

/-- The faces of the nerve of the large-face cover of a planar point cloud on `Fin 4`. -/
theorem fin_four_mem_largeFaceNerve (p : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (a : TDA.Filtration.SubdivisionRips.Index) (S : Finset (Finset (Fin 4))) :
    S ∈ nerve (MeasureBifiltration.largeFaceCover p a) ↔
      S.Nonempty ∧ (∀ s ∈ S, s ∈ TDA.Filtration.SubdivisionRips.openCech p
          (TDA.Filtration.SubdivisionRips.radius a) ∧
        TDA.Filtration.SubdivisionRips.mass a ≤ (s.card : ℝ) / Fintype.card (Fin 4)) ∧
      S.biUnion id ∈ TDA.Filtration.SubdivisionRips.openCech p
        (TDA.Filtration.SubdivisionRips.radius a) :=
  MeasureBifiltration.mem_largeFaceNerve_iff p a S

end TDA.Topology.NerveRelabelClientExamples
