import TDA.Simplicial.BarycentricHomology
import TDA.Simplicial.ContiguityHomotopy

/-!
# Signed comparison through nested cone carriers

On a flag the apex labels lie in its least required face. Each map on its greatest member is
carried by that cone, giving two prisms with the same endpoint.
-/

namespace TDA.Topology.ConvexNerve

open CategoryTheory TDA.Simplicial
noncomputable section
universe u

variable {I : Type u}
variable {K L : PreAbstractSimplicialComplex I}

/-- Faces that still form a face on adjoining all labels of `J`. -/
def coneCarrier [DecidableEq I] (K : PreAbstractSimplicialComplex I) (J : Finset I) : PreAbstractSimplicialComplex I where
  faces := {S | S.Nonempty ∧ S ∪ J ∈ K}
  isRelLowerSet_faces := by
    intro S hS
    exact ⟨hS.1, fun T hTS hT => ⟨hT, (K.isRelLowerSet_faces hS.2).2
      (Finset.union_subset_union_left hTS) (hT.mono Finset.subset_union_left)⟩⟩

/-- A larger target complex and a smaller required face enlarge the carrier. -/
theorem coneCarrier_mono [DecidableEq I] (h : K ≤ L) {A B : Finset I} (hAB : A ⊆ B) :
    coneCarrier K B ≤ coneCarrier L A := by
  intro S hS
  exact ⟨hS.1, (L.isRelLowerSet_faces (h hS.2)).2
    (Finset.union_subset_union_right hAB) (hS.1.mono Finset.subset_union_left)⟩

/-- Every vertex of the required face is an apex of its carrier. -/
theorem coneCarrier_apex [LinearOrder I] {J : Finset I} (hJ : J ∈ K) {i : I} (hi : i ∈ J) :
    ApexInsertionClosed (coneCarrier K J) i := by
  constructor
  · exact ⟨Finset.singleton_nonempty _, by simpa [Finset.singleton_union, hi] using hJ⟩
  · intro S hS
    refine ⟨Finset.insert_nonempty _ _, ?_⟩
    simpa only [Finset.insert_union, Finset.insert_eq_of_mem (Finset.mem_union_right S hi)] using hS.2

section Prism
variable {V I : Type u} [LinearOrder V] [Fintype V] [Nonempty V]

variable {Q : PreAbstractSimplicialComplex V} {N : PreAbstractSimplicialComplex I}

/-- A common apex map on subdivided flags compares two maps carried by nested face cones. -/
theorem exists_contiguous_apexMap [DecidableEq I] (f g : VertexMap Q N) (J : Finset V → Finset I)
    (j : Finset V → I) (hj : ∀ S ∈ Q, j S ∈ J S)
    (hanti : ∀ S ∈ Q, ∀ T ∈ Q, S ⊆ T → J T ⊆ J S)
    (hf : ∀ S ∈ Q, ∀ T ∈ Q, S ⊆ T → T.image f ∈ coneCarrier N (J S))
    (hg : ∀ S ∈ Q, ∀ T ∈ Q, S ⊆ T → T.image g ∈ coneCarrier N (J S)) :
    ∃ b : VertexMap (barycentricSubdivision Q) N,
      Contiguous (VertexMap.comp (lastVertexMap Q) f) b ∧
      Contiguous (VertexMap.comp (lastVertexMap Q) g) b := by
  -- Vertex maps take images with `Classical.decEq`; decidable equality is a subsingleton.
  obtain rfl : ‹DecidableEq I› = Classical.decEq I := Subsingleton.elim _ _
  classical
  have bounds (F : Finset (Finset V)) (hF : F ∈ barycentricSubdivision Q) :
      (F.image (fun A => f (lastVertex A)) ∪ F.image j ∈ N) ∧
      (F.image (fun A => g (lastVertex A)) ∪ F.image j ∈ N) := by
    obtain ⟨S, hS, T, hT, hst⟩ := exists_flag_extrema hF
    have mem (A) (hA : A ∈ F) : A ∈ Q := (hF.2.1 A hA).1
    have hv (A) (hA : A ∈ F) : lastVertex A ∈ T := by
      have hn := (Q.isRelLowerSet_faces (mem A hA)).1
      rw [lastVertex_of_nonempty A hn]
      exact (hst A hA).2 (Finset.max'_mem A hn)
    have H (u : V → I) : F.image (fun A => u (lastVertex A)) ⊆ T.image u := by
      intro i hi
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image_of_mem u (hv A hA)
    have hjS : F.image j ⊆ J S := by
      intro i hi
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hi
      exact hanti S (mem S hS) A (mem A hA) (hst A hA).1 (hj A (mem A hA))
    have hST := (hst S hS).2
    have hn := hF.1.image j
    have carried (u : V → I) (hu : T.image u ∈ coneCarrier N (J S)) :
        F.image (fun A => u (lastVertex A)) ∪ F.image j ∈ N :=
      (N.isRelLowerSet_faces hu.2).2 (Finset.union_subset_union (H u) hjS)
        (hn.mono Finset.subset_union_right)
    exact ⟨carried f (hf S (mem S hS) T (mem T hT) hST),
      carried g (hg S (mem S hS) T (mem T hT) hST)⟩
  let b : VertexMap (barycentricSubdivision Q) N := ⟨j, fun F hF =>
    (N.isRelLowerSet_faces (bounds F hF).1).2 Finset.subset_union_right (hF.1.image j)⟩
  exact ⟨b, fun F hF => (bounds F hF).1, fun F hF => (bounds F hF).2⟩

end Prism

section Chains
variable {V I : Type u} [Fintype V] [LinearOrder V] [Nonempty V] [LinearOrder I] [LinearOrder (Finset V)]
variable {Q : PreAbstractSimplicialComplex V} {N : PreAbstractSimplicialComplex I}

/-- Descend two signed prism homotopies through the subdivision chain section. -/
theorem chainHomotopy_of_contiguous_after_lastVertex (R : Type*) [Ring R] (f g : VertexMap Q N)
    (b : VertexMap (barycentricSubdivision Q) N)
    (hf : Contiguous (VertexMap.comp (lastVertexMap Q) f) b)
    (hg : Contiguous (VertexMap.comp (lastVertexMap Q) g) b) :
    Nonempty (Homotopy (simplicialChainMap R f) (simplicialChainMap R g)) := by
  have h := (((hf.chainHomotopy R).trans (hg.chainHomotopy R).symm).compLeft (barycentricSubdivisionChainMap R Q))
  rw [simplicialChainMap_comp, simplicialChainMap_comp, ← Category.assoc, ← Category.assoc] at h
  change Homotopy ((barycentricSubdivisionChainMap R Q ≫ lastVertexChainMap R Q) ≫ _)
    ((barycentricSubdivisionChainMap R Q ≫ lastVertexChainMap R Q) ≫ _) at h
  rw [barycentricSubdivisionChainMap_lastVertex_eq_id, Category.id_comp, Category.id_comp] at h
  exact ⟨h⟩

end Chains

end
end TDA.Topology.ConvexNerve
