import TDA.Topology.NerveStarLabeling
import TDA.Topology.ConeCarrierComparison

/-!
# Inclusion of nerves of nested convex covers

The common star labeling supplies a homology inverse after subdivision. Naturality of last
vertices identifies both composites with the identities on the original nerves.
-/

namespace TDA.Topology.ConvexNerve

open CategoryTheory TDA.Simplicial TDA.Topology.SubdivisionRealization
noncomputable section
universe u

open scoped TDA.Topology.SubdivisionRealization

variable {I : Type u} [Fintype I] [LinearOrder I] [Nonempty I]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : LinearOrder (Finset I) := faceLinearOrder I

/-- Intersect the faces of a flag to obtain its least face when the flag is nonempty. -/
def leastFlagFace (F : Finset (Finset I)) := Finset.univ.filter (fun i => ∀ A ∈ F, i ∈ A)

omit [Nonempty I] in
/-- The intersection belongs to a flag and is contained in each member. -/
theorem leastFlagFace_spec {K : PreAbstractSimplicialComplex I} {F : Finset (Finset I)}
    (hf : F ∈ barycentricSubdivision K) : leastFlagFace F ∈ F ∧ ∀ A ∈ F, leastFlagFace F ⊆ A := by
  obtain ⟨S, hS, hmin⟩ := exists_least_face hf
  have eqS : leastFlagFace F = S := by
    ext i
    simp only [leastFlagFace, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h S hS, fun hi A hA => hmin A hA hi⟩
  exact eqS ▸ ⟨hS, hmin⟩

/-- The signed chain map of a subordinate labeling is homotopic to the natural last-vertex map. -/
theorem chainHomotopy_labeling_lastVertex (U : I → Set E) (hc : ∀ i, Convex ℝ (U i)) (p : Finset I → E)
    (hp : ∀ A ∈ nerve U, ∀ i ∈ A, p A ∈ U i)
    (n : ℕ) (a : VertexMap (subdividedFlags (nerve U) n) (nerve U))
    (ha : ∀ T ∈ subdividedFlags (nerve U) n, ∀ v ∈ T, ∀ w ∈ T, vertexPosition p n w ∈ U (a v))
    (R : Type*) [Ring R] :
    Nonempty (Homotopy (simplicialChainMap R a) (simplicialChainMap R (flagLastVertex (nerve U) n))) := by
  classical
  let N := nerve U
  let Q := subdividedFlags N n
  let A := originalFace (V := Finset I) n
  -- The least and greatest original faces of the supporting flag bound both label maps.
  let J (T : Finset (Vertex (Finset I) n)) := leastFlagFace (A T)
  let B (T : Finset (Vertex (Finset I) n)) := flagUnion (A T)
  have anc (T) (hT : T ∈ Q) := originalFace_mem (barycentricSubdivision N) n T hT
  have hJ (T) (hT : T ∈ Q) := (leastFlagFace_spec (anc T hT)).1
  have hJne (T) (hT : T ∈ Q) : (J T).Nonempty :=
    (N.isRelLowerSet_faces ((anc T hT).2.1 _ (hJ T hT)).1).1
  let j (T : Finset (Vertex (Finset I) n)) : I := if h : (J T).Nonempty then h.choose else Classical.choice ‹Nonempty I›
  have jmem (T) (hT : T ∈ Q) : j T ∈ J T := by
    simpa only [j, dite_eq_left (hJne T hT)] using (hJne T hT).choose_spec
  have anti (S) (hs : S ∈ Q) (T) (ht : T ∈ Q) (hst : S ⊆ T) : J T ⊆ J S :=
    (leastFlagFace_spec (anc T ht)).2 _ (originalFace_mono n hst (hJ S hs))
  have subB (S) (hs : S ∈ Q) (T) (_ : T ∈ Q) (hst : S ⊆ T) : J S ⊆ B T :=
    subset_flagUnion (originalFace_mono n hst (hJ S hs))
  have hB (T) (hT : T ∈ Q) : B T ∈ N := ((anc T hT).2.1 _ (flagUnion_mem (anc T hT))).1
  have geom (S) (hs : S ∈ Q) (w) (hw : w ∈ S) (i) (hi : i ∈ J S) : vertexPosition p n w ∈ U i :=
    vertexPosition_mem_convex (barycentricSubdivision N) p (U i) (hc i) n S hs
      (fun G hG => hp G ((anc S hs).2.1 G hG).1 i ((leastFlagFace_spec (anc S hs)).2 G hG hi)) w hw
  have top (T) (hT : T ∈ Q) (v) (hv : v ∈ T) : flagLastVertex N n v ∈ B T := by
    have h := lastVertexLabel_mem (barycentricSubdivision N) n T hT v hv
    have hn := (N.isRelLowerSet_faces ((anc T hT).2.1 _ h).1).1
    change lastVertex (iteratedLastVertex (barycentricSubdivision N) n v) ∈ B T
    rw [iteratedLastVertex_apply, lastVertex_of_nonempty _ hn]
    exact subset_flagUnion h (Finset.max'_mem _ hn)
  -- For S ⊆ T, a vertex of S witnesses the labels of T together with J S.
  -- Last vertices and J S lie in the greatest face B T.
  obtain ⟨b, hf, hg⟩ := exists_contiguous_apexMap a (flagLastVertex N n) J j jmem anti
    (fun S hs T ht hst => by
      let : DecidableEq I := Classical.decEq I
      obtain ⟨w, hw⟩ := (Q.isRelLowerSet_faces hs).1
      have hne := (Q.isRelLowerSet_faces ht).1.image a
      refine ⟨hne, hne.mono Finset.subset_union_left, vertexPosition p n w, ?_⟩
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
        exact ha T ht v hv w (hst hw)
      · exact geom S hs w hw i hi)
    (fun S hs T ht hst => by
      let : DecidableEq I := Classical.decEq I
      have hn := (Q.isRelLowerSet_faces ht).1.image (flagLastVertex N n)
      refine ⟨hn, (N.isRelLowerSet_faces (hB T ht)).2 (Finset.union_subset ?_ (subB S hs T ht hst))
        (hn.mono Finset.subset_union_left)⟩
      intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact top T ht v hv)
  let : LinearOrder (Finset (Vertex (Finset I) n)) := faceLinearOrder _
  exact chainHomotopy_of_contiguous_after_lastVertex R a (flagLastVertex N n) b hf hg

/-- One common subdivision and labeling restrict literally and compare to both last-vertex maps
on signed chains. -/
theorem exists_common_chain_comparisons {C D : I → Set E} (ho : ∀ i, IsOpen (C i))
    (hC : ∀ i, Convex ℝ (C i)) (hD : ∀ i, Convex ℝ (D i))
    (h : ∀ i, C i ⊆ D i) (hu : (⋃ i, C i) = ⋃ i, D i) :
    let K := nerve C
    let L := nerve D
    let i : VertexMap K L := inclusionVertexMap (nerve_mono h)
    ∃ (n : ℕ) (a : VertexMap (subdividedFlags L n) K),
      let j : VertexMap (subdividedFlags K n) (subdividedFlags L n) :=
        inclusionVertexMap (complex_mono (subdivision_mono (nerve_mono h)) n)
      let aK := VertexMap.comp j a
      let aL := VertexMap.comp a i
      (∀ v, aK v = a v ∧ aL v = a v) ∧ VertexMap.comp j aL = VertexMap.comp aK i ∧
      ∀ (R : Type*) [Ring R],
        Nonempty (Homotopy (simplicialChainMap R aK) (simplicialChainMap R (flagLastVertex K n))) ∧
        Nonempty (Homotopy (simplicialChainMap R aL) (simplicialChainMap R (flagLastVertex L n))) := by
  obtain ⟨p, hpC, hpD, n, a, ha, _⟩ := exists_common_labeling C D ho hD h hu
  refine ⟨n, a, fun _ => ⟨rfl, rfl⟩, ?_, ?_⟩
  · ext v
    rfl
  · intro R _
    exact ⟨chainHomotopy_labeling_lastVertex C hC p hpC n _ (fun T ht v hv w hw =>
      ha T (complex_mono (subdivision_mono (nerve_mono h)) n ht) v hv w hw) R,
      chainHomotopy_labeling_lastVertex D hD p hpD n _ (fun T ht v hv w hw => h _ (ha T ht v hv w hw)) R⟩

private theorem isIso_of_comparison_square {A : Type*} [Category* A]
    (X Y X' Y' : A) (i : X ⟶ Y) (j : X' ⟶ Y') (a : Y' ⟶ X)
    (lX : X' ≅ X) (lY : Y' ≅ Y)
    (hnat : j ≫ lY.hom = lX.hom ≫ i)
    (hL : a ≫ i = lY.hom) (hK : j ≫ a = lX.hom) : IsIso i := by
  refine ⟨⟨lY.inv ≫ a, ?_, ?_⟩⟩
  · apply (cancel_epi lX.hom).mp
    simp only [← Category.assoc, ← hnat]
    simp [Category.assoc, hK]
  · simp [Category.assoc, hL]

private theorem isIso_inhabited {C D : I → Set E} (ho : ∀ i, IsOpen (C i))
    (hC : ∀ i, Convex ℝ (C i)) (hD : ∀ i, Convex ℝ (D i))
    (h : ∀ i, C i ⊆ D i) (hu : (⋃ i, C i) = ⋃ i, D i) (R : Type*) [Ring R] (k : ℕ) :
    IsIso (simplicialHomologyIncl R (nerve_mono h) k) := by
  obtain ⟨n, a, _, _, chains⟩ := exists_common_chain_comparisons ho hC hD h hu
  let K := nerve C
  let L := nerve D
  let i : VertexMap K L := inclusionVertexMap (nerve_mono h)
  let j : VertexMap (subdividedFlags K n) (subdividedFlags L n) :=
        inclusionVertexMap (complex_mono (subdivision_mono (nerve_mono h)) n)
  obtain ⟨hcK, hcL⟩ := chains R
  let := isIso_flagLastVertex K R k n
  let := isIso_flagLastVertex L R k n
  rw [← simplicialHomologyMap_inclusion R (nerve_mono h) k]
  change IsIso (simplicialHomologyMap R i k)
  apply isIso_of_comparison_square _ _ _ _ _ (simplicialHomologyMap R j k) (simplicialHomologyMap R a k)
    (asIso (simplicialHomologyMap R (flagLastVertex K n) k)) (asIso (simplicialHomologyMap R (flagLastVertex L n) k))
  · change simplicialHomologyMap R j k ≫ simplicialHomologyMap R (flagLastVertex L n) k =
      simplicialHomologyMap R (flagLastVertex K n) k ≫ simplicialHomologyMap R i k
    rw [← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp]
    exact congrArg (fun f => simplicialHomologyMap R f k) (flagLastVertex_naturality (nerve_mono h) n)
  · rw [← simplicialHomologyMap_comp]
    exact hcL.some.homologyMap_eq k
  · rw [← simplicialHomologyMap_comp]
    exact hcK.some.homologyMap_eq k

omit [Nonempty I] in

/-- For nested finite convex families with equal union and open smaller members, the actual
same-label nerve inclusion induces an isomorphism in every degree over every ring. -/
theorem isIso_simplicialHomologyIncl {C D : I → Set E} (ho : ∀ i, IsOpen (C i))
    (hC : ∀ i, Convex ℝ (C i)) (hD : ∀ i, Convex ℝ (D i))
    (h : ∀ i, C i ⊆ D i) (hu : (⋃ i, C i) = ⋃ i, D i) (R : Type*) [Ring R] (k : ℕ) :
    IsIso (simplicialHomologyIncl R (nerve_mono h) k) := by
  cases isEmpty_or_nonempty I with
  | inl empty =>
    let := empty
    apply simplicialHomologyIncl_isIso_of_eq
    apply le_antisymm (nerve_mono h)
    exact fun _ hD => hD.1.elim (fun v _ => isEmptyElim v)
  | inr ne =>
    let := ne
    exact isIso_inhabited ho hC hD h hu R k

end
end TDA.Topology.ConvexNerve
