import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Topology.Homotopy.Contractible
import TDA.Topology.MultiNerve
import TDA.Simplicial.VertexChainMap

/-!
# Realization and coordinate stars of a labelled simplicial complex

A barycentric point belongs to the realization when its positive support is a face. The
coordinate stars recover the labelled complex as their nerve. For finite labels, each inhabited
intersection indexed by a nonempty set of labels contracts to the barycenter of that face.
-/

namespace TDA.Topology

open Convexity TDA.Simplicial

noncomputable section

variable {V : Type*}

/-- Barycentric probability weights supported on a face of the labelled complex. -/
abbrev Realization (K : PreAbstractSimplicialComplex V) :=
  {p : StdSimplex ℝ V // p.weights.support ∈ K}

namespace Realization

variable {K L M : PreAbstractSimplicialComplex V}

/-- The inclusion of realizations keeps every barycentric coordinate. -/
def incl (h : K ≤ L) : C(Realization K, Realization L) :=
  ⟨fun p => ⟨p.val, h p.property⟩, continuous_subtype_val.subtype_mk _⟩

@[simp] theorem incl_weights (h : K ≤ L) (x : Realization K) (v : V) :
    (incl h x).val.weights v = x.val.weights v := rfl

@[simp] theorem incl_id : incl (le_refl K) = ContinuousMap.id _ := rfl

@[simp] theorem incl_comp (h : K ≤ L) (g : L ≤ M) : (incl g).comp (incl h) = incl (h.trans g) := rfl

/-- For finite labels, the realization carries the subspace topology from the coordinate functions. -/
theorem isEmbedding_weights [Finite V] :
    Topology.IsEmbedding (fun x : Realization K => (x.val.weights : V → ℝ)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ V).comp Topology.IsEmbedding.subtypeVal

/-- The open star of a label consists of the points with positive weight at that label. -/
def coordinateStar (K : PreAbstractSimplicialComplex V) (v : V) : Set (Realization K) :=
  {p | 0 < p.val.weights v}

theorem isOpen_coordinateStar (v : V) : IsOpen (coordinateStar K v) :=
  isOpen_lt continuous_const ((StdSimplex.continuous_weights_apply ℝ v).comp continuous_subtype_val)

theorem mem_coordinateStar_iff (x : Realization K) (v : V) :
    x ∈ coordinateStar K v ↔ v ∈ x.val.weights.support :=
  (lt_iff_le_and_ne.trans (and_iff_right (x.val.weights_nonneg v))).trans
    (ne_comm.trans Finsupp.mem_support_iff.symm)

theorem covers_coordinateStar : Covers (coordinateStar K) Set.univ := by
  intro x _
  obtain ⟨v, hv⟩ := x.val.support_weights_nonempty
  exact ⟨v, (mem_coordinateStar_iff _ _).2 hv⟩

theorem isEmpty_bot : IsEmpty (Realization (⊥ : PreAbstractSimplicialComplex V)) :=
  ⟨fun p => p.property⟩

theorem isEmpty_of_isEmpty [IsEmpty V] : IsEmpty (Realization K) :=
  ⟨fun p => p.val.nonempty.elim isEmptyElim⟩

theorem coordinateStar_eq_empty (v : V) (hv : ({v} : Finset V) ∉ K) : coordinateStar K v = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hv ((K.isRelLowerSet_faces x.property).2
    (Finset.singleton_subset_iff.mpr ((mem_coordinateStar_iff _ _).1 hx)) (Finset.singleton_nonempty _))

variable {J : Finset V}

private theorem subBarycenter_weight (hn : J.Nonempty) {v : V} (hv : v ∈ J) :
    (StdSimplex.subBarycenter (K := ℝ) J hn).weights v = (J.card : ℝ)⁻¹ := by
  classical
  simp [StdSimplex.weights_subBarycenter, Finsupp.single_apply, hv]

private theorem subBarycenter_pos (hn : J.Nonempty) {v : V} (hv : v ∈ J) :
    0 < (StdSimplex.subBarycenter (K := ℝ) J hn).weights v := by
  rw [subBarycenter_weight hn hv]
  exact inv_pos.mpr (by exact_mod_cast hn.card_pos)

private theorem subBarycenter_support (hn : J.Nonempty) :
    (StdSimplex.subBarycenter (K := ℝ) J hn).weights.support = J := by
  ext v
  by_cases hv : v ∈ J
  · simp [Finsupp.mem_support_iff, (subBarycenter_pos hn hv).ne', hv]
  · simp [Finsupp.mem_support_iff, StdSimplex.subBarycenter_weights_apply_eq_zero J hn v hv,
      hv]

/-- The subspace where every label in the finite set has positive weight. -/
abbrev StarIntersection (K : PreAbstractSimplicialComplex V) (J : Finset V) :=
  ↥(interMember (coordinateStar K) J)

/-- The barycenter of a face, viewed in the intersection of its coordinate stars. -/
def faceBarycenter (hJ : J ∈ K) : StarIntersection K J := by
  have hn := (K.isRelLowerSet_faces hJ).1
  exact ⟨⟨StdSimplex.subBarycenter J hn, by rw [subBarycenter_support]; exact hJ⟩,
    (mem_interMember_iff _).2 (fun _ hv => subBarycenter_pos hn hv)⟩

/-- The barycenter assigns weight `1 / J.card` to each vertex of the face. -/
theorem faceBarycenter_weights_of_mem (hJ : J ∈ K) {v : V} (hv : v ∈ J) :
    (faceBarycenter hJ).val.val.weights v = (J.card : ℝ)⁻¹ :=
  subBarycenter_weight (K.isRelLowerSet_faces hJ).1 hv

theorem faceBarycenter_support (hJ : J ∈ K) : (faceBarycenter hJ).val.val.weights.support = J :=
  subBarycenter_support (K.isRelLowerSet_faces hJ).1

/-- A nonempty set of indices has a common star point exactly when it is a face. -/
theorem interMember_nonempty_iff (hn : J.Nonempty) :
    (interMember (coordinateStar K) J).Nonempty ↔ J ∈ K := by
  refine ⟨?_, fun h => ⟨(faceBarycenter h).val, (faceBarycenter h).property⟩⟩
  rintro ⟨p, hp⟩
  exact (K.isRelLowerSet_faces p.property).2
    (fun v hv => (mem_coordinateStar_iff p v).1 ((mem_interMember_iff _).1 hp v hv)) hn

/-- The coordinate-star cover has the original complex as its labelled nerve. -/
theorem nerve_coordinateStar (K : PreAbstractSimplicialComplex V) : nerve (coordinateStar K) = K := by
  ext s
  constructor
  · rintro ⟨hs, p, hp⟩
    exact (interMember_nonempty_iff hs).1 ⟨p, (mem_interMember_iff _).2 hp⟩
  · intro hs
    exact ⟨(K.isRelLowerSet_faces hs).1, (faceBarycenter hs).val,
      (mem_interMember_iff _).1 (faceBarycenter hs).property⟩

private def mix (t : unitInterval) (a b : StdSimplex ℝ V) : StdSimplex ℝ V :=
  convexCombPair (R := ℝ) (unitInterval.symm t) t
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) a b

private theorem mix_coord (t : unitInterval) (a b : StdSimplex ℝ V) (v : V) :
    (mix t a b).weights v = (1 - (t : ℝ)) * a.weights v + (t : ℝ) * b.weights v := by
  simp [mix, unitInterval.coe_symm_eq, StdSimplex.weights_convexCombPair, smul_eq_mul]

private theorem mix_support (t : unitInterval) (x : StarIntersection K J) (hJ : J ∈ K) :
    (mix t x.val.val (faceBarycenter hJ).val.val).weights.support ⊆ x.val.val.weights.support := by
  intro v hv
  by_contra h
  have hvJ : v ∉ J := fun hvJ =>
    h ((mem_coordinateStar_iff _ _).1 ((mem_interMember_iff _).1 x.property v hvJ))
  have hz : x.val.val.weights v = 0 := Finsupp.notMem_support_iff.mp h
  have hb : (faceBarycenter hJ).val.val.weights v = 0 :=
    StdSimplex.subBarycenter_weights_apply_eq_zero J (K.isRelLowerSet_faces hJ).1 v hvJ
  exact Finsupp.mem_support_iff.mp hv (by simp [mix_coord, hz, hb])

private theorem mix_pos (t : unitInterval) (x : StarIntersection K J) (hJ : J ∈ K) {v : V} (hv : v ∈ J) :
    0 < (mix t x.val.val (faceBarycenter hJ).val.val).weights v := by
  have hx : 0 < x.val.val.weights v := (mem_interMember_iff _).1 x.property v hv
  have hb : 0 < (faceBarycenter hJ).val.val.weights v :=
    (mem_interMember_iff _).1 (faceBarycenter hJ).property v hv
  rw [mix_coord]
  rcases eq_or_lt_of_le t.property.1 with ht | ht
  · simp [← ht, hx]
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.property.2) hx.le) (mul_pos ht hb)

private def motion (hJ : J ∈ K) (t : unitInterval) (x : StarIntersection K J) : StarIntersection K J := by
  let w := mix t x.val.val (faceBarycenter hJ).val.val
  exact ⟨⟨w, (K.isRelLowerSet_faces x.val.property).2 (mix_support t x hJ) w.support_weights_nonempty⟩,
    (mem_interMember_iff _).2 (fun _ hv => mix_pos t x hJ hv)⟩

private theorem continuous_motion [Finite V] (hJ : J ∈ K) :
    Continuous fun z : unitInterval × StarIntersection K J => motion hJ z.1 z.2 := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous_iff.mpr
  apply continuous_pi
  intro v
  change Continuous fun z : unitInterval × StarIntersection K J =>
    (mix z.1 z.2.val.val (faceBarycenter hJ).val.val).weights v
  simp only [mix_coord]
  fun_prop

/-- For finite labels, the straight-line contraction of a face’s star intersection to its
barycenter. -/
def contraction [Finite V] (hJ : J ∈ K) : (ContinuousMap.id (StarIntersection K J)).Homotopy
    (ContinuousMap.const _ (faceBarycenter hJ)) where
  toFun z := motion hJ z.1 z.2
  continuous_toFun := continuous_motion hJ
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    apply StdSimplex.ext
    ext v
    change (mix 0 _ _).weights v = _
    simp [mix_coord]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    apply StdSimplex.ext
    ext v
    change (mix 1 _ _).weights v = _
    simp [mix_coord]

theorem contraction_weights [Finite V] (hJ : J ∈ K) (t : unitInterval)
    (x : StarIntersection K J) (v : V) :
    ((contraction hJ) (t, x)).val.val.weights v =
      (1 - (t : ℝ)) * x.val.val.weights v + (t : ℝ) * (faceBarycenter hJ).val.val.weights v :=
  mix_coord _ _ _ _

theorem contraction_support_subset [Finite V] (hJ : J ∈ K) (t : unitInterval)
    (x : StarIntersection K J) :
    ((contraction hJ) (t, x)).val.val.weights.support ⊆ x.val.val.weights.support :=
  mix_support t x hJ

theorem contractibleSpace_starIntersection [Finite V] (hJ : J ∈ K) :
    ContractibleSpace (StarIntersection K J) :=
  (contractible_iff_id_nullhomotopic _).2 ⟨faceBarycenter hJ, ⟨contraction hJ⟩⟩

@[simp] theorem pullback_coordinateStar (h : K ≤ L) :
    pullback (incl h) (coordinateStar L) = coordinateStar K := rfl

@[simp] theorem preimage_interMember (h : K ≤ L) (J : Finset V) :
    (incl h) ⁻¹' interMember (coordinateStar L) J = interMember (coordinateStar K) J := by
  ext p
  simp only [Set.mem_preimage, mem_interMember_iff]
  rfl

/-- The map of labelled nerves induced by the continuous inclusion of realizations. -/
def starNerveInclusion (h : K ≤ L) : VertexMap (nerve (coordinateStar K)) (nerve (coordinateStar L)) :=
  inclusionVertexMap (nerve_pullback_le (incl h) (coordinateStar L))

/-- Identifying the two star nerves with their complexes carries the cover map to the original inclusion. -/
theorem starNerveInclusion_naturality (h : K ≤ L) :
    VertexMap.comp (starNerveInclusion h) (inclusionVertexMap (nerve_coordinateStar L).le) =
      VertexMap.comp (inclusionVertexMap (nerve_coordinateStar K).le) (inclusionVertexMap h) := by
  ext v
  rfl

end Realization

end

end TDA.Topology
