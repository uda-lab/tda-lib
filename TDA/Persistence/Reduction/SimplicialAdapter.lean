import TDA.Persistence.Reduction.FilteredNormalForm
import TDA.Persistence.FaceOrderTemplate
import TDA.Simplicial.FiniteHomology

/-!
# Face coordinates for simplicial reduction

The index of a face is zero based, while the first prefix containing it has
stage number one greater than its index.  The degree records the cardinality
of a nonempty face, not that of an ambient vertex set.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u w

namespace TDA.Persistence.Reduction

open TDA.Simplicial TDA.Filtration Module

variable {V : Type u} [LinearOrder V]
variable {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TotalFace K)]
variable {f : FilterFunction K α}

/-- The homological degree of an enumerated nonempty face. -/
def faceDegree (e : CompatibleOrder f) (i : Fin (faceCount K)) : ℕ :=
  (e.enum i).val.card - 1

/-- A face's vertex count is exactly one more than its degree. -/
theorem face_card_eq_degree_add_one (e : CompatibleOrder f)
    (i : Fin (faceCount K)) :
    (e.enum i).val.card = faceDegree e i + 1 := by
  have hpos : 0 < (e.enum i).val.card :=
    Finset.card_pos.mpr ((K.isRelLowerSet_faces (e.enum i).property).1)
  simp only [faceDegree]
  omega

/-- Convert an enumerated face to the degreewise face subtype. -/
def indexedFace (e : CompatibleOrder f) (i : Fin (faceCount K))
    (p : ℕ) (hp : faceDegree e i = p) : Face K p :=
  ⟨(e.enum i).val, (e.enum i).property,
    by rw [face_card_eq_degree_add_one e i, hp]⟩

/-- The index of a face, with no ambient finite vertex hypothesis. -/
def degreewiseFaceIndex (e : CompatibleOrder f) (p : ℕ) (s : Face K p) :
    Fin (faceCount K) :=
  e.enum.symm ⟨s.1, s.2.1⟩

theorem degreewiseFaceIndex_degree (e : CompatibleOrder f) (p : ℕ)
    (s : Face K p) : faceDegree e (degreewiseFaceIndex e p s) = p := by
  have he : e.enum (degreewiseFaceIndex e p s) = (⟨s.1, s.2.1⟩ : TotalFace K) :=
    e.enum.apply_symm_apply _
  have hc := face_card_eq_degree_add_one e (degreewiseFaceIndex e p s)
  rw [he] at hc
  have hs := s.2.2
  simp only at hc
  omega

theorem degreewiseFaceIndex_indexedFace (e : CompatibleOrder f)
    (i : Fin (faceCount K)) (p : ℕ) (hp : faceDegree e i = p) :
    degreewiseFaceIndex e p (indexedFace e i p hp) = i := by
  exact e.enum.symm_apply_apply i

theorem indexedFace_degreewiseFaceIndex (e : CompatibleOrder f)
    (p : ℕ) (s : Face K p) :
    indexedFace e (degreewiseFaceIndex e p s) p
      (degreewiseFaceIndex_degree e p s) = s := by
  apply Subtype.ext
  change (e.enum (e.enum.symm ⟨s.1, s.2.1⟩)).val = s.1
  exact congrArg Subtype.val (e.enum.apply_symm_apply ⟨s.1, s.2.1⟩)

/-- A face with index below `t` is precisely a face of the prefix. -/
def prefixIndexedFace (e : CompatibleOrder f) (t p : ℕ)
    (i : {i : Fin (faceCount K) // i.val < t ∧ faceDegree e i = p}) :
    Face (e.prefixComplex t) p :=
  ⟨(e.enum i.1).val,
    (e.mem_prefixComplex t _).mpr
      ⟨(e.enum i.1).property, by simpa using i.2.1⟩,
    by rw [face_card_eq_degree_add_one e i.1, i.2.2]⟩

/-- The inverse of `prefixIndexedFace` uses membership in the prefix. -/
noncomputable def prefixFaceIndex (e : CompatibleOrder f) (t p : ℕ)
    (s : Face (e.prefixComplex t) p) :
    {i : Fin (faceCount K) // i.val < t ∧ faceDegree e i = p} := by
  classical
  let hsK : s.1 ∈ K := Classical.choose ((e.mem_prefixComplex t s.1).mp s.2.1)
  have hidx := Classical.choose_spec ((e.mem_prefixComplex t s.1).mp s.2.1)
  let i := e.enum.symm ⟨s.1, hsK⟩
  refine ⟨i, hidx, ?_⟩
  have hc := face_card_eq_degree_add_one e i
  have he : e.enum i = ⟨s.1, hsK⟩ := e.enum.apply_symm_apply _
  rw [he] at hc
  have hs := s.2.2
  simp only at hc
  omega

/-- Every degreewise prefix basis is exactly an indexed subset of all faces. -/
noncomputable def prefixFaceEquiv (e : CompatibleOrder f) (t p : ℕ) :
    {i : Fin (faceCount K) // i.val < t ∧ faceDegree e i = p} ≃
      Face (e.prefixComplex t) p where
  toFun := prefixIndexedFace e t p
  invFun := prefixFaceIndex e t p
  left_inv := by
    intro i
    apply Subtype.ext
    change e.enum.symm (e.enum i.1) = i.1
    exact e.enum.symm_apply_apply i.1
  right_inv := by
    intro s
    apply Subtype.ext
    change (e.enum (e.enum.symm
      ⟨s.1, Classical.choose ((e.mem_prefixComplex t s.1).mp s.2.1)⟩)).val = s.1
    exact congrArg Subtype.val (e.enum.apply_symm_apply _)

noncomputable instance prefixFaceFinite (e : CompatibleOrder f) (t p : ℕ) :
    Finite (Face (e.prefixComplex t) p) :=
  Finite.of_equiv _ (prefixFaceEquiv e t p)

variable (k : Type u) [Field k] [DecidableEq k]

/-- All face coordinates supported in the degree-`p` prefix. -/
noncomputable def prefixDegreeSpace (e : CompatibleOrder f) (t p : ℕ) :
    Submodule k (Fin (faceCount K) → k) :=
  Pi.spanSubset k {i | i.val < t ∧ faceDegree e i = p}

/-- The coordinate submodule is exactly simultaneous prefix support and
homogeneous degree, with no truncated subtraction in the degree condition. -/
theorem mem_prefixDegreeSpace_iff (e : CompatibleOrder f)
    (t p : ℕ) (x : Fin (faceCount K) → k) :
    x ∈ prefixDegreeSpace k e t p ↔
      PrefixSupported t x ∧ Homogeneous (faceDegree e) p x := by
  rw [prefixDegreeSpace, Pi.mem_spanSubset_iff]
  constructor
  · intro hx
    constructor
    · intro i hi
      exact hx i (by simp; omega)
    · intro i hi
      exact hx i (by simp [hi])
  · rintro ⟨hpre, hdeg⟩ i hi
    by_cases ht : i.val < t
    · exact hdeg i (by
        intro he
        exact hi ⟨ht, he⟩)
    · exact hpre i (by omega)

/-- Extend coordinates on the indexed basis by zero to all faces. -/
noncomputable def extendPrefixCoordinates (e : CompatibleOrder f) (t p : ℕ) :
    ({i : Fin (faceCount K) // i.val < t ∧ faceDegree e i = p} → k) ≃ₗ[k]
      prefixDegreeSpace k e t p where
  toFun x := ⟨fun i => if h : i.val < t ∧ faceDegree e i = p then x ⟨i, h⟩ else 0,
    by
      rw [prefixDegreeSpace, Pi.mem_spanSubset_iff]
      intro i hi
      have hi' : ¬ (i.val < t ∧ faceDegree e i = p) := hi
      simp [hi']⟩
  invFun x i := x.1 i.1
  left_inv := by
    intro x
    funext i
    simp [i.2]
  right_inv := by
    intro x
    apply Subtype.ext
    funext i
    by_cases hi : i.val < t ∧ faceDegree e i = p
    · simp [hi]
    · have hz : x.1 i = 0 :=
        (Pi.mem_spanSubset_iff.mp x.2) i hi
      simp [hi, hz]
  map_add' := by
    intro x y
    apply Subtype.ext
    funext i
    by_cases hi : i.val < t ∧ faceDegree e i = p <;> simp [hi]
  map_smul' := by
    intro a x
    apply Subtype.ext
    funext i
    by_cases hi : i.val < t ∧ faceDegree e i = p <;> simp [hi]

/-- Chains of every prefix and degree in the common all-face coordinates. -/
noncomputable def prefixChainEquiv (e : CompatibleOrder f) (t p : ℕ) :
    Chain (e.prefixComplex t) k p ≃ₗ[k] prefixDegreeSpace k e t p := by
  letI : Finite (Face (e.prefixComplex t) p) :=
    Finite.of_equiv _ (prefixFaceEquiv e t p)
  exact ((chainCoordinates (e.prefixComplex t) k p).trans
    (LinearEquiv.funCongrLeft k k (prefixFaceEquiv e t p))).trans
      (extendPrefixCoordinates k e t p)

/-- The coordinate of a chain is its coefficient at the corresponding face. -/
theorem prefixChainEquiv_apply (e : CompatibleOrder f) (t p : ℕ)
    (c : Chain (e.prefixComplex t) k p) (i : Fin (faceCount K))
    (hi : i.val < t ∧ faceDegree e i = p) :
    (prefixChainEquiv k e t p c).1 i = c (prefixIndexedFace e t p ⟨i, hi⟩) := by
  simp only [prefixChainEquiv, LinearEquiv.trans_apply,
    LinearEquiv.funCongrLeft_apply]
  simp [extendPrefixCoordinates, hi, chainCoordinates_apply, prefixFaceEquiv]

/-- Outside the matching degreewise prefix, the coordinate vanishes. -/
theorem prefixChainEquiv_apply_zero (e : CompatibleOrder f) (t p : ℕ)
    (c : Chain (e.prefixComplex t) k p) (i : Fin (faceCount K))
    (hi : ¬ (i.val < t ∧ faceDegree e i = p)) :
    (prefixChainEquiv k e t p c).1 i = 0 :=
  Pi.mem_spanSubset_iff.mp (prefixChainEquiv k e t p c).2 i hi

/-- A basis simplex occupies exactly its own zero-based face coordinate. -/
theorem prefixChainEquiv_single_apply (e : CompatibleOrder f) (t p : ℕ)
    (s : Face (e.prefixComplex t) p) (a : k)
    (i : Fin (faceCount K)) :
    (prefixChainEquiv k e t p (Finsupp.single s a)).1 i =
      if i = (prefixFaceIndex e t p s).1 then a else 0 := by
  classical
  by_cases hi : i.val < t ∧ faceDegree e i = p
  · rw [prefixChainEquiv_apply k e t p _ i hi]
    have he : prefixIndexedFace e t p ⟨i, hi⟩ = s ↔
        i = (prefixFaceIndex e t p s).1 := by
      constructor
      · intro h
        have := congrArg (prefixFaceIndex e t p) h
        have hh : prefixFaceIndex e t p (prefixIndexedFace e t p ⟨i, hi⟩) =
            ⟨i, hi⟩ := (prefixFaceEquiv e t p).left_inv ⟨i, hi⟩
        rw [hh] at this
        exact congrArg Subtype.val this
      · intro h
        have ht : (⟨i, hi⟩ : {q : Fin (faceCount K) //
            q.val < t ∧ faceDegree e q = p}) = prefixFaceIndex e t p s :=
          Subtype.ext h
        rw [ht]
        exact (prefixFaceEquiv e t p).right_inv s
    by_cases h : i = (prefixFaceIndex e t p s).1
    · have hf : s = prefixIndexedFace e t p ⟨i, hi⟩ := (he.mpr h).symm
      simp only [Finsupp.single_apply, if_pos hf, if_pos h]
    · have hf : s ≠ prefixIndexedFace e t p ⟨i, hi⟩ := by
        intro heq
        exact h (he.mp heq.symm)
      simp only [Finsupp.single_apply, if_neg hf, if_neg h]
  · rw [prefixChainEquiv_apply_zero k e t p _ i hi]
    have hne : i ≠ (prefixFaceIndex e t p s).1 := by
      intro h
      exact hi (h ▸ (prefixFaceIndex e t p s).2)
    simp [hne]

/-- Keeping the same all-face coordinates realizes a prefix chain inclusion. -/
noncomputable def prefixDegreeIncl (e : CompatibleOrder f) (s t p : ℕ)
    (hst : s ≤ t) : prefixDegreeSpace k e s p →ₗ[k]
      prefixDegreeSpace k e t p :=
  Submodule.inclusion (by
    intro x hx
    rw [prefixDegreeSpace, Pi.mem_spanSubset_iff] at hx ⊢
    intro i hi
    exact hx i (fun h => hi ⟨lt_of_lt_of_le h.1 hst, h.2⟩))

theorem prefixFaceIndex_inclusion (e : CompatibleOrder f)
    (s t p : ℕ) (hst : s ≤ t) (q : Face (e.prefixComplex s) p) :
    (prefixFaceIndex e t p
      (faceIncl (e.prefixComplex_mono hst) p q)).1 =
      (prefixFaceIndex e s p q).1 := by
  rfl

/-- Chain inclusion retains the same common all-face coordinates. -/
theorem prefixChainEquiv_inclusion (e : CompatibleOrder f)
    (s t p : ℕ) (hst : s ≤ t) :
    (prefixChainEquiv k e t p).toLinearMap.comp
        (chainIncl k (e.prefixComplex_mono hst) p) =
      (prefixDegreeIncl k e s t p hst).comp
        (prefixChainEquiv k e s p).toLinearMap := by
  classical
  apply Finsupp.lhom_ext
  intro q a
  apply Subtype.ext
  funext i
  change (prefixChainEquiv k e t p
      (chainIncl k (e.prefixComplex_mono hst) p (Finsupp.single q a))).1 i =
    (prefixChainEquiv k e s p (Finsupp.single q a)).1 i
  rw [chainIncl_single,
    prefixChainEquiv_single_apply, prefixChainEquiv_single_apply,
    prefixFaceIndex_inclusion e s t p hst q]

/-- Square all-face matrix obtained from the existing oriented degreewise boundary. -/
noncomputable def faceBoundaryMatrix (e : CompatibleOrder f) :
    Matrix (Fin (faceCount K)) (Fin (faceCount K)) k := by
  classical
  exact fun i j =>
    if h : faceDegree e j = faceDegree e i + 1 then
      letI : Fintype (Face K (faceDegree e i + 1)) := Fintype.ofFinite _
      boundaryMatrix K k (faceDegree e i)
        (indexedFace e i (faceDegree e i) rfl)
        (indexedFace e j (faceDegree e i + 1) h)
    else 0

/-- Every nonzero entry has exactly adjacent homological degrees. -/
theorem faceBoundaryMatrix_degree (e : CompatibleOrder f)
    (i j : Fin (faceCount K)) (hij : faceBoundaryMatrix k e i j ≠ 0) :
    faceDegree e j = faceDegree e i + 1 := by
  classical
  by_contra h
  exact hij (by simp [faceBoundaryMatrix, h])

/-- Vertices have zero columns: the differential is unaugmented. -/
theorem faceBoundaryMatrix_vertex (e : CompatibleOrder f)
    (j : Fin (faceCount K)) (hj : faceDegree e j = 0) :
    (faceBoundaryMatrix k e).col j = 0 := by
  classical
  ext i
  by_cases h : faceDegree e j = faceDegree e i + 1
  · omega
  · simp [faceBoundaryMatrix, h]

/-- The matrix entry is the sum of ordered signed deletions. -/
theorem faceBoundaryMatrix_apply (e : CompatibleOrder f)
    (i j : Fin (faceCount K)) :
    faceBoundaryMatrix k e i j =
      if h : faceDegree e j = faceDegree e i + 1 then
        ∑ a : Fin (faceDegree e i + 2),
          if deletedFace K (faceDegree e i)
              (indexedFace e j (faceDegree e i + 1) h) a =
                indexedFace e i (faceDegree e i) rfl
          then (-1 : k) ^ (a : ℕ) else 0
      else 0 := by
  classical
  letI : Fintype (Face K (faceDegree e i + 1)) := Fintype.ofFinite _
  unfold faceBoundaryMatrix
  split_ifs with h
  · exact boundaryMatrix_apply K k (faceDegree e i) _ _
  · rfl

/-- On a fixed pair of adjacent degrees, the square entry is the degreewise boundary matrix coefficient. -/
theorem faceBoundaryMatrix_of_degree (e : CompatibleOrder f)
    (i j : Fin (faceCount K)) (p : ℕ)
    (hi : faceDegree e i = p) (hj : faceDegree e j = p + 1) :
    faceBoundaryMatrix k e i j =
      letI : Fintype (Face K (p + 1)) := Fintype.ofFinite _
      boundaryMatrix K k p (indexedFace e i p hi)
        (indexedFace e j (p + 1) hj) := by
  classical
  subst p
  rw [faceBoundaryMatrix, dif_pos hj]

/-- Deleting the `a`th ordered vertex gives the signed coefficient. -/
theorem faceBoundaryMatrix_deletedFace (e : CompatibleOrder f)
    (j : Fin (faceCount K)) (p : ℕ) (hj : faceDegree e j = p + 1)
    (a : Fin (p + 2)) :
    faceBoundaryMatrix k e
      (degreewiseFaceIndex e p
        (deletedFace K p (indexedFace e j (p + 1) hj) a)) j =
      (-1 : k) ^ (a : ℕ) := by
  let s := deletedFace K p (indexedFace e j (p + 1) hj) a
  have hs : faceDegree e (degreewiseFaceIndex e p s) = p :=
    degreewiseFaceIndex_degree e p s
  rw [faceBoundaryMatrix_of_degree k e _ j p hs hj]
  letI : Fintype (Face K (p + 1)) := Fintype.ofFinite _
  have hrow : indexedFace e (degreewiseFaceIndex e p s) p hs = s :=
    indexedFace_degreewiseFaceIndex e p s
  rw [hrow]
  exact boundaryMatrix_deletedFace K k p (indexedFace e j (p + 1) hj) a

/-- Only proper faces can have nonzero boundary coefficients. -/
theorem faceBoundaryMatrix_strict (e : CompatibleOrder f) :
    StrictBoundary (faceBoundaryMatrix k e) := by
  classical
  intro i j hij
  have hdeg := faceBoundaryMatrix_degree k e i j hij
  letI : Fintype (Face K (faceDegree e i + 1)) := Fintype.ofFinite _
  have hmatrix : boundaryMatrix K k (faceDegree e i)
      (indexedFace e i (faceDegree e i) rfl)
      (indexedFace e j (faceDegree e i + 1) hdeg) ≠ 0 := by
    simpa only [faceBoundaryMatrix, dif_pos hdeg] using hij
  have hex : ∃ a : Fin (faceDegree e i + 2),
      deletedFace K (faceDegree e i)
        (indexedFace e j (faceDegree e i + 1) hdeg) a =
          indexedFace e i (faceDegree e i) rfl := by
    by_contra hn
    push_neg at hn
    exact hmatrix (boundaryMatrix_eq_zero_of_not_deletedFace K k
      (faceDegree e i) _ _ hn)
  obtain ⟨a, ha⟩ := hex
  have hproper : (e.enum i).val ⊂ (e.enum j).val := by
    have hdel : (deletedFace K (faceDegree e i)
        (indexedFace e j (faceDegree e i + 1) hdeg) a).1 ⊂
          (indexedFace e j (faceDegree e i + 1) hdeg).1 :=
      Finset.erase_ssubset (Finset.orderEmbOfFin_mem _ _ a)
    rw [ha] at hdel
    simpa only [indexedFace] using hdel
  exact e.face_lt i j hproper

/-- A nonzero matrix coefficient lowers degree by precisely one. -/
theorem faceBoundaryMatrix_lowersDegree (e : CompatibleOrder f) :
    LowersDegree (faceDegree e) (faceBoundaryMatrix k e) :=
  faceBoundaryMatrix_degree k e

/-- On one prefix and degree the square matrix restricts to a differential. -/
noncomputable def prefixMatrixBoundary (e : CompatibleOrder f) (t p : ℕ) :
    prefixDegreeSpace k e t (p + 1) →ₗ[k] prefixDegreeSpace k e t p :=
  (Matrix.toLin' (faceBoundaryMatrix k e)).domRestrict
    (prefixDegreeSpace k e t (p + 1)) |>.codRestrict
      (prefixDegreeSpace k e t p) (by
        intro x
        rw [prefixDegreeSpace, Pi.mem_spanSubset_iff]
        intro i hi
        change (faceBoundaryMatrix k e).mulVec x.1 i = 0
        rw [Matrix.mulVec_apply_eq_sum]
        apply Finset.sum_eq_zero
        intro j _
        by_cases hij : faceBoundaryMatrix k e i j = 0
        · simp [hij]
        · have hdeg := faceBoundaryMatrix_degree k e i j hij
          have hlt := faceBoundaryMatrix_strict k e i j hij
          have hnot : ¬ (j.val < t ∧ faceDegree e j = p + 1) := by
            intro hj
            apply hi
            constructor
            · exact lt_trans hlt hj.1
            · omega
          have hz := Pi.mem_spanSubset_iff.mp x.2 j hnot
          simp [hz])

/-- A boundary coefficient is invariant under inclusion of complexes
on the same ordered ambient vertex type. -/
theorem boundaryMatrix_inclusion_entry
    {L : PreAbstractSimplicialComplex V} (p : ℕ)
    [Finite (Face L (p + 1))] [Finite (Face L p)] (h : L ≤ K)
    (τ : Face L p) (σ : Face L (p + 1)) :
    letI : Fintype (Face L (p + 1)) := Fintype.ofFinite _
    letI : Fintype (Face K (p + 1)) := Fintype.ofFinite _
    boundaryMatrix L k p τ σ =
      boundaryMatrix K k p (faceIncl h p τ) (faceIncl h (p + 1) σ) := by
  classical
  letI : Fintype (Face L (p + 1)) := Fintype.ofFinite _
  letI : Fintype (Face K (p + 1)) := Fintype.ofFinite _
  rw [boundaryMatrix_apply, boundaryMatrix_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hd := faceIncl_deletedFace h p σ a
  have hinj : Function.Injective (faceIncl h p) := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : Face K p => z.1) hxy)
  rw [← hd]
  simp only [hinj.eq_iff]

/-- A square entry inside a prefix equals that prefix's oriented
boundary coefficient. -/
theorem faceBoundaryMatrix_prefix_entry (e : CompatibleOrder f)
    (t p : ℕ) (i j : Fin (faceCount K))
    (hi : i.val < t ∧ faceDegree e i = p)
    (hj : j.val < t ∧ faceDegree e j = p + 1) :
    faceBoundaryMatrix k e i j =
      letI : Fintype (Face (e.prefixComplex t) (p + 1)) := Fintype.ofFinite _
      boundaryMatrix (e.prefixComplex t) k p
        (prefixIndexedFace e t p ⟨i, hi⟩)
        (prefixIndexedFace e t (p + 1) ⟨j, hj⟩) := by
  classical
  let hpre : e.prefixComplex t ≤ K := by
    intro s hs
    exact ((e.mem_prefixComplex t s).mp hs).1
  letI : Finite (Face (e.prefixComplex t) p) :=
    Finite.of_equiv _ (prefixFaceEquiv e t p)
  letI : Finite (Face (e.prefixComplex t) (p + 1)) :=
    Finite.of_equiv _ (prefixFaceEquiv e t (p + 1))
  letI : Fintype (Face (e.prefixComplex t) (p + 1)) := Fintype.ofFinite _
  letI : Fintype (Face K (p + 1)) := Fintype.ofFinite _
  rw [faceBoundaryMatrix_of_degree k e i j p hi.2 hj.2]
  have h := boundaryMatrix_inclusion_entry k p hpre
    (prefixIndexedFace e t p ⟨i, hi⟩)
    (prefixIndexedFace e t (p + 1) ⟨j, hj⟩)
  simpa only [prefixIndexedFace, indexedFace, faceIncl] using h.symm

theorem prefixChainEquiv_single_vector (e : CompatibleOrder f)
    (t p : ℕ) (σ : Face (e.prefixComplex t) p) (a : k) :
    (prefixChainEquiv k e t p (Finsupp.single σ a)).1 =
      Pi.single (prefixFaceIndex e t p σ).1 a := by
  classical
  funext i
  rw [prefixChainEquiv_single_apply]
  simp only [Pi.single_apply]

/-- The signed boundary is multiplication by the square matrix on a
single prefix simplex. -/
theorem prefixMatrixBoundary_single (e : CompatibleOrder f) (t p : ℕ)
    (σ : Face (e.prefixComplex t) (p + 1)) (a : k) :
    prefixMatrixBoundary k e t p
        (prefixChainEquiv k e t (p + 1) (Finsupp.single σ a)) =
      prefixChainEquiv k e t p
        (boundary (e.prefixComplex t) k p (Finsupp.single σ a)) := by
  classical
  let j := (prefixFaceIndex e t (p + 1) σ).1
  have hj : j.val < t ∧ faceDegree e j = p + 1 :=
    (prefixFaceIndex e t (p + 1) σ).2
  apply Subtype.ext
  funext i
  change (faceBoundaryMatrix k e).mulVec
      (prefixChainEquiv k e t (p + 1) (Finsupp.single σ a)).1 i = _
  rw [prefixChainEquiv_single_vector, Matrix.mulVec_single]
  by_cases hi : i.val < t ∧ faceDegree e i = p
  · rw [prefixChainEquiv_apply k e t p _ i hi]
    have hentry := faceBoundaryMatrix_prefix_entry k e t p i j hi hj
    have hσ : prefixIndexedFace e t (p + 1)
        (prefixFaceIndex e t (p + 1) σ) = σ :=
      (prefixFaceEquiv e t (p + 1)).right_inv σ
    have hσ' : prefixIndexedFace e t (p + 1) ⟨j, hj⟩ = σ := hσ
    rw [hσ'] at hentry
    letI : Fintype (Face (e.prefixComplex t) (p + 1)) := Fintype.ofFinite _
    have hcoeff := boundaryMatrix_mulVec (e.prefixComplex t) k p
      (Finsupp.single σ a)
    have hcoord := congrFun hcoeff (prefixIndexedFace e t p ⟨i, hi⟩)
    have hsingle : chainCoordinates (e.prefixComplex t) k (p + 1)
        (Finsupp.single σ a) = Pi.single σ a := by
      funext q
      rw [chainCoordinates_apply]
      by_cases hq : q = σ
      · subst q
        simp only [Finsupp.single_apply, Pi.single_apply, if_pos rfl]
      · simp only [Finsupp.single_apply, Pi.single_apply,
          if_neg hq, if_neg (Ne.symm hq)]
    rw [hsingle, Matrix.mulVec_single] at hcoord
    change MulOpposite.op a • faceBoundaryMatrix k e i j = _
    rw [hentry]
    simpa only [Matrix.col_apply, Pi.smul_apply,
      chainCoordinates_apply] using hcoord
  · rw [prefixChainEquiv_apply_zero k e t p _ i hi]
    have hz : faceBoundaryMatrix k e i j = 0 := by
      by_contra hn
      have hdeg := faceBoundaryMatrix_degree k e i j hn
      have hlt := faceBoundaryMatrix_strict k e i j hn
      apply hi
      constructor
      · exact lt_trans hlt hj.1
      · omega
    change MulOpposite.op a • faceBoundaryMatrix k e i j = 0
    rw [hz, smul_zero]

/-- At every stage and degree, the chain equivalence commutes with the
existing simplicial boundary. -/
theorem prefixChainEquiv_boundary (e : CompatibleOrder f) (t p : ℕ) :
    (prefixMatrixBoundary k e t p).comp
        (prefixChainEquiv k e t (p + 1)).toLinearMap =
      (prefixChainEquiv k e t p).toLinearMap.comp
        (boundary (e.prefixComplex t) k p) := by
  apply Finsupp.lhom_ext
  intro σ a
  exact prefixMatrixBoundary_single k e t p σ a

theorem faceBoundaryMatrix_mulVec_prefix (e : CompatibleOrder f)
    (t p : ℕ) (c : Chain (e.prefixComplex t) k (p + 1)) :
    (faceBoundaryMatrix k e).mulVec
        (prefixChainEquiv k e t (p + 1) c).1 =
      (prefixChainEquiv k e t p
        (boundary (e.prefixComplex t) k p c)).1 := by
  have h := congrArg (fun F => F c) (prefixChainEquiv_boundary k e t p)
  exact congrArg Subtype.val h

/-- The unaugmented square boundary kills every degree-zero coordinate vector. -/
theorem faceBoundaryMatrix_mulVec_zero_degree (e : CompatibleOrder f)
    (t : ℕ) (x : prefixDegreeSpace k e t 0) :
    (faceBoundaryMatrix k e).mulVec x.1 = 0 := by
  classical
  funext r
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : faceBoundaryMatrix k e r j = 0
  · simp [hj]
  · have hdegree := faceBoundaryMatrix_degree k e r j hj
    have hnot : ¬ (j.val < t ∧ faceDegree e j = 0) := by
      intro h
      omega
    have hz := Pi.mem_spanSubset_iff.mp x.2 j hnot
    simp [hz]

/-- The full all-face matrix squares to zero by the simplicial
boundary composition law, including the separate unaugmented degree zero. -/
theorem faceBoundaryMatrix_sq_zero (e : CompatibleOrder f) :
    faceBoundaryMatrix k e * faceBoundaryMatrix k e = 0 := by
  classical
  let D := faceBoundaryMatrix k e
  apply Matrix.ext
  intro r j
  have hentry : (D * D) r j = (D.mulVec (D.col j)) r := by
    simp only [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum, Matrix.col_apply]
  rw [hentry]
  cases hdeg : faceDegree e j with
  | zero =>
      have hz := faceBoundaryMatrix_vertex k e j hdeg
      simp [D, hz]
  | succ p =>
      let jj : {i : Fin (faceCount K) //
          i.val < faceCount K ∧ faceDegree e i = p + 1} :=
        ⟨j, j.isLt, hdeg⟩
      let σ := prefixIndexedFace e (faceCount K) (p + 1) jj
      have hindex : (prefixFaceIndex e (faceCount K) (p + 1) σ).1 = j := by
        have h := (prefixFaceEquiv e (faceCount K) (p + 1)).left_inv jj
        exact congrArg Subtype.val h
      have hvec : (prefixChainEquiv k e (faceCount K) (p + 1)
          (Finsupp.single σ 1)).1 = Pi.single j 1 := by
        rw [prefixChainEquiv_single_vector, hindex]
      have hcol : D.col j =
          (prefixChainEquiv k e (faceCount K) p
            (boundary (e.prefixComplex (faceCount K)) k p
              (Finsupp.single σ 1))).1 := by
        calc
          D.col j = D.mulVec (Pi.single j 1) :=
            (Matrix.mulVec_single_one D j).symm
          _ = D.mulVec (prefixChainEquiv k e (faceCount K) (p + 1)
              (Finsupp.single σ 1)).1 := by rw [hvec]
          _ = _ := faceBoundaryMatrix_mulVec_prefix k e (faceCount K) p _
      cases p with
      | zero =>
          rw [hcol]
          have hz := faceBoundaryMatrix_mulVec_zero_degree k e
            (faceCount K)
            (prefixChainEquiv k e (faceCount K) 0
              (boundary (e.prefixComplex (faceCount K)) k 0
                (Finsupp.single σ 1)))
          exact congrFun hz r
      | succ q =>
          rw [hcol]
          rw [faceBoundaryMatrix_mulVec_prefix k e (faceCount K) q]
          have hsq := congrArg (fun F => F (Finsupp.single σ 1))
            (boundary_comp_boundary (e.prefixComplex (faceCount K)) k q)
          simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hsq
          rw [hsq, map_zero]
          rfl

/-- Simplicial cycles are exactly #196's original matrix cycles under
the all-prefix chain coordinates. -/
theorem prefixChainEquiv_cycle_iff (e : CompatibleOrder f)
    (t p : ℕ) (c : Chain (e.prefixComplex t) k p) :
    c ∈ simplicialCycles (e.prefixComplex t) k p ↔
      OriginalCycle (faceDegree e) (faceBoundaryMatrix k e) p t
        (prefixChainEquiv k e t p c).1 := by
  have hsupport := (mem_prefixDegreeSpace_iff k e t p
    (prefixChainEquiv k e t p c).1).mp (prefixChainEquiv k e t p c).2
  cases p with
  | zero =>
      rw [simplicialCycles_zero]
      constructor
      · intro _
        exact ⟨hsupport.1, hsupport.2,
          faceBoundaryMatrix_mulVec_zero_degree k e t _⟩
      · intro _
        trivial
  | succ q =>
      rw [simplicialCycles_succ]
      have hb := faceBoundaryMatrix_mulVec_prefix k e t q c
      constructor
      · intro hc
        have hzero : boundary (e.prefixComplex t) k q c = 0 := hc
        rw [hzero, map_zero] at hb
        exact ⟨hsupport.1, hsupport.2, hb⟩
      · intro hc
        have hz := hb.symm.trans hc.2.2
        have hzero : boundary (e.prefixComplex t) k q c = 0 := by
          apply (prefixChainEquiv k e t q).injective
          apply Subtype.ext
          rw [map_zero]
          change (prefixChainEquiv k e t q
            (boundary (e.prefixComplex t) k q c)).1 = 0
          exact hz
        exact hzero

/-- The image of the boundary is exactly #196's OriginalBoundary,
including prefix support on the preimage. -/
theorem prefixChainEquiv_boundary_iff (e : CompatibleOrder f)
    (t p : ℕ) (z : simplicialCycles (e.prefixComplex t) k p) :
    z ∈ simplicialBoundaries (e.prefixComplex t) k p ↔
      OriginalBoundary (faceDegree e) (faceBoundaryMatrix k e) p t
        (prefixChainEquiv k e t p z.1).1 := by
  rw [mem_simplicialBoundaries_iff]
  constructor
  · rintro ⟨c, hc⟩
    let y := prefixChainEquiv k e t (p + 1) c
    have hy := (mem_prefixDegreeSpace_iff k e t (p + 1) y.1).mp y.2
    refine ⟨y.1, hy.1, hy.2, ?_⟩
    rw [faceBoundaryMatrix_mulVec_prefix k e t p c, hc]
  · rintro ⟨y, hpre, hdeg, hy⟩
    let x : prefixDegreeSpace k e t (p + 1) :=
      ⟨y, (mem_prefixDegreeSpace_iff k e t (p + 1) y).mpr ⟨hpre, hdeg⟩⟩
    let c := (prefixChainEquiv k e t (p + 1)).symm x
    refine ⟨c, ?_⟩
    apply (prefixChainEquiv k e t p).injective
    apply Subtype.ext
    have hb := faceBoundaryMatrix_mulVec_prefix k e t p c
    have hc : (prefixChainEquiv k e t (p + 1) c).1 = y := by
      exact congrArg Subtype.val
        ((prefixChainEquiv k e t (p + 1)).apply_symm_apply x)
    rw [hc, hy] at hb
    exact hb.symm

/-- The cycle space, not just its dimension, is the original matrix
cycle space of the reducer input. -/
noncomputable def prefixCycleCoordinateEquiv (e : CompatibleOrder f) (t p : ℕ) :
    simplicialCycles (e.prefixComplex t) k p ≃ₗ[k]
      originalCycleSpace (faceDegree e) (faceBoundaryMatrix k e) p t where
  toFun z := ⟨(prefixChainEquiv k e t p z.1).1,
    (prefixChainEquiv_cycle_iff k e t p z.1).mp z.2⟩
  invFun x := by
    let y : prefixDegreeSpace k e t p :=
      ⟨x.1, (mem_prefixDegreeSpace_iff k e t p x.1).mpr
        ⟨x.2.1, x.2.2.1⟩⟩
    let c := (prefixChainEquiv k e t p).symm y
    have hc : (prefixChainEquiv k e t p c).1 = x.1 :=
      congrArg Subtype.val ((prefixChainEquiv k e t p).apply_symm_apply y)
    exact ⟨c, (prefixChainEquiv_cycle_iff k e t p c).mpr
      (by rw [hc]; exact x.2)⟩
  left_inv := by
    intro z
    apply Subtype.ext
    change (prefixChainEquiv k e t p).symm
      (prefixChainEquiv k e t p z.1) = z.1
    exact (prefixChainEquiv k e t p).symm_apply_apply z.1
  right_inv := by
    intro x
    apply Subtype.ext
    change ((prefixChainEquiv k e t p)
      ((prefixChainEquiv k e t p).symm
        ⟨x.1, (mem_prefixDegreeSpace_iff k e t p x.1).mpr
          ⟨x.2.1, x.2.2.1⟩⟩)).1 = x.1
    exact congrArg Subtype.val ((prefixChainEquiv k e t p).apply_symm_apply _)
  map_add' := by
    intro x y
    apply Subtype.ext
    change ((prefixChainEquiv k e t p) (x.1 + y.1)).1 =
      ((prefixChainEquiv k e t p) x.1).1 +
        ((prefixChainEquiv k e t p) y.1).1
    exact congrArg Subtype.val (map_add (prefixChainEquiv k e t p) x.1 y.1)
  map_smul' := by
    intro a x
    apply Subtype.ext
    change ((prefixChainEquiv k e t p) (a • x.1)).1 =
      a • ((prefixChainEquiv k e t p) x.1).1
    exact congrArg Subtype.val (map_smul (prefixChainEquiv k e t p) a x.1)

/-- The cycle inclusion keeps its original all-face coordinate vector. -/
theorem prefixCycleCoordinateEquiv_inclusion (e : CompatibleOrder f)
    (s t p : ℕ) (hst : s ≤ t)
    (z : simplicialCycles (e.prefixComplex s) k p) :
    (prefixCycleCoordinateEquiv k e t p
      (simplicialCycleIncl k (e.prefixComplex_mono hst) p z)).1 =
      (prefixCycleCoordinateEquiv k e s p z).1 := by
  have hc := congrArg
    (fun F : Chain (e.prefixComplex s) k p →ₗ[k] prefixDegreeSpace k e t p =>
      (F z.1).1)
    (prefixChainEquiv_inclusion k e s t p hst)
  change ((prefixChainEquiv k e t p)
    (chainIncl k (e.prefixComplex_mono hst) p z.1)).1 =
    ((prefixChainEquiv k e s p) z.1).1 at hc
  change ((prefixChainEquiv k e t p)
    (chainIncl k (e.prefixComplex_mono hst) p z.1)).1 =
    ((prefixChainEquiv k e s p) z.1).1
  exact hc

/-- The square matrix is fed to the existing reducer. -/
noncomputable def reducedFaceBoundary (e : CompatibleOrder f) :
    Matrix (Fin (faceCount K)) (Fin (faceCount K)) k :=
  replay (faceBoundaryMatrix k e)
    (matrixReductionTrace (faceBoundaryMatrix k e))

noncomputable def faceReductionChange (e : CompatibleOrder f) :
    Matrix (Fin (faceCount K)) (Fin (faceCount K)) k :=
  traceChange (matrixReductionTrace (faceBoundaryMatrix k e))

noncomputable def faceReductionChangeInv (e : CompatibleOrder f) :
    Matrix (Fin (faceCount K)) (Fin (faceCount K)) k :=
  traceChangeInv (matrixReductionTrace (faceBoundaryMatrix k e))

/-- The reducer certificate is obtained from the boundary laws. -/
theorem faceReduction_normalForm (e : CompatibleOrder f) :
    let D := faceBoundaryMatrix k e
    let R := reducedFaceBoundary k e
    let V := faceReductionChange k e
    let W := faceReductionChangeInv k e
    R = D * V ∧ TraceChangeCertificate (faceDegree e) V W ∧
      LowersDegree (faceDegree e) R ∧ StrictBoundary R ∧
      DistinctPivots R ∧
      (∀ j i, columnPivot (R.col j) = some i →
        columnPivot (R.col i) = none) := by
  exact matrixReductionTrace_normalForm_input
    (faceDegree e) (faceBoundaryMatrix k e)
      (faceBoundaryMatrix_sq_zero k e)
      (faceBoundaryMatrix_strict k e)
      (faceBoundaryMatrix_lowersDegree k e)

/-- The kernel submodule in #196, packaged to keep the large reducer
certificate opaque during quotient elaboration. -/
noncomputable def faceMatrixBoundarySubmodule (e : CompatibleOrder f)
    (p t : ℕ) :
    Submodule k (originalCycleSpace (faceDegree e) (faceBoundaryMatrix k e) p t) := by
  let h := faceReduction_normalForm k e
  exact LinearMap.ker (originalLiveMap (faceDegree e) (faceBoundaryMatrix k e)
    (reducedFaceBoundary k e) (faceReductionChange k e)
    (faceReductionChangeInv k e) (faceBoundaryMatrix_sq_zero k e)
    h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t)

/-- #196's original homology quotient for the simplicial boundary. -/
noncomputable abbrev faceMatrixHomology (e : CompatibleOrder f)
    (p t : ℕ) : Type u :=
  (originalCycleSpace (faceDegree e) (faceBoundaryMatrix k e) p t) ⧸
    faceMatrixBoundarySubmodule k e p t

/-- The packaged quotient has precisely #196's originalHomology type. -/
theorem faceMatrixHomology_eq_originalHomology (e : CompatibleOrder f)
    (p t : ℕ) :
    faceMatrixHomology k e p t =
      (let h := faceReduction_normalForm k e
       originalHomology (faceDegree e) (faceBoundaryMatrix k e)
         (reducedFaceBoundary k e) (faceReductionChange k e)
         (faceReductionChangeInv k e) (faceBoundaryMatrix_sq_zero k e)
         h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t) := by
  rfl

/-- The quotient kernel used by #196 is precisely the image of the simplicial boundary under the cycle equivalence. -/
theorem prefixCycleCoordinateEquiv_boundaries (e : CompatibleOrder f) (t p : ℕ) :
    (simplicialBoundaries (e.prefixComplex t) k p).map
        (prefixCycleCoordinateEquiv k e t p).toLinearMap =
      LinearMap.ker
        (let h := faceReduction_normalForm k e
         originalLiveMap (faceDegree e) (faceBoundaryMatrix k e)
           (reducedFaceBoundary k e) (faceReductionChange k e)
           (faceReductionChangeInv k e) (faceBoundaryMatrix_sq_zero k e)
           h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t) := by
  let h := faceReduction_normalForm k e
  let E := prefixCycleCoordinateEquiv k e t p
  apply Submodule.ext
  intro x
  change x ∈ (simplicialBoundaries (e.prefixComplex t) k p).map E.toLinearMap ↔
    x ∈ LinearMap.ker
      (originalLiveMap (faceDegree e) (faceBoundaryMatrix k e)
        (reducedFaceBoundary k e) (faceReductionChange k e)
        (faceReductionChangeInv k e) (faceBoundaryMatrix_sq_zero k e)
        h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t)
  rw [Submodule.map_equiv_eq_comap_symm]
  change E.symm x ∈ simplicialBoundaries (e.prefixComplex t) k p ↔ _
  have hc : (prefixChainEquiv k e t p (E.symm x).1).1 = x.1 := by
    exact congrArg Subtype.val (E.apply_symm_apply x)
  rw [prefixChainEquiv_boundary_iff, hc]
  exact (originalHomology_kernel_eq_boundaries (faceDegree e)
    (faceBoundaryMatrix k e) (reducedFaceBoundary k e)
    (faceReductionChange k e) (faceReductionChangeInv k e)
    (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1
    h.2.2.2.2.1 p t x).symm

/-- Send a simplicial cycle to the live coordinates of the reducer. -/
noncomputable def prefixCycleToLive (e : CompatibleOrder f) (t p : ℕ) :
    simplicialCycles (e.prefixComplex t) k p →ₗ[k]
      aliveSpace (faceDegree e) (reducedFaceBoundary k e) p t := by
  let h := faceReduction_normalForm k e
  exact (originalLiveMap (faceDegree e) (faceBoundaryMatrix k e)
    (reducedFaceBoundary k e) (faceReductionChange k e)
    (faceReductionChangeInv k e) (faceBoundaryMatrix_sq_zero k e)
    h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t).comp
      (prefixCycleCoordinateEquiv k e t p).toLinearMap

/-- The boundary image is exactly the kernel of the live map. -/
theorem prefixCycleToLive_kernel_eq_boundaries (e : CompatibleOrder f)
    (t p : ℕ) :
    LinearMap.ker (prefixCycleToLive k e t p) =
      simplicialBoundaries (e.prefixComplex t) k p := by
  let h := faceReduction_normalForm k e
  apply Submodule.ext
  intro z
  change (originalLiveMap (faceDegree e) (faceBoundaryMatrix k e)
      (reducedFaceBoundary k e) (faceReductionChange k e)
      (faceReductionChangeInv k e) (faceBoundaryMatrix_sq_zero k e)
      h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t)
      (prefixCycleCoordinateEquiv k e t p z) = 0 ↔
    z ∈ simplicialBoundaries (e.prefixComplex t) k p
  have hk := originalHomology_kernel_eq_boundaries (faceDegree e)
    (faceBoundaryMatrix k e) (reducedFaceBoundary k e)
    (faceReductionChange k e) (faceReductionChangeInv k e)
    (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1
    h.2.2.2.2.1 p t (prefixCycleCoordinateEquiv k e t p z)
  exact hk.trans (prefixChainEquiv_boundary_iff k e t p z).symm

theorem prefixCycleToLive_surjective (e : CompatibleOrder f)
    (t p : ℕ) : Function.Surjective (prefixCycleToLive k e t p) := by
  let h := faceReduction_normalForm k e
  intro y
  obtain ⟨x, hx⟩ := originalLiveMap_surjective (faceDegree e)
    (faceBoundaryMatrix k e) (reducedFaceBoundary k e)
    (faceReductionChange k e) (faceReductionChangeInv k e)
    (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1
    h.2.2.2.2.1 p t y
  obtain ⟨z, hz⟩ := (prefixCycleCoordinateEquiv k e t p).surjective x
  refine ⟨z, ?_⟩
  change (originalLiveMap (faceDegree e) (faceBoundaryMatrix k e)
    (reducedFaceBoundary k e) (faceReductionChange k e)
    (faceReductionChangeInv k e) (faceBoundaryMatrix_sq_zero k e)
    h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t)
    (prefixCycleCoordinateEquiv k e t p z) = y
  rw [hz]
  exact hx

noncomputable local instance prefixCyclesHasQuotient (e : CompatibleOrder f)
    (t p : ℕ) :
    HasQuotient (simplicialCycles (e.prefixComplex t) k p)
      (Submodule k (simplicialCycles (e.prefixComplex t) k p)) :=
  Submodule.hasQuotient (R := k) (M := simplicialCycles (e.prefixComplex t) k p)

private noncomputable def prefixQuotientCoordinateEquiv (e : CompatibleOrder f) (t p : ℕ) :=
  Submodule.Quotient.equiv (R := k) (R₂ := k)
    (M := simplicialCycles (e.prefixComplex t) k p)
    (N := originalCycleSpace (faceDegree e) (faceBoundaryMatrix k e) p t)
    (σ₁₂ := RingHom.id k) (σ₂₁ := RingHom.id k)
    (simplicialBoundaries (e.prefixComplex t) k p)
    (faceMatrixBoundarySubmodule k e p t)
    (prefixCycleCoordinateEquiv k e t p) (prefixCycleCoordinateEquiv_boundaries k e t p)

/-- The cycle/boundary quotient is #196's original-boundary quotient. -/
noncomputable def prefixQuotientToMatrixHomology (e : CompatibleOrder f) (t p : ℕ) :
    ((simplicialCycles (e.prefixComplex t) k p) ⧸
      simplicialBoundaries (e.prefixComplex t) k p) ≃ₗ[k]
    faceMatrixHomology k e p t := prefixQuotientCoordinateEquiv k e t p

theorem prefixQuotientToMatrixHomology_mkQ (e : CompatibleOrder f) (t p : ℕ)
    (z : simplicialCycles (e.prefixComplex t) k p) :
    prefixQuotientToMatrixHomology k e t p
        (Submodule.mkQ (R := k)
          (M := simplicialCycles (e.prefixComplex t) k p)
          (simplicialBoundaries (e.prefixComplex t) k p) z) =
      Submodule.mkQ (R := k)
        (M := originalCycleSpace (faceDegree e) (faceBoundaryMatrix k e) p t)
        (faceMatrixBoundarySubmodule k e p t) (prefixCycleCoordinateEquiv k e t p z) := by
  rfl

/-- Simplicial prefix homology equals the reducer's original quotient. -/
noncomputable def prefixHomologyEquivMatrixHomology (e : CompatibleOrder f) (t p : ℕ) :
    simplicialHomology (e.prefixComplex t) k p ≃ₗ[k]
      faceMatrixHomology k e p t :=
  (homologyKernelQuotient.{u,u,u} k
    (simplicialChainComplex (e.prefixComplex t) k) p).toLinearEquiv.trans
      (prefixQuotientToMatrixHomology k e t p)

end TDA.Persistence.Reduction
