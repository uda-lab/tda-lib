import TDA.Simplicial.ArbitraryApexCone
import TDA.Simplicial.Inclusion
import TDA.Filtration.SubdivisionRips
import Mathlib.Algebra.Homology.Homotopy

/-!
# Homology invariance under barycentric subdivision

The normalized subdivision complex at mass zero is the flag complex of all
nonempty faces.  This file builds the last-vertex map and the natural chain
equivalence between it and the original face chains.
-/

universe u v

namespace TDA.Simplicial

open CategoryTheory Module
open scoped BigOperators

noncomputable section

variable {V : Type u} [LinearOrder V] [Fintype V]
variable {K L : PreAbstractSimplicialComplex V}

/-- The barycentric subdivision is the zero-mass flag complex. -/
abbrev barycentricSubdivision (K : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Finset V) :=
  TDA.Filtration.SubdivisionRips.subdivision K 0

/-- The maximum of a nonempty face, with an irrelevant default off the face locus. -/
def lastVertex [Nonempty V] (s : Finset V) : V :=
  if hs : s.Nonempty then s.max' hs else Classical.choice ‹Nonempty V›

@[simp] theorem lastVertex_of_nonempty [Nonempty V] (s : Finset V)
    (hs : s.Nonempty) : lastVertex s = s.max' hs := by
  simp [lastVertex, hs]

private theorem flag_maximum_subset (K : PreAbstractSimplicialComplex V)
    (S : Finset (Finset V)) (hS : S ∈ barycentricSubdivision K) :
    ∃ t ∈ S, ∀ s ∈ S, s ⊆ t := by
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image S Finset.card hS.1
  refine ⟨t, ht, ?_⟩
  intro s hs
  rcases hS.2.2 s hs t ht with hst | hts
  · exact hst
  · have heq : t = s := Finset.eq_of_subset_of_card_le hts (hmax s hs)
    simpa [heq]

/-- Send each nonempty face of the original complex to its greatest vertex. -/
def lastVertexMap [Nonempty V] (K : PreAbstractSimplicialComplex V) :
    VertexMap (barycentricSubdivision K) K where
  toFun := lastVertex
  map_face := by
    classical
    intro S hS
    obtain ⟨t, ht, htop⟩ := flag_maximum_subset K S hS
    have htK : t ∈ K :=
      ((TDA.Filtration.SubdivisionRips.mem_subdivision_iff K 0 S).mp hS).2.1 t ht |>.1
    have htne : t.Nonempty := (K.isRelLowerSet_faces htK).1
    change (@Finset.image (Finset V) V (Classical.decEq V) lastVertex S) ∈ K
    have himage_nonempty :
        (@Finset.image (Finset V) V (Classical.decEq V)
          lastVertex S).Nonempty := by
      obtain ⟨s, hs⟩ := hS.1
      exact ⟨lastVertex s,
        (@Finset.mem_image (Finset V) V (Classical.decEq V)
          lastVertex S (lastVertex s)).mpr ⟨s, hs, rfl⟩⟩
    have himage_subset :
        @Finset.image (Finset V) V (Classical.decEq V)
          lastVertex S ⊆ t := by
      intro x hx
      rcases (@Finset.mem_image (Finset V) V (Classical.decEq V) lastVertex S x).mp hx
        with ⟨s, hs, rfl⟩
      have hsK : s ∈ K :=
        ((TDA.Filtration.SubdivisionRips.mem_subdivision_iff K 0 S).mp hS).2.1 s hs |>.1
      have hsne : s.Nonempty := (K.isRelLowerSet_faces hsK).1
      rw [lastVertex_of_nonempty s hsne]
      exact htop s hs (Finset.max'_mem s hsne)
    exact (K.isRelLowerSet_faces htK).2 himage_subset himage_nonempty

/-- The simplex on a specified finite nonempty vertex set. -/
private def simplexOn (s : Finset V) : PreAbstractSimplicialComplex V where
  faces := {t | t.Nonempty ∧ t ⊆ s}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    intro u hut hu
    exact ⟨hu, hut.trans ht.2⟩

private theorem simplexOn_mono {s t : Finset V} (hst : s ⊆ t) :
    simplexOn s ≤ simplexOn t := by
  intro u hu
  exact ⟨hu.1, hu.2.trans hst⟩

private theorem simplexOn_le {n : ℕ} (s : Face K n) : simplexOn s.1 ≤ K := by
  intro t ht
  exact (K.isRelLowerSet_faces s.2.1).2 ht.2 ht.1

variable [LinearOrder (Finset V)]
local instance instFinsetDecidableEq : DecidableEq (Finset V) :=
  (inferInstance : LinearOrder (Finset V)).toDecidableEq

private theorem deletedFace_subset {n : ℕ} (s : Face K (n + 1)) (i : Fin (n + 2)) :
    (deletedFace K n s i).1 ⊆ s.1 :=
  Finset.erase_subset _ _

private theorem subdivisionSimplexFace_mem (s : Finset V) (hs : s.Nonempty) :
    ({s} : Finset (Finset V)) ∈ barycentricSubdivision (simplexOn s) := by
  rw [barycentricSubdivision, TDA.Filtration.SubdivisionRips.mem_subdivision_iff]
  refine ⟨by simp, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_singleton] at ht
    subst t
    refine ⟨⟨hs, Finset.Subset.rfl⟩, ?_⟩
    positivity
  · intro t ht u hu
    simp only [Finset.mem_singleton] at ht hu
    subst t
    subst u
    exact Or.inl Finset.Subset.rfl

private theorem subdivisionSimplexApex_mem (s : Finset V) (hs : s.Nonempty) :
    ({s} : Finset (Finset V)) ∈ barycentricSubdivision (simplexOn s) :=
  subdivisionSimplexFace_mem s hs

private theorem subdivisionSimplex_insert_mem (s : Finset V) (hs : s.Nonempty)
    (S : Finset (Finset V)) (hS : S ∈ barycentricSubdivision (simplexOn s)) :
    insert s S ∈ barycentricSubdivision (simplexOn s) := by
  rw [barycentricSubdivision, TDA.Filtration.SubdivisionRips.mem_subdivision_iff] at hS ⊢
  have hsub : ∀ t ∈ S, t ⊆ s := by
    intro t ht
    exact ((hS.2.1 t ht).1).2
  refine ⟨⟨s, Finset.mem_insert_self _ _⟩, ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨⟨hs, Finset.Subset.rfl⟩, by positivity⟩
    · exact hS.2.1 t ht
  · intro t ht u hu
    rcases Finset.mem_insert.mp ht with hts | htS
    · subst t
      rcases Finset.mem_insert.mp hu with hus | huS
      · subst u
        exact Or.inl Finset.Subset.rfl
      · exact Or.inr (hsub u huS)
    · rcases Finset.mem_insert.mp hu with hus | huS
      · subst u
        exact Or.inl (hsub t htS)
      · exact hS.2.2 t htS u huS

private theorem subdivisionSimplexIsCone (s : Finset V) (hs : s.Nonempty) :
    (∀ S ∈ barycentricSubdivision (simplexOn s),
      insert s S ∈ barycentricSubdivision (simplexOn s)) := by
  intro S hS
  exact subdivisionSimplex_insert_mem s hs S hS

private theorem subdivisionSimplexApexClosed (s : Finset V) (hs : s.Nonempty) :
    ApexInsertionClosed (barycentricSubdivision (simplexOn s)) s :=
  ⟨subdivisionSimplexApex_mem s hs, subdivisionSimplexIsCone s hs⟩

variable (R : Type v) [Ring R]

private theorem face_nonempty {n : ℕ} (s : Face K n) : s.1.Nonempty :=
  (K.isRelLowerSet_faces s.2.1).1

private theorem subdivision_simplex_mono {s t : Finset V} (hst : s ⊆ t) :
    barycentricSubdivision (simplexOn s) ≤ barycentricSubdivision (simplexOn t) := by
  exact TDA.Filtration.SubdivisionRips.subdivision_mono
    (simplexOn_mono hst) (show (0 : ℝ) ≤ 0 by rfl)

private def simplexFace (s : Finset V) {n : ℕ} (hs : s.Nonempty)
    (hcard : s.card = n + 1) : Face (simplexOn s) n :=
  ⟨s, ⟨hs, Finset.Subset.rfl⟩, hcard⟩

/-- The recursively subdivided oriented chain carried by one finite simplex. -/
private noncomputable def subdivisionSimplex (n : ℕ) :
    ∀ (s : Finset V), s.Nonempty → s.card = n + 1 →
      Chain (barycentricSubdivision (simplexOn s)) R n := by
  induction n with
  | zero =>
      intro s hs hc
      exact Finsupp.single
        ⟨{s}, subdivisionSimplexFace_mem s hs, by simp⟩ (1 : R)
  | succ n ih =>
      intro s hs hc
      classical
      let C : PreAbstractSimplicialComplex (Finset V) :=
        barycentricSubdivision (simplexOn s)
      let σ := simplexFace s hs hc
      let τ (i : Fin (n + 2)) := deletedFace (simplexOn s) n σ i
      let facets : Chain C R n :=
        ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) •
          chainIncl R (subdivision_simplex_mono (deletedFace_subset σ i)) n
            (ih (τ i).1 (face_nonempty (τ i)) (τ i).2.2)
      change Chain C R (n + 1)
      exact arbitraryApexConeFill C R s n facets

private noncomputable def subdivisionBoundary (n : ℕ) (s : Finset V)
    (hs : s.Nonempty) (hc : s.card = n + 2) :
    Chain (barycentricSubdivision (simplexOn s)) R n := by
  classical
  let σ := simplexFace s hs hc
  exact ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) •
    chainIncl R (subdivision_simplex_mono (deletedFace_subset σ i)) n
      (subdivisionSimplex R n (deletedFace (simplexOn s) n σ i).1
        ((deletedFace (simplexOn s) n σ i).2.1).1
        (deletedFace (simplexOn s) n σ i).2.2)

private theorem subdivisionSimplex_succ (n : ℕ) (s : Finset V)
    (hs : s.Nonempty) (hc : s.card = n + 2) :
    subdivisionSimplex R (n + 1) s hs hc =
      arbitraryApexConeFill (barycentricSubdivision (simplexOn s)) R s n
        (subdivisionBoundary R n s hs hc) := by
  classical
  rfl

/-- Subdivision of an original face, transported from its local simplex to the ambient complex. -/
private noncomputable def subdividedFace (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] (n : ℕ) (s : Face K n) :
    Chain (barycentricSubdivision K) R n :=
  chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono
    (simplexOn_le s) (show (0 : ℝ) ≤ 0 by rfl)) n
    (subdivisionSimplex R n s.1 (face_nonempty s) s.2.2)

/-- The natural subdivision chain map, defined on the face basis. -/
private noncomputable def barycentricChainMap (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] (n : ℕ) :
    Chain K R n →ₗ[R] Chain (barycentricSubdivision K) R n :=
  Finsupp.linearCombination R (fun s : Face K n => subdividedFace K R n s)

@[simp] private theorem barycentricChainMap_single
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R]
    (n : ℕ) (s : Face K n) (a : R) :
    barycentricChainMap K R n (Finsupp.single s a) = a • subdividedFace K R n s := by
  simp [barycentricChainMap]

private theorem barycentricChainMap_inclusion (h : K ≤ L) (n : ℕ) :
    (chainIncl R
        (TDA.Filtration.SubdivisionRips.subdivision_mono h (show (0 : ℝ) ≤ 0 by rfl)) n).comp
      (barycentricChainMap K R n) =
    (barycentricChainMap L R n).comp (chainIncl R h n) := by
  classical
  apply Finsupp.lhom_ext
  intro s a
  let h₁ := TDA.Filtration.SubdivisionRips.subdivision_mono
    (simplexOn_le s) (show (0 : ℝ) ≤ 0 by rfl)
  let h₂ := TDA.Filtration.SubdivisionRips.subdivision_mono h
    (show (0 : ℝ) ≤ 0 by rfl)
  let h₃ := TDA.Filtration.SubdivisionRips.subdivision_mono
    (simplexOn_le (faceIncl h n s)) (show (0 : ℝ) ≤ 0 by rfl)
  have hcomp : h₁.trans h₂ = h₃ := Subsingleton.elim _ _
  have hraw :
      subdivisionSimplex R n s.1 (face_nonempty s) s.2.2 =
      subdivisionSimplex R n s.1 (face_nonempty (faceIncl h n s))
        (faceIncl h n s).2.2 := by
    have hhs : face_nonempty (faceIncl h n s) = face_nonempty s := Subsingleton.elim _ _
    have hhc : (faceIncl h n s).2.2 = s.2.2 := Subsingleton.elim _ _
    rw [hhs, hhc]
  change chainIncl R h₂ n (barycentricChainMap K R n (Finsupp.single s a)) =
    barycentricChainMap L R n (chainIncl R h n (Finsupp.single s a))
  rw [barycentricChainMap_single, map_smul, chainIncl_single,
    barycentricChainMap_single]
  change a • chainIncl R h₂ n
      (chainIncl R h₁ n
        (subdivisionSimplex R n s.1 (face_nonempty s) s.2.2)) =
    a • chainIncl R h₃ n
      (subdivisionSimplex R n s.1 (face_nonempty (faceIncl h n s))
        (faceIncl h n s).2.2)
  congr 1
  calc
    chainIncl R h₂ n
        (chainIncl R h₁ n
          (subdivisionSimplex R n s.1 (face_nonempty s) s.2.2)) =
      ((chainIncl R h₂ n).comp (chainIncl R h₁ n))
        (subdivisionSimplex R n s.1 (face_nonempty s) s.2.2) := rfl
    _ = chainIncl R (h₁.trans h₂) n
        (subdivisionSimplex R n s.1 (face_nonempty s) s.2.2) := by
      exact congrArg (fun f : _ →ₗ[R] _ => f
        (subdivisionSimplex R n s.1 (face_nonempty s) s.2.2))
          (chainIncl_comp R h₁ h₂ n).symm
    _ = chainIncl R h₃ n
        (subdivisionSimplex R n s.1 (face_nonempty s) s.2.2) := by
      exact congrArg
        (fun h' => chainIncl R h' n
          (subdivisionSimplex R n s.1 (face_nonempty s) s.2.2)) hcomp
    _ = chainIncl R h₃ n
        (subdivisionSimplex R n s.1 (face_nonempty (faceIncl h n s))
          (faceIncl h n s).2.2) := congrArg (chainIncl R h₃ n) hraw

private theorem subdivisionBoundary_eq_chainMap_boundary
    (n : ℕ) (s : Finset V) (hs : s.Nonempty) (hc : s.card = n + 2) :
    subdivisionBoundary R n s hs hc =
      barycentricChainMap (simplexOn s) R n
        (boundary (simplexOn s) R n
          (Finsupp.single (simplexFace s hs hc) (1 : R))) := by
  classical
  rw [boundary_single, map_smul, map_sum]
  simp only [one_smul, barycentricChainMap_single]
  unfold subdivisionBoundary subdividedFace
  congr 1

private theorem subdivisionBoundary_in_ambient {n : ℕ} (s : Face K (n + 1)) :
    chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono
        (simplexOn_le s) (show (0 : ℝ) ≤ 0 by rfl)) n
        (subdivisionBoundary R n s.1 (face_nonempty s) s.2.2) =
      barycentricChainMap K R n (boundary K R n (Finsupp.single s (1 : R))) := by
  classical
  let T := simplexOn s.1
  let σ := simplexFace s.1 (face_nonempty s) s.2.2
  have hnat := LinearMap.congr_fun
    (barycentricChainMap_inclusion (R := R) (simplexOn_le s) n)
    (boundary T R n (Finsupp.single σ (1 : R)))
  have hface : faceIncl (simplexOn_le s) (n + 1) σ = s := by
    apply Subtype.ext
    rfl
  have hbnd := LinearMap.congr_fun
    (boundary_chainIncl R (simplexOn_le s) n)
    (Finsupp.single σ (1 : R))
  simp only [LinearMap.comp_apply, chainIncl_single, hface] at hbnd
  calc
    _ = chainIncl R
        (TDA.Filtration.SubdivisionRips.subdivision_mono
          (simplexOn_le s) (show (0 : ℝ) ≤ 0 by rfl)) n
        (barycentricChainMap T R n
          (boundary T R n (Finsupp.single σ (1 : R)))) := by
      rw [subdivisionBoundary_eq_chainMap_boundary]
    _ = barycentricChainMap K R n
        (chainIncl R (simplexOn_le s) n
          (boundary T R n (Finsupp.single σ (1 : R)))) := hnat
    _ = barycentricChainMap K R n
        (boundary K R n (Finsupp.single s (1 : R))) := by rw [← hbnd]

private theorem zeroChainCoefficientSum_barycentricChainMap
    (K : PreAbstractSimplicialComplex V) :
    (zeroChainCoefficientSum (barycentricSubdivision K) R).comp
      (barycentricChainMap K R 0) = zeroChainCoefficientSum K R := by
  apply Finsupp.lhom_ext
  intro s a
  change zeroChainCoefficientSum (barycentricSubdivision K) R
      (barycentricChainMap K R 0 (Finsupp.single s a)) =
    zeroChainCoefficientSum K R (Finsupp.single s a)
  rw [barycentricChainMap_single]
  rw [map_smul]
  simp [subdividedFace, subdivisionSimplex, chainIncl_single,
    zeroChainCoefficientSum_single]

private theorem zeroChainCoefficientSum_boundary_zero
    (K : PreAbstractSimplicialComplex V) :
    (zeroChainCoefficientSum K R).comp (boundary K R 0) = 0 := by
  apply Finsupp.lhom_ext
  intro s a
  change zeroChainCoefficientSum K R (boundary K R 0 (Finsupp.single s a)) = 0
  rw [boundary_single, map_smul, map_sum]
  simp [zeroChainCoefficientSum_single, Fin.sum_univ_succ]

private theorem subdivisionBoundary_augmentation_zero
    (s : Finset V) (hs : s.Nonempty) (hc : s.card = 2) :
    zeroChainCoefficientSum (barycentricSubdivision (simplexOn s)) R
      (subdivisionBoundary R 0 s hs hc) = 0 := by
  classical
  let T := simplexOn s
  let σ := simplexFace s hs hc
  have hrepr := subdivisionBoundary_eq_chainMap_boundary R 0 s hs hc
  have hmap := LinearMap.congr_fun
    (zeroChainCoefficientSum_barycentricChainMap (R := R) T)
    (boundary T R 0 (Finsupp.single σ (1 : R)))
  simp only [LinearMap.comp_apply] at hmap
  have hboundary := LinearMap.congr_fun
    (zeroChainCoefficientSum_boundary_zero (R := R) T)
    (Finsupp.single σ (1 : R))
  calc
    zeroChainCoefficientSum (barycentricSubdivision T) R
        (subdivisionBoundary R 0 s hs hc) =
      zeroChainCoefficientSum (barycentricSubdivision T) R
        (barycentricChainMap T R 0 (boundary T R 0 (Finsupp.single σ (1 : R)))) :=
      congrArg (zeroChainCoefficientSum (barycentricSubdivision T) R) hrepr
    _ = zeroChainCoefficientSum T R
        (boundary T R 0 (Finsupp.single σ (1 : R))) := hmap
    _ = 0 := by
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hboundary

private theorem subdivisionBoundary_cycle (m : ℕ) (s : Finset V)
    (hs : s.Nonempty) (hc : s.card = m + 3)
    (ih : ∀ T : PreAbstractSimplicialComplex V,
      (boundary (barycentricSubdivision T) R m).comp
          (barycentricChainMap T R (m + 1)) =
        (barycentricChainMap T R m).comp (boundary T R m)) :
    boundary (barycentricSubdivision (simplexOn s)) R m
      (subdivisionBoundary R (m + 1) s hs hc) = 0 := by
  classical
  let T := simplexOn s
  let σ := simplexFace s hs hc
  have hrepr := subdivisionBoundary_eq_chainMap_boundary R (m + 1) s hs hc
  have hIH := LinearMap.congr_fun (ih T)
    (boundary T R (m + 1) (Finsupp.single σ (1 : R)))
  simp only [LinearMap.comp_apply] at hIH
  have hsq :
      boundary T R m (boundary T R (m + 1) (Finsupp.single σ (1 : R))) = 0 := by
    have h := LinearMap.congr_fun (boundary_comp_boundary T R m)
      (Finsupp.single σ (1 : R))
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  calc
    boundary (barycentricSubdivision T) R m
        (subdivisionBoundary R (m + 1) s hs hc) =
      boundary (barycentricSubdivision T) R m
        (barycentricChainMap T R (m + 1)
          (boundary T R (m + 1) (Finsupp.single σ (1 : R)))) :=
      congrArg (boundary (barycentricSubdivision T) R m) hrepr
    _ = barycentricChainMap T R m
        (boundary T R m (boundary T R (m + 1) (Finsupp.single σ (1 : R)))) := hIH
    _ = 0 := by rw [hsq, map_zero]

private theorem subdivisionBoundary_fill_boundary_zero
    (s : Finset V) (hs : s.Nonempty) (hc : s.card = 2) :
    boundary (barycentricSubdivision (simplexOn s)) R 0
        (arbitraryApexConeFill (barycentricSubdivision (simplexOn s)) R s 0
          (subdivisionBoundary R 0 s hs hc)) = subdivisionBoundary R 0 s hs hc := by
  have hsum := subdivisionBoundary_augmentation_zero R s hs hc
  rw [boundary_arbitraryApexConeFill_zero_of_closed
      (barycentricSubdivision (simplexOn s)) R s
      (subdivisionSimplexApexClosed s hs)
      (subdivisionBoundary R 0 s hs hc), hsum]
  simp

private theorem subdivisionSimplex_boundary_zero (s : Finset V) (hs : s.Nonempty)
    (hc : s.card = 2) :
    boundary (barycentricSubdivision (simplexOn s)) R 0
        (subdivisionSimplex R 1 s hs hc) = subdivisionBoundary R 0 s hs hc := by
  rw [subdivisionSimplex_succ R 0 s hs hc]
  exact subdivisionBoundary_fill_boundary_zero R s hs hc

private theorem subdivisionBoundary_fill_boundary_succ (m : ℕ) (s : Finset V)
    (hs : s.Nonempty) (hc : s.card = m + 3)
    (ih : ∀ T : PreAbstractSimplicialComplex V,
      (boundary (barycentricSubdivision T) R m).comp
          (barycentricChainMap T R (m + 1)) =
        (barycentricChainMap T R m).comp (boundary T R m)) :
    boundary (barycentricSubdivision (simplexOn s)) R (m + 1)
        (arbitraryApexConeFill (barycentricSubdivision (simplexOn s)) R s
          (m + 1) (subdivisionBoundary R (m + 1) s hs hc)) =
      subdivisionBoundary R (m + 1) s hs hc := by
  have hcycle := subdivisionBoundary_cycle R m s hs hc ih
  have hcone := boundary_arbitraryApexConeFill_add_of_closed
    (barycentricSubdivision (simplexOn s)) R s
    (subdivisionSimplexApexClosed s hs) m (subdivisionBoundary R (m + 1) s hs hc)
  rw [hcycle, arbitraryApexConeFill_zero, add_zero] at hcone
  exact hcone

private theorem subdivisionSimplex_boundary_succ (m : ℕ) (s : Finset V)
    (hs : s.Nonempty) (hc : s.card = m + 3)
    (ih : ∀ T : PreAbstractSimplicialComplex V,
      (boundary (barycentricSubdivision T) R m).comp
          (barycentricChainMap T R (m + 1)) =
        (barycentricChainMap T R m).comp (boundary T R m)) :
    boundary (barycentricSubdivision (simplexOn s)) R (m + 1)
        (subdivisionSimplex R (m + 2) s hs hc) =
      subdivisionBoundary R (m + 1) s hs hc := by
  rw [subdivisionSimplex_succ R (m + 1) s hs hc]
  exact subdivisionBoundary_fill_boundary_succ R m s hs hc ih

private theorem barycentricChainMap_boundary :
    ∀ n : ℕ, ∀ K : PreAbstractSimplicialComplex V,
      (boundary (barycentricSubdivision K) R n).comp
          (barycentricChainMap K R (n + 1)) =
        (barycentricChainMap K R n).comp (boundary K R n) := by
  intro n
  induction n with
  | zero =>
      intro K
      apply Finsupp.lhom_ext
      intro s a
      let T := simplexOn s.1
      let hlocal := TDA.Filtration.SubdivisionRips.subdivision_mono
        (simplexOn_le s) (show (0 : ℝ) ≤ 0 by rfl)
      have hraw := subdivisionSimplex_boundary_zero R s.1 (face_nonempty s) s.2.2
      have hleft := subdivisionBoundary_in_ambient (K := K) (R := R) s
      have hlocalBoundary :
          boundary (barycentricSubdivision K) R 0
              (chainIncl R hlocal 1
                (subdivisionSimplex R 1 s.1 (face_nonempty s) s.2.2)) =
            chainIncl R hlocal 0
              (boundary (barycentricSubdivision T) R 0
                (subdivisionSimplex R 1 s.1 (face_nonempty s) s.2.2)) := by
        have h := LinearMap.congr_fun (boundary_chainIncl R hlocal 0)
          (subdivisionSimplex R 1 s.1 (face_nonempty s) s.2.2)
        simpa only [LinearMap.comp_apply] using h
      have hbd_single :
          boundary K R 0 (Finsupp.single s a) =
            a • boundary K R 0 (Finsupp.single s (1 : R)) := by
        rw [boundary_single, boundary_single]
        simp
      change boundary (barycentricSubdivision K) R 0
          (barycentricChainMap K R 1 (Finsupp.single s a)) =
        barycentricChainMap K R 0 (boundary K R 0 (Finsupp.single s a))
      calc
        _ = a • boundary (barycentricSubdivision K) R 0
              (chainIncl R hlocal 1
                (subdivisionSimplex R 1 s.1 (face_nonempty s) s.2.2)) := by
          rw [barycentricChainMap_single, subdividedFace, map_smul]
        _ = a • chainIncl R hlocal 0
              (boundary (barycentricSubdivision T) R 0
                (subdivisionSimplex R 1 s.1 (face_nonempty s) s.2.2)) :=
          congrArg (fun c => a • c) hlocalBoundary
        _ = a • chainIncl R hlocal 0 (subdivisionBoundary R 0 s.1
              (face_nonempty s) s.2.2) := by rw [hraw]
        _ = a • barycentricChainMap K R 0
              (boundary K R 0 (Finsupp.single s (1 : R))) := by
          rw [hleft]
        _ = _ := by rw [hbd_single, map_smul]
  | succ n ih =>
      intro K
      apply Finsupp.lhom_ext
      intro s a
      let T := simplexOn s.1
      let hlocal := TDA.Filtration.SubdivisionRips.subdivision_mono
        (simplexOn_le s) (show (0 : ℝ) ≤ 0 by rfl)
      have hraw := subdivisionSimplex_boundary_succ R n s.1 (face_nonempty s) s.2.2 ih
      have hleft := subdivisionBoundary_in_ambient (K := K) (R := R) s
      have hlocalBoundary :
          boundary (barycentricSubdivision K) R (n + 1)
              (chainIncl R hlocal (n + 2)
                (subdivisionSimplex R (n + 2) s.1 (face_nonempty s) s.2.2)) =
            chainIncl R hlocal (n + 1)
              (boundary (barycentricSubdivision T) R (n + 1)
                (subdivisionSimplex R (n + 2) s.1 (face_nonempty s) s.2.2)) := by
        have h := LinearMap.congr_fun (boundary_chainIncl R hlocal (n + 1))
          (subdivisionSimplex R (n + 2) s.1 (face_nonempty s) s.2.2)
        simpa only [LinearMap.comp_apply] using h
      have hbd_single :
          boundary K R (n + 1) (Finsupp.single s a) =
            a • boundary K R (n + 1) (Finsupp.single s (1 : R)) := by
        rw [boundary_single, boundary_single]
        simp
      change boundary (barycentricSubdivision K) R (n + 1)
          (barycentricChainMap K R (n + 2) (Finsupp.single s a)) =
        barycentricChainMap K R (n + 1)
          (boundary K R (n + 1) (Finsupp.single s a))
      calc
        _ = a • boundary (barycentricSubdivision K) R (n + 1)
              (chainIncl R hlocal (n + 2)
                (subdivisionSimplex R (n + 2) s.1 (face_nonempty s) s.2.2)) := by
          rw [barycentricChainMap_single, subdividedFace, map_smul]
        _ = a • chainIncl R hlocal (n + 1)
              (boundary (barycentricSubdivision T) R (n + 1)
                (subdivisionSimplex R (n + 2) s.1 (face_nonempty s) s.2.2)) :=
          congrArg (fun c => a • c) hlocalBoundary
        _ = a • chainIncl R hlocal (n + 1) (subdivisionBoundary R (n + 1)
              s.1 (face_nonempty s) s.2.2) := by rw [hraw]
        _ = a • barycentricChainMap K R (n + 1)
              (boundary K R (n + 1) (Finsupp.single s (1 : R))) := by
          rw [hleft]
        _ = _ := by rw [hbd_single, map_smul]

/-- The subdivision chain map as a morphism of the existing simplicial chain complexes. -/
noncomputable def barycentricSubdivisionChainMap
    (K : PreAbstractSimplicialComplex V) :
    simplicialChainComplex K R ⟶
      simplicialChainComplex (barycentricSubdivision K) R :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (barycentricChainMap K R n)) (by
      intro n
      apply ModuleCat.hom_ext
      simp only [simplicialChainComplex_d]
      exact barycentricChainMap_boundary R n K)

/-- The last-vertex map as a morphism of the existing simplicial chain complexes. -/
noncomputable def lastVertexChainMap (K : PreAbstractSimplicialComplex V) [Nonempty V] :
    simplicialChainComplex (barycentricSubdivision K) R ⟶ simplicialChainComplex K R :=
  simplicialChainMap R (lastVertexMap K)

/-- Homology map induced by the recursively defined subdivision chain map. -/
noncomputable def barycentricHomologyMap (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    simplicialHomology K R n ⟶
      simplicialHomology (barycentricSubdivision K) R n :=
  HomologicalComplex.homologyMap (barycentricSubdivisionChainMap R K) n

/-- Homology map induced by the last-vertex simplicial map. -/
noncomputable def lastVertexHomologyMap (K : PreAbstractSimplicialComplex V)
    [Nonempty V] (n : ℕ) :
    simplicialHomology (barycentricSubdivision K) R n ⟶ simplicialHomology K R n :=
  simplicialHomologyMap R (lastVertexMap K) n

private theorem lastVertexMap_naturality [Nonempty V] (h : K ≤ L) :
    VertexMap.comp (inclusionVertexMap
      (TDA.Filtration.SubdivisionRips.subdivision_mono h (show (0 : ℝ) ≤ 0 by rfl)))
      (lastVertexMap L) =
    VertexMap.comp (lastVertexMap K) (inclusionVertexMap h) := by
  apply VertexMap.ext
  intro s
  rfl

/-- The last-vertex homology maps commute with same-carrier inclusions. -/
theorem lastVertexHomologyMap_naturality [Nonempty V] (h : K ≤ L) (n : ℕ) :
    simplicialHomologyIncl R
        (TDA.Filtration.SubdivisionRips.subdivision_mono h
          (show (0 : ℝ) ≤ 0 by rfl)) n ≫ lastVertexHomologyMap R L n =
      lastVertexHomologyMap R K n ≫ simplicialHomologyIncl R h n := by
  have heq := lastVertexMap_naturality h
  rw [← simplicialHomologyMap_inclusion R
      (TDA.Filtration.SubdivisionRips.subdivision_mono h
        (show (0 : ℝ) ≤ 0 by rfl)) n,
    ← simplicialHomologyMap_inclusion R h n]
  unfold lastVertexHomologyMap
  rw [← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp]
  exact congrArg (fun f => simplicialHomologyMap R f n) heq

private noncomputable def barycentricApproximation [Nonempty V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Chain (barycentricSubdivision K) R n →ₗ[R]
      Chain (barycentricSubdivision K) R n :=
  (barycentricChainMap K R n).comp
    (vertexChainMap R (lastVertexMap K) n) - LinearMap.id

private theorem barycentricApproximation_boundary [Nonempty V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    (boundary (barycentricSubdivision K) R n).comp
        (barycentricApproximation R K (n + 1)) =
      (barycentricApproximation R K n).comp
        (boundary (barycentricSubdivision K) R n) := by
  apply LinearMap.ext
  intro c
  simp only [barycentricApproximation, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  have hS := LinearMap.congr_fun (barycentricChainMap_boundary R n K)
    (vertexChainMap R (lastVertexMap K) (n + 1) c)
  have hL := LinearMap.congr_fun
    (boundary_vertexChainMap R (lastVertexMap K) n) c
  simp only [LinearMap.comp_apply] at hS hL
  calc
    boundary (barycentricSubdivision K) R n
        (barycentricChainMap K R (n + 1)
          (vertexChainMap R (lastVertexMap K) (n + 1) c)) -
        boundary (barycentricSubdivision K) R n c =
      barycentricChainMap K R n
        (boundary K R n (vertexChainMap R (lastVertexMap K) (n + 1) c)) -
        boundary (barycentricSubdivision K) R n c := by rw [hS]
    _ = barycentricChainMap K R n
        (vertexChainMap R (lastVertexMap K) n
          (boundary (barycentricSubdivision K) R n c)) -
        boundary (barycentricSubdivision K) R n c := by rw [hL]
    _ = _ := rfl

private theorem lastVertexChainMap_naturality [Nonempty V] (h : K ≤ L) (n : ℕ) :
    (chainIncl R h n).comp (vertexChainMap R (lastVertexMap K) n) =
      (vertexChainMap R (lastVertexMap L) n).comp
        (chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
          (show (0 : ℝ) ≤ 0 by rfl)) n) := by
  have heq := congrArg (fun f => vertexChainMap R f n)
    (lastVertexMap_naturality h)
  rw [vertexChainMap_comp, vertexChainMap_comp, vertexChainMap_inclusion,
    vertexChainMap_inclusion] at heq
  exact heq.symm

private theorem barycentricApproximation_naturality [Nonempty V]
    (h : K ≤ L) (n : ℕ) :
    (chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
      (show (0 : ℝ) ≤ 0 by rfl)) n).comp
        (barycentricApproximation R K n) =
      (barycentricApproximation R L n).comp
        (chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
          (show (0 : ℝ) ≤ 0 by rfl)) n) := by
  apply LinearMap.ext
  intro c
  simp only [barycentricApproximation, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  have hS := LinearMap.congr_fun
    (barycentricChainMap_inclusion (R := R) h n)
    (vertexChainMap R (lastVertexMap K) n c)
  have hL := LinearMap.congr_fun (lastVertexChainMap_naturality (R := R) h n) c
  simp only [LinearMap.comp_apply] at hS hL
  calc
    chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
        (show (0 : ℝ) ≤ 0 by rfl)) n
        (barycentricChainMap K R n (vertexChainMap R (lastVertexMap K) n c)) -
      chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
        (show (0 : ℝ) ≤ 0 by rfl)) n c =
      barycentricChainMap L R n
        (chainIncl R h n (vertexChainMap R (lastVertexMap K) n c)) -
      chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
        (show (0 : ℝ) ≤ 0 by rfl)) n c := by rw [hS]
    _ = barycentricChainMap L R n
        (vertexChainMap R (lastVertexMap L) n
          (chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
            (show (0 : ℝ) ≤ 0 by rfl)) n c)) -
      chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
        (show (0 : ℝ) ≤ 0 by rfl)) n c := by rw [hL]
    _ = _ := rfl

private def flagTopFace {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (σ : Face (barycentricSubdivision K) n) : Finset V := σ.1.biUnion id

private theorem flagTopFace_mem {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (σ : Face (barycentricSubdivision K) n) : flagTopFace σ ∈ K := by
  obtain ⟨t, ht, hmax⟩ := flag_maximum_subset K σ.1 σ.2.1
  have htop : flagTopFace σ = t := by
    simp only [flagTopFace]
    ext x
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨u, hu, hxu⟩
      exact hmax u hu hxu
    · intro hx
      exact ⟨t, ht, hx⟩
  rw [htop]
  exact ((TDA.Filtration.SubdivisionRips.mem_subdivision_iff K 0 σ.1).mp
    σ.2.1).2.1 t ht |>.1

private theorem flagTopFace_nonempty {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (σ : Face (barycentricSubdivision K) n) : (flagTopFace σ).Nonempty :=
  (K.isRelLowerSet_faces (flagTopFace_mem σ)).1

private theorem flagFace_subset_top {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (σ : Face (barycentricSubdivision K) n) (t : Finset V) (ht : t ∈ σ.1) :
    t ⊆ flagTopFace σ := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨t, ht, hx⟩

private theorem simplexOn_mem_le {t : Finset V} (ht : t ∈ K) : simplexOn t ≤ K := by
  intro u hu
  exact (K.isRelLowerSet_faces ht).2 hu.2 hu.1

private def flagLocalFace {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (σ : Face (barycentricSubdivision K) n) :
    Face (barycentricSubdivision (simplexOn (flagTopFace σ))) n := by
  classical
  refine ⟨σ.1, ?_, σ.2.2⟩
  rw [barycentricSubdivision, TDA.Filtration.SubdivisionRips.mem_subdivision_iff]
  have hflag := (TDA.Filtration.SubdivisionRips.mem_subdivision_iff K 0 σ.1).mp
    σ.2.1
  refine ⟨hflag.1, ?_, hflag.2.2⟩
  intro t ht
  have htK : t ∈ K := (hflag.2.1 t ht).1
  have htne : t.Nonempty := (K.isRelLowerSet_faces htK).1
  refine ⟨⟨htne, flagFace_subset_top σ t ht⟩, ?_⟩
  positivity

private theorem flagLocalFace_inclusion {K : PreAbstractSimplicialComplex V} {n : ℕ}
    (σ : Face (barycentricSubdivision K) n) :
    faceIncl (TDA.Filtration.SubdivisionRips.subdivision_mono
      (simplexOn_mem_le (flagTopFace_mem σ)) (show (0 : ℝ) ≤ 0 by rfl)) n
      (flagLocalFace σ) = σ := by
  apply Subtype.ext
  rfl

private theorem flagLocalSubdivisionInclusion
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (σ : Face (barycentricSubdivision K) n) :
    barycentricSubdivision (simplexOn (flagTopFace σ)) ≤ barycentricSubdivision K :=
  TDA.Filtration.SubdivisionRips.subdivision_mono
    (simplexOn_mem_le (flagTopFace_mem σ)) (show (0 : ℝ) ≤ 0 by rfl)

private noncomputable def barycentricHomotopyBasis [Nonempty V] :
    (n : ℕ) → ∀ (K : PreAbstractSimplicialComplex V),
      Face (barycentricSubdivision K) n →
        Chain (barycentricSubdivision K) R (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro K σ
      let T := simplexOn (flagTopFace σ)
      let σlocal := flagLocalFace σ
      exact chainIncl R (flagLocalSubdivisionInclusion K 0 σ) 1
        (arbitraryApexConeFill (barycentricSubdivision T) R
          (flagTopFace σ) 0
          (barycentricApproximation R T 0
            (Finsupp.single σlocal (1 : R))))
  | succ n ih =>
      intro K σ
      let T := simplexOn (flagTopFace σ)
      let σlocal := flagLocalFace σ
      let Hprev : Chain (barycentricSubdivision T) R n →ₗ[R]
          Chain (barycentricSubdivision T) R (n + 1) :=
        Finsupp.linearCombination R (ih T)
      let defect : Chain (barycentricSubdivision T) R (n + 1) :=
        barycentricApproximation R T (n + 1)
            (Finsupp.single σlocal (1 : R)) -
          Hprev (boundary (barycentricSubdivision T) R n
            (Finsupp.single σlocal (1 : R)))
      exact chainIncl R (flagLocalSubdivisionInclusion K (n + 1) σ) (n + 2)
        (arbitraryApexConeFill (barycentricSubdivision T) R
          (flagTopFace σ) (n + 1) defect)

private noncomputable def barycentricHomotopyComponent [Nonempty V]
    (n : ℕ) (K : PreAbstractSimplicialComplex V) :
    Chain (barycentricSubdivision K) R n →ₗ[R]
      Chain (barycentricSubdivision K) R (n + 1) :=
  Finsupp.linearCombination R (barycentricHomotopyBasis R n K)

private theorem barycentricHomotopyBasis_zero [Nonempty V]
    (K : PreAbstractSimplicialComplex V)
    (σ : Face (barycentricSubdivision K) 0) :
    barycentricHomotopyBasis R 0 K σ =
      chainIncl R (flagLocalSubdivisionInclusion K 0 σ) 1
        (arbitraryApexConeFill
          (barycentricSubdivision (simplexOn (flagTopFace σ))) R
          (flagTopFace σ) 0
          (barycentricApproximation R (simplexOn (flagTopFace σ)) 0
            (Finsupp.single (flagLocalFace σ) (1 : R)))) := by
  rfl

private theorem barycentricHomotopyBasis_succ [Nonempty V]
    (n : ℕ) (K : PreAbstractSimplicialComplex V)
    (σ : Face (barycentricSubdivision K) (n + 1)) :
    barycentricHomotopyBasis R (n + 1) K σ =
      chainIncl R (flagLocalSubdivisionInclusion K (n + 1) σ) (n + 2)
        (arbitraryApexConeFill
          (barycentricSubdivision (simplexOn (flagTopFace σ))) R
          (flagTopFace σ) (n + 1)
          (barycentricApproximation R (simplexOn (flagTopFace σ)) (n + 1)
              (Finsupp.single (flagLocalFace σ) (1 : R)) -
            barycentricHomotopyComponent R n (simplexOn (flagTopFace σ))
              (boundary
                (barycentricSubdivision (simplexOn (flagTopFace σ))) R n
                (Finsupp.single (flagLocalFace σ) (1 : R))))) := by
  rfl

private theorem barycentricHomotopyComponent_single [Nonempty V]
    (n : ℕ) (K : PreAbstractSimplicialComplex V)
    (σ : Face (barycentricSubdivision K) n) (a : R) :
    barycentricHomotopyComponent R n K (Finsupp.single σ a) =
      a • barycentricHomotopyBasis R n K σ := by
  simp [barycentricHomotopyComponent]

private theorem barycentricHomotopyComponent_naturality [Nonempty V]
    (h : K ≤ L) (n : ℕ) :
    (chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
      (show (0 : ℝ) ≤ 0 by rfl)) (n + 1)).comp
        (barycentricHomotopyComponent R n K) =
      (barycentricHomotopyComponent R n L).comp
        (chainIncl R (TDA.Filtration.SubdivisionRips.subdivision_mono h
          (show (0 : ℝ) ≤ 0 by rfl)) n) := by
  apply Finsupp.lhom_ext
  intro σ a
  let hsd := TDA.Filtration.SubdivisionRips.subdivision_mono h
    (show (0 : ℝ) ≤ 0 by rfl)
  let σ' := faceIncl hsd n σ
  have hlocal :
      (flagLocalSubdivisionInclusion K n σ).trans hsd =
        flagLocalSubdivisionInclusion L n σ' := by
    apply Subsingleton.elim
  change chainIncl R hsd (n + 1)
      (barycentricHomotopyComponent R n K (Finsupp.single σ a)) =
    barycentricHomotopyComponent R n L (chainIncl R hsd n (Finsupp.single σ a))
  simp only [LinearMap.comp_apply, chainIncl_single]
  have hbasis :
      chainIncl R hsd (n + 1) (barycentricHomotopyBasis R n K σ) =
        barycentricHomotopyBasis R n L σ' := by
    cases n with
    | zero =>
        rw [barycentricHomotopyBasis_zero, barycentricHomotopyBasis_zero]
        let localFill := arbitraryApexConeFill
          (barycentricSubdivision (simplexOn (flagTopFace σ))) R
          (flagTopFace σ) 0
          (barycentricApproximation R (simplexOn (flagTopFace σ)) 0
            (Finsupp.single (flagLocalFace σ) (1 : R)))
        have hpoint := LinearMap.congr_fun
          (chainIncl_comp R (flagLocalSubdivisionInclusion K 0 σ) hsd 1)
          localFill
        simp only [LinearMap.comp_apply] at hpoint
        rw [hlocal] at hpoint
        have hFill : arbitraryApexConeFill
            (barycentricSubdivision (simplexOn (flagTopFace σ'))) R
            (flagTopFace σ') 0
            (barycentricApproximation R (simplexOn (flagTopFace σ')) 0
              (Finsupp.single (flagLocalFace σ') (1 : R))) = localFill := by
          change localFill = localFill
          rfl
        simp_rw [hFill]
        change chainIncl R hsd 1
            (chainIncl R (flagLocalSubdivisionInclusion K 0 σ) 1 localFill) =
          chainIncl R (flagLocalSubdivisionInclusion L 0 σ') 1 localFill
        exact hpoint.symm
    | succ n =>
        rw [barycentricHomotopyBasis_succ, barycentricHomotopyBasis_succ]
        let localFill := arbitraryApexConeFill
          (barycentricSubdivision (simplexOn (flagTopFace σ))) R
          (flagTopFace σ) (n + 1)
          (barycentricApproximation R (simplexOn (flagTopFace σ)) (n + 1)
              (Finsupp.single (flagLocalFace σ) (1 : R)) -
            (Finsupp.linearCombination R (barycentricHomotopyBasis R n
              (simplexOn (flagTopFace σ))))
              (boundary (barycentricSubdivision (simplexOn (flagTopFace σ))) R n
                (Finsupp.single (flagLocalFace σ) (1 : R))))
        have hpoint := LinearMap.congr_fun
          (chainIncl_comp R (flagLocalSubdivisionInclusion K (n + 1) σ) hsd
            (n + 2)) localFill
        simp only [LinearMap.comp_apply] at hpoint
        rw [hlocal] at hpoint
        have hFill : arbitraryApexConeFill
            (barycentricSubdivision (simplexOn (flagTopFace σ'))) R
            (flagTopFace σ') (n + 1)
            (barycentricApproximation R (simplexOn (flagTopFace σ')) (n + 1)
                (Finsupp.single (flagLocalFace σ') (1 : R)) -
              (barycentricHomotopyComponent R n
                (simplexOn (flagTopFace σ')))
                (boundary (barycentricSubdivision (simplexOn (flagTopFace σ'))) R n
                  (Finsupp.single (flagLocalFace σ') (1 : R)))) = localFill := by
          change localFill = localFill
          rfl
        simp_rw [hFill]
        change chainIncl R hsd (n + 2)
            (chainIncl R (flagLocalSubdivisionInclusion K (n + 1) σ)
              (n + 2) localFill) =
          chainIncl R (flagLocalSubdivisionInclusion L (n + 1) σ')
            (n + 2) localFill
        exact hpoint.symm
  simp only [barycentricHomotopyComponent_single, map_smul, chainIncl_single]
  rw [hbasis]

private theorem barycentricApproximation_augmentation [Nonempty V]
    (K : PreAbstractSimplicialComplex V) :
    (zeroChainCoefficientSum (barycentricSubdivision K) R).comp
        (barycentricApproximation R K 0) = 0 := by
  apply LinearMap.ext
  intro c
  simp only [barycentricApproximation, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  have hS := LinearMap.congr_fun
    (zeroChainCoefficientSum_barycentricChainMap (R := R) K)
    (vertexChainMap R (lastVertexMap K) 0 c)
  have hL := LinearMap.congr_fun
    (zeroChainCoefficientSum_vertexChainMap R (lastVertexMap K)) c
  simp only [LinearMap.comp_apply] at hS hL
  calc
    zeroChainCoefficientSum (barycentricSubdivision K) R
        (barycentricChainMap K R 0 (vertexChainMap R (lastVertexMap K) 0 c)) -
      zeroChainCoefficientSum (barycentricSubdivision K) R c =
      zeroChainCoefficientSum K R (vertexChainMap R (lastVertexMap K) 0 c) -
      zeroChainCoefficientSum (barycentricSubdivision K) R c := by rw [hS]
    _ = zeroChainCoefficientSum (barycentricSubdivision K) R c -
      zeroChainCoefficientSum (barycentricSubdivision K) R c := by rw [hL]
    _ = 0 := sub_self _

private def barycentricHomotopyEquationAt [Nonempty V] (n : ℕ)
    (K : PreAbstractSimplicialComplex V) : Prop :=
  match n with
  | 0 =>
      (boundary (barycentricSubdivision K) R 0).comp
        (barycentricHomotopyComponent R 0 K) =
        barycentricApproximation R K 0
  | Nat.succ n =>
      (boundary (barycentricSubdivision K) R (n + 1)).comp
          (barycentricHomotopyComponent R (n + 1) K) +
        (barycentricHomotopyComponent R n K).comp
          (boundary (barycentricSubdivision K) R n) =
        barycentricApproximation R K (n + 1)

private theorem barycentricHomotopyEquation [Nonempty V] :
    ∀ n : ℕ, ∀ K : PreAbstractSimplicialComplex V,
      barycentricHomotopyEquationAt R n K := by
  intro n
  induction n with
  | zero =>
      intro K
      apply Finsupp.lhom_ext
      intro σ a
      have hunit :
          boundary (barycentricSubdivision K) R 0
              (barycentricHomotopyComponent R 0 K (Finsupp.single σ (1 : R))) =
            barycentricApproximation R K 0 (Finsupp.single σ (1 : R)) := by
        let t := flagTopFace σ
        let T := simplexOn t
        let σlocal := flagLocalFace σ
        let hlocal := flagLocalSubdivisionInclusion K 0 σ
        have hsum := LinearMap.congr_fun
          (barycentricApproximation_augmentation (R := R) T)
          (Finsupp.single σlocal (1 : R))
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hsum
        have hfill := boundary_arbitraryApexConeFill_zero_of_closed
          (barycentricSubdivision T) R t (subdivisionSimplexApexClosed t
            (flagTopFace_nonempty σ))
          (barycentricApproximation R T 0
            (Finsupp.single σlocal (1 : R)))
        have hfill' :
            boundary (barycentricSubdivision T) R 0
                (arbitraryApexConeFill (barycentricSubdivision T) R t 0
                  (barycentricApproximation R T 0
                    (Finsupp.single σlocal (1 : R)))) =
              barycentricApproximation R T 0
                (Finsupp.single σlocal (1 : R)) := by
          rw [hfill, hsum]
          simp only [Finsupp.single_zero, sub_zero]
        have hbd := LinearMap.congr_fun (boundary_chainIncl R hlocal 0)
          (arbitraryApexConeFill (barycentricSubdivision T) R t 0
            (barycentricApproximation R T 0 (Finsupp.single σlocal (1 : R))))
        simp only [LinearMap.comp_apply] at hbd
        have hnat := LinearMap.congr_fun
          (barycentricApproximation_naturality (R := R)
            (simplexOn_mem_le (flagTopFace_mem σ)) 0)
          (Finsupp.single σlocal (1 : R))
        have hface := flagLocalFace_inclusion σ
        have hsd : TDA.Filtration.SubdivisionRips.subdivision_mono
            (simplexOn_mem_le (flagTopFace_mem σ))
            (show (0 : ℝ) ≤ 0 by rfl) = hlocal := by
          apply Subsingleton.elim
        rw [hsd] at hnat
        simp only [barycentricSubdivision, LinearMap.comp_apply,
          chainIncl_single, σlocal, hface] at hnat
        calc
          boundary (barycentricSubdivision K) R 0
              (barycentricHomotopyComponent R 0 K
                (Finsupp.single σ (1 : R))) =
            chainIncl R hlocal 0
              (boundary (barycentricSubdivision T) R 0
                (arbitraryApexConeFill (barycentricSubdivision T) R t 0
                  (barycentricApproximation R T 0
                    (Finsupp.single σlocal (1 : R))))) := by
              simp only [barycentricHomotopyComponent_single,
                barycentricHomotopyBasis_zero, one_smul]
              exact hbd
          _ = chainIncl R hlocal 0
              (barycentricApproximation R T 0
                (Finsupp.single σlocal (1 : R))) := by rw [hfill']
          _ = barycentricApproximation R K 0
              (Finsupp.single σ (1 : R)) := by
              exact hnat
      have hsingle : Finsupp.single σ a = a • Finsupp.single σ (1 : R) := by
        simp
      rw [hsingle, map_smul, map_smul]
      exact congrArg (fun c => a • c) hunit

  | succ n ih =>
      intro K
      apply Finsupp.lhom_ext
      intro σ a
      have hunit :
          boundary (barycentricSubdivision K) R (n + 1)
              (barycentricHomotopyComponent R (n + 1) K
                (Finsupp.single σ (1 : R))) +
            barycentricHomotopyComponent R n K
              (boundary (barycentricSubdivision K) R n
                (Finsupp.single σ (1 : R))) =
          barycentricApproximation R K (n + 1)
            (Finsupp.single σ (1 : R)) := by
        let t := flagTopFace σ
        let T := simplexOn t
        let σlocal := flagLocalFace σ
        let hlocal := flagLocalSubdivisionInclusion K (n + 1) σ
        let y := boundary (barycentricSubdivision T) R n
          (Finsupp.single σlocal (1 : R))
        let defect : Chain (barycentricSubdivision T) R (n + 1) :=
          barycentricApproximation R T (n + 1)
              (Finsupp.single σlocal (1 : R)) -
            barycentricHomotopyComponent R n T y
        have hcycle : boundary (barycentricSubdivision T) R n defect = 0 := by
          dsimp [defect, y]
          rw [map_sub]
          have hA := LinearMap.congr_fun
            (barycentricApproximation_boundary (R := R) T n)
            (Finsupp.single σlocal (1 : R))
          simp only [LinearMap.comp_apply] at hA
          cases n with
          | zero =>
              have hIH := ih T
              change (boundary (barycentricSubdivision T) R 0).comp
                  (barycentricHomotopyComponent R 0 T) =
                barycentricApproximation R T 0 at hIH
              have hH := LinearMap.congr_fun hIH
                (boundary (barycentricSubdivision T) R 0
                  (Finsupp.single σlocal (1 : R)))
              simp only [LinearMap.comp_apply] at hH
              calc
                boundary (barycentricSubdivision T) R 0
                    (barycentricApproximation R T 1
                      (Finsupp.single σlocal (1 : R))) -
                  boundary (barycentricSubdivision T) R 0
                    (barycentricHomotopyComponent R 0 T
                      (boundary (barycentricSubdivision T) R 0
                        (Finsupp.single σlocal (1 : R)))) =
                  barycentricApproximation R T 0
                    (boundary (barycentricSubdivision T) R 0
                      (Finsupp.single σlocal (1 : R))) -
                  barycentricApproximation R T 0
                    (boundary (barycentricSubdivision T) R 0
                      (Finsupp.single σlocal (1 : R))) := by rw [hA, hH]
                _ = 0 := sub_self _
          | succ m =>
              have hIH := ih T
              change (boundary (barycentricSubdivision T) R (m + 1)).comp
                    (barycentricHomotopyComponent R (m + 1) T) +
                  (barycentricHomotopyComponent R m T).comp
                    (boundary (barycentricSubdivision T) R m) =
                barycentricApproximation R T (m + 1) at hIH
              have hHraw := LinearMap.congr_fun hIH
                (boundary (barycentricSubdivision T) R (m + 1)
                  (Finsupp.single σlocal (1 : R)))
              simp only [LinearMap.comp_apply, LinearMap.add_apply] at hHraw
              have hsq : boundary (barycentricSubdivision T) R m
                  (boundary (barycentricSubdivision T) R (m + 1)
                    (Finsupp.single σlocal (1 : R))) = 0 := by
                have h := LinearMap.congr_fun
                  (boundary_comp_boundary (barycentricSubdivision T) R m)
                  (Finsupp.single σlocal (1 : R))
                simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
              have hH :
                  boundary (barycentricSubdivision T) R (m + 1)
                      (barycentricHomotopyComponent R (m + 1) T
                        (boundary (barycentricSubdivision T) R (m + 1)
                          (Finsupp.single σlocal (1 : R)))) =
                    barycentricApproximation R T (m + 1)
                      (boundary (barycentricSubdivision T) R (m + 1)
                        (Finsupp.single σlocal (1 : R))) := by
                rw [hsq, map_zero, add_zero] at hHraw
                exact hHraw
              calc
                boundary (barycentricSubdivision T) R (m + 1)
                    (barycentricApproximation R T (m + 2)
                      (Finsupp.single σlocal (1 : R))) -
                  boundary (barycentricSubdivision T) R (m + 1)
                    (barycentricHomotopyComponent R (m + 1) T
                      (boundary (barycentricSubdivision T) R (m + 1)
                        (Finsupp.single σlocal (1 : R)))) =
                  barycentricApproximation R T (m + 1)
                    (boundary (barycentricSubdivision T) R (m + 1)
                      (Finsupp.single σlocal (1 : R))) -
                  barycentricApproximation R T (m + 1)
                    (boundary (barycentricSubdivision T) R (m + 1)
                      (Finsupp.single σlocal (1 : R))) := by rw [hA, hH]
                _ = 0 := sub_self _
        have hcone := boundary_arbitraryApexConeFill_add_of_closed
          (barycentricSubdivision T) R t
          (subdivisionSimplexApexClosed t (flagTopFace_nonempty σ)) n defect
        have hfill :
            boundary (barycentricSubdivision T) R (n + 1)
                (arbitraryApexConeFill (barycentricSubdivision T) R t
                  (n + 1) defect) = defect := by
          rw [hcycle, arbitraryApexConeFill_zero, add_zero] at hcone
          exact hcone
        have hbd := LinearMap.congr_fun
          (boundary_chainIncl R hlocal (n + 1))
          (arbitraryApexConeFill (barycentricSubdivision T) R t
            (n + 1) defect)
        simp only [LinearMap.comp_apply] at hbd
        have hHnat := LinearMap.congr_fun
          (barycentricHomotopyComponent_naturality (R := R)
            (simplexOn_mem_le (flagTopFace_mem σ)) n) y
        simp only [LinearMap.comp_apply] at hHnat
        have hface : faceIncl hlocal (n + 1) σlocal = σ := by
          apply Subtype.ext
          rfl
        have hbdface := LinearMap.congr_fun
          (boundary_chainIncl R hlocal n)
          (Finsupp.single σlocal (1 : R))
        simp only [LinearMap.comp_apply] at hbdface
        have hbdface' :
            boundary (barycentricSubdivision K) R n
                (Finsupp.single σ (1 : R)) =
              chainIncl R hlocal n
                (boundary (barycentricSubdivision T) R n
                  (Finsupp.single σlocal (1 : R))) := by
          simpa only [LinearMap.comp_apply, chainIncl_single, hface] using hbdface
        have hHvalue :
            barycentricHomotopyComponent R n K
                (boundary (barycentricSubdivision K) R n
                  (Finsupp.single σ (1 : R))) =
              chainIncl R hlocal (n + 1)
                (barycentricHomotopyComponent R n T y) := by
          rw [hbdface']
          exact hHnat.symm
        have hnat := LinearMap.congr_fun
          (barycentricApproximation_naturality (R := R)
            (simplexOn_mem_le (flagTopFace_mem σ)) (n + 1))
          (Finsupp.single σlocal (1 : R))
        simp only [LinearMap.comp_apply] at hnat
        have happrox :
            chainIncl R hlocal (n + 1)
                (barycentricApproximation R T (n + 1)
                  (Finsupp.single σlocal (1 : R))) =
              barycentricApproximation R K (n + 1)
                (Finsupp.single σ (1 : R)) := by
          simpa only [LinearMap.comp_apply, chainIncl_single, hface] using hnat
        calc
          boundary (barycentricSubdivision K) R (n + 1)
              (barycentricHomotopyComponent R (n + 1) K
                (Finsupp.single σ (1 : R))) +
              barycentricHomotopyComponent R n K
                (boundary (barycentricSubdivision K) R n
                  (Finsupp.single σ (1 : R))) =
            chainIncl R hlocal (n + 1)
                (boundary (barycentricSubdivision T) R (n + 1)
                  (arbitraryApexConeFill (barycentricSubdivision T) R t
                    (n + 1) defect)) +
              chainIncl R hlocal (n + 1)
                (barycentricHomotopyComponent R n T y) := by
            simp only [barycentricHomotopyComponent_single,
              barycentricHomotopyBasis_succ, one_smul]
            rw [hbd, hHvalue]
          _ = chainIncl R hlocal (n + 1) defect +
              chainIncl R hlocal (n + 1)
                (barycentricHomotopyComponent R n T y) := by rw [hfill]
          _ = chainIncl R hlocal (n + 1)
                (barycentricApproximation R T (n + 1)
                  (Finsupp.single σlocal (1 : R))) := by
            simp only [defect, map_sub]
            abel
          _ = barycentricApproximation R K (n + 1)
                (Finsupp.single σ (1 : R)) := happrox
      have hsingle : Finsupp.single σ a = a • Finsupp.single σ (1 : R) := by
        simp
      rw [hsingle]
      simp only [map_smul, smul_add, barycentricHomotopyComponent_single,
        one_smul]
      exact congrArg (fun c => a • c) hunit

private def barycentricHomotopyHom [Nonempty V]
    (K : PreAbstractSimplicialComplex V) (i j : ℕ) :
    (simplicialChainComplex (barycentricSubdivision K) R).X i ⟶
      (simplicialChainComplex (barycentricSubdivision K) R).X j :=
  if hij : i + 1 = j then
    ModuleCat.ofHom (barycentricHomotopyComponent R i K) ≫
      eqToHom (congrArg
        (fun k => (simplicialChainComplex (barycentricSubdivision K) R).X k) hij)
  else 0

private theorem barycentricHomotopy_zero_map_identity [Nonempty V]
    (K : PreAbstractSimplicialComplex V) :
    (barycentricChainMap K R 0).comp
        (vertexChainMap R (lastVertexMap K) 0) =
      (boundary (barycentricSubdivision K) R 0).comp
          (barycentricHomotopyComponent R 0 K) + LinearMap.id := by
  have heq := barycentricHomotopyEquation R 0 K
  change (boundary (barycentricSubdivision K) R 0).comp
      (barycentricHomotopyComponent R 0 K) =
    barycentricApproximation R K 0 at heq
  dsimp [barycentricApproximation] at heq
  rw [heq]
  abel

private theorem barycentricHomotopy_succ_map_identity [Nonempty V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    (barycentricChainMap K R (n + 1)).comp
        (vertexChainMap R (lastVertexMap K) (n + 1)) =
      (boundary (barycentricSubdivision K) R (n + 1)).comp
          (barycentricHomotopyComponent R (n + 1) K) +
        (barycentricHomotopyComponent R n K).comp
          (boundary (barycentricSubdivision K) R n) + LinearMap.id := by
  have heq := barycentricHomotopyEquation R (n + 1) K
  change (boundary (barycentricSubdivision K) R (n + 1)).comp
        (barycentricHomotopyComponent R (n + 1) K) +
      (barycentricHomotopyComponent R n K).comp
        (boundary (barycentricSubdivision K) R n) =
    barycentricApproximation R K (n + 1) at heq
  dsimp [barycentricApproximation] at heq
  rw [heq]
  abel

private theorem barycentricHomotopyHom_succ [Nonempty V]
    (K : PreAbstractSimplicialComplex V) (i : ℕ) :
    barycentricHomotopyHom R K i (i + 1) =
      ModuleCat.ofHom (barycentricHomotopyComponent R i K) := by
  simp [barycentricHomotopyHom]

@[simp] theorem lastVertexChainMap_f [Nonempty V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    (lastVertexChainMap R K).f n =
      ModuleCat.ofHom (vertexChainMap R (lastVertexMap K) n) := rfl

@[simp] theorem barycentricSubdivisionChainMap_f
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    (barycentricSubdivisionChainMap R K).f n =
      ModuleCat.ofHom (barycentricChainMap K R n) := rfl

/-- Last-vertex followed by subdivision is chain-homotopic to the identity
on barycentric subdivision. -/
noncomputable def barycentricSubdivisionHomotopy [Nonempty V]
    (K : PreAbstractSimplicialComplex V) :
    Homotopy
      (lastVertexChainMap R K ≫ barycentricSubdivisionChainMap R K)
      (𝟙 (simplicialChainComplex (barycentricSubdivision K) R)) where
  hom := barycentricHomotopyHom R K
  zero i j hij := dif_neg hij
  comm i := by
    cases i with
    | zero =>
        rw [prevD_eq (j' := 1) (w := by simp),
          dNext_eq_zero _ _ (by simp), zero_add]
        simp only [barycentricHomotopyHom_succ,
          lastVertexChainMap_f, barycentricSubdivisionChainMap_f,
          HomologicalComplex.comp_f, simplicialChainComplex_d]
        apply ModuleCat.hom_ext
        change (barycentricChainMap K R 0).comp
              (vertexChainMap R (lastVertexMap K) 0) =
          (boundary (barycentricSubdivision K) R 0).comp
              (barycentricHomotopyComponent R 0 K) + LinearMap.id
        exact barycentricHomotopy_zero_map_identity R K
    | succ n =>
        rw [dNext_eq (i' := n) (w := by simp),
          prevD_eq (j' := n + 2) (w := by simp)]
        simp only [barycentricHomotopyHom_succ,
          lastVertexChainMap_f, barycentricSubdivisionChainMap_f,
          HomologicalComplex.comp_f, simplicialChainComplex_d]
        apply ModuleCat.hom_ext
        change (barycentricChainMap K R (n + 1)).comp
                (vertexChainMap R (lastVertexMap K) (n + 1)) =
            (barycentricHomotopyComponent R n K).comp
                (boundary (barycentricSubdivision K) R n) +
              (boundary (barycentricSubdivision K) R (n + 1)).comp
                (barycentricHomotopyComponent R (n + 1) K) + LinearMap.id
        rw [barycentricHomotopy_succ_map_identity]
        abel

private theorem simplexChain_singleton (n : ℕ) (s : Finset V)
    (hs : s.Nonempty) (hc : s.card = n + 1)
    (c : Chain (simplexOn s) R n) :
    ∃ a : R, c = Finsupp.single (simplexFace s hs hc) a := by
  let σ := simplexFace s hs hc
  have hface : ∀ τ : Face (simplexOn s) n, τ = σ := by
    intro τ
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le τ.2.1.2
    change s.card ≤ τ.1.card
    rw [hc, τ.2.2]
  refine ⟨c σ, ?_⟩
  apply Finsupp.ext
  intro τ
  rw [hface τ]
  change c σ = (Finsupp.single σ (c σ)) σ
  exact Finsupp.single_eq_same.symm

private theorem deletedFace_injective (n : ℕ) (s : Face K (n + 1)) :
    Function.Injective (fun i : Fin (n + 2) => deletedFace K n s i) := by
  intro i j hij
  have hset :
      s.1.erase (s.1.orderEmbOfFin s.2.2 i) =
        s.1.erase (s.1.orderEmbOfFin s.2.2 j) := congrArg Subtype.val hij
  have hvertex := (Finset.erase_inj s.1
    (Finset.orderEmbOfFin_mem s.1 s.2.2 i)).mp hset
  exact (s.1.orderEmbOfFin s.2.2).injective hvertex

private theorem scalar_eq_one_of_boundary_eq (n : ℕ) (s : Face K (n + 1))
    (a : R)
    (hboundary : boundary K R n (Finsupp.single s a) =
      boundary K R n (Finsupp.single s (1 : R))) : a = 1 := by
  classical
  let i0 : Fin (n + 2) := ⟨0, by omega⟩
  let τ := deletedFace K n s i0
  have hsum :
      ((∑ i : Fin (n + 2),
        (Finsupp.single (deletedFace K n s i) ((-1 : R) ^ (i : ℕ)) : Chain K R n)) τ) =
        1 := by
    change Finsupp.applyAddHom τ
      (∑ i : Fin (n + 2),
        (Finsupp.single (deletedFace K n s i) ((-1 : R) ^ (i : ℕ)) : Chain K R n)) = 1
    rw [map_sum]
    rw [Finset.sum_eq_single i0]
    · simp [i0, τ]
    · intro i hi hne
      have hface : deletedFace K n s i ≠ τ := by
        intro h
        exact hne ((deletedFace_injective (K := K) n s) h)
      simp [hface]
    · intro hi
      exact (hi (Finset.mem_univ i0)).elim
  have hcoeff := congrArg (fun c : Chain K R n => c τ) hboundary
  rw [boundary_single, boundary_single] at hcoeff
  simp only [Finsupp.smul_apply, smul_eq_mul] at hcoeff
  rw [hsum] at hcoeff
  simpa using hcoeff

private theorem lastVertex_subdivisionSimplex_zero [Nonempty V]
    (s : Finset V) (hs : s.Nonempty) (hc : s.card = 1) :
    vertexChainMap R (lastVertexMap (simplexOn s)) 0
      (subdivisionSimplex R 0 s hs hc) =
    Finsupp.single (simplexFace s hs hc) (1 : R) := by
  let τ : Face (barycentricSubdivision (simplexOn s)) 0 :=
    ⟨{s}, subdivisionSimplexFace_mem s hs, by simp⟩
  have hsub : subdivisionSimplex R 0 s hs hc = Finsupp.single τ (1 : R) := rfl
  have hface :
      vertexImageFace (lastVertexMap (simplexOn s)) τ
        (by intro i j _; exact Fin.ext (by omega)) =
      simplexFace s hs hc := by
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
    have hmax : lastVertex s = v := by
      rw [lastVertex_of_nonempty s hs]
      rw [Finset.max'_eq_iff]
      constructor
      · rw [hv]
        simp
      · intro w hw
        rw [hv] at hw
        simp only [Finset.mem_singleton] at hw
        simpa [hw]
    apply Subtype.ext
    unfold vertexImageFace tupleFace
    have henum : τ.1.orderEmbOfFin τ.2.2 = (fun _ : Fin 1 => s) := by
      funext i
      have hi := Finset.orderEmbOfFin_mem τ.1 τ.2.2 i
      simpa [τ] using hi
    have hfun : lastVertexMap (simplexOn s) ∘ τ.1.orderEmbOfFin τ.2.2 =
        fun _ : Fin 1 => lastVertex s := by
      funext i
      simp [lastVertexMap, henum]
    change Finset.univ.image
        ((lastVertexMap (simplexOn s)).toFun ∘ τ.1.orderEmbOfFin τ.2.2) = s
    rw [hfun, Finset.image_const Finset.univ_nonempty (lastVertex s), hmax, hv]
  rw [hsub, vertexChainMap_vertex, hface]

private theorem lastVertex_after_barycentricChainMap [Nonempty V] :
    ∀ n : ℕ, ∀ K : PreAbstractSimplicialComplex V,
      (vertexChainMap R (lastVertexMap K) n).comp
        (barycentricChainMap K R n) = LinearMap.id := by
  intro n
  induction n with
  | zero =>
      intro K
      apply Finsupp.lhom_ext
      intro s a
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      let T := simplexOn s.1
      let h : T ≤ K := simplexOn_le s
      let hsd := TDA.Filtration.SubdivisionRips.subdivision_mono h
        (show (0 : ℝ) ≤ 0 by rfl)
      let σlocal := simplexFace s.1 (face_nonempty s) s.2.2
      have hface : faceIncl h 0 σlocal = s := by
        apply Subtype.ext
        rfl
      have hlocal := lastVertex_subdivisionSimplex_zero R s.1
        (face_nonempty s) s.2.2
      have hnat := LinearMap.congr_fun
        (lastVertexChainMap_naturality (R := R) (K := T) (L := K) h 0)
        (subdivisionSimplex R 0 s.1 (face_nonempty s) s.2.2)
      simp only [LinearMap.comp_apply] at hnat
      have hS : barycentricChainMap K R 0 (Finsupp.single s (1 : R)) =
          chainIncl R hsd 0 (subdivisionSimplex R 0 s.1
            (face_nonempty s) s.2.2) := by
        rw [barycentricChainMap_single, subdividedFace]
        simp only [one_smul]
      have hunit : vertexChainMap R (lastVertexMap K) 0
          (barycentricChainMap K R 0 (Finsupp.single s (1 : R))) =
          Finsupp.single s (1 : R) := by
        rw [hS]
        rw [← hnat, hlocal, chainIncl_single, hface]
      have hsingle : Finsupp.single s a = a • Finsupp.single s (1 : R) := by simp
      rw [hsingle]
      simp only [map_smul]
      exact congrArg (fun c => a • c) hunit
  | succ n ih =>
      intro K
      apply Finsupp.lhom_ext
      intro s a
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      let T := simplexOn s.1
      let h : T ≤ K := simplexOn_le s
      let hsd := TDA.Filtration.SubdivisionRips.subdivision_mono h
        (show (0 : ℝ) ≤ 0 by rfl)
      let σlocal := simplexFace s.1 (face_nonempty s) s.2.2
      have hface : faceIncl h (n + 1) σlocal = s := by
        apply Subtype.ext
        rfl
      have hsdSelf :
          TDA.Filtration.SubdivisionRips.subdivision_mono (simplexOn_le σlocal)
            (show (0 : ℝ) ≤ 0 by rfl) = le_refl (barycentricSubdivision T) := by
        apply Subsingleton.elim
      have hSlocal : barycentricChainMap T R (n + 1)
          (Finsupp.single σlocal (1 : R)) =
          subdivisionSimplex R (n + 1) s.1 (face_nonempty s) s.2.2 := by
        rw [barycentricChainMap_single, subdividedFace]
        simp only [one_smul]
        change chainIncl R
            (TDA.Filtration.SubdivisionRips.subdivision_mono (simplexOn_le σlocal)
              (show (0 : ℝ) ≤ 0 by rfl)) (n + 1)
            (subdivisionSimplex R (n + 1) σlocal.1
              (face_nonempty σlocal) σlocal.2.2) =
          subdivisionSimplex R (n + 1) s.1 (face_nonempty s) s.2.2
        rw [hsdSelf]
        have hid := LinearMap.congr_fun
          (chainIncl_id (barycentricSubdivision T) R (n + 1))
          (subdivisionSimplex R (n + 1) s.1 (face_nonempty s) s.2.2)
        have harg : subdivisionSimplex R (n + 1) σlocal.1
            (face_nonempty σlocal) σlocal.2.2 =
          subdivisionSimplex R (n + 1) s.1 (face_nonempty s) s.2.2 := by
          rfl
        rw [harg]
        change (chainIncl R (le_refl (barycentricSubdivision T)) (n + 1))
            (subdivisionSimplex R (n + 1) s.1 (face_nonempty s) s.2.2) = _
        exact hid
      have hnat := LinearMap.congr_fun
        (lastVertexChainMap_naturality (R := R) (K := T) (L := K) h (n + 1))
        (subdivisionSimplex R (n + 1) s.1 (face_nonempty s) s.2.2)
      simp only [LinearMap.comp_apply] at hnat
      let z := vertexChainMap R (lastVertexMap T) (n + 1)
        (subdivisionSimplex R (n + 1) s.1 (face_nonempty s) s.2.2)
      obtain ⟨b, hb⟩ := simplexChain_singleton R (n + 1) s.1
        (face_nonempty s) s.2.2 z
      have hL := LinearMap.congr_fun
        (boundary_vertexChainMap R (lastVertexMap T) n)
        (barycentricChainMap T R (n + 1)
          (Finsupp.single σlocal (1 : R)))
      simp only [LinearMap.comp_apply] at hL
      have hSboundary := LinearMap.congr_fun
        (barycentricChainMap_boundary R n T)
        (Finsupp.single σlocal (1 : R))
      simp only [LinearMap.comp_apply] at hSboundary
      have hIH := LinearMap.congr_fun (ih T)
        (boundary T R n (Finsupp.single σlocal (1 : R)))
      simp only [LinearMap.comp_apply] at hIH
      have hboundary : boundary T R n z =
          boundary T R n (Finsupp.single σlocal (1 : R)) := by
        calc
          boundary T R n z =
              vertexChainMap R (lastVertexMap T) n
                (boundary (barycentricSubdivision T) R n
                  (barycentricChainMap T R (n + 1)
                    (Finsupp.single σlocal (1 : R)))) := by
              dsimp only [z]
              rw [← hSlocal]
              exact hL
          _ = vertexChainMap R (lastVertexMap T) n
                (barycentricChainMap T R n
                  (boundary T R n (Finsupp.single σlocal (1 : R)))) := by
              rw [hSboundary]
          _ = boundary T R n (Finsupp.single σlocal (1 : R)) := hIH
      have hb_eq := hboundary
      rw [hb] at hb_eq
      have hb_one := scalar_eq_one_of_boundary_eq R n σlocal b hb_eq
      rw [hb_one] at hb
      have hunit : vertexChainMap R (lastVertexMap K) (n + 1)
          (barycentricChainMap K R (n + 1) (Finsupp.single s (1 : R))) =
          Finsupp.single s (1 : R) := by
        have hS : barycentricChainMap K R (n + 1)
            (Finsupp.single s (1 : R)) = chainIncl R hsd (n + 1)
              (subdivisionSimplex R (n + 1) s.1 (face_nonempty s) s.2.2) := by
          rw [barycentricChainMap_single, subdividedFace]
          simp only [one_smul]
        rw [hS, ← hnat]
        change chainIncl R h (n + 1) z = Finsupp.single s (1 : R)
        rw [hb, chainIncl_single, hface]
      have hsingle : Finsupp.single s a = a • Finsupp.single s (1 : R) := by simp
      rw [hsingle]
      simp only [map_smul]
      exact congrArg (fun c => a • c) hunit

/-- The subdivision chain map followed by the last-vertex chain map is the
identity on the original chain complex. -/
theorem barycentricSubdivisionChainMap_lastVertex_eq_id [Nonempty V]
    (K : PreAbstractSimplicialComplex V) :
    barycentricSubdivisionChainMap R K ≫ lastVertexChainMap R K =
      𝟙 (simplicialChainComplex K R) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, barycentricSubdivisionChainMap_f,
    lastVertexChainMap_f]
  apply ModuleCat.hom_ext
  exact lastVertex_after_barycentricChainMap R n K

/-- The last-vertex and subdivision chain maps form a homotopy equivalence. -/
noncomputable def barycentricChainHomotopyEquiv [Nonempty V]
    (K : PreAbstractSimplicialComplex V) :
    HomotopyEquiv (simplicialChainComplex (barycentricSubdivision K) R)
      (simplicialChainComplex K R) where
  hom := lastVertexChainMap R K
  inv := barycentricSubdivisionChainMap R K
  homotopyHomInvId := barycentricSubdivisionHomotopy R K
  homotopyInvHomId := Homotopy.ofEq
    (barycentricSubdivisionChainMap_lastVertex_eq_id R K)

/-- Barycentric subdivision induces a natural isomorphism on simplicial homology. -/
noncomputable def barycentricHomologyIso [Nonempty V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    simplicialHomology (barycentricSubdivision K) R n ≅ simplicialHomology K R n :=
  (barycentricChainHomotopyEquiv R K).toHomologyIso n

/-- The barycentric homology isomorphism commutes with same-carrier inclusions. -/
theorem barycentricHomologyIso_naturality [Nonempty V] (h : K ≤ L) (n : ℕ) :
    simplicialHomologyIncl R
        (TDA.Filtration.SubdivisionRips.subdivision_mono h
          (show (0 : ℝ) ≤ 0 by rfl)) n ≫ (barycentricHomologyIso R L n).hom =
      (barycentricHomologyIso R K n).hom ≫ simplicialHomologyIncl R h n := by
  change simplicialHomologyIncl R
      (TDA.Filtration.SubdivisionRips.subdivision_mono h
        (show (0 : ℝ) ≤ 0 by rfl)) n ≫ lastVertexHomologyMap R L n =
    lastVertexHomologyMap R K n ≫ simplicialHomologyIncl R h n
  exact lastVertexHomologyMap_naturality R h n

end

end TDA.Simplicial
