import TDA.Persistence.Reduction.FiniteInputBasisTransition
import Mathlib.LinearAlgebra.StdBasis

/-!
# A complete computed basis of integer-sublevel homology

The coordinate equivalence reads normal-form coefficients in the order of the
degree-specific query. Its inverse expresses every actual homology class uniquely
as a sum of the returned cycle classes.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration Module

private theorem cast_alive_iff {m n : ℕ} (hn : m = n)
    (d : Fin m → ℕ) (R : Matrix (Fin m) (Fin m) (ZMod 2))
    (p t : ℕ) (i : Fin m) :
    AliveCoordinate (fun j => d ((finCongr hn).symm j))
      ((Matrix.reindex (finCongr hn) (finCongr hn)) R) p t ((finCongr hn) i) ↔
      AliveCoordinate d R p t i := by
  cases hn
  rfl

private noncomputable def faceLabelEquiv (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    letI := faceFintype xs h
    BasisIndex xs p a ≃ {j // AliveCoordinate (faceDegree (compatibleOrder xs h))
      (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h)) p (sublevelStage xs a) j} := by
  letI := faceFintype xs h
  let e := finCongr (faceCount_eq_length xs h)
  let f := fun i : BasisIndex xs p a =>
    (⟨e.symm (basisRecord xs p a i).birthIndex,
      alive_faceVector xs h p _ _ (basisRecord_alive xs h p a i)⟩ :
      {j // AliveCoordinate (faceDegree (compatibleOrder xs h))
        (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h)) p (sublevelStage xs a) j})
  apply Equiv.ofBijective f
  constructor
  · intro i j he
    exact basisRecord_birth_injective xs p a (e.symm.injective (congrArg Subtype.val he))
  · intro j
    have hd : degree xs = fun i => faceDegree (compatibleOrder xs h) (e.symm i) := by
      funext i
      exact degree_eq_faceDegree xs h i
    have hi : AliveCoordinate (degree xs) (reduced xs) p (sublevelStage xs a) (e j.1) := by
      rw [hd, reduced_reindex xs h]
      exact (cast_alive_iff (faceCount_eq_length xs h) _ _ p _ j.1).mpr j.2
    obtain ⟨i, hi⟩ := (basisRecord_birth_bijective xs h p a).2 ⟨e j.1, hi⟩
    refine ⟨i, Subtype.ext ?_⟩
    exact (congrArg e.symm (congrArg Subtype.val hi)).trans (e.symm_apply_apply j.1)

private noncomputable def aliveRecordCoordinates (xs : Input) (h : Valid xs)
    (p : ℕ) (a : ℤ) :
    letI := faceFintype xs h
    aliveSpace (faceDegree (compatibleOrder xs h))
      (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h)) p (sublevelStage xs a) ≃ₗ[ZMod 2]
        (BasisIndex xs p a → ZMod 2) := by
  classical
  letI := faceFintype xs h
  let e := faceLabelEquiv xs h p a
  exact
    { toFun := fun x i => x.1 (e i).1
      invFun := fun c => ⟨fun j => if hj : AliveCoordinate (faceDegree (compatibleOrder xs h))
          (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h)) p (sublevelStage xs a) j
          then c (e.symm ⟨j, hj⟩) else 0, by
        intro j hj
        simp only [dif_neg hj]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext j
        by_cases hj : AliveCoordinate (faceDegree (compatibleOrder xs h))
            (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h)) p (sublevelStage xs a) j
        · simp only [dif_pos hj, Equiv.apply_symm_apply]
        · simp only [dif_neg hj, x.2 j hj]
      right_inv := by
        intro c
        funext i
        simp only [dif_pos (e i).2]
        change c (e.symm (e i)) = c i
        rw [e.symm_apply_apply]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- All actual homology classes in the finite, ordered computed coordinates. -/
noncomputable def sublevelCoordinates (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p ≃ₗ[ZMod 2]
      (BasisIndex xs p a → ZMod 2) := by
  letI := faceFintype xs h
  exact (sublevelHomologyToAlive xs h p a).trans (aliveRecordCoordinates xs h p a)

theorem sublevelCoordinates_apply (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (x : simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p)
    (i : BasisIndex xs p a) :
    letI := faceFintype xs h
    sublevelCoordinates xs h p a x i = (sublevelHomologyToAlive xs h p a x).1
      ((finCongr (faceCount_eq_length xs h)).symm (basisRecord xs p a i).birthIndex) := rfl

private noncomputable def classOfDegree (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (hp : r.occurrence.degree = p) (ha : r.occurrence.birth ≤ a) :
    simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p :=
  hp ▸ sublevelClass xs h r hr a ha

private theorem classOfDegree_coordinate (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (hp : r.occurrence.degree = p) (ha : r.occurrence.AliveAt a) :
    letI := faceFintype xs h
    (sublevelHomologyToAlive xs h p a (classOfDegree xs h p a r hr hp ha.1)).1 =
      Pi.single ((finCongr (faceCount_eq_length xs h)).symm r.birthIndex) (1 : ZMod 2) := by
  subst p
  exact sublevelClass_coordinate xs h r hr a ha

/-- The exact returned cycle class, regarded in the query's selected degree. -/
noncomputable def basisClass (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (i : BasisIndex xs p a) :
    simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p :=
  classOfDegree xs h p a (basisRecord xs p a i) (basisRecord_spec xs p a i).1
    (basisRecord_spec xs p a i).2.2 (basisRecord_spec xs p a i).2.1.1

theorem basisClass_eq_sublevelClass (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (i : BasisIndex xs p a) :
    basisClass xs h p a i =
      (basisRecord_spec xs p a i).2.2 ▸
        sublevelClass xs h (basisRecord xs p a i) (basisRecord_spec xs p a i).1 a
          (basisRecord_spec xs p a i).2.1.1 := rfl

theorem sublevelCoordinates_basisClass (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (i : BasisIndex xs p a) :
    sublevelCoordinates xs h p a (basisClass xs h p a i) = Pi.single i (1 : ZMod 2) := by
  let := faceFintype xs h
  funext j
  rw [sublevelCoordinates_apply]
  have hc := classOfDegree_coordinate xs h p a (basisRecord xs p a i)
    (basisRecord_spec xs p a i).1 (basisRecord_spec xs p a i).2.2
    (basisRecord_spec xs p a i).2.1
  rw [show (sublevelHomologyToAlive xs h p a (basisClass xs h p a i)).1 = _ from hc]
  simp only [Pi.single_apply, (finCongr (faceCount_eq_length xs h)).symm.injective.eq_iff,
    (basisRecord_birth_injective xs p a).eq_iff]

/-- The returned cycle classes form a basis of the entire actual sublevel homology. -/
noncomputable def sublevelBasis (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    Basis (BasisIndex xs p a) (ZMod 2)
      (simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p) :=
  Basis.ofEquivFun (sublevelCoordinates xs h p a)

theorem sublevelBasis_apply (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (i : BasisIndex xs p a) : sublevelBasis xs h p a i = basisClass xs h p a i := by
  apply (sublevelCoordinates xs h p a).injective
  have hi := congrFun (Basis.coe_ofEquivFun (sublevelCoordinates xs h p a)) i
  rw [sublevelBasis, hi, LinearEquiv.apply_symm_apply, sublevelCoordinates_basisClass]

theorem sublevelBasis_repr (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (x : simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p)
    (i : BasisIndex xs p a) :
    (sublevelBasis xs h p a).repr x i = sublevelCoordinates xs h p a x i :=
  Basis.ofEquivFun_repr_apply _ _ _

/-- Expansion of an arbitrary actual class in the exact computed cycle classes. -/
theorem sublevelClass_expansion (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (x : simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p) :
    ∑ i, sublevelCoordinates xs h p a x i • basisClass xs h p a i = x := by
  simpa only [sublevelBasis_apply, sublevelBasis_repr] using (sublevelBasis xs h p a).sum_repr x

/-- Every class has exactly one coefficient vector in the returned cycle classes. -/
theorem sublevelClass_unique_expansion (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (x : simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p) :
    ∃! c : BasisIndex xs p a → ZMod 2, ∑ i, c i • basisClass xs h p a i = x := by
  refine ⟨sublevelCoordinates xs h p a x, ?_, ?_⟩
  · exact sublevelClass_expansion xs h p a x
  · intro c hc
    apply funext
    intro j
    have he := congrArg (fun y => sublevelCoordinates xs h p a y j) hc
    simpa [map_sum, map_smul, sublevelCoordinates_basisClass, Pi.single_apply] using he

theorem sublevelHomology_finrank (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    Module.finrank (ZMod 2) (simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p) =
      (activeRepresentatives xs p a).length := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (sublevelBasis xs h p a)

private theorem classOfDegree_naturality (xs : Input) (h : Valid xs) (p : ℕ)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (hp : r.occurrence.degree = p) (a b : ℤ) (hab : a ≤ b)
    (ha : r.occurrence.birth ≤ a) (hb : r.occurrence.birth ≤ b) :
    (simplicialHomologyIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab) p).hom
      (classOfDegree xs h p a r hr hp ha) = classOfDegree xs h p b r hr hp hb := by
  subst p
  exact sublevelClass_naturality xs h r hr a b hab ha hb

private theorem classOfDegree_eval (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (hp : r.occurrence.degree = p) (hb : r.occurrence.birth ≤ a)
    (j : BasisIndex xs p a) :
    sublevelCoordinates xs h p a (classOfDegree xs h p a r hr hp hb) j =
      if (basisRecord xs p a j).birthIndex = r.birthIndex then 1 else 0 := by
  let := faceFintype xs h
  by_cases ha : r.occurrence.AliveAt a
  · rw [sublevelCoordinates_apply]
    rw [classOfDegree_coordinate xs h p a r hr hp ha]
    simp only [Pi.single_apply, (finCongr (faceCount_eq_length xs h)).symm.injective.eq_iff]
  · have hz : sublevelClass xs h r hr a hb = 0 := by
      by_contra hn
      exact ha ((sublevelClass_nonzero_iff xs h r hr a hb).mp hn)
    have hz' : classOfDegree xs h p a r hr hp hb = 0 := by
      subst p
      exact hz
    have hn : (basisRecord xs p a j).birthIndex ≠ r.birthIndex := by
      intro he
      have heq := representedOccurrences_birth_injective xs (basisRecord xs p a j) r
        (basisRecord_spec xs p a j).1 hr he
      exact ha (heq ▸ (basisRecord_spec xs p a j).2.1)
    rw [hz', map_zero]
    simp only [Pi.zero_apply, if_neg hn]

/-- One column of the inclusion matrix, for the exact computed cycle class. -/
theorem sublevelCoordinates_inclusion_basisClass (xs : Input) (h : Valid xs)
    (p : ℕ) (a b : ℤ) (hab : a ≤ b) (i : BasisIndex xs p a) :
    sublevelCoordinates xs h p b
      ((simplicialHomologyIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab) p).hom
        (basisClass xs h p a i)) = fun j => basisTransition xs p a b j i := by
  let r := basisRecord xs p a i
  have hr := (basisRecord_spec xs p a i).1
  have hp := (basisRecord_spec xs p a i).2.2
  have ha := (basisRecord_spec xs p a i).2.1.1
  change sublevelCoordinates xs h p b
    ((simplicialHomologyIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab) p).hom
      (classOfDegree xs h p a r hr hp ha)) = _
  rw [classOfDegree_naturality xs h p r hr hp a b hab ha (ha.trans hab)]
  funext j
  exact classOfDegree_eval xs h p b r hr hp (ha.trans hab) j

/-- The executable birth-matching matrix represents the actual inclusion on every class. -/
theorem sublevelCoordinates_naturality (xs : Input) (h : Valid xs) (p : ℕ)
    (a b : ℤ) (hab : a ≤ b)
    (x : simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p) :
    sublevelCoordinates xs h p b
      ((simplicialHomologyIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab) p).hom x) =
      (basisTransition xs p a b).mulVec (sublevelCoordinates xs h p a x) := by
  let f := (simplicialHomologyIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab) p).hom
  let c := sublevelCoordinates xs h p a x
  calc
    sublevelCoordinates xs h p b (f x) =
        sublevelCoordinates xs h p b (f (∑ i, c i • basisClass xs h p a i)) :=
      congrArg (fun y => sublevelCoordinates xs h p b (f y))
        (sublevelClass_expansion xs h p a x).symm
    _ = (basisTransition xs p a b).mulVec c := by
      funext j
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        sublevelCoordinates_inclusion_basisClass xs h p a b hab,
        Matrix.mulVec, dotProduct, f]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _

/-- Consecutive coordinate matrices compose with the actual inclusions. -/
theorem basisTransition_comp (xs : Input) (h : Valid xs) (p : ℕ)
    (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    basisTransition xs p b c * basisTransition xs p a b = basisTransition xs p a c := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨x, rfl⟩ := (sublevelCoordinates xs h p a).surjective v
  rw [← Matrix.mulVec_mulVec, ← sublevelCoordinates_naturality xs h p a b hab,
    ← sublevelCoordinates_naturality xs h p b c hbc,
    ← sublevelCoordinates_naturality xs h p a c (hab.trans hbc)]
  congr 1
  exact congrArg (fun f => f.hom x)
    (simplicialHomologyIncl_comp (ZMod 2) ((gradeFilter xs h).sublevel_mono hab)
      ((gradeFilter xs h).sublevel_mono hbc) p).symm

end TDA.Persistence.Reduction.FiniteInput
