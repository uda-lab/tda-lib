import TDA.Persistence.GeneratedUpsetQuotientResolution

/-!
# Consumers of the hook quotient resolution

Concrete quotient classes distinguish generator occurrences even when their births agree.
The examples also use the actual rank-exact kernel rows, lower-complement target, and the
zero terms arising from bottom-valued and empty families.
-/

set_option autoImplicit false

namespace TDA.Persistence.GeneratedUpsetQuotientResolution.Examples

open CategoryTheory CategoryTheory.Limits
open GeneratedUpsetResolution

private instance : HasFiniteBiproducts (PModule ℚ ℕ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable def hookClass {m r : ℕ} (f : Fin m → ℕ) (A : FaceIndex m r)
    (p : ℕ) (hp : p ∈ Hook.support 0 (faceJoin f A)) :
    (term (k := ℚ) f r).obj p :=
  ((hookSumIso (k := ℚ) f r).inv.app p).hom
    (((biproduct.ι (fun B : FaceIndex m r => Hook.module (k := ℚ) 0 (faceJoin f B)) A).app p).hom
      (SupportInterval.one _ hp))

private theorem hookClass_coordinate {m r : ℕ} (f : Fin m → ℕ) (A B : FaceIndex m r)
    (p : ℕ) (hp : p ∈ Hook.support 0 (faceJoin f A)) :
    (((biproduct.π (fun C : FaceIndex m r => Hook.module (k := ℚ) 0 (faceJoin f C)) B).app p).hom
      (((hookSumIso (k := ℚ) f r).hom.app p).hom (hookClass f A p hp)) : ℚ) =
      if A = B then 1 else 0 := by
  classical
  unfold hookClass
  have he := congrArg (fun t : (⨁ (fun C : FaceIndex m r =>
    Hook.module (k := ℚ) 0 (faceJoin f C))) ⟶ _ =>
      (t.app p).hom (((biproduct.ι (fun C : FaceIndex m r =>
        Hook.module (k := ℚ) 0 (faceJoin f C)) A).app p).hom (SupportInterval.one _ hp)))
    (hookSumIso (k := ℚ) f r).inv_hom_id
  change ((hookSumIso (k := ℚ) f r).hom.app p).hom
    (((hookSumIso (k := ℚ) f r).inv.app p).hom _) = _ at he
  simp only [NatTrans.id_app] at he
  rw [he]
  change (((biproduct.ι (fun C : FaceIndex m r =>
    Hook.module (k := ℚ) 0 (faceJoin f C)) A ≫
      biproduct.π (fun C : FaceIndex m r => Hook.module (k := ℚ) 0 (faceJoin f C)) B).app p).hom
        (SupportInterval.one _ hp) : ℚ) = _
  by_cases hAB : A = B
  · subst B
    rw [biproduct.ι_π_self, if_pos rfl]
    rfl
  · rw [biproduct.ι_π_ne _ hAB, if_neg hAB]
    rfl

private theorem hookClass_ne_zero {m r : ℕ} (f : Fin m → ℕ) (A : FaceIndex m r)
    (p : ℕ) (hp : p ∈ Hook.support 0 (faceJoin f A)) : hookClass f A p hp ≠ 0 := by
  intro hz
  have h := hookClass_coordinate f A A p hp
  rw [hz, map_zero, map_zero] at h
  norm_num at h

/-- The one-generator quotient at degree zero has a nonzero class below the generator. -/
theorem one_generator_quotient_nonzero :
    ∃ x : (term (k := ℚ) (fun _ : Fin 1 => (1 : ℕ)) 0).obj 0, x ≠ 0 := by
  let A : FaceIndex 1 0 := singletonFaceIndex 0
  have hp : 0 ∈ Hook.support 0 (faceJoin (fun _ : Fin 1 => (1 : ℕ)) A) := by
    simp [A, faceJoin_singleton, Hook.support]
  exact ⟨hookClass _ A 0 hp, hookClass_ne_zero _ A 0 hp⟩

/-- Repeated generators still give two distinct nonzero occurrence classes in quotient degree zero. -/
theorem repeated_occurrence_classes_distinct :
    ∃ x y : (term (k := ℚ) (fun _ : Fin 2 => (1 : ℕ)) 0).obj 0,
      x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y := by
  let f : Fin 2 → ℕ := fun _ => 1
  let A : FaceIndex 2 0 := singletonFaceIndex 0
  let B : FaceIndex 2 0 := singletonFaceIndex 1
  have hpA : 0 ∈ Hook.support 0 (faceJoin f A) := by simp [A, f, Hook.support]
  have hpB : 0 ∈ Hook.support 0 (faceJoin f B) := by simp [B, f, Hook.support]
  have hAB : A ≠ B := by decide
  refine ⟨hookClass f A 0 hpA, hookClass f B 0 hpB,
    hookClass_ne_zero f A 0 hpA, hookClass_ne_zero f B 0 hpB, ?_⟩
  intro hxy
  have hx := hookClass_coordinate f A A 0 hpA
  have hy := hookClass_coordinate f B A 0 hpB
  rw [hxy] at hx
  rw [if_pos rfl] at hx
  rw [if_neg (Ne.symm hAB)] at hy
  exact zero_ne_one (hy.symm.trans hx)

/-- For two distinct births, the degree-one quotient has a nonzero face class. -/
theorem two_generator_positive_quotient_nonzero :
    ∃ x : (term (k := ℚ) (fun i : Fin 2 => i.val + 1) 1).obj 0, x ≠ 0 := by
  let A : FaceIndex 2 1 := ⟨Finset.univ, by decide⟩
  have hp : 0 ∈ Hook.support 0 (faceJoin (fun i : Fin 2 => i.val + 1) A) := by
    refine ⟨Nat.zero_le _, ?_⟩
    intro h
    have h1 : 1 ≤ faceJoin (fun i : Fin 2 => i.val + 1) A := by
      exact Finset.le_sup' (f := fun i : Fin 2 => i.val + 1) (show (0 : Fin 2) ∈ A.1 by simp [A])
    omega
  exact ⟨hookClass _ A 0 hp, hookClass_ne_zero _ A 0 hp⟩

/-- The two-generator quotient uses the actual differential's rank-exact kernel row. -/
theorem two_generator_kernel_row_rankExact :
    IsRankExact
      (kernel.ι (differential (k := ℚ) (fun i : Fin 2 => i.val + 1) 0))
      (kernelRowLift (augmentation_range_eq_ker (k := ℚ) (fun i : Fin 2 => i.val + 1))) :=
  zero_kernelRow_rankExact _

/-- Bottom-valued generators yield zero quotient terms even for a nonempty family. -/
theorem bottom_generator_quotients_zero (r : ℕ) :
    IsZero (term (k := ℚ) (fun _ : Fin 1 => (0 : ℕ)) r) :=
  term_bottomFamily_isZero 1 r

/-- A repeated nonempty family has precisely the expected lower-complement target. -/
noncomputable def repeated_targetIso :
    target (k := ℚ) (fun _ : Fin 2 => (1 : ℕ)) ≅
      SupportInterval.module (k := ℚ) (complementSupport (fun _ : Fin 2 => (1 : ℕ)))
        (complementSupport_ordConnected _) := targetIso _ (by decide)

/-- Below a repeated generator, the actual target projection preserves the coefficient one. -/
theorem repeated_target_projection_coefficient :
    (((targetProjection (k := ℚ) (fun _ : Fin 2 => (1 : ℕ)) (by decide)).app 0).hom
      (SupportInterval.one _ (mem_generatedSupport_bottom (by decide : 0 < 2) 0)) : ℚ) = 1 := by
  rw [targetProjection_val, if_pos]
  · rfl
  · simp [complementSupport]

/-- The empty occurrence family has zero quotient terms and zero augmented target. -/
theorem empty_family_quotients_zero (r : ℕ) :
    IsZero (term (k := ℚ) (fun i : Fin 0 => (Fin.elim0 i : ℕ)) r) ∧
      IsZero (target (k := ℚ) (fun i : Fin 0 => (Fin.elim0 i : ℕ))) :=
  ⟨term_fin_zero_isZero _ r, target_fin_zero_isZero _⟩

end TDA.Persistence.GeneratedUpsetQuotientResolution.Examples
