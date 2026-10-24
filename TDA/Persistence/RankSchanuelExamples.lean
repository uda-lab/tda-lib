import TDA.Persistence.RankSchanuel
import TDA.Persistence.HookEndomorphisms

/-!
# Persistent Schanuel with redundant covers

A genuine two-coordinate hook is covered by two and by three copies of
itself. Both covers have nonzero kernels. The first sequence uses the
original hook as its kernel term through the diagonal `(1,-1)`, rather
than naming the categorical kernel. These data exercise both source
transport and positive-width Schanuel, in arbitrary characteristic.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankSchanuelExamples

open CategoryTheory CategoryTheory.Limits CoordinateShift
open scoped TDA.Persistence NNReal ZeroObject

private instance {k : Type u} [Field k] {J : Type} [PartialOrder J] :
    HasBinaryBiproducts (PModule.{u,0,u} k J) := HasBinaryBiproducts.of_hasBinaryProducts

/-- The birth of the two-coordinate hook. -/
def birthGrade : Fin 2 → ℝ := fun _ => 0

/-- The finite death of the two-coordinate hook. -/
def deathGrade : Fin 2 → ℝ := fun _ => 2

private theorem birth_lt_death : birthGrade < deathGrade := by
  apply lt_of_le_of_ne
  · intro j; norm_num [birthGrade, deathGrade]
  · intro h
    have h0 := congrFun h 0
    norm_num [birthGrade, deathGrade] at h0

variable (k : Type u) [Field k]

/-- A hook with unbounded support in the real plane. -/
noncomputable abbrev hook : PModule.{u,0,u} k (Fin 2 → ℝ) :=
  Hook.module birthGrade deathGrade

/-- A redundant cover source with two occurrences. -/
noncomputable abbrev cover : PModule.{u,0,u} k (Fin 2 → ℝ) := hook k ⊞ hook k

/-- A second redundant cover source with three occurrences. -/
noncomputable abbrev cover3 : PModule.{u,0,u} k (Fin 2 → ℝ) := cover k ⊞ hook k

private theorem biprod_projective {A B : PModule.{u,0,u} k (Fin 2 → ℝ)}
    (hA : IsRankProjective A) (hB : IsRankProjective B) : IsRankProjective (A ⊞ B) := by
  intro L M N ι π hs α
  obtain ⟨f, hf⟩ := hA L M N ι π hs (biprod.inl ≫ α)
  obtain ⟨g, hg⟩ := hB L M N ι π hs (biprod.inr ≫ α)
  refine ⟨biprod.desc f g, ?_⟩
  apply biprod.hom_ext'
  · simpa only [← Category.assoc, biprod.inl_desc] using hf
  · simpa only [← Category.assoc, biprod.inr_desc] using hg

private theorem cover_projective : IsRankProjective (cover k) :=
  biprod_projective k (Hook.isRankProjective birth_lt_death) (Hook.isRankProjective birth_lt_death)

private theorem cover3_projective : IsRankProjective (cover3 k) :=
  biprod_projective k (cover_projective k) (Hook.isRankProjective birth_lt_death)

private theorem binary_finiteDimensional (A B : PModule.{u,0,u} k (Fin 2 → ℝ))
    (a : Fin 2 → ℝ) [FiniteDimensional k (A.obj a)] [FiniteDimensional k (B.obj a)] :
    FiniteDimensional k ((A ⊞ B).obj a) := by
  let := preservesBinaryBiproduct_of_preservesBinaryProduct
    ((evaluation (Fin 2 → ℝ) (ModuleCat.{u} k)).obj a) (X := A) (Y := B)
  let e := Functor.mapBiprod ((evaluation (Fin 2 → ℝ) (ModuleCat.{u} k)).obj a) A B ≪≫
    ModuleCat.biprodIsoProd (A.obj a) (B.obj a)
  exact FiniteDimensional.of_injective e.hom.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)

private instance cover_finiteDimensional (a : Fin 2 → ℝ) :
    FiniteDimensional k ((cover k).obj a) := binary_finiteDimensional k (hook k) (hook k) a

private instance cover3_finiteDimensional (a : Fin 2 → ℝ) :
    FiniteDimensional k ((cover3 k).obj a) := binary_finiteDimensional k (cover k) (hook k) a

/-- The first kernel inclusion is the actual diagonal `(1,-1)`. -/
noncomputable def diagonal : hook k ⟶ cover k := biprod.lift (𝟙 _) (-𝟙 _)

/-- The quotient adds the two redundant coordinates. -/
noncomputable def quotient2 : cover k ⟶ hook k := biprod.fst + biprod.snd

/-- The second quotient adds all three redundant coordinates. -/
noncomputable def quotient3 : cover3 k ⟶ hook k := biprod.desc (quotient2 k) (𝟙 _)

private theorem fst_diagonal (a : Fin 2 → ℝ) (x : (hook k).obj a) :
    ((biprod.fst : cover k ⟶ hook k).app a).hom (((diagonal k).app a).hom x) = x :=
  congrArg (fun f : hook k ⟶ hook k => (f.app a).hom x) (biprod.lift_fst (𝟙 _) (-𝟙 _))

private theorem snd_diagonal (a : Fin 2 → ℝ) (x : (hook k).obj a) :
    ((biprod.snd : cover k ⟶ hook k).app a).hom (((diagonal k).app a).hom x) = -x :=
  congrArg (fun f : hook k ⟶ hook k => (f.app a).hom x) (biprod.lift_snd (𝟙 _) (-𝟙 _))

private theorem quotient2_app (a : Fin 2 → ℝ) (x : (cover k).obj a) :
    ((quotient2 k).app a).hom x =
      ((biprod.fst : cover k ⟶ hook k).app a).hom x +
        ((biprod.snd : cover k ⟶ hook k).app a).hom x := rfl

private theorem cover_fiber_ext (a : Fin 2 → ℝ) {x y : (cover k).obj a}
    (h₁ : ((biprod.fst : cover k ⟶ hook k).app a).hom x =
      ((biprod.fst : cover k ⟶ hook k).app a).hom y)
    (h₂ : ((biprod.snd : cover k ⟶ hook k).app a).hom x =
      ((biprod.snd : cover k ⟶ hook k).app a).hom y) : x = y := by
  have hf : HookInfinity.fromBirth a (cover k) x ≫ biprod.fst =
      HookInfinity.fromBirth a (cover k) y ≫ biprod.fst := by
    apply HookInfinity.hom_ext
    simpa only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
      HookInfinity.fromBirth_birth] using h₁
  have hg : HookInfinity.fromBirth a (cover k) x ≫ biprod.snd =
      HookInfinity.fromBirth a (cover k) y ≫ biprod.snd := by
    apply HookInfinity.hom_ext
    simpa only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
      HookInfinity.fromBirth_birth] using h₂
  have he := biprod.hom_ext _ _ hf hg
  simpa only [HookInfinity.fromBirth_birth] using congrArg
    (fun f : HookInfinity.module (R := k) a ⟶ cover k => (f.app a).hom (HookInfinity.birth a)) he

private theorem quotient2_section : (biprod.inl : hook k ⟶ cover k) ≫ quotient2 k = 𝟙 _ := by
  simp [quotient2, Preadditive.comp_add]

private theorem pointwise2 : IsPointwiseShortExact (diagonal k) (quotient2 k) where
  injective a := by
    intro x y h
    have he := congrArg ((biprod.fst : cover k ⟶ hook k).app a).hom h
    exact (fst_diagonal k a x).symm.trans (he.trans (fst_diagonal k a y))
  surjective a := by
    intro x
    refine ⟨((biprod.inl : hook k ⟶ cover k).app a).hom x, ?_⟩
    exact congrArg (fun f : hook k ⟶ hook k => (f.app a).hom x) (quotient2_section k)
  range_eq_ker a := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change ((quotient2 k).app a).hom (((diagonal k).app a).hom x) = 0
      rw [quotient2_app, fst_diagonal, snd_diagonal, add_neg_cancel]
    · intro hy
      refine ⟨((biprod.fst : cover k ⟶ hook k).app a).hom y, ?_⟩
      apply cover_fiber_ext k a
      · exact fst_diagonal k a _
      · rw [snd_diagonal]
        have hsum : ((biprod.fst : cover k ⟶ hook k).app a).hom y +
            ((biprod.snd : cover k ⟶ hook k).app a).hom y = 0 :=
          (quotient2_app k a y).symm.trans hy
        have he := congrArg Neg.neg (eq_neg_of_add_eq_zero_left hsum)
        simpa only [neg_neg] using he

/-- A rank-exact sequence with the original hook as its noncanonical kernel term. -/
theorem rankExact2 : IsRankExact (diagonal k) (quotient2 k) :=
  (pointwise2 k).rankExact_of_section biprod.inl (quotient2_section k)

private theorem quotient3_section : (biprod.inr : hook k ⟶ cover3 k) ≫ quotient3 k = 𝟙 _ :=
  biprod.inr_desc _ _

/-- The three-copy cover has its actual rank-exact categorical kernel sequence. -/
theorem rankExact3 : IsRankExact (kernel.ι (quotient3 k)) (quotient3 k) := by
  have hsurj : ∀ a, Function.Surjective ((quotient3 k).app a).hom := by
    intro a x
    refine ⟨((biprod.inr : hook k ⟶ cover3 k).app a).hom x, ?_⟩
    exact congrArg (fun f : hook k ⟶ hook k => (f.app a).hom x) (quotient3_section k)
  exact (RankKernel.shortExact (quotient3 k) hsurj).rankExact_of_section
    biprod.inr (quotient3_section k)

/-- Positive-width Schanuel for redundant covers of different sizes. -/
noncomputable def positiveInterleaving :
    CoordinateInterleaving 1 (cover k ⊞ (shift 1).obj (kernel (quotient3 k)))
      ((shift 1).obj (hook k) ⊞ cover3 k) :=
  RankSchanuel.interleavingOfSequences (quotient2 k) (quotient3 k)
    (CoordinateInterleaving.refl 1 (hook k)) (rankExact2 k) (rankExact3 k)
    (cover_projective k) (cover3_projective k)

/-- The same actual noncanonical sequence works at width zero. -/
theorem zero_width :
    Nonempty ((cover k ⊞ (shift 0).obj (kernel (quotient3 k))) ≅
      ((shift 0).obj (hook k) ⊞ cover3 k)) :=
  ⟨(RankSchanuel.interleavingOfSequences (quotient2 k) (quotient3 k)
    (CoordinateInterleaving.refl 0 (hook k)) (rankExact2 k) (rankExact3 k)
    (cover_projective k) (cover3_projective k)).toIso⟩

/-- Static Schanuel is constructed for the two actual categorical kernels. -/
theorem static_kernel_sum :
    Nonempty ((cover k ⊞ kernel (quotient3 k)) ≅ (kernel (quotient2 k) ⊞ cover3 k)) :=
  ⟨RankSchanuel.kernelSumIso (quotient2 k) (quotient3 k)
    (rankExact2 k).isRankDeflation (rankExact3 k).isRankDeflation
    (cover_projective k) (cover3_projective k)⟩

private noncomputable def unitAtBirth : (hook k).obj birthGrade :=
  SupportInterval.one (Hook.support birthGrade deathGrade) (Hook.birth_mem birth_lt_death)

private theorem unitAtBirth_ne_zero : unitAtBirth k ≠ 0 := by
  intro h
  have he := congrArg (fun x : (hook k).obj birthGrade => (x : k)) h
  exact one_ne_zero he

/-- Both redundant covers have genuinely nonzero categorical kernels. -/
theorem kernels_nonzero :
    (∃ x : (kernel (quotient2 k)).obj birthGrade, x ≠ 0) ∧
      (∃ x : (kernel (quotient3 k)).obj birthGrade, x ≠ 0) := by
  constructor
  · let e := ((rankExact2 k).toIsPointwiseShortExact.kernelIso.app birthGrade).toLinearEquiv
    refine ⟨e (unitAtBirth k), ?_⟩
    exact fun h => unitAtBirth_ne_zero k (e.injective (h.trans (map_zero e).symm))
  · let f : hook k ⟶ cover3 k := diagonal k ≫ biprod.inl
    have hf : f ≫ quotient3 k = 0 := by
      dsimp [f, quotient3]
      rw [Category.assoc, biprod.inl_desc]
      exact (rankExact2 k).toIsPointwiseShortExact.comp_eq_zero
    let z := kernel.lift (quotient3 k) f hf
    refine ⟨(z.app birthGrade).hom (unitAtBirth k), ?_⟩
    intro hz
    have he := congrArg (fun t : hook k ⟶ cover3 k =>
      ((biprod.fst : cover k ⟶ hook k).app birthGrade).hom
        (((biprod.fst : cover3 k ⟶ cover k).app birthGrade).hom
          ((t.app birthGrade).hom (unitAtBirth k)))) (kernel.lift_ι (quotient3 k) f hf)
    have hfst : ((biprod.fst : cover3 k ⟶ cover k).app birthGrade).hom
        ((f.app birthGrade).hom (unitAtBirth k)) =
          ((diagonal k).app birthGrade).hom (unitAtBirth k) :=
      congrArg (fun t : hook k ⟶ cover k => (t.app birthGrade).hom (unitAtBirth k))
        (show f ≫ (biprod.fst : cover3 k ⟶ cover k) = diagonal k from by
          dsimp only [f]
          rw [Category.assoc, biprod.inl_fst, Category.comp_id])
    change _ = ((biprod.fst : cover k ⟶ hook k).app birthGrade).hom
      (((biprod.fst : cover3 k ⟶ cover k).app birthGrade).hom
        ((f.app birthGrade).hom (unitAtBirth k))) at he
    rw [hfst, fst_diagonal] at he
    change ((biprod.fst : cover k ⟶ hook k).app birthGrade).hom
      (((biprod.fst : cover3 k ⟶ cover k).app birthGrade).hom
        (((kernel.ι (quotient3 k)).app birthGrade).hom
          ((z.app birthGrade).hom (unitAtBirth k)))) = unitAtBirth k at he
    rw [hz, map_zero, map_zero, map_zero] at he
    exact unitAtBirth_ne_zero k he.symm

/-- The positive-width construction and its nonzero kernels work in characteristic two. -/
theorem characteristic_two :
    Nonempty (CoordinateInterleaving 1
      (cover (ZMod 2) ⊞ (shift 1).obj (kernel (quotient3 (ZMod 2))))
      ((shift 1).obj (hook (ZMod 2)) ⊞ cover3 (ZMod 2))) ∧
    (∃ x : (kernel (quotient2 (ZMod 2))).obj birthGrade, x ≠ 0) ∧
      (∃ x : (kernel (quotient3 (ZMod 2))).obj birthGrade, x ≠ 0) :=
  ⟨⟨positiveInterleaving (ZMod 2)⟩, kernels_nonzero (ZMod 2)⟩

/-- The construction also admits zero coordinate directions, where the grade poset is a singleton. -/
theorem no_coordinates :
    let a : Fin 0 → ℝ := fun _ => 0
    let M := HookInfinity.module (R := ℚ) a
    Nonempty (CoordinateInterleaving 1 (M ⊞ (shift 1).obj (kernel (𝟙 M)))
      ((shift 1).obj (kernel (𝟙 M)) ⊞ M)) ∧ HookInfinity.birth (R := ℚ) a ≠ 0 := by
  dsimp only
  let a : Fin 0 → ℝ := fun _ => 0
  let M := HookInfinity.module (R := ℚ) a
  exact ⟨⟨RankSchanuel.interleaving (𝟙 M) (𝟙 M) (CoordinateInterleaving.refl 1 M)
    (IsRankDeflation.id M) (IsRankDeflation.id M)
    (HookInfinity.isRankProjective a) (HookInfinity.isRankProjective a)⟩,
    HookInfinity.birth_ne_zero a⟩

/-- A public component law detects a nonzero forward map at strictly positive width. -/
theorem positive_pullback_forward_nonzero :
    let M := HookInfinity.module (R := k) birthGrade
    RankSchanuel.forward (𝟙 M) (𝟙 M) (CoordinateInterleaving.refl 1 M) ≠ 0 := by
  dsimp only
  let M := HookInfinity.module (R := k) birthGrade
  let i := CoordinateInterleaving.refl 1 M
  let x := HookInfinity.birth (R := k) birthGrade
  let y := (i.φ.app birthGrade).hom x
  have hy : y ≠ 0 := by
    have hab : birthGrade ≤ translation 1 birthGrade := by
      intro j; norm_num [translation, birthGrade]
    have he := HookInfinity.fiberEquivOfLe_structureMap (R := k)
      (le_refl birthGrade) hab x
    intro h
    change structureMapLinear M hab x = 0 at h
    rw [h, map_zero] at he
    have hx : x = 0 := (HookInfinity.fiberEquivOfLe (R := k)
      (le_refl birthGrade)).injective (he.symm.trans (map_zero _).symm)
    exact HookInfinity.birth_ne_zero birthGrade hx
  let z := PullbackFiber.mk ((shift 1).map (𝟙 M)) ((𝟙 M) ≫ i.φ) birthGrade y x rfl
  have hz := RankSchanuel.forward_snd_app (𝟙 M) (𝟙 M) i birthGrade z
  have hz' := PullbackFiber.fst_mk ((shift 1).map (𝟙 M)) ((𝟙 M) ≫ i.φ)
    birthGrade y x rfl
  have he := hz.trans hz'
  intro h
  change RankSchanuel.forward (𝟙 M) (𝟙 M) i = 0 at h
  have hz0 : ((RankSchanuel.forward (𝟙 M) (𝟙 M) i).app birthGrade).hom z = 0 := by
    rw [h]
    rfl
  rw [hz0] at he
  exact hy (he.symm.trans (map_zero _))

private instance zero_subsingleton (p : Fin 2 → ℝ) :
    Subsingleton ((0 : PModule ℚ (Fin 2 → ℝ)).obj p) :=
  ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)

private instance zero_finiteDimensional (p : Fin 2 → ℝ) :
    FiniteDimensional ℚ ((0 : PModule ℚ (Fin 2 → ℝ)).obj p) := by
  infer_instance

private theorem zero_projective : IsRankProjective (0 : PModule ℚ (Fin 2 → ℝ)) := by
  intro L M N ι π hs α
  exact ⟨0, (isZero_zero _).eq_of_src _ _⟩

/-- Zero modules also give an actual Schanuel interleaving at positive width. -/
theorem zero_module :
    let M : PModule ℚ (Fin 2 → ℝ) := 0
    Nonempty (CoordinateInterleaving 1 (M ⊞ (shift 1).obj (kernel (𝟙 M)))
      ((shift 1).obj (kernel (𝟙 M)) ⊞ M)) := by
  dsimp only
  exact ⟨RankSchanuel.interleaving (𝟙 _) (𝟙 _) (CoordinateInterleaving.refl 1 _)
    (IsRankDeflation.id _) (IsRankDeflation.id _) zero_projective zero_projective⟩

end TDA.Persistence.RankSchanuelExamples
