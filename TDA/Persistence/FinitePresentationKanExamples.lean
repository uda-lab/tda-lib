import TDA.Persistence.FinitePresentationGridKan
import TDA.Persistence.HookEndomorphisms

/-!
# Finite-grid reconstruction with genuine relations

Two generators share a birth grade. One nonzero relation kills the first
at coordinate grade two, while the second maps to a principal upset and survives.
The grid records grades without identifying generator occurrences. These
presentations test actual Kan comparisons and extension of natural maps.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FinitePresentationKanExamples

open CategoryTheory CategoryTheory.Limits GradedFree
open scoped TDA.Persistence ZeroObject

/-- Two distinct generator occurrences at the same coordinate grade. -/
abbrev generators (n : ℕ) : GradedGenerators (Fin n → ℝ) where
  Carrier := Fin 2
  grade _ _ := 0

/-- One relation at the coordinate grade two. -/
abbrev relations (n : ℕ) : GradedGenerators (Fin n → ℝ) where
  Carrier := Unit
  grade _ _ := 2

private theorem birth_le_death (n : ℕ) : (generators n).grade (0 : Fin 2) ≤ (relations n).grade () := by
  intro i
  norm_num [generators, relations]

variable (R : Type u) [Ring R] (n : ℕ)

/-- The first generator is killed by a genuine homogeneous relation. -/
noncomputable abbrev presentation : Presentation (R := R) (P := Fin n → ℝ) :=
  Presentation.ofRelations (generators n) (relations n)
    (fun _ => GradedFree.generator (generators n) (0 : Fin 2) (birth_le_death n))

/-- Both original occurrence families are finite. -/
theorem presentation_finite : (presentation R n).IsFinite :=
  ⟨inferInstanceAs (Finite (Fin 2)), inferInstanceAs (Finite Unit)⟩

/-- The primitive relation is nonzero over every nontrivial coefficient ring. -/
theorem relation_nonzero [Nontrivial R] : (presentation R n).relationMap ≠ 0 := by
  intro h
  have he := congrArg (fun f : module (R := R) (relations n) ⟶ module (generators n) =>
    ((f.app ((relations n).grade ())).hom (GradedFree.birth (relations n) ())).val (0 : Fin 2)) h
  have hb := Presentation.ofRelations_at_birth (R := R) (generators n) (relations n)
    (fun _ => GradedFree.generator (generators n) (0 : Fin 2) (birth_le_death n)) ()
  change (((presentation R n).relationMap.app ((relations n).grade ())).hom
    (GradedFree.birth (relations n) ())).val (0 : Fin 2) = 0 at he
  rw [hb] at he
  change (Finsupp.single (0 : Fin 2) (1 : R)) 0 = 0 at he
  rw [Finsupp.single_eq_same] at he
  exact one_ne_zero he

private noncomputable abbrev keepSecond :
    module (R := R) (generators n) ⟶ HookInfinity.module (R := R) ((generators n).grade (0 : Fin 2)) :=
  GradedFree.lift (generators n) _
    (fun g : Fin 2 => if g = 0 then 0 else HookInfinity.birth (R := R) ((generators n).grade (0 : Fin 2)))

private theorem keepSecond_relation : (presentation R n).relationMap ≫ keepSecond R n = 0 := by
  apply GradedFree.hom_ext_birth (relations n)
  intro y
  cases y
  change ((keepSecond R n).app ((relations n).grade ())).hom
    (((presentation R n).relationMap.app ((relations n).grade ())).hom
      (GradedFree.birth (relations n) ())) = 0
  have hr := Presentation.ofRelations_at_birth (R := R) (generators n) (relations n)
    (fun _ => GradedFree.generator (generators n) (0 : Fin 2) (birth_le_death n)) ()
  have h₁ := congrArg ((keepSecond R n).app ((relations n).grade ())).hom hr
  have hn := congrArg (fun f => f.hom (GradedFree.birth (R := R) (generators n) (0 : Fin 2)))
    ((keepSecond R n).naturality (homOfLE (birth_le_death n)))
  change ((keepSecond R n).app ((relations n).grade ())).hom
      (structureMapLinear (module (R := R) (generators n)) (birth_le_death n)
        (GradedFree.birth (generators n) (0 : Fin 2))) =
    structureMapLinear (HookInfinity.module ((generators n).grade (0 : Fin 2))) (birth_le_death n)
      (((keepSecond R n).app ((generators n).grade (0 : Fin 2))).hom (GradedFree.birth (generators n) (0 : Fin 2))) at hn
  have hb : ((keepSecond R n).app ((generators n).grade (0 : Fin 2))).hom
      (GradedFree.birth (generators n) (0 : Fin 2)) = 0 :=
    GradedFree.lift_birth (generators n) _
      (fun g : Fin 2 => if g = 0 then 0 else HookInfinity.birth (R := R) ((generators n).grade (0 : Fin 2))) 0
  have h₂ := hn.trans ((congrArg
    (structureMapLinear (HookInfinity.module (R := R) ((generators n).grade (0 : Fin 2)))
      (birth_le_death n)) hb).trans (map_zero _))
  have h₃ := congrArg ((keepSecond R n).app ((relations n).grade ())).hom
    (GradedFree.generator_eq_structureMap (R := R) (generators n) (0 : Fin 2) (birth_le_death n))
  exact h₁.trans (h₃.trans h₂)

private noncomputable def keepSecondDesc :
    (presentation R n).presented ⟶ HookInfinity.module (R := R) ((generators n).grade (0 : Fin 2)) :=
  (presentation R n).desc (keepSecond R n) (keepSecond_relation R n)

/-- The surviving vector in the presented quotient is the second generator image. -/
noncomputable def secondValue : (presentation R n).presented.obj ((generators n).grade (0 : Fin 2)) :=
  ((presentation R n).cover.app ((generators n).grade (0 : Fin 2))).hom
    (GradedFree.birth (generators n) (1 : Fin 2))

private theorem secondValue_image :
    ((keepSecondDesc R n).app ((generators n).grade (0 : Fin 2))).hom (secondValue R n) =
      HookInfinity.birth (R := R) ((generators n).grade (0 : Fin 2)) := by
  have he := congrArg (fun f : module (R := R) (generators n) ⟶
      HookInfinity.module ((generators n).grade (0 : Fin 2)) =>
    (f.app ((generators n).grade (0 : Fin 2))).hom (GradedFree.birth (generators n) (1 : Fin 2)))
      ((presentation R n).cover_desc (keepSecond R n) (keepSecond_relation R n))
  change ((keepSecondDesc R n).app ((generators n).grade (0 : Fin 2))).hom (secondValue R n) = _ at he
  have hb := GradedFree.lift_birth (R := R) (generators n)
    (HookInfinity.module (R := R) ((generators n).grade (0 : Fin 2)))
    (fun g : Fin 2 => if g = 0 then 0 else HookInfinity.birth (R := R) ((generators n).grade (0 : Fin 2)))
    (1 : Fin 2)
  exact he.trans (hb.trans (if_neg (by decide : (1 : Fin 2) ≠ 0)))

/-- A genuine nonzero quotient remains after imposing the nonzero relation. -/
theorem surviving_generator {k : Type u} [Field k] : secondValue k n ≠ 0 := by
  intro h
  have he := secondValue_image k n
  rw [h, map_zero] at he
  exact HookInfinity.birth_ne_zero ((generators n).grade (0 : Fin 2)) he.symm

/-- Equal grid birth points retain two different free generator vectors. -/
theorem repeated_births [Nontrivial R] :
    (presentation R n).generatorGridPoint (presentation_finite R n) (0 : Fin 2) =
      (presentation R n).generatorGridPoint (presentation_finite R n) (1 : Fin 2) ∧
    GradedFree.birth (R := R) (generators n) (0 : Fin 2) ≠ GradedFree.birth (R := R) (generators n) (1 : Fin 2) := by
  constructor
  · rfl
  · intro h
    have he := congrArg (fun x : (module (R := R) (generators n)).obj ((generators n).grade (0 : Fin 2)) =>
      x.val (0 : Fin 2)) h
    change (Finsupp.single (0 : Fin 2) (1 : R)) 0 = (Finsupp.single (1 : Fin 2) (1 : R)) 0 at he
    simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at he
    exact one_ne_zero he

/-- The same genuine-relation example reconstructs over the ring of integers. -/
theorem integer_reconstruction :
    (presentation ℤ 2).relationMap ≠ 0 ∧
    Nonempty (((presentation ℤ 2).gridCoordinates (presentation_finite ℤ 2)).embedding.monotone.functor.leftKanExtension
      ((presentation ℤ 2).gridModule (presentation_finite ℤ 2)) ≅ (presentation ℤ 2).presented) :=
  ⟨relation_nonzero ℤ 2, ⟨(presentation ℤ 2).gridKanIso (presentation_finite ℤ 2)⟩⟩

/-- The field specialization supplies an actual finite grid with pfd fibers. -/
theorem field_grid :
    ∃ (G : CoordinateGrid 2) (N : PModule ℚ G.Point),
      (∀ p, FiniteDimensional ℚ (N.obj p)) ∧
        Nonempty (G.embedding.monotone.functor.leftKanExtension N ≅ (presentation ℚ 2).presented) :=
  GradedFree.finitelyPresented_exists_pfd_finiteGridKan _
    ((presentation ℚ 2).finitelyPresented (presentation_finite ℚ 2))

/-- Extend a nonidentity natural map from the finite grid of the genuine quotient. -/
noncomputable def extendedDouble : (presentation ℚ 2).presented ⟶ (presentation ℚ 2).presented :=
  ((presentation ℚ 2).gridHomEquiv (presentation_finite ℚ 2) (presentation ℚ 2).presented).symm
    (((presentation ℚ 2).gridCoordinates (presentation_finite ℚ 2)).embedding.monotone.functor.whiskerLeft
      ((2 : ℚ) • 𝟙 (presentation ℚ 2).presented))

/-- The extended map agrees with the specified nonidentity map at every real grade. -/
theorem extendedDouble_eq : extendedDouble = (2 : ℚ) • 𝟙 (presentation ℚ 2).presented := by
  let D := presentation ℚ 2
  let hD := presentation_finite ℚ 2
  change (D.gridHomEquiv hD D.presented).symm
    ((D.gridCoordinates hD).embedding.monotone.functor.whiskerLeft ((2 : ℚ) • 𝟙 D.presented)) = _
  rw [← D.gridHomEquiv_apply hD D.presented ((2 : ℚ) • 𝟙 D.presented)]
  exact (D.gridHomEquiv hD D.presented).symm_apply_apply _

/-- The extension of the nonidentity grid map is actually nonzero. -/
theorem extendedDouble_nonzero : extendedDouble ≠ 0 := by
  intro h
  rw [extendedDouble_eq] at h
  have he := congrArg (fun f : (presentation ℚ 2).presented ⟶ (presentation ℚ 2).presented =>
    (f.app ((generators 2).grade (0 : Fin 2))).hom (secondValue ℚ 2)) h
  change (2 : ℚ) • secondValue ℚ 2 = 0 at he
  exact (smul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (surviving_generator 2)) he

/-- In characteristic two the same relation remains nonzero, while doubling extends to zero. -/
theorem characteristic_two :
    let D := presentation (ZMod 2) 2
    let hD := presentation_finite (ZMod 2) 2
    D.relationMap ≠ 0 ∧ secondValue (ZMod 2) 2 ≠ 0 ∧
      (D.gridHomEquiv hD D.presented).symm
        ((D.gridCoordinates hD).embedding.monotone.functor.whiskerLeft
          ((2 : ZMod 2) • 𝟙 D.presented)) = 0 := by
  dsimp only
  refine ⟨relation_nonzero (ZMod 2) 2, surviving_generator 2, ?_⟩
  let D := presentation (ZMod 2) 2
  let hD := presentation_finite (ZMod 2) 2
  change (D.gridHomEquiv hD D.presented).symm
    ((D.gridCoordinates hD).embedding.monotone.functor.whiskerLeft ((2 : ZMod 2) • 𝟙 D.presented)) = 0
  rw [← D.gridHomEquiv_apply hD D.presented ((2 : ZMod 2) • 𝟙 D.presented), Equiv.symm_apply_apply]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

/-- The zero-direction grid has one point and the presented module is still nonzero. -/
theorem no_coordinates :
    let D := presentation ℚ 0
    let hD := presentation_finite ℚ 0
    Fintype.card (D.gridCoordinates hD).Point = 1 ∧ secondValue ℚ 0 ≠ 0 ∧
      Nonempty ((D.gridCoordinates hD).embedding.monotone.functor.leftKanExtension
        (D.gridModule hD) ≅ D.presented) := by
  dsimp only
  refine ⟨?_, surviving_generator 0, ⟨(presentation ℚ 0).gridKanIso (presentation_finite ℚ 0)⟩⟩
  simp [CoordinateGrid.Point]

/-- There are no generators in this family. -/
abbrev noGenerators (n : ℕ) : GradedGenerators (Fin n → ℝ) where
  Carrier := Empty
  grade := Empty.elim

/-- An empty relation family reconstructs the actual repeated-generator free module. -/
theorem no_relations :
    let D := zeroRelationPresentation (R := R) (generators n) (noGenerators n)
    let hD : D.IsFinite := ⟨inferInstanceAs (Finite (Fin 2)), inferInstanceAs (Finite Empty)⟩
    Nonempty ((D.gridCoordinates hD).embedding.monotone.functor.leftKanExtension
      (D.gridModule hD) ≅ module (R := R) (generators n)) := by
  dsimp only
  let D := zeroRelationPresentation (R := R) (generators n) (noGenerators n)
  let hD : D.IsFinite := ⟨inferInstanceAs (Finite (Fin 2)), inferInstanceAs (Finite Empty)⟩
  exact ⟨D.gridKanIso hD ≪≫ zeroRelationPresentedIso (generators n) (noGenerators n)⟩

/-- Empty generator and relation families also reconstruct the actual zero module. -/
theorem zero_module :
    ∃ (G : CoordinateGrid n) (N : PModule.{u,0,u} R G.Point),
      Nonempty (G.embedding.monotone.functor.leftKanExtension N ≅ (0 : PModule R (Fin n → ℝ))) := by
  have hz : IsZero (module (R := R) (noGenerators n)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply GradedFree.hom_ext_birth (noGenerators n)
    intro g
    exact g.elim
  exact GradedFree.finitelyPresented_exists_finiteGridKan _
    (finitelyPresented_of_iso (free_finitelyPresented (noGenerators n)) hz.isoZero)

/-- Reconstruction also works over the zero ring, without a nontriviality hypothesis. -/
theorem zero_ring :
    let D := presentation (ZMod 1) 2
    let hD := presentation_finite (ZMod 1) 2
    Nonempty ((D.gridCoordinates hD).embedding.monotone.functor.leftKanExtension
      (D.gridModule hD) ≅ D.presented) :=
  ⟨(presentation (ZMod 1) 2).gridKanIso (presentation_finite (ZMod 1) 2)⟩

end TDA.Persistence.FinitePresentationKanExamples
