import TDA.Persistence.GradedFreeSum
import TDA.Persistence.FinitePresentation
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Adding redundant graded generators to a presentation

Each chosen element of a presented module can be given a new generator at its
grade. A new relation identifies that generator with a free lift of the chosen
element. The enlarged presentation has the same quotient, including when the
generator and relation families are finite.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

variable (D : Presentation.{u,v,w} (R := R) (P := P))
  (V : GradedGenerators.{v,w} P)
  (chosen : ∀ x : V.Carrier, D.presented.obj (V.grade x))

/-- The map assigning each added generator its selected quotient element. -/
noncomputable def Presentation.chosenMap :
    module (R := R) V ⟶ D.presented :=
  lift V D.presented chosen

/-- Free representatives of the selected quotient elements. -/
noncomputable def Presentation.chosenLift :
    module (R := R) V ⟶ module D.generators :=
  Classical.choose (D.exists_lift V (D.chosenMap V chosen))

@[simp] theorem Presentation.chosenLift_cover :
    D.chosenLift V chosen ≫ D.cover = D.chosenMap V chosen :=
  Classical.choose_spec (D.exists_lift V (D.chosenMap V chosen))

/-- Enlarge the generator family and adjoin one relation per new generator.
The new relation is its basis vector minus the chosen old free representative. -/
noncomputable def Presentation.adjoinRedundant : Presentation.{u,v,w} (R := R) (P := P) where
  generators := D.generators.sum V
  relations := D.relations.sum V
  relationMap := sumDesc D.relations V
    (D.relationMap ≫ sumInl D.generators V)
    (sumInr D.generators V - D.chosenLift V chosen ≫ sumInl D.generators V)

/-- Send original generators to their quotient classes and new generators to
their chosen quotient elements. -/
noncomputable def Presentation.adjoinCollapse :
    module (R := R) (D.generators.sum V) ⟶ D.presented :=
  sumDesc D.generators V D.cover (D.chosenMap V chosen)

@[simp] theorem Presentation.sumInl_adjoinRelation :
    sumInl D.relations V ≫ (D.adjoinRedundant V chosen).relationMap =
      D.relationMap ≫ sumInl D.generators V :=
  sumInl_sumDesc D.relations V _ _

@[simp] theorem Presentation.sumInr_adjoinRelation :
    sumInr D.relations V ≫ (D.adjoinRedundant V chosen).relationMap =
      sumInr D.generators V - D.chosenLift V chosen ≫ sumInl D.generators V :=
  sumInr_sumDesc D.relations V _ _

@[simp] theorem Presentation.sumInl_adjoinCollapse :
    sumInl D.generators V ≫ D.adjoinCollapse V chosen = D.cover :=
  sumInl_sumDesc D.generators V _ _

@[simp] theorem Presentation.sumInr_adjoinCollapse :
    sumInr D.generators V ≫ D.adjoinCollapse V chosen = D.chosenMap V chosen :=
  sumInr_sumDesc D.generators V _ _

/-- Both the old relations and the new identifying relations vanish after
mapping the enlarged free module to the original quotient. -/
theorem Presentation.adjoinRelation_collapse :
    (D.adjoinRedundant V chosen).relationMap ≫ D.adjoinCollapse V chosen = 0 := by
  apply sumHom_ext D.relations V
  · calc
      sumInl D.relations V ≫
          ((D.adjoinRedundant V chosen).relationMap ≫ D.adjoinCollapse V chosen) =
        (sumInl D.relations V ≫ (D.adjoinRedundant V chosen).relationMap) ≫
          D.adjoinCollapse V chosen := (Category.assoc _ _ _).symm
      _ = (D.relationMap ≫ sumInl D.generators V) ≫ D.adjoinCollapse V chosen :=
        congrArg (· ≫ D.adjoinCollapse V chosen) (D.sumInl_adjoinRelation V chosen)
      _ = D.relationMap ≫ (sumInl D.generators V ≫ D.adjoinCollapse V chosen) :=
        Category.assoc _ _ _
      _ = D.relationMap ≫ D.cover :=
        congrArg (D.relationMap ≫ ·) (D.sumInl_adjoinCollapse V chosen)
      _ = 0 := D.relations_vanish
      _ = sumInl D.relations V ≫ (0 : _ ⟶ D.presented) := by simp
  · calc
      sumInr D.relations V ≫
          ((D.adjoinRedundant V chosen).relationMap ≫ D.adjoinCollapse V chosen) =
        (sumInr D.relations V ≫ (D.adjoinRedundant V chosen).relationMap) ≫
          D.adjoinCollapse V chosen := (Category.assoc _ _ _).symm
      _ = (sumInr D.generators V -
          D.chosenLift V chosen ≫ sumInl D.generators V) ≫
            D.adjoinCollapse V chosen :=
        congrArg (· ≫ D.adjoinCollapse V chosen) (D.sumInr_adjoinRelation V chosen)
      _ = (sumInr D.generators V ≫ D.adjoinCollapse V chosen) -
          ((D.chosenLift V chosen ≫ sumInl D.generators V) ≫
            D.adjoinCollapse V chosen) := sub_comp _ _ _
      _ = D.chosenMap V chosen - (D.chosenLift V chosen ≫ D.cover) := by
        rw [D.sumInr_adjoinCollapse V chosen, Category.assoc,
          D.sumInl_adjoinCollapse V chosen]
      _ = 0 := by rw [D.chosenLift_cover V chosen]; simp
      _ = sumInr D.relations V ≫ (0 : _ ⟶ D.presented) := by simp

/-- The enlarged quotient maps to the original quotient by its specified
generator images. -/
noncomputable def Presentation.adjoinForget :
    (D.adjoinRedundant V chosen).presented ⟶ D.presented :=
  (D.adjoinRedundant V chosen).desc (D.adjoinCollapse V chosen)
    (D.adjoinRelation_collapse V chosen)

@[simp] theorem Presentation.adjoinCover_forget :
    (D.adjoinRedundant V chosen).cover ≫ D.adjoinForget V chosen =
      D.adjoinCollapse V chosen :=
  (D.adjoinRedundant V chosen).cover_desc _ _

/-- The old relations vanish in the enlarged quotient. -/
theorem Presentation.oldRelation_adjoinCover :
    D.relationMap ≫
      (sumInl D.generators V ≫ (D.adjoinRedundant V chosen).cover) = 0 := by
  have hrelzero : ((D.adjoinRedundant V chosen).relationMap ≫
      (D.adjoinRedundant V chosen).cover :
        module (R := R) (D.relations.sum V) ⟶
          (D.adjoinRedundant V chosen).presented) = 0 :=
    (D.adjoinRedundant V chosen).relations_vanish
  calc
    D.relationMap ≫
        (sumInl D.generators V ≫ (D.adjoinRedundant V chosen).cover) =
      (D.relationMap ≫ sumInl D.generators V) ≫
        (D.adjoinRedundant V chosen).cover := (Category.assoc _ _ _).symm
    _ = (sumInl D.relations V ≫ (D.adjoinRedundant V chosen).relationMap) ≫
        (D.adjoinRedundant V chosen).cover := by
          exact (congrArg (· ≫ (D.adjoinRedundant V chosen).cover)
            (D.sumInl_adjoinRelation V chosen)).symm
    _ = sumInl D.relations V ≫
        ((D.adjoinRedundant V chosen).relationMap ≫
          (D.adjoinRedundant V chosen).cover) := Category.assoc _ _ _
    _ = 0 := by
      exact (congrArg (sumInl D.relations V ≫ ·)
        hrelzero).trans (by simp)

/-- The original quotient maps into the enlarged quotient through its
original generators. -/
noncomputable def Presentation.adjoinInclude :
    D.presented ⟶ (D.adjoinRedundant V chosen).presented :=
  D.desc (sumInl D.generators V ≫ (D.adjoinRedundant V chosen).cover)
    (D.oldRelation_adjoinCover V chosen)

@[simp] theorem Presentation.cover_adjoinInclude :
    D.cover ≫ D.adjoinInclude V chosen =
      sumInl D.generators V ≫ (D.adjoinRedundant V chosen).cover :=
  D.cover_desc _ _

/-- The new generator and its chosen old representative have the same class
in the enlarged quotient. -/
theorem Presentation.sumInr_adjoinCover :
    sumInr D.generators V ≫ (D.adjoinRedundant V chosen).cover =
      D.chosenMap V chosen ≫ D.adjoinInclude V chosen := by
  have hrelzero : ((D.adjoinRedundant V chosen).relationMap ≫
      (D.adjoinRedundant V chosen).cover :
        module (R := R) (D.relations.sum V) ⟶
          (D.adjoinRedundant V chosen).presented) = 0 :=
    (D.adjoinRedundant V chosen).relations_vanish
  have hzero :
      (sumInr D.generators V - D.chosenLift V chosen ≫ sumInl D.generators V) ≫
        (D.adjoinRedundant V chosen).cover = 0 := by
    calc
      _ = (sumInr D.relations V ≫ (D.adjoinRedundant V chosen).relationMap) ≫
            (D.adjoinRedundant V chosen).cover := by
              rw [D.sumInr_adjoinRelation V chosen]
      _ = sumInr D.relations V ≫
            ((D.adjoinRedundant V chosen).relationMap ≫
              (D.adjoinRedundant V chosen).cover) := Category.assoc _ _ _
      _ = 0 := by
        exact (congrArg (sumInr D.relations V ≫ ·)
          hrelzero).trans (by simp)
  have hdiff : (sumInr D.generators V ≫ (D.adjoinRedundant V chosen).cover) -
      ((D.chosenLift V chosen ≫ sumInl D.generators V) ≫
        (D.adjoinRedundant V chosen).cover) = 0 :=
    (sub_comp _ _ _).symm.trans hzero
  have heq := sub_eq_zero.mp hdiff
  calc
    sumInr D.generators V ≫ (D.adjoinRedundant V chosen).cover =
        (D.chosenLift V chosen ≫ sumInl D.generators V) ≫
          (D.adjoinRedundant V chosen).cover := heq
    _ = D.chosenLift V chosen ≫
          (sumInl D.generators V ≫ (D.adjoinRedundant V chosen).cover) :=
            Category.assoc _ _ _
    _ = D.chosenLift V chosen ≫ (D.cover ≫ D.adjoinInclude V chosen) := by
      rw [D.cover_adjoinInclude V chosen]
    _ = (D.chosenLift V chosen ≫ D.cover) ≫ D.adjoinInclude V chosen :=
      (Category.assoc _ _ _).symm
    _ = D.chosenMap V chosen ≫ D.adjoinInclude V chosen := by
      rw [D.chosenLift_cover V chosen]

theorem Presentation.adjoinInclude_forget :
    D.adjoinInclude V chosen ≫ D.adjoinForget V chosen = 𝟙 D.presented := by
  have hc : Epi D.cover := by
    change Epi (cokernel.π D.relationMap)
    infer_instance
  apply (cancel_epi D.cover).mp
  calc
    D.cover ≫ (D.adjoinInclude V chosen ≫ D.adjoinForget V chosen) =
        (D.cover ≫ D.adjoinInclude V chosen) ≫ D.adjoinForget V chosen :=
      (Category.assoc _ _ _).symm
    _ = (sumInl D.generators V ≫ (D.adjoinRedundant V chosen).cover) ≫
          D.adjoinForget V chosen := by rw [D.cover_adjoinInclude V chosen]
    _ = sumInl D.generators V ≫
          ((D.adjoinRedundant V chosen).cover ≫ D.adjoinForget V chosen) :=
      Category.assoc _ _ _
    _ = sumInl D.generators V ≫ D.adjoinCollapse V chosen := by
      exact congrArg (sumInl D.generators V ≫ ·) (D.adjoinCover_forget V chosen)
    _ = D.cover := D.sumInl_adjoinCollapse V chosen
    _ = D.cover ≫ 𝟙 D.presented := by simp

theorem Presentation.adjoinForget_include :
    D.adjoinForget V chosen ≫ D.adjoinInclude V chosen =
      𝟙 (D.adjoinRedundant V chosen).presented := by
  let E := D.adjoinRedundant V chosen
  have hc : Epi E.cover := by
    change Epi (cokernel.π E.relationMap)
    infer_instance
  apply (cancel_epi E.cover).mp
  have hW : (sumInl D.generators V ≫ E.cover) ≫ D.adjoinForget V chosen =
      D.cover := by
    calc
      _ = sumInl D.generators V ≫ (E.cover ≫ D.adjoinForget V chosen) :=
        Category.assoc _ _ _
      _ = sumInl D.generators V ≫ D.adjoinCollapse V chosen :=
        congrArg (sumInl D.generators V ≫ ·) (D.adjoinCover_forget V chosen)
      _ = D.cover := D.sumInl_adjoinCollapse V chosen
  have hV : (sumInr D.generators V ≫ E.cover) ≫ D.adjoinForget V chosen =
      D.chosenMap V chosen := by
    calc
      _ = sumInr D.generators V ≫ (E.cover ≫ D.adjoinForget V chosen) :=
        Category.assoc _ _ _
      _ = sumInr D.generators V ≫ D.adjoinCollapse V chosen :=
        congrArg (sumInr D.generators V ≫ ·) (D.adjoinCover_forget V chosen)
      _ = D.chosenMap V chosen := D.sumInr_adjoinCollapse V chosen
  apply sumHom_ext D.generators V
  · calc
      sumInl D.generators V ≫ (E.cover ≫
          (D.adjoinForget V chosen ≫ D.adjoinInclude V chosen)) =
        ((sumInl D.generators V ≫ E.cover) ≫ D.adjoinForget V chosen) ≫
          D.adjoinInclude V chosen :=
        (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm
      _ = D.cover ≫ D.adjoinInclude V chosen :=
        congrArg (· ≫ D.adjoinInclude V chosen) hW
      _ = sumInl D.generators V ≫ E.cover := D.cover_adjoinInclude V chosen
      _ = sumInl D.generators V ≫ (E.cover ≫ 𝟙 E.presented) :=
        (congrArg (sumInl D.generators V ≫ ·) (Category.comp_id E.cover)).symm
  · calc
      sumInr D.generators V ≫ (E.cover ≫
          (D.adjoinForget V chosen ≫ D.adjoinInclude V chosen)) =
        ((sumInr D.generators V ≫ E.cover) ≫ D.adjoinForget V chosen) ≫
          D.adjoinInclude V chosen :=
        (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm
      _ = D.chosenMap V chosen ≫ D.adjoinInclude V chosen :=
        congrArg (· ≫ D.adjoinInclude V chosen) hV
      _ = sumInr D.generators V ≫ E.cover :=
        (D.sumInr_adjoinCover V chosen).symm
      _ = sumInr D.generators V ≫ (E.cover ≫ 𝟙 E.presented) :=
        (congrArg (sumInr D.generators V ≫ ·) (Category.comp_id E.cover)).symm

/-- Adding a generator with its identifying relation leaves the presented
module unchanged. -/
noncomputable def Presentation.adjoinRedundantIso :
    (D.adjoinRedundant V chosen).presented ≅ D.presented where
  hom := D.adjoinForget V chosen
  inv := D.adjoinInclude V chosen
  hom_inv_id := D.adjoinForget_include V chosen
  inv_hom_id := D.adjoinInclude_forget V chosen

/-- Finite generator and relation families remain finite after adjoining a
finite redundant family. -/
theorem Presentation.adjoinRedundant_finite (hD : D.IsFinite) [Finite V.Carrier] :
    (D.adjoinRedundant V chosen).IsFinite := by
  classical
  change Finite (D.generators.Carrier ⊕ V.Carrier) ∧
    Finite (D.relations.Carrier ⊕ V.Carrier)
  let : Finite D.generators.Carrier := hD.1
  let : Finite D.relations.Carrier := hD.2
  let : Fintype D.generators.Carrier := Fintype.ofFinite D.generators.Carrier
  let : Fintype D.relations.Carrier := Fintype.ofFinite D.relations.Carrier
  let : Fintype V.Carrier := Fintype.ofFinite V.Carrier
  exact ⟨inferInstance, inferInstance⟩

end TDA.Persistence.GradedFree
