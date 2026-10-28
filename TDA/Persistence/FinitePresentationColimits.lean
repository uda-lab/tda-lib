import TDA.Persistence.GradedFreeSum
import TDA.Persistence.FinitePresentationLifting
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Finite presentations of categorical colimits

Finite graded-free presentations are closed under categorical cokernels and
binary biproducts. The comparison maps below keep the original generator
occurrences, including repeated grades, and present cokernels by adjoining the
lifted image of each source generator to the target relations.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

private instance : HasBinaryBiproducts (PModule.{u,v,max u w} R P) :=
  HasBinaryBiproducts.of_hasBinaryProducts

private theorem Presentation.cover_epi (D : Presentation.{u,v,w} (R := R) (P := P)) :
    Epi D.cover := by
  change Epi (cokernel.π D.relationMap)
  infer_instance

private theorem finite_sum_type {A B : Type w} (hA : Finite A) (hB : Finite B) :
    Finite (A ⊕ B) := by
  letI : Finite A := hA
  letI : Finite B := hB
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  exact Finite.of_fintype (A ⊕ B)

/-- The presentation of a cokernel obtained by adjoining the lifted source
generators to the target's relation family. -/
noncomputable abbrev Presentation.cokernelPresentation
    (D E : Presentation.{u,v,w} (R := R) (P := P))
    (α : module (R := R) D.generators ⟶ module E.generators) :
    Presentation.{u,v,w} (R := R) (P := P) where
  generators := E.generators
  relations := E.relations.sum D.generators
  relationMap := sumDesc E.relations D.generators E.relationMap α

@[reassoc (attr := simp)]
theorem Presentation.sumInl_cokernelPresentation_relationMap
    (D E : Presentation.{u,v,w} (R := R) (P := P))
    (α : module (R := R) D.generators ⟶ module E.generators) :
    sumInl E.relations D.generators ≫
        (D.cokernelPresentation E α).relationMap = E.relationMap := by
  simp [Presentation.cokernelPresentation]

@[reassoc (attr := simp)]
theorem Presentation.sumInr_cokernelPresentation_relationMap
    (D E : Presentation.{u,v,w} (R := R) (P := P))
    (α : module (R := R) D.generators ⟶ module E.generators) :
    sumInr E.relations D.generators ≫
        (D.cokernelPresentation E α).relationMap = α := by
  simp [Presentation.cokernelPresentation]

/-- The target presentation's quotient map into the explicit cokernel
presentation. -/
noncomputable def Presentation.cokernelTargetMap
    (D E : Presentation.{u,v,w} (R := R) (P := P))
    (α : module (R := R) D.generators ⟶ module E.generators) :
    E.presented ⟶ (D.cokernelPresentation E α).presented := by
  let F := D.cokernelPresentation E α
  apply E.desc F.cover
  have hErel : E.relationMap ≫ F.cover = 0 := by
    calc
      E.relationMap ≫ F.cover =
          (sumInl E.relations D.generators ≫ F.relationMap) ≫ F.cover := by
            exact congrArg (fun g => g ≫ F.cover)
              (Presentation.sumInl_cokernelPresentation_relationMap D E α).symm
      _ = 0 := by
        rw [Category.assoc, F.relations_vanish]
        simp
  exact hErel

@[reassoc (attr := simp)]
theorem Presentation.cokernelTargetMap_cover
    (D E : Presentation.{u,v,w} (R := R) (P := P))
    (α : module (R := R) D.generators ⟶ module E.generators) :
    E.cover ≫ D.cokernelTargetMap E α = (D.cokernelPresentation E α).cover := by
  simp [Presentation.cokernelTargetMap]

/-- The presentation comparison identifies the constructed quotient with the
actual categorical cokernel. The lift equation is the only compatibility
needed from the chosen map on generators. -/
noncomputable def Presentation.cokernelComparison
    (D E : Presentation.{u,v,w} (R := R) (P := P))
    (f : D.presented ⟶ E.presented)
    (α : module (R := R) D.generators ⟶ module E.generators)
    (hα : α ≫ E.cover = D.cover ≫ f) :
    Limits.cokernel f ≅ (D.cokernelPresentation E α).presented := by
  let F := D.cokernelPresentation E α
  let qE : E.presented ⟶ F.presented := D.cokernelTargetMap E α
  have hkill : f ≫ qE = 0 := by
    letI := Presentation.cover_epi D
    apply (cancel_epi D.cover).1
    calc
      (D.cover ≫ f) ≫ qE = (α ≫ E.cover) ≫ qE := by
        exact congrArg (fun g => g ≫ qE) hα.symm
      _ = α ≫ F.cover := by
        calc
          (α ≫ E.cover) ≫ qE = α ≫ (E.cover ≫ qE) := by
            simp only [Category.assoc]
          _ = α ≫ F.cover := by
            exact congrArg (fun g => α ≫ g)
              (Presentation.cokernelTargetMap_cover D E α)
      _ = 0 := by
        calc
          α ≫ F.cover =
              (sumInr E.relations D.generators ≫ F.relationMap) ≫ F.cover := by
                exact congrArg (fun g => g ≫ F.cover)
                  (Presentation.sumInr_cokernelPresentation_relationMap D E α).symm
          _ = 0 := by
            rw [Category.assoc, F.relations_vanish]
            simp
  have hrel : F.relationMap ≫ E.cover ≫ Limits.cokernel.π f = 0 := by
    change (sumDesc E.relations D.generators E.relationMap α) ≫
      E.cover ≫ Limits.cokernel.π f = 0
    apply sumHom_ext E.relations D.generators
    · change sumInl E.relations D.generators ≫
        sumDesc E.relations D.generators E.relationMap α ≫
          E.cover ≫ Limits.cokernel.π f = 0
      calc
        sumInl E.relations D.generators ≫
            sumDesc E.relations D.generators E.relationMap α ≫ E.cover ≫
              Limits.cokernel.π f =
            E.relationMap ≫ E.cover ≫ Limits.cokernel.π f := by
              exact congrArg (fun g => g ≫ E.cover ≫ Limits.cokernel.π f)
                (sumInl_sumDesc E.relations D.generators E.relationMap α)
        _ = 0 := by rw [← Category.assoc, E.relations_vanish]; simp
    · change sumInr E.relations D.generators ≫
        sumDesc E.relations D.generators E.relationMap α ≫
          E.cover ≫ Limits.cokernel.π f = 0
      calc
        sumInr E.relations D.generators ≫
            sumDesc E.relations D.generators E.relationMap α ≫ E.cover ≫
              Limits.cokernel.π f =
            (α ≫ E.cover) ≫ Limits.cokernel.π f := by
              exact congrArg (fun g => g ≫ E.cover ≫ Limits.cokernel.π f)
                (sumInr_sumDesc E.relations D.generators E.relationMap α)
        _ = 0 := by rw [hα]; simp [Category.assoc]
  let r : F.presented ⟶ Limits.cokernel f :=
    F.desc (E.cover ≫ Limits.cokernel.π f) hrel
  letI : Epi F.cover := Presentation.cover_epi F
  have hrCover : F.cover ≫ r = E.cover ≫ Limits.cokernel.π f := by
    dsimp [r]
    exact F.cover_desc _ _
  refine
    { hom := Limits.cokernel.desc f qE hkill
      inv := r
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (cancel_epi (Limits.cokernel.π f)).1
    calc
      Limits.cokernel.π f ≫ (Limits.cokernel.desc f qE hkill ≫ r) =
          qE ≫ r := by simp
      _ = Limits.cokernel.π f := by
        letI := Presentation.cover_epi E
        apply (cancel_epi E.cover).1
        calc
          E.cover ≫ (qE ≫ r) = F.cover ≫ r := by
            rw [← Category.assoc]
            exact congrArg (fun g => g ≫ r)
              (Presentation.cokernelTargetMap_cover D E α)
          _ = E.cover ≫ Limits.cokernel.π f := hrCover
  · apply (cancel_epi F.cover).1
    calc
      F.cover ≫ (r ≫ Limits.cokernel.desc f qE hkill) =
          (E.cover ≫ Limits.cokernel.π f) ≫ Limits.cokernel.desc f qE hkill := by
            simpa only [Category.assoc] using congrArg
              (fun g => g ≫ Limits.cokernel.desc f qE hkill) hrCover
      _ = F.cover := by
        rw [Category.assoc, Limits.cokernel.π_desc]
        exact Presentation.cokernelTargetMap_cover D E α

@[reassoc (attr := simp)]
theorem Presentation.cokernelComparison_π
    (D E : Presentation.{u,v,w} (R := R) (P := P))
    (f : D.presented ⟶ E.presented)
    (α : module (R := R) D.generators ⟶ module E.generators)
    (hα : α ≫ E.cover = D.cover ≫ f) :
    Limits.cokernel.π f ≫ (D.cokernelComparison E f α hα).hom =
      D.cokernelTargetMap E α := by
  simp [Presentation.cokernelComparison]

@[reassoc (attr := simp)]
theorem Presentation.cokernelComparison_cover
    (D E : Presentation.{u,v,w} (R := R) (P := P))
    (f : D.presented ⟶ E.presented)
    (α : module (R := R) D.generators ⟶ module E.generators)
    (hα : α ≫ E.cover = D.cover ≫ f) :
    (D.cokernelPresentation E α).cover ≫
        (D.cokernelComparison E f α hα).inv = E.cover ≫ Limits.cokernel.π f := by
  simp [Presentation.cokernelComparison]

/-- A finite presentation of a binary biproduct, formed from disjoint unions
of both generator and relation occurrences. -/
noncomputable abbrev Presentation.biprodPresentation
    (D E : Presentation.{u,v,w} (R := R) (P := P)) :
    Presentation.{u,v,w} (R := R) (P := P) where
  generators := D.generators.sum E.generators
  relations := D.relations.sum E.relations
  relationMap := sumDesc D.relations E.relations
    (D.relationMap ≫ sumInl D.generators E.generators)
    (E.relationMap ≫ sumInr D.generators E.generators)

@[reassoc (attr := simp)]
theorem Presentation.sumInl_biprodPresentation_relationMap
    (D E : Presentation.{u,v,w} (R := R) (P := P)) :
    sumInl D.relations E.relations ≫ (D.biprodPresentation E).relationMap =
      D.relationMap ≫ sumInl D.generators E.generators := by
  simp [Presentation.biprodPresentation]

@[reassoc (attr := simp)]
theorem Presentation.sumInr_biprodPresentation_relationMap
    (D E : Presentation.{u,v,w} (R := R) (P := P)) :
    sumInr D.relations E.relations ≫ (D.biprodPresentation E).relationMap =
      E.relationMap ≫ sumInr D.generators E.generators := by
  simp [Presentation.biprodPresentation]

/-- The presentation comparison identifies the disjoint-union presentation
with the actual categorical biproduct. -/
noncomputable def Presentation.biprodComparison
    (D E : Presentation.{u,v,w} (R := R) (P := P)) :
    D.presented ⊞ E.presented ≅ (D.biprodPresentation E).presented := by
  let F := D.biprodPresentation E
  letI := Presentation.cover_epi D
  letI := Presentation.cover_epi E
  letI := Presentation.cover_epi F
  let qD : D.presented ⟶ F.presented := D.desc
    (sumInl D.generators E.generators ≫ F.cover) (by
      change D.relationMap ≫ sumInl D.generators E.generators ≫
        (D.biprodPresentation E).cover = 0
      calc
        D.relationMap ≫ sumInl D.generators E.generators ≫
            (D.biprodPresentation E).cover =
            (sumInl D.relations E.relations ≫
              (D.biprodPresentation E).relationMap) ≫
                (D.biprodPresentation E).cover := by
                  rw [Presentation.sumInl_biprodPresentation_relationMap]
                  simp only [Category.assoc]
        _ = 0 := by
          rw [Category.assoc, (D.biprodPresentation E).relations_vanish]
          simp)
  let qE : E.presented ⟶ F.presented := E.desc
    (sumInr D.generators E.generators ≫ F.cover) (by
      change E.relationMap ≫ sumInr D.generators E.generators ≫
        (D.biprodPresentation E).cover = 0
      calc
        E.relationMap ≫ sumInr D.generators E.generators ≫
            (D.biprodPresentation E).cover =
            (sumInr D.relations E.relations ≫
              (D.biprodPresentation E).relationMap) ≫
                (D.biprodPresentation E).cover := by
                  rw [Presentation.sumInr_biprodPresentation_relationMap]
                  simp only [Category.assoc]
        _ = 0 := by
          rw [Category.assoc, (D.biprodPresentation E).relations_vanish]
          simp)
  let toF : D.presented ⊞ E.presented ⟶ F.presented := biprod.desc qD qE
  let genToBiprod : module (R := R) F.generators ⟶ D.presented ⊞ E.presented :=
    sumDesc D.generators E.generators (D.cover ≫ biprod.inl) (E.cover ≫ biprod.inr)
  have hGenInl : sumInl D.generators E.generators ≫ genToBiprod =
      D.cover ≫ biprod.inl := by
    dsimp [genToBiprod]
    exact sumInl_sumDesc D.generators E.generators (D.cover ≫ biprod.inl)
      (E.cover ≫ biprod.inr)
  have hGenInr : sumInr D.generators E.generators ≫ genToBiprod =
      E.cover ≫ biprod.inr := by
    dsimp [genToBiprod]
    exact sumInr_sumDesc D.generators E.generators (D.cover ≫ biprod.inl)
      (E.cover ≫ biprod.inr)
  have hrel : F.relationMap ≫ genToBiprod = 0 := by
    change (sumDesc D.relations E.relations
        (D.relationMap ≫ sumInl D.generators E.generators)
        (E.relationMap ≫ sumInr D.generators E.generators)) ≫ genToBiprod = 0
    apply sumHom_ext D.relations E.relations
    · calc
        sumInl D.relations E.relations ≫
            sumDesc D.relations E.relations
              (D.relationMap ≫ sumInl D.generators E.generators)
              (E.relationMap ≫ sumInr D.generators E.generators) ≫ genToBiprod =
            D.relationMap ≫ sumInl D.generators E.generators ≫ genToBiprod := by
              simp
        _ = D.relationMap ≫ D.cover ≫ biprod.inl := by
          exact congrArg (fun g => D.relationMap ≫ g) hGenInl
        _ = 0 := by
          simpa only [Category.assoc, zero_comp] using
            congrArg (fun g => g ≫ biprod.inl) D.relations_vanish
    · calc
        sumInr D.relations E.relations ≫
            sumDesc D.relations E.relations
              (D.relationMap ≫ sumInl D.generators E.generators)
              (E.relationMap ≫ sumInr D.generators E.generators) ≫ genToBiprod =
            E.relationMap ≫ sumInr D.generators E.generators ≫ genToBiprod := by
              simp
        _ = E.relationMap ≫ E.cover ≫ biprod.inr := by
          exact congrArg (fun g => E.relationMap ≫ g) hGenInr
        _ = 0 := by
          simpa only [Category.assoc, zero_comp] using
            congrArg (fun g => g ≫ biprod.inr) E.relations_vanish
  let fromF : F.presented ⟶ D.presented ⊞ E.presented := F.desc genToBiprod hrel
  have hqD : D.cover ≫ qD = sumInl D.generators E.generators ≫ F.cover := by
    dsimp [qD]
    exact D.cover_desc _ _
  have hqE : E.cover ≫ qE = sumInr D.generators E.generators ≫ F.cover := by
    dsimp [qE]
    exact E.cover_desc _ _
  have hFcover : F.cover ≫ fromF = genToBiprod := by
    dsimp [fromF]
    exact F.cover_desc _ _
  refine
    { hom := toF
      inv := fromF
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply biprod.hom_ext'
    · apply (cancel_epi D.cover).1
      calc
        D.cover ≫ biprod.inl ≫ toF ≫ fromF =
            D.cover ≫ qD ≫ fromF := by simp [toF]
        _ = sumInl D.generators E.generators ≫ F.cover ≫ fromF := by
          simpa only [Category.assoc] using congrArg (fun g => g ≫ fromF) hqD
        _ = sumInl D.generators E.generators ≫ genToBiprod := by
          exact congrArg (fun g => sumInl D.generators E.generators ≫ g) hFcover
        _ = D.cover ≫ biprod.inl := by
          simp [genToBiprod]
    · apply (cancel_epi E.cover).1
      calc
        E.cover ≫ biprod.inr ≫ toF ≫ fromF =
            E.cover ≫ qE ≫ fromF := by simp [toF]
        _ = sumInr D.generators E.generators ≫ F.cover ≫ fromF := by
          simpa only [Category.assoc] using congrArg (fun g => g ≫ fromF) hqE
        _ = sumInr D.generators E.generators ≫ genToBiprod := by
          exact congrArg (fun g => sumInr D.generators E.generators ≫ g) hFcover
        _ = E.cover ≫ biprod.inr := by
          simp [genToBiprod]
  · apply (cancel_epi F.cover).1
    apply sumHom_ext D.generators E.generators
    · change sumInl D.generators E.generators ≫ F.cover ≫ fromF ≫ toF =
        sumInl D.generators E.generators ≫ F.cover
      calc
        _ = sumInl D.generators E.generators ≫ genToBiprod ≫ toF := by
          exact congrArg (fun g => sumInl D.generators E.generators ≫ g ≫ toF) hFcover
        _ = D.cover ≫ biprod.inl ≫ toF := by
          simpa only [Category.assoc] using congrArg (fun g => g ≫ toF) hGenInl
        _ = D.cover ≫ qD := by simp [toF, Category.assoc]
        _ = sumInl D.generators E.generators ≫ F.cover := hqD
    · change sumInr D.generators E.generators ≫ F.cover ≫ fromF ≫ toF =
        sumInr D.generators E.generators ≫ F.cover
      calc
        _ = sumInr D.generators E.generators ≫ genToBiprod ≫ toF := by
          exact congrArg (fun g => sumInr D.generators E.generators ≫ g ≫ toF) hFcover
        _ = E.cover ≫ biprod.inr ≫ toF := by
          simpa only [Category.assoc] using congrArg (fun g => g ≫ toF) hGenInr
        _ = E.cover ≫ qE := by simp [toF, Category.assoc]
        _ = sumInr D.generators E.generators ≫ F.cover := hqE

@[reassoc (attr := simp)]
theorem Presentation.biprodComparison_inl_cover
    (D E : Presentation.{u,v,w} (R := R) (P := P)) :
    D.cover ≫ biprod.inl ≫ (D.biprodComparison E).hom =
      sumInl D.generators E.generators ≫ (D.biprodPresentation E).cover := by
  simp [Presentation.biprodComparison]

@[reassoc (attr := simp)]
theorem Presentation.biprodComparison_inr_cover
    (D E : Presentation.{u,v,w} (R := R) (P := P)) :
    E.cover ≫ biprod.inr ≫ (D.biprodComparison E).hom =
      sumInr D.generators E.generators ≫ (D.biprodPresentation E).cover := by
  simp [Presentation.biprodComparison]

@[reassoc (attr := simp)]
theorem Presentation.biprodComparison_cover
    (D E : Presentation.{u,v,w} (R := R) (P := P)) :
    (D.biprodPresentation E).cover ≫ (D.biprodComparison E).inv =
      sumDesc D.generators E.generators (D.cover ≫ biprod.inl)
        (E.cover ≫ biprod.inr) := by
  simp [Presentation.biprodComparison]

/-- Finite presentation is closed under the actual categorical cokernel of a
map between finitely presented modules. -/
theorem finitelyPresented_cokernel
    {M N : PModule.{u,v,max u w} R P} (f : M ⟶ N)
    (hM : FinitelyPresented.{u,v,w} (R := R) (P := P) M)
    (hN : FinitelyPresented.{u,v,w} (R := R) (P := P) N) :
    FinitelyPresented.{u,v,w} (R := R) (P := P) (Limits.cokernel f) := by
  obtain ⟨D, hD, ⟨d⟩⟩ := hM
  obtain ⟨E, hE, ⟨e⟩⟩ := hN
  letI : Finite D.generators.Carrier := hD.1
  letI : Finite D.relations.Carrier := hD.2
  letI : Finite E.generators.Carrier := hE.1
  letI : Finite E.relations.Carrier := hE.2
  let f' := d.hom ≫ f ≫ e.inv
  obtain ⟨α, hα⟩ := E.exists_lift D.generators (D.cover ≫ f')
  let F := D.cokernelPresentation E α
  have hF : F.IsFinite := by
    change Finite E.generators.Carrier ∧
      Finite (E.relations.sum D.generators).Carrier
    exact ⟨hE.1, finite_sum_type hE.2 hD.1⟩
  let cokerIso := D.cokernelComparison E f' α hα
  have hFP' : FinitelyPresented.{u,v,w} (R := R) (P := P) (Limits.cokernel f') :=
    finitelyPresented_of_iso (F.finitelyPresented hF) cokerIso.symm
  let inputIso : Limits.cokernel f' ≅ Limits.cokernel f :=
    cokernel.mapIso (f := f') f d e (by simp [f', Category.assoc])
  exact finitelyPresented_of_iso hFP' inputIso

/-- Finite presentation is closed under the actual binary biproduct of two
finitely presented modules. -/
theorem finitelyPresented_biprod
    {M N : PModule.{u,v,max u w} R P}
    (hM : FinitelyPresented.{u,v,w} (R := R) (P := P) M)
    (hN : FinitelyPresented.{u,v,w} (R := R) (P := P) N) :
    FinitelyPresented.{u,v,w} (R := R) (P := P) (M ⊞ N) := by
  obtain ⟨D, hD, ⟨d⟩⟩ := hM
  obtain ⟨E, hE, ⟨e⟩⟩ := hN
  letI : Finite D.generators.Carrier := hD.1
  letI : Finite D.relations.Carrier := hD.2
  letI : Finite E.generators.Carrier := hE.1
  letI : Finite E.relations.Carrier := hE.2
  let F := D.biprodPresentation E
  have hF : F.IsFinite := by
    change Finite (D.generators.sum E.generators).Carrier ∧
      Finite (D.relations.sum E.relations).Carrier
    exact ⟨finite_sum_type hD.1 hE.1, finite_sum_type hD.2 hE.2⟩
  let isoDE := D.biprodComparison E
  let isoInput : D.presented ⊞ E.presented ≅ M ⊞ N :=
    (biprod.mapIso d e)
  have hFP : FinitelyPresented.{u,v,w} (R := R) (P := P)
      (D.presented ⊞ E.presented) :=
    finitelyPresented_of_iso (F.finitelyPresented hF) isoDE.symm
  exact finitelyPresented_of_iso hFP isoInput

end TDA.Persistence.GradedFree
