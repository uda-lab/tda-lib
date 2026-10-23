import TDA.Persistence.FinitePresentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Structure maps away from presentation grades

For a presented module, a structure map is invertible whenever the generator
and relation free modules have the same available basis vectors at both ends.
This is the algebraic form of the no-critical-grade step in Lesnick's closure
argument (Lemma 6.4). The argument applies to any preorder and ring.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- If no generator or relation becomes available between `a` and `b`, the
presented module's transition is an isomorphism. -/
theorem Presentation.structureMap_isIso_of_birth_iff
    (D : Presentation.{u,v,w} (R := R) (P := P)) {a b : P} (hab : a ≤ b)
    (hG : ∀ g : D.generators.Carrier,
      D.generators.grade g ≤ a ↔ D.generators.grade g ≤ b)
    (hY : ∀ y : D.relations.Carrier,
      D.relations.grade y ≤ a ↔ D.relations.grade y ≤ b) :
    IsIso (structureMap D.presented hab) := by
  let evA := (evaluation P (ModuleCat.{max u w} R)).obj a
  let evB := (evaluation P (ModuleCat.{max u w} R)).obj b
  let eA := PreservesCokernel.iso evA D.relationMap
  let eB := PreservesCokernel.iso evB D.relationMap
  let gIso := structureIsoOfBirthIff (R := R) D.generators hab hG
  let yIso := structureIsoOfBirthIff (R := R) D.relations hab hY
  have hs : D.relationMap.app a ≫ gIso.hom =
      yIso.hom ≫ D.relationMap.app b :=
    (D.relationMap.naturality (homOfLE hab)).symm
  let cIso := cokernel.mapIso (f := D.relationMap.app a)
    (D.relationMap.app b) yIso gIso hs
  have hkey : structureMap D.presented hab ≫ eB.hom = eA.hom ≫ cIso.hom := by
    have hcover : Epi (D.cover.app a) :=
      (ModuleCat.epi_iff_surjective _).mpr (D.cover_surjective a)
    apply (cancel_epi (D.cover.app a)).mp
    have ha : D.cover.app a ≫ eA.hom = cokernel.π (D.relationMap.app a) := by
      exact PreservesCokernel.π_iso_hom evA D.relationMap
    have hb : D.cover.app b ≫ eB.hom = cokernel.π (D.relationMap.app b) := by
      exact PreservesCokernel.π_iso_hom evB D.relationMap
    have hn : D.cover.app a ≫ structureMap D.presented hab =
        gIso.hom ≫ D.cover.app b :=
      (D.cover.naturality (homOfLE hab)).symm
    calc
      D.cover.app a ≫ (structureMap D.presented hab ≫ eB.hom) =
          (D.cover.app a ≫ structureMap D.presented hab) ≫ eB.hom := by
            exact (Category.assoc _ _ _).symm
      _ = (gIso.hom ≫ D.cover.app b) ≫ eB.hom := by rw [hn]
      _ = gIso.hom ≫ cokernel.π (D.relationMap.app b) := by
        exact (Category.assoc _ _ _).trans (congrArg (gIso.hom ≫ ·) hb)
      _ = cokernel.π (D.relationMap.app a) ≫ cIso.hom := by
        simp [cIso, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
      _ = D.cover.app a ≫ (eA.hom ≫ cIso.hom) := by
        exact (congrArg (· ≫ cIso.hom) ha.symm).trans (Category.assoc _ _ _)
  have hcomp : IsIso (eA.hom ≫ cIso.hom) :=
    IsIso.comp_isIso' eA.isIso_hom cIso.isIso_hom
  have htotal : IsIso (structureMap D.presented hab ≫ eB.hom) := by
    rw [hkey]
    exact hcomp
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (structureMap D.presented hab) eB.hom eB.isIso_hom htotal

variable {n : ℕ}

/-- Coordinate values of the generator and relation grades. -/
def Presentation.criticalCoordinates
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ)) (i : Fin n) : Set ℝ :=
  Set.range (fun g : D.generators.Carrier => D.generators.grade g i) ∪
    Set.range (fun y : D.relations.Carrier => D.relations.grade y i)

theorem Presentation.criticalCoordinates_finite
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ)) (hD : D.IsFinite)
    (i : Fin n) : (D.criticalCoordinates i).Finite := by
  let : Finite D.generators.Carrier := hD.1
  let : Finite D.relations.Carrier := hD.2
  exact (Set.finite_range _).union (Set.finite_range _)

theorem Presentation.generators_birth_iff_of_no_critical
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ))
    {a b : Fin n → ℝ} (hab : a ≤ b)
    (hgap : ∀ i, Disjoint (Set.Ioc (a i) (b i)) (D.criticalCoordinates i))
    (g : D.generators.Carrier) :
    D.generators.grade g ≤ a ↔ D.generators.grade g ≤ b := by
  constructor
  · exact fun h => h.trans hab
  · intro hb i
    by_contra h
    exact Set.disjoint_left.mp (hgap i) ⟨lt_of_not_ge h, hb i⟩ (Or.inl ⟨g, rfl⟩)

theorem Presentation.relations_birth_iff_of_no_critical
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ))
    {a b : Fin n → ℝ} (hab : a ≤ b)
    (hgap : ∀ i, Disjoint (Set.Ioc (a i) (b i)) (D.criticalCoordinates i))
    (y : D.relations.Carrier) :
    D.relations.grade y ≤ a ↔ D.relations.grade y ≤ b := by
  constructor
  · exact fun h => h.trans hab
  · intro hb i
    by_contra h
    exact Set.disjoint_left.mp (hgap i) ⟨lt_of_not_ge h, hb i⟩ (Or.inr ⟨y, rfl⟩)

/-- A finite presentation has invertible transition maps across rectangles
whose open-right coordinate gaps contain no presentation grade. -/
theorem Presentation.structureMap_isIso_of_no_critical
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ))
    {a b : Fin n → ℝ} (hab : a ≤ b)
    (hgap : ∀ i, Disjoint (Set.Ioc (a i) (b i)) (D.criticalCoordinates i)) :
    IsIso (structureMap D.presented hab) :=
  D.structureMap_isIso_of_birth_iff hab
    (D.generators_birth_iff_of_no_critical hab hgap)
    (D.relations_birth_iff_of_no_critical hab hgap)


/-- A finite presentation has a positive right-hand slack at every parameter:
all smaller diagonal moves induce isomorphisms. -/
theorem Presentation.exists_pos_structureMap_isIso
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ))
    (hD : D.IsFinite) (a : Fin n → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ : ℝ) (hδ : 0 ≤ δ), δ ≤ ε →
      IsIso (structureMap D.presented
        (show a ≤ (fun i => a i + δ) from fun _ => le_add_of_nonneg_right hδ)) := by
  classical
  let : Finite D.generators.Carrier := hD.1
  let : Finite D.relations.Carrier := hD.2
  let : Fintype D.generators.Carrier := Fintype.ofFinite D.generators.Carrier
  let : Fintype D.relations.Carrier := Fintype.ofFinite D.relations.Carrier
  let gG : Finset ℝ :=
    (Finset.univ : Finset (D.generators.Carrier × Fin n)).image
      (fun p => D.generators.grade p.1 p.2 - a p.2)
  let gY : Finset ℝ :=
    (Finset.univ : Finset (D.relations.Carrier × Fin n)).image
      (fun p => D.relations.grade p.1 p.2 - a p.2)
  let gaps : Finset ℝ := insert 1 ((gG ∪ gY).filter (fun t => 0 < t))
  have hnonempty : gaps.Nonempty := ⟨1, Finset.mem_insert_self ..⟩
  have hpositive : ∀ t ∈ gaps, 0 < t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · norm_num
    · exact (Finset.mem_filter.mp ht).2
  have hmin : 0 < gaps.min' hnonempty :=
    hpositive _ (Finset.min'_mem gaps hnonempty)
  let ε : ℝ := gaps.min' hnonempty / 2
  have hε : 0 < ε := half_pos hmin
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε
  have hgap : ∀ i, Disjoint (Set.Ioc (a i) (a i + δ))
      (D.criticalCoordinates i) := by
    intro i
    apply Set.disjoint_left.mpr
    intro c hc hcrit
    have hdiffpos : 0 < c - a i := sub_pos.mpr hc.1
    have hmem : c - a i ∈ gaps := by
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨?_, hdiffpos⟩
      rcases hcrit with ⟨g, rfl⟩ | ⟨y, rfl⟩
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨(g, i), Finset.mem_univ _, rfl⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(y, i), Finset.mem_univ _, rfl⟩)
    have hsmall : ε < c - a i :=
      lt_of_lt_of_le (half_lt_self hmin) (Finset.min'_le gaps _ hmem)
    have hupper : c - a i ≤ δ :=
      sub_le_iff_le_add.mpr (by simpa [add_comm] using hc.2)
    exact (not_lt_of_ge (hupper.trans hδε)) hsmall
  exact D.structureMap_isIso_of_no_critical
    (fun _ => le_add_of_nonneg_right hδ) hgap


private theorem structureMap_isIso_of_iso
    {M N : PModule.{u,v,max u w} R P} (e : M ≅ N)
    {a b : P} (hab : a ≤ b)
    (h : IsIso (structureMap M hab)) : IsIso (structureMap N hab) := by
  have hright : IsIso (structureMap M hab ≫ e.hom.app b) :=
    IsIso.comp_isIso' h (inferInstance : IsIso (e.hom.app b))
  have hnat : e.hom.app a ≫ structureMap N hab =
      structureMap M hab ≫ e.hom.app b :=
    (e.hom.naturality (homOfLE hab)).symm
  have hleft : IsIso (e.hom.app a ≫ structureMap N hab) := by
    rw [hnat]
    exact hright
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    (e.hom.app a) (structureMap N hab)
    (inferInstance : IsIso (e.hom.app a)) hleft

/-- A finitely presented multiparameter module has finite critical coordinates;
any comparable points whose coordinate gaps avoid them have an invertible
transition. -/
theorem finitelyPresented_exists_finite_criticalCoordinates
    (M : PModule.{u,0,max u w} R (Fin n → ℝ))
    (hM : FinitelyPresented (R := R) (P := Fin n → ℝ) M) :
    ∃ S : Fin n → Set ℝ, (∀ i, (S i).Finite) ∧
      ∀ {a b : Fin n → ℝ} (hab : a ≤ b),
        (∀ i, Disjoint (Set.Ioc (a i) (b i)) (S i)) →
          IsIso (structureMap M hab) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  refine ⟨D.criticalCoordinates, D.criticalCoordinates_finite hD, ?_⟩
  intro a b hab hgap
  exact structureMap_isIso_of_iso e hab
    (D.structureMap_isIso_of_no_critical hab hgap)

/-- Every finitely presented multiparameter module is locally constant under
sufficiently small nonnegative diagonal moves to the right. -/
theorem finitelyPresented_exists_pos_structureMap_isIso
    (M : PModule.{u,0,max u w} R (Fin n → ℝ))
    (hM : FinitelyPresented (R := R) (P := Fin n → ℝ) M)
    (a : Fin n → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ : ℝ) (hδ : 0 ≤ δ), δ ≤ ε →
      IsIso (structureMap M
        (show a ≤ (fun i => a i + δ) from fun _ => le_add_of_nonneg_right hδ)) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  obtain ⟨ε, hε, hstable⟩ := D.exists_pos_structureMap_isIso hD a
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε
  exact structureMap_isIso_of_iso e _ (hstable δ hδ hδε)

end TDA.Persistence.GradedFree
