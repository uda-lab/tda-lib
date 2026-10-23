import TDA.Persistence.GradedFreeSum
import TDA.Persistence.GradedFreeShift
import TDA.Persistence.FinitePresentation
import TDA.Persistence.FinitePresentationLifting
import TDA.Persistence.CoordinateInterleaving

/-!
# Interleavings from cross-presentations

Lesnick's cross-presentation uses `W₁ ⊕ W₂(-ε)` on one side and
`W₁(-ε) ⊕ W₂` on the other. A one-step cross map keeps the coefficients of
each basis vector and changes only its availability grade. Its two-step
composite is the ordinary structure map. The same maps descend through the
primitive relations and their delayed opposites, giving an actual
interleaving of the two presented quotients. This proves the
cross-presentations-to-interleaving direction of Lesnick Theorem 4.4 over
any ring, including dimension zero and infinite families.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence NNReal

variable {R : Type u} [Ring R] {n : ℕ}

/-- The generator family on the first side of a cross-presentation. -/
def crossLeft (ε : ℝ≥0) (W₁ W₂ : GradedGenerators.{0,w} (Fin n → ℝ)) :
    GradedGenerators.{0,w} (Fin n → ℝ) :=
  W₁.sum (W₂.shiftGrade (-(ε : ℝ)))

/-- The generator family on the second side of a cross-presentation. -/
def crossRight (ε : ℝ≥0) (W₁ W₂ : GradedGenerators.{0,w} (Fin n → ℝ)) :
    GradedGenerators.{0,w} (Fin n → ℝ) :=
  (W₁.shiftGrade (-(ε : ℝ))).sum W₂

private theorem cross_left_fiber_le (ε : ℝ≥0)
    (W₁ W₂ : GradedGenerators.{0,w} (Fin n → ℝ)) (a : Fin n → ℝ) :
    fiber (R := R) (crossLeft ε W₁ W₂) a ≤
      fiber (R := R) (crossRight ε W₁ W₂) (CoordinateShift.translation ε a) := by
  intro x hx g hg i
  cases g with
  | inl g =>
    have h : W₁.grade g i ≤ a i := by
      simpa [crossLeft, GradedGenerators.sum, Sum.elim] using hx hg i
    simpa [crossRight, GradedGenerators.sum, Sum.elim,
      GradedGenerators.shiftGrade, CoordinateShift.translation_apply]
      using add_le_add_right h (ε : ℝ)
  | inr g =>
    have h : W₂.grade g i + (ε : ℝ) ≤ a i := by
      simpa [crossLeft, GradedGenerators.sum, Sum.elim,
        GradedGenerators.shiftGrade]
        using hx hg i
    have h' : W₂.grade g i ≤ a i + (ε : ℝ) := by
      nlinarith [ε.coe_nonneg]
    simpa [crossRight, GradedGenerators.sum, Sum.elim,
      CoordinateShift.translation_apply] using h'

private theorem cross_right_fiber_le (ε : ℝ≥0)
    (W₁ W₂ : GradedGenerators.{0,w} (Fin n → ℝ)) (a : Fin n → ℝ) :
    fiber (R := R) (crossRight ε W₁ W₂) a ≤
      fiber (R := R) (crossLeft ε W₁ W₂) (CoordinateShift.translation ε a) := by
  intro x hx g hg i
  cases g with
  | inl g =>
    have h : W₁.grade g i + (ε : ℝ) ≤ a i := by
      simpa [crossRight, GradedGenerators.sum, Sum.elim,
        GradedGenerators.shiftGrade]
        using hx hg i
    have h' : W₁.grade g i ≤ a i + (ε : ℝ) := by
      nlinarith [ε.coe_nonneg]
    simpa [crossLeft, GradedGenerators.sum, Sum.elim,
      CoordinateShift.translation_apply] using h'
  | inr g =>
    have h : W₂.grade g i ≤ a i := by
      simpa [crossRight, GradedGenerators.sum, Sum.elim] using hx hg i
    simpa [crossLeft, GradedGenerators.sum, Sum.elim,
      GradedGenerators.shiftGrade, CoordinateShift.translation_apply]
      using add_le_add_right h (ε : ℝ)

/-- Free cross map: a basis vector is carried unchanged to its next eligible grade. -/
noncomputable def crossFreeLR (ε : ℝ≥0)
    (W₁ W₂ : GradedGenerators.{0,w} (Fin n → ℝ)) :
    module (R := R) (crossLeft ε W₁ W₂) ⟶
      (CoordinateShift.shift ε).obj (module (crossRight ε W₁ W₂)) where
  app a := ModuleCat.ofHom (Submodule.inclusion (cross_left_fiber_le (R := R) ε W₁ W₂ a))
  naturality a b f := by
    apply ModuleCat.hom_ext
    rfl

/-- The cross map in the other direction. -/
noncomputable def crossFreeRL (ε : ℝ≥0)
    (W₁ W₂ : GradedGenerators.{0,w} (Fin n → ℝ)) :
    module (R := R) (crossRight ε W₁ W₂) ⟶
      (CoordinateShift.shift ε).obj (module (crossLeft ε W₁ W₂)) where
  app a := ModuleCat.ofHom (Submodule.inclusion (cross_right_fiber_le (R := R) ε W₁ W₂ a))
  naturality a b f := by
    apply ModuleCat.hom_ext
    rfl

/-- The free cross maps give an actual interleaving, with no quotient assumptions. -/
noncomputable def crossFreeInterleaving (ε : ℝ≥0)
    (W₁ W₂ : GradedGenerators.{0,w} (Fin n → ℝ)) :
    CoordinateInterleaving ε
      (module (R := R) (crossLeft ε W₁ W₂))
      (module (R := R) (crossRight ε W₁ W₂)) :=
  CoordinateInterleaving.ofApp (crossFreeLR (R := R) ε W₁ W₂)
    (crossFreeRL (R := R) ε W₁ W₂)
    (by intro a; apply ModuleCat.hom_ext; rfl)
    (by intro a; apply ModuleCat.hom_ext; rfl)

private theorem delayed_grade_eq_translation (ε : ℝ≥0)
    (Y : GradedGenerators.{0,w} (Fin n → ℝ)) (y : Y.Carrier) :
    (Y.shiftGrade (-(ε : ℝ))).grade y =
      CoordinateShift.translation ε (Y.grade y) := by
  funext i
  simp

/-- Shift a homogeneous map out of a free family from its old births to the
same relations born `ε` later. -/
noncomputable def delaySource (ε : ℝ≥0)
    (Y : GradedGenerators.{0,w} (Fin n → ℝ))
    (M : PModule.{u,0,max u w} R (Fin n → ℝ))
    (f : module (R := R) Y ⟶ (CoordinateShift.shift ε).obj M) :
    module (R := R) (Y.shiftGrade (-(ε : ℝ))) ⟶ M :=
  lift (Y.shiftGrade (-(ε : ℝ))) M (fun y =>
    M.map (eqToHom (delayed_grade_eq_translation ε Y y).symm)
      (f.app (Y.grade y) (birth Y y)))

theorem delaySource_birth (ε : ℝ≥0)
    (Y : GradedGenerators.{0,w} (Fin n → ℝ))
    (M : PModule.{u,0,max u w} R (Fin n → ℝ))
    (f : module (R := R) Y ⟶ (CoordinateShift.shift ε).obj M)
    (y : Y.Carrier) :
    (delaySource ε Y M f).app ((Y.shiftGrade (-(ε : ℝ))).grade y)
      (birth (Y.shiftGrade (-(ε : ℝ))) y) =
    M.map (eqToHom (delayed_grade_eq_translation ε Y y).symm)
      (f.app (Y.grade y) (birth Y y)) :=
  lift_birth (Y.shiftGrade (-(ε : ℝ))) M _ y

/-- If the delayed birth values vanish after a map, then the original shifted
birth values vanish too. The index equality is the actual grade arithmetic. -/
theorem delaySource_comp_zero (ε : ℝ≥0)
    (Y : GradedGenerators.{0,w} (Fin n → ℝ))
    {M N : PModule.{u,0,max u w} R (Fin n → ℝ)}
    (f : module (R := R) Y ⟶ (CoordinateShift.shift ε).obj M)
    (ρ : M ⟶ N)
    (h : delaySource ε Y M f ≫ ρ = 0) :
    f ≫ (CoordinateShift.shift ε).map ρ = 0 := by
  apply hom_ext_birth Y
  intro y
  let t := Y.grade y
  let d := (Y.shiftGrade (-(ε : ℝ))).grade y
  let e : d = CoordinateShift.translation ε t := delayed_grade_eq_translation ε Y y
  have hy := congrArg
    (fun q : module (R := R) (Y.shiftGrade (-(ε : ℝ))) ⟶ N =>
      q.app d (birth (Y.shiftGrade (-(ε : ℝ))) y)) h
  change ρ.app d ((delaySource ε Y M f).app d
    (birth (Y.shiftGrade (-(ε : ℝ))) y)) = 0 at hy
  rw [delaySource_birth] at hy
  have hn := ρ.naturality (eqToHom e)
  have hv := congrArg
    (fun q : M.obj d ⟶ N.obj (CoordinateShift.translation ε t) =>
      q (M.map (eqToHom e.symm) (f.app t (birth Y y)))) hn
  change ρ.app (CoordinateShift.translation ε t)
        (M.map (eqToHom e) (M.map (eqToHom e.symm)
          (f.app t (birth Y y)))) =
    N.map (eqToHom e) (ρ.app d (M.map (eqToHom e.symm)
      (f.app t (birth Y y)))) at hv
  have hy' : ρ.app d (M.map (eqToHom e.symm)
      (f.app t (birth Y y))) = 0 := by
    simpa [d, t, e] using hy
  rw [hy', map_zero] at hv
  have hc : M.map (eqToHom e) (M.map (eqToHom e.symm)
        (f.app t (birth Y y))) = f.app t (birth Y y) := by
    calc
      _ = M.map (eqToHom e.symm ≫ eqToHom e) (f.app t (birth Y y)) := by
        rw [Functor.map_comp]
        rfl
      _ = _ := by simp
  change ρ.app (CoordinateShift.translation ε t) (f.app t (birth Y y)) = 0
  simpa only [hc] using hv

/-- Primitive homogeneous relations on both sides determine the two full
cross-presentations; no interleaving or vanishing condition is stored. -/
structure CrossData (ε : ℝ≥0) where
  W₁ : GradedGenerators.{0,w} (Fin n → ℝ)
  W₂ : GradedGenerators.{0,w} (Fin n → ℝ)
  Y₁ : GradedGenerators.{0,w} (Fin n → ℝ)
  Y₂ : GradedGenerators.{0,w} (Fin n → ℝ)
  r₁ : module (R := R) Y₁ ⟶ module (crossLeft ε W₁ W₂)
  r₂ : module (R := R) Y₂ ⟶ module (crossRight ε W₁ W₂)

variable {ε : ℝ≥0} (C : CrossData.{u,w} (R := R) (n := n) ε)

/-- The first side's primitive relations, transported to the second side a
step later. -/
noncomputable def CrossData.leftDelayed :
    module (R := R) (C.Y₁.shiftGrade (-(ε : ℝ))) ⟶
      module (crossRight ε C.W₁ C.W₂) :=
  delaySource ε C.Y₁ (module (crossRight ε C.W₁ C.W₂))
    (C.r₁ ≫ crossFreeLR ε C.W₁ C.W₂)

/-- The opposite primitive relations, transported back to the first side. -/
noncomputable def CrossData.rightDelayed :
    module (R := R) (C.Y₂.shiftGrade (-(ε : ℝ))) ⟶
      module (crossLeft ε C.W₁ C.W₂) :=
  delaySource ε C.Y₂ (module (crossLeft ε C.W₁ C.W₂))
    (C.r₂ ≫ crossFreeRL ε C.W₁ C.W₂)

/-- The first quotient has relations `Y₁ ⊕ Y₂(-ε)`. -/
noncomputable abbrev CrossData.leftPresentation :
    Presentation.{u,0,w} (R := R) (P := Fin n → ℝ) where
  generators := crossLeft ε C.W₁ C.W₂
  relations := C.Y₁.sum (C.Y₂.shiftGrade (-(ε : ℝ)))
  relationMap := sumDesc C.Y₁ (C.Y₂.shiftGrade (-(ε : ℝ))) C.r₁ C.rightDelayed

/-- The second quotient has relations `Y₁(-ε) ⊕ Y₂`. -/
noncomputable abbrev CrossData.rightPresentation :
    Presentation.{u,0,w} (R := R) (P := Fin n → ℝ) where
  generators := crossRight ε C.W₁ C.W₂
  relations := (C.Y₁.shiftGrade (-(ε : ℝ))).sum C.Y₂
  relationMap := sumDesc (C.Y₁.shiftGrade (-(ε : ℝ))) C.Y₂ C.leftDelayed C.r₂

/-- Finiteness of the four primitive families gives finite presentations on
both sides. -/
theorem CrossData.finite (h : Finite C.W₁.Carrier ∧ Finite C.W₂.Carrier ∧
    Finite C.Y₁.Carrier ∧ Finite C.Y₂.Carrier) :
    C.leftPresentation.IsFinite ∧ C.rightPresentation.IsFinite := by
  rcases h with ⟨hW₁, hW₂, hY₁, hY₂⟩
  have : Finite C.W₁.Carrier := hW₁
  have : Finite C.W₂.Carrier := hW₂
  have : Finite C.Y₁.Carrier := hY₁
  have : Finite C.Y₂.Carrier := hY₂
  let : Fintype C.W₁.Carrier := Fintype.ofFinite _
  let : Fintype C.W₂.Carrier := Fintype.ofFinite _
  let : Fintype C.Y₁.Carrier := Fintype.ofFinite _
  let : Fintype C.Y₂.Carrier := Fintype.ofFinite _
  change (Finite (C.W₁.Carrier ⊕ C.W₂.Carrier) ∧
      Finite (C.Y₁.Carrier ⊕ C.Y₂.Carrier)) ∧
    (Finite (C.W₁.Carrier ⊕ C.W₂.Carrier) ∧
      Finite (C.Y₁.Carrier ⊕ C.Y₂.Carrier))
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

private theorem CrossData.primitiveLR_vanish :
    C.r₁ ≫ crossFreeLR ε C.W₁ C.W₂ ≫
      (CoordinateShift.shift ε).map C.rightPresentation.cover = 0 := by
  have hv : C.leftDelayed ≫ C.rightPresentation.cover = 0 := by
    have h := congrArg
      (fun f : module (R := R) C.rightPresentation.relations ⟶
          C.rightPresentation.presented =>
        sumInl (C.Y₁.shiftGrade (-(ε : ℝ))) C.Y₂ ≫ f)
      C.rightPresentation.relations_vanish
    have hz : sumInl (R := R) (C.Y₁.shiftGrade (-(ε : ℝ))) C.Y₂ ≫
        (0 : module (R := R) C.rightPresentation.relations ⟶
          C.rightPresentation.presented) = 0 := by
      apply NatTrans.ext
      funext a
      rfl
    rw [hz] at h
    simpa [CrossData.rightPresentation, ← Category.assoc] using h
  exact delaySource_comp_zero ε C.Y₁
    (C.r₁ ≫ crossFreeLR ε C.W₁ C.W₂) C.rightPresentation.cover hv

private theorem CrossData.oppositeLR_birth
    (y : C.Y₂.Carrier)
    (h : C.Y₂.grade y ≤ CoordinateShift.translation ε
      ((C.Y₂.shiftGrade (-(ε : ℝ))).grade y)) :
    (crossFreeLR ε C.W₁ C.W₂).app
        ((C.Y₂.shiftGrade (-(ε : ℝ))).grade y)
        (C.rightDelayed.app ((C.Y₂.shiftGrade (-(ε : ℝ))).grade y)
          (birth (C.Y₂.shiftGrade (-(ε : ℝ))) y)) =
      structureMapLinear (module (R := R) (crossRight ε C.W₁ C.W₂)) h
        (C.r₂.app (C.Y₂.grade y) (birth C.Y₂ y)) := by
  apply Subtype.ext
  rw [CrossData.rightDelayed, delaySource_birth]
  rfl

private theorem CrossData.oppositeLR_vanish :
    C.rightDelayed ≫ crossFreeLR ε C.W₁ C.W₂ ≫
      (CoordinateShift.shift ε).map C.rightPresentation.cover = 0 := by
  have hr : C.r₂ ≫ C.rightPresentation.cover = 0 := by
    have h := congrArg
      (fun f : module (R := R) C.rightPresentation.relations ⟶
          C.rightPresentation.presented =>
        sumInr (C.Y₁.shiftGrade (-(ε : ℝ))) C.Y₂ ≫ f)
      C.rightPresentation.relations_vanish
    have hz : sumInr (R := R) (C.Y₁.shiftGrade (-(ε : ℝ))) C.Y₂ ≫
        (0 : module (R := R) C.rightPresentation.relations ⟶
          C.rightPresentation.presented) = 0 := by
      apply NatTrans.ext
      funext a
      rfl
    rw [hz] at h
    simpa [CrossData.rightPresentation, ← Category.assoc] using h
  apply hom_ext_birth (C.Y₂.shiftGrade (-(ε : ℝ)))
  intro y
  let d := (C.Y₂.shiftGrade (-(ε : ℝ))).grade y
  let t := C.Y₂.grade y
  let x := C.r₂.app t (birth C.Y₂ y)
  have ht : t ≤ CoordinateShift.translation ε d := by
    intro i
    dsimp [t, d, CoordinateShift.translation, GradedGenerators.shiftGrade]
    change C.Y₂.grade y i ≤
      (C.Y₂.grade y i - -(ε : ℝ)) + (ε : ℝ)
    nlinarith [ε.coe_nonneg]
  have hx : C.rightPresentation.cover.app t x = 0 := by
    have h := congrArg
      (fun q : module (R := R) C.Y₂ ⟶ C.rightPresentation.presented =>
        q.app t (birth C.Y₂ y)) hr
    change C.rightPresentation.cover.app t x = 0 at h
    exact h
  have hn := C.rightPresentation.cover.naturality (homOfLE ht)
  have hv := congrArg
    (fun q : (module (R := R) (crossRight ε C.W₁ C.W₂)).obj t ⟶
        C.rightPresentation.presented.obj (CoordinateShift.translation ε d) =>
      q x) hn
  change C.rightPresentation.cover.app (CoordinateShift.translation ε d)
      (structureMapLinear (module (R := R) (crossRight ε C.W₁ C.W₂)) ht x) =
    structureMapLinear C.rightPresentation.presented ht
      (C.rightPresentation.cover.app t x) at hv
  rw [hx, map_zero] at hv
  change C.rightPresentation.cover.app (CoordinateShift.translation ε d)
    ((crossFreeLR ε C.W₁ C.W₂).app d
      (C.rightDelayed.app d (birth (C.Y₂.shiftGrade (-(ε : ℝ))) y))) = 0
  rw [C.oppositeLR_birth y ht]
  exact hv

/-- Both relation families vanish after crossing and passing to the opposite
quotient. This is the actual descent condition for the cross map. -/
theorem CrossData.leftRelationsCross_vanish :
    C.leftPresentation.relationMap ≫ crossFreeLR ε C.W₁ C.W₂ ≫
      (CoordinateShift.shift ε).map C.rightPresentation.cover = 0 := by
  apply sumHom_ext C.Y₁ (C.Y₂.shiftGrade (-(ε : ℝ)))
  · calc
      _ = C.r₁ ≫ crossFreeLR ε C.W₁ C.W₂ ≫
          (CoordinateShift.shift ε).map C.rightPresentation.cover := by
        simp [CrossData.leftPresentation, ← Category.assoc]
      _ = 0 := C.primitiveLR_vanish
      _ = sumInl (R := R) C.Y₁ (C.Y₂.shiftGrade (-(ε : ℝ))) ≫
          (0 : module (R := R) C.leftPresentation.relations ⟶
            (CoordinateShift.shift ε).obj C.rightPresentation.presented) := by
        apply NatTrans.ext
        funext a
        rfl
  · calc
      _ = C.rightDelayed ≫ crossFreeLR ε C.W₁ C.W₂ ≫
          (CoordinateShift.shift ε).map C.rightPresentation.cover := by
        simp [CrossData.leftPresentation, ← Category.assoc]
      _ = 0 := C.oppositeLR_vanish
      _ = sumInr (R := R) C.Y₁ (C.Y₂.shiftGrade (-(ε : ℝ))) ≫
          (0 : module (R := R) C.leftPresentation.relations ⟶
            (CoordinateShift.shift ε).obj C.rightPresentation.presented) := by
        apply NatTrans.ext
        funext a
        rfl

/-- The first cross map descends through both relation families to the
presented quotient. -/
noncomputable def CrossData.quotientLR :
    C.leftPresentation.presented ⟶
      (CoordinateShift.shift ε).obj C.rightPresentation.presented :=
  C.leftPresentation.desc
    (crossFreeLR ε C.W₁ C.W₂ ≫
      (CoordinateShift.shift ε).map C.rightPresentation.cover)
    (by simpa only [Category.assoc] using C.leftRelationsCross_vanish)

theorem CrossData.cover_quotientLR :
    C.leftPresentation.cover ≫ C.quotientLR =
      crossFreeLR ε C.W₁ C.W₂ ≫
        (CoordinateShift.shift ε).map C.rightPresentation.cover :=
  C.leftPresentation.cover_desc _ _

private theorem CrossData.primitiveRL_vanish :
    C.r₂ ≫ crossFreeRL ε C.W₁ C.W₂ ≫
      (CoordinateShift.shift ε).map C.leftPresentation.cover = 0 := by
  have hv : C.rightDelayed ≫ C.leftPresentation.cover = 0 := by
    have h := congrArg
      (fun f : module (R := R) C.leftPresentation.relations ⟶
          C.leftPresentation.presented =>
        sumInr C.Y₁ (C.Y₂.shiftGrade (-(ε : ℝ))) ≫ f)
      C.leftPresentation.relations_vanish
    have hz : sumInr (R := R) C.Y₁ (C.Y₂.shiftGrade (-(ε : ℝ))) ≫
        (0 : module (R := R) C.leftPresentation.relations ⟶
          C.leftPresentation.presented) = 0 := by
      apply NatTrans.ext
      funext a
      rfl
    rw [hz] at h
    simpa [CrossData.leftPresentation, ← Category.assoc] using h
  exact delaySource_comp_zero ε C.Y₂
    (C.r₂ ≫ crossFreeRL ε C.W₁ C.W₂) C.leftPresentation.cover hv

private theorem CrossData.oppositeRL_birth
    (y : C.Y₁.Carrier)
    (h : C.Y₁.grade y ≤ CoordinateShift.translation ε
      ((C.Y₁.shiftGrade (-(ε : ℝ))).grade y)) :
    (crossFreeRL ε C.W₁ C.W₂).app
        ((C.Y₁.shiftGrade (-(ε : ℝ))).grade y)
        (C.leftDelayed.app ((C.Y₁.shiftGrade (-(ε : ℝ))).grade y)
          (birth (C.Y₁.shiftGrade (-(ε : ℝ))) y)) =
      structureMapLinear (module (R := R) (crossLeft ε C.W₁ C.W₂)) h
        (C.r₁.app (C.Y₁.grade y) (birth C.Y₁ y)) := by
  apply Subtype.ext
  rw [CrossData.leftDelayed, delaySource_birth]
  rfl

private theorem CrossData.oppositeRL_vanish :
    C.leftDelayed ≫ crossFreeRL ε C.W₁ C.W₂ ≫
      (CoordinateShift.shift ε).map C.leftPresentation.cover = 0 := by
  have hr : C.r₁ ≫ C.leftPresentation.cover = 0 := by
    have h := congrArg
      (fun f : module (R := R) C.leftPresentation.relations ⟶
          C.leftPresentation.presented =>
        sumInl C.Y₁ (C.Y₂.shiftGrade (-(ε : ℝ))) ≫ f)
      C.leftPresentation.relations_vanish
    have hz : sumInl (R := R) C.Y₁ (C.Y₂.shiftGrade (-(ε : ℝ))) ≫
        (0 : module (R := R) C.leftPresentation.relations ⟶
          C.leftPresentation.presented) = 0 := by
      apply NatTrans.ext
      funext a
      rfl
    rw [hz] at h
    simpa [CrossData.leftPresentation, ← Category.assoc] using h
  apply hom_ext_birth (C.Y₁.shiftGrade (-(ε : ℝ)))
  intro y
  let d := (C.Y₁.shiftGrade (-(ε : ℝ))).grade y
  let t := C.Y₁.grade y
  let x := C.r₁.app t (birth C.Y₁ y)
  have ht : t ≤ CoordinateShift.translation ε d := by
    intro i
    dsimp [t, d, CoordinateShift.translation, GradedGenerators.shiftGrade]
    change C.Y₁.grade y i ≤
      (C.Y₁.grade y i - -(ε : ℝ)) + (ε : ℝ)
    nlinarith [ε.coe_nonneg]
  have hx : C.leftPresentation.cover.app t x = 0 := by
    have h := congrArg
      (fun q : module (R := R) C.Y₁ ⟶ C.leftPresentation.presented =>
        q.app t (birth C.Y₁ y)) hr
    change C.leftPresentation.cover.app t x = 0 at h
    exact h
  have hn := C.leftPresentation.cover.naturality (homOfLE ht)
  have hv := congrArg
    (fun q : (module (R := R) (crossLeft ε C.W₁ C.W₂)).obj t ⟶
        C.leftPresentation.presented.obj (CoordinateShift.translation ε d) =>
      q x) hn
  change C.leftPresentation.cover.app (CoordinateShift.translation ε d)
      (structureMapLinear (module (R := R) (crossLeft ε C.W₁ C.W₂)) ht x) =
    structureMapLinear C.leftPresentation.presented ht
      (C.leftPresentation.cover.app t x) at hv
  rw [hx, map_zero] at hv
  change C.leftPresentation.cover.app (CoordinateShift.translation ε d)
    ((crossFreeRL ε C.W₁ C.W₂).app d
      (C.leftDelayed.app d (birth (C.Y₁.shiftGrade (-(ε : ℝ))) y))) = 0
  rw [C.oppositeRL_birth y ht]
  exact hv

theorem CrossData.rightRelationsCross_vanish :
    C.rightPresentation.relationMap ≫ crossFreeRL ε C.W₁ C.W₂ ≫
      (CoordinateShift.shift ε).map C.leftPresentation.cover = 0 := by
  apply sumHom_ext (C.Y₁.shiftGrade (-(ε : ℝ))) C.Y₂
  · calc
      _ = C.leftDelayed ≫ crossFreeRL ε C.W₁ C.W₂ ≫
          (CoordinateShift.shift ε).map C.leftPresentation.cover := by
        simp [CrossData.rightPresentation, ← Category.assoc]
      _ = 0 := C.oppositeRL_vanish
      _ = sumInl (R := R) (C.Y₁.shiftGrade (-(ε : ℝ))) C.Y₂ ≫
          (0 : module (R := R) C.rightPresentation.relations ⟶
            (CoordinateShift.shift ε).obj C.leftPresentation.presented) := by
        apply NatTrans.ext
        funext a
        rfl
  · calc
      _ = C.r₂ ≫ crossFreeRL ε C.W₁ C.W₂ ≫
          (CoordinateShift.shift ε).map C.leftPresentation.cover := by
        simp [CrossData.rightPresentation, ← Category.assoc]
      _ = 0 := C.primitiveRL_vanish
      _ = sumInr (R := R) (C.Y₁.shiftGrade (-(ε : ℝ))) C.Y₂ ≫
          (0 : module (R := R) C.rightPresentation.relations ⟶
            (CoordinateShift.shift ε).obj C.leftPresentation.presented) := by
        apply NatTrans.ext
        funext a
        rfl

/-- The second cross map descends through both relation families. -/
noncomputable def CrossData.quotientRL :
    C.rightPresentation.presented ⟶
      (CoordinateShift.shift ε).obj C.leftPresentation.presented :=
  C.rightPresentation.desc
    (crossFreeRL ε C.W₁ C.W₂ ≫
      (CoordinateShift.shift ε).map C.leftPresentation.cover)
    (by simpa only [Category.assoc] using C.rightRelationsCross_vanish)

theorem CrossData.cover_quotientRL :
    C.rightPresentation.cover ≫ C.quotientRL =
      crossFreeRL ε C.W₁ C.W₂ ≫
        (CoordinateShift.shift ε).map C.leftPresentation.cover :=
  C.rightPresentation.cover_desc _ _

/-- Cross-presentations yield an actual interleaving of their quotient modules.
No interleaving equation is part of the input data. -/
noncomputable def CrossData.quotientInterleaving :
    CoordinateInterleaving ε C.leftPresentation.presented
      C.rightPresentation.presented where
  φ := C.quotientLR
  ψ := C.quotientRL
  φ_ψ := by
    have : Epi C.leftPresentation.cover := by
      change Epi (cokernel.π C.leftPresentation.relationMap)
      infer_instance
    apply (cancel_epi C.leftPresentation.cover).mp
    simp only [← Category.assoc, C.cover_quotientLR]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [C.cover_quotientRL, Functor.map_comp]
    simp only [Category.assoc]
    rw [CoordinateShift.compIso_naturality]
    simpa only [Category.assoc, crossFreeInterleaving, CoordinateInterleaving.ofApp] using
      (congrArg (fun f => f ≫ (CoordinateShift.shift (ε + ε)).map
        C.leftPresentation.cover)
        (crossFreeInterleaving (R := R) ε C.W₁ C.W₂).φ_ψ).trans
          (CoordinateShift.transition_naturality (ε + ε)
            C.leftPresentation.cover).symm
  ψ_φ := by
    have : Epi C.rightPresentation.cover := by
      change Epi (cokernel.π C.rightPresentation.relationMap)
      infer_instance
    apply (cancel_epi C.rightPresentation.cover).mp
    simp only [← Category.assoc, C.cover_quotientRL]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [C.cover_quotientLR, Functor.map_comp]
    simp only [Category.assoc]
    rw [CoordinateShift.compIso_naturality]
    simpa only [Category.assoc, crossFreeInterleaving, CoordinateInterleaving.ofApp] using
      (congrArg (fun f => f ≫ (CoordinateShift.shift (ε + ε)).map
        C.rightPresentation.cover)
        (crossFreeInterleaving (R := R) ε C.W₁ C.W₂).ψ_φ).trans
          (CoordinateShift.transition_naturality (ε + ε)
            C.rightPresentation.cover).symm

/-- Transport the quotient interleaving to modules with the displayed
cross-presentations. No interleaving or descent equation is assumed. -/
noncomputable def CrossData.interleavingOfIso
    {M N : PModule.{u,0,max u w} R (Fin n → ℝ)}
    (eM : C.leftPresentation.presented ≅ M)
    (eN : C.rightPresentation.presented ≅ N) : CoordinateInterleaving ε M N :=
  C.quotientInterleaving.congr eM eN

/-- At parameter zero the two cross-presented quotients are naturally isomorphic. -/
noncomputable def CrossData.zeroIso (C : CrossData.{u,w} (R := R) (n := n) 0) :
    C.leftPresentation.presented ≅ C.rightPresentation.presented :=
  C.quotientInterleaving.toIso

end TDA.Persistence.GradedFree
