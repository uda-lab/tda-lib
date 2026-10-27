import TDA.Persistence.IncidenceQuotientSimple
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!
# Right-module extension along the diagonal quotient

For the actual quotient map on the opposite incidence algebras, this file constructs
extension of scalars as a quotient by the action of its kernel.  The construction is
valid over an arbitrary field.  Its projective and degree-zero consequences are
underived statements; no exactness of a chosen resolution is asserted here.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceQuotientBaseChange

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceVertexTor
open TDA.Persistence.IncidenceQuotientSimple

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : DecidableLE S := Classical.decRel _
local instance : DecidableLT S := Classical.decRel _
local instance : DecidableEq S := Classical.decEq _
local instance : DecidableEq (WithTop S) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset S) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop S × WithTop S => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset S) := Classical.decRel _
local instance : DecidableLT (PairPoset S) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset S) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset S) := Classical.decEq _
local instance : Fintype (ComparablePair S) := Fintype.ofFinite _

abbrev Incidence := FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)
abbrev DiagonalIdeal := FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
  (k := k) (S := S)
abbrev DiagonalQuotient := Incidence (k := k) (S := S) ⧸ DiagonalIdeal (k := k) (S := S)
abbrev RightIncidence := (Incidence (k := k) (S := S))ᵐᵒᵖ
abbrev RightQuotient := (DiagonalQuotient (k := k) (S := S))ᵐᵒᵖ

local instance diagonalIdealTwoSided :
    (DiagonalIdeal (k := k) (S := S)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := S)

/-- The actual quotient projection on the right-module rings. -/
def quotientHom : RightIncidence (k := k) (S := S) →+* RightQuotient (k := k) (S := S) :=
  (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))).op

/-- The right-module quotient map is surjective. -/
theorem quotientHom_surjective :
    Function.Surjective (quotientHom (k := k) (S := S)) := by
  intro c
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (MulOpposite.unop c)
  refine ⟨MulOpposite.op b, ?_⟩
  simpa [quotientHom] using congrArg MulOpposite.op hb

/-- The relations killed when extending a right incidence module across the quotient. -/
def relation (M : ModuleCat (RightIncidence (k := k) (S := S))) :
    Submodule (RightIncidence (k := k) (S := S)) M :=
  Submodule.span (RightIncidence (k := k) (S := S))
    (Set.range fun z : (RingHom.ker (quotientHom (k := k) (S := S))) × M =>
      (z.1 : RightIncidence (k := k) (S := S)) • z.2)

/-- The kernel-action quotient, before its descended quotient-ring action is installed. -/
abbrev quotient (M : ModuleCat (RightIncidence (k := k) (S := S))) :=
  M ⧸ relation (k := k) (S := S) M

private theorem kernel_smul_class_eq_zero
    (M : ModuleCat (RightIncidence (k := k) (S := S)))
    (a : RightIncidence (k := k) (S := S))
    (ha : a ∈ RingHom.ker (quotientHom (k := k) (S := S))) (m : M) :
    (relation (k := k) (S := S) M).mkQ (a • m) = 0 := by
  apply (Submodule.Quotient.eq (relation (k := k) (S := S) M)).2
  change a • m - 0 ∈ relation (k := k) (S := S) M
  simpa [relation] using (Submodule.subset_span
    (s := Set.range fun z :
      (RingHom.ker (quotientHom (k := k) (S := S))) × M =>
        (z.1 : RightIncidence (k := k) (S := S)) • z.2)
    ⟨(⟨a, ha⟩, m), rfl⟩)

/-- Every element in the kernel of the quotient map acts by zero on the quotient. -/
theorem kernel_action_annihilates
    (M : ModuleCat (RightIncidence (k := k) (S := S)))
    (a : RightIncidence (k := k) (S := S))
    (ha : a ∈ RingHom.ker (quotientHom (k := k) (S := S)))
    (x : quotient (k := k) (S := S) M) :
    a • x = 0 := by
  obtain ⟨m, rfl⟩ := (relation (k := k) (S := S) M).mkQ_surjective x
  exact kernel_smul_class_eq_zero (k := k) (S := S) M a ha m

private theorem kernel_le_action_ker
    (M : ModuleCat (RightIncidence (k := k) (S := S))) :
    RingHom.ker (quotientHom (k := k) (S := S)) ≤
      RingHom.ker (Module.toAddMonoidEnd (RightIncidence (k := k) (S := S))
        (quotient (k := k) (S := S) M)) := by
  intro a ha
  change Module.toAddMonoidEnd (RightIncidence (k := k) (S := S))
      (quotient (k := k) (S := S) M) a = 0
  apply AddMonoidHom.ext
  intro x
  change a • x = 0
  exact kernel_action_annihilates (k := k) (S := S) M a ha x

/-- The right-module action on the quotient, factored through the actual quotient ring. -/
noncomputable def quotientAction
    (M : ModuleCat (RightIncidence (k := k) (S := S))) :
    RightQuotient (k := k) (S := S) →+*
      AddMonoid.End (quotient (k := k) (S := S) M) :=
  (quotientHom (k := k) (S := S)).liftOfSurjective
    (quotientHom_surjective (k := k) (S := S))
    ⟨Module.toAddMonoidEnd (RightIncidence (k := k) (S := S))
        (quotient (k := k) (S := S) M),
      kernel_le_action_ker (k := k) (S := S) M⟩

/-- The descended action agrees with the original action after quotient projection. -/
@[simp] theorem quotientAction_comp_apply
    (M : ModuleCat (RightIncidence (k := k) (S := S)))
    (r : RightIncidence (k := k) (S := S)) (x : quotient (k := k) (S := S) M) :
    quotientAction (k := k) (S := S) M (quotientHom (k := k) (S := S) r) x = r • x := by
  rw [quotientAction, RingHom.liftOfSurjective_comp_apply]
  rfl

@[instance_reducible] private noncomputable def quotientModuleStructure
    (M : ModuleCat (RightIncidence (k := k) (S := S))) :
    Module (RightQuotient (k := k) (S := S)) (quotient (k := k) (S := S) M) := by
  let Q := quotient (k := k) (S := S) M
  letI : SMul (RightQuotient (k := k) (S := S)) Q :=
    ⟨fun c x => quotientAction (k := k) (S := S) M c x⟩
  exact {
    one_smul x := by
      change quotientAction (k := k) (S := S) M 1 x = x
      rw [(quotientAction (k := k) (S := S) M).map_one]
      exact rfl
    mul_smul c d x := by
      change quotientAction (k := k) (S := S) M (c * d) x =
        quotientAction (k := k) (S := S) M c
          (quotientAction (k := k) (S := S) M d x)
      rw [(quotientAction (k := k) (S := S) M).map_mul]
      rfl
    smul_zero c := by
      change quotientAction (k := k) (S := S) M c 0 = 0
      exact (quotientAction (k := k) (S := S) M c).map_zero
    smul_add c x y := by
      change quotientAction (k := k) (S := S) M c (x + y) =
        quotientAction (k := k) (S := S) M c x +
          quotientAction (k := k) (S := S) M c y
      exact (quotientAction (k := k) (S := S) M c).map_add x y
    zero_smul x := by
      change quotientAction (k := k) (S := S) M 0 x = 0
      rw [(quotientAction (k := k) (S := S) M).map_zero]
      rfl
    add_smul c d x := by
      change quotientAction (k := k) (S := S) M (c + d) x =
        quotientAction (k := k) (S := S) M c x +
          quotientAction (k := k) (S := S) M d x
      rw [(quotientAction (k := k) (S := S) M).map_add]
      rfl
  }

@[instance_reducible] noncomputable instance quotientModule_isModule
    (M : ModuleCat (RightIncidence (k := k) (S := S))) :
    Module (RightQuotient (k := k) (S := S)) (quotient (k := k) (S := S) M) :=
  quotientModuleStructure (k := k) (S := S) M

/-- The actual quotient object with its action obtained from the ring-map factorization. -/
noncomputable def quotientModule
    (M : ModuleCat (RightIncidence (k := k) (S := S))) :
    ModuleCat (RightQuotient (k := k) (S := S)) :=
  ModuleCat.of (RightQuotient (k := k) (S := S)) (quotient (k := k) (S := S) M)

@[simp] theorem quotientModule_smul
    (M : ModuleCat (RightIncidence (k := k) (S := S)))
    (c : RightQuotient (k := k) (S := S)) (x : quotientModule (k := k) (S := S) M) :
    c • x = quotientAction (k := k) (S := S) M c x := rfl

@[simp] theorem quotientModule_class_smul
    (M : ModuleCat (RightIncidence (k := k) (S := S)))
    (r : RightIncidence (k := k) (S := S)) (m : M) :
    quotientHom (k := k) (S := S) r •
      (relation (k := k) (S := S) M).mkQ m =
        (relation (k := k) (S := S) M).mkQ (r • m) := by
  letI : Module (RightQuotient (k := k) (S := S)) (quotient (k := k) (S := S) M) :=
    quotientModuleStructure (k := k) (S := S) M
  change quotientAction (k := k) (S := S) M
    (quotientHom (k := k) (S := S) r)
      ((relation (k := k) (S := S) M).mkQ m) = _
  rw [quotientAction_comp_apply]
  rfl

/-- The canonical quotient map, viewed as a right-incidence-linear map into the restricted
extension. -/
noncomputable def quotientProjectionHom
    (M : ModuleCat (RightIncidence (k := k) (S := S))) :
    M →ₗ[RightIncidence (k := k) (S := S)]
      (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj
        (quotientModule (k := k) (S := S) M) := by
  let target := (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj
    (quotientModule (k := k) (S := S) M)
  letI : Module (RightIncidence (k := k) (S := S)) target := target.isModule
  exact {
    toFun := (relation (k := k) (S := S) M).mkQ
    map_add' := by intro x y; rfl
    map_smul' := by
      intro r m
      change (relation (k := k) (S := S) M).mkQ (r • m) =
        quotientHom (k := k) (S := S) r •
          (relation (k := k) (S := S) M).mkQ m
      exact (quotientModule_class_smul (k := k) (S := S) M r m).symm
  }

/-- The canonical quotient map, viewed as a right-incidence-linear map into the restricted
extension. -/
noncomputable def quotientProjection
    (M : ModuleCat (RightIncidence (k := k) (S := S))) :
    M ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj
      (quotientModule (k := k) (S := S) M) :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom (quotientProjectionHom (k := k) (S := S) M).toAddMonoidHom)
    (fun r => by
      letI : Module (RightIncidence (k := k) (S := S)) M := M.isModule
      apply AddCommGrpCat.ext
      intro m
      change (((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj
          (quotientModule (k := k) (S := S) M)).smul r).hom
            (quotientProjectionHom (k := k) (S := S) M m) =
        quotientProjectionHom (k := k) (S := S) M
          (((ModuleCat.of (RightIncidence (k := k) (S := S)) M).smul r).hom m)
      change quotientHom (k := k) (S := S) r •
          quotientProjectionHom (k := k) (S := S) M (m : M) =
        quotientProjectionHom (k := k) (S := S) M (r • (m : M))
      exact (quotientProjectionHom (k := k) (S := S) M).map_smul r (m : M) |>.symm)

@[simp] theorem quotientProjection_apply
    (M : ModuleCat (RightIncidence (k := k) (S := S))) (m : M) :
    (quotientProjection (k := k) (S := S) M).hom m =
      (relation (k := k) (S := S) M).mkQ m := by
  change quotientProjectionHom (k := k) (S := S) M m = _
  rfl

private theorem relation_map_le
    {M N : ModuleCat (RightIncidence (k := k) (S := S))} (g : M ⟶ N) :
    relation (k := k) (S := S) M ≤
      Submodule.comap g.hom (relation (k := k) (S := S) N) := by
  apply Submodule.span_le.2
  rintro _ ⟨z, rfl⟩
  apply Submodule.subset_span
  refine ⟨(z.1, g.hom z.2), ?_⟩
  change z.1 • g.hom z.2 = g.hom (z.1 • z.2)
  exact (g.hom.map_smul z.1 z.2).symm

/-- The map between quotient presentations induced by an actual module map. -/
def mapQuotient {M N : ModuleCat (RightIncidence (k := k) (S := S))}
    (g : M ⟶ N) : quotient (k := k) (S := S) M →ₗ[RightIncidence (k := k) (S := S)]
      quotient (k := k) (S := S) N :=
  (relation (k := k) (S := S) M).mapQ
    (relation (k := k) (S := S) N) g.hom (relation_map_le (k := k) (S := S) g)

@[simp] theorem mapQuotient_mkQ {M N : ModuleCat (RightIncidence (k := k) (S := S))}
    (g : M ⟶ N) (m : M) :
    mapQuotient (k := k) (S := S) g ((relation (k := k) (S := S) M).mkQ m) =
      (relation (k := k) (S := S) N).mkQ (g.hom m) := rfl

/-- The induced map on the descended quotient modules is linear over the quotient ring. -/
def extensionMap {M N : ModuleCat (RightIncidence (k := k) (S := S))}
    (g : M ⟶ N) : quotientModule (k := k) (S := S) M ⟶
      quotientModule (k := k) (S := S) N :=
  ModuleCat.ofHom {
    toFun := mapQuotient (k := k) (S := S) g
    map_add' := (mapQuotient (k := k) (S := S) g).map_add
    map_smul' := by
      intro c x
      obtain ⟨r, hr⟩ := quotientHom_surjective (k := k) (S := S) c
      obtain ⟨m, hm⟩ := (relation (k := k) (S := S) M).mkQ_surjective x
      rw [← hm, ← hr]
      calc
        mapQuotient (k := k) (S := S) g
            (quotientHom (k := k) (S := S) r •
              (relation (k := k) (S := S) M).mkQ m) =
            mapQuotient (k := k) (S := S) g
              ((relation (k := k) (S := S) M).mkQ (r • m)) := by
                rw [quotientModule_class_smul]
        _ = (relation (k := k) (S := S) N).mkQ (g.hom (r • m)) :=
              mapQuotient_mkQ (k := k) (S := S) g (r • m)
        _ = (relation (k := k) (S := S) N).mkQ (r • g.hom m) := by
              rw [g.hom.map_smul]
        _ = quotientHom (k := k) (S := S) r •
              (relation (k := k) (S := S) N).mkQ (g.hom m) := by
              rw [← quotientModule_class_smul]
        _ = quotientHom (k := k) (S := S) r •
              mapQuotient (k := k) (S := S) g
                ((relation (k := k) (S := S) M).mkQ m) := by
              rw [mapQuotient_mkQ]
  }

@[simp] theorem extensionMap_mkQ {M N : ModuleCat (RightIncidence (k := k) (S := S))}
    (g : M ⟶ N) (m : M) :
    (extensionMap (k := k) (S := S) g).hom
      ((relation (k := k) (S := S) M).mkQ m) =
        (relation (k := k) (S := S) N).mkQ (g.hom m) :=
  mapQuotient_mkQ (k := k) (S := S) g m

/-- The extension-of-scalars functor defined by the actual kernel-action quotients. -/
noncomputable def extensionFunctor :
    ModuleCat (RightIncidence (k := k) (S := S)) ⥤ ModuleCat (RightQuotient (k := k) (S := S)) where
  obj := quotientModule (k := k) (S := S)
  map := extensionMap (k := k) (S := S)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m, hm⟩ := (relation (k := k) (S := S) M).mkQ_surjective x
    rw [← hm]
    change mapQuotient (k := k) (S := S) (𝟙 M)
      ((relation (k := k) (S := S) M).mkQ m) = _
    rw [mapQuotient_mkQ]
    rfl
  map_comp {M N P} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m, hm⟩ := (relation (k := k) (S := S) M).mkQ_surjective x
    rw [← hm]
    change mapQuotient (k := k) (S := S) (f ≫ g)
      ((relation (k := k) (S := S) M).mkQ m) =
        mapQuotient (k := k) (S := S) g
          (mapQuotient (k := k) (S := S) f
            ((relation (k := k) (S := S) M).mkQ m))
    rw [mapQuotient_mkQ, mapQuotient_mkQ, mapQuotient_mkQ]
    rfl

private theorem relation_le_ker_of_restrictedMap
    {M : ModuleCat (RightIncidence (k := k) (S := S))}
    {N : ModuleCat (RightQuotient (k := k) (S := S))}
    (g : M ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) :
    relation (k := k) (S := S) M ≤ LinearMap.ker g.hom := by
  apply Submodule.span_le.2
  rintro _ ⟨z, rfl⟩
  change g.hom (z.1 • z.2) = 0
  calc
    g.hom (z.1 • z.2) =
        (z.1 : RightIncidence (k := k) (S := S)) • g.hom z.2 := by
          exact g.hom.map_smul _ _
    _ = 0 := by
      have hz : quotientHom (k := k) (S := S) z.1 = 0 :=
        RingHom.mem_ker.mp z.1.property
      simp [ModuleCat.restrictScalars.smul_def, hz]
      exact zero_smul _ _

/-- The quotient map out of `M/K(M)` induced by a map into a restricted quotient module. -/
noncomputable def liftQuotient
    {M : ModuleCat (RightIncidence (k := k) (S := S))}
    {N : ModuleCat (RightQuotient (k := k) (S := S))}
    (g : M ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) :
    quotient (k := k) (S := S) M →ₗ[RightIncidence (k := k) (S := S)]
      (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N :=
  (relation (k := k) (S := S) M).liftQ g.hom
    (relation_le_ker_of_restrictedMap (k := k) (S := S) g)

@[simp] theorem liftQuotient_mkQ
    {M : ModuleCat (RightIncidence (k := k) (S := S))}
    {N : ModuleCat (RightQuotient (k := k) (S := S))}
    (g : M ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)
    (m : M) :
    liftQuotient (k := k) (S := S) g ((relation (k := k) (S := S) M).mkQ m) =
      g.hom m := rfl

/-- The factor map is linear over the quotient ring. -/
noncomputable def liftCLinearMap
    {M : ModuleCat (RightIncidence (k := k) (S := S))}
    {N : ModuleCat (RightQuotient (k := k) (S := S))}
    (g : M ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) :
    quotientModule (k := k) (S := S) M →ₗ[RightQuotient (k := k) (S := S)] N := by
  let p := liftQuotient (k := k) (S := S) g
  exact {
    toFun := p
    map_add' := p.map_add
    map_smul' := by
      intro c x
      obtain ⟨r, hr⟩ := quotientHom_surjective (k := k) (S := S) c
      obtain ⟨m, hm⟩ := (relation (k := k) (S := S) M).mkQ_surjective x
      rw [← hm, ← hr]
      calc
        p (quotientHom (k := k) (S := S) r •
            (relation (k := k) (S := S) M).mkQ m) =
            p ((relation (k := k) (S := S) M).mkQ (r • m)) := by
              rw [quotientModule_class_smul]
        _ = g.hom (r • m) := rfl
        _ = quotientHom (k := k) (S := S) r • g.hom m := by
              exact g.hom.map_smul r m
        _ = quotientHom (k := k) (S := S) r •
              p ((relation (k := k) (S := S) M).mkQ m) := by rw [liftQuotient_mkQ]
  }

@[simp] theorem liftCLinearMap_mkQ
    {M : ModuleCat (RightIncidence (k := k) (S := S))}
    {N : ModuleCat (RightQuotient (k := k) (S := S))}
    (g : M ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)
    (m : M) :
    liftCLinearMap (k := k) (S := S) g
      ((relation (k := k) (S := S) M).mkQ m) = g.hom m := rfl

/-- The unique quotient-ring-linear factor of a map that kills `K(M)`. -/
noncomputable def liftMap
    {M : ModuleCat (RightIncidence (k := k) (S := S))}
    {N : ModuleCat (RightQuotient (k := k) (S := S))}
    (g : M ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) :
    quotientModule (k := k) (S := S) M ⟶ N :=
  ModuleCat.ofHom (liftCLinearMap (k := k) (S := S) g)

@[simp] theorem liftMap_mkQ
    {M : ModuleCat (RightIncidence (k := k) (S := S))}
    {N : ModuleCat (RightQuotient (k := k) (S := S))}
    (g : M ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)
    (m : M) :
    (liftMap (k := k) (S := S) g).hom
      ((relation (k := k) (S := S) M).mkQ m) = g.hom m :=
  by
    change liftCLinearMap (k := k) (S := S) g
      ((relation (k := k) (S := S) M).mkQ m) = _
    exact liftCLinearMap_mkQ (k := k) (S := S) g m

instance extensionFunctor_additive :
    (extensionFunctor (k := k) (S := S)).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m, hm⟩ := (relation (k := k) (S := S) M).mkQ_surjective x
    rw [← hm]
    change mapQuotient (k := k) (S := S) (f + g)
      ((relation (k := k) (S := S) M).mkQ m) =
        mapQuotient (k := k) (S := S) f
            ((relation (k := k) (S := S) M).mkQ m) +
          mapQuotient (k := k) (S := S) g
            ((relation (k := k) (S := S) M).mkQ m)
    rw [mapQuotient_mkQ, mapQuotient_mkQ, mapQuotient_mkQ]
    rfl

/-- The hom-set equivalence defining extension as left adjoint to restriction. -/
noncomputable def extensionHomEquiv
    (M : ModuleCat (RightIncidence (k := k) (S := S)))
    (N : ModuleCat (RightQuotient (k := k) (S := S))) :
    ((extensionFunctor (k := k) (S := S)).obj M ⟶ N) ≃
      (M ⟶ (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) where
  toFun f := quotientProjection (k := k) (S := S) M ≫
    (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).map f
  invFun := liftMap (k := k) (S := S)
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m, hm⟩ := (relation (k := k) (S := S) M).mkQ_surjective x
    rw [← hm]
    change (liftMap (k := k) (S := S)
        (quotientProjection (k := k) (S := S) M ≫
          (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).map f)).hom
        ((relation (k := k) (S := S) M).mkQ m) =
      f.hom ((relation (k := k) (S := S) M).mkQ m)
    rw [liftMap_mkQ]
    simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply,
      quotientProjection_apply]
    rfl
  right_inv g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (liftMap (k := k) (S := S) g).hom
        ((relation (k := k) (S := S) M).mkQ m) = g.hom m
    exact liftMap_mkQ (k := k) (S := S) g m

/-- Extension of scalars along the actual quotient map is left adjoint to restriction. -/
noncomputable def extensionAdjunction :
    extensionFunctor (k := k) (S := S) ⊣
      ModuleCat.restrictScalars (quotientHom (k := k) (S := S)) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := extensionHomEquiv (k := k) (S := S)
    homEquiv_naturality_left_symm := by
      intro M' M N f g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨m, hm⟩ := (relation (k := k) (S := S) M').mkQ_surjective x
      rw [← hm]
      change (liftMap (k := k) (S := S) (f ≫ g)).hom
          ((relation (k := k) (S := S) M').mkQ m) =
        (extensionMap (k := k) (S := S) f ≫
          liftMap (k := k) (S := S) g).hom
          ((relation (k := k) (S := S) M').mkQ m)
      simp only [liftMap_mkQ, ModuleCat.comp_apply, extensionMap_mkQ]
      rfl
    homEquiv_naturality_right := by
      intro M N N' f g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change (quotientProjection (k := k) (S := S) M ≫
          (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).map (f ≫ g)).hom m =
        ((quotientProjection (k := k) (S := S) M ≫
          (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).map f) ≫
          (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).map g).hom m
      simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply,
        quotientProjection_apply]
      rfl
  }

end

end TDA.Persistence.IncidenceQuotientBaseChange
