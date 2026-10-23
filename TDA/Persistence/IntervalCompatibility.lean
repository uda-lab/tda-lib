import TDA.Persistence.SupportInterval
import TDA.Persistence.AlgebraicFamily
import TDA.Persistence.ConstructibleBarcode

/-!
Compatibility between arbitrary order-convex support modules and the existing
real half-open barcode realization. Every isomorphism below is a natural
isomorphism of persistence modules, including at zero fibers.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IntervalCompatibility

open CategoryTheory

variable {k : Type u} [Field k]

/-- The support of an existing real barcode endpoint pair. -/
def support (p : ℝ × WithTop ℝ) : Set ℝ := {t | RealBarcode.alive p t}

/-- Half-open supports, including empty supports and infinite death, are order-convex. -/
theorem support_ordConnected (p : ℝ × WithTop ℝ) : (support p).OrdConnected := by
  refine ⟨?_⟩
  intro s hs t ht r hr
  exact ⟨hs.1.trans hr.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hr.2) ht.2⟩

/-- The generic supported module has exactly the same real fibers and maps as
the existing half-open interval module. -/
theorem support_module_eq (p : ℝ × WithTop ℝ) :
    SupportInterval.module (k := k) (support p) (support_ordConnected p) =
      RealBarcode.intervalModule (k := k) p := by
  rfl

/-- Canonical natural isomorphism on all endpoint pairs, including empty
supports and essential right tails. -/
noncomputable def intervalIso (p : ℝ × WithTop ℝ) :
    SupportInterval.module (k := k) (support p) (support_ordConnected p) ≅
      RealBarcode.intervalModule (k := k) p :=
  eqToIso (support_module_eq p)

/-- A finite direct sum of generic half-open support modules realizes the
existing endpoint list with one coordinate per occurrence. -/
noncomputable def ofListIso (xs : List (ℝ × WithTop ℝ)) :
    AlgebraicFamily.familyModule
      (fun i : Fin xs.length => SupportInterval.module (k := k)
        (support (xs.get i)) (support_ordConnected (xs.get i))) ≅
      RealBarcode.ofList (k := k) xs := by
  let F (i : Fin xs.length) := SupportInterval.module (k := k)
    (support (xs.get i)) (support_ordConnected (xs.get i))
  let G (i : Fin xs.length) := RealBarcode.intervalModule (k := k) (xs.get i)
  change AlgebraicFamily.familyModule F ≅ RealBarcode.familyModule G
  exact AlgebraicFamily.finiteProductIso F ≪≫
    RealBarcode.familyIso (Equiv.refl _) F G (fun i => intervalIso (xs.get i))

/-- Every finite real endpoint diagram admits the same algebraic-sum
realization, including repeated endpoint occurrences. -/
noncomputable def realizeIso (D : Diagram ℝ) :
    AlgebraicFamily.familyModule
      (fun i : Fin D.points.toList.length => SupportInterval.module (k := k)
        (support (D.points.toList.get i))
        (support_ordConnected (D.points.toList.get i))) ≅
      RealBarcode.realize (k := k) D :=
  ofListIso D.points.toList

/-- A finite-constructible module's existing diagram decomposition also gives
an algebraic direct sum of generic half-open support modules. -/
noncomputable def constructibleIso {n : ℕ} (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,u} k ℝ) (hM : FiniteConstructible.IsConstructible c M)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) :
    M ≅ AlgebraicFamily.familyModule
      (fun i : Fin (FiniteConstructible.moduleDiagram c M hfd).points.toList.length =>
        SupportInterval.module (k := k)
          (support ((FiniteConstructible.moduleDiagram c M hfd).points.toList.get i))
          (support_ordConnected
            ((FiniteConstructible.moduleDiagram c M hfd).points.toList.get i))) :=
  FiniteConstructible.barcodeRealizationIso c M hM hfd ≪≫
    (realizeIso (FiniteConstructible.moduleDiagram c M hfd)).symm

end TDA.Persistence.IntervalCompatibility
