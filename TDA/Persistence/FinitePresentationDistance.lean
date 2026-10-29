import TDA.Persistence.FinitePresentationClosure
import Mathlib.Topology.EMetricSpace.Basic

/-!
# The interleaving distance on finitely presented isomorphism classes

For a ring `R` and `n : ℕ`, take the subtype of finitely presented modules
`PModule R (Fin n → ℝ)` and quotient it by natural isomorphism. The coordinate
interleaving distance descends to this quotient and defines an extended metric.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.GradedFree

open CategoryTheory
open scoped TDA.Persistence NNReal ENNReal

variable {R : Type u} [Ring R] {n : ℕ}

/-- A coordinate persistence module together with a proof of finite presentation. -/
abbrev FinitelyPresentedModule :=
  {M : PModule.{u,0,max u w} R (Fin n → ℝ) // FinitelyPresented (R := R) M}

namespace FinitePresentationIsoClasses

/-- Finitely presented modules are equivalent when naturally isomorphic. -/
def isoSetoid : Setoid (FinitelyPresentedModule (R := R) (n := n)) where
  r M N := Nonempty (M.1 ≅ N.1)
  iseqv := ⟨
    fun M => ⟨Iso.refl M.1⟩,
    fun h => by
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩,
    fun h₁ h₂ => by
      rcases h₁ with ⟨e⟩
      rcases h₂ with ⟨f⟩
      exact ⟨e ≪≫ f⟩⟩

end FinitePresentationIsoClasses

/-- Isomorphism classes of finitely presented coordinate persistence modules. -/
abbrev FinitePresentationIsoClasses :=
  Quotient (FinitePresentationIsoClasses.isoSetoid (R := R) (n := n))

namespace FinitePresentationIsoClasses

/-- The isomorphism class represented by a finitely presented module. -/
def classOf (M : FinitelyPresentedModule (R := R) (n := n)) :
    FinitePresentationIsoClasses (R := R) (n := n) :=
  Quotient.mk isoSetoid M

/-- The coordinate interleaving distance on isomorphism classes. -/
noncomputable def distance
    (x y : FinitePresentationIsoClasses (R := R) (n := n)) : ℝ≥0∞ :=
  Quotient.lift₂
    (fun M N => coordinateInterleavingDistance M.1 N.1)
    (by
      intro M M' N N' hM hN
      rcases hM with ⟨e⟩
      rcases hN with ⟨f⟩
      exact coordinateInterleavingDistance_congr e f)
    x y

@[simp]
theorem distance_classOf
    (M N : FinitelyPresentedModule (R := R) (n := n)) :
    distance (classOf M) (classOf N) =
      coordinateInterleavingDistance M.1 N.1 := rfl

/-- Isomorphic representatives have the same distance to any isomorphic pair. -/
theorem distance_congr
    {M M' N N' : FinitelyPresentedModule (R := R) (n := n)}
    (e : M.1 ≅ M'.1) (f : N.1 ≅ N'.1) :
    distance (classOf M) (classOf N) = distance (classOf M') (classOf N') := by
  rw [distance_classOf, distance_classOf]
  exact coordinateInterleavingDistance_congr e f

/-- Every isomorphism class has zero distance from itself. -/
theorem distance_self (x : FinitePresentationIsoClasses (R := R) (n := n)) :
    distance x x = 0 := by
  induction x using Quotient.inductionOn with
  | h M =>
    change distance (classOf M) (classOf M) = 0
    rw [distance_classOf]
    exact coordinateInterleavingDistance_self M.1

/-- The quotient distance is symmetric. -/
theorem distance_comm (x y : FinitePresentationIsoClasses (R := R) (n := n)) :
    distance x y = distance y x := by
  induction x using Quotient.inductionOn with
  | h M =>
    induction y using Quotient.inductionOn with
    | h N =>
      change distance (classOf M) (classOf N) = distance (classOf N) (classOf M)
      rw [distance_classOf, distance_classOf]
      exact coordinateInterleavingDistance_comm M.1 N.1

/-- The quotient distance satisfies the extended triangle inequality. -/
theorem distance_triangle
    (x y z : FinitePresentationIsoClasses (R := R) (n := n)) :
    distance x z ≤ distance x y + distance y z := by
  induction x using Quotient.inductionOn with
  | h M =>
    induction y using Quotient.inductionOn with
    | h N =>
      induction z using Quotient.inductionOn with
      | h P =>
        change distance (classOf M) (classOf P) ≤
          distance (classOf M) (classOf N) + distance (classOf N) (classOf P)
        rw [distance_classOf, distance_classOf, distance_classOf]
        exact coordinateInterleavingDistance_triangle M.1 N.1 P.1

/-- On presented representatives, zero distance is equivalent to natural isomorphism. -/
theorem distance_classOf_eq_zero_iff_iso
    (M N : FinitelyPresentedModule (R := R) (n := n)) :
    distance (classOf M) (classOf N) = 0 ↔ Nonempty (M.1 ≅ N.1) := by
  rw [distance_classOf]
  exact finitelyPresented_distance_eq_zero_iff_iso M.2 N.2

/-- Zero distance on the quotient is equality of isomorphism classes. -/
theorem distance_eq_zero_iff_eq
    (x y : FinitePresentationIsoClasses (R := R) (n := n)) :
    distance x y = 0 ↔ x = y := by
  constructor
  · intro h
    induction x using Quotient.inductionOn with
    | h M =>
      induction y using Quotient.inductionOn with
      | h N =>
        change distance (classOf M) (classOf N) = 0 at h
        rw [distance_classOf] at h
        apply Quotient.sound
        apply (finitelyPresented_distance_eq_zero_iff_iso M.2 N.2).mp
        exact h
  · rintro rfl
    exact distance_self x

/-- Isomorphism classes form an extended metric space for the descended distance. -/
noncomputable instance emetricSpace :
    EMetricSpace (FinitePresentationIsoClasses (R := R) (n := n)) where
  toPseudoEMetricSpace :=
    PseudoEMetricSpace.ofEDist distance distance_self distance_comm distance_triangle
  eq_of_edist_eq_zero := by
    intro x y h
    change distance x y = 0 at h
    exact distance_eq_zero_iff_eq x y |>.mp h

/-- The `edist` instance agrees with the original distance on representatives. -/
@[simp]
theorem edist_classOf
    (M N : FinitelyPresentedModule (R := R) (n := n)) :
    edist (classOf M) (classOf N) = coordinateInterleavingDistance M.1 N.1 := rfl

end FinitePresentationIsoClasses

end TDA.Persistence.GradedFree
