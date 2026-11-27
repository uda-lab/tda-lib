import TDA.Reeb.ConstructibleTransport
import TDA.Reeb.ThickeningConstructibleExamples

/-!
# Client statements of the constructible transport companions

Regression fixtures for #1301, family 15 of the downstream-use audit (#1207). The carrier is
`ULift.{1} Unit`, a type in universe `1`, with the constant heights `c` and the homeomorphism
`Homeomorph.ulift` to the universe-`0` model `Unit`. Each statement is a plain application of a
companion of `TDA/Reeb/ConstructibleTransport.lean`.

* The constant heights on `ULift.{1} Unit` transport to constructible spaces.
* The sup-norm bound for two constant heights on the `Type 1` carrier.
* The model independence of the distance along `Homeomorph.ulift` at universe `0`.
-/

namespace TDA.Reeb.ConstructibleTransportClientExamples

open CategoryTheory TDA.Reeb TDA.Reeb.RGraph
open TDA.Reeb.Examples.ThickeningConstructible (constOver isConstructibleSpace_constOver)
open scoped NNReal ENNReal

/-- The constant height `c` on the carrier `ULift.{1} Unit`. -/
def constUp (c : ℝ) : C(ULift.{1} Unit, ℝ) := ContinuousMap.const _ c

/-- The transport of the constant height on `ULift.{1} Unit` along `Homeomorph.ulift` is the
constant height on `Unit`, which is constructible. -/
theorem isConstructibleSpace_constUp_transport (c : ℝ) :
    IsConstructibleSpace (Over.mk (TopCat.ofHom
      ((constUp c).comp ⟨(Homeomorph.ulift (X := Unit)).symm,
        (Homeomorph.ulift (X := Unit)).symm.continuous⟩))) :=
  isConstructibleSpace_constOver Unit c

/-- The constructible interleaving distance of the transports of two constant heights on a
carrier in `Type 1` is at most their uniform extended distance. -/
theorem constructibleInterleavingDistance_constUp_le (a b : ℝ) :
    constructibleInterleavingDistance ⟨_, isConstructibleSpace_constUp_transport a⟩
        ⟨_, isConstructibleSpace_constUp_transport b⟩ ≤
      edist (UniformFun.ofFun ⇑(constUp a)) (UniformFun.ofFun ⇑(constUp b)) :=
  constructibleInterleavingDistance_le_edist_of_homeomorph Homeomorph.ulift
    (isConstructibleSpace_constUp_transport a) (isConstructibleSpace_constUp_transport b)

/-- Model independence of the distance along `Homeomorph.ulift` at universe `0`. -/
theorem constructibleInterleavingDistance_ulift_zero_eq (a b : ℝ)
    (hF : IsConstructibleSpace (Over.mk (TopCat.ofHom
      (ContinuousMap.const (ULift.{0} Unit) a))))
    (hG : IsConstructibleSpace (Over.mk (TopCat.ofHom
      (ContinuousMap.const (ULift.{0} Unit) b)))) :
    constructibleInterleavingDistance ⟨_, hF⟩ ⟨_, hG⟩ =
      constructibleInterleavingDistance
        ⟨_, (isConstructibleSpace_iff_of_homeomorph Homeomorph.ulift
          (f' := ContinuousMap.const Unit a) (fun _ => rfl)).1 hF⟩
        ⟨_, (isConstructibleSpace_iff_of_homeomorph Homeomorph.ulift
          (f' := ContinuousMap.const Unit b) (fun _ => rfl)).1 hG⟩ :=
  constructibleInterleavingDistance_eq_of_homeomorph Homeomorph.ulift
    (f' := ContinuousMap.const Unit a) (g' := ContinuousMap.const Unit b)
    (fun _ => rfl) (fun _ => rfl) hF hG

end TDA.Reeb.ConstructibleTransportClientExamples
