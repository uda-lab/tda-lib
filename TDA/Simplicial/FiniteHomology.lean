import TDA.Simplicial.FiniteCycles

set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v
open CategoryTheory Module
namespace TDA.Simplicial
variable {V : Type u} [LinearOrder V]

private noncomputable abbrev actualCyclesQuotientWitness
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R] (n : ℕ) :
    HasQuotient (simplicialCycles K R n) (Submodule R (simplicialCycles K R n)) :=
  Submodule.hasQuotient (R := R) (M := simplicialCycles K R n)

private noncomputable abbrev coordinateCyclesQuotientWitness
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Finite (Face K n)] :
    HasQuotient (coordinateCycles K R n) (Submodule R (coordinateCycles K R n)) :=
  Submodule.hasQuotient (R := R) (M := coordinateCycles K R n)

attribute [local instance] actualCyclesQuotientWitness coordinateCyclesQuotientWitness


abbrev coordinateHomology
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Fintype (Face K (n + 1))]
    [DecidableEq (Face K (n + 1))] [Finite (Face K n)] : Type (max u v) :=
  coordinateCycles K R n ⧸ coordinateBoundaries K R n

private noncomputable def quotientCoordinatesAux
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Fintype (Face K (n + 1))]
    [DecidableEq (Face K (n + 1))] [Finite (Face K n)] :=
  Submodule.Quotient.equiv (R := R) (R₂ := R)
    (M := simplicialCycles K R n) (N := coordinateCycles K R n)
    (σ₁₂ := RingHom.id R) (σ₂₁ := RingHom.id R)
    (simplicialBoundaries K R n) (coordinateBoundaries K R n)
    (cycleCoordinates K R n) (simplicialBoundaries_map_cycleCoordinates K R n)

noncomputable def quotientCoordinates
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Fintype (Face K (n + 1))]
    [DecidableEq (Face K (n + 1))] [Finite (Face K n)] :
    (simplicialCycles K R n ⧸ simplicialBoundaries K R n) ≃ₗ[R]
      coordinateHomology K R n :=
  quotientCoordinatesAux K R n

noncomputable def simplicialHomologyCoordinates
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Fintype (Face K (n + 1))]
    [DecidableEq (Face K (n + 1))] [Finite (Face K n)] :
    simplicialHomology K R n ≃ₗ[R] coordinateHomology K R n :=
  (homologyKernelQuotient.{v,u,v} R (simplicialChainComplex K R) n).toLinearEquiv.trans
    (quotientCoordinates K R n)

noncomputable def coordinateHomologyIncl
    (R : Type v) [CommRing R]
    {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Fintype (Face L (n + 1))] [DecidableEq (Face L (n + 1))]
    [Finite (Face L n)] :
    coordinateHomology K R n →ₗ[R] coordinateHomology L R n :=
  (coordinateBoundaries K R n).mapQ (coordinateBoundaries L R n)
    (coordinateCycleIncl R h n) (coordinateBoundaries_le_comap R h n)

variable (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]

theorem quotientCoordinates_mkQ (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] (z : simplicialCycles K R n) :
    quotientCoordinates K R n
        (Submodule.mkQ (R := R) (M := simplicialCycles K R n)
          (simplicialBoundaries K R n) z) =
      Submodule.mkQ (R := R) (M := coordinateCycles K R n)
        (coordinateBoundaries K R n) (cycleCoordinates K R n z) := by
  rfl

theorem simplicialHomologyCoordinates_mkQ (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] (z : simplicialCycles K R n) :
    simplicialHomologyCoordinates K R n
        ((homologyKernelQuotient.{v,u,v} R (simplicialChainComplex K R) n).inv.hom
          (Submodule.mkQ (R := R) (M := simplicialCycles K R n)
            (simplicialBoundaries K R n) z)) =
      Submodule.mkQ (R := R) (M := coordinateCycles K R n)
        (coordinateBoundaries K R n) (cycleCoordinates K R n z) := by
  change quotientCoordinates K R n
    ((homologyKernelQuotient.{v,u,v} R (simplicialChainComplex K R) n).toLinearEquiv
      ((homologyKernelQuotient.{v,u,v} R (simplicialChainComplex K R) n).toLinearEquiv.symm
        (Submodule.mkQ (R := R) (M := simplicialCycles K R n)
          (simplicialBoundaries K R n) z))) = _
  have hcancel := (homologyKernelQuotient.{v,u,v} R
    (simplicialChainComplex K R) n).toLinearEquiv.apply_symm_apply
      (Submodule.mkQ (R := R) (M := simplicialCycles K R n)
        (simplicialBoundaries K R n) z)
  exact (congrArg (quotientCoordinates K R n) hcancel).trans
    (quotientCoordinates_mkQ K R n z)

section Inclusion
variable {K L : PreAbstractSimplicialComplex V}
variable (R : Type v) [CommRing R]

theorem coordinateHomologyIncl_mkQ (h : K ≤ L) (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Fintype (Face L (n + 1))] [DecidableEq (Face L (n + 1))]
    [Finite (Face L n)] (z : coordinateCycles K R n) :
    coordinateHomologyIncl R h n
        (Submodule.mkQ (R := R) (M := coordinateCycles K R n)
          (coordinateBoundaries K R n) z) =
      Submodule.mkQ (R := R) (M := coordinateCycles L R n)
        (coordinateBoundaries L R n) (coordinateCycleIncl R h n z) := by
  rfl

theorem quotientCoordinates_naturality (h : K ≤ L) (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Fintype (Face L (n + 1))] [DecidableEq (Face L (n + 1))]
    [Finite (Face L n)] :
    (coordinateHomologyIncl R h n).comp (quotientCoordinates K R n).toLinearMap =
      (quotientCoordinates L R n).toLinearMap.comp (simplicialQuotientIncl R h n) := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.inductionOn' with
  | _ z =>
    change (coordinateHomologyIncl R h n)
      (quotientCoordinates K R n
        (Submodule.mkQ (R := R) (M := simplicialCycles K R n)
          (simplicialBoundaries K R n) z)) =
      quotientCoordinates L R n
        (simplicialQuotientIncl R h n
          (Submodule.mkQ (R := R) (M := simplicialCycles K R n)
            (simplicialBoundaries K R n) z))
    rw [quotientCoordinates_mkQ, coordinateHomologyIncl_mkQ,
      simplicialQuotientIncl_mkQ, quotientCoordinates_mkQ]
    have hc := congrArg (fun f => f z) (cycleCoordinates_naturality R h n)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
      congrArg (Submodule.mkQ (R := R) (M := coordinateCycles L R n)
        (coordinateBoundaries L R n)) hc

theorem simplicialHomologyCoordinates_naturality (h : K ≤ L) (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Fintype (Face L (n + 1))] [DecidableEq (Face L (n + 1))]
    [Finite (Face L n)] :
    (coordinateHomologyIncl R h n).comp
        (simplicialHomologyCoordinates K R n).toLinearMap =
      (simplicialHomologyCoordinates L R n).toLinearMap.comp
        (simplicialHomologyIncl R h n).hom := by
  apply LinearMap.ext
  intro x
  let qK := (homologyKernelQuotient.{v,u,v} R (simplicialChainComplex K R) n)
  let qL := (homologyKernelQuotient.{v,u,v} R (simplicialChainComplex L R) n)
  have hq := congrArg (fun f => f.hom x)
    (simplicialHomologyIncl_quotient_naturality R h n)
  have he := congrArg
    (fun f => f (qK.toLinearEquiv x)) (quotientCoordinates_naturality R h n)
  change (coordinateHomologyIncl R h n)
      (quotientCoordinates K R n (qK.toLinearEquiv x)) =
    quotientCoordinates L R n (qL.toLinearEquiv ((simplicialHomologyIncl R h n).hom x))
  calc
    _ = quotientCoordinates L R n (simplicialQuotientIncl R h n (qK.toLinearEquiv x)) := by
      exact he
    _ = _ := by
      congr 1
      exact hq.symm

end Inclusion

section Laws
variable (R : Type v) [CommRing R]

theorem coordinateHomologyIncl_id
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Fintype (Face K n)] [DecidableEq (Face K n)] :
    coordinateHomologyIncl R (le_refl K) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (quotientCoordinates K R n).surjective x
  have hq := congrArg (fun f => f y)
    (quotientCoordinates_naturality R (le_refl K) n)
  simp only [LinearMap.comp_apply, simplicialQuotientIncl_id,
    LinearMap.id_apply] at hq
  simpa only [LinearEquiv.coe_coe, LinearMap.id_apply] using hq

theorem coordinateHomologyIncl_comp
    {K L M : PreAbstractSimplicialComplex V} (h : K ≤ L) (g : L ≤ M) (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Fintype (Face L (n + 1))] [DecidableEq (Face L (n + 1))]
    [Fintype (Face L n)] [DecidableEq (Face L n)]
    [Fintype (Face M (n + 1))] [DecidableEq (Face M (n + 1))]
    [Finite (Face M n)] :
    coordinateHomologyIncl R (h.trans g) n =
      (coordinateHomologyIncl R g n).comp (coordinateHomologyIncl R h n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (quotientCoordinates K R n).surjective x
  have hkh := congrArg (fun f => f y) (quotientCoordinates_naturality R h n)
  have hlm := congrArg (fun f => f ((simplicialQuotientIncl R h n) y))
    (quotientCoordinates_naturality R g n)
  have hkm := congrArg (fun f => f y) (quotientCoordinates_naturality R (h.trans g) n)
  simp only [LinearMap.comp_apply] at hkh hlm hkm
  change (coordinateHomologyIncl R (h.trans g) n)
      ((quotientCoordinates K R n).toLinearMap y) =
    (coordinateHomologyIncl R g n)
      ((coordinateHomologyIncl R h n) ((quotientCoordinates K R n).toLinearMap y))
  calc
    _ = (quotientCoordinates M R n).toLinearMap (simplicialQuotientIncl R (h.trans g) n y) := by
      simpa only [LinearEquiv.coe_coe] using hkm
    _ = (quotientCoordinates M R n).toLinearMap
        (simplicialQuotientIncl R g n (simplicialQuotientIncl R h n y)) := by
          congr 1
          exact congrArg (fun f => f y) (simplicialQuotientIncl_comp R h g n)
    _ = _ := by rw [← hlm, ← hkh]

end Laws


end TDA.Simplicial
