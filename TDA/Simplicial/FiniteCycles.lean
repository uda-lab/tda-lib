import TDA.Simplicial.FiniteCoordinates
import TDA.Simplicial.Homology

universe u v
open Module
open scoped Matrix

namespace TDA.Simplicial

variable {V : Type u} [LinearOrder V]

noncomputable def coordinateCycles
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Finite (Face K n)] : Submodule R (Face K n → R) :=
  (simplicialCycles K R n).comap (chainCoordinates K R n).symm.toLinearMap

noncomputable def cycleCoordinates
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Finite (Face K n)] :
    simplicialCycles K R n ≃ₗ[R] coordinateCycles K R n :=
  ((chainCoordinates K R n).symm.ofSubmodule' (simplicialCycles K R n)).symm

private theorem boundary_mem_cycles
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) (c : Chain K R (n + 1)) :
    boundary K R n c ∈ simplicialCycles K R n := by
  cases n with
  | zero => rw [simplicialCycles_zero]; trivial
  | succ m =>
    rw [simplicialCycles_succ]
    change boundary K R m (boundary K R (m + 1) c) = 0
    have h := congrArg (fun f : Chain K R (m + 2) →ₗ[R] Chain K R m => f c)
      (boundary_comp_boundary K R m)
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, Nat.add_assoc] using h

private theorem boundaryMatrix_apply_symm
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Fintype (Face K (n + 1))]
    [DecidableEq (Face K (n + 1))] [Finite (Face K n)]
    (x : Face K (n + 1) → R) :
    Matrix.toLin' (boundaryMatrix K R n) x =
      chainCoordinates K R n (boundary K R n ((chainCoordinates K R (n + 1)).symm x)) := by
  have h := boundaryMatrix_mulVec K R n ((chainCoordinates K R (n + 1)).symm x)
  simpa only [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply] using h

noncomputable def coordinateBoundaryToCycles
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Fintype (Face K (n + 1))]
    [DecidableEq (Face K (n + 1))] [Finite (Face K n)] :
    (Face K (n + 1) → R) →ₗ[R] coordinateCycles K R n :=
  (Matrix.toLin' (boundaryMatrix K R n)).codRestrict (coordinateCycles K R n) (by
    intro x
    change (chainCoordinates K R n).symm
      (Matrix.toLin' (boundaryMatrix K R n) x) ∈ simplicialCycles K R n
    rw [boundaryMatrix_apply_symm]
    simpa only [LinearEquiv.symm_apply_apply] using
      boundary_mem_cycles K R n ((chainCoordinates K R (n + 1)).symm x))

noncomputable def coordinateBoundaries
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Fintype (Face K (n + 1))]
    [DecidableEq (Face K (n + 1))] [Finite (Face K n)] :
    Submodule R (coordinateCycles K R n) :=
  LinearMap.range (coordinateBoundaryToCycles K R n)

noncomputable def coordinateCycleIncl
    (R : Type v) [CommRing R]
    {K L : PreAbstractSimplicialComplex V} (h : K ≤ L)
    (n : ℕ) [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Finite (Face L n)] :
    coordinateCycles K R n →ₗ[R] coordinateCycles L R n :=
  ((Matrix.toLin' (chainInclusionMatrix R h n)).domRestrict
    (coordinateCycles K R n)).codRestrict (coordinateCycles L R n) (by
      intro z
      let c : Chain K R n := (chainCoordinates K R n).symm (z : Face K n → R)
      have hc : c ∈ simplicialCycles K R n := z.property
      have hcy : chainIncl R h n c ∈ simplicialCycles L R n := by
        let hz : simplicialCycles K R n := ⟨c, hc⟩
        have hx := (simplicialCycleIncl R h n hz).property
        rw [simplicialCycleIncl_coe] at hx
        have hhz : (hz : Chain K R n) = c := rfl
        rw [hhz] at hx
        change chainIncl R h n c ∈ simplicialCycles L R n at hx
        exact hx
      change (chainCoordinates L R n).symm
        (Matrix.toLin' (chainInclusionMatrix R h n) (z : Face K n → R)) ∈
          simplicialCycles L R n
      have hm := chainInclusionMatrix_mulVec R h n c
      change chainInclusionMatrix R h n *ᵥ (z : Face K n → R) =
        chainCoordinates L R n (chainIncl R h n c) at hm
      rw [Matrix.toLin'_apply, hm]
      simpa only [LinearEquiv.symm_apply_apply] using hcy)

variable (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]

theorem coordinateCycles_zero [Finite (Face K 0)] :
    coordinateCycles K R 0 = ⊤ := by
  simp [coordinateCycles, simplicialCycles_zero]

theorem coordinateCycles_succ (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] :
    coordinateCycles K R (n + 1) =
      LinearMap.ker (Matrix.toLin' (boundaryMatrix K R n)) := by
  apply Submodule.ext
  intro x
  change (chainCoordinates K R (n + 1)).symm x ∈ simplicialCycles K R (n + 1) ↔
    x ∈ LinearMap.ker (Matrix.toLin' (boundaryMatrix K R n))
  rw [simplicialCycles_succ]
  change boundary K R n ((chainCoordinates K R (n + 1)).symm x) = 0 ↔
    Matrix.toLin' (boundaryMatrix K R n) x = 0
  rw [boundaryMatrix_apply_symm]
  constructor
  · intro h; rw [h, map_zero]
  · intro h; exact (chainCoordinates K R n).injective (by simpa using h)

theorem cycleCoordinates_coe (n : ℕ) [Finite (Face K n)]
    (z : simplicialCycles K R n) :
    (cycleCoordinates K R n z : Face K n → R) =
      chainCoordinates K R n (z : Chain K R n) := by
  exact (LinearEquiv.ofSubmodule'_symm_apply
    (chainCoordinates K R n).symm (simplicialCycles K R n) z)

theorem coordinateBoundaryToCycles_coe (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] (x : Face K (n + 1) → R) :
    (coordinateBoundaryToCycles K R n x : Face K n → R) =
      boundaryMatrix K R n *ᵥ x := by
  rfl

theorem mem_coordinateBoundaries_iff (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] (z : coordinateCycles K R n) :
    z ∈ coordinateBoundaries K R n ↔
      ∃ x : Face K (n + 1) → R,
        boundaryMatrix K R n *ᵥ x = (z : Face K n → R) := by
  rw [coordinateBoundaries, LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (coordinateBoundaryToCycles_coe K R n x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact (coordinateBoundaryToCycles_coe K R n x).trans hx

theorem simplicialBoundaries_map_cycleCoordinates (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] :
    (simplicialBoundaries K R n).map (cycleCoordinates K R n).toLinearMap =
      coordinateBoundaries K R n := by
  apply Submodule.ext
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp hz
    obtain ⟨c, hc⟩ := (mem_simplicialBoundaries_iff R K n w).mp hw
    apply (mem_coordinateBoundaries_iff K R n z).mpr
    refine ⟨chainCoordinates K R (n + 1) c, ?_⟩
    rw [boundaryMatrix_mulVec, hc]
    rw [← cycleCoordinates_coe K R n w]
    exact congrArg Subtype.val hwz
  · intro hz
    obtain ⟨x, hx⟩ := (mem_coordinateBoundaries_iff K R n z).mp hz
    let c : Chain K R (n + 1) := (chainCoordinates K R (n + 1)).symm x
    let w : simplicialCycles K R n := (cycleCoordinates K R n).symm z
    have hc : boundary K R n c = (w : Chain K R n) := by
      apply (chainCoordinates K R n).injective
      have hm := boundaryMatrix_mulVec K R n c
      change boundaryMatrix K R n *ᵥ x =
        chainCoordinates K R n (boundary K R n c) at hm
      calc
        chainCoordinates K R n (boundary K R n c) =
            boundaryMatrix K R n *ᵥ x := hm.symm
        _ = (z : Face K n → R) := hx
        _ = chainCoordinates K R n (w : Chain K R n) := by
          rw [← cycleCoordinates_coe K R n w]
          simp [w]
    apply Submodule.mem_map.mpr
    refine ⟨w, (mem_simplicialBoundaries_iff R K n w).mpr ⟨c, hc⟩, ?_⟩
    exact (cycleCoordinates K R n).apply_symm_apply z

section Inclusion
variable {K L : PreAbstractSimplicialComplex V}
variable (R : Type v) [CommRing R]

theorem coordinateCycleIncl_coe (h : K ≤ L) (n : ℕ)
    [Fintype (Face K n)] [DecidableEq (Face K n)] [Finite (Face L n)]
    (z : coordinateCycles K R n) :
    (coordinateCycleIncl R h n z : Face L n → R) =
      chainInclusionMatrix R h n *ᵥ (z : Face K n → R) := by
  rfl

theorem cycleCoordinates_naturality (h : K ≤ L) (n : ℕ)
    [Fintype (Face K n)] [DecidableEq (Face K n)] [Finite (Face L n)] :
    (coordinateCycleIncl R h n).comp (cycleCoordinates K R n).toLinearMap =
      (cycleCoordinates L R n).toLinearMap.comp (simplicialCycleIncl R h n) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [coordinateCycleIncl_coe, cycleCoordinates_coe, cycleCoordinates_coe,
    simplicialCycleIncl_coe]
  exact chainInclusionMatrix_mulVec R h n (z : Chain K R n)

theorem coordinateCycleIncl_boundaryToCycles (h : K ≤ L) (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Fintype (Face L (n + 1))] [DecidableEq (Face L (n + 1))]
    [Finite (Face L n)] :
    (coordinateCycleIncl R h n).comp (coordinateBoundaryToCycles K R n) =
      (coordinateBoundaryToCycles L R n).comp
        (Matrix.toLin' (chainInclusionMatrix R h (n + 1))) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply]
  rw [coordinateCycleIncl_coe, coordinateBoundaryToCycles_coe,
    coordinateBoundaryToCycles_coe, Matrix.toLin'_apply]
  have hm := boundaryMatrix_chainInclusionMatrix R h n
  calc
    chainInclusionMatrix R h n *ᵥ (boundaryMatrix K R n *ᵥ x) =
        (chainInclusionMatrix R h n * boundaryMatrix K R n) *ᵥ x :=
          Matrix.mulVec_mulVec x (chainInclusionMatrix R h n)
            (boundaryMatrix K R n)
    _ = (boundaryMatrix L R n * chainInclusionMatrix R h (n + 1)) *ᵥ x := by
          rw [hm]
    _ = boundaryMatrix L R n *ᵥ (chainInclusionMatrix R h (n + 1) *ᵥ x) :=
          (Matrix.mulVec_mulVec x (boundaryMatrix L R n)
            (chainInclusionMatrix R h (n + 1))).symm

theorem coordinateBoundaries_le_comap (h : K ≤ L) (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Fintype (Face L (n + 1))] [DecidableEq (Face L (n + 1))]
    [Finite (Face L n)] :
    coordinateBoundaries K R n ≤
      (coordinateBoundaries L R n).comap (coordinateCycleIncl R h n) := by
  intro z hz
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
  change coordinateCycleIncl R h n (coordinateBoundaryToCycles K R n x) ∈
    coordinateBoundaries L R n
  rw [← LinearMap.comp_apply, coordinateCycleIncl_boundaryToCycles,
    LinearMap.comp_apply]
  exact LinearMap.mem_range_self _ _

end Inclusion
end TDA.Simplicial
