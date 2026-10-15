import TDA.Persistence.DiagramLaws

/-!
# Calculus through ordered presentations of persistence diagrams

The derivatives here are derivatives of maps between real normed spaces.  No
derivative or topology is assigned to `Diagram`.
-/

namespace TDA.Persistence

/-- Finite endpoint pairs and essential birth coordinates.  This is the entire
domain of `orderedQ`, including reversed and diagonal finite pairs. -/
abbrev DiagramCoordinates (m n : ℕ) :=
  (Fin m → ℝ × ℝ) × (Fin n → ℝ)

/-- A factorization of a diagram-valued map through `orderedQ` on an explicit
open neighborhood. -/
structure LocalDiagramLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (m n : ℕ) where
  carrier : Set E
  isOpen_carrier : IsOpen carrier
  coordinates : E → DiagramCoordinates m n
  factorization : ∀ x ∈ carrier, B x = orderedQ m n (coordinates x)
  smooth : ContDiffOn ℝ 1 coordinates carrier

/-- Smoothness of a scalar loss at *every* ordered presentation of one diagram.
The neighborhood may depend on the presentation. -/
def C1ThroughAllRepresentatives (V : Diagram ℝ → ℝ) (D : Diagram ℝ) : Prop :=
  ∀ (m n : ℕ) (z : DiagramCoordinates m n), orderedQ m n z = D →
    ∃ W : Set (DiagramCoordinates m n), IsOpen W ∧ z ∈ W ∧
      ContDiffOn ℝ 1 (V ∘ orderedQ m n) W

/-- A scalar diagram loss is locally `C¹` when pulled back through a smooth
local lift. -/
theorem localLift_scalar_c1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalDiagramLift B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : C1ThroughAllRepresentatives V (B x)) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ L.carrier ∧
      ContDiffOn ℝ 1 (V ∘ B) U := by
  obtain ⟨W, hWopen, hzW, hW⟩ := hV m n (L.coordinates x)
    (L.factorization x hx).symm
  let U := L.carrier ∩ L.coordinates ⁻¹' W
  have hUopen : IsOpen U :=
    L.smooth.continuousOn.isOpen_inter_preimage L.isOpen_carrier hWopen
  have hcomp : ContDiffOn ℝ 1 ((V ∘ orderedQ m n) ∘ L.coordinates) U :=
    hW.comp (L.smooth.mono Set.inter_subset_left) Set.inter_subset_right
  refine ⟨U, hUopen, ⟨hx, hzW⟩, Set.inter_subset_left, ?_⟩
  apply hcomp.congr
  intro y hy
  simp only [Function.comp_apply]
  rw [L.factorization y hy.1]

/-- The ordinary Fréchet derivative of a scalar diagram loss is the chain
rule expression for any smooth local lift.  The `HasFDerivAt` conclusion
also certifies that this derivative exists. -/
theorem localLift_scalar_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalDiagramLift B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : C1ThroughAllRepresentatives V (B x)) :
    HasFDerivAt (V ∘ B)
      ((fderiv ℝ (V ∘ orderedQ m n) (L.coordinates x)).comp
        (fderiv ℝ L.coordinates x)) x := by
  obtain ⟨W, hWopen, hzW, hW⟩ := hV m n (L.coordinates x)
    (L.factorization x hx).symm
  have hl : DifferentiableAt ℝ L.coordinates x :=
    (L.smooth.contDiffAt (L.isOpen_carrier.mem_nhds hx)).differentiableAt_one
  have hg : DifferentiableAt ℝ (V ∘ orderedQ m n) (L.coordinates x) :=
    (hW.contDiffAt (hWopen.mem_nhds hzW)).differentiableAt_one
  have hcomp := (hg.hasFDerivAt.comp x hl.hasFDerivAt)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [L.isOpen_carrier.mem_nhds hx] with y hy
  simp only [Function.comp_apply]
  rw [L.factorization y hy]

/-- Equality with the unique ordinary derivative, excluding any default
value for a nonexistent derivative. -/
theorem localLift_scalar_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalDiagramLift B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : C1ThroughAllRepresentatives V (B x)) :
    fderiv ℝ (V ∘ B) x =
      (fderiv ℝ (V ∘ orderedQ m n) (L.coordinates x)).comp
        (fderiv ℝ L.coordinates x) :=
  (localLift_scalar_hasFDerivAt B V m n L x hx hV).fderiv

/-- Two smooth local presentations can have different coordinate dimensions;
their composed derivatives still agree because both derive the same loss. -/
theorem localLift_scalar_derivative_independent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ)
    (m n m' n' : ℕ) (L : LocalDiagramLift B m n)
    (L' : LocalDiagramLift B m' n') (x : E)
    (hx : x ∈ L.carrier) (hx' : x ∈ L'.carrier)
    (hV : C1ThroughAllRepresentatives V (B x)) :
    (fderiv ℝ (V ∘ orderedQ m n) (L.coordinates x)).comp
        (fderiv ℝ L.coordinates x) =
      (fderiv ℝ (V ∘ orderedQ m' n') (L'.coordinates x)).comp
        (fderiv ℝ L'.coordinates x) := by
  rw [← localLift_scalar_fderiv B V m n L x hx hV,
    ← localLift_scalar_fderiv B V m' n' L' x hx' hV]

end TDA.Persistence
