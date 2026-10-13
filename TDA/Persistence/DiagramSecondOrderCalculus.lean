import TDA.Persistence.DiagramCalculus
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Second-order scalar calculus through ordered diagram presentations

All derivatives are ordinary Fréchet derivatives between real normed spaces.
The convention is `D²f(x)[h,k] = D(Df)(x)[h][k]`. No topology on diagrams is used.
-/

open Topology

namespace TDA.Persistence

/-- `C²` regularity at every full ordered presentation, with a presentation-dependent
open neighborhood. Diagonal and reversed finite pairs are included. -/
def C2ThroughAllRepresentatives (V : Diagram ℝ → ℝ) (D : Diagram ℝ) : Prop :=
  ∀ (m n : ℕ) (z : DiagramCoordinates m n), orderedQ m n z = D →
    ∃ W : Set (DiagramCoordinates m n), IsOpen W ∧ z ∈ W ∧
      ContDiffOn ℝ 2 (V ∘ orderedQ m n) W

/-- Second-order all-presentations regularity implies the existing first-order condition. -/
theorem C2ThroughAllRepresentatives.c1 {V : Diagram ℝ → ℝ} {D : Diagram ℝ}
    (hV : C2ThroughAllRepresentatives V D) : C1ThroughAllRepresentatives V D := by
  intro m n z hz
  obtain ⟨W, hW, hzW, hs⟩ := hV m n z hz
  exact ⟨W, hW, hzW, hs.of_le (by norm_num)⟩

/-- A second-order local lift retains the entire existing first-order lift. -/
structure LocalC2DiagramLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (m n : ℕ) extends LocalDiagramLift B m n where
  smooth_two : ContDiffOn ℝ 2 coordinates carrier

section Chain

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The ordinary second-order chain expression, as a continuous bilinear map.
The first summand differentiates the outer derivative and the second differentiates
the lift derivative, retaining curvature of the parametrization. -/
noncomputable def secondDerivativeChain (g : F → G) (f : E → F) (x : E) :
    E →L[ℝ] E →L[ℝ] G :=
  ((ContinuousLinearMap.compL ℝ E F G).flip (fderiv ℝ f x)).comp
      ((fderiv ℝ (fderiv ℝ g) (f x)).comp (fderiv ℝ f x)) +
    (ContinuousLinearMap.compL ℝ E F G (fderiv ℝ g (f x))).comp
      (fderiv ℝ (fderiv ℝ f) x)

/-- Evaluation of the bilinear chain expression displays both chain-rule terms. -/
theorem secondDerivativeChain_apply (g : F → G) (f : E → F) (x h k : E) :
    secondDerivativeChain g f x h k =
      fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x h) (fderiv ℝ f x k) +
      fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x h k) := by
  rfl

/-- Differentiating the derivative of a `C²` composition gives the full chain expression.
This establishes existence, and hence cannot hold merely by a default `fderiv` value. -/
theorem secondDerivativeChain_hasFDerivAt (g : F → G) (f : E → F) (x : E)
    (hg : ContDiffAt ℝ 2 g (f x)) (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (fderiv ℝ (g ∘ f)) (secondDerivativeChain g f x) x := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) (f x) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hc := (hdg.hasFDerivAt.comp x (hf.differentiableAt (by norm_num)).hasFDerivAt)
    |>.clm_comp hdf.hasFDerivAt
  have heq : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ g (f y)).comp (fderiv ℝ f y) := by
    filter_upwards [hf.eventually (by norm_num),
      hf.continuousAt (hg.eventually (by norm_num))] with y hfy hgy
    change ContDiffAt ℝ 2 g (f y) at hgy
    exact fderiv_comp y (hgy.differentiableAt (by norm_num))
      (hfy.differentiableAt (by norm_num))
  simpa only [secondDerivativeChain, Function.comp_apply, add_comm] using hc.congr_of_eventuallyEq heq

/-- Equality with the nested derivative follows from the genuine derivative theorem. -/
theorem secondDerivativeChain_fderiv (g : F → G) (f : E → F) (x : E)
    (hg : ContDiffAt ℝ 2 g (f x)) (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x = secondDerivativeChain g f x :=
  (secondDerivativeChain_hasFDerivAt g f x hg hf).fderiv

/-- Postcomposition by a fixed continuous linear selection differentiates twice without
an additional term. This applies in particular to fixed face-coordinate selection. -/
theorem secondDerivative_linear_postcomp (R : F →L[ℝ] G) (g : E → F) (x : E)
    (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => R (g y))) x =
      (ContinuousLinearMap.compL ℝ E F G R).comp (fderiv ℝ (fderiv ℝ g) x) := by
  rw [show (fun y => R (g y)) = R ∘ g from rfl,
    secondDerivativeChain_fderiv R g x R.contDiff.contDiffAt hg]
  have hR : fderiv ℝ (R : F → G) = fun _ => R :=
    funext fun y => R.fderiv
  simp [secondDerivativeChain, hR]

end Chain

/-- A scalar loss pulled back through a `C²` local lift is `C²` on an open
neighborhood contained in the original carrier. -/
theorem localLift_scalar_c2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalC2DiagramLift B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : C2ThroughAllRepresentatives V (B x)) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ L.carrier ∧
      ContDiffOn ℝ 2 (V ∘ B) U := by
  obtain ⟨W, hWopen, hzW, hW⟩ := hV m n (L.coordinates x)
    (L.factorization x hx).symm
  let U := L.carrier ∩ L.coordinates ⁻¹' W
  have hUopen : IsOpen U :=
    L.smooth_two.continuousOn.isOpen_inter_preimage L.isOpen_carrier hWopen
  have hcomp : ContDiffOn ℝ 2 ((V ∘ orderedQ m n) ∘ L.coordinates) U :=
    hW.comp (L.smooth_two.mono Set.inter_subset_left) Set.inter_subset_right
  refine ⟨U, hUopen, ⟨hx, hzW⟩, Set.inter_subset_left, ?_⟩
  apply hcomp.congr
  intro y hy
  simp only [Function.comp_apply]
  rw [L.factorization y hy.1]

/-- The derivative map of the scalar loss has the full bilinear chain expression
as its derivative. -/
theorem localLift_scalar_hasFDerivAt_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalC2DiagramLift B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : C2ThroughAllRepresentatives V (B x)) :
    HasFDerivAt (fderiv ℝ (V ∘ B))
      (secondDerivativeChain (V ∘ orderedQ m n) L.coordinates x) x := by
  obtain ⟨W, hWopen, hzW, hW⟩ := hV m n (L.coordinates x)
    (L.factorization x hx).symm
  have hg := hW.contDiffAt (hWopen.mem_nhds hzW)
  have hf := L.smooth_two.contDiffAt (L.isOpen_carrier.mem_nhds hx)
  have heq : (V ∘ B) =ᶠ[𝓝 x] ((V ∘ orderedQ m n) ∘ L.coordinates) := by
    filter_upwards [L.isOpen_carrier.mem_nhds hx] with y hy
    simp only [Function.comp_apply]
    rw [L.factorization y hy]
  exact (secondDerivativeChain_hasFDerivAt _ _ x hg hf).congr_of_eventuallyEq heq.fderiv

/-- The second derivative is the bilinear chain expression of any `C²` local lift. -/
theorem localLift_scalar_second_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalC2DiagramLift B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : C2ThroughAllRepresentatives V (B x)) :
    fderiv ℝ (fderiv ℝ (V ∘ B)) x =
      secondDerivativeChain (V ∘ orderedQ m n) L.coordinates x :=
  (localLift_scalar_hasFDerivAt_fderiv B V m n L x hx hV).fderiv

/-- The scalar second derivative is symmetric under the stated `C²` assumptions. -/
theorem localLift_scalar_second_fderiv_symmetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalC2DiagramLift B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : C2ThroughAllRepresentatives V (B x)) (h k : E) :
    fderiv ℝ (fderiv ℝ (V ∘ B)) x h k =
      fderiv ℝ (fderiv ℝ (V ∘ B)) x k h := by
  obtain ⟨U, hU, hxU, _, hs⟩ := localLift_scalar_c2 B V m n L x hx hV
  exact (hs.contDiffAt (hU.mem_nhds hxU)).isSymmSndFDerivAt (by norm_num) h k

/-- Symmetry also holds directly for the bilinear expression obtained from a lift. -/
theorem localLift_scalar_secondDerivativeChain_symmetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalC2DiagramLift B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : C2ThroughAllRepresentatives V (B x)) (h k : E) :
    secondDerivativeChain (V ∘ orderedQ m n) L.coordinates x h k =
      secondDerivativeChain (V ∘ orderedQ m n) L.coordinates x k h := by
  rw [← localLift_scalar_second_fderiv B V m n L x hx hV]
  exact localLift_scalar_second_fderiv_symmetric B V m n L x hx hV h k

/-- Any two admissible local presentations give the same final bilinear form,
even with different finite and essential coordinate counts. -/
theorem localLift_scalar_second_derivative_independent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ)
    (m n m' n' : ℕ) (L : LocalC2DiagramLift B m n)
    (L' : LocalC2DiagramLift B m' n') (x : E)
    (hx : x ∈ L.carrier) (hx' : x ∈ L'.carrier)
    (hV : C2ThroughAllRepresentatives V (B x)) :
    secondDerivativeChain (V ∘ orderedQ m n) L.coordinates x =
      secondDerivativeChain (V ∘ orderedQ m' n') L'.coordinates x := by
  rw [← localLift_scalar_second_fderiv B V m n L x hx hV,
    ← localLift_scalar_second_fderiv B V m' n' L' x hx' hV]

end TDA.Persistence
