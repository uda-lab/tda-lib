import TDA.Persistence.DiagramSecondOrderCalculus

/-!
# Regularity through ordered diagram presentations

All `ContDiff` assertions concern Euclidean coordinate maps or scalar pullbacks.
The diagram type has no topology or derivative here. In particular, order zero
means continuity. The index is governed solely by mathlib's `ContDiff` predicate.
-/

namespace TDA.Persistence
open scoped ContDiff

/-- A `Cʳ` factorization on the stated open carrier. -/
structure LocalCrDiagramLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ∞ω) (B : E → Diagram ℝ) (m n : ℕ) where
  carrier : Set E
  isOpen_carrier : IsOpen carrier
  coordinates : E → DiagramCoordinates m n
  factorization : ∀ x ∈ carrier, B x = orderedQ m n (coordinates x)
  regular : ContDiffOn ℝ r coordinates carrier

/-- Existence of a `Cʳ` local lift at a point, including membership in its carrier. -/
def DiagramContDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ∞ω) (B : E → Diagram ℝ) (x₀ : E) : Prop :=
  ∃ m n, ∃ L : LocalCrDiagramLift r B m n, x₀ ∈ L.carrier

/-- Scalar `Cʳ` regularity on an open neighborhood of every ordered representative. -/
def CrThroughAllRepresentatives (r : ℕ∞ω) (V : Diagram ℝ → ℝ)
    (D : Diagram ℝ) : Prop :=
  ∀ (m n : ℕ) (z : DiagramCoordinates m n), orderedQ m n z = D →
    ∃ W : Set (DiagramCoordinates m n), IsOpen W ∧ z ∈ W ∧
      ContDiffOn ℝ r (V ∘ orderedQ m n) W

theorem CrThroughAllRepresentatives.of_le {r r' : ℕ∞ω} (h : r' ≤ r)
    {V : Diagram ℝ → ℝ} {D : Diagram ℝ}
    (hV : CrThroughAllRepresentatives r V D) :
    CrThroughAllRepresentatives r' V D := by
  intro m n z hz
  obtain ⟨W, hW, hzW, hs⟩ := hV m n z hz
  exact ⟨W, hW, hzW, hs.of_le h⟩

def LocalCrDiagramLift.of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r r' : ℕ∞ω} (h : r' ≤ r) {B : E → Diagram ℝ} {m n : ℕ}
    (L : LocalCrDiagramLift r B m n) : LocalCrDiagramLift r' B m n where
  carrier := L.carrier
  isOpen_carrier := L.isOpen_carrier
  coordinates := L.coordinates
  factorization := L.factorization
  regular := L.regular.of_le h

theorem DiagramContDiffAt.of_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r r' : ℕ∞ω} (h : r' ≤ r) {B : E → Diagram ℝ} {x : E}
    (hB : DiagramContDiffAt r B x) : DiagramContDiffAt r' B x := by
  obtain ⟨m, n, L, hx⟩ := hB
  exact ⟨m, n, L.of_le h, hx⟩

/-- The loss is `Cʳ` near the point, using the representative selected by the lift. -/
theorem localLift_scalar_cr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ∞ω) (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalCrDiagramLift r B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : CrThroughAllRepresentatives r V (B x)) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ L.carrier ∧
      ContDiffOn ℝ r (V ∘ B) U := by
  obtain ⟨W, hWopen, hzW, hW⟩ := hV m n (L.coordinates x)
    (L.factorization x hx).symm
  let U := L.carrier ∩ L.coordinates ⁻¹' W
  have hUopen : IsOpen U :=
    L.regular.continuousOn.isOpen_inter_preimage L.isOpen_carrier hWopen
  have hcomp : ContDiffOn ℝ r ((V ∘ orderedQ m n) ∘ L.coordinates) U :=
    hW.comp (L.regular.mono Set.inter_subset_left) Set.inter_subset_right
  refine ⟨U, hUopen, ⟨hx, hzW⟩, Set.inter_subset_left, ?_⟩
  apply hcomp.congr
  intro y hy
  simp only [Function.comp_apply]
  rw [L.factorization y hy.1]

theorem CrThroughAllRepresentatives.one_iff {V : Diagram ℝ → ℝ} {D : Diagram ℝ} :
    CrThroughAllRepresentatives 1 V D ↔ C1ThroughAllRepresentatives V D := Iff.rfl

theorem CrThroughAllRepresentatives.two_iff {V : Diagram ℝ → ℝ} {D : Diagram ℝ} :
    CrThroughAllRepresentatives 2 V D ↔ C2ThroughAllRepresentatives V D := Iff.rfl

/-- The old `C¹` lift embeds without changing its carrier or coordinates. -/
def LocalDiagramLift.toCr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E → Diagram ℝ} {m n : ℕ} (L : LocalDiagramLift B m n) :
    LocalCrDiagramLift 1 B m n where
  carrier := L.carrier
  isOpen_carrier := L.isOpen_carrier
  coordinates := L.coordinates
  factorization := L.factorization
  regular := L.smooth

/-- The old `C²` lift embeds without changing its carrier or coordinates. -/
def LocalC2DiagramLift.toCr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E → Diagram ℝ} {m n : ℕ} (L : LocalC2DiagramLift B m n) :
    LocalCrDiagramLift 2 B m n where
  carrier := L.carrier
  isOpen_carrier := L.isOpen_carrier
  coordinates := L.coordinates
  factorization := L.factorization
  regular := L.smooth_two

/-- Recover the unchanged old `C¹` lift at index one. -/
def LocalCrDiagramLift.toC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E → Diagram ℝ} {m n : ℕ} (L : LocalCrDiagramLift 1 B m n) :
    LocalDiagramLift B m n where
  carrier := L.carrier
  isOpen_carrier := L.isOpen_carrier
  coordinates := L.coordinates
  factorization := L.factorization
  smooth := L.regular

/-- Recover both old fields of a `C²` lift at index two. -/
def LocalCrDiagramLift.toC2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E → Diagram ℝ} {m n : ℕ} (L : LocalCrDiagramLift 2 B m n) :
    LocalC2DiagramLift B m n where
  carrier := L.carrier
  isOpen_carrier := L.isOpen_carrier
  coordinates := L.coordinates
  factorization := L.factorization
  smooth := L.regular.of_le (by norm_num)
  smooth_two := L.regular

/-- At order one the general scalar conclusion is supplied by the unchanged
first-order lift theorem. -/
theorem localLift_scalar_cr_one {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalCrDiagramLift 1 B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : CrThroughAllRepresentatives 1 V (B x)) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ L.carrier ∧
      ContDiffOn ℝ 1 (V ∘ B) U :=
  localLift_scalar_c1 B V m n L.toC1 x hx hV

/-- At order two the general scalar conclusion is supplied by the unchanged
second-order lift theorem. -/
theorem localLift_scalar_cr_two {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalCrDiagramLift 2 B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : CrThroughAllRepresentatives 2 V (B x)) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ L.carrier ∧
      ContDiffOn ℝ 2 (V ∘ B) U :=
  localLift_scalar_c2 B V m n L.toC2 x hx hV

/-- Index zero yields ordinary continuity of the scalar pullback. -/
theorem localLift_scalar_continuousOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → Diagram ℝ) (V : Diagram ℝ → ℝ) (m n : ℕ)
    (L : LocalCrDiagramLift 0 B m n) (x : E) (hx : x ∈ L.carrier)
    (hV : CrThroughAllRepresentatives 0 V (B x)) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ L.carrier ∧
      ContinuousOn (V ∘ B) U := by
  obtain ⟨U, hU, hxU, hsub, hs⟩ := localLift_scalar_cr 0 B V m n L x hx hV
  exact ⟨U, hU, hxU, hsub, hs.continuousOn⟩

/-- Insert auxiliary diagonal values after the retained finite slots. This is
a continuous linear map of finite-dimensional coordinate spaces. -/
noncomputable def diagonalInsertionLinear (m t n : ℕ) :
    (DiagramCoordinates m n × (Fin t → ℝ)) →ₗ[ℝ] DiagramCoordinates (m + t) n where
    toFun := fun z =>
      (Fin.append z.1.1 (fun i => (z.2 i, z.2 i)), z.1.2)
    map_add' := by
      intro x y
      ext i <;> simp [Fin.append]
      all_goals cases i using Fin.addCases <;> simp
    map_smul' := by
      intro a x
      ext i <;> simp [Fin.append]
      all_goals cases i using Fin.addCases <;> simp

noncomputable def diagonalInsertion (m t n : ℕ) :
    (DiagramCoordinates m n × (Fin t → ℝ)) →L[ℝ] DiagramCoordinates (m + t) n :=
  ⟨diagonalInsertionLinear m t n,
    (diagonalInsertionLinear m t n).continuous_of_finiteDimensional⟩

/-- Pulling an ordered diagram back along diagonal insertion deletes exactly
the inserted slots, regardless of their auxiliary real values. -/
theorem orderedQ_diagonalInsertion (m t n : ℕ)
    (z : DiagramCoordinates m n × (Fin t → ℝ)) :
    orderedQ (m + t) n (diagonalInsertion m t n z) = orderedQ m n z.1 := by
  change orderedQ (m + t) n
    (Fin.append z.1.1 (fun i => (z.2 i, z.2 i)), z.1.2) = orderedQ m n z.1
  apply (orderedQ_eq_iff _ _ _ _ _ _).mpr
  constructor
  · simp only [List.ofFn_fin_append]
    simp [List.ofFn_eq_map, List.filter_map, Function.comp_def]
  · rfl

/-- Regularity on the diagonal subspace follows from regularity of the
reduced pullback. This makes no assertion on an ambient open neighborhood of
the full representative. -/
theorem contDiffOn_diagonalInsertion (r : ℕ∞ω) (m t n : ℕ)
    (V : Diagram ℝ → ℝ) (W : Set (DiagramCoordinates m n))
    (hV : ContDiffOn ℝ r (V ∘ orderedQ m n) W) :
    ContDiffOn ℝ r (V ∘ orderedQ (m + t) n ∘ diagonalInsertion m t n)
      ((fun z : DiagramCoordinates m n × (Fin t → ℝ) => z.1) ⁻¹' W) := by
  have hp : ContDiffOn ℝ r (fun z : DiagramCoordinates m n × (Fin t → ℝ) => z.1)
      ((fun z : DiagramCoordinates m n × (Fin t → ℝ) => z.1) ⁻¹' W) :=
    contDiff_fst.contDiffOn
  have hc := hV.comp hp (fun _ hz => hz)
  convert hc using 1
  ext z
  simp [Function.comp_def, orderedQ_diagonalInsertion]

end TDA.Persistence
