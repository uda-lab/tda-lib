import TDA.Topology.SingularMayerVietoris
import TDA.Topology.QuasiIsoOfIterate
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Small chains of two rays, the flip sign over `ℚ`, and contractible complexes

The open rays `(-∞, 1)` and `(0, ∞)` cover `ℝ`. Constant simplices are small, and the point `2`
lies in the second ray only. The affine segment from `2` to `-1` is a singular `1`-simplex that
is not small, so small chains are a proper subcomplex of all singular chains even for an open
cover. The small chains still fit into the short exact sequence over `ℚ`. Over `ℚ`, exchanging
the two pieces of any bicartesian square changes every nonzero connecting map. Finally, the
iteration criterion shows that a complex contractible by a homotopy `0 ≃ 𝟙` has the homology of
the zero complex.
-/

namespace TDA.Topology.SingularMayerVietorisExamples

open CategoryTheory Limits AlgebraicTopology Opposite HomologicalComplex ZeroObject
open scoped Simplicial

noncomputable section

/-- The real line as a topological space (fixture-local name). -/
abbrev lineSpace : TopCat.{0} := TopCat.of ℝ

/-- The open ray `(-∞, 1)`. -/
def lowerRay : Set lineSpace := Set.Iio (1 : ℝ)

/-- The open ray `(0, ∞)`. -/
def upperRay : Set lineSpace := Set.Ioi (0 : ℝ)

/-- The constant `0`-simplex at a point of the real line. -/
def pointSimplex (p : ℝ) : (TopCat.toSSet.obj lineSpace).obj (op ⦋0⦌) :=
  (lineSpace.toSSetObjEquiv (op ⦋0⦌)).symm (ContinuousMap.const _ p)

/-- The affine `1`-simplex `x ↦ 3 x₀ - 1`, from `2` at the vertex `0` to `-1` at the vertex
`1`. -/
def segmentSimplex : (TopCat.toSSet.obj lineSpace).obj (op ⦋1⦌) :=
  (lineSpace.toSSetObjEquiv (op ⦋1⦌)).symm
    ⟨fun x => 3 * x.weights 0 - 1,
      ((Convexity.StdSimplex.continuous_weights_apply ℝ _).const_mul 3).sub continuous_const⟩

private theorem range_pointSimplex (p : ℝ) :
    Set.range (lineSpace.toSSetObjEquiv (op ⦋0⦌) (pointSimplex p)) = {p} := by
  rw [pointSimplex, Equiv.apply_symm_apply]
  exact Set.range_const

/-- The point `1/2` lies in both rays, so its constant simplex lies in the intersection. -/
theorem pointSimplex_half_mem_inter :
    pointSimplex (1 / 2) ∈ (simplicesIn (lowerRay ∩ upperRay)).obj (op ⦋0⦌) := by
  rw [mem_simplicesIn_iff, range_pointSimplex, Set.singleton_subset_iff]
  constructor <;> norm_num [lowerRay, upperRay]

/-- The point `2` lies in the upper ray only: its constant simplex is small but does not lie in
the lower ray. -/
theorem pointSimplex_two_mem_small_not_mem_lower :
    pointSimplex 2 ∈ (smallSimplices lowerRay upperRay).obj (op ⦋0⦌) ∧
      pointSimplex 2 ∉ (simplicesIn lowerRay).obj (op ⦋0⦌) := by
  rw [mem_smallSimplices_iff, mem_simplicesIn_iff, range_pointSimplex]
  simp only [Set.singleton_subset_iff]
  norm_num [lowerRay, upperRay]

/-- The segment from `2` to `-1` is not small for the two rays, although the rays form an open
cover of the line. -/
theorem segmentSimplex_not_mem_smallSimplices :
    segmentSimplex ∉ (smallSimplices lowerRay upperRay).obj (op ⦋1⦌) := by
  rw [mem_smallSimplices_iff, segmentSimplex, Equiv.apply_symm_apply]
  rintro (h | h)
  · have := h ⟨Convexity.StdSimplex.single 0, rfl⟩
    norm_num [lowerRay] at this
  · have := h ⟨Convexity.StdSimplex.single 1, rfl⟩
    norm_num [upperRay] at this

/-- The two rays cover the line. -/
theorem lowerRay_union_upperRay : lowerRay ∪ upperRay = Set.univ := by
  ext x
  simp only [lowerRay, upperRay, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_univ,
    iff_true]
  by_contra! h
  linarith [h.1, h.2]

/-- The Mayer–Vietoris sequence of small chains of the two rays over `ℚ` is short exact, with
first map `(inc, -inc)`. -/
theorem shortExact_rays :
    (mvShortComplex (isPushout_smallChains (ModuleCat.of ℚ ℚ) lowerRay upperRay)).ShortExact ∧
      (mvShortComplex (isPushout_smallChains (ModuleCat.of ℚ ℚ) lowerRay upperRay)).f =
        biprod.lift
          (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
            (bicartSq_simplicesIn lowerRay upperRay).le₁₂) (ModuleCat.of ℚ ℚ))
          (-SSet.chainComplexMap (SSet.Subcomplex.homOfLE
            (bicartSq_simplicesIn lowerRay upperRay).le₁₃) (ModuleCat.of ℚ ℚ)) :=
  ⟨shortExact_smallChains _ lowerRay upperRay, rfl⟩

/-- Over `ℚ`, a nonzero morphism differs from its negative. -/
theorem neg_ne_self_of_ne_zero {M N : ModuleCat.{0} ℚ} (φ : M ⟶ N) (hφ : φ ≠ 0) : -φ ≠ φ := by
  intro h
  apply hφ
  have h2 : (2 : ℚ) • φ = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel φ
  have := congrArg (fun ψ => (2 : ℚ)⁻¹ • ψ) h2
  simpa [smul_smul] using this

/-- **The flip sign over `ℚ`.** For any bicartesian square of subcomplexes, the connecting map of
the flipped square is the negative, so it differs from the original one whenever that is
nonzero. -/
theorem bicartδ_flip_ne {X : SSet.{0}} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) (n : ℕ)
    (hδ : bicartδ (ModuleCat.of ℚ ℚ) sq n ≠ 0) :
    bicartδ (ModuleCat.of ℚ ℚ) (bicartSq_flip sq) n = -bicartδ (ModuleCat.of ℚ ℚ) sq n ∧
      bicartδ (ModuleCat.of ℚ ℚ) (bicartSq_flip sq) n ≠ bicartδ (ModuleCat.of ℚ ℚ) sq n := by
  rw [bicartδ_flip _ sq]
  exact ⟨rfl, neg_ne_self_of_ne_zero _ hδ⟩

/-- **A contractible complex is acyclic**, by the iteration criterion applied to `S = 0` and
the zero subcomplex: the inclusion of the zero complex is a quasi-isomorphism. -/
theorem quasiIso_zero_of_homotopy {B : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (T : Homotopy (0 : B ⟶ B) (𝟙 B)) :
    QuasiIso (0 : (0 : ChainComplex (ModuleCat.{0} ℚ) ℕ) ⟶ B) := by
  have : Mono (0 : (0 : ChainComplex (ModuleCat.{0} ℚ) ℕ) ⟶ B) :=
    mono_of_source_iso_zero _ (Iso.refl _)
  refine quasiIso_of_iterate_mem 0 0 T (fun n a => ?_) (fun n m a => ?_) (fun n b => ⟨1, ?_⟩)
  · simp
  · simp
  · simp

end

end TDA.Topology.SingularMayerVietorisExamples
