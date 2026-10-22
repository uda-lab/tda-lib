import TDA.Persistence.SublevelLossHessianExamples

/-!
# Second-order presentation changes and insufficient regularity

A nonlinear singleton filtration admits different-dimensional presentations
with two unequal moving diagonal pairs and a nontrivial permutation of their labels.
Additional two-essential-path examples exercise essential relabeling. The examples
identify final scalar second derivatives without identifying ambient coefficient arrays.
-/

namespace TDA.Persistence

/-- Two essential births which remain unequal at every parameter. -/
def quadraticEssentialCoordinates (t : ℝ) : DiagramCoordinates 0 2 :=
  (Fin.elim0, ![t ^ 2, 1 + t ^ 2])

/-- Swap the two essential labels. -/
def swappedQuadraticEssentialCoordinates (t : ℝ) : DiagramCoordinates 0 2 :=
  (Fin.elim0, (quadraticEssentialCoordinates t).2 ∘ Equiv.swap 0 1)

/-- A redundant diagonal pair moves cubically while the essential labels are swapped. -/
def paddedQuadraticEssentialCoordinates (t : ℝ) : DiagramCoordinates 1 2 :=
  (fun _ => (t ^ 3, t ^ 3), (swappedQuadraticEssentialCoordinates t).2)

/-- The diagram family represented by the two nonlinear essential births. -/
noncomputable def quadraticEssentialDiagram (t : ℝ) : Diagram ℝ :=
  orderedQ 0 2 (quadraticEssentialCoordinates t)

/-- Relabeling genuinely changes the ordered coordinates. -/
theorem quadraticEssentialCoordinates_swap_nontrivial (t : ℝ) :
    quadraticEssentialCoordinates t ≠ swappedQuadraticEssentialCoordinates t := by
  intro h
  have hzero := congrArg (fun z : DiagramCoordinates 0 2 => z.2 0) h
  simp [quadraticEssentialCoordinates, swappedQuadraticEssentialCoordinates] at hzero

/-- The swapped paths represent the same diagram on the whole parameter space. -/
theorem swappedQuadraticEssentialCoordinates_factorization (t : ℝ) :
    orderedQ 0 2 (swappedQuadraticEssentialCoordinates t) = quadraticEssentialDiagram t := by
  simpa [swappedQuadraticEssentialCoordinates, quadraticEssentialCoordinates,
    quadraticEssentialDiagram] using orderedQ_perm 0 2 (Equiv.refl _) (Equiv.swap 0 1)
      (quadraticEssentialCoordinates t).1 (quadraticEssentialCoordinates t).2

/-- Removing a cubically moving diagonal pair gives the original diagram. -/
theorem paddedQuadraticEssentialCoordinates_factorization (t : ℝ) :
    orderedQ 1 2 (paddedQuadraticEssentialCoordinates t) = quadraticEssentialDiagram t := by
  rw [← swappedQuadraticEssentialCoordinates_factorization t]
  apply Diagram.ext
  simp [orderedQ, paddedQuadraticEssentialCoordinates, swappedQuadraticEssentialCoordinates]

private theorem quadraticEssentialCoordinates_contDiff :
    ContDiff ℝ 2 quadraticEssentialCoordinates := by
  apply ContDiff.prodMk
  · exact contDiff_const
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop

private theorem swappedQuadraticEssentialCoordinates_contDiff :
    ContDiff ℝ 2 swappedQuadraticEssentialCoordinates := by
  apply ContDiff.prodMk
  · exact contDiff_const
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [quadraticEssentialCoordinates] <;> fun_prop

private theorem paddedQuadraticEssentialCoordinates_contDiff :
    ContDiff ℝ 2 paddedQuadraticEssentialCoordinates := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fun_prop
  · exact contDiff_snd.comp swappedQuadraticEssentialCoordinates_contDiff

/-- The original two-birth presentation is globally C². -/
def quadraticEssentialLift : LocalC2DiagramLift quadraticEssentialDiagram 0 2 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := quadraticEssentialCoordinates
  factorization := by intro t _; rfl
  smooth := (quadraticEssentialCoordinates_contDiff.of_le (by norm_num)).contDiffOn
  smooth_two := quadraticEssentialCoordinates_contDiff.contDiffOn

/-- The genuinely relabeled presentation is globally C². -/
def swappedQuadraticEssentialLift : LocalC2DiagramLift quadraticEssentialDiagram 0 2 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := swappedQuadraticEssentialCoordinates
  factorization := by intro t _; exact (swappedQuadraticEssentialCoordinates_factorization t).symm
  smooth := (swappedQuadraticEssentialCoordinates_contDiff.of_le (by norm_num)).contDiffOn
  smooth_two := swappedQuadraticEssentialCoordinates_contDiff.contDiffOn

/-- The presentation of different dimension with a moving diagonal pair is globally C². -/
def paddedQuadraticEssentialLift : LocalC2DiagramLift quadraticEssentialDiagram 1 2 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := paddedQuadraticEssentialCoordinates
  factorization := by intro t _; exact (paddedQuadraticEssentialCoordinates_factorization t).symm
  smooth := (paddedQuadraticEssentialCoordinates_contDiff.of_le (by norm_num)).contDiffOn
  smooth_two := paddedQuadraticEssentialCoordinates_contDiff.contDiffOn

/-- The scalar loss is a nonconstant quadratic polynomial. -/
theorem quadraticEssentialDiagram_scalar_loss (t : ℝ) :
    essentialBirthSum (quadraticEssentialDiagram t) = 1 + 2 * t ^ 2 := by
  simp [quadraticEssentialDiagram, essentialBirthSum_orderedQ,
    quadraticEssentialCoordinates, Fin.sum_univ_two]
  ring

private theorem quadraticEssentialDiagram_scalar_fderiv (x : ℝ) :
    fderiv ℝ (essentialBirthSum ∘ quadraticEssentialDiagram) x =
      (4 * x) • ContinuousLinearMap.id ℝ ℝ := by
  have hf : (essentialBirthSum ∘ quadraticEssentialDiagram) =
      (fun t : ℝ => 1 + 2 * t ^ 2) := by
    funext t
    exact quadraticEssentialDiagram_scalar_loss t
  rw [hf]
  have hd := ((squareLinear_hasFDerivAt (ContinuousLinearMap.id ℝ ℝ) x).const_mul 2).const_add 1
  simpa only [ContinuousLinearMap.id_apply, smul_smul,
    show (2 : ℝ) * (2 * x) = 4 * x by ring] using hd.fderiv

/-- The second derivative exists and is the bilinear map `(h,k) ↦ 4*h*k`. -/
theorem quadraticEssentialDiagram_scalar_hasFDerivAt_fderiv (x : ℝ) :
    HasFDerivAt (fderiv ℝ (essentialBirthSum ∘ quadraticEssentialDiagram))
      (((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ).smulRight
        (ContinuousLinearMap.id ℝ ℝ)) x := by
  have hf : fderiv ℝ (essentialBirthSum ∘ quadraticEssentialDiagram) =
      fun t => (4 * t) • ContinuousLinearMap.id ℝ ℝ :=
    funext quadraticEssentialDiagram_scalar_fderiv
  rw [hf]
  exact ((ContinuousLinearMap.id ℝ ℝ).hasFDerivAt.const_mul 4).smul_const
    (ContinuousLinearMap.id ℝ ℝ)

/-- The concrete second derivative is nonzero and independent of the parameter. -/
theorem quadraticEssentialDiagram_scalar_secondFDeriv_apply (x h k : ℝ) :
    fderiv ℝ (fderiv ℝ (essentialBirthSum ∘ quadraticEssentialDiagram)) x h k =
      4 * h * k := by
  rw [(quadraticEssentialDiagram_scalar_hasFDerivAt_fderiv x).fderiv]
  simp [ContinuousLinearMap.smulRight_apply, mul_assoc]

/-- A nontrivial swap preserves the final second derivative. -/
theorem quadraticEssentialLift_second_derivative_relabel (x : ℝ) :
    secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 2)
        quadraticEssentialLift.coordinates x =
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 2)
        swappedQuadraticEssentialLift.coordinates x := by
  exact localLift_scalar_second_derivative_independent quadraticEssentialDiagram
    essentialBirthSum 0 2 0 2 quadraticEssentialLift swappedQuadraticEssentialLift x
    (Set.mem_univ x) (Set.mem_univ x) (essentialBirthSum_c2_all _)

/-- Adding the moving diagonal pair changes the dimension and preserves the final
bilinear form. No ambient coefficient uniqueness is asserted. -/
theorem quadraticEssentialLift_second_derivative_padding (x : ℝ) :
    secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 2)
        quadraticEssentialLift.coordinates x =
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 1 2)
        paddedQuadraticEssentialLift.coordinates x := by
  exact localLift_scalar_second_derivative_independent quadraticEssentialDiagram
    essentialBirthSum 0 2 1 2 quadraticEssentialLift paddedQuadraticEssentialLift x
    (Set.mem_univ x) (Set.mem_univ x) (essentialBirthSum_c2_all _)

/-- Both the original and the padded presentations compute the concrete Hessian. -/
theorem quadraticEssentialLift_second_derivative_values (x h k : ℝ) :
    secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 2)
        quadraticEssentialLift.coordinates x h k = 4 * h * k ∧
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 1 2)
        paddedQuadraticEssentialLift.coordinates x h k = 4 * h * k := by
  have hv := localLift_scalar_second_fderiv quadraticEssentialDiagram essentialBirthSum
    0 2 quadraticEssentialLift x (Set.mem_univ x) (essentialBirthSum_c2_all _)
  have hvalue : secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 2)
      quadraticEssentialLift.coordinates x h k = 4 * h * k := by
    rw [← hv]
    exact quadraticEssentialDiagram_scalar_secondFDeriv_apply x h k
  exact ⟨hvalue, by rw [← quadraticEssentialLift_second_derivative_padding x]; exact hvalue⟩

/-- A singleton filtration with nonlinear face value `1 + 2*t²`. -/
def quadraticSingletonPresentationFilter (t : ℝ) :=
  Examples.singletonFilter (1 + 2 * t ^ 2)

/-- The degree-zero persistence diagram of this singleton family. -/
noncomputable def sublevelQuadraticSingletonDiagram (t : ℝ) : Diagram ℝ :=
  dgm (ZMod 2) (quadraticSingletonPresentationFilter t) 0

/-- The minimal presentation retains the unique essential birth. -/
def sublevelQuadraticSingletonCoordinates (t : ℝ) : DiagramCoordinates 0 1 :=
  (Fin.elim0, fun _ => 1 + 2 * t ^ 2)

/-- Two unequal redundant diagonal pairs move cubically in a larger presentation. -/
def paddedSublevelQuadraticSingletonCoordinates (t : ℝ) : DiagramCoordinates 2 1 :=
  (![(t ^ 3, t ^ 3), (1 + t ^ 3, 1 + t ^ 3)],
    (sublevelQuadraticSingletonCoordinates t).2)

/-- Swap the two unequal diagonal-pair labels in the family's padded lift. -/
def swappedSublevelQuadraticSingletonCoordinates (t : ℝ) : DiagramCoordinates 2 1 :=
  ((paddedSublevelQuadraticSingletonCoordinates t).1 ∘ Equiv.swap 0 1,
    (paddedSublevelQuadraticSingletonCoordinates t).2)

/-- The minimal coordinates factor the diagram, using singleton homology. -/
theorem sublevelQuadraticSingletonCoordinates_factorization (t : ℝ) :
    orderedQ 0 1 (sublevelQuadraticSingletonCoordinates t) =
      sublevelQuadraticSingletonDiagram t := by
  apply Diagram.ext
  rw [sublevelQuadraticSingletonDiagram, quadraticSingletonPresentationFilter,
    Examples.singleton_points]
  simp [orderedQ, sublevelQuadraticSingletonCoordinates]

/-- The full two-pair padded coordinates still factor the diagram. -/
theorem paddedSublevelQuadraticSingletonCoordinates_factorization (t : ℝ) :
    orderedQ 2 1 (paddedSublevelQuadraticSingletonCoordinates t) =
      sublevelQuadraticSingletonDiagram t := by
  rw [← sublevelQuadraticSingletonCoordinates_factorization t]
  apply Diagram.ext
  simp [orderedQ, paddedSublevelQuadraticSingletonCoordinates, sublevelQuadraticSingletonCoordinates]

/-- Relabeling the padded finite coordinates preserves the diagram. -/
theorem swappedSublevelQuadraticSingletonCoordinates_factorization (t : ℝ) :
    orderedQ 2 1 (swappedSublevelQuadraticSingletonCoordinates t) =
      sublevelQuadraticSingletonDiagram t := by
  rw [← paddedSublevelQuadraticSingletonCoordinates_factorization t]
  simpa [swappedSublevelQuadraticSingletonCoordinates] using
    orderedQ_perm 2 1 (Equiv.swap 0 1) (Equiv.refl _)
      (paddedSublevelQuadraticSingletonCoordinates t).1
      (paddedSublevelQuadraticSingletonCoordinates t).2

/-- This finite-pair relabeling is nontrivial at every parameter. -/
theorem sublevelQuadraticSingletonCoordinates_swap_nontrivial (t : ℝ) :
    paddedSublevelQuadraticSingletonCoordinates t ≠
      swappedSublevelQuadraticSingletonCoordinates t := by
  intro h
  have hzero := congrArg (fun z : DiagramCoordinates 2 1 => (z.1 0).1) h
  simp [paddedSublevelQuadraticSingletonCoordinates,
    swappedSublevelQuadraticSingletonCoordinates] at hzero

private theorem sublevelQuadraticSingletonCoordinates_contDiff :
    ContDiff ℝ 2 sublevelQuadraticSingletonCoordinates := by
  apply ContDiff.prodMk
  · exact contDiff_const
  · apply contDiff_pi.mpr
    intro i
    fun_prop

private theorem paddedSublevelQuadraticSingletonCoordinates_contDiff :
    ContDiff ℝ 2 paddedSublevelQuadraticSingletonCoordinates := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  · exact contDiff_snd.comp sublevelQuadraticSingletonCoordinates_contDiff

private theorem swappedSublevelQuadraticSingletonCoordinates_contDiff :
    ContDiff ℝ 2 swappedSublevelQuadraticSingletonCoordinates := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [paddedSublevelQuadraticSingletonCoordinates] <;> fun_prop
  · exact contDiff_snd.comp paddedSublevelQuadraticSingletonCoordinates_contDiff

/-- A globally C² minimal lift of the singleton family. -/
def sublevelQuadraticSingletonLift : LocalC2DiagramLift sublevelQuadraticSingletonDiagram 0 1 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := sublevelQuadraticSingletonCoordinates
  factorization := by intro t _; exact (sublevelQuadraticSingletonCoordinates_factorization t).symm
  smooth := (sublevelQuadraticSingletonCoordinates_contDiff.of_le (by norm_num)).contDiffOn
  smooth_two := sublevelQuadraticSingletonCoordinates_contDiff.contDiffOn

/-- A globally C² lift of the same family with two redundant diagonal pairs. -/
def paddedSublevelQuadraticSingletonLift :
    LocalC2DiagramLift sublevelQuadraticSingletonDiagram 2 1 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := paddedSublevelQuadraticSingletonCoordinates
  factorization := by
    intro t _
    exact (paddedSublevelQuadraticSingletonCoordinates_factorization t).symm
  smooth := (paddedSublevelQuadraticSingletonCoordinates_contDiff.of_le (by norm_num)).contDiffOn
  smooth_two := paddedSublevelQuadraticSingletonCoordinates_contDiff.contDiffOn

/-- A globally C² lift with a nontrivial permutation of the padded finite labels. -/
def swappedSublevelQuadraticSingletonLift :
    LocalC2DiagramLift sublevelQuadraticSingletonDiagram 2 1 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := swappedSublevelQuadraticSingletonCoordinates
  factorization := by
    intro t _
    exact (swappedSublevelQuadraticSingletonCoordinates_factorization t).symm
  smooth := (swappedSublevelQuadraticSingletonCoordinates_contDiff.of_le (by norm_num)).contDiffOn
  smooth_two := swappedSublevelQuadraticSingletonCoordinates_contDiff.contDiffOn

/-- The loss of the singleton family is the same nonconstant quadratic polynomial. -/
theorem sublevelQuadraticSingletonDiagram_scalar_loss (t : ℝ) :
    essentialBirthSum (sublevelQuadraticSingletonDiagram t) = 1 + 2 * t ^ 2 :=
  singleton_essential_loss _

private theorem sublevelQuadraticSingletonDiagram_scalar_eq :
    essentialBirthSum ∘ sublevelQuadraticSingletonDiagram =
      essentialBirthSum ∘ quadraticEssentialDiagram := by
  funext t
  rw [Function.comp_apply, Function.comp_apply,
    sublevelQuadraticSingletonDiagram_scalar_loss, quadraticEssentialDiagram_scalar_loss]

/-- The derivative map of the scalar loss has the genuine derivative `4*h*k`. -/
theorem sublevelQuadraticSingletonDiagram_scalar_hasFDerivAt_fderiv (x : ℝ) :
    HasFDerivAt (fderiv ℝ (essentialBirthSum ∘ sublevelQuadraticSingletonDiagram))
      (((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ).smulRight
        (ContinuousLinearMap.id ℝ ℝ)) x := by
  rw [sublevelQuadraticSingletonDiagram_scalar_eq]
  exact quadraticEssentialDiagram_scalar_hasFDerivAt_fderiv x

/-- The singleton scalar second derivative is `4*h*k`. -/
theorem sublevelQuadraticSingletonDiagram_scalar_secondFDeriv_apply (x h k : ℝ) :
    fderiv ℝ (fderiv ℝ (essentialBirthSum ∘ sublevelQuadraticSingletonDiagram)) x h k =
      4 * h * k := by
  rw [sublevelQuadraticSingletonDiagram_scalar_eq]
  exact quadraticEssentialDiagram_scalar_secondFDeriv_apply x h k

/-- Nontrivial finite-pair relabeling preserves the final scalar bilinear form. -/
theorem sublevelQuadraticSingletonLift_second_derivative_relabel (x : ℝ) :
    secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        paddedSublevelQuadraticSingletonLift.coordinates x =
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        swappedSublevelQuadraticSingletonLift.coordinates x := by
  exact localLift_scalar_second_derivative_independent sublevelQuadraticSingletonDiagram
    essentialBirthSum 2 1 2 1 paddedSublevelQuadraticSingletonLift
    swappedSublevelQuadraticSingletonLift x (Set.mem_univ x) (Set.mem_univ x)
    (essentialBirthSum_c2_all _)

/-- Redundant diagonal coordinates change the dimension from `(0,1)` to `(2,1)`
while preserving the final scalar bilinear form. -/
theorem sublevelQuadraticSingletonLift_second_derivative_padding (x : ℝ) :
    secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 1)
        sublevelQuadraticSingletonLift.coordinates x =
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        paddedSublevelQuadraticSingletonLift.coordinates x := by
  exact localLift_scalar_second_derivative_independent sublevelQuadraticSingletonDiagram
    essentialBirthSum 0 1 2 1 sublevelQuadraticSingletonLift
    paddedSublevelQuadraticSingletonLift x (Set.mem_univ x) (Set.mem_univ x)
    (essentialBirthSum_c2_all _)

/-- All three presentations of the family compute the concrete Hessian `4*h*k`.
Only the final bilinear forms are identified, without ambient coefficient uniqueness. -/
theorem sublevelQuadraticSingletonLift_second_derivative_values (x h k : ℝ) :
    secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 1)
        sublevelQuadraticSingletonLift.coordinates x h k = 4 * h * k ∧
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        paddedSublevelQuadraticSingletonLift.coordinates x h k = 4 * h * k ∧
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        swappedSublevelQuadraticSingletonLift.coordinates x h k = 4 * h * k := by
  have hv := localLift_scalar_second_fderiv sublevelQuadraticSingletonDiagram essentialBirthSum
    0 1 sublevelQuadraticSingletonLift x (Set.mem_univ x) (essentialBirthSum_c2_all _)
  have hvalue : secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 1)
      sublevelQuadraticSingletonLift.coordinates x h k = 4 * h * k := by
    rw [← hv]
    exact sublevelQuadraticSingletonDiagram_scalar_secondFDeriv_apply x h k
  have hpadded : secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
      paddedSublevelQuadraticSingletonLift.coordinates x h k = 4 * h * k := by
    rw [← sublevelQuadraticSingletonLift_second_derivative_padding x]
    exact hvalue
  exact ⟨hvalue, hpadded, by
    rw [← sublevelQuadraticSingletonLift_second_derivative_relabel x]
    exact hpadded⟩

/-- The empty complex has its unique real filtration. -/
def emptyComplexFilter :
    TDA.Filtration.FilterFunction (⊥ : PreAbstractSimplicialComplex (Fin 0)) ℝ where
  value := fun s => ((TDA.Filtration.mem_bot_iff s.val).mp s.property).elim
  mono := by
    intro τ σ _
    exact ((TDA.Filtration.mem_bot_iff τ.val).mp τ.property).elim

/-- The persistence construction on the empty complex gives the empty diagram. -/
theorem emptyComplexFilter_diagram (p : ℕ) :
    dgm (ZMod 2) emptyComplexFilter p = orderedQ 0 0 (Fin.elim0, Fin.elim0) := by
  have hc : emptyComplexFilter.criticalValues.card = 0 := by
    rw [(emptyComplexFilter.criticalValues_eq_empty_iff).2 rfl]
    rfl
  let : IsEmpty (Fin emptyComplexFilter.criticalValues.card) := by
    rw [hc]
    infer_instance
  apply Diagram.ext
  simp [dgm, gradeHomologyBarcode, rankBarcode, ofIndexBars, orderedQ]

/-- Any scalar loss on the empty family is constant; no regularity of the
loss on other representatives is needed for this particular scalar function. -/
theorem emptyComplexFilter_scalar_loss (V : Diagram ℝ → ℝ) (p : ℕ) :
    V (dgm (ZMod 2) emptyComplexFilter p) =
      V (orderedQ 0 0 (Fin.elim0, Fin.elim0)) := by
  rw [emptyComplexFilter_diagram]

/-- The empty family's scalar derivative map has derivative zero. -/
theorem emptyComplexFilter_scalar_hasFDerivAt_fderiv
    (V : Diagram ℝ → ℝ) (p : ℕ) (x : ℝ) :
    HasFDerivAt (fderiv ℝ (fun _ : ℝ => V (dgm (ZMod 2) emptyComplexFilter p)))
      (0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) x := by
  have hdf : fderiv ℝ (fun _ : ℝ => V (dgm (ZMod 2) emptyComplexFilter p)) =
      (fun _ : ℝ => (0 : ℝ →L[ℝ] ℝ)) := by
    funext t
    exact fderiv_const_apply (𝕜 := ℝ) _
  rw [hdf]
  exact hasFDerivAt_const _ _

/-- The second derivative of every scalar loss on the empty family is zero. -/
theorem emptyComplexFilter_scalar_second_fderiv (V : Diagram ℝ → ℝ) (p : ℕ) (x : ℝ) :
    fderiv ℝ (fderiv ℝ (fun _ : ℝ => V (dgm (ZMod 2) emptyComplexFilter p))) x = 0 :=
  (emptyComplexFilter_scalar_hasFDerivAt_fderiv V p x).fderiv

/-- The absolute endpoint loss fails C² through all representatives of the empty
diagram, because that condition would imply its already-disproved C¹ condition. -/
theorem absoluteFiniteEndpointDifference_not_c2_empty :
    ¬ C2ThroughAllRepresentatives absoluteFiniteEndpointDifference
      (orderedQ 0 0 (Fin.elim0, Fin.elim0)) := by
  intro h
  exact absoluteFiniteEndpointDifference_not_c1_empty h.c1

end TDA.Persistence
