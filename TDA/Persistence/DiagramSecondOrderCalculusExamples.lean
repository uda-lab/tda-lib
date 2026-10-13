import TDA.Persistence.ActualLossHessianExamples

/-!
# Second-order presentation changes and insufficient regularity

An actual nonlinear singleton filtration admits different-dimensional presentations
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

/-- An actual singleton filtration with nonlinear face value `1 + 2*t²`. -/
def quadraticSingletonPresentationFilter (t : ℝ) :=
  Examples.singletonFilter (1 + 2 * t ^ 2)

/-- The actual degree-zero persistence diagram of this singleton family. -/
noncomputable def actualQuadraticSingletonDiagram (t : ℝ) : Diagram ℝ :=
  dgm (ZMod 2) (quadraticSingletonPresentationFilter t) 0

/-- The minimal presentation retains the unique essential birth. -/
def actualQuadraticSingletonCoordinates (t : ℝ) : DiagramCoordinates 0 1 :=
  (Fin.elim0, fun _ => 1 + 2 * t ^ 2)

/-- Two unequal redundant diagonal pairs move cubically in a larger presentation. -/
def paddedActualQuadraticSingletonCoordinates (t : ℝ) : DiagramCoordinates 2 1 :=
  (![(t ^ 3, t ^ 3), (1 + t ^ 3, 1 + t ^ 3)],
    (actualQuadraticSingletonCoordinates t).2)

/-- Swap the two unequal diagonal-pair labels in the actual family's padded lift. -/
def swappedActualQuadraticSingletonCoordinates (t : ℝ) : DiagramCoordinates 2 1 :=
  ((paddedActualQuadraticSingletonCoordinates t).1 ∘ Equiv.swap 0 1,
    (paddedActualQuadraticSingletonCoordinates t).2)

/-- The minimal coordinates factor the actual diagram, using actual singleton homology. -/
theorem actualQuadraticSingletonCoordinates_factorization (t : ℝ) :
    orderedQ 0 1 (actualQuadraticSingletonCoordinates t) =
      actualQuadraticSingletonDiagram t := by
  apply Diagram.ext
  rw [actualQuadraticSingletonDiagram, quadraticSingletonPresentationFilter,
    Examples.singleton_points]
  simp [orderedQ, actualQuadraticSingletonCoordinates]

/-- The full two-pair padded coordinates still factor the actual diagram. -/
theorem paddedActualQuadraticSingletonCoordinates_factorization (t : ℝ) :
    orderedQ 2 1 (paddedActualQuadraticSingletonCoordinates t) =
      actualQuadraticSingletonDiagram t := by
  rw [← actualQuadraticSingletonCoordinates_factorization t]
  apply Diagram.ext
  simp [orderedQ, paddedActualQuadraticSingletonCoordinates, actualQuadraticSingletonCoordinates]

/-- Relabeling the padded finite coordinates preserves the actual diagram. -/
theorem swappedActualQuadraticSingletonCoordinates_factorization (t : ℝ) :
    orderedQ 2 1 (swappedActualQuadraticSingletonCoordinates t) =
      actualQuadraticSingletonDiagram t := by
  rw [← paddedActualQuadraticSingletonCoordinates_factorization t]
  simpa [swappedActualQuadraticSingletonCoordinates] using
    orderedQ_perm 2 1 (Equiv.swap 0 1) (Equiv.refl _)
      (paddedActualQuadraticSingletonCoordinates t).1
      (paddedActualQuadraticSingletonCoordinates t).2

/-- This finite-pair relabeling is nontrivial at every parameter. -/
theorem actualQuadraticSingletonCoordinates_swap_nontrivial (t : ℝ) :
    paddedActualQuadraticSingletonCoordinates t ≠
      swappedActualQuadraticSingletonCoordinates t := by
  intro h
  have hzero := congrArg (fun z : DiagramCoordinates 2 1 => (z.1 0).1) h
  simp [paddedActualQuadraticSingletonCoordinates,
    swappedActualQuadraticSingletonCoordinates] at hzero

private theorem actualQuadraticSingletonCoordinates_contDiff :
    ContDiff ℝ 2 actualQuadraticSingletonCoordinates := by
  apply ContDiff.prodMk
  · exact contDiff_const
  · apply contDiff_pi.mpr
    intro i
    fun_prop

private theorem paddedActualQuadraticSingletonCoordinates_contDiff :
    ContDiff ℝ 2 paddedActualQuadraticSingletonCoordinates := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  · exact contDiff_snd.comp actualQuadraticSingletonCoordinates_contDiff

private theorem swappedActualQuadraticSingletonCoordinates_contDiff :
    ContDiff ℝ 2 swappedActualQuadraticSingletonCoordinates := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [paddedActualQuadraticSingletonCoordinates] <;> fun_prop
  · exact contDiff_snd.comp paddedActualQuadraticSingletonCoordinates_contDiff

/-- A globally C² minimal lift of the actual singleton family. -/
def actualQuadraticSingletonLift : LocalC2DiagramLift actualQuadraticSingletonDiagram 0 1 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := actualQuadraticSingletonCoordinates
  factorization := by intro t _; exact (actualQuadraticSingletonCoordinates_factorization t).symm
  smooth := (actualQuadraticSingletonCoordinates_contDiff.of_le (by norm_num)).contDiffOn
  smooth_two := actualQuadraticSingletonCoordinates_contDiff.contDiffOn

/-- A globally C² lift of the same actual family with two redundant diagonal pairs. -/
def paddedActualQuadraticSingletonLift :
    LocalC2DiagramLift actualQuadraticSingletonDiagram 2 1 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := paddedActualQuadraticSingletonCoordinates
  factorization := by
    intro t _
    exact (paddedActualQuadraticSingletonCoordinates_factorization t).symm
  smooth := (paddedActualQuadraticSingletonCoordinates_contDiff.of_le (by norm_num)).contDiffOn
  smooth_two := paddedActualQuadraticSingletonCoordinates_contDiff.contDiffOn

/-- A globally C² lift with a nontrivial permutation of the padded finite labels. -/
def swappedActualQuadraticSingletonLift :
    LocalC2DiagramLift actualQuadraticSingletonDiagram 2 1 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := swappedActualQuadraticSingletonCoordinates
  factorization := by
    intro t _
    exact (swappedActualQuadraticSingletonCoordinates_factorization t).symm
  smooth := (swappedActualQuadraticSingletonCoordinates_contDiff.of_le (by norm_num)).contDiffOn
  smooth_two := swappedActualQuadraticSingletonCoordinates_contDiff.contDiffOn

/-- The loss of the actual singleton family is the same nonconstant quadratic polynomial. -/
theorem actualQuadraticSingletonDiagram_scalar_loss (t : ℝ) :
    essentialBirthSum (actualQuadraticSingletonDiagram t) = 1 + 2 * t ^ 2 :=
  singleton_essential_loss _

private theorem actualQuadraticSingletonDiagram_scalar_eq :
    essentialBirthSum ∘ actualQuadraticSingletonDiagram =
      essentialBirthSum ∘ quadraticEssentialDiagram := by
  funext t
  rw [Function.comp_apply, Function.comp_apply,
    actualQuadraticSingletonDiagram_scalar_loss, quadraticEssentialDiagram_scalar_loss]

/-- The derivative map of the actual scalar loss has the genuine derivative `4*h*k`. -/
theorem actualQuadraticSingletonDiagram_scalar_hasFDerivAt_fderiv (x : ℝ) :
    HasFDerivAt (fderiv ℝ (essentialBirthSum ∘ actualQuadraticSingletonDiagram))
      (((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ).smulRight
        (ContinuousLinearMap.id ℝ ℝ)) x := by
  rw [actualQuadraticSingletonDiagram_scalar_eq]
  exact quadraticEssentialDiagram_scalar_hasFDerivAt_fderiv x

/-- The actual singleton scalar second derivative is `4*h*k`. -/
theorem actualQuadraticSingletonDiagram_scalar_secondFDeriv_apply (x h k : ℝ) :
    fderiv ℝ (fderiv ℝ (essentialBirthSum ∘ actualQuadraticSingletonDiagram)) x h k =
      4 * h * k := by
  rw [actualQuadraticSingletonDiagram_scalar_eq]
  exact quadraticEssentialDiagram_scalar_secondFDeriv_apply x h k

/-- Nontrivial finite-pair relabeling preserves the final actual scalar bilinear form. -/
theorem actualQuadraticSingletonLift_second_derivative_relabel (x : ℝ) :
    secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        paddedActualQuadraticSingletonLift.coordinates x =
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        swappedActualQuadraticSingletonLift.coordinates x := by
  exact localLift_scalar_second_derivative_independent actualQuadraticSingletonDiagram
    essentialBirthSum 2 1 2 1 paddedActualQuadraticSingletonLift
    swappedActualQuadraticSingletonLift x (Set.mem_univ x) (Set.mem_univ x)
    (essentialBirthSum_c2_all _)

/-- Redundant diagonal coordinates change the dimension from `(0,1)` to `(2,1)`
while preserving the final actual scalar bilinear form. -/
theorem actualQuadraticSingletonLift_second_derivative_padding (x : ℝ) :
    secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 1)
        actualQuadraticSingletonLift.coordinates x =
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        paddedActualQuadraticSingletonLift.coordinates x := by
  exact localLift_scalar_second_derivative_independent actualQuadraticSingletonDiagram
    essentialBirthSum 0 1 2 1 actualQuadraticSingletonLift
    paddedActualQuadraticSingletonLift x (Set.mem_univ x) (Set.mem_univ x)
    (essentialBirthSum_c2_all _)

/-- All three presentations of the actual family compute the concrete Hessian `4*h*k`.
Only the final bilinear forms are identified, without ambient coefficient uniqueness. -/
theorem actualQuadraticSingletonLift_second_derivative_values (x h k : ℝ) :
    secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 1)
        actualQuadraticSingletonLift.coordinates x h k = 4 * h * k ∧
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        paddedActualQuadraticSingletonLift.coordinates x h k = 4 * h * k ∧
      secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
        swappedActualQuadraticSingletonLift.coordinates x h k = 4 * h * k := by
  have hv := localLift_scalar_second_fderiv actualQuadraticSingletonDiagram essentialBirthSum
    0 1 actualQuadraticSingletonLift x (Set.mem_univ x) (essentialBirthSum_c2_all _)
  have hvalue : secondDerivativeChain (essentialBirthSum ∘ orderedQ 0 1)
      actualQuadraticSingletonLift.coordinates x h k = 4 * h * k := by
    rw [← hv]
    exact actualQuadraticSingletonDiagram_scalar_secondFDeriv_apply x h k
  have hpadded : secondDerivativeChain (essentialBirthSum ∘ orderedQ 2 1)
      paddedActualQuadraticSingletonLift.coordinates x h k = 4 * h * k := by
    rw [← actualQuadraticSingletonLift_second_derivative_padding x]
    exact hvalue
  exact ⟨hvalue, hpadded, by
    rw [← actualQuadraticSingletonLift_second_derivative_relabel x]
    exact hpadded⟩

/-- The actual empty complex has its unique real filtration. -/
def emptyActualFilter :
    TDA.Filtration.FilterFunction (⊥ : PreAbstractSimplicialComplex (Fin 0)) ℝ where
  value := fun s => ((TDA.Filtration.mem_bot_iff s.val).mp s.property).elim
  mono := by
    intro τ σ _
    exact ((TDA.Filtration.mem_bot_iff τ.val).mp τ.property).elim

/-- The actual persistence construction on the empty complex gives the empty diagram. -/
theorem emptyActualFilter_diagram (p : ℕ) :
    dgm (ZMod 2) emptyActualFilter p = orderedQ 0 0 (Fin.elim0, Fin.elim0) := by
  have hc : emptyActualFilter.criticalValues.card = 0 := by
    rw [(emptyActualFilter.criticalValues_eq_empty_iff).2 rfl]
    rfl
  let : IsEmpty (Fin emptyActualFilter.criticalValues.card) := by
    rw [hc]
    infer_instance
  apply Diagram.ext
  simp [dgm, gradeHomologyBarcode, rankBarcode, ofIndexBars, orderedQ]

/-- Any scalar loss on the actual empty family is constant; no regularity of the
loss on other representatives is needed for this particular scalar function. -/
theorem emptyActualFilter_scalar_loss (V : Diagram ℝ → ℝ) (p : ℕ) :
    V (dgm (ZMod 2) emptyActualFilter p) =
      V (orderedQ 0 0 (Fin.elim0, Fin.elim0)) := by
  rw [emptyActualFilter_diagram]

/-- The actual empty family's scalar derivative map has derivative zero. -/
theorem emptyActualFilter_scalar_hasFDerivAt_fderiv
    (V : Diagram ℝ → ℝ) (p : ℕ) (x : ℝ) :
    HasFDerivAt (fderiv ℝ (fun _ : ℝ => V (dgm (ZMod 2) emptyActualFilter p)))
      (0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) x := by
  have hdf : fderiv ℝ (fun _ : ℝ => V (dgm (ZMod 2) emptyActualFilter p)) =
      (fun _ : ℝ => (0 : ℝ →L[ℝ] ℝ)) := by
    funext t
    exact fderiv_const_apply (𝕜 := ℝ) _
  rw [hdf]
  exact hasFDerivAt_const _ _

/-- The second derivative of every scalar loss on the actual empty family is zero. -/
theorem emptyActualFilter_scalar_second_fderiv (V : Diagram ℝ → ℝ) (p : ℕ) (x : ℝ) :
    fderiv ℝ (fderiv ℝ (fun _ : ℝ => V (dgm (ZMod 2) emptyActualFilter p))) x = 0 :=
  (emptyActualFilter_scalar_hasFDerivAt_fderiv V p x).fderiv

/-- The absolute endpoint loss fails C² through all representatives of the empty
diagram, because that condition would imply its already-disproved C¹ condition. -/
theorem absoluteFiniteEndpointDifference_not_c2_empty :
    ¬ C2ThroughAllRepresentatives absoluteFiniteEndpointDifference
      (orderedQ 0 0 (Fin.elim0, Fin.elim0)) := by
  intro h
  exact absoluteFiniteEndpointDifference_not_c1_empty h.c1

end TDA.Persistence
