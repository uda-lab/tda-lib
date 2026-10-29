import TDA.Persistence.TwoInjectiveHomDimension

/-!
# Examples for the actual two-injective Hom sequence

These examples exercise the constructed maps for a nonzero constant module,
a repeated-coordinate module, and zero/singleton boundaries. The dimension
shift consumer is shown with the actual Hom cokernel estimate as an explicit
hypothesis; these examples do not assert its finite-algebra bound.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.TwoInjectiveHomDimensionExamples

open CategoryTheory CategoryTheory.Limits
open FiniteRankProjectiveHomExact
open FiniteInjectiveRankDimension
open TwoInjectivePresentation
open TwoInjectiveHomDimension
open scoped ZeroObject

noncomputable section

private abbrev H (k : Type u) [Field k] (S : Type) [Lattice S] [Finite S] :=
  homFunctor (k := k) (S := S)

/-- A nonzero constant persistence module over the infinite field of rationals. -/
abbrev scalarLine : PModule ℚ (Fin 2) :=
  (Functor.const (Fin 2)).obj (ModuleCat.of ℚ ℚ)

private instance scalarLine_finiteDimensional (p : Fin 2) :
    FiniteDimensional ℚ (scalarLine.obj p) := by
  change FiniteDimensional ℚ ℚ
  infer_instance

theorem scalarLine_nonzero_fiber :
    ∃ x : scalarLine.obj 0, x ≠ 0 := by
  change ∃ x : ℚ, x ≠ 0
  refine ⟨7, ?_⟩
  norm_num

/-- The actual two-injective presentation of a nonzero module is monic and has
the advertised vanishing composition. -/
theorem scalarLine_presentation_laws :
    Mono (firstEmbedding scalarLine) ∧
      firstEmbedding scalarLine ≫ differential scalarLine = 0 :=
  ⟨firstEmbedding_mono scalarLine, firstEmbedding_comp_differential scalarLine⟩

/-- The two actual Hom rows are short exact for the nonzero constant module. -/
theorem scalarLine_actual_shortExact_rows :
    (firstShortComplex scalarLine).ShortExact ∧
      (secondShortComplex scalarLine).ShortExact :=
  ⟨firstShortComplex_shortExact scalarLine,
    secondShortComplex_shortExact scalarLine⟩

/-- A two-dimensional fiber produces repeated coordinate occurrences while
the actual Hom image and cokernel rows remain short exact. -/
abbrev doubleSingleton : PModule ℚ (Fin 1) :=
  (Functor.const (Fin 1)).obj (ModuleCat.of ℚ (ℚ × ℚ))

private instance doubleSingleton_finiteDimensional (p : Fin 1) :
    FiniteDimensional ℚ (doubleSingleton.obj p) := by
  change FiniteDimensional ℚ (ℚ × ℚ)
  infer_instance

theorem doubleSingleton_dimension :
    ∀ p : Fin 1, Module.finrank ℚ (doubleSingleton.obj p) = 2 := by
  intro p
  simp [doubleSingleton, Module.finrank_prod]

theorem doubleSingleton_actual_shortExact_rows :
    (firstShortComplex doubleSingleton).ShortExact ∧
      (secondShortComplex doubleSingleton).ShortExact :=
  ⟨firstShortComplex_shortExact doubleSingleton,
    secondShortComplex_shortExact doubleSingleton⟩

private instance zeroFiberSubsingleton {S : Type} [PartialOrder S] (p : S) :
    Subsingleton ((0 : PModule ℚ S).obj p) :=
  ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)

private instance zeroFiber_finiteDimensional {S : Type} [Lattice S]
    [OrderBot S] [OrderTop S] [Finite S] (p : S) :
    FiniteDimensional ℚ ((0 : PModule ℚ S).obj p) := by
  infer_instance

/-- The zero module exercises both actual cokernel/image rows as well. -/
theorem zero_actual_shortExact_rows :
    (firstShortComplex (0 : PModule ℚ (Fin 2))).ShortExact ∧
      (secondShortComplex (0 : PModule ℚ (Fin 2))).ShortExact :=
  ⟨firstShortComplex_shortExact _, secondShortComplex_shortExact _⟩

/-- On a singleton index, the actual two-injective and two-row constructions
remain valid over the infinite coefficient field. -/
abbrev singletonScalar : PModule ℚ (Fin 1) :=
  (Functor.const (Fin 1)).obj (ModuleCat.of ℚ ℚ)

private instance singletonScalar_finiteDimensional (p : Fin 1) :
    FiniteDimensional ℚ (singletonScalar.obj p) := by
  change FiniteDimensional ℚ ℚ
  infer_instance

theorem singleton_actual_shortExact_rows :
    (firstShortComplex singletonScalar).ShortExact ∧
      (secondShortComplex singletonScalar).ShortExact :=
  ⟨firstShortComplex_shortExact singletonScalar,
    secondShortComplex_shortExact singletonScalar⟩

/-- The shift consumer is also available over any field; its only
homological input is the bound on the actual cokernel of Hom(delta). -/
theorem arbitraryField_actualCokernel_shift
    {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]
    [OrderBot S] [OrderTop S] (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] (d : ℕ)
    (hD : maxComplementCard (S := S) - 1 ≤ d)
    (hC : HasProjectiveDimensionLE (homCokernel M) (d + 2)) :
    HasProjectiveDimensionLE ((H k S).obj M) d :=
  hom_hasProjectiveDimensionLE_of_actualCokernel M d hD hC

end

end TDA.Persistence.TwoInjectiveHomDimensionExamples
