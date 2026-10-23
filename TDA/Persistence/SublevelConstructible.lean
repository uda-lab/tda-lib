import TDA.Persistence.SublevelInterleaving
import TDA.Persistence.ConstructibleIsometry

set_option autoImplicit false

/-!
# Constructibility of sublevel modules and the filter-diagram isometry

The real sublevel homology module of a filter on a finite complex is finite-constructible on
the increasing enumeration `criticalValue` of its attained face values, over every ring: below
the first value the sublevel is empty, and within a cell of that grid the sublevel does not
change. Over a field the critical fibers are finite-dimensional, and the module diagram on this
grid is the filter diagram `dgm` by definition, since both are the value-labelled rank barcode
of the same critical-grade module. The finite-constructible isometry therefore identifies the
bottleneck distance of two filter diagrams on the same complex with the interleaving distance of
their sublevel modules. The finite-filter stability bound follows again, from the inclusion
interleaving of the sublevel modules instead of face-order interpolation.

These are library extensions proved from the merged definitions.
-/

universe u v

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits TDA.Simplicial TDA.Filtration
open TDA.Persistence.FiniteConstructible
open scoped NNReal ENNReal

variable {V : Type u} [LinearOrder V]

/-! ### Homology of equal and empty complexes -/

section Homology

variable (R : Type v) [Ring R]

/-- The empty complex has zero homology in every degree, over every ring. -/
theorem isZero_simplicialHomology_bot (n : ℕ) :
    IsZero (simplicialHomology (⊥ : PreAbstractSimplicialComplex V) R n) := by
  have hX : IsZero ((simplicialChainComplex (⊥ : PreAbstractSimplicialComplex V) R).X n) := by
    rw [simplicialChainComplex_X]
    exact ModuleCat.isZero_of_subsingleton _
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ hX

/-- The homology inclusion between equal complexes is an isomorphism. -/
theorem isIso_simplicialHomologyIncl_of_eq {A B : PreAbstractSimplicialComplex V}
    (hAB : A = B) (h : A ≤ B) (n : ℕ) : IsIso (simplicialHomologyIncl R h n) := by
  subst hAB
  change IsIso (simplicialHomologyIncl R (le_refl A) n)
  rw [simplicialHomologyIncl_id]
  infer_instance

end Homology

/-! ### Constructibility over a ring -/

section Constructible

variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]

omit [LinearOrder V] in
/-- Two ordered thresholds in the same cell of the critical grid have the same sublevel. -/
theorem sublevel_eq_of_cellIndex_eq (f : FilterFunction K ℝ) {s t : ℝ} (hst : s ≤ t)
    (h : cellIndex f.criticalValue s = cellIndex f.criticalValue t) :
    f.sublevel s = f.sublevel t := by
  apply le_antisymm (f.sublevel_mono hst)
  intro σ hσ
  obtain ⟨hσK, hσt⟩ := (f.mem_sublevel_iff t σ).1 hσ
  obtain ⟨i, hi⟩ := f.exists_criticalValue_eq ⟨σ, hσK⟩
  have hit : i.val < (cellIndex f.criticalValue t).val :=
    (lt_cellIndex_iff _ i t).2 (hi.le.trans hσt)
  rw [← h] at hit
  exact (f.mem_sublevel_iff s σ).2 ⟨hσK, hi.symm.le.trans ((lt_cellIndex_iff _ i s).1 hit)⟩

omit [LinearOrder V] in
/-- A threshold below every critical value has empty sublevel. -/
theorem sublevel_eq_bot_of_forall_criticalValue_lt (f : FilterFunction K ℝ) {t : ℝ}
    (h : ∀ i, t < f.criticalValue i) : f.sublevel t = ⊥ :=
  f.sublevel_eq_bot_of_forall_lt t fun σ => by
    obtain ⟨i, hi⟩ := f.exists_criticalValue_eq σ
    exact hi ▸ h i

variable (R : Type v) [Ring R] (n : ℕ)

/-- The sublevel homology module of a filter on a finite complex is finite-constructible on
the increasing enumeration of its attained face values, over every ring. -/
theorem sublevelModule_isConstructible (f : FilterFunction K ℝ) :
    IsConstructible f.criticalValue (sublevelModule R f n) where
  zero_left t ht := by
    change IsZero (simplicialHomology (f.sublevel t) R n)
    rw [sublevel_eq_bot_of_forall_criticalValue_lt f ht]
    exact isZero_simplicialHomology_bot R n
  isIso_map s t hst h :=
    isIso_simplicialHomologyIncl_of_eq R (sublevel_eq_of_cellIndex_eq f hst h)
      (f.sublevel_mono hst) n

end Constructible

/-! ### The filter diagram as a module diagram -/

section Field

variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
variable (k : Type u) [Field k] (n : ℕ)

/-- Over a field, the sublevel module has finite-dimensional fibers at the critical values. -/
theorem sublevelModule_finiteDimensional (f : FilterFunction K ℝ) :
    ∀ i, FiniteDimensional k ((sublevelModule k f n).obj (f.criticalValue i)) :=
  fun i => gradeHomology_finiteDimensional k f n i

/-- The module diagram of the sublevel module on the critical grid is the filter diagram. Both
are the value-labelled rank barcode of the critical-grade homology module, with essential
classes at death `⊤`. -/
theorem moduleDiagram_sublevelModule (f : FilterFunction K ℝ) :
    moduleDiagram f.criticalValue (sublevelModule k f n)
      (sublevelModule_finiteDimensional k n f) = dgm k f n :=
  rfl

/-- The sublevel module is isomorphic to the half-open realization of its filter diagram. -/
noncomputable def sublevelModuleRealizationIso (f : FilterFunction K ℝ) :
    sublevelModule k f n ≅ RealBarcode.realize (k := k) (dgm k f n) :=
  barcodeRealizationIso f.criticalValue (sublevelModule k f n)
      (sublevelModule_isConstructible k n f) (sublevelModule_finiteDimensional k n f) ≪≫
    eqToIso (congrArg (RealBarcode.realize (k := k)) (moduleDiagram_sublevelModule k n f))

/-- For two filters on the same finite complex, the bottleneck distance of their diagrams is the
interleaving distance of their sublevel modules. The critical grids are unrelated. -/
theorem bottleneck_dgm_eq_realInterleavingDistance (f g : FilterFunction K ℝ) :
    bottleneck (dgm k f n) (dgm k g n) =
      realInterleavingDistance (sublevelModule k f n) (sublevelModule k g n) := by
  rw [← moduleDiagram_sublevelModule k n f, ← moduleDiagram_sublevelModule k n g]
  exact bottleneck_eq_distance (sublevelModule_isConstructible k n f)
    (sublevelModule_isConstructible k n g) (sublevelModule_finiteDimensional k n f)
    (sublevelModule_finiteDimensional k n g)

/-- At every finite parameter, sublevel interleavings and cost-bounded occurrence matchings of
the filter diagrams exist together. -/
theorem nonempty_sublevelInterleaving_iff (f g : FilterFunction K ℝ) (ε : ℝ≥0) :
    Nonempty (RealInterleaving ε (sublevelModule k f n) (sublevelModule k g n)) ↔
      ∃ A : OccurrenceMatching (dgm k f n).finiteOccurrences (dgm k g n).finiteOccurrences
          (dgm k f n).essentialOccurrences (dgm k g n).essentialOccurrences,
        A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤ (ε : ℝ≥0∞) :=
  interleaving_iff_matching (sublevelModule_isConstructible k n f)
    (sublevelModule_isConstructible k n g) (sublevelModule_finiteDimensional k n f)
    (sublevelModule_finiteDimensional k n g) ε

/-- Finite-filter stability, derived from the isometry and the inclusion interleaving of the
sublevel modules. -/
theorem bottleneck_dgm_le_faceSupDifference_algebraic (f g : FilterFunction K ℝ) :
    bottleneck (dgm k f n) (dgm k g n) ≤ ENNReal.ofReal (faceSupDifference f g) := by
  rw [bottleneck_dgm_eq_realInterleavingDistance]
  exact realInterleavingDistance_sublevel_le_faceSupDifference k n f g

/-- The sublevel modules of two filters on the same finite complex are at finite interleaving
distance. -/
theorem realInterleavingDistance_sublevel_ne_top (f g : FilterFunction K ℝ) :
    realInterleavingDistance (sublevelModule k f n) (sublevelModule k g n) ≠ ⊤ := by
  rw [← bottleneck_dgm_eq_realInterleavingDistance]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (bottleneck_dgm_le_faceSupDifference_algebraic k n f g)

/-- Two filters on the same finite complex have the same number of essential classes. -/
theorem essentialPart_card_dgm_eq (f g : FilterFunction K ℝ) :
    (essentialPart (dgm k f n).points).card = (essentialPart (dgm k g n).points).card := by
  by_contra hne
  exact realInterleavingDistance_sublevel_ne_top k n f g
    ((distance_eq_top_iff_essential_card_ne (sublevelModule_isConstructible k n f)
      (sublevelModule_isConstructible k n g) (sublevelModule_finiteDimensional k n f)
      (sublevelModule_finiteDimensional k n g)).2 hne)

end Field

end TDA.Persistence
