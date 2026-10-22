import TDA.Persistence.FiniteDecomposition

/-!
# Finite decomposition acceptance examples

These inputs are explicit persistence modules over an arbitrary field. The scalar transition
example records the inverse scaling used by its compatible linear equivalences.
-/

universe u

set_option backward.isDefEq.respectTransparency false

namespace TDA.Persistence.FiniteDecompositionExamples

open CategoryTheory
variable {k : Type u} [Field k]

/-- The sole interval on one observed stage. -/
def bar01 : FiniteInterval 1 := ⟨0, 1, by decide, by decide⟩
/-- Survival at both of the two observed stages. -/
def bar02 : FiniteInterval 2 := ⟨0, 2, by decide, by decide⟩
/-- A class that dies before the second observed stage. -/
def bar01two : FiniteInterval 2 := ⟨0, 1, by decide, by decide⟩
/-- A class born at the second observed stage. -/
def bar12 : FiniteInterval 2 := ⟨1, 2, by decide, by decide⟩
/-- Birth at the final observed stage, with finite endpoint `N = 3`. -/
def bar23 : FiniteInterval 3 := ⟨2, 3, by decide, by decide⟩

/-- The zero module, including on nonempty index sets, with explicit zero fibers. -/
def zeroDiagram (N : ℕ) : PModule.{u,0,u} k (Fin N) where
  obj _ := ModuleCat.of k (Fin 0 → k)
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

instance zeroDiagram_finiteDimensional (N : ℕ) (i : Fin N) :
    FiniteDimensional k ((zeroDiagram (k := k) N).obj i) := by
  change FiniteDimensional k (Fin 0 → k)
  infer_instance

private instance emptyBarcode_subsingleton (N : ℕ) (i : Fin N) :
    Subsingleton ((barcodeModule (k := k) (0 : Multiset (FiniteInterval N))).obj i) := by
  dsimp [barcodeModule, barcodeModuleOfList]
  rw [@Multiset.toList_zero (FiniteInterval N)]
  refine ⟨fun x y => ?_⟩
  funext t
  exact Fin.elim0 t

/-- The empty index case uses no selected stage or nonzero vector. -/
noncomputable def emptyIndexIso (M : PModule.{u,0,u} k (Fin 0)) :
    M ≅ barcodeModule (k := k) (0 : Multiset (FiniteInterval 0)) :=
  NatIso.ofComponents (fun i => Fin.elim0 i) (by intro i; exact Fin.elim0 i)

/-- The explicit zero diagram is naturally isomorphic to the empty realization. -/
noncomputable def zeroDiagramIso (N : ℕ) :
    zeroDiagram (k := k) N ≅ barcodeModule (k := k) (0 : Multiset (FiniteInterval N)) := by
  refine NatIso.ofComponents (fun i => ?_) ?_
  · haveI : Subsingleton ((zeroDiagram (k := k) N).obj i) := by
      change Subsingleton (Fin 0 → k)
      infer_instance
    let E : ((zeroDiagram (k := k) N).obj i) ≃ₗ[k]
        ((barcodeModule (k := k) (0 : Multiset (FiniteInterval N))).obj i) :=
      LinearEquiv.ofSubsingleton _ _
    exact E.toModuleIso
  · intro i j f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _

theorem zeroDiagram_barcode (N : ℕ) : rankBarcode (zeroDiagram (k := k) N) = 0 :=
  rankBarcode_eq_of_iso_barcodeModule 0 (zeroDiagramIso N)

/-- A concrete nonempty observed index set still has the empty zero-module barcode. -/
theorem zeroThreeStages_decomposition : rankBarcode (zeroDiagram (k := k) 3) = 0 ∧
    Nonempty (zeroDiagram (k := k) 3 ≅
      barcodeModule (k := k) (0 : Multiset (FiniteInterval 3))) :=
  ⟨zeroDiagram_barcode 3, ⟨zeroDiagramIso 3⟩⟩

/-- One observed stage with the genuine fiber `k × k`. -/
def oneStagePair : PModule.{u,0,u} k (Fin 1) where
  obj _ := ModuleCat.of k (k × k)
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

instance oneStagePair_finiteDimensional (i : Fin 1) :
    FiniteDimensional k ((oneStagePair (k := k)).obj i) := by
  change FiniteDimensional k (k × k)
  infer_instance

theorem oneStagePair_barcode : rankBarcode (oneStagePair (k := k)) =
    Multiset.replicate 2 bar01 := by
  rw [← rankBarcode_barcodeModule (k := k) (Multiset.replicate 2 bar01)]
  apply (rankBarcode_eq_iff _ _).2
  intro i j hij
  fin_cases i
  fin_cases j
  rw [rank_barcodeMap]
  change Module.finrank k (LinearMap.range (LinearMap.id : (k × k) →ₗ[k] (k × k))) = _
  rw [LinearMap.range_id, finrank_top]
  simp [Module.finrank_prod, bar01, -Multiset.cons_zero]

/-- Two initial zero fibers followed by a copy of the field. -/
noncomputable def delayedBirthFiber (i : Fin 3) : Submodule k k :=
  if i.val < 2 then ⊥ else ⊤

private theorem delayedBirthFiber_mono {i j : Fin 3} (hij : i ≤ j) :
    delayedBirthFiber (k := k) i ≤ delayedBirthFiber (k := k) j := by
  classical
  by_cases hi : i.val < 2
  · simp only [delayedBirthFiber, if_pos hi]
    exact bot_le
  · have hj : ¬ j.val < 2 := by
      have h := Fin.le_iff_val_le_val.mp hij
      omega
    simp only [delayedBirthFiber, if_neg hi, if_neg hj]
    exact le_refl _

/-- The maps are the inclusions of zero or full-field fibers. -/
noncomputable def delayedBirthDiagram : PModule.{u,0,u} k (Fin 3) where
  obj i := ModuleCat.of k (delayedBirthFiber (k := k) i)
  map f := ModuleCat.ofHom (Submodule.inclusion (delayedBirthFiber_mono (k := k) (leOfHom f)))
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance delayedBirthDiagram_finiteDimensional (i : Fin 3) :
    FiniteDimensional k ((delayedBirthDiagram (k := k)).obj i) := by
  change FiniteDimensional k (delayedBirthFiber (k := k) i)
  infer_instance

theorem delayedBirth_zero_initial :
    Module.finrank k ((delayedBirthDiagram (k := k)).obj (0 : Fin 3)) = 0 ∧
    Module.finrank k ((delayedBirthDiagram (k := k)).obj (1 : Fin 3)) = 0 := by
  change Module.finrank k (delayedBirthFiber (k := k) 0) = 0 ∧
    Module.finrank k (delayedBirthFiber (k := k) 1) = 0
  simp [delayedBirthFiber]

theorem delayedBirth_final_dimension :
    Module.finrank k ((delayedBirthDiagram (k := k)).obj (2 : Fin 3)) = 1 := by
  change Module.finrank k (delayedBirthFiber (k := k) 2) = 1
  simp [delayedBirthFiber]

theorem delayedBirth_barcode : rankBarcode (delayedBirthDiagram (k := k)) =
    ({bar23} : Multiset (FiniteInterval 3)) := by
  rw [← rankBarcode_barcodeModule (k := k) ({bar23} : Multiset (FiniteInterval 3))]
  apply (rankBarcode_eq_iff _ _).2
  intro i j hij
  rw [rank_barcodeMap]
  change Module.finrank k (LinearMap.range
    (Submodule.inclusion (delayedBirthFiber_mono (k := k) hij))) = _
  rw [LinearMap.finrank_range_of_inj (Submodule.inclusion_injective _)]
  fin_cases i <;> fin_cases j <;>
    simp_all [delayedBirthFiber, bar23, ← Multiset.cons_zero]

/-- Multiplication by `c` is the transition; self maps remain identities. -/
def scalarTransitionDiagram (c : k) : PModule.{u,0,u} k (Fin 2) where
  obj _ := ModuleCat.of k k
  map {i j} _ := if i = j then 𝟙 _ else ModuleCat.ofHom (c • LinearMap.id)
  map_id i := by simp
  map_comp {i j l} f g := by
    have hij : i ≤ j := leOfHom f
    have hjl : j ≤ l := leOfHom g
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all

instance scalarTransitionDiagram_finiteDimensional (c : k) (i : Fin 2) :
    FiniteDimensional k ((scalarTransitionDiagram c).obj i) := by
  change FiniteDimensional k k
  infer_instance

theorem scalarTransitionDiagram_map (c : k) (x : k) :
    structureMapLinear (scalarTransitionDiagram c) (show (0 : Fin 2) ≤ 1 by decide) x =
      c * x := rfl

/-- The second component divides by `c`; naturality cancels the transition scalar. -/
noncomputable def scalarTransitionIso (c : k) (hc : c ≠ 0) :
    scalarTransitionDiagram c ≅ identityTransitionDiagram k := by
  refine NatIso.ofComponents (fun i =>
    if i = 0 then (LinearEquiv.refl k k).toModuleIso
    else (LinearEquiv.smulOfNeZero k k c hc).symm.toModuleIso) ?_
  intro i j f
  have hij : i ≤ j := leOfHom f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  fin_cases i <;> fin_cases j <;>
    simp_all [scalarTransitionDiagram, identityTransitionDiagram, LinearMap.comp_apply]
  change k at x
  change (LinearEquiv.smulOfNeZero k k c hc).symm (c * x) = x
  exact (LinearEquiv.smulOfNeZero k k c hc).symm_apply_apply x

theorem scalarTransitionIso_final (c : k) (hc : c ≠ 0) (x : k) :
    ((scalarTransitionIso c hc).hom.app (1 : Fin 2)).hom x = c⁻¹ * x := rfl

instance identityTransition_finiteDimensional (i : Fin 2) :
    FiniteDimensional k ((identityTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

instance zeroTransition_finiteDimensional (i : Fin 2) :
    FiniteDimensional k ((zeroTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

theorem identityTransition_barcode : rankBarcode (identityTransitionDiagram k) =
    ({bar02} : Multiset (FiniteInterval 2)) := by
  rw [← rankBarcode_barcodeModule (k := k) ({bar02} : Multiset (FiniteInterval 2))]
  apply (rankBarcode_eq_iff _ _).2
  intro i j hij
  rw [rank_barcodeMap]
  change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = _
  rw [LinearMap.range_id, finrank_top, Module.finrank_self]
  fin_cases i <;> fin_cases j <;>
    simp [bar02, ← Multiset.cons_zero]

theorem scalarTransition_barcode (c : k) (hc : c ≠ 0) :
    rankBarcode (scalarTransitionDiagram c) = ({bar02} : Multiset (FiniteInterval 2)) := by
  rw [rankBarcode_eq_of_iso (scalarTransitionIso c hc), identityTransition_barcode]

theorem zeroTransition_barcode : rankBarcode (zeroTransitionDiagram k) =
    ({bar01two, bar12} : Multiset (FiniteInterval 2)) := by
  rw [← rankBarcode_barcodeModule (k := k)
    ({bar01two, bar12} : Multiset (FiniteInterval 2))]
  apply (rankBarcode_eq_iff _ _).2
  intro i j hij
  rw [rank_barcodeMap]
  fin_cases i <;> fin_cases j
  · unfold structureMapRank
    rw [structureMapLinear_self]
    change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = _
    rw [LinearMap.range_id, finrank_top, Module.finrank_self]
    simp [bar01two, bar12, ← Multiset.cons_zero]
  · change Module.finrank k (LinearMap.range (0 : k →ₗ[k] k)) = _
    rw [LinearMap.range_zero, finrank_bot]
    simp [bar01two, bar12, ← Multiset.cons_zero]
  · change (1 : ℕ) ≤ 0 at hij
    omega
  · unfold structureMapRank
    rw [structureMapLinear_self]
    change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = _
    rw [LinearMap.range_id, finrank_top, Module.finrank_self]
    simp [bar01two, bar12, ← Multiset.cons_zero]

theorem identity_zero_same_dimensions_different_barcodes :
    (∀ i : Fin 2, Module.finrank k ((identityTransitionDiagram k).obj i) =
      Module.finrank k ((zeroTransitionDiagram k).obj i)) ∧
    rankBarcode (identityTransitionDiagram k) ≠ rankBarcode (zeroTransitionDiagram k) ∧
    ¬ Nonempty (identityTransitionDiagram k ≅ zeroTransitionDiagram k) := by
  have hbarcode : rankBarcode (identityTransitionDiagram k) ≠
      rankBarcode (zeroTransitionDiagram k) := by
    rw [identityTransition_barcode, zeroTransition_barcode]
    intro h
    have hcard := congrArg Multiset.card h
    simp at hcard
  exact ⟨fun _ => rfl, hbarcode, fun ⟨e⟩ => hbarcode (rankBarcode_eq_of_iso e)⟩

private instance emptyIndex_finiteDimensional (M : PModule.{u,0,u} k (Fin 0)) :
    ∀ i : Fin 0, FiniteDimensional k (M.obj i) := fun i => Fin.elim0 i

theorem emptyIndex_barcode (M : PModule.{u,0,u} k (Fin 0)) : rankBarcode M = 0 :=
  rankBarcode_eq_of_iso_barcodeModule 0 (emptyIndexIso M)

/-- Exactly two occurrences of the same bar realize the one-stage pair. -/
noncomputable def oneStagePairIso : oneStagePair (k := k) ≅
    barcodeModule (k := k) (Multiset.replicate 2 bar01) :=
  rankBarcodeIso _ ≪≫ eqToIso (congrArg (barcodeModule (k := k)) oneStagePair_barcode)

/-- Every interval decomposition of the pair has these two occurrences. -/
theorem oneStagePair_decomposition_unique (B : Multiset (FiniteInterval 1))
    (e : oneStagePair (k := k) ≅ barcodeModule (k := k) B) :
    B = Multiset.replicate 2 bar01 :=
  barcode_decomposition_unique (oneStagePair (k := k)) B
    (Multiset.replicate 2 bar01) e oneStagePairIso

/-- The delayed class survives the last observation; its endpoint is the finite size three. -/
noncomputable def delayedBirthIso : delayedBirthDiagram (k := k) ≅
    barcodeModule (k := k) ({bar23} : Multiset (FiniteInterval 3)) :=
  rankBarcodeIso _ ≪≫ eqToIso (congrArg (barcodeModule (k := k)) delayedBirth_barcode)

noncomputable def identityTransitionBarcodeIso : identityTransitionDiagram k ≅
    barcodeModule (k := k) ({bar02} : Multiset (FiniteInterval 2)) :=
  rankBarcodeIso _ ≪≫ eqToIso (congrArg (barcodeModule (k := k)) identityTransition_barcode)

/-- The explicit inverse-scaled isomorphism supplies the first step of this decomposition. -/
noncomputable def scalarTransitionBarcodeIso (c : k) (hc : c ≠ 0) :
    scalarTransitionDiagram c ≅
      barcodeModule (k := k) ({bar02} : Multiset (FiniteInterval 2)) :=
  scalarTransitionIso c hc ≪≫ identityTransitionBarcodeIso

noncomputable def zeroTransitionBarcodeIso : zeroTransitionDiagram k ≅
    barcodeModule (k := k) ({bar01two, bar12} : Multiset (FiniteInterval 2)) :=
  rankBarcodeIso _ ≪≫ eqToIso (congrArg (barcodeModule (k := k)) zeroTransition_barcode)

end TDA.Persistence.FiniteDecompositionExamples
