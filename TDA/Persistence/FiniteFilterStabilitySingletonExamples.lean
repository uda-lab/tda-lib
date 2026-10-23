import TDA.Persistence.FiniteFilterStability
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-! An one-vertex degree-zero diagram attains the stability bound. -/

namespace TDA.Persistence.StabilityExamples
open TDA.Simplicial TDA.Filtration TDA.Persistence CategoryTheory

private instance vertexMem (s : Finset (Fin 2)) :
    Decidable (s ∈ singletonFace (0 : Fin 2)) :=
  decidable_of_iff (s = {0}) (mem_singletonFace_iff 0 s).symm

private instance vertexFaces : Fintype (TotalFace (singletonFace (0 : Fin 2))) :=
  inferInstance

/-- The real filter on one vertex. -/
def vertexFilter (a : ℝ) :
    FilterFunction (singletonFace (0 : Fin 2)) ℝ where
  value := fun _ => a
  mono := by intros; exact le_rfl

private theorem vertex_criticalValues (a : ℝ) :
    (vertexFilter a).criticalValues = {a} := by
  ext b
  constructor
  · intro hb
    obtain ⟨σ, hσ⟩ := ((vertexFilter a).mem_criticalValues b).1 hb
    exact Finset.mem_singleton.mpr (by simpa [vertexFilter] using hσ.symm)
  · intro hb
    have hface : ({0} : Finset (Fin 2)) ∈ singletonFace (0 : Fin 2) :=
      (mem_singletonFace_iff _ _).2 rfl
    have hb' : b = a := Finset.mem_singleton.mp hb
    subst b
    exact ((vertexFilter a).mem_criticalValues a).2 ⟨⟨{0}, hface⟩, rfl⟩

private theorem vertex_card (a : ℝ) : (vertexFilter a).criticalValues.card = 1 := by
  rw [vertex_criticalValues]
  simp

private noncomputable def vertex_i (a : ℝ) : Fin (vertexFilter a).criticalValues.card :=
  ⟨0, by rw [vertex_card]; decide⟩

private theorem vertex_critical (a : ℝ) :
    (vertexFilter a).criticalValue (vertex_i a) = a := by
  have h := (vertexFilter a).criticalValue_mem (vertex_i a)
  simpa [vertex_criticalValues] using h

private theorem vertex_stage (a : ℝ) :
    (vertexFilter a).gradeFiltration (vertex_i a) = singletonFace (0 : Fin 2) := by
  rw [(vertexFilter a).gradeFiltration_apply, vertex_critical]
  apply (vertexFilter a).sublevel_eq_self_of_forall_le
  intro s
  rfl

private theorem vertex_h0 (a : ℝ) :
    Module.finrank (ZMod 2)
      ((simplicialHomologyPModule (ZMod 2)
        (vertexFilter a).gradeFiltration 0).obj (vertex_i a)) = 1 := by
  rw [simplicialHomologyPModule_obj, vertex_stage]
  exact (simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).finrank_eq.trans
    (Module.finrank_self (ZMod 2))

private noncomputable def vertex_bar (a : ℝ) :
    FiniteInterval (vertexFilter a).criticalValues.card :=
  ⟨0, 1, by omega, by rw [vertex_card]⟩

private theorem vertex_barcode (a : ℝ) :
    gradeHomologyBarcode (ZMod 2) (vertexFilter a) 0 =
      ({vertex_bar a} : Multiset (FiniteInterval (vertexFilter a).criticalValues.card)) := by
  calc
    gradeHomologyBarcode (ZMod 2) (vertexFilter a) 0 =
        rankBarcode (barcodeModule (k := ZMod 2)
          ({vertex_bar a} :
            Multiset (FiniteInterval (vertexFilter a).criticalValues.card))) := by
      apply (rankBarcode_eq_iff
        (simplicialHomologyPModule (ZMod 2) (vertexFilter a).gradeFiltration 0)
        (barcodeModule (k := ZMod 2)
          ({vertex_bar a} :
            Multiset (FiniteInterval (vertexFilter a).criticalValues.card)))).mpr
      intro i j hij
      have hi : i = vertex_i a := by
        apply Fin.ext
        have hh := i.isLt
        have hc := vertex_card a
        omega
      have hj : j = vertex_i a := by
        apply Fin.ext
        have hh := j.isLt
        have hc := vertex_card a
        omega
      subst i
      subst j
      rw [rank_barcodeMap]
      have hr : structureMapRank
          (simplicialHomologyPModule (ZMod 2) (vertexFilter a).gradeFiltration 0)
          (vertex_i a) (vertex_i a) hij = 1 := by
        unfold structureMapRank
        rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
        exact vertex_h0 a
      rw [hr]
      rw [show ({vertex_bar a} :
        Multiset (FiniteInterval (vertexFilter a).criticalValues.card)) =
          vertex_bar a ::ₘ 0 by rfl, Multiset.countP_cons]
      simp [vertex_bar, vertex_i]
    _ = _ := rankBarcode_barcodeModule _

private theorem vertex_points (a : ℝ) :
    (dgm (ZMod 2) (vertexFilter a) 0).points =
      ({(a, (⊤ : WithTop ℝ))} : Multiset (ℝ × WithTop ℝ)) := by
  rw [dgm, vertex_barcode]
  simp [ofIndexBars, vertex_bar]
  change ((vertexFilter a).criticalValue (vertex_i a),
      if hd : 1 < (vertexFilter a).criticalValues.card then
        ((vertexFilter a).criticalValue ⟨1, hd⟩ : WithTop ℝ)
      else (⊤ : WithTop ℝ)) = (a, ⊤)
  simp [vertex_card, vertex_critical]

private theorem vertex_orderedQ (a : ℝ) :
    dgm (ZMod 2) (vertexFilter a) 0 =
      orderedQ 0 1 ((Fin.elim0 : Fin 0 → ℝ × ℝ), fun _ => a) := by
  apply Diagram.ext
  simpa [orderedQ] using vertex_points a

private theorem vertex_faceSupDifference (a b : ℝ) :
    faceSupDifference (vertexFilter a) (vertexFilter b) = |a - b| := by
  apply le_antisymm
  · unfold faceSupDifference
    apply (Finset.fold_max_le |a - b|).mpr
    constructor
    · exact abs_nonneg _
    · intro σ _
      rfl
  · let σ : TotalFace (singletonFace (0 : Fin 2)) :=
      ⟨{0}, (mem_singletonFace_iff _ _).2 rfl⟩
    simpa [vertexFilter] using
      (abs_face_difference_le (vertexFilter a) (vertexFilter b) σ)

/-- The unique essential point moves by exactly the change in the vertex grade. Infinity is retained as the death sentinel. -/
theorem vertex_bottleneck_sharp (a b : ℝ) :
    bottleneck (dgm (ZMod 2) (vertexFilter a) 0)
      (dgm (ZMod 2) (vertexFilter b) 0) = ENNReal.ofReal |a - b| := by
  rw [vertex_orderedQ, vertex_orderedQ]
  have hf₁ : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ × ℝ) =
        finitePart (orderedQ 0 1 ((Fin.elim0 : Fin 0 → ℝ × ℝ), fun _ => a)).points := by
    simp [finitePart_orderedQ]
  have hf₂ : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ × ℝ) =
        finitePart (orderedQ 0 1 ((Fin.elim0 : Fin 0 → ℝ × ℝ), fun _ => b)).points := by
    simp [finitePart_orderedQ]
  rw [bottleneck_eq_presentation _ _
    (Fin.elim0 : Fin 0 → ℝ × ℝ) (Fin.elim0 : Fin 0 → ℝ × ℝ)
    (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
    hf₁ hf₂
    (by simpa using (orderedQ_essential_occurrences 0 1
      ((Fin.elim0 : Fin 0 → ℝ × ℝ), fun _ : Fin 1 => a)))
    (by simpa using (orderedQ_essential_occurrences 0 1
      ((Fin.elim0 : Fin 0 → ℝ × ℝ), fun _ : Fin 1 => b)))]
  exact presentationBottleneck_essential_singletons a b

theorem vertex_stability_bound_sharp (a b : ℝ) :
    bottleneck (dgm (ZMod 2) (vertexFilter a) 0)
      (dgm (ZMod 2) (vertexFilter b) 0) =
        ENNReal.ofReal (faceSupDifference (vertexFilter a) (vertexFilter b)) := by
  rw [vertex_bottleneck_sharp, vertex_faceSupDifference]

end TDA.Persistence.StabilityExamples
