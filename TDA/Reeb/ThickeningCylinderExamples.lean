import TDA.Reeb.ThickeningCylinder
import TDA.Reeb.ThickeningSliceExamples
import TDA.Topology.QuotientProductExamples

/-!
# Fixtures for the thickening presentation of one cylinder

Acceptance fixtures for `TDA.Reeb.ThickeningCylinder`, mostly for the segment `[0, 1]` at
`ε = 1/2` on the grid `G4 = (-3/2 < -1/2 < 1/2 < 3/2)` of `TDA.Reeb.ThickeningSliceExamples`:

* **Empty pieces.** The vertex piece at the level `-3/2` and the edge piece over the corner-only
  slab `[-3/2, -1/2]` are empty, for every `E`.
* **A corner-only fibre.** The vertex piece at `-1/2` is `E × {0}`, and its points go to the corner
  `(y, 0, -1/2)` of the thickened cylinder.
* **Endpoint collapse.** The left endpoint map of the slab `[-1/2, 1/2]` collapses the reference
  slice `[0, 1/2]` to the point slice `{0}` at `-1/2`; it is not injective when `E` is nonempty.
* **Coincident events.** On the shifted witness of `pair 0 1`, whose events `1 - ε = 0 + ε`
  coincide, the construction still gives the homeomorphism.
* **`ε = 0`.** Every cylinder point `((y, σ), u)` goes to `(y, u, 0)`.
* **A vertex strip.** For `[1, 1]` at `ε = 1/2` on the grid `1/2 < 3/2`, the vertex point at level
  `1/2` goes to the band coordinate `-1/2`.
* **No Hausdorff hypothesis.** For the Sierpiński space `E = Prop`, the pieces are compact and
  locally path-connected but not Hausdorff, the realization is not Hausdorff, and the homeomorphism
  applies.
-/

open Set Topology
open scoped NNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.ThickeningCylinder

open CylinderPresentation Thickening CriticalValues Examples.ThickeningSlice
open RGraph (fragAff)
open GeometricThickening (Band)

/-- The thickening presentation of `E × [0, 1]` at `ε = 1/2` on the grid `G4`. -/
abbrev C4 (E : Type) [TopologicalSpace E] : CylinderPresentation.{0} 3 :=
  cylinderThick 0 1 halfNN E G4 hasEvents_G4

/-! ### Empty pieces -/

/-- **Empty slice.** The vertex piece at the level `-3/2` is empty. -/
theorem isEmpty_C4_V_zero (E : Type) [TopologicalSpace E] : IsEmpty ((C4 E).V 0) :=
  ⟨fun p => by
    obtain ⟨-, s, hs⟩ := p
    have h := mem_slice_iff.1 hs
    rw [G4_value_zero, coe_halfNN] at h
    linarith [h.1.1, h.2.2]⟩

/-- **Empty slice.** The edge piece over the corner-only slab is empty. -/
theorem isEmpty_C4_E_zero (E : Type) [TopologicalSpace E] : IsEmpty ((C4 E).E 0) :=
  ⟨fun p => by
    obtain ⟨-, s, hs⟩ := p
    rw [slice_mid_G4_zero] at hs
    exact hs⟩

/-! ### A corner-only fibre -/

/-- The slice at the corner level `-1/2` is the point `{0}`. -/
theorem slice_G4_one : slice 0 1 halfNN (G4.value 1) = {0} := by
  ext s
  rw [mem_slice_iff, G4_value_one, coe_halfNN, mem_singleton_iff, mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, -, h4⟩
    exact le_antisymm (by linarith) h1
  · rintro rfl
    norm_num

/-- **Corner-only fibre.** The vertex point at the corner level goes to the corner `(y, 0, -1/2)`. -/
theorem toCylinder_corner (E : Type) [TopologicalSpace E] (y : E)
    (h : (0 : ℝ) ∈ slice 0 1 halfNN (G4.value 1)) :
    toCylinder 0 1 halfNN E G4 hasEvents_G4 ((C4 E).ofVertex G4 1 (y, ⟨0, h⟩)) =
      (y, ⟨0, by norm_num⟩, ⟨-1 / 2, by norm_num⟩) := by
  rw [toCylinder_ofVertex]
  refine Prod.ext rfl (Prod.ext rfl (Subtype.ext ?_))
  show G4.value 1 - 0 = -1 / 2
  rw [G4_value_one]
  norm_num

/-! ### Endpoint collapse -/

theorem mid_G4_one : G4.mid 1 = 0 := by
  simp only [CriticalValues.mid]
  rw [show (1 : Fin 3).castSucc = 1 from rfl, show (1 : Fin 3).succ = 2 from rfl, G4_value_one,
    G4_value_two]
  norm_num

/-- **Endpoint collapse.** The left endpoint map of the slab `[-1/2, 1/2]` sends the reference slice
`[0, 1/2]` to the point slice `{0}`; it is not injective. -/
theorem not_injective_C4_left (E : Type) [TopologicalSpace E] [Nonempty E] :
    ¬ Function.Injective ((C4 E).left 1) := by
  obtain ⟨y⟩ := ‹Nonempty E›
  have h0 : (0 : ℝ) ∈ slice 0 1 halfNN (G4.mid 1) := by
    rw [mid_G4_one, mem_slice_iff, coe_halfNN]
    norm_num
  have h1 : (1 / 2 : ℝ) ∈ slice 0 1 halfNN (G4.mid 1) := by
    rw [mid_G4_one, mem_slice_iff, coe_halfNN]
    norm_num
  have hu : max (0 : ℝ) (G4.value (Fin.castSucc (1 : Fin 3)) - halfNN) =
      min 1 (G4.value (Fin.castSucc (1 : Fin 3)) + halfNN) := by
    rw [show G4.value (Fin.castSucc (1 : Fin 3)) = -1 / 2 from G4_value_one, coe_halfNN]
    norm_num
  have hcol : (C4 E).left 1 (y, ⟨0, h0⟩) = (C4 E).left 1 (y, ⟨1 / 2, h1⟩) := by
    refine Prod.ext rfl (Subtype.ext ?_)
    show fragAff 0 1 halfNN (G4.mid 1) (G4.value (Fin.castSucc (1 : Fin 3))) 0 =
      fragAff 0 1 halfNN (G4.mid 1) (G4.value (Fin.castSucc (1 : Fin 3))) (1 / 2)
    rw [RGraph.fragAff_collapse hu, RGraph.fragAff_collapse hu]
  intro hinj
  have hp := congrArg (fun p : E × slice (0 : ℝ) 1 halfNN (G4.mid 1) => (p.2 : ℝ)) (hinj hcol)
  norm_num at hp

/-! ### Coincident events -/

/-- **Coincident events.** On the shifted witness of `pair 0 1` at `ε = 1/2`, the events
`1 - ε = 0 + ε` coincide, so the grid has three levels and two slabs, and the thickening
presentation still realizes `E × [0, 1] × [-1/2, 1/2]`. -/
theorem nonempty_homeomorph_coincident (E : Type) [TopologicalSpace E] :
    (1 : ℝ) - halfNN = 0 + halfNN ∧ P01.shiftedCount halfNN = 2 ∧
      Nonempty ((pairThick 0 1 halfNN E one_pos).Realization (P01.shifted halfNN) ≃ₜ
        E × Icc (0 : ℝ) 1 × Band halfNN) :=
  ⟨coincident_events, shiftedCount_P01, ⟨pairThickHomeomorph 0 1 halfNN E one_pos⟩⟩

/-! ### `ε = 0` -/

/-- The grid `0 < 1` lists the events of `[0, 1]` at `ε = 0`. -/
theorem hasEvents_P01_zero : P01.HasEvents 0 1 0 :=
  ⟨⟨0, by simp⟩, ⟨0, by simp⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

/-- **`ε = 0`.** A cylinder point `((y, σ), u)` goes to `(y, u, 0)`. -/
theorem toCylinder_zero (E : Type) [TopologicalSpace E]
    (p : (E × slice 0 1 0 (P01.mid 0)) × Seg P01 0) :
    ((toCylinder 0 1 0 E P01 hasEvents_P01_zero
        ((cylinderThick 0 1 0 E P01 hasEvents_P01_zero).ofCylinder P01 0 p)).2.1 : ℝ) = p.2 ∧
      ((toCylinder 0 1 0 E P01 hasEvents_P01_zero
        ((cylinderThick 0 1 0 E P01 hasEvents_P01_zero).ofCylinder P01 0 p)).2.2 : ℝ) = 0 := by
  have hu : (p.2 : ℝ) ∈ Icc (0 : ℝ) 1 := p.2.2
  have h := fragAff_zero hu (P01.mid 0) p.1.2
  refine ⟨h, ?_⟩
  show (p.2 : ℝ) - fragAff 0 1 ((0 : ℝ≥0) : ℝ) (P01.mid 0) p.2 p.1.2 = 0
  rw [h, sub_self]

/-! ### A vertex strip -/

/-- The grid `1/2 < 3/2`. -/
abbrev Gs : CriticalValues 1 := pair (1 / 2) (3 / 2) (by norm_num)

/-- The grid `1/2 < 3/2` lists the events of the vertex strip `[1, 1]` at `ε = 1/2`. -/
theorem hasEvents_Gs : Gs.HasEvents 1 1 halfNN :=
  ⟨⟨0, by norm_num [Gs]⟩, ⟨1, by norm_num [Gs]⟩, ⟨0, by norm_num [Gs]⟩, ⟨1, by norm_num [Gs]⟩⟩

/-- **Vertex strip.** The vertex point at level `1/2` goes to the band coordinate `-1/2`, so its
height `1 + t` is the level. -/
theorem vertexStripHomeomorph_Gs (E : Type) [TopologicalSpace E] (y : E)
    (h : (1 : ℝ) ∈ slice 1 1 halfNN (Gs.value 0)) :
    vertexStripHomeomorph 1 halfNN E Gs hasEvents_Gs
        ((cylinderThick 1 1 halfNN E Gs hasEvents_Gs).ofVertex Gs 0 (y, ⟨1, h⟩)) =
      (y, ⟨-1 / 2, by norm_num⟩) := by
  refine Prod.ext rfl (Subtype.ext ?_)
  show Gs.value 0 - 1 = -1 / 2
  norm_num [Gs]

/-! ### No Hausdorff hypothesis -/

/-- The pieces for the Sierpiński space are compact. -/
theorem compactSpace_C4_Prop_V (j : Fin 4) : CompactSpace ((C4 Prop).V j) := inferInstance

/-- The pieces for the Sierpiński space are locally path-connected. -/
theorem locallyPathConnectedSpace_C4_Prop_E (k : Fin 3) :
    LocallyPathConnectedSpace ((C4 Prop).E k) :=
  inferInstance

/-- The corner vertex piece for the Sierpiński space is not Hausdorff. -/
theorem not_t2Space_C4_Prop_V_one : ¬ T2Space ((C4 Prop).V 1) := fun h => by
  have h0 : (0 : ℝ) ∈ slice 0 1 halfNN (G4.value 1) := by
    rw [slice_G4_one]
    exact mem_singleton _
  have : T2Space (Prop × slice (0 : ℝ) 1 halfNN (G4.value 1)) := h
  exact TDA.Topology.Examples.not_t2Space_Prop
    (isEmbedding_prodMkLeft (⟨0, h0⟩ : slice (0 : ℝ) 1 halfNN (G4.value 1))).t2Space

/-- **No Hausdorff hypothesis.** The homeomorphism applies to the Sierpiński space. -/
theorem nonempty_homeomorph_Prop :
    Nonempty ((C4 Prop).Realization G4 ≃ₜ Prop × Icc (0 : ℝ) 1 × Band halfNN) :=
  ⟨cylinderThickHomeomorph 0 1 halfNN Prop G4 hasEvents_G4⟩

/-- The realization for the Sierpiński space is not Hausdorff. -/
theorem not_t2Space_C4_Prop : ¬ T2Space ((C4 Prop).Realization G4) := fun _ =>
  TDA.Topology.Examples.not_t2Space_Prop
    (((cylinderThickHomeomorph 0 1 halfNN Prop G4 hasEvents_G4).symm.isEmbedding.comp
      (isEmbedding_prodMkLeft ((⟨0, by norm_num⟩, ⟨0, by norm_num⟩) :
        Icc (0 : ℝ) 1 × Band halfNN))).t2Space)

end Examples.ThickeningCylinder

end

end TDA.Reeb
