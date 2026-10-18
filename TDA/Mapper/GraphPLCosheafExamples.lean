import TDA.Mapper.GraphPLCosheaf
import TDA.Mapper.GraphPLReebDataExamples

/-!
# Constructibility and cosheaf identification of graph-PL height: fixtures

D1. The 4-cycle fixture exhibits the graph-PL path-component precosheaf and its identification
with the corresponding finite Reeb data.

D2. The single-edge fixture exhibits constructibility both at the coarse list `S02` and at the
refinement `S012`, whose middle level carries no vertex.

D3. The subdivided Y-tree gives the same constructibility and cosheaf identification for a
branching graph.

D4. The horizontal-edge fixture records the one-component value at its constant level.

D5. The negative-control fixture shows that the covering hypothesis cannot be dropped: for two
isolated vertices with heights `0` and `2`, `missing_not_covers` records the uncovered height and
constructibility fails.
-/

namespace TDA.Mapper.GraphPLCosheafExamples

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval TDA.Reeb.RGraph
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ edgeGraph_dart pointGraph path3)
open TDA.Mapper.GraphPL
open TDA.Mapper.UniformCoverExamples (d12 d03 c4_edge_cases)
open TDA.Mapper.UniformCoverCellsExamples (Y hY y02 y12 y23 Y_edge_cases Y_vertexCells_one
  Y_vertexCells_other Y_edgeCells)
open TDA.Reeb.Examples.Cylinder (S01 S01_value_zero S01_value_one)
open TDA.Reeb.Examples.ConstructibleCylinder (S0 S012)
open TDA.Reeb.Examples.ConstructibleRepresentation (S02)
open TDA.Reeb.RGraph.Examples (cycleData pathData cycle_not_iso_path)
open TDA.Mapper.GraphPLReebDataExamples

noncomputable section

/-! ## D1. The 4-cycle -/

/-- The graph-PL component precosheaf of the 4-cycle is constructible at `S012`. -/
theorem c4_isConstructibleAt :
    S012.IsConstructibleAt (intervalComponents (plHeight C4 h4)) :=
  isConstructibleAt_intervalComponents_plHeight C4 h4 c4_covers

/-- The finite Reeb cosheaf of the 4-cycle data is identified with its graph-PL component
precosheaf. -/
noncomputable def c4_cosheafIso :
    cycleData.toCosheaf S012 ≅ intervalComponents (plHeight C4 h4) :=
  graphPLCosheafIsoOfIso C4 h4 c4_covers cycleIso

/-- The value of the 4-cycle cosheaf over the middle star has cardinality two. -/
theorem c4_cosheaf_card_J1 :
    Nat.card ((cycleData.toCosheaf S012).obj (S012.J 1)) = 2 := by
  exact (Nat.card_congr ((c4_cosheafIso.app (S012.J 1)).toEquiv)).trans c4_star_one_card

/-! ## D2. The single edge -/

/-- The single-edge component precosheaf is constructible at the coarse list `S02`. -/
theorem edge_isConstructibleAt_S02 :
    S02.IsConstructibleAt (intervalComponents (plHeight edgeGraph h02)) :=
  isConstructibleAt_intervalComponents_plHeight edgeGraph h02 edge_covers_S02

/-- The single-edge component precosheaf is constructible at the refinement `S012`, whose level
one carries no vertex. -/
theorem edge_isConstructibleAt_S012 :
    S012.IsConstructibleAt (intervalComponents (plHeight edgeGraph h02)) :=
  isConstructibleAt_intervalComponents_plHeight edgeGraph h02 edge_covers_S012

/-- The finite Reeb cosheaf of the single edge at `S012` is identified with its component
precosheaf. -/
noncomputable def edge_cosheafIso_S012 :
    (graphPLReebData edgeGraph h02 S012).toCosheaf S012 ≅
      intervalComponents (plHeight edgeGraph h02) :=
  graphPLCosheafIso edgeGraph h02 edge_covers_S012

/-! ## D3. The subdivided Y-tree -/

/-- The subdivided Y-tree component precosheaf is constructible at `S0123`. -/
theorem Y_isConstructibleAt :
    S0123.IsConstructibleAt (intervalComponents (plHeight Y hY)) :=
  isConstructibleAt_intervalComponents_plHeight Y hY Y_covers

/-- The finite Reeb cosheaf of the subdivided Y-tree is identified with its component
precosheaf. -/
noncomputable def Y_cosheafIso :
    (graphPLReebData Y hY S0123).toCosheaf S0123 ≅
      intervalComponents (plHeight Y hY) :=
  graphPLCosheafIso Y hY Y_covers

/-! ## D4. The horizontal edge -/

/-- The constant-height horizontal-edge component precosheaf is constructible at `S0`. -/
theorem flatEdge_isConstructibleAt :
    S0.IsConstructibleAt
      (intervalComponents (plHeight edgeGraph (fun _ => (0 : ℝ)))) :=
  isConstructibleAt_intervalComponents_plHeight edgeGraph (fun _ => (0 : ℝ)) const_covers

/-- The finite Reeb cosheaf of the horizontal edge is identified with its component precosheaf. -/
noncomputable def flatEdge_cosheafIso :
    (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0).toCosheaf S0 ≅
      intervalComponents (plHeight edgeGraph (fun _ => (0 : ℝ))) :=
  graphPLCosheafIso edgeGraph (fun _ => (0 : ℝ)) const_covers

/-- The horizontal-edge component value over its level has cardinality one. -/
theorem flatEdge_cosheaf_card :
    Nat.card ((intervalComponents (plHeight edgeGraph (fun _ => (0 : ℝ)))).obj (S0.J 0)) = 1 := by
  calc
    Nat.card ((intervalComponents (plHeight edgeGraph (fun _ => (0 : ℝ)))).obj (S0.J 0)) =
        Nat.card (((graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0).toCosheaf S0).obj
          (S0.J 0)) :=
      (Nat.card_congr ((flatEdge_cosheafIso.app (S0.J 0)).toEquiv)).symm
    _ = Nat.card ((graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0).V 0) :=
      (Nat.card_congr ((graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0).vertexLabel S0 0)).symm
    _ = 1 := flatEdge_count

/-! ## D5. A missing-level boundary -/

section helpers

variable {α : Type*}

private theorem card_one_of {P : α → Prop} {a : α} (ha : P a) (hP : ∀ x, P x → x = a) :
    Nat.card {x // P x} = 1 :=
  Nat.card_eq_one_iff_unique.2
    ⟨⟨fun x y => Subtype.ext ((hP x.1 x.2).trans (hP y.1 y.2).symm)⟩, ⟨⟨a, ha⟩⟩⟩

end helpers

variable {V : Type*} {G : SimpleGraph V}

private theorem induce_mk_injective_of_not_adj {S : Set V}
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) :
    Function.Injective (G.induce S).connectedComponentMk := fun x y hxy => by
  obtain ⟨p⟩ := ConnectedComponent.exact hxy
  cases p with
  | nil => rfl
  | cons hadj _ => exact (hS _ (Subtype.prop _) _ (Subtype.prop _) hadj).elim

private theorem card_induce_of_not_adj {S : Set V} (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) :
    Nat.card (G.induce S).ConnectedComponent = Nat.card S := by
  refine (Nat.card_congr (Equiv.ofBijective (G.induce S).connectedComponentMk
    ⟨induce_mk_injective_of_not_adj hS, fun c => ?_⟩)).symm
  induction c using ConnectedComponent.ind with
  | h v => exact ⟨v, rfl⟩

private theorem card_induce_singleton {S : Set V} {v₀ : V} (hv₀ : v₀ ∈ S)
    (hS : ∀ v ∈ S, v = v₀) : Nat.card (G.induce S).ConnectedComponent = 1 := by
  rw [card_induce_of_not_adj fun x hx y hy hxy => G.loopless.irrefl x
    (by rw [hS x hx, ← hS y hy] at hxy ⊢; exact hxy)]
  exact card_one_of (P := (· ∈ S)) hv₀ hS

private theorem bot_edge_false (e : (⊥ : SimpleGraph V).edgeSet) : False := by
  obtain ⟨d, -⟩ := exists_dartEdge_eq e
  exact d.adj

private theorem missing_ioo_card :
    Nat.card ((intervalComponents (plHeight (⊥ : SimpleGraph Bool) h02)).obj
      (ioo (-1) 1)) = 1 := by
  have : IsEmpty (UncoveredEdge (⊥ : SimpleGraph Bool) h02 (ioo (-1) 1)) :=
    ⟨fun e => bot_edge_false e.1⟩
  have h_induced :
      Nat.card ((⊥ : SimpleGraph Bool).induce
        (h02 ⁻¹' ((ioo (-1) 1 : OpenInterval) : Set ℝ))).ConnectedComponent = 1 :=
    card_induce_singleton (G := (⊥ : SimpleGraph Bool)) (v₀ := false)
      (by
        change h02 false ∈ ioo (-1 : ℝ) 1
        norm_num [h02, mem_ioo])
      (by
        intro v hv
        cases v
        · rfl
        · change h02 true ∈ ioo (-1 : ℝ) 1 at hv
          norm_num [h02, mem_ioo] at hv)
  refine (Nat.card_congr ((preimageComponentsEquiv (⊥ : SimpleGraph Bool) h02 (ioo (-1) 1)).trans
    (cellComponentsEquivSum (⊥ : SimpleGraph Bool) h02 (ioo (-1) 1)))).trans ?_
  rw [Nat.card_sum, h_induced, Nat.card_of_isEmpty]

/-- The component precosheaf for the missing-level boundary is not constructible at `S0`. -/
theorem missing_not_isConstructibleAt :
    ¬ S0.IsConstructibleAt
      (intervalComponents (plHeight (⊥ : SimpleGraph Bool) h02)) := by
  intro hF
  let I : OpenInterval := ioo (-1) 1
  have hIJ : I ≤ S0.J 0 := by
    rw [S0.J_eq_top_of_zero]
    exact le_top
  have hI : (I : Set ℝ).Nonempty := by
    refine ⟨0, ?_⟩
    change (0 : ℝ) ∈ ioo (-1) 1
    norm_num [mem_ioo]
  have hlev : ∀ i, S0.value i ∈ I ↔ S0.value i ∈ S0.J 0 := by
    intro i
    fin_cases i
    rw [S0.J_eq_top_of_zero]
    exact ⟨
      fun _ => by
        change (S0.value 0 : ℝ) ∈ (Set.univ : Set ℝ)
        exact Set.mem_univ _,
      fun _ => by
        change (S0.value 0) ∈ ioo (-1) 1
        simp [S0, mem_ioo]⟩
  have : Finite (((intervalComponents (plHeight (⊥ : SimpleGraph Bool) h02)).obj I)) :=
    hF.finite I
  have hcard := Nat.card_le_card_of_surjective
    ((intervalComponents (plHeight (⊥ : SimpleGraph Bool) h02)).map (homOfLE hIJ))
    (hF.bijective hIJ hI hlev).2
  have hIcard :
      Nat.card ((intervalComponents (plHeight (⊥ : SimpleGraph Bool) h02)).obj I) = 1 := by
    simpa [I] using missing_ioo_card
  rw [missing_star_card, hIcard] at hcard
  omega

end

end TDA.Mapper.GraphPLCosheafExamples
