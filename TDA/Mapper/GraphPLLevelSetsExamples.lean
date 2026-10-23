import TDA.Mapper.GraphPLLevelSets
import TDA.Mapper.GraphPLReebDataExamples

/-!
# Closed level sets of graph-PL height: fixtures

Acceptance fixtures for `TDA.Mapper.GraphPLLevelSets`, covering horizontal levels,
crossing edges, empty levels, level windows, the negative window control, and the
finite Reeb-data corollary.
-/

namespace TDA.Mapper.GraphPLLevelSetsExamples

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ edgeGraph_dart)
open TDA.Mapper.GraphPL
open TDA.Mapper.GraphPLReebDataExamples
open TDA.Mapper.UniformCoverExamples (d12 d03 c4_edge_cases)
open TDA.Reeb.Examples.ConstructibleCylinder (S0 S012)

noncomputable section

/-! ## Local helper lemmas

The corresponding helpers in `GraphPLReebDataExamples` are private there.  These
copies keep the fixture module independent of private declarations in that file.
-/

private theorem card_zero_of {α : Type*} {P : α → Prop} (hP : ∀ x, ¬ P x) :
    Nat.card {x // P x} = 0 := by
  have : IsEmpty {x // P x} := ⟨fun x => hP x.1 x.2⟩
  exact Nat.card_of_isEmpty

private theorem card_two_of {α : Type*} {P : α → Prop} {a b : α} (hab : a ≠ b)
    (ha : P a) (hb : P b) (hP : ∀ x, P x → x = a ∨ x = b) : Nat.card {x // P x} = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h), ?_⟩
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases hP x.1 x.2 with h | h
  · exact .inl (Subtype.ext h)
  · exact .inr (Subtype.ext h)

private theorem induce_mk_injective_of_not_adj {V : Type*} {G : SimpleGraph V}
    {S : Set V} (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) :
    Function.Injective (G.induce S).connectedComponentMk := fun x y hxy => by
  obtain ⟨p⟩ := ConnectedComponent.exact hxy
  cases p with
  | nil => rfl
  | cons hadj _ => exact (hS _ (Subtype.prop _) _ (Subtype.prop _) hadj).elim

private theorem card_induce_empty {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hS : ∀ v, v ∉ S) : Nat.card (G.induce S).ConnectedComponent = 0 := by
  have : IsEmpty (G.induce S).ConnectedComponent :=
    ⟨fun c => by
      induction c using ConnectedComponent.ind with
      | h v => exact hS v.1 v.2⟩
  exact Nat.card_of_isEmpty

private theorem not_edgeCrosses_of_ge {V : Type*} {G : SimpleGraph V} {h : V → ℝ}
    {c : ℝ} (hc : ∀ v, h v ≤ c) (e : G.edgeSet) : ¬ EdgeCrosses G h c e :=
  fun ⟨d, _, _, hmax⟩ => by
    rcases max_choice (h d.fst) (h d.snd) with hm | hm <;> rw [hm] at hmax <;>
      linarith [hc d.fst, hc d.snd]

private theorem card_levelVertex {V : Type*} [Finite V] (G : SimpleGraph V) (h : V → ℝ) (c : ℝ)
    {m k : ℕ} (hm : Nat.card (G.induce {v | h v = c}).ConnectedComponent = m)
    (hk : Nat.card {e : G.edgeSet // EdgeCrosses G h c e} = k) :
    Nat.card (LevelVertex G h c) = m + k := by
  classical
  let _ := Fintype.ofFinite V
  rw [Nat.card_sum, hm, hk]

private theorem c4_level_not_adj (c : ℝ) :
    ∀ x ∈ {v | h4 v = c}, ∀ y ∈ {v | h4 v = c}, ¬ C4.Adj x y := by
  intro x hx y hy hadj
  have hxy : h4 x = h4 y := hx.trans hy.symm
  fin_cases x <;> fin_cases y <;>
    first | exact absurd hadj (by decide) | norm_num [h4] at hxy

private theorem c4_dartEdge_ne {d d' : C4.Dart} (h₁ : d.toProd ≠ d'.toProd)
    (h₂ : d.toProd ≠ d'.toProd.swap) : dartEdge d ≠ dartEdge d' := fun hdd => by
  rcases dartEdge_eq_iff.1 hdd with h | h
  · exact h₁ (congrArg Dart.toProd h)
  · exact h₂ (congrArg Dart.toProd h)

private theorem c4_card_level_one :
    Nat.card (C4.induce {v | h4 v = 1}).ConnectedComponent = 2 := by
  have hm := c4_level_one.1
  rw [show S012.value 1 = (1 : ℝ) by norm_num] at hm
  exact hm

private theorem S012_one_value : S012.value 1 = (1 : ℝ) := by
  show ((1 : ℕ) : ℝ) = 1
  norm_num

private theorem c4_not_crosses_one (e : C4.edgeSet) :
    ¬ EdgeCrosses C4 h4 1 e := by
  have he := c4_level_one.2 e
  simpa only [show S012.value 1 = (1 : ℝ) by norm_num] using he

private theorem h02_crosses_one :
    EdgeCrosses edgeGraph h02 1 (dartEdge d₀) := by
  simpa only [show S012.value 1 = (1 : ℝ) by norm_num] using edge_crosses_one

private theorem h02_midpoint_mem :
    plHeight edgeGraph h02 (edgePoint edgeGraph d₀
      ⟨1 / 2, by norm_num, by norm_num⟩) ∈ ({1} : Set ℝ) := by
  rw [plHeight_edgePoint, dartHeight_d₀]
  norm_num

private theorem flat_midpoint_mem :
    plHeight edgeGraph (fun _ => (0 : ℝ)) (edgePoint edgeGraph d₀
      ⟨1 / 2, by norm_num, by norm_num⟩) ∈ ({0} : Set ℝ) := by
  rw [plHeight_edgePoint, dartHeight_of_eq (fun _ => (0 : ℝ)) rfl]
  simp

/-! ## L1. The 4-cycle at level `1` -/

/-- The closed level of the C4 height at `1` has two path components. -/
theorem c4_level_one_card :
    Nat.card (ZerothHomotopy (ClosedLevel C4 h4 1)) = 2 := by
  calc
    Nat.card (ZerothHomotopy (ClosedLevel C4 h4 1)) = Nat.card (LevelVertex C4 h4 1) :=
      Nat.card_congr (closedLevelComponentsEquiv C4 h4 1)
    _ = 2 + 0 := card_levelVertex C4 h4 1 c4_card_level_one
      (card_zero_of c4_not_crosses_one)
    _ = 2 := by norm_num

/-- The level-one classes of C4's vertices `1` and `3` are distinct. -/
theorem c4_level_one_ne :
    (ZerothHomotopy.mk
        (⟨vertex C4 1, by rw [plHeight_vertex, h4_one]; simp⟩ : ClosedLevel C4 h4 1)) ≠
      (ZerothHomotopy.mk
        (⟨vertex C4 3, by rw [plHeight_vertex, h4_three]; simp⟩ : ClosedLevel C4 h4 1)) := by
  intro hneq
  have hcomp := congrArg (closedLevelComponentsEquiv C4 h4 1) hneq
  rw [closedLevelComponentsEquiv_mk_vertex C4 h4 1 h4_one,
    closedLevelComponentsEquiv_mk_vertex C4 h4 3 h4_three] at hcomp
  have hvert := induce_mk_injective_of_not_adj (G := C4)
    (S := {v | h4 v = 1}) (c4_level_not_adj 1) (Sum.inl.inj hcomp)
  exact absurd (congrArg Subtype.val hvert) (by decide : ((1 : Fin 4) ≠ 3))

/-! ## L2. A horizontal edge -/

/-- The constant-height single edge has one closed-level component. -/
theorem flat_level_card :
    Nat.card (ZerothHomotopy
      (ClosedLevel edgeGraph (fun _ => (0 : ℝ)) 0)) = 1 := by
  calc
    Nat.card (ZerothHomotopy
        (ClosedLevel edgeGraph (fun _ => (0 : ℝ)) 0)) =
        Nat.card (LevelVertex edgeGraph (fun _ => (0 : ℝ)) 0) :=
      Nat.card_congr (closedLevelComponentsEquiv edgeGraph (fun _ => (0 : ℝ)) 0)
    _ = Nat.card ((graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0).V 0) := by
      rfl
    _ = 1 := flatEdge_count

/-- The midpoint of the horizontal edge is in the class of its false endpoint. -/
theorem flat_midpoint_class :
    (ZerothHomotopy.mk
        (⟨edgePoint edgeGraph d₀ ⟨1 / 2, by norm_num, by norm_num⟩,
          flat_midpoint_mem⟩ : ClosedLevel edgeGraph (fun _ => (0 : ℝ)) 0)) =
      ZerothHomotopy.mk
        (⟨vertex edgeGraph false, by rw [plHeight_vertex]; simp⟩ :
          ClosedLevel edgeGraph (fun _ => (0 : ℝ)) 0) := by
  symm
  exact TDA.Topology.mk_eq_of_joinedIn (plHeight edgeGraph (fun _ => (0 : ℝ)))
    ({0} : Set ℝ)
    (joinedIn_level_of_eq edgeGraph (fun _ => (0 : ℝ)) rfl rfl
      ⟨1 / 2, by norm_num, by norm_num⟩)
    (by rw [plHeight_vertex]; simp) flat_midpoint_mem

/-! ## L3. A crossing edge -/

/-- The height-one closed level of the single edge has one component. -/
theorem crossing_level_card :
    Nat.card (ZerothHomotopy (ClosedLevel edgeGraph h02 1)) = 1 := by
  calc
    Nat.card (ZerothHomotopy (ClosedLevel edgeGraph h02 1)) =
        Nat.card (LevelVertex edgeGraph h02 1) :=
      Nat.card_congr (closedLevelComponentsEquiv edgeGraph h02 1)
    _ = Nat.card ((graphPLReebData edgeGraph h02 S012).V 1) := by
      rw [graphPLReebData_V, S012_one_value]
    _ = 1 := edge_S012_V1.2

/-- The crossing point of the single edge is its midpoint. -/
theorem crossing_midpoint_eq :
    edgePoint edgeGraph d₀ ⟨1 / 2, by norm_num, by norm_num⟩ =
      (crossingPoint edgeGraph h02 ⟨dartEdge d₀, h02_crosses_one⟩).1 := by
  exact eq_crossingPoint edgeGraph h02 ⟨dartEdge d₀, h02_crosses_one⟩ d₀ rfl
    ⟨1 / 2, by norm_num, by norm_num⟩ (by rw [dartHeight_d₀]; norm_num)

/-- The closed-level classification sends the crossing midpoint to the crossing branch. -/
theorem crossing_midpoint :
    closedLevelComponentsEquiv edgeGraph h02 1
        (ZerothHomotopy.mk
          (⟨edgePoint edgeGraph d₀ ⟨1 / 2, by norm_num, by norm_num⟩,
            h02_midpoint_mem⟩ : ClosedLevel edgeGraph h02 1)) =
      Sum.inr ⟨dartEdge d₀, h02_crosses_one⟩ := by
  have hp :
      (⟨edgePoint edgeGraph d₀ ⟨1 / 2, by norm_num, by norm_num⟩,
          h02_midpoint_mem⟩ : ClosedLevel edgeGraph h02 1) =
        crossingPoint edgeGraph h02 ⟨dartEdge d₀, h02_crosses_one⟩ := by
    apply Subtype.ext
    exact crossing_midpoint_eq
  exact (congrArg (fun p : ClosedLevel edgeGraph h02 1 =>
      closedLevelComponentsEquiv edgeGraph h02 1 (ZerothHomotopy.mk p)) hp).trans
    (closedLevelComponentsEquiv_crossingPoint edgeGraph h02
      ⟨dartEdge d₀, h02_crosses_one⟩)

/-! ## L4. C4 at a level with no vertex -/

private theorem c4_half_no_vertex (v : Fin 4) : h4 v ≠ (1 / 2 : ℝ) := by
  fin_cases v <;> norm_num [h4]

private theorem c4_three_no_vertex (v : Fin 4) : h4 v ≠ (3 : ℝ) := by
  fin_cases v <;> norm_num [h4]

private theorem c4_half_crosses_d01 :
    EdgeCrosses C4 h4 (1 / 2) (dartEdge d01) := by
  rw [edgeCrosses_dartEdge_iff]
  norm_num [d01, h4]

private theorem c4_half_crosses_d03 :
    EdgeCrosses C4 h4 (1 / 2) (dartEdge d03) := by
  rw [edgeCrosses_dartEdge_iff]
  norm_num [d03, h4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_succ]

private theorem c4_half_not_crosses_d12 :
    ¬ EdgeCrosses C4 h4 (1 / 2) (dartEdge d12) := by
  rw [edgeCrosses_dartEdge_iff]
  norm_num [d12, h4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_succ]

private theorem c4_half_not_crosses_d23 :
    ¬ EdgeCrosses C4 h4 (1 / 2) (dartEdge d23) := by
  rw [edgeCrosses_dartEdge_iff]
  norm_num [d23, h4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_succ]

private theorem c4_half_crossing_cases (e : C4.edgeSet)
    (he : EdgeCrosses C4 h4 (1 / 2) e) :
    e = dartEdge d01 ∨ e = dartEdge d03 := by
  rcases c4_edge_cases e with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact (c4_half_not_crosses_d12 he).elim
  · exact (c4_half_not_crosses_d23 he).elim
  · exact .inr rfl

private theorem c4_d01_ne_d03 : dartEdge d01 ≠ dartEdge d03 :=
  c4_dartEdge_ne (by decide) (by decide)

private theorem c4_half_crossing_card :
    Nat.card {e : C4.edgeSet // EdgeCrosses C4 h4 (1 / 2) e} = 2 :=
  card_two_of c4_d01_ne_d03 c4_half_crosses_d01 c4_half_crosses_d03
    c4_half_crossing_cases

/-- The C4 level at `1/2` has two path components, one for each crossing edge. -/
theorem c4_half_card :
    Nat.card (ZerothHomotopy (ClosedLevel C4 h4 (1 / 2))) = 2 := by
  calc
    Nat.card (ZerothHomotopy (ClosedLevel C4 h4 (1 / 2))) =
        Nat.card (LevelVertex C4 h4 (1 / 2)) :=
      Nat.card_congr (closedLevelComponentsEquiv C4 h4 (1 / 2))
    _ = 0 + 2 := card_levelVertex C4 h4 (1 / 2)
      (card_induce_empty c4_half_no_vertex) c4_half_crossing_card
    _ = 2 := by norm_num

/-- The two crossing points at level `1/2` lie in distinct path components. -/
theorem c4_half_crossing_ne :
    (ZerothHomotopy.mk (crossingPoint C4 h4 ⟨dartEdge d01, c4_half_crosses_d01⟩) :
      ZerothHomotopy (ClosedLevel C4 h4 (1 / 2))) ≠
    ZerothHomotopy.mk (crossingPoint C4 h4 ⟨dartEdge d03, c4_half_crosses_d03⟩) := by
  intro hneq
  have hcomp := congrArg (closedLevelComponentsEquiv C4 h4 (1 / 2)) hneq
  rw [closedLevelComponentsEquiv_crossingPoint C4 h4,
    closedLevelComponentsEquiv_crossingPoint C4 h4] at hcomp
  have heq : (⟨dartEdge d01, c4_half_crosses_d01⟩ :
      {e : C4.edgeSet // EdgeCrosses C4 h4 (1 / 2) e}) =
      ⟨dartEdge d03, c4_half_crosses_d03⟩ := Sum.inr.inj hcomp
  exact c4_d01_ne_d03 (congrArg Subtype.val heq)

/-! ## L5. The empty boundary level -/

/-- The C4 closed level at height `3` has no path components. -/
theorem c4_three_empty :
    IsEmpty (ZerothHomotopy (ClosedLevel C4 h4 3)) := by
  apply (closedLevelComponentsEquiv C4 h4 3).isEmpty_congr.mpr
  refine ⟨fun y => ?_⟩
  rcases y with y | e
  · induction y using ConnectedComponent.ind with
    | h v =>
      exact c4_three_no_vertex v.1 v.2
  · exact (not_edgeCrosses_of_ge (h := h4) (c := 3) (fun v => by
      fin_cases v <;> norm_num [h4]) e.1 e.2).elim

/-! ## L6. A positive level window -/

/-- The interval `I4` is a level window for C4 at height `1`. -/
theorem I4_isLevelWindow : IsLevelWindow h4 1 I4 := by
  constructor
  · simpa [h4_one] using one_mem_I4
  · intro v hv
    rcases h4_mem_I4.1 hv with rfl | rfl <;> simp [h4]

/-- Inclusion into `I4` is bijective on C4 level-one path components. -/
theorem I4_bijective :
    Function.Bijective
      (componentMap (levelInclusion C4 h4 I4_isLevelWindow.1)) :=
  componentMap_levelInclusion_bijective C4 h4 I4_isLevelWindow

/-! ## L7. A window containing another vertex height -/

private theorem J4_one_mem : (1 : ℝ) ∈ J4 := by
  rw [mem_ioo]
  norm_num

/-- `J4` is not a level window at height `1`, because it contains height `0`. -/
theorem J4_not_isLevelWindow : ¬ IsLevelWindow h4 1 J4 := by
  intro hJ
  have h0 := hJ.2 0 (h4_mem_J4 0)
  norm_num [h4] at h0

/-- The inclusion into `J4` is not injective on C4 level-one path components. -/
theorem J4_not_injective :
    ¬ Function.Injective
      (componentMap (levelInclusion C4 h4 (c := 1) (I := J4) J4_one_mem)) := by
  intro hinj
  let z1 : ZerothHomotopy (ClosedLevel C4 h4 1) :=
    ZerothHomotopy.mk
      (⟨vertex C4 1, by rw [plHeight_vertex, h4_one]; simp⟩ : ClosedLevel C4 h4 1)
  let z3 : ZerothHomotopy (ClosedLevel C4 h4 1) :=
    ZerothHomotopy.mk
      (⟨vertex C4 3, by rw [plHeight_vertex, h4_three]; simp⟩ : ClosedLevel C4 h4 1)
  have hz1 : componentMap (levelInclusion C4 h4 I4_isLevelWindow.1) z1 = x1 := by
    dsimp [z1, x1]
    apply congrArg ZerothHomotopy.mk
    exact Subtype.ext rfl
  have hz3 : componentMap (levelInclusion C4 h4 I4_isLevelWindow.1) z3 = x3 := by
    dsimp [z3, x3]
    apply congrArg ZerothHomotopy.mk
    exact Subtype.ext rfl
  have hI4J : (I4 : Set ℝ) ⊆ (J4 : Set ℝ) :=
    OpenInterval.le_iff_subset.1 I4_le_J4
  have hinc :
      levelInclusion C4 h4 J4_one_mem =
        (TDA.Topology.preimageSetInclusion (plHeight C4 h4) hI4J).comp
          (levelInclusion C4 h4 I4_isLevelWindow.1) := by
    exact ContinuousMap.ext (fun _ => rfl)
  have hcomp :
      componentMap (levelInclusion C4 h4 J4_one_mem) =
        componentMap (TDA.Topology.preimageSetInclusion (plHeight C4 h4) hI4J) ∘
          componentMap (levelInclusion C4 h4 I4_isLevelWindow.1) := by
    rw [hinc, componentMap_comp]
  have hmerge :
      componentMap (TDA.Topology.preimageSetInclusion (plHeight C4 h4) hI4J) x1 =
        componentMap (TDA.Topology.preimageSetInclusion (plHeight C4 h4) hI4J) x3 := by
    change
      componentMap (TDA.Reeb.preimageInclusion (plHeight C4 h4)
          (toOpens_le_iff.2 I4_le_J4)) x1 =
        componentMap (TDA.Reeb.preimageInclusion (plHeight C4 h4)
          (toOpens_le_iff.2 I4_le_J4)) x3
    exact c4_J_preimage_merge
  have hmap : componentMap (levelInclusion C4 h4 J4_one_mem) z1 =
      componentMap (levelInclusion C4 h4 J4_one_mem) z3 := by
    have h1 := congrFun hcomp z1
    have h3 := congrFun hcomp z3
    change componentMap (levelInclusion C4 h4 J4_one_mem) z1 =
      componentMap (TDA.Topology.preimageSetInclusion (plHeight C4 h4) hI4J)
        (componentMap (levelInclusion C4 h4 I4_isLevelWindow.1) z1) at h1
    change componentMap (levelInclusion C4 h4 J4_one_mem) z3 =
      componentMap (TDA.Topology.preimageSetInclusion (plHeight C4 h4) hI4J)
        (componentMap (levelInclusion C4 h4 I4_isLevelWindow.1) z3) at h3
    rw [hz1] at h1
    rw [hz3] at h3
    exact h1.trans (hmerge.trans h3.symm)
  exact c4_level_one_ne (by simpa [z1, z3] using hinj hmap)

/-! ## L8. The finite Reeb-data corollary -/

/-- The level-one Reeb-data vertex type has the closed-level cardinality. -/
theorem c4_reeb_V1_card :
    Nat.card ((graphPLReebData C4 h4 S012).V 1) =
      Nat.card (ZerothHomotopy (ClosedLevel C4 h4 (S012.value 1))) :=
  Nat.card_congr (graphPLReebDataVEquivClosedLevel C4 h4 S012 1)

/-- The C4 star classification factors through the closed-level classification. -/
theorem c4_star_triangle :
    graphPLStarEquiv C4 h4 S012 c4_covers 1 ∘
        componentMap (levelInclusion C4 h4 (S012.value_mem_J 1)) =
      closedLevelComponentsEquiv C4 h4 (S012.value 1) :=
  graphPLStarEquiv_comp_componentMap_levelInclusion C4 h4 S012 c4_covers 1

end
end TDA.Mapper.GraphPLLevelSetsExamples
