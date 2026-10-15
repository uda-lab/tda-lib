import TDA.Reeb.ConstructibleQuotient
import TDA.Reeb.RGraphExamples
import TDA.Reeb.ConstructibleCylinderExamples

/-!
# Examples: constructible Reeb quotients and component graphs

The fixtures use actual presentations with compact locally path-connected pieces, their
realizations, and actual slice morphisms.

* `[0, 1]` is locally path-connected and path-connected. The pinned mathlib has no instance for
  `unitInterval`, so both are local instances here.
* Constant-height interval: `[0, 1]` at the single level of `S0` has the two distinct raw points
  `0` and `1` but one Reeb class. The quotient and the vertex set of its component data have one
  element, and the quotient is a graph object.
* Thickening: `thicken D` replaces every vertex and edge label of finite data `D` by
  `label × [0, 1]`, with the endpoint maps acting on the label. Its component data are isomorphic
  to `D` (`thickenIso`), its Reeb quotient is the graph object of `D` (`thickenQuotientIso`), and
  it is a constructible ℝ-space.
* Empty pieces: the thickening of empty data has an empty Reeb quotient, isomorphic to the empty
  graph.
* Two unattached connected pieces: two disjoint intervals at the single level of `S0` remain two
  distinct vertices, and the quotient has exactly two points.
* Noninjective attaching maps: in the thickened pinch, the left endpoint map is not injective on
  points or on components. Two different raw bottom ends share a Reeb class, while the two edges
  at a regular height and the two top vertices stay apart. The quotient is the pinch graph.
* Parallel edge components: in the thickened parallel edges both edge components have the same
  endpoints and stay apart at every regular height and interval coordinate, and the quotient is
  not isomorphic to a single edge.
* Transport and different critical lists: the single edge refined over `0 < 1/2 < 1`, presented
  over `0 < 1` through the refinement isomorphism, has a graph-object quotient. Its identity,
  with the presentations over `0 < 1` and over `0 < 1/2 < 1`, induces a graph map between the two
  component graphs, and the comparison square holds.
* A height-dependent self-map: the twist of the thickened parallel edges is the identity on vertex
  pieces and, on the cylinder, swaps the two edges and moves the interval coordinate by
  `s + t (1 - t) (1 - s)`. Its regular fiber maps at `1/2` and `3/4` differ pointwise, while its
  component data map is the edge swap, not the identity. The naturality square is computed on strip
  points and holds in the slice.
* Generator formulas on the thickened pinch: the forward strip and cylinder formulas and the
  inverse vertex formula, with their heights.
* Graph case: for the parallel edges, the projection homeomorphism followed by the comparison is
  the realization of the canonical data isomorphism, also in the slice. The functor to graph
  objects is applied to the thickened pinch.
-/

open Set Topology CategoryTheory

namespace TDA.Reeb

noncomputable section

namespace Examples.ConstructibleQuotient

open CylinderPresentation TDA.Reeb.Examples.Cylinder
open TDA.Reeb.Examples.ConstructibleCylinder (S0 D0 threeQuarters)

/-! ### `[0, 1]` as a piece -/

/-- `[0, 1]` is locally path-connected (pinned mathlib has no instance for `unitInterval`). -/
theorem locallyPathConnectedSpace_unitInterval : LocallyPathConnectedSpace unitInterval := by
  refine LocallyPathConnectedSpace.of_bases (p := fun _ (ε : ℝ) => 0 < ε)
    (s := fun x ε => ((↑) : unitInterval → ℝ) ⁻¹' Ioo ((x : ℝ) - ε) (x + ε)) (fun x => ?_)
    fun x ε hε => ?_
  · rw [nhds_subtype]
    exact (nhds_basis_Ioo_pos (x : ℝ)).comap _
  · have hW : IsPathConnected (Icc (0 : ℝ) 1 ∩ Ioo ((x : ℝ) - ε) (x + ε)) :=
      ((convex_Icc (𝕜 := ℝ) _ _).inter (convex_Ioo _ _)).isPathConnected
        ⟨(x : ℝ), x.2, by constructor <;> linarith⟩
    have := hW.preimage_coe (U := Icc (0 : ℝ) 1) inter_subset_left
    rwa [Subtype.preimage_coe_self_inter] at this

attribute [local instance] locallyPathConnectedSpace_unitInterval

theorem pathConnectedSpace_unitInterval : PathConnectedSpace unitInterval :=
  PathConnectedSpace.of_locallyPathConnectedSpace

attribute [local instance] pathConnectedSpace_unitInterval

/-! ### A constant-height interval collapses to a point -/

/-- The interval `[0, 1]` at the single level of `S0`, with no edges. -/
def intervalPres : CylinderPresentation.{0} 0 where
  V _ := unitInterval
  E e := e.elim0
  topE e := e.elim0
  left e := e.elim0
  right e := e.elim0

instance intervalPres_compactSpace_V (i : Fin 1) : CompactSpace (intervalPres.V i) :=
  inferInstanceAs (CompactSpace unitInterval)

instance intervalPres_lpc_V (i : Fin 1) : LocallyPathConnectedSpace (intervalPres.V i) :=
  inferInstanceAs (LocallyPathConnectedSpace unitInterval)

instance intervalPres_pathConnected_V (i : Fin 1) : PathConnectedSpace (intervalPres.V i) :=
  inferInstanceAs (PathConnectedSpace unitInterval)

instance intervalPres_compactSpace_E (e : Fin 0) : CompactSpace (intervalPres.E e) := e.elim0

instance intervalPres_lpc_E (e : Fin 0) : LocallyPathConnectedSpace (intervalPres.E e) := e.elim0

/-- The raw space has the two distinct points `0` and `1` over the single level. -/
theorem interval_ofVertex_zero_ne_one :
    intervalPres.ofVertex S0 0 (0 : unitInterval) ≠ intervalPres.ofVertex S0 0 (1 : unitInterval) :=
  fun h => by simpa using congrArg Subtype.val (intervalPres.ofVertex_injective S0 0 h)

/-- In the Reeb quotient every point of the interval has the same class. -/
theorem interval_collapse (a b : unitInterval) :
    ReebQuotient.mk (intervalPres.height S0) (intervalPres.ofVertex S0 0 a) =
      ReebQuotient.mk (intervalPres.height S0) (intervalPres.ofVertex S0 0 b) :=
  intervalPres.quotientComponentGraphMap_injective S0
    (congrArg ((ofFiniteData intervalPres.componentData).ofVertex S0 0)
      (intervalPres.vertexClass_eq_iff.2 (PathConnectedSpace.joined a b)))

/-- The quotient is a single point. -/
theorem interval_quotient_card : Nat.card (ReebQuotient (intervalPres.height S0)) = 1 := by
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun q q' => ?_⟩,
    ⟨ReebQuotient.mk _ (intervalPres.ofVertex S0 0 (0 : unitInterval))⟩⟩
  induction q using ReebQuotient.ind with
  | h x =>
    induction q' using ReebQuotient.ind with
    | h x' =>
      obtain ⟨a, rfl⟩ := ofVertex_surjective_zero S0 intervalPres x
      obtain ⟨b, rfl⟩ := ofVertex_surjective_zero S0 intervalPres x'
      exact interval_collapse a b

/-- Its component data has one vertex. -/
theorem interval_componentData_card : Nat.card (intervalPres.componentData.V 0) = 1 :=
  Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨ZerothHomotopy.mk (0 : unitInterval)⟩⟩

/-- The quotient is a graph object. -/
theorem interval_isRGraph :
    RGraph.IsRGraph ((ReebQuotient.quotientFunctor ℝ).obj
      (Over.mk (TopCat.ofHom (intervalPres.height S0)))) :=
  RGraph.isRGraph_quotient S0 intervalPres (Iso.refl _)

/-! ### Thickened finite data -/

section thicken

variable {n : ℕ}

/-- Thicken finite data by `[0, 1]`: pieces `V i × [0, 1]` and `E e × [0, 1]` with discrete labels;
the endpoint maps act on the label and keep the interval coordinate. Every piece is compact,
locally path-connected and positive-dimensional. -/
abbrev thicken (D : FiniteReebData.{0} n) : CylinderPresentation.{0} n where
  V i := (ofFiniteData D).V i × unitInterval
  E e := (ofFiniteData D).E e × unitInterval
  left e := ((ofFiniteData D).left e).prodMap (ContinuousMap.id unitInterval)
  right e := ((ofFiniteData D).right e).prodMap (ContinuousMap.id unitInterval)

/-- `a ↦ [(a, 0)]` is a bijection `A → π₀ (A × [0, 1])` for discrete `A`. -/
theorem mk_prod_zero_bijective (A : Type) [TopologicalSpace A] [DiscreteTopology A] :
    Function.Bijective fun a : A =>
      (ZerothHomotopy.mk (a, (0 : unitInterval)) : ZerothHomotopy (A × unitInterval)) := by
  refine ⟨fun a a' h => ?_, fun c => ?_⟩
  · exact joined_eq_of_discrete ((Quotient.exact h : Joined _ _).map continuous_fst)
  · induction c using ZerothHomotopy.rec with
    | mk p =>
      exact ⟨p.1, ZerothHomotopy.sound
        ((Path.refl p.1).prod (PathConnectedSpace.somePath (0 : unitInterval) p.2))⟩

/-- Vertex classes of a thickening are labelled by the first coordinate. -/
theorem thicken_vertexClass_eq_iff (D : FiniteReebData.{0} n) (i : Fin (n + 1))
    (a a' : (ofFiniteData D).V i) (s s' : unitInterval) :
    (thicken D).vertexClass i (a, s) = (thicken D).vertexClass i (a', s') ↔ a = a' := by
  rw [vertexClass_eq_iff]
  constructor
  · intro h
    exact joined_eq_of_discrete (h.map continuous_fst)
  · rintro rfl
    exact ⟨(Path.refl a).prod (PathConnectedSpace.somePath s s')⟩

/-- Edge classes of a thickening are labelled by the first coordinate. -/
theorem thicken_edgeClass_eq_iff (D : FiniteReebData.{0} n) (k : Fin n)
    (a a' : (ofFiniteData D).E k) (s s' : unitInterval) :
    (thicken D).edgeClass k (a, s) = (thicken D).edgeClass k (a', s') ↔ a = a' := by
  rw [edgeClass_eq_iff]
  constructor
  · intro h
    exact joined_eq_of_discrete (h.map continuous_fst)
  · rintro rfl
    exact ⟨(Path.refl a).prod (PathConnectedSpace.somePath s s')⟩

/-- The canonical data map `D ⟶ π₀`-data of the thickening, `x ↦ [(x, 0)]`. -/
def thickenUnit (D : FiniteReebData.{0} n) : D.Hom (thicken D).componentData where
  v i x := ZerothHomotopy.mk (X := (thicken D).V i) (x, 0)
  e k y := ZerothHomotopy.mk (X := (thicken D).E k) (y, 0)
  left_comm _ _ := rfl
  right_comm _ _ := rfl

/-- The thickening has the component data of `D`. -/
def thickenIso (D : FiniteReebData.{0} n) : D ≅ (thicken D).componentData where
  hom := thickenUnit D
  inv := (thickenUnit D).inv (fun i => mk_prod_zero_bijective ((ofFiniteData D).V i))
    (fun k => mk_prod_zero_bijective ((ofFiniteData D).E k))
  hom_inv_id := FiniteReebData.Hom.comp_inv _ _ _
  inv_hom_id := FiniteReebData.Hom.inv_comp _ _ _

/-- The Reeb quotient of the thickening is the graph object of `D`. -/
def thickenQuotientIso (S : CriticalValues n) (D : FiniteReebData.{0} n) :
    (ReebQuotient.quotientFunctor ℝ).obj (Over.mk (TopCat.ofHom ((thicken D).height S))) ≅
      RGraph.toOver S D :=
  (thicken D).quotientOverIso S ≪≫ (RGraph.realizationFunctor S).mapIso (thickenIso D).symm

/-- The thickening is a constructible ℝ-space. -/
theorem thicken_isConstructibleSpace (S : CriticalValues n) (D : FiniteReebData.{0} n) :
    IsConstructibleSpace (Over.mk (TopCat.ofHom ((thicken D).height S))) :=
  ⟨n, S, thicken D, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, ⟨Iso.refl _⟩⟩

end thicken

/-! ### Empty pieces -/

/-- With empty pieces the realization, hence the Reeb quotient, is empty; the comparison still
applies (its component data is empty). -/
theorem emptyThick_quotient_isEmpty : IsEmpty (ReebQuotient ((thicken (emptyData 1)).height S01)) :=
  haveI := (thicken (emptyData 1)).isEmpty_realization S01
  inferInstance

/-- The empty thickening is a constructible ℝ-space whose Reeb quotient is the empty graph. -/
def emptyThick_quotientIso :
    (ReebQuotient.quotientFunctor ℝ).obj
        (Over.mk (TopCat.ofHom ((thicken (emptyData 1)).height S01))) ≅
      RGraph.toOver S01 (emptyData 1) :=
  thickenQuotientIso S01 (emptyData 1)

/-! ### Two unattached connected pieces at one level remain two vertices -/

/-- `D0` has two vertices at the single level and no edge; its thickening is two disjoint
intervals at height `0`. -/
abbrev twoPieces : CylinderPresentation.{0} 0 := thicken D0

/-- The two vertex pieces of `twoPieces`, as points of the realization. -/
abbrev twoPt (b : Fin 2) (s : unitInterval) : twoPieces.Realization S0 :=
  twoPieces.ofVertex S0 0 (b, s)

theorem twoPieces_ne :
    ReebQuotient.mk (twoPieces.height S0) (twoPt 0 0) ≠
      ReebQuotient.mk (twoPieces.height S0) (twoPt 1 0) := fun h => by
  have h1 : (ofFiniteData twoPieces.componentData).ofVertex S0 0
        (twoPieces.vertexClass 0 ((0 : Fin 2), (0 : unitInterval))) =
      (ofFiniteData twoPieces.componentData).ofVertex S0 0
        (twoPieces.vertexClass 0 ((1 : Fin 2), (0 : unitInterval))) :=
    congrArg (twoPieces.quotientComponentGraphMap S0) h
  have h2 : (0 : Fin 2) = 1 :=
    (thicken_vertexClass_eq_iff D0 0 _ _ 0 0).1
      ((ofFiniteData twoPieces.componentData).ofVertex_injective S0 0 h1)
  exact absurd h2 (by decide)

theorem twoPieces_collapse (b : Fin 2) (s : unitInterval) :
    ReebQuotient.mk (twoPieces.height S0) (twoPt b s) =
      ReebQuotient.mk (twoPieces.height S0) (twoPt b 0) :=
  twoPieces.quotientComponentGraphMap_injective S0
    (congrArg ((ofFiniteData twoPieces.componentData).ofVertex S0 0)
      ((thicken_vertexClass_eq_iff D0 0 b b s 0).2 rfl))

theorem twoPieces_cases (q : ReebQuotient (twoPieces.height S0)) :
    q = ReebQuotient.mk _ (twoPt 0 0) ∨ q = ReebQuotient.mk _ (twoPt 1 0) := by
  induction q using ReebQuotient.ind with
  | h x =>
    obtain ⟨⟨a, s⟩, rfl⟩ := ofVertex_surjective_zero S0 twoPieces x
    have key : ∀ b : Fin 2, ∀ s : unitInterval,
        ReebQuotient.mk (twoPieces.height S0) (twoPt b s) = ReebQuotient.mk _ (twoPt 0 0) ∨
          ReebQuotient.mk (twoPieces.height S0) (twoPt b s) = ReebQuotient.mk _ (twoPt 1 0) := by
      intro b s
      rw [twoPieces_collapse b s]
      exact (Fin.forall_fin_two (p := fun b : Fin 2 =>
        ReebQuotient.mk (twoPieces.height S0) (twoPt b 0) = ReebQuotient.mk _ (twoPt 0 0) ∨
          ReebQuotient.mk (twoPieces.height S0) (twoPt b 0) =
            ReebQuotient.mk _ (twoPt 1 0))).2 ⟨Or.inl rfl, Or.inr rfl⟩ b
    exact key a s

/-- Exactly two vertices. -/
theorem twoPieces_quotient_card : Nat.card (ReebQuotient (twoPieces.height S0)) = 2 :=
  Nat.card_eq_two_iff.2 ⟨_, _, twoPieces_ne, Set.eq_univ_of_forall fun q => by
    rcases twoPieces_cases q with h | h <;> simp [h]⟩

/-! ### Noninjective attaching maps -/

/-- The thickened pinch over `S01 = {0, 1}`: `V = Bool × [0, 1]` at both levels and
`E 0 = Bool × [0, 1]`. The left endpoint map `(b, s) ↦ (false, s)` sends both edge pieces to one
vertex piece; the right endpoint map is the identity. -/
abbrev pinchI : CylinderPresentation.{0} 1 := thicken pinchData

theorem pinchI_left_not_injective : ¬ Function.Injective (pinchI.left 0) := fun h =>
  Bool.false_ne_true (congrArg Prod.fst
    (h (a₁ := ((false : Bool), (0 : unitInterval))) (a₂ := ((true : Bool), (0 : unitInterval)))
      rfl))

/-- The induced map on edge components is not injective either. -/
theorem pinchI_componentData_left_not_injective :
    ¬ Function.Injective ((ofFiniteData pinchI.componentData).left 0) := fun h =>
  Bool.false_ne_true ((thicken_edgeClass_eq_iff pinchData 0 _ _ 0 0).1
    (h (a₁ := pinchI.edgeClass 0 (false, 0)) (a₂ := pinchI.edgeClass 0 (true, 0)) rfl))

/-- Two raw cylinder ends that are different points of `X` ... -/
theorem pinchI_bottom_ne_raw :
    pinchI.ofCylinder S01 0 (((false : Bool), (0 : unitInterval)), segBot S01 0) ≠
      pinchI.ofCylinder S01 0 (((true : Bool), (1 : unitInterval)), segBot S01 0) := by
  rw [ofCylinder_segBot, ofCylinder_segBot]
  intro h
  have := congrArg (fun p => (p.2 : ℝ)) (pinchI.ofVertex_injective S01 _ h)
  change ((0 : unitInterval) : ℝ) = ((1 : unitInterval) : ℝ) at this
  simp at this

/-- ... have the same Reeb class, through the bottom vertex piece. -/
theorem pinchI_bottom_merged :
    ReebQuotient.mk (pinchI.height S01)
        (pinchI.ofCylinder S01 0 (((false : Bool), (0 : unitInterval)), segBot S01 0)) =
      ReebQuotient.mk (pinchI.height S01)
        (pinchI.ofCylinder S01 0 (((true : Bool), (1 : unitInterval)), segBot S01 0)) := by
  rw [ofCylinder_segBot, ofCylinder_segBot]
  exact pinchI.quotientComponentGraphMap_injective S01
    (congrArg ((ofFiniteData pinchI.componentData).ofVertex S01 _)
      ((thicken_vertexClass_eq_iff pinchData _ _ _ 0 1).2 rfl))

/-- The two edges stay apart at a regular height. -/
theorem pinchI_regular_separate :
    ReebQuotient.mk (pinchI.height S01)
        (pinchI.ofStrip S01 0 (((false : Bool), (0 : unitInterval)), half)) ≠
      ReebQuotient.mk (pinchI.height S01)
        (pinchI.ofStrip S01 0 (((true : Bool), (0 : unitInterval)), half)) := fun h => by
  have h1 :
      (ofFiniteData pinchI.componentData).ofStrip S01 0 (pinchI.edgeClass 0 (false, 0), half) =
        (ofFiniteData pinchI.componentData).ofStrip S01 0 (pinchI.edgeClass 0 (true, 0), half) :=
    congrArg (pinchI.quotientComponentGraphMap S01) h
  exact Bool.false_ne_true ((thicken_edgeClass_eq_iff pinchData 0 _ _ 0 0).1
    (congrArg Prod.fst ((ofFiniteData pinchI.componentData).ofStrip_injective S01 0 h1)))

/-- The two top vertices stay apart. -/
theorem pinchI_top_separate :
    ReebQuotient.mk (pinchI.height S01)
        (pinchI.ofVertex S01 1 ((false : Bool), (0 : unitInterval))) ≠
      ReebQuotient.mk (pinchI.height S01)
        (pinchI.ofVertex S01 1 ((true : Bool), (0 : unitInterval))) := fun h => by
  have h1 : (ofFiniteData pinchI.componentData).ofVertex S01 1 (pinchI.vertexClass 1 (false, 0)) =
      (ofFiniteData pinchI.componentData).ofVertex S01 1 (pinchI.vertexClass 1 (true, 0)) :=
    congrArg (pinchI.quotientComponentGraphMap S01) h
  exact Bool.false_ne_true ((thicken_vertexClass_eq_iff pinchData 1 _ _ 0 0).1
    ((ofFiniteData pinchI.componentData).ofVertex_injective S01 1 h1))

/-- The Reeb quotient of the thickened pinch is the pinch graph. -/
def pinchI_quotientIso :
    (ReebQuotient.quotientFunctor ℝ).obj (Over.mk (TopCat.ofHom (pinchI.height S01))) ≅
      RGraph.toOver S01 pinchData :=
  thickenQuotientIso S01 pinchData

/-! ### Parallel edge components -/

/-- Thickened parallel edges over `S01`: `V = Unit × [0, 1]` at both levels, `E 0 = Bool × [0, 1]`,
both edge pieces attached to the same vertex pieces. -/
abbrev parallelI : CylinderPresentation.{0} 1 := thicken parallelData

/-- The two edge components have the same endpoints. -/
theorem parallelI_same_endpoints (s s' : unitInterval) :
    (ofFiniteData parallelI.componentData).left 0 (parallelI.edgeClass 0 (false, s)) =
        (ofFiniteData parallelI.componentData).left 0 (parallelI.edgeClass 0 (true, s')) ∧
      (ofFiniteData parallelI.componentData).right 0 (parallelI.edgeClass 0 (false, s)) =
        (ofFiniteData parallelI.componentData).right 0 (parallelI.edgeClass 0 (true, s')) :=
  ⟨(thicken_vertexClass_eq_iff parallelData 0 _ _ s s').2 rfl,
    (thicken_vertexClass_eq_iff parallelData 1 _ _ s s').2 rfl⟩

/-- The two parallel edges stay apart at every regular height. -/
theorem parallelI_regular_separate (s s' : unitInterval) (t : (S01.K 0 : Set ℝ)) :
    ReebQuotient.mk (parallelI.height S01) (parallelI.ofStrip S01 0 (((false : Bool), s), t)) ≠
      ReebQuotient.mk (parallelI.height S01) (parallelI.ofStrip S01 0 (((true : Bool), s'), t)) :=
  fun h => by
  have h1 :
      (ofFiniteData parallelI.componentData).ofStrip S01 0 (parallelI.edgeClass 0 (false, s), t) =
        (ofFiniteData parallelI.componentData).ofStrip S01 0
          (parallelI.edgeClass 0 (true, s'), t) :=
    congrArg (parallelI.quotientComponentGraphMap S01) h
  exact Bool.false_ne_true ((thicken_edgeClass_eq_iff parallelData 0 _ _ s s').1
    (congrArg Prod.fst ((ofFiniteData parallelI.componentData).ofStrip_injective S01 0 h1)))

/-- The quotient is not a single edge (`RGraph.Examples.parallel_not_iso_single`). -/
theorem parallelI_not_iso_single :
    IsEmpty ((ReebQuotient.quotientFunctor ℝ).obj (Over.mk (TopCat.ofHom (parallelI.height S01))) ≅
      RGraph.toOver S01 RGraph.Examples.singleEdge) :=
  ⟨fun i => RGraph.Examples.parallel_not_iso_single.false
    ((thickenQuotientIso S01 parallelData).symm ≪≫ i)⟩

/-! ### Transport along an isomorphism over `ℝ` -/

/-- The refinement of the single edge over `0 < 1/2 < 1` is isomorphic over `ℝ` to the single edge
over `0 < 1` (`RGraph.refineIso`). Its Reeb quotient is compared with the component graph through
that isomorphism; the object itself is not a realization over `S01`. -/
def refinedSingleEdge_quotientIso :
    (ReebQuotient.quotientFunctor ℝ).obj (RGraph.toOver RGraph.Examples.Shalf
        (RGraph.refineData RGraph.Examples.S01_sub_Shalf RGraph.Examples.singleEdge)) ≅
      RGraph.toOver S01 (ofFiniteData RGraph.Examples.singleEdge).componentData :=
  (ofFiniteData RGraph.Examples.singleEdge).quotientIsoOfIso S01
    (RGraph.refineIso RGraph.Examples.S01_sub_Shalf RGraph.Examples.singleEdge)

theorem refinedSingleEdge_isRGraph :
    RGraph.IsRGraph ((ReebQuotient.quotientFunctor ℝ).obj (RGraph.toOver RGraph.Examples.Shalf
      (RGraph.refineData RGraph.Examples.S01_sub_Shalf RGraph.Examples.singleEdge))) :=
  RGraph.isRGraph_quotient S01 (ofFiniteData RGraph.Examples.singleEdge)
    (RGraph.refineIso RGraph.Examples.S01_sub_Shalf RGraph.Examples.singleEdge)

/-- The identity of the refined single edge, presented over `S01` through the refinement
isomorphism and over `Shalf` by its own realization, induces a graph map between component graphs
over different critical lists, and the comparison square holds. -/
theorem refinedSingleEdge_inducedGraphMap_square :
    (ReebQuotient.quotientFunctor ℝ).map (𝟙 (RGraph.toOver RGraph.Examples.Shalf
        (RGraph.refineData RGraph.Examples.S01_sub_Shalf RGraph.Examples.singleEdge))) ≫
        ((ofFiniteData (RGraph.refineData RGraph.Examples.S01_sub_Shalf
          RGraph.Examples.singleEdge)).quotientIsoOfIso RGraph.Examples.Shalf (Iso.refl _)).hom =
      ((ofFiniteData RGraph.Examples.singleEdge).quotientIsoOfIso S01
          (RGraph.refineIso RGraph.Examples.S01_sub_Shalf RGraph.Examples.singleEdge)).hom ≫
        inducedGraphMap S01 RGraph.Examples.Shalf
          (RGraph.refineIso RGraph.Examples.S01_sub_Shalf RGraph.Examples.singleEdge)
          (Iso.refl _) (𝟙 _) :=
  inducedGraphMap_square _ _ _ _ _

/-! ### A height-dependent map: naturality for arbitrary height-preserving maps -/

/-- `s + t (1 - t) (1 - s)`: in `[0, 1]` for `s, t ∈ [0, 1]`, and `s` at `t = 0, 1`. -/
def bumpVal (s t : ℝ) : ℝ := s + t * (1 - t) * (1 - s)

theorem bumpVal_mem {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    bumpVal s t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  unfold bumpVal
  constructor
  · nlinarith [mul_nonneg (mul_nonneg ht0 (sub_nonneg.2 ht1)) (sub_nonneg.2 hs1)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sq_nonneg (t - 1 / 2))]

theorem seg01_mem (e : Fin 1) (t : Seg S01 e) : (t : ℝ) ∈ Icc (0 : ℝ) 1 := by
  obtain rfl := Fin.fin_one_eq_zero e
  have h : (t : ℝ) ∈ Icc (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) := t.2
  simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one] using h

/-- `bumpVal` as a point of `[0, 1]`. -/
def bumpI (s : unitInterval) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : unitInterval :=
  ⟨bumpVal s t, bumpVal_mem s.2 ht⟩

theorem continuous_bump (e : Fin 1) :
    Continuous fun p : parallelI.Cylinder S01 e => bumpI p.1.2 (p.2 : ℝ) (seg01_mem e p.2) := by
  refine Continuous.subtype_mk ?_ _
  unfold bumpVal
  fun_prop

/-- The swap of the two parallel edges, on the discrete edge set. -/
def flipE (e : Fin 1) : (ofFiniteData parallelData).E e → (ofFiniteData parallelData).E e :=
  fun b => Bool.not b

/-- The twist: the identity on vertex pieces; on the cylinder it swaps the two edges and moves the
interval coordinate by `bumpVal`, which depends on the height. -/
def twistMaps : parallelI.CompatibleMaps S01 (parallelI.Realization S01) where
  vertex i := ⟨parallelI.ofVertex S01 i, parallelI.continuous_ofVertex S01 i⟩
  cylinder e := ⟨fun p => parallelI.ofCylinder S01 e
      ((flipE e p.1.1, bumpI p.1.2 (p.2 : ℝ) (seg01_mem e p.2)), p.2),
    (parallelI.continuous_ofCylinder S01 e).comp
      ((((continuous_of_discreteTopology (f := flipE e)).comp
        (continuous_fst.comp continuous_fst)).prodMk (continuous_bump e)).prodMk continuous_snd)⟩
  segBot_eq e y := by
    refine (parallelI.ofCylinder_segBot S01 e _).trans
      (congrArg (parallelI.ofVertex S01 e.castSucc) (Prod.ext rfl (Subtype.ext ?_)))
    obtain rfl := Fin.fin_one_eq_zero e
    show bumpVal (y.2 : ℝ) (S01.value (Fin.castSucc 0)) = (y.2 : ℝ)
    simp [bumpVal]
  segTop_eq e y := by
    refine (parallelI.ofCylinder_segTop S01 e _).trans
      (congrArg (parallelI.ofVertex S01 e.succ) (Prod.ext rfl (Subtype.ext ?_)))
    obtain rfl := Fin.fin_one_eq_zero e
    show bumpVal (y.2 : ℝ) (S01.value (Fin.succ 0)) = (y.2 : ℝ)
    simp [bumpVal]

/-- The twist as a continuous self-map. -/
def twist : C(parallelI.Realization S01, parallelI.Realization S01) := lift twistMaps

theorem height_twist (x : parallelI.Realization S01) :
    parallelI.height S01 (twist x) = parallelI.height S01 x := by
  obtain ⟨y, rfl⟩ := parallelI.quotMk_surjective S01 x
  rcases y with ⟨i, v⟩ | ⟨e, p⟩ <;> rfl

theorem K01_mem (t : (S01.K 0 : Set ℝ)) : (t : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have h : S01.value (Fin.castSucc 0) < t ∧ (t : ℝ) < S01.value (Fin.succ 0) := t.2
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one] at h
  exact ⟨h.1.le, h.2.le⟩

/-- Pointwise, the regular fiber map of the twist at `t` is `(b, s) ↦ (¬b, bump s t)`. -/
theorem twist_regularFiberMap (t : (S01.K 0 : Set ℝ)) (b : Bool) (s : unitInterval) :
    regularFiberMap S01 twist height_twist 0 t (b, s) = (flipE 0 b, bumpI s t (K01_mem t)) := by
  have h2 : parallelI.ofStrip S01 0 (regularFiberMap S01 twist height_twist 0 t (b, s), t) =
      parallelI.ofStrip S01 0 ((flipE 0 b, bumpI s t (K01_mem t)), t) :=
    (map_ofStrip_eq S01 twist height_twist 0 t (b, s)).symm.trans rfl
  exact congrArg Prod.fst (parallelI.ofStrip_injective S01 0 h2)

/-- It depends on the height: `1/2` and `3/4` give different fiber maps. -/
theorem twist_regularFiberMap_depends :
    regularFiberMap S01 twist height_twist 0 half ≠
      regularFiberMap S01 twist height_twist 0 threeQuarters := fun h => by
  have h1 := congrArg (fun g : C(parallelI.E 0, parallelI.E 0) =>
    ((g ((false : Bool), (0 : unitInterval))).2 : ℝ)) h
  have e1 : ((regularFiberMap S01 twist height_twist 0 half
      ((false : Bool), (0 : unitInterval))).2 : ℝ) = bumpVal 0 (1 / 2) := by
    rw [twist_regularFiberMap]
    rfl
  have e2 : ((regularFiberMap S01 twist height_twist 0 threeQuarters
      ((false : Bool), (0 : unitInterval))).2 : ℝ) = bumpVal 0 (3 / 4) := by
    rw [twist_regularFiberMap]
    rfl
  have h2 : bumpVal 0 (1 / 2) = bumpVal 0 (3 / 4) := e1.symm.trans (h1.trans e2)
  norm_num [bumpVal] at h2

/-- On components it is the edge swap, whatever the height. -/
theorem twist_componentDataHom_e (b : Bool) (s : unitInterval) :
    (componentDataHom S01 twist height_twist).e 0 (parallelI.edgeClass 0 (b, s)) =
      parallelI.edgeClass 0 (!b, s) := by
  have h : (componentDataHom S01 twist height_twist).e 0 (parallelI.edgeClass 0 (b, s)) =
      parallelI.edgeClass 0 (regularFiberMap S01 twist height_twist 0 half (b, s)) :=
    congrFun (componentDataHom_e S01 twist height_twist 0 half) _
  rw [h, twist_regularFiberMap]
  exact (thicken_edgeClass_eq_iff parallelData 0 _ _ _ _).2 rfl

theorem twist_componentDataHom_ne_id :
    componentDataHom S01 twist height_twist ≠ FiniteReebData.Hom.id _ := fun h => by
  have h1 := congrArg (fun φ : FiniteReebData.Hom _ _ =>
    φ.e 0 (parallelI.edgeClass 0 (false, 0))) h
  simp only [twist_componentDataHom_e] at h1
  exact Bool.false_ne_true ((thicken_edgeClass_eq_iff parallelData 0 _ _ 0 0).1 h1).symm

/-- The naturality square on a strip point: the quotient map of the twist is the realized swap. -/
theorem twist_quotient_strip (b : Bool) (s : unitInterval) (t : (S01.K 0 : Set ℝ)) :
    parallelI.quotientComponentGraphMap S01
        (ReebQuotient.map twist height_twist
          (ReebQuotient.mk _ (parallelI.ofStrip S01 0 ((b, s), t)))) =
      (ofFiniteData parallelI.componentData).ofStrip S01 0 (parallelI.edgeClass 0 (!b, s), t) := by
  rw [quotientComponentGraphMap_natural]
  exact congrArg (fun c => (ofFiniteData parallelI.componentData).ofStrip S01 0 (c, t))
    (twist_componentDataHom_e b s)

/-- The twist as a slice morphism. -/
def twistOver :
    Over.mk (TopCat.ofHom (parallelI.height S01)) ⟶ Over.mk (TopCat.ofHom (parallelI.height S01)) :=
  Over.homMk (TopCat.ofHom twist) (by ext x; exact height_twist x)

/-- Its slice naturality square. -/
theorem twistOver_natural :
    (ReebQuotient.quotientFunctor ℝ).map twistOver ≫ (parallelI.quotientOverIso S01).hom =
      (parallelI.quotientOverIso S01).hom ≫
        (RGraph.realizationFunctor S01).map
          (componentDataHom S01 (overHomMap S01 twistOver) (height_overHomMap S01 twistOver)) :=
  quotientOverIso_natural S01 twistOver

/-! ### Generator formulas, height and projection on the thickened pinch -/

theorem pinchI_formula_strip (b : Bool) (s : unitInterval) :
    pinchI.quotientComponentGraphHomeomorph S01
        (ReebQuotient.mk _ (pinchI.ofStrip S01 0 ((b, s), half))) =
      (ofFiniteData pinchI.componentData).ofStrip S01 0 (pinchI.edgeClass 0 (b, s), half) ∧
    (ofFiniteData pinchI.componentData).height S01
        (pinchI.quotientComponentGraphHomeomorph S01
          (ReebQuotient.mk _ (pinchI.ofStrip S01 0 ((b, s), half)))) = 1 / 2 ∧
    ReebQuotient.height (pinchI.height S01)
        (ReebQuotient.mk _ (pinchI.ofStrip S01 0 ((b, s), half))) = 1 / 2 :=
  ⟨rfl, rfl, rfl⟩

theorem pinchI_formula_vertex (b : Bool) (s : unitInterval) :
    (pinchI.quotientComponentGraphHomeomorph S01).symm
        ((ofFiniteData pinchI.componentData).ofVertex S01 1 (pinchI.vertexClass 1 (b, s))) =
      ReebQuotient.mk _ (pinchI.ofVertex S01 1 (b, s)) ∧
    ReebQuotient.height (pinchI.height S01)
        ((pinchI.quotientComponentGraphHomeomorph S01).symm
          ((ofFiniteData pinchI.componentData).ofVertex S01 1 (pinchI.vertexClass 1 (b, s)))) = 1 :=
  ⟨pinchI.quotientComponentGraphHomeomorph_symm_ofVertex S01 1 (b, s), by
    rw [height_quotientComponentGraphHomeomorph_symm]
    exact S01_value_one⟩

theorem pinchI_formula_cylinder (b : Bool) (s : unitInterval) (t : Seg S01 0) :
    pinchI.quotientComponentGraphHomeomorph S01
        (ReebQuotient.mk _ (pinchI.ofCylinder S01 0 ((b, s), t))) =
      (ofFiniteData pinchI.componentData).ofCylinder S01 0 (pinchI.edgeClass 0 (b, s), t) ∧
    (ofFiniteData pinchI.componentData).height S01
        (pinchI.quotientComponentGraphHomeomorph S01
          (ReebQuotient.mk _ (pinchI.ofCylinder S01 0 ((b, s), t)))) = t :=
  ⟨rfl, rfl⟩

/-! ### The graph case -/

theorem parallel_graph_case (x : (ofFiniteData parallelData).Realization S01) :
    (ofFiniteData parallelData).quotientComponentGraphMap S01
        (RGraph.projHomeomorph S01 parallelData x) =
      realizeHom S01 parallelData.toComponentData x :=
  quotientComponentGraphMap_projHomeomorph S01 parallelData x

theorem parallel_graph_case_over :
    (ReebQuotient.projNatTrans ℝ).app
          (Over.mk (TopCat.ofHom ((ofFiniteData parallelData).height S01))) ≫
        ((ofFiniteData parallelData).quotientOverIso S01).hom =
      (RGraph.realizationFunctor S01).map parallelData.toComponentData :=
  projNatTrans_comp_quotientOverIso S01 parallelData

/-- The functor from constructible ℝ-spaces to graph objects, on the thickened pinch. -/
def pinchI_rgraph : RGraph.RGraphCat :=
  quotientRGraphFunctor.obj ⟨_, thicken_isConstructibleSpace S01 pinchData⟩

end Examples.ConstructibleQuotient

end

end TDA.Reeb
