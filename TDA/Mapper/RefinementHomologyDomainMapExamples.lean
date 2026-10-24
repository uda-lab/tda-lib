import TDA.Mapper.RefinementHomologyDomainMap
import TDA.Mapper.RefinementHomologyCappedTowerExamples
import TDA.Mapper.GraphPLReebStabilityExamples
import TDA.Mapper.GraphPLLevelSets
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Topology.UnitInterval

/-!
# Height-preserving map fixtures

* **Edge reversal.** The vertex swap of the single edge is a graph isomorphism from the heights
  `(0, 1)` to the heights `(1, 0)`.  With the labels `0, 1, 2`, base `0`, spacing `1` and the
  uniform grid of spacing `1/4` from `0` to `2`, the capped centred diagrams of the two
  piecewise-linear heights are at bottleneck distance `0` in every degree, although the vertex
  heights are at distance `1`.
* **Identity and composite.** The identity of the unit interval induces the identity vertex
  map.  The point map `Unit → Bool` selecting `false`, followed by the endpoint inclusion
  `Bool → unitInterval`, gives a composition law instance with two non-identity maps over
  their heights.
* **Not a homeomorphism.** The two endpoints of the unit interval, at heights `0` and `1`, map into
  the interval by inclusion over the height `x ↦ x`, with the single member `ℝ`.  The Mapper of the
  endpoints has two vertices and no edge, that of the interval has one, and the induced `H₀` map
  over `ℚ` goes from dimension `2` to dimension `1`; it is not injective.
* **Graph relabelling and reflection.** Swapping the vertices `0` and `1` sends the 4-cycle
  with heights `0, 1, 2, 1` to a different graph on `Fin 4` with heights `1, 0, 2, 1`; their
  capped centred diagrams are at bottleneck distance `0`.  Separately, the reflection fixing
  `0` and `2` preserves the original heights.  On the level `1`, its domain map sends the
  class of the vertex `1` to the class of the vertex `3`, a different component index.
-/

namespace TDA.Mapper.RefinementHomologyDomainMapExamples

open CategoryTheory SimpleGraph
open TDA.Topology TDA.Simplicial TDA.Persistence TDA.Persistence.FiniteConstructible
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Mapper.GraphPL (ClosedLevel closedLevelComponentsEquiv closedLevelComponentsEquiv_mk_vertex)
open TDA.Reeb.Examples.GraphRealization (edgeGraph)
open TDA.Reeb.Examples.GraphPLVertexPerturbation (tilted)
open TDA.Mapper.GraphPLReebStabilityExamples (reversed reversal_geometricInterleavingDistance)
open TDA.Mapper.RefinementHomologyCappedTowerExamples (edgeGrid)
open scoped NNReal ENNReal

noncomputable section

/-- Any linear order on component indices; the statements below do not depend on the choice. -/
local instance {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (U : ι → Set Y) : LinearOrder (ComponentIndex f U) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-! ## Edge reversal -/

/-- The vertex swap of the single edge as a graph isomorphism. -/
def swapIso : edgeGraph ≃g edgeGraph where
  toEquiv := Equiv.boolNot
  map_rel_iff' := by simp

theorem reversed_swapIso (b : Bool) : reversed (swapIso b) = tilted b := by
  cases b <;> rfl

/-- The capped centred diagrams of the heights `(0, 1)` and `(1, 0)` on the single edge are at
bottleneck distance `0`, while the heights are at distance `1`. -/
theorem edge_reversal_bottleneck_eq_zero (k : Type) [Field k] (n : ℕ) :
    bottleneck (cappedCentredDiagram k (plHeight edgeGraph tilted) 0 1
        (fun w : Fin 3 => (w : ℤ)) edgeGrid n)
      (cappedCentredDiagram k (plHeight edgeGraph reversed) 0 1
        (fun w : Fin 3 => (w : ℤ)) edgeGrid n) = 0 ∧
      edist tilted reversed = 1 :=
  ⟨bottleneck_cappedCentredDiagram_plHeight_iso k 0 1 _ edgeGrid n swapIso
      (fun v => reversed_swapIso v),
    (reversal_geometricInterleavingDistance).2.2.1⟩

/-- With the labels `0, 1` the same holds. -/
theorem edge_reversal_bottleneck_eq_zero_two_labels (k : Type) [Field k] (n : ℕ) :
    bottleneck (cappedCentredDiagram k (plHeight edgeGraph tilted) 0 1
        (fun w : Fin 2 => (w : ℤ)) edgeGrid n)
      (cappedCentredDiagram k (plHeight edgeGraph reversed) 0 1
        (fun w : Fin 2 => (w : ℤ)) edgeGrid n) = 0 ∧
      edist tilted reversed = 1 :=
  ⟨bottleneck_cappedCentredDiagram_plHeight_iso k 0 1 _ edgeGrid n swapIso
      (fun v => reversed_swapIso v),
    (reversal_geometricInterleavingDistance).2.2.1⟩

/-! ## Identity and composite -/

/-- The constant height `0` on the one-point space. -/
def pointHeight : C(Unit, ℝ) :=
  ContinuousMap.const Unit 0

/-- The height `x ↦ x` on the unit interval. -/
def intervalHeight : C(unitInterval, ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of the point at `0`. -/
def pointToZero : C(Unit, unitInterval) :=
  ContinuousMap.const Unit 0

theorem intervalHeight_pointToZero (u : Unit) : intervalHeight (pointToZero u) = pointHeight u :=
  rfl

example (U : Bool → Set ℝ) :
    mapperDomainMap (f := intervalHeight) (f' := intervalHeight) (ContinuousMap.id unitInterval)
        (fun _ => rfl) U = VertexMap.id (mapper intervalHeight U) :=
  mapperDomainMap_id U

/-! ## Graph relabelling and reflection -/

/-- The 4-cycle. -/
abbrev cycle4 : SimpleGraph (Fin 4) :=
  cycleGraph 4

/-- Heights `0, 1, 2, 1` on the vertices of the 4-cycle. -/
def cycleHeight : Fin 4 → ℝ :=
  ![0, 1, 2, 1]

/-- The reflection of the 4-cycle fixing the vertices `0` and `2`. -/
def reflection : cycle4 ≃g cycle4 where
  toEquiv := Equiv.neg (Fin 4)
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem cycleHeight_reflection (v : Fin 4) : cycleHeight (reflection v) = cycleHeight v := by
  fin_cases v <;> simp [cycleHeight, reflection]

/-- The graph obtained by swapping the labels `0` and `1` of the 4-cycle. -/
abbrev cycle4' : SimpleGraph (Fin 4) :=
  cycle4.map (Equiv.swap (0 : Fin 4) 1).toEmbedding

/-- Heights `1, 0, 2, 1` on the relabelled 4-cycle. -/
def cycleHeight' : Fin 4 → ℝ :=
  cycleHeight ∘ Equiv.swap 0 1

/-- The relabelling isomorphism swapping the vertices `0` and `1`. -/
def cycleRelabelIso : cycle4 ≃g cycle4' :=
  SimpleGraph.Iso.map (Equiv.swap 0 1) cycle4

example : cycle4' ≠ cycle4 := by
  intro h
  have hadj : cycle4'.Adj 0 2 := by
    have h := cycleRelabelIso.toHom.map_adj (show cycle4.Adj 1 2 by decide)
    change cycle4'.Adj ((Equiv.swap (0 : Fin 4) 1) 1) ((Equiv.swap (0 : Fin 4) 1) 2) at h
    convert h using 1 <;> decide
  rw [h] at hadj
  exact (by decide : ¬ cycle4.Adj 0 2) hadj

/-- The capped centred diagrams of the 4-cycle with heights `0, 1, 2, 1` and its relabelling
by the swap of `0` and `1`, with heights `1, 0, 2, 1`, are at bottleneck distance `0`. -/
theorem cycle4_relabel_bottleneck_eq_zero (k : Type) [Field k] (n : ℕ) :
    bottleneck (cappedCentredDiagram k (plHeight cycle4 cycleHeight) 0 1
        (fun w : Fin 3 => (w : ℤ)) edgeGrid n)
      (cappedCentredDiagram k (plHeight cycle4' cycleHeight') 0 1
        (fun w : Fin 3 => (w : ℤ)) edgeGrid n) = 0 :=
  bottleneck_cappedCentredDiagram_plHeight_iso k 0 1 _ edgeGrid n cycleRelabelIso
    (by
      intro v
      change cycleHeight ((Equiv.swap (0 : Fin 4) 1) ((Equiv.swap (0 : Fin 4) 1) v)) =
        cycleHeight v
      simp)

/-- The level `1` of the 4-cycle height. -/
abbrev levelOne : Unit → Set ℝ :=
  fun _ => {1}

private theorem cycleHeight_one : cycleHeight 1 = 1 := by simp [cycleHeight]

private theorem cycleHeight_three : cycleHeight 3 = 1 := by simp [cycleHeight]

/-- The vertex `1` as a point of the level `1`. -/
def levelPoint₁ : PullbackSpace (plHeight cycle4 cycleHeight) levelOne () :=
  ⟨vertex cycle4 1, by
    show cycleHeight 1 ∈ ({1} : Set ℝ)
    rw [cycleHeight_one]; rfl⟩

/-- The vertex `3` as a point of the level `1`. -/
def levelPoint₃ : PullbackSpace (plHeight cycle4 cycleHeight) levelOne () :=
  ⟨vertex cycle4 3, by
    show cycleHeight 3 ∈ ({1} : Set ℝ)
    rw [cycleHeight_three]; rfl⟩

theorem mk_levelPoint₁_ne_mk_levelPoint₃ :
    (ZerothHomotopy.mk levelPoint₁ : ZerothHomotopy (ClosedLevel cycle4 cycleHeight 1)) ≠
      ZerothHomotopy.mk levelPoint₃ := by
  intro h
  have h₁ := closedLevelComponentsEquiv_mk_vertex cycle4 cycleHeight 1 cycleHeight_one
  have h₃ := closedLevelComponentsEquiv_mk_vertex cycle4 cycleHeight 3 cycleHeight_three
  have h' := h₁.symm.trans ((congrArg (closedLevelComponentsEquiv cycle4 cycleHeight 1) h).trans
    h₃)
  have hreach := (ConnectedComponent.eq.1 (Sum.inl.inj h'))
  have hbot : cycle4.induce {v | cycleHeight v = 1} = ⊥ := by
    ext a b
    simp only [comap_adj, Function.Embedding.coe_subtype, bot_adj, iff_false]
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    change cycleHeight a = 1 at ha
    change cycleHeight b = 1 at hb
    have hlevel : ∀ v : Fin 4, cycleHeight v = 1 → v = 1 ∨ v = 3 := by
      intro v hv
      fin_cases v <;> simp_all [cycleHeight]
    have hna : ∀ a b : Fin 4, (a = 1 ∨ a = 3) → (b = 1 ∨ b = 3) → ¬ cycle4.Adj a b := by
      decide
    exact hna a b (hlevel a ha) (hlevel b hb)
  rw [hbot, reachable_bot] at hreach
  have := congrArg Subtype.val hreach
  exact absurd this (by decide)

/-- The reflection moves the class of the vertex `1` over the level `1` to the class of the
vertex `3`, a different component index; the domain map is an isomorphism of the Mapper homology
modules that is not the identity on `ComponentIndex`. -/
theorem reflection_domainIndexMap_vertex_one :
    domainIndexMap (f := plHeight cycle4 cycleHeight) (f' := plHeight cycle4 cycleHeight)
        (realizationMap reflection.toHom)
        (plHeight_realizationHomeomorph reflection cycleHeight_reflection) levelOne
        ⟨(), ZerothHomotopy.mk levelPoint₁⟩ = ⟨(), ZerothHomotopy.mk levelPoint₃⟩ ∧
      domainIndexMap (f := plHeight cycle4 cycleHeight) (f' := plHeight cycle4 cycleHeight)
        (realizationMap reflection.toHom)
        (plHeight_realizationHomeomorph reflection cycleHeight_reflection) levelOne
        ⟨(), ZerothHomotopy.mk levelPoint₁⟩ ≠ ⟨(), ZerothHomotopy.mk levelPoint₁⟩ := by
  refine ⟨rfl, fun h => ?_⟩
  have h' : (ZerothHomotopy.mk levelPoint₃ : ZerothHomotopy (ClosedLevel cycle4 cycleHeight 1)) =
      ZerothHomotopy.mk levelPoint₁ := eq_of_heq (Sigma.mk.inj h).2
  exact mk_levelPoint₁_ne_mk_levelPoint₃ h'.symm

/-! ## A map that is not a homeomorphism -/

/-- The inclusion of the two endpoints of the unit interval. -/
def endpoints : C(Bool, unitInterval) :=
  ⟨fun b => if b then 1 else 0, continuous_of_discreteTopology⟩

/-- The height `x ↦ x` restricted to the two endpoints, at heights `0` and `1`. -/
def endpointHeight : C(Bool, ℝ) :=
  intervalHeight.comp endpoints

/-- The point map selecting the endpoint `false`, of height `0`. -/
def pointToFalse : C(Unit, Bool) :=
  ContinuousMap.const Unit false

/-- Composition of the point map to the two endpoints and their inclusion into the interval
induces the composite of the two Mapper vertex maps, for any `Bool`-indexed family. -/
example (U : Bool → Set ℝ) :
    mapperDomainMap (f := pointHeight) (f' := intervalHeight)
        (endpoints.comp pointToFalse) (fun _ => rfl) U =
      VertexMap.comp (mapperDomainMap (f := pointHeight) (f' := endpointHeight) pointToFalse
          (fun _ => rfl) U)
        (mapperDomainMap (f := endpointHeight) (f' := intervalHeight)
          endpoints (fun _ => rfl) U) :=
  mapperDomainMap_comp (f := pointHeight) (f' := endpointHeight) (f'' := intervalHeight)
    pointToFalse (fun _ => rfl) endpoints (fun _ => rfl) U

/-- The single member `ℝ`. -/
abbrev wholeLine : Unit → Set ℝ :=
  fun _ => Set.univ

private theorem faceOne_isEmpty {Z : Type} [TopologicalSpace Z] (g : C(Z, ℝ)) :
    IsEmpty (Face (mapper g wholeLine) 1) :=
  ⟨fun s => by
    have hmult : CoverMultiplicityAtMost g wholeLine 1 := fun _ _ t _ => by
      simpa using Finset.card_le_univ t
    have := mapper_face_card_le_of_multiplicity g wholeLine hmult s.2.1
    have h2 := s.2.2
    omega⟩

private def faceZeroEquiv {Z : Type} [TopologicalSpace Z] (g : C(Z, ℝ)) :
    Face (mapper g wholeLine) 0 ≃ ComponentIndex g wholeLine where
  toFun s := (Finset.card_eq_one.1 s.2.2).choose
  invFun a := ⟨{a}, componentIndex_supported g wholeLine a, Finset.card_singleton a⟩
  left_inv s := Subtype.ext (Finset.card_eq_one.1 s.2.2).choose_spec.symm
  right_inv a := by
    have := (Finset.card_eq_one.1 (Finset.card_singleton a)).choose_spec
    exact (Finset.singleton_inj.1 this).symm

private def componentIndexEquiv {Z : Type} [TopologicalSpace Z] (g : C(Z, ℝ)) :
    ComponentIndex g wholeLine ≃ ZerothHomotopy (PullbackSpace g wholeLine ()) :=
  Equiv.uniqueSigma _

private theorem nat_card_face_zero {Z : Type} [TopologicalSpace Z] (g : C(Z, ℝ)) :
    Nat.card (Face (mapper g wholeLine) 0) =
      Nat.card (ZerothHomotopy (PullbackSpace g wholeLine ())) :=
  Nat.card_congr ((faceZeroEquiv g).trans (componentIndexEquiv g))

private theorem finrank_zeroHomology {Z : Type} [TopologicalSpace Z] (g : C(Z, ℝ))
    [LinearOrder (ComponentIndex g wholeLine)]
    [Finite (ZerothHomotopy (PullbackSpace g wholeLine ()))] :
    Module.finrank ℚ (simplicialHomology (mapper g wholeLine) ℚ 0) =
      Nat.card (ZerothHomotopy (PullbackSpace g wholeLine ())) := by
  have : Finite (Face (mapper g wholeLine) 0) :=
    Finite.of_equiv _ ((faceZeroEquiv g).trans (componentIndexEquiv g)).symm
  have := faceOne_isEmpty g
  have := Fintype.ofFinite (Face (mapper g wholeLine) 0)
  rw [finrank_zeroHomology_of_no_edges, Fintype.card_eq_nat_card, nat_card_face_zero]

/-- The two endpoints lie in different path components of the discrete space. -/
private theorem card_endpoint_components :
    Nat.card (ZerothHomotopy (PullbackSpace endpointHeight wholeLine ())) = 2 := by
  let q : Bool → ZerothHomotopy (PullbackSpace endpointHeight wholeLine ()) :=
    fun b => ZerothHomotopy.mk ⟨b, trivial⟩
  have hinj : Function.Injective q := by
    intro a b hab
    by_contra hne
    obtain ⟨p⟩ := Quotient.exact hab
    have hc : Continuous fun t => (p t).1 := continuous_subtype_val.comp p.continuous
    have := PreconnectedSpace.constant inferInstance hc (x := 0) (y := 1)
    simp at this
    exact hne this
  have hsurj : Function.Surjective q := by
    intro c
    induction c using ZerothHomotopy.rec with
    | mk x => exact ⟨x.1, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective q ⟨hinj, hsurj⟩)]
  simp

/-- The unit interval is path-connected, by convexity. -/
private theorem pathConnectedSpace_unitInterval : PathConnectedSpace unitInterval :=
  isPathConnected_iff_pathConnectedSpace.1
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, unitInterval.zero_mem⟩)

private theorem card_interval_components :
    Nat.card (ZerothHomotopy (PullbackSpace intervalHeight wholeLine ())) = 1 := by
  let e : unitInterval → PullbackSpace intervalHeight wholeLine () := fun x => ⟨x, trivial⟩
  have := pathConnectedSpace_unitInterval
  have : PathConnectedSpace (PullbackSpace intervalHeight wholeLine ()) :=
    (show Function.Surjective e from fun x => ⟨x.1, rfl⟩).pathConnectedSpace (by fun_prop)
  exact Nat.card_unique

/-- The induced `H₀` map over `ℚ` of the inclusion of the endpoints of the unit interval over
the height `x ↦ x` goes from a space of dimension `2` to a space of dimension `1` and is not
injective. -/
theorem endpoints_homologyDomainMap_not_injective :
    Module.finrank ℚ (simplicialHomology (mapper endpointHeight wholeLine) ℚ 0) = 2 ∧
      Module.finrank ℚ (simplicialHomology (mapper intervalHeight wholeLine) ℚ 0) = 1 ∧
      ¬ Function.Injective
        (mapperHomologyDomainMap (f := endpointHeight) (f' := intervalHeight) ℚ endpoints
          (fun _ => rfl) wholeLine 0).hom := by
  have h2 : Finite (ZerothHomotopy (PullbackSpace endpointHeight wholeLine ())) :=
    Nat.finite_of_card_ne_zero (by rw [card_endpoint_components]; omega)
  have h1 : Finite (ZerothHomotopy (PullbackSpace intervalHeight wholeLine ())) :=
    Nat.finite_of_card_ne_zero (by rw [card_interval_components]; omega)
  have hsrc := finrank_zeroHomology endpointHeight
  have htgt := finrank_zeroHomology intervalHeight
  rw [card_endpoint_components] at hsrc
  rw [card_interval_components] at htgt
  refine ⟨hsrc, htgt, fun hinj => ?_⟩
  have : Module.Finite ℚ (simplicialHomology (mapper intervalHeight wholeLine) ℚ 0) :=
    Module.finite_of_finrank_pos (by omega)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

end

end TDA.Mapper.RefinementHomologyDomainMapExamples
