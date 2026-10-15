import TDA.Reeb.GraphRealization
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Fixtures for realizations of simple graphs

Acceptance fixtures for `TDA.Reeb.GraphRealization`:

* **Empty vertex type.** For every `[IsEmpty V]`, in any universe, the realization, its path
  components and the graph components are empty, and neither the graph is connected nor the
  realization path connected.
* **One isolated vertex.** The realization is a point (`Unique` and a homeomorphism with `Unit`),
  both component types have exactly one element, and the graph is connected.
* **One edge on two vertices.** For `⊤ : SimpleGraph Bool`, an explicit homeomorphism with
  `unitInterval` sends `vertex false` to `0`, `vertex true` to `1`, the dart `false → true` at `t`
  to `t` and its reversal at `t` to `σ t`. The reversed dart at the reversed parameter is the same
  point, and distinct parameters, interior ones included, give distinct points.
* **Two disjoint edges.** On `Bool × Bool`, the path components are equivalent to `Bool`: exactly
  two classes, with explicit distinct representatives and an exhaustive classification.
* **A path with two edges folded onto one edge.** The homomorphism `pathGraph 3 →g ⊤` with
  `0, 1, 2 ↦ false, true, false` identifies the nonadjacent ends and the two distinct edges; it is a
  graph homomorphism, not an edge contraction. The generator formulas hold on every vertex and on
  the darts `0 → 1`, `1 → 2` and `2 → 1`: the dart `1 → 2` goes to the reversed dart, so its edge
  coordinate is reversed. Naturality is evaluated at the interior point `1/2` of both orientations
  of the second edge. The target graph is connected, so this square alone does not discriminate at
  the level of components; the generator and orientation formulas do.
* **A permutation of two components.** Swapping the two disjoint edges induces the map exchanging
  the two path-component classes, which is not the identity. The naturality square at the first
  class has both sides equal to the class of `(true, false)`, distinct from the class it starts
  from, so the swap is the discriminating component-level fixture.
* **Infinite edgeless graphs.** On `ℕ`, distinct vertices stay distinct and lie in distinct path
  components, so there are infinitely many path components, and the realization is not path
  connected; no finiteness is assumed. On `ℝ`, distinct vertices lie in distinct path components and
  the realization is not path connected, although `ℝ` is: the topology of the vertex type is not
  used.
-/

open SimpleGraph unitInterval Topology

namespace TDA.Reeb.Examples.GraphRealization

open TDA.Reeb.GraphRealization

noncomputable section

/-! ### Empty vertex type -/

section Empty

variable {V : Type*} [IsEmpty V] (G : SimpleGraph V)

theorem empty_realization_isEmpty : IsEmpty (Realization G) := inferInstance

theorem empty_zerothHomotopy_isEmpty : IsEmpty (ZerothHomotopy (Realization G)) :=
  (componentsEquiv G).isEmpty_congr.2 inferInstance

theorem empty_connectedComponent_isEmpty : IsEmpty G.ConnectedComponent := inferInstance

theorem empty_not_connected : ¬ G.Connected := fun h => isEmptyElim (Classical.choice h.nonempty)

theorem empty_not_pathConnectedSpace : ¬ PathConnectedSpace (Realization G) := fun h =>
  isEmptyElim (Classical.choice h.nonempty)

end Empty

/-! ### One isolated vertex -/

/-- One vertex and no edge. -/
abbrev pointGraph : SimpleGraph Unit := ⊥

instance pointUnique : Unique (Realization pointGraph) where
  default := vertex pointGraph ()
  uniq x := ind pointGraph (p := fun x => x = vertex pointGraph ()) (fun _ => rfl)
    (fun d _ => d.adj.elim) x

/-- The realization of one isolated vertex is a point. -/
def pointHomeomorph : Realization pointGraph ≃ₜ Unit := Homeomorph.homeomorphOfUnique _ _

instance pointComponentsUnique : Unique (ZerothHomotopy (Realization pointGraph)) :=
  (componentsEquiv pointGraph).unique

theorem point_card_connectedComponent : Nat.card pointGraph.ConnectedComponent = 1 :=
  Nat.card_unique

theorem point_card_zerothHomotopy : Nat.card (ZerothHomotopy (Realization pointGraph)) = 1 :=
  Nat.card_unique

theorem point_pathConnectedSpace : PathConnectedSpace (Realization pointGraph) :=
  ⟨inferInstance, fun x y => by rw [Subsingleton.elim x y]⟩

theorem point_connected : pointGraph.Connected :=
  (connected_iff_pathConnectedSpace _).2 point_pathConnectedSpace

/-! ### One edge on two vertices -/

/-- The single edge `false — true`. -/
abbrev edgeGraph : SimpleGraph Bool := ⊤

/-- The dart `false → true`. -/
def d₀ : edgeGraph.Dart := ⟨(false, true), by simp⟩

theorem edgeGraph_dart (d : edgeGraph.Dart) : d = d₀ ∨ d = d₀.symm := by
  rcases d with ⟨⟨a, b⟩, h⟩
  have hab : a ≠ b := h
  cases a <;> cases b
  · exact absurd rfl hab
  · exact .inl rfl
  · exact .inr rfl
  · exact absurd rfl hab

/-- The edge coordinate on a dart: the parameter on `d₀`, its reversal on `d₀.symm`. -/
def edgeCoordCell (d : edgeGraph.Dart) : C(unitInterval, unitInterval) :=
  if d.fst then ⟨σ, continuous_symm⟩ else ContinuousMap.id _

/-- The coordinate of the single-edge realization. -/
def edgeCoord : C(Realization edgeGraph, unitInterval) :=
  continuousLift edgeGraph (fun b => if b then 1 else 0) edgeCoordCell
    (fun d t => by
      rcases edgeGraph_dart d with rfl | rfl
      · simp [edgeCoordCell, d₀]
      · simp [edgeCoordCell, d₀])
    (fun d => by
      rcases edgeGraph_dart d with rfl | rfl
      · simp [edgeCoordCell, d₀]
      · simp [edgeCoordCell, d₀, symm_zero])

/-- The realization of one edge is the unit interval. -/
def edgeHomeomorph : Realization edgeGraph ≃ₜ unitInterval where
  toFun := edgeCoord
  invFun := edgePoint edgeGraph d₀
  left_inv x := by
    induction x using ind edgeGraph with
    | vertex b =>
      cases b
      · exact edgePoint_zero edgeGraph d₀
      · exact edgePoint_one edgeGraph d₀
    | edgePoint d t =>
      rcases edgeGraph_dart d with rfl | rfl
      · rfl
      · exact edgePoint_symm edgeGraph d₀.symm t
  right_inv _ := rfl
  continuous_toFun := edgeCoord.continuous
  continuous_invFun := continuous_edgePoint edgeGraph d₀

theorem edgeHomeomorph_vertex_false : edgeHomeomorph (vertex edgeGraph false) = 0 := rfl

theorem edgeHomeomorph_vertex_true : edgeHomeomorph (vertex edgeGraph true) = 1 := rfl

theorem edgeHomeomorph_edgePoint (t : unitInterval) :
    edgeHomeomorph (edgePoint edgeGraph d₀ t) = t := rfl

theorem edgeHomeomorph_edgePoint_symm (t : unitInterval) :
    edgeHomeomorph (edgePoint edgeGraph d₀.symm t) = σ t := rfl

theorem edgeHomeomorph_symm_apply (t : unitInterval) :
    edgeHomeomorph.symm t = edgePoint edgeGraph d₀ t := rfl

/-- The reversed dart at the reversed parameter is the same point. -/
theorem edge_reversed (t : unitInterval) :
    edgePoint edgeGraph d₀.symm (σ t) = edgePoint edgeGraph d₀ t :=
  edgePoint_symm edgeGraph d₀ t

/-- Distinct parameters, in particular distinct interior parameters, stay distinct. -/
theorem edge_param_injective : Function.Injective (edgePoint edgeGraph d₀) :=
  edgeHomeomorph.symm.injective

theorem edge_interior_ne {s t : unitInterval} (h : s ≠ t) :
    edgePoint edgeGraph d₀ s ≠ edgePoint edgeGraph d₀ t :=
  edge_param_injective.ne h

/-! ### Two disjoint edges -/

/-- The edges `(a, false) — (a, true)` for `a : Bool`. -/
def twoEdges : SimpleGraph (Bool × Bool) where
  Adj p q := p.1 = q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

theorem fst_eq_of_reachable {p q : Bool × Bool} (h : twoEdges.Reachable p q) : p.1 = q.1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons h _ ih => exact h.1.trans ih

theorem reachable_base (p : Bool × Bool) : twoEdges.Reachable (p.1, false) p := by
  rcases p with ⟨a, _ | _⟩
  · exact .rfl
  · exact Adj.reachable (G := twoEdges) ⟨rfl, Bool.false_ne_true⟩

/-- The graph components are indexed by the first coordinate. -/
def twoEdgesSide : twoEdges.ConnectedComponent ≃ Bool where
  toFun := ConnectedComponent.lift Prod.fst fun _ _ p _ => fst_eq_of_reachable ⟨p⟩
  invFun b := twoEdges.connectedComponentMk (b, false)
  left_inv c := by
    induction c using ConnectedComponent.ind with
    | h p => exact ConnectedComponent.sound (reachable_base p)
  right_inv _ := rfl

/-- Exactly two path components. -/
def twoEdgesComponents : ZerothHomotopy (Realization twoEdges) ≃ Bool :=
  (componentsEquiv twoEdges).trans twoEdgesSide

/-- The representative classes. -/
def c₀ : ZerothHomotopy (Realization twoEdges) :=
  ZerothHomotopy.mk (vertex twoEdges (false, false))

def c₁ : ZerothHomotopy (Realization twoEdges) :=
  ZerothHomotopy.mk (vertex twoEdges (true, false))

theorem twoEdges_card : Nat.card (ZerothHomotopy (Realization twoEdges)) = 2 := by
  rw [Nat.card_congr twoEdgesComponents, Nat.card_eq_fintype_card, Fintype.card_bool]

theorem twoEdgesComponents_c₀ : twoEdgesComponents c₀ = false := rfl

theorem twoEdgesComponents_c₁ : twoEdgesComponents c₁ = true := rfl

theorem c₀_ne_c₁ : c₀ ≠ c₁ := fun h => by
  simpa [twoEdgesComponents_c₀, twoEdgesComponents_c₁] using congrArg twoEdgesComponents h

theorem twoEdges_classification (c : ZerothHomotopy (Realization twoEdges)) :
    c = c₀ ∨ c = c₁ := by
  have h := twoEdgesComponents.symm_apply_apply c
  cases hc : twoEdgesComponents c
  · exact .inl (by rw [← h, hc]; rfl)
  · exact .inr (by rw [← h, hc]; rfl)

/-! ### A path with two edges folded onto one edge -/

/-- The path `0 — 1 — 2`. -/
abbrev path3 : SimpleGraph (Fin 3) := pathGraph 3

theorem fold_adj : ∀ u v : Fin 3,
    u.val + 1 = v.val ∨ v.val + 1 = u.val → decide (u = 1) ≠ decide (v = 1) := by
  decide

/-- Fold `0, 1, 2 ↦ false, true, false`: a graph homomorphism identifying the nonadjacent ends
`0` and `2`, not an edge contraction. -/
def fold : path3 →g edgeGraph where
  toFun i := decide (i = 1)
  map_rel' h := (top_adj _ _).2 (fold_adj _ _ (pathGraph_adj.1 h))

/-- The darts `0 → 1`, `1 → 2` and its reversal `2 → 1`. -/
def d01 : path3.Dart := ⟨(0, 1), pathGraph_adj.2 (.inl (by decide))⟩

def d12 : path3.Dart := ⟨(1, 2), pathGraph_adj.2 (.inl (by decide))⟩

def d21 : path3.Dart := ⟨(2, 1), pathGraph_adj.2 (.inr (by decide))⟩

/-- The interior parameter `1/2`. -/
def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

theorem fold_vertex_zero : realizationMap fold (vertex path3 0) = vertex edgeGraph false := rfl

theorem fold_vertex_two : realizationMap fold (vertex path3 2) = vertex edgeGraph false := rfl

theorem fold_vertex_one : realizationMap fold (vertex path3 1) = vertex edgeGraph true := rfl

theorem fold_identifies_ends :
    vertex path3 0 ≠ vertex path3 2 ∧
      realizationMap fold (vertex path3 0) = realizationMap fold (vertex path3 2) :=
  ⟨(vertex_injective path3).ne (by decide), rfl⟩

theorem fold_edgePoint_d21 (t : unitInterval) :
    realizationMap fold (edgePoint path3 d21 t) = edgePoint edgeGraph d₀ t := rfl

theorem fold_edgePoint_d12 (t : unitInterval) :
    realizationMap fold (edgePoint path3 d12 t) = edgePoint edgeGraph d₀.symm t := rfl

theorem fold_edgePoint_d01 (t : unitInterval) :
    realizationMap fold (edgePoint path3 d01 t) = edgePoint edgeGraph d₀ t := rfl

/-- On the interval coordinate, the edge `1 — 2` is reversed by the fold. -/
theorem fold_coord_d12 (t : unitInterval) :
    edgeHomeomorph (realizationMap fold (edgePoint path3 d12 t)) = σ t := rfl

/-- A height on the path separating its two edges. -/
def pathHeight : Realization path3 → ℝ :=
  lift path3 (fun i => (i : ℝ)) (fun d t => (1 - (t : ℝ)) * d.fst + t * d.snd)
    (fun d t => by
      simp only [coe_symm_eq]
      rw [show d.symm.toProd.1 = d.toProd.2 from rfl, show d.symm.toProd.2 = d.toProd.1 from rfl]
      ring)
    (fun d => by simp)

/-- The fold identifies the distinct source edges `0 — 1` and `1 — 2` pointwise off the shared
vertex. -/
theorem fold_identifies_edges {t : unitInterval} (ht : t ≠ 1) :
    edgePoint path3 d01 t ≠ edgePoint path3 d21 t ∧
      realizationMap fold (edgePoint path3 d01 t) =
        realizationMap fold (edgePoint path3 d21 t) := by
  refine ⟨fun h => ht ?_, rfl⟩
  have h' := congrArg pathHeight h
  simp only [pathHeight, lift_edgePoint, d01, d21] at h'
  norm_num at h'
  ext
  simp only [Set.Icc.coe_one]
  linarith

/-- Naturality at the interior point `1/2` of the reversed dart `2 → 1`, with both sides
computed. -/
theorem fold_naturality_d21 :
    componentsEquiv edgeGraph
        (TDA.Reeb.componentMap (realizationMap fold) (.mk (edgePoint path3 d21 half))) =
      (componentsEquiv path3 (.mk (edgePoint path3 d21 half))).map fold ∧
    componentsEquiv edgeGraph
        (TDA.Reeb.componentMap (realizationMap fold) (.mk (edgePoint path3 d21 half))) =
      edgeGraph.connectedComponentMk false ∧
    (componentsEquiv path3 (.mk (edgePoint path3 d21 half))).map fold =
      edgeGraph.connectedComponentMk false :=
  ⟨componentsEquiv_componentMap path3 fold _, rfl, rfl⟩

/-- Naturality at the interior point `1/2` of the dart `1 → 2`, whose image is the reversed
dart. -/
theorem fold_naturality_d12 :
    componentsEquiv edgeGraph
        (TDA.Reeb.componentMap (realizationMap fold) (.mk (edgePoint path3 d12 half))) =
      (componentsEquiv path3 (.mk (edgePoint path3 d12 half))).map fold ∧
    componentsEquiv edgeGraph
        (TDA.Reeb.componentMap (realizationMap fold) (.mk (edgePoint path3 d12 half))) =
      edgeGraph.connectedComponentMk true :=
  ⟨componentsEquiv_componentMap path3 fold _, rfl⟩

/-! ### A permutation of two components -/

/-- Swap the two edges. -/
def swapHom : twoEdges →g twoEdges where
  toFun p := (!p.1, p.2)
  map_rel' h := ⟨congrArg (!·) h.1, h.2⟩

theorem swap_c₀ : TDA.Reeb.componentMap (realizationMap swapHom) c₀ = c₁ := rfl

theorem swap_c₁ : TDA.Reeb.componentMap (realizationMap swapHom) c₁ = c₀ := rfl

theorem swap_ne_id : TDA.Reeb.componentMap (realizationMap swapHom) ≠ id := fun h =>
  c₀_ne_c₁ (by rw [← swap_c₀, h]; rfl)

/-- The square at `c₀` is discriminating: both sides are the class of `(true, false)`, which is
not the class of `c₀`. -/
theorem swap_naturality :
    componentsEquiv twoEdges (TDA.Reeb.componentMap (realizationMap swapHom) c₀) =
      (componentsEquiv twoEdges c₀).map swapHom ∧
    (componentsEquiv twoEdges c₀).map swapHom = twoEdges.connectedComponentMk (true, false) ∧
    twoEdges.connectedComponentMk (true, false) ≠ componentsEquiv twoEdges c₀ :=
  ⟨componentsEquiv_componentMap twoEdges swapHom c₀, rfl, fun h =>
    c₀_ne_c₁ ((componentsEquiv twoEdges).injective h).symm⟩

/-! ### Infinite edgeless graphs; the vertex topology is not used -/

/-- In an edgeless graph on any type, distinct vertices lie in distinct path components. -/
theorem bot_class_injective (α : Type*) :
    Function.Injective fun a : α => ZerothHomotopy.mk (vertex (⊥ : SimpleGraph α) a) :=
  fun _ _ h => reachable_bot.1 (ConnectedComponent.exact (congrArg (componentsEquiv ⊥) h))

/-- The edgeless graph on `ℕ`. -/
abbrev natGraph : SimpleGraph ℕ := ⊥

theorem nat_vertex_injective : Function.Injective (vertex natGraph) := vertex_injective natGraph

theorem nat_class_injective :
    Function.Injective fun n : ℕ => ZerothHomotopy.mk (vertex natGraph n) :=
  bot_class_injective ℕ

theorem nat_zerothHomotopy_infinite : Infinite (ZerothHomotopy (Realization natGraph)) :=
  Infinite.of_injective _ nat_class_injective

theorem nat_not_pathConnectedSpace : ¬ PathConnectedSpace (Realization natGraph) := fun h =>
  absurd (nat_class_injective (Subsingleton.elim _ _ : _ = ZerothHomotopy.mk (vertex natGraph 1)))
    (by decide : (0 : ℕ) ≠ 1)

/-- The edgeless graph on `ℝ`. The realization ignores the path-connected topology of `ℝ`. -/
abbrev realGraph : SimpleGraph ℝ := ⊥

theorem real_class_injective :
    Function.Injective fun x : ℝ => ZerothHomotopy.mk (vertex realGraph x) :=
  bot_class_injective ℝ

theorem real_not_pathConnectedSpace :
    ¬ PathConnectedSpace (Realization realGraph) ∧ PathConnectedSpace ℝ :=
  ⟨fun h => zero_ne_one
    (reachable_bot.1 (((connected_iff_pathConnectedSpace realGraph).2 h).preconnected 0 1)),
    inferInstance⟩

end

end TDA.Reeb.Examples.GraphRealization
