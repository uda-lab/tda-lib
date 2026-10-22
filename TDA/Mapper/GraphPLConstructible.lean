import TDA.Mapper.GraphPLReebQuotient
import TDA.Reeb.ConstructibleThickeningQuotient
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Lemmas

/-! # The graph-PL realization as a constructible ℝ-space

This module develops the graph-PL realization and its constructible-space presentation: (A) the
Hausdorff and locally path-connected topology of graph realizations, (B) closed-level pieces and
their homeomorphisms, (C) the finite cylinder presentation and constructible-space structure,
(D) the quotient and Reeb-graph identifications, and (E) the thickening comparisons.  These are
library results and make no external source claim.  The realization and presentation statements
are universe-polymorphic, while the slice statements use `V : Type`.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory Filter
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open scoped NNReal

noncomputable section

universe u v

section realization

variable {V : Type u} (G : SimpleGraph V)

local instance : DecidableEq V := Classical.decEq V

/-- Barycentric coordinates send `vertex v` to `Pi.single v 1` and `edgePoint d t` to the affine
combination of the two endpoint coordinates. -/
noncomputable def barycentric : C(Realization G, V → ℝ) := by
  exact continuousLift G (fun v => Pi.single v 1)
    (fun d => ⟨fun t => (1 - (t : ℝ)) • Pi.single d.fst 1 +
      (t : ℝ) • Pi.single d.snd 1, by
        exact continuous_pi fun v =>
          ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
            (continuous_subtype_val.smul continuous_const)⟩)
    (fun d t => by
      ext v
      simp [unitInterval.coe_symm_eq, Pi.single_apply]
      ring)
    (fun d => by
      ext v
      simp [Pi.single_apply])

/-- Barycentric coordinates on a vertex. -/
theorem barycentric_vertex (v : V) : barycentric G (vertex G v) = Pi.single v 1 := by
  rfl

/-- Barycentric coordinates on an edge point. -/
theorem barycentric_edgePoint (d : G.Dart) (t : unitInterval) :
    barycentric G (edgePoint G d t) =
      (1 - (t : ℝ)) • Pi.single d.fst 1 + (t : ℝ) • Pi.single d.snd 1 := by
  rfl

private theorem barycentric_edge_coord_pos {d : G.Dart} {t : unitInterval} {i : V}
    (_ht₀ : 0 < (t : ℝ)) (_ht₁ : (t : ℝ) < 1)
    (hi : 0 < barycentric G (edgePoint G d t) i) :
    i = d.fst ∨ i = d.snd := by
  by_contra hn
  have hfst : i ≠ d.fst := fun h => hn (Or.inl h)
  have hsnd : i ≠ d.snd := fun h => hn (Or.inr h)
  simp [barycentric_edgePoint, hfst, hsnd] at hi

private theorem barycentric_edge_eq_vertex {d : G.Dart} {t : unitInterval} {v : V}
    (h : barycentric G (edgePoint G d t) = barycentric G (vertex G v)) :
    t = 0 ∧ d.fst = v ∨ t = 1 ∧ d.snd = v := by
  by_cases hfv : d.fst = v
  · left
    refine ⟨?_, hfv⟩
    have hs := congr_fun h d.snd
    have hne : v ≠ d.snd := by
      intro hv
      exact d.fst_ne_snd (hfv.trans hv)
    have : (t : ℝ) = 0 := by
      simpa [barycentric_edgePoint, barycentric_vertex, Pi.single_apply, hne, eq_comm] using hs
    exact Subtype.ext (by rw [Set.Icc.coe_zero]; exact this)
  · by_cases hsv : d.snd = v
    · right
      refine ⟨?_, hsv⟩
      have hs := congr_fun h d.fst
      have hne : v ≠ d.fst := Ne.symm hfv
      have : 1 - (t : ℝ) = 0 := by
        simpa [barycentric_edgePoint, barycentric_vertex, Pi.single_apply, hfv, hne, eq_comm,
          d.fst_ne_snd] using hs
      exact Subtype.ext (by rw [Set.Icc.coe_one]; linarith only [this])
    · have hs₀ := congr_fun h d.fst
      have hs₁ := congr_fun h d.snd
      have ht₀ : (t : ℝ) = 0 := by
        simpa [barycentric_edgePoint, barycentric_vertex, Pi.single_apply, hfv, hsv, eq_comm,
          d.fst_ne_snd] using hs₁
      have ht₁ : (t : ℝ) = 1 := by
        have hs₀' : (0 : ℝ) = 1 - (t : ℝ) := by
          simpa [barycentric_edgePoint, barycentric_vertex, Pi.single_apply, hfv, hsv, eq_comm,
            d.snd_ne_fst] using hs₀
        linarith only [hs₀']
      linarith

private theorem barycentric_edge_eq_edgePoint {d d' : G.Dart} {t t' : unitInterval}
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (ht₀' : t' ≠ 0) (ht₁' : t' ≠ 1)
    (h : barycentric G (edgePoint G d t) = barycentric G (edgePoint G d' t')) :
    (d' = d ∧ t' = t) ∨ (d' = d.symm ∧ t' = unitInterval.symm t) := by
  have htpos : 0 < (t : ℝ) :=
    lt_of_le_of_ne t.2.1 (Ne.symm (unitInterval.coe_ne_zero.mpr ht₀))
  have htlt : (t : ℝ) < 1 :=
    lt_of_le_of_ne t.2.2 (unitInterval.coe_ne_one.mpr ht₁)
  have htpos' : 0 < (t' : ℝ) :=
    lt_of_le_of_ne t'.2.1 (Ne.symm (unitInterval.coe_ne_zero.mpr ht₀'))
  have htlt' : (t' : ℝ) < 1 :=
    lt_of_le_of_ne t'.2.2 (unitInterval.coe_ne_one.mpr ht₁')
  have hedge : dartEdge d = dartEdge d' := by
    apply Subtype.ext
    apply Sym2.ext
    intro i
    constructor
    · intro hi
      have hpos : 0 < barycentric G (edgePoint G d t) i := by
        rcases mem_dartEdge.mp hi with rfl | rfl
        · have hc : barycentric G (edgePoint G d t) d.fst = 1 - (t : ℝ) := by
            simp [barycentric_edgePoint, d.fst_ne_snd]
          rw [hc]
          linarith
        · have hc : barycentric G (edgePoint G d t) d.snd = (t : ℝ) := by
            simp [barycentric_edgePoint, eq_comm]
          rw [hc]
          exact htpos
      have hpos' : 0 < barycentric G (edgePoint G d' t') i := by
        rw [← congr_fun h i]
        exact hpos
      exact mem_dartEdge.mpr (barycentric_edge_coord_pos G htpos' htlt' hpos')
    · intro hi
      have hpos : 0 < barycentric G (edgePoint G d' t') i := by
        rcases mem_dartEdge.mp hi with rfl | rfl
        · have hc : barycentric G (edgePoint G d' t') d'.fst = 1 - (t' : ℝ) := by
            simp [barycentric_edgePoint, d'.fst_ne_snd]
          rw [hc]
          linarith
        · have hc : barycentric G (edgePoint G d' t') d'.snd = (t' : ℝ) := by
            simp [barycentric_edgePoint, eq_comm]
          rw [hc]
          exact htpos'
      have hpos' : 0 < barycentric G (edgePoint G d t) i := by
        rw [congr_fun h i]
        exact hpos
      exact mem_dartEdge.mpr (barycentric_edge_coord_pos G htpos htlt hpos')
  rcases (dartEdge_eq_iff.mp hedge) with hd | hd
  · left
    refine ⟨hd.symm, ?_⟩
    have hs := congr_fun h d.snd
    have heq : (t : ℝ) = (t' : ℝ) := by
      subst d'
      simpa [barycentric_edgePoint, Pi.single_apply, eq_comm, d.snd_ne_fst] using hs
    exact Subtype.ext heq.symm
  · right
    have hd' : d' = d.symm := by
      apply Dart.ext
      exact congrArg Prod.swap (congrArg Dart.toProd hd.symm)
    refine ⟨hd', ?_⟩
    have hs := congr_fun h d.snd
    have hs' : (t : ℝ) = 1 - (t' : ℝ) := by
      simpa [barycentric_edgePoint, Pi.single_apply, eq_comm, d.snd_ne_fst,
        d'.fst_ne_snd, hd] using hs
    have heq : (t' : ℝ) = 1 - (t : ℝ) := by linarith
    apply Subtype.ext
    rw [unitInterval.coe_symm_eq]
    exact heq

/-- The barycentric map is injective. -/
theorem barycentric_injective : Function.Injective (barycentric G) := by
  classical
  intro x
  refine ind G (p := fun x => ∀ y, barycentric G x = barycentric G y → x = y) ?_ ?_ x
  · intro v y
    refine ind G (p := fun y => barycentric G (vertex G v) = barycentric G y →
      vertex G v = y) ?_ ?_ y
    · intro w h
      by_contra hvw
      have hv := congr_fun h v
      simp [barycentric_vertex, Pi.single_apply, eq_comm] at hv
      exact hvw (congrArg (vertex G) hv)
    · intro d t h
      have h' := barycentric_edge_eq_vertex G h.symm
      rcases h' with ⟨ht, hd⟩ | ⟨ht, hd⟩
      · rw [ht, edgePoint_zero]
        exact congrArg (vertex G) hd.symm
      · rw [ht, edgePoint_one]
        exact congrArg (vertex G) hd.symm
  · intro d t y
    refine ind G (p := fun y => barycentric G (edgePoint G d t) = barycentric G y →
      edgePoint G d t = y) ?_ ?_ y
    · intro v h
      rcases barycentric_edge_eq_vertex G h with ⟨ht, hd⟩ | ⟨ht, hd⟩
      · rw [ht, edgePoint_zero]
        exact congrArg (vertex G) hd
      · rw [ht, edgePoint_one]
        exact congrArg (vertex G) hd
    · intro d' t' h
      by_cases ht₀ : t = 0
      · rw [ht₀, edgePoint_zero]
        have h' := barycentric_edge_eq_vertex G (by
          simpa [ht₀, edgePoint_zero] using h.symm)
        rcases h' with ⟨ht', hd'⟩ | ⟨ht', hd'⟩
        · rw [ht', edgePoint_zero]
          exact congrArg (vertex G) hd'.symm
        · rw [ht', edgePoint_one]
          exact congrArg (vertex G) hd'.symm
      · by_cases ht₁ : t = 1
        · rw [ht₁, edgePoint_one]
          have h' := barycentric_edge_eq_vertex G (by
            simpa [ht₁, edgePoint_one] using h.symm)
          rcases h' with ⟨ht', hd'⟩ | ⟨ht', hd'⟩
          · rw [ht', edgePoint_zero]
            exact congrArg (vertex G) hd'.symm
          · rw [ht', edgePoint_one]
            exact congrArg (vertex G) hd'.symm
        · by_cases ht₀' : t' = 0
          · rw [ht₀', edgePoint_zero]
            have h' := barycentric_edge_eq_vertex G (by
              simpa [ht₀', edgePoint_zero] using h)
            rcases h' with ⟨ht', hd'⟩ | ⟨ht', hd'⟩
            · rw [ht', edgePoint_zero]
              exact congrArg (vertex G) hd'
            · rw [ht', edgePoint_one]
              exact congrArg (vertex G) hd'
          · by_cases ht₁' : t' = 1
            · rw [ht₁', edgePoint_one]
              have h' := barycentric_edge_eq_vertex G (by
                simpa [ht₁', edgePoint_one] using h)
              rcases h' with ⟨ht', hd'⟩ | ⟨ht', hd'⟩
              · rw [ht', edgePoint_zero]
                exact congrArg (vertex G) hd'
              · rw [ht', edgePoint_one]
                exact congrArg (vertex G) hd'
            · rcases barycentric_edge_eq_edgePoint G ht₀ ht₁ ht₀' ht₁' h with
                ⟨hd, ht⟩ | ⟨hd, ht⟩
              · rw [hd, ht]
              · rw [hd, ht, edgePoint_symm]

/-- The realization is Hausdorff. -/
theorem t2Space_realization : T2Space (Realization G) :=
  T2Space.of_injective_continuous (barycentric_injective G) (barycentric G).continuous

/-- An edge point is a vertex exactly at one of its endpoints. -/
theorem edgePoint_eq_vertex_iff {d : G.Dart} {t : unitInterval} {v : V} :
    edgePoint G d t = vertex G v ↔ (t = 0 ∧ d.fst = v) ∨ (t = 1 ∧ d.snd = v) := by
  constructor
  · intro h
    exact barycentric_edge_eq_vertex G (congrArg (barycentric G) h)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact edgePoint_zero G d
    · exact edgePoint_one G d

/-- Interior points on graph edges are identified only by reversal. -/
theorem edgePoint_eq_edgePoint_iff {d d' : G.Dart} {t t' : unitInterval}
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    edgePoint G d t = edgePoint G d' t' ↔
      (d' = d ∧ t' = t) ∨ (d' = d.symm ∧ t' = unitInterval.symm t) := by
  constructor
  · intro h
    have ht₀' : t' ≠ 0 := by
      intro ht'
      subst t'
      have hv := (edgePoint_eq_vertex_iff G).mp (h.trans (edgePoint_zero G d'))
      rcases hv with ⟨ht, _⟩ | ⟨ht, _⟩
      · exact ht₀ ht
      · exact ht₁ ht
    have ht₁' : t' ≠ 1 := by
      intro ht'
      subst t'
      have hv := (edgePoint_eq_vertex_iff G).mp (h.trans (edgePoint_one G d'))
      rcases hv with ⟨ht, _⟩ | ⟨ht, _⟩
      · exact ht₀ ht
      · exact ht₁ ht
    have h' := barycentric_edge_eq_edgePoint G ht₀ ht₁
      ht₀' ht₁'
      (congrArg (barycentric G) h)
    exact h'
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact (edgePoint_symm G d t).symm

private theorem locallyPathConnectedSpace_unitInterval :
    LocallyPathConnectedSpace unitInterval := by
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

/-- The graph realization is locally path-connected. -/
theorem locallyPathConnectedSpace_realization :
    LocallyPathConnectedSpace (Realization G) := by
  let _ : TopologicalSpace V := ⊥
  let _ : DiscreteTopology V := ⟨rfl⟩
  let _ : LocallyPathConnectedSpace unitInterval := locallyPathConnectedSpace_unitInterval
  let _ : LocallyPathConnectedSpace (Cells G) := by
    change LocallyPathConnectedSpace (V ⊕ Σ _ : G.Dart, unitInterval)
    infer_instance
  change LocallyPathConnectedSpace (Quot (CellRel G))
  infer_instance

/-- A graph embedding induces an injective map on realizations. -/
theorem realizationMap_injective {W : Type v} {H : SimpleGraph W} (φ : G ↪g H) :
    Function.Injective (realizationMap φ.toHom) := by
  classical
  have hmapDart : Function.Injective (φ.toHom.mapDart) := by
    intro d d' h
    apply Dart.ext
    have hp : (φ d.fst, φ d.snd) = (φ d'.fst, φ d'.snd) := by
      have hp := congrArg Dart.toProd h
      change (φ d.fst, φ d.snd) = (φ d'.fst, φ d'.snd) at hp
      exact hp
    exact Prod.ext (φ.injective (congrArg Prod.fst hp))
      (φ.injective (congrArg Prod.snd hp))
  have hsymm (d : G.Dart) :
      (φ.toHom.mapDart d).symm = φ.toHom.mapDart d.symm := by
    apply Dart.ext
    rfl
  have hVE {v : V} {d : G.Dart} {t : unitInterval}
      (h : realizationMap φ.toHom (vertex G v) =
        realizationMap φ.toHom (edgePoint G d t)) :
      vertex G v = edgePoint G d t := by
    have h' := (edgePoint_eq_vertex_iff H).mp h.symm
    rcases h' with ⟨ht, hd⟩ | ⟨ht, hd⟩
    · have ht' : t = 0 := ht
      rw [ht', edgePoint_zero]
      have hd' : φ d.fst = φ v := by
        simpa [SimpleGraph.Hom.mapDart_apply] using hd
      exact congrArg (vertex G) (φ.injective hd').symm
    · have ht' : t = 1 := ht
      rw [ht', edgePoint_one]
      have hd' : φ d.snd = φ v := by
        simpa [SimpleGraph.Hom.mapDart_apply] using hd
      exact congrArg (vertex G) (φ.injective hd').symm
  have hEV {v : V} {d : G.Dart} {t : unitInterval}
      (h : realizationMap φ.toHom (edgePoint G d t) =
        realizationMap φ.toHom (vertex G v)) :
      edgePoint G d t = vertex G v := by
    have h' := (edgePoint_eq_vertex_iff H).mp h
    rcases h' with ⟨ht, hd⟩ | ⟨ht, hd⟩
    · have ht' : t = 0 := ht
      rw [ht', edgePoint_zero]
      have hd' : φ d.fst = φ v := by
        simpa [SimpleGraph.Hom.mapDart_apply] using hd
      exact congrArg (vertex G) (φ.injective hd')
    · have ht' : t = 1 := ht
      rw [ht', edgePoint_one]
      have hd' : φ d.snd = φ v := by
        simpa [SimpleGraph.Hom.mapDart_apply] using hd
      exact congrArg (vertex G) (φ.injective hd')
  intro x
  refine ind G (p := fun x => ∀ y, realizationMap φ.toHom x = realizationMap φ.toHom y →
    x = y) ?_ ?_ x
  · intro v y
    refine ind G (p := fun y => realizationMap φ.toHom (vertex G v) =
      realizationMap φ.toHom y → vertex G v = y) ?_ ?_ y
    · intro w h
      exact congrArg (vertex G) (φ.injective (vertex_injective H (by simpa using h)))
    · intro d t h
      exact hVE h
  · intro d t y
    refine ind G (p := fun y => realizationMap φ.toHom (edgePoint G d t) =
      realizationMap φ.toHom y → edgePoint G d t = y) ?_ ?_ y
    · intro v h
      exact hEV h
    · intro d' t' h
      by_cases ht₀ : t = 0
      · rw [ht₀, edgePoint_zero]
        apply hVE
        simpa [ht₀, realizationMap_edgePoint, realizationMap_vertex, edgePoint_zero] using h
      · by_cases ht₁ : t = 1
        · rw [ht₁, edgePoint_one]
          apply hVE
          simpa [ht₁, realizationMap_edgePoint, realizationMap_vertex, edgePoint_one] using h
        · by_cases ht₀' : t' = 0
          · rw [ht₀', edgePoint_zero]
            apply hEV
            simpa [ht₀', realizationMap_edgePoint, realizationMap_vertex, edgePoint_zero] using h
          · by_cases ht₁' : t' = 1
            · rw [ht₁', edgePoint_one]
              apply hEV
              simpa [ht₁', realizationMap_edgePoint, realizationMap_vertex, edgePoint_one] using h
            · have h' := (edgePoint_eq_edgePoint_iff H ht₀ ht₁).mp h
              rcases h' with ⟨hd, ht⟩ | ⟨hd, ht⟩
              · have hd' : d' = d := hmapDart hd
                have ht' : t' = t := ht
                rw [hd', ht']
              · have hdmap : φ.toHom.mapDart d' = φ.toHom.mapDart d.symm :=
                  hd.trans (hsymm d)
                have hd' : d' = d.symm := hmapDart hdmap
                have ht' : t' = unitInterval.symm t := ht
                rw [hd', ht']
                exact (edgePoint_symm G d t).symm

end realization

section level

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- The realization of the level graph together with the crossing edges. -/
def LevelPiece (c : ℝ) : Type u :=
  Realization (G.induce {v | h v = c}) ⊕ {e : G.edgeSet // EdgeCrosses G h c e}

/-- The level-graph summand has its realization topology and the crossing summand is discrete. -/
instance instTopologicalSpaceLevelPiece (c : ℝ) : TopologicalSpace (LevelPiece G h c) :=
  @instTopologicalSpaceSum (Realization (G.induce {v | h v = c}))
    {e : G.edgeSet // EdgeCrosses G h c e} inferInstance ⊥

private theorem level_realization_height {c : ℝ}
    (z : Realization (G.induce {v | h v = c})) :
    plHeight G h (realizationMap (Embedding.induce _).toHom z) = c := by
  induction z using ind (G.induce {v | h v = c}) with
  | vertex v =>
      simp only [realizationMap_vertex, plHeight_vertex]
      exact v.property
  | edgePoint d t =>
      rw [realizationMap_edgePoint, plHeight_edgePoint]
      have hd : h ((Embedding.induce (G := G) {v | h v = c}).toHom.mapDart d).fst =
          h ((Embedding.induce (G := G) {v | h v = c}).toHom.mapDart d).snd := by
        simpa [SimpleGraph.Hom.mapDart_apply] using
          (d.fst.property.trans d.snd.property.symm)
      rw [dartHeight_of_eq h hd]
      change h (d.fst : V) = c
      exact d.fst.property

/-- The level-piece map sends level-graph points to the closed level and crossing edges to their
crossing points. -/
noncomputable def levelPieceMap (c : ℝ) : C(LevelPiece G h c, ClosedLevel G h c) := by
  letI : TopologicalSpace {e : G.edgeSet // EdgeCrosses G h c e} := ⊥
  letI : DiscreteTopology {e : G.edgeSet // EdgeCrosses G h c e} := ⟨rfl⟩
  let f : C(Realization (G.induce {v | h v = c}), ClosedLevel G h c) :=
    ⟨fun z => ⟨realizationMap (Embedding.induce _).toHom z, level_realization_height G h z⟩,
      (realizationMap (Embedding.induce _).toHom).continuous.subtype_mk
        (level_realization_height G h)⟩
  exact
    { toFun := Sum.elim f (crossingPoint G h)
      continuous_toFun := f.continuous.sumElim continuous_of_discreteTopology }

private theorem levelPieceMap_inl (c : ℝ)
    (z : Realization (G.induce {v | h v = c})) :
    (levelPieceMap G h c (Sum.inl z)).1 =
      realizationMap (Embedding.induce (G := G) {v | h v = c}).toHom z := by
  rfl

private theorem levelPieceMap_inr (c : ℝ)
    (e : {e : G.edgeSet // EdgeCrosses G h c e}) :
    (levelPieceMap G h c (Sum.inr e)).1 = crossingPoint G h e := by
  rfl

private theorem exists_dart_crossing' {c : ℝ}
    (e : {e : G.edgeSet // EdgeCrosses G h c e}) :
    ∃ d : G.Dart, dartEdge d = e.1 ∧ h d.fst < c ∧ c < h d.snd := by
  obtain ⟨d, hd⟩ := exists_dartEdge_eq e.1
  have hcross : EdgeCrosses G h c (dartEdge d) := by
    rw [hd]
    exact e.2
  obtain ⟨hmin, hmax⟩ := (edgeCrosses_dartEdge_iff d).1 hcross
  rcases le_total (h d.fst) (h d.snd) with hab | hab
  · refine ⟨d, hd, ?_, ?_⟩
    · rw [min_eq_left hab] at hmin
      exact hmin
    · rw [max_eq_right hab] at hmax
      exact hmax
  · refine ⟨d.symm, ?_, ?_, ?_⟩
    · rw [dartEdge_symm]
      exact hd
    · rw [min_eq_right hab] at hmin
      exact hmin
    · rw [max_eq_left hab] at hmax
      exact hmax

private theorem crossingPoint_spec' {c : ℝ}
    (e : {e : G.edgeSet // EdgeCrosses G h c e}) :
    ∃ d : G.Dart, ∃ h₁ : h d.fst < c, ∃ h₂ : c < h d.snd,
      dartEdge d = e.1 ∧
        (crossingPoint G h e).1 = edgePoint G d (crossingParam G h h₁ h₂) := by
  obtain ⟨d, hd, h₁, h₂⟩ := exists_dart_crossing' G h e
  refine ⟨d, h₁, h₂, hd, ?_⟩
  exact (eq_crossingPoint G h e d hd (crossingParam G h h₁ h₂)
    (dartHeight_crossingParam G h h₁ h₂)).symm

private theorem crossingParam_interior {c : ℝ} {d : G.Dart}
    (h₁ : h d.fst < c) (h₂ : c < h d.snd) :
    0 < (crossingParam G h h₁ h₂ : ℝ) ∧ (crossingParam G h h₁ h₂ : ℝ) < 1 := by
  constructor
  · dsimp [crossingParam]
    exact div_pos (by linarith) (by linarith)
  · dsimp [crossingParam]
    apply (div_lt_one (by linarith)).2
    linarith

private theorem level_crossing_not_level_graph {c : ℝ}
    (z : Realization (G.induce {v | h v = c}))
    (e : {e : G.edgeSet // EdgeCrosses G h c e}) :
    realizationMap (Embedding.induce _).toHom z ≠ (crossingPoint G h e).1 := by
  classical
  obtain ⟨d', h₁, h₂, hd', hpoint⟩ := crossingPoint_spec' G h e
  have hi := crossingParam_interior G h h₁ h₂
  intro hz
  have hcross_eq : edgePoint G d' (crossingParam G h h₁ h₂) =
      realizationMap (Embedding.induce (G := G) {v | h v = c}).toHom z :=
    hpoint.symm.trans hz.symm
  induction z using ind (G.induce {v | h v = c}) with
  | vertex v =>
      have hv := (edgePoint_eq_vertex_iff G).mp (by
        simpa [realizationMap_vertex] using hcross_eq)
      rcases hv with ⟨ht, _⟩ | ⟨ht, _⟩
      · exact (ne_of_gt hi.1)
          (congrArg (fun s : unitInterval => (s : ℝ)) ht)
      · exact (ne_of_lt hi.2)
          (congrArg (fun s : unitInterval => (s : ℝ)) ht)
  | edgePoint d t =>
      by_cases ht₀ : t = 0
      · have hv := (edgePoint_eq_vertex_iff G).mp (by
          simpa [realizationMap_edgePoint, realizationMap_vertex, ht₀, edgePoint_zero]
            using hcross_eq)
        rcases hv with ⟨ht, _⟩ | ⟨ht, _⟩
        · exact (ne_of_gt hi.1)
            (congrArg (fun s : unitInterval => (s : ℝ)) ht)
        · exact (ne_of_lt hi.2)
            (congrArg (fun s : unitInterval => (s : ℝ)) ht)
      · by_cases ht₁ : t = 1
        · have hv := (edgePoint_eq_vertex_iff G).mp (by
            simpa [realizationMap_edgePoint, realizationMap_vertex, ht₁, edgePoint_one]
              using hcross_eq)
          rcases hv with ⟨ht, _⟩ | ⟨ht, _⟩
          · exact (ne_of_gt hi.1)
              (congrArg (fun s : unitInterval => (s : ℝ)) ht)
          · exact (ne_of_lt hi.2)
              (congrArg (fun s : unitInterval => (s : ℝ)) ht)
        · have heq : edgePoint G
              ((Embedding.induce (G := G) {v | h v = c}).toHom.mapDart d) t =
              edgePoint G d' (crossingParam G h h₁ h₂) := by
            calc
              edgePoint G
                  ((Embedding.induce (G := G) {v | h v = c}).toHom.mapDart d) t =
                  (realizationMap (Embedding.induce (G := G) {v | h v = c}).toHom
                    (edgePoint (G.induce {v | h v = c}) d t)) :=
                (realizationMap_edgePoint _ _ _).symm
              _ = (crossingPoint G h e).1 := hz
              _ = edgePoint G d' (crossingParam G h h₁ h₂) := hpoint
          have hcases := (edgePoint_eq_edgePoint_iff G ht₀ ht₁).mp heq
          rcases hcases with ⟨hdart, _⟩ | ⟨hdart, _⟩
          · have hsrc : h
                ((Embedding.induce (G := G) {v | h v = c}).toHom.mapDart d).fst = c :=
              by
                change h (d.fst : V) = c
                exact d.fst.property
            exact (ne_of_lt h₁) (by simpa [hdart] using hsrc)
          · have hsrc : h
                ((Embedding.induce (G := G) {v | h v = c}).toHom.mapDart d).snd = c :=
              by
                change h (d.snd : V) = c
                exact d.snd.property
            exact (ne_of_lt h₁) (by simpa [hdart] using hsrc)

theorem levelPieceMap_bijective (c : ℝ) : Function.Bijective (levelPieceMap G h c) := by
  classical
  constructor
  · intro x y hxy
    rcases x with x | e <;> rcases y with y | e'
    · have hmap : realizationMap (Embedding.induce _).toHom x =
          realizationMap (Embedding.induce _).toHom y := by
        change (⟨realizationMap (Embedding.induce _).toHom x, _⟩ : ClosedLevel G h c) =
          ⟨realizationMap (Embedding.induce _).toHom y, _⟩ at hxy
        exact congrArg Subtype.val hxy
      exact congrArg Sum.inl
        (realizationMap_injective (G.induce {v | h v = c})
          (Embedding.induce (G := G) {v | h v = c}) hmap)
    · change (⟨realizationMap (Embedding.induce _).toHom x, _⟩ : ClosedLevel G h c) =
        crossingPoint G h e' at hxy
      exact (level_crossing_not_level_graph G h x e').elim (congrArg Subtype.val hxy)
    · change crossingPoint G h e =
        (⟨realizationMap (Embedding.induce _).toHom y, _⟩ : ClosedLevel G h c) at hxy
      exact (level_crossing_not_level_graph G h y e).elim (congrArg Subtype.val hxy.symm)
    · obtain ⟨d, h₁, h₂, hd, hpoint⟩ := crossingPoint_spec' G h e
      obtain ⟨d', h₁', h₂', hd', hpoint'⟩ := crossingPoint_spec' G h e'
      change crossingPoint G h e = crossingPoint G h e' at hxy
      have heq : edgePoint G d (crossingParam G h h₁ h₂) =
          edgePoint G d' (crossingParam G h h₁' h₂') := by
        rw [← hpoint, ← hpoint']
        exact congrArg Subtype.val hxy
      have hi := crossingParam_interior G h h₁ h₂
      have ht₀ : crossingParam G h h₁ h₂ ≠ 0 :=
        unitInterval.coe_ne_zero.mp hi.1.ne'
      have ht₁ : crossingParam G h h₁ h₂ ≠ 1 :=
        unitInterval.coe_ne_one.mp hi.2.ne
      have hc := (edgePoint_eq_edgePoint_iff G ht₀ ht₁).mp heq
      rcases hc with ⟨hc, _⟩ | ⟨hc, _⟩
      · apply congrArg Sum.inr
        apply Subtype.ext
        have heq : dartEdge d = dartEdge d' := by rw [hc]
        exact hd.symm.trans (heq.trans hd')
      · apply congrArg Sum.inr
        apply Subtype.ext
        have heq : dartEdge d = dartEdge d' := by
          rw [hc, dartEdge_symm]
        exact hd.symm.trans (heq.trans hd')
  · intro z
    rcases z with ⟨z, hz⟩
    induction z using ind G with
    | vertex v =>
        have hv : h v = c := by simpa [plHeight_vertex] using hz
        refine ⟨Sum.inl (vertex (G.induce {v | h v = c}) ⟨v, hv⟩), ?_⟩
        apply Subtype.ext
        rfl
    | edgePoint d t =>
        have ht : dartHeight h d t = c := by simpa [plHeight_edgePoint] using hz
        by_cases hh : h d.fst = h d.snd
        · have hfst : h d.fst = c := (dartHeight_of_eq h hh t).symm.trans ht
          have hsnd : h d.snd = c := hh.symm.trans hfst
          let d' : (G.induce {v | h v = c}).Dart :=
            ⟨(⟨d.fst, hfst⟩, ⟨d.snd, hsnd⟩), d.adj⟩
          have hd' : (Embedding.induce (G := G) {v | h v = c}).toHom.mapDart d' = d := by
            apply Dart.ext
            rfl
          refine ⟨Sum.inl (edgePoint (G.induce {v | h v = c}) d' t), ?_⟩
          apply Subtype.ext
          rw [levelPieceMap_inl, realizationMap_edgePoint, hd']
        · by_cases ht₀ : t = 0
          · have hv : h d.fst = c := by
              exact (dartHeight_zero h d).symm.trans (by simpa [ht₀] using ht)
            refine ⟨Sum.inl (vertex (G.induce {v | h v = c}) ⟨d.fst, hv⟩), ?_⟩
            apply Subtype.ext
            rw [levelPieceMap_inl, realizationMap_vertex]
            show _ = edgePoint G d t
            rw [ht₀, edgePoint_zero]
            rfl
          · by_cases ht₁ : t = 1
            · have hv : h d.snd = c := by
                exact (dartHeight_one h d).symm.trans (by simpa [ht₁] using ht)
              refine ⟨Sum.inl (vertex (G.induce {v | h v = c}) ⟨d.snd, hv⟩), ?_⟩
              apply Subtype.ext
              rw [levelPieceMap_inl, realizationMap_vertex]
              show _ = edgePoint G d t
              rw [ht₁, edgePoint_one]
              rfl
            · have hne : h d.fst ≠ h d.snd := hh
              have hfst : h d.fst ≠ c := by
                intro hfc
                have hzero : dartHeight h d 0 = dartHeight h d t := by
                  rw [dartHeight_zero, hfc, ht]
                exact ht₀ (dartHeight_injective h hne hzero).symm
              have hsnd : h d.snd ≠ c := by
                intro hsc
                have hone : dartHeight h d 1 = dartHeight h d t := by
                  rw [dartHeight_one, hsc, ht]
                exact ht₁ (dartHeight_injective h hne hone).symm
              have hcross : EdgeCrosses G h c (dartEdge d) := by
                rw [edgeCrosses_dartEdge_iff]
                rcases le_total (h d.fst) (h d.snd) with hab | hab
                · rw [min_eq_left hab, max_eq_right hab]
                  constructor
                  · have hle : h d.fst ≤ c := by
                      rw [← ht]
                      unfold dartHeight
                      nlinarith [mul_nonneg t.2.1 (sub_nonneg.2 hab),
                        mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hab)]
                    exact lt_of_le_of_ne hle hfst
                  · have hle : c ≤ h d.snd := by
                      rw [← ht]
                      unfold dartHeight
                      nlinarith [mul_nonneg t.2.1 (sub_nonneg.2 hab),
                        mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hab)]
                    exact lt_of_le_of_ne hle (Ne.symm hsnd)
                · rw [min_eq_right hab, max_eq_left hab]
                  constructor
                  · have hle : h d.snd ≤ c := by
                      rw [← ht]
                      unfold dartHeight
                      nlinarith [mul_nonneg t.2.1 (sub_nonneg.2 hab),
                        mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hab)]
                    exact lt_of_le_of_ne hle hsnd
                  · have hle : c ≤ h d.fst := by
                      rw [← ht]
                      unfold dartHeight
                      nlinarith [mul_nonneg t.2.1 (sub_nonneg.2 hab),
                        mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hab)]
                    exact lt_of_le_of_ne hle (Ne.symm hfst)
              let e : {e : G.edgeSet // EdgeCrosses G h c e} := ⟨dartEdge d, hcross⟩
              refine ⟨Sum.inr e, ?_⟩
              apply Subtype.ext
              exact (eq_crossingPoint G h e d rfl t ht).symm

variable [Finite V]

/-- The level piece is compact. -/
theorem compactSpace_levelPiece (c : ℝ) : CompactSpace (LevelPiece G h c) := by
  let _ : CompactSpace (Realization (G.induce {v | h v = c})) :=
    compactSpace_realization (G.induce {v | h v = c})
  let _ : TopologicalSpace {e : G.edgeSet // EdgeCrosses G h c e} := ⊥
  let _ : Finite {e : G.edgeSet // EdgeCrosses G h c e} := Subtype.finite
  let _ : CompactSpace {e : G.edgeSet // EdgeCrosses G h c e} :=
    @Finite.compactSpace _ ⊥ inferInstance
  unfold LevelPiece
  infer_instance

/-- The level-piece map is a homeomorphism onto the closed level. -/
noncomputable def levelPieceHomeomorph (c : ℝ) :
    LevelPiece G h c ≃ₜ ClosedLevel G h c := by
  letI : CompactSpace (LevelPiece G h c) := compactSpace_levelPiece G h c
  letI : T2Space (Realization G) := t2Space_realization G
  exact (levelPieceMap G h c).continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (levelPieceMap_bijective G h c))

/-- The homeomorphism evaluates to the level-piece map. -/
theorem levelPieceHomeomorph_apply (c : ℝ) (z : LevelPiece G h c) :
    levelPieceHomeomorph G h c z = levelPieceMap G h c z := by
  rfl

/-- The closed level is compact. -/
theorem compactSpace_closedLevel (c : ℝ) : CompactSpace (ClosedLevel G h c) := by
  let _ : CompactSpace (LevelPiece G h c) := compactSpace_levelPiece G h c
  let _ : T2Space (Realization G) := t2Space_realization G
  exact (levelPieceHomeomorph G h c).compactSpace

/-- The closed level is locally path-connected. -/
theorem locallyPathConnectedSpace_closedLevel (c : ℝ) :
    LocallyPathConnectedSpace (ClosedLevel G h c) := by
  let _ : TopologicalSpace {e : G.edgeSet // EdgeCrosses G h c e} := ⊥
  let _ : DiscreteTopology {e : G.edgeSet // EdgeCrosses G h c e} := ⟨rfl⟩
  let _ : LocallyPathConnectedSpace (Realization (G.induce {v | h v = c})) :=
    locallyPathConnectedSpace_realization _
  let _ : LocallyPathConnectedSpace {e : G.edgeSet // EdgeCrosses G h c e} := by
    infer_instance
  let _ : LocallyPathConnectedSpace (LevelPiece G h c) := by
    unfold LevelPiece
    infer_instance
  let _ : T2Space (Realization G) := t2Space_realization G
  exact (levelPieceHomeomorph G h c).symm.isOpenEmbedding.locallyPathConnectedSpace

end level

/-! (C) the presentation -/
section presentation

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) {n : ℕ} (S : CriticalValues n)

private theorem exists_spanDart {p q : ℝ} (_hpq : p < q) (y : SpanEdge G h p q) :
    ∃ d : G.Dart, dartEdge d = y.1 ∧ h d.fst ≤ p ∧ q ≤ h d.snd := by
  rcases y.2 with ⟨d, hd, hmin, hmax⟩
  rcases le_total (h d.fst) (h d.snd) with hab | hab
  · refine ⟨d, hd, ?_, ?_⟩
    · rw [min_eq_left hab] at hmin
      exact hmin
    · rw [max_eq_right hab] at hmax
      exact hmax
  · refine ⟨d.symm, ?_, ?_, ?_⟩
    · rw [dartEdge_symm]
      exact hd
    · rw [min_eq_right hab] at hmin
      exact hmin
    · rw [max_eq_left hab] at hmax
      exact hmax

/-- The upward dart of a spanning edge over a nonempty closed interval. -/
noncomputable def spanDart {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) : G.Dart :=
  Classical.choose (exists_spanDart G h hpq y)

/-- The defining edge and endpoint inequalities of `spanDart`. -/
theorem spanDart_spec {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) :
    dartEdge (spanDart G h hpq y) = y.1 ∧
      h (spanDart G h hpq y).fst ≤ p ∧ q ≤ h (spanDart G h hpq y).snd :=
  Classical.choose_spec (exists_spanDart G h hpq y)

private theorem spanDart_height_lt {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) :
    h (spanDart G h hpq y).fst < h (spanDart G h hpq y).snd := by
  have hd := spanDart_spec G h hpq y
  exact lt_of_lt_of_le (hd.2.1.trans_lt hpq) hd.2.2

private theorem spanDart_den_pos {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) :
    0 < h (spanDart G h hpq y).snd - h (spanDart G h hpq y).fst :=
  sub_pos.2 (spanDart_height_lt G h hpq y)

private theorem spanParam_mem {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) (t : Icc p q) :
    ((t : ℝ) - h (spanDart G h hpq y).fst) /
        (h (spanDart G h hpq y).snd - h (spanDart G h hpq y).fst) ∈ unitInterval := by
  have hden := spanDart_den_pos G h hpq y
  have h₁ := (spanDart_spec G h hpq y).2.1
  have h₂ := (spanDart_spec G h hpq y).2.2
  have ht₁ : p ≤ (t : ℝ) := t.2.1
  have ht₂ : (t : ℝ) ≤ q := t.2.2
  refine ⟨div_nonneg ?_ hden.le, (div_le_one hden).2 ?_⟩
  · linarith
  · linarith

private noncomputable def spanParam {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) :
    C(Icc p q, unitInterval) :=
  ⟨fun t => ⟨((t : ℝ) - h (spanDart G h hpq y).fst) /
      (h (spanDart G h hpq y).snd - h (spanDart G h hpq y).fst), spanParam_mem G h hpq y t⟩,
    Continuous.subtype_mk
      ((continuous_subtype_val.sub continuous_const).div_const _)
      (fun t => spanParam_mem G h hpq y t)⟩

/-- The point of a spanning edge at every height in its closed span. -/
noncomputable def spanPoint {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) :
    C(Icc p q, Realization G) :=
  ⟨fun t => edgePoint G (spanDart G h hpq y) (spanParam G h hpq y t),
    (continuous_edgePoint G (spanDart G h hpq y)).comp
      (spanParam G h hpq y).continuous⟩

private theorem spanPoint_apply {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) (t : Icc p q) :
    spanPoint G h hpq y t =
      edgePoint G (spanDart G h hpq y) (spanParam G h hpq y t) := rfl

private theorem coe_spanParam {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) (t : Icc p q) :
    (spanParam G h hpq y t : ℝ) =
      ((t : ℝ) - h (spanDart G h hpq y).fst) /
        (h (spanDart G h hpq y).snd - h (spanDart G h hpq y).fst) := rfl

/-- The graph-PL height of `spanPoint` is its interval parameter. -/
theorem plHeight_spanPoint {p q : ℝ} (hpq : p < q) (y : SpanEdge G h p q) (t : Icc p q) :
    plHeight G h (spanPoint G h hpq y t) = t := by
  rw [spanPoint_apply, plHeight_edgePoint]
  unfold dartHeight
  rw [coe_spanParam]
  have hden := spanDart_den_pos G h hpq y
  have hmul := div_mul_cancel₀
    ((t : ℝ) - h (spanDart G h hpq y).fst)
    hden.ne'
  linear_combination hmul

/-- The closed-level and spanning-edge cylinder presentation of a graph realization. -/
noncomputable def graphPLPresentation : CylinderPresentation.{u} n where
  V i := ClosedLevel G h (S.value i)
  E e := SpanEdge G h (S.value e.castSucc) (S.value e.succ)
  topV _ := inferInstance
  topE _ := ⊥
  left e := @ContinuousMap.mk _ _ ⊥ _
    (fun y => ⟨spanPoint G h (S.value_castSucc_lt_succ e) y
      (CylinderPresentation.segBot S e), by
        rw [plHeight_spanPoint]
        rfl⟩)
    continuous_bot
  right e := @ContinuousMap.mk _ _ ⊥ _
    (fun y => ⟨spanPoint G h (S.value_castSucc_lt_succ e) y
      (CylinderPresentation.segTop S e), by
        rw [plHeight_spanPoint]
        rfl⟩)
    continuous_bot

instance instDiscreteTopologyGraphPLPresentationE (e : Fin n) :
    DiscreteTopology ((graphPLPresentation G h S).E e) := ⟨rfl⟩

instance instFiniteGraphPLPresentationE [Finite V] (e : Fin n) :
    Finite ((graphPLPresentation G h S).E e) := by
  classical
  change Finite {a : G.edgeSet //
    EdgeSpans G h (S.value e.castSucc) (S.value e.succ) a}
  infer_instance

instance instCompactSpaceGraphPLPresentationV [Finite V] (i : Fin (n + 1)) :
    CompactSpace ((graphPLPresentation G h S).V i) := by
  change CompactSpace (ClosedLevel G h (S.value i))
  exact compactSpace_closedLevel G h _

instance instLocallyPathConnectedSpaceGraphPLPresentationV [Finite V] (i : Fin (n + 1)) :
    LocallyPathConnectedSpace ((graphPLPresentation G h S).V i) := by
  change LocallyPathConnectedSpace (ClosedLevel G h (S.value i))
  exact locallyPathConnectedSpace_closedLevel G h _

private noncomputable def graphPLCompatibleMaps :
    (graphPLPresentation G h S).CompatibleMaps S (Realization G) :=
  { vertex := fun i =>
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C((graphPLPresentation G h S).V i, Realization G))
    cylinder := fun e =>
      (⟨fun p => spanPoint G h (S.value_castSucc_lt_succ e) p.1 p.2,
        continuous_prod_of_discrete_left.2 fun y =>
          (spanPoint G h (S.value_castSucc_lt_succ e) y).continuous⟩ :
        C((graphPLPresentation G h S).Cylinder S e, Realization G))
    segBot_eq := fun _ _ => rfl
    segTop_eq := fun _ _ => rfl }

/-- The map from the cylinder presentation to the graph realization. -/
noncomputable def graphPLPresentationMap :
    C((graphPLPresentation G h S).Realization S, Realization G) :=
  CylinderPresentation.lift (graphPLCompatibleMaps G h S)

private theorem graphPLPresentationMap_ofCylinder (e : Fin n)
    (y : (graphPLPresentation G h S).E e) (t : CylinderPresentation.Seg S e) :
    graphPLPresentationMap G h S
        ((graphPLPresentation G h S).ofCylinder S e (y, t)) =
      spanPoint G h (S.value_castSucc_lt_succ e) y t := rfl

private theorem graphPLPresentationMap_ofStrip (e : Fin n)
    (p : (graphPLPresentation G h S).E e × (S.K e : Set ℝ)) :
    graphPLPresentationMap G h S ((graphPLPresentation G h S).ofStrip S e p) =
      spanPoint G h (S.value_castSucc_lt_succ e) p.1
        (CylinderPresentation.gapIncl S e p.2) := by
  rw [CylinderPresentation.ofStrip_eq_ofCylinder, graphPLPresentationMap_ofCylinder]

/-- The presentation map is the subtype inclusion on a vertex piece. -/
theorem graphPLPresentationMap_ofVertex (i : Fin (n + 1))
    (p : ClosedLevel G h (S.value i)) :
    graphPLPresentationMap G h S ((graphPLPresentation G h S).ofVertex S i p) = p.1 := rfl

/-- The presentation map preserves the graph-PL height. -/
theorem plHeight_graphPLPresentationMap (x : (graphPLPresentation G h S).Realization S) :
    plHeight G h (graphPLPresentationMap G h S x) =
      (graphPLPresentation G h S).height S x := by
  have hmap :
      (plHeight G h).comp (graphPLPresentationMap G h S) =
        (graphPLPresentation G h S).height S := by
    refine (graphPLPresentation G h S).hom_ext ?_ ?_
    · intro i p
      exact (p.2 : plHeight G h p.1 = S.value i)
    · intro e p
      exact plHeight_spanPoint G h (S.value_castSucc_lt_succ e) p.1 p.2
  exact congrArg (fun f => f x) hmap

/-- The presentation map is injective, without a covering hypothesis. -/
theorem graphPLPresentationMap_injective :
    Function.Injective (graphPLPresentationMap G h S) := by
  intro x y hxy
  rcases (graphPLPresentation G h S).exists_rep S x with ⟨i, p, rfl⟩ | ⟨e, p, rfl⟩
  · rcases (graphPLPresentation G h S).exists_rep S y with ⟨j, q, rfl⟩ | ⟨e', q, rfl⟩
    · have hpq : p.1 = q.1 := by
        rw [← graphPLPresentationMap_ofVertex G h S i p,
          ← graphPLPresentationMap_ofVertex G h S j q]
        exact hxy
      have hij : i = j := S.strictMono.injective (by
        calc
          S.value i = plHeight G h p.1 := p.2.symm
          _ = plHeight G h q.1 := congrArg (plHeight G h) hpq
          _ = S.value j := q.2)
      subst j
      apply congrArg ((graphPLPresentation G h S).ofVertex S i)
      exact Subtype.ext hpq
    · exfalso
      have hh : S.value i = (q.2 : ℝ) := by
        have := congrArg (plHeight G h) hxy
        rw [plHeight_graphPLPresentationMap, plHeight_graphPLPresentationMap] at this
        simpa [CylinderPresentation.height_ofVertex, CylinderPresentation.height_ofStrip] using this
      exact S.value_notMem_K e' i (hh.symm ▸ q.2.2)
  · rcases (graphPLPresentation G h S).exists_rep S y with ⟨j, q, rfl⟩ | ⟨e', q, rfl⟩
    · exfalso
      have hh : (p.2 : ℝ) = S.value j := by
        have := congrArg (plHeight G h) hxy
        rw [plHeight_graphPLPresentationMap, plHeight_graphPLPresentationMap] at this
        simpa [CylinderPresentation.height_ofStrip, CylinderPresentation.height_ofVertex] using this
      exact S.value_notMem_K e j (hh ▸ p.2.2)
    · have hh : (p.2 : ℝ) = (q.2 : ℝ) := by
        have := congrArg (plHeight G h) hxy
        rw [plHeight_graphPLPresentationMap, plHeight_graphPLPresentationMap] at this
        simpa [CylinderPresentation.height_ofStrip] using this
      have he : e = e' := S.eq_of_mem_K_of_mem_Icc
        (by rw [← hh]; exact p.2.2) (Ioo_subset_Icc_self q.2.2)
      subst e'
      have hpoint :
          spanPoint G h (S.value_castSucc_lt_succ e) p.1
              (CylinderPresentation.gapIncl S e p.2) =
            spanPoint G h (S.value_castSucc_lt_succ e) q.1
              (CylinderPresentation.gapIncl S e q.2) := by
        rw [graphPLPresentationMap_ofStrip G h S e p,
          graphPLPresentationMap_ofStrip G h S e q] at hxy
        exact hxy
      let d := spanDart G h (S.value_castSucc_lt_succ e) p.1
      let d' := spanDart G h (S.value_castSucc_lt_succ e) q.1
      have hd := spanDart_spec G h (S.value_castSucc_lt_succ e) p.1
      have hd' := spanDart_spec G h (S.value_castSucc_lt_succ e) q.1
      have htp : h d.fst < (p.2 : ℝ) := by
        dsimp [d]
        exact lt_of_le_of_lt hd.2.1 p.2.2.1
      have hsp : (p.2 : ℝ) < h d.snd := by
        exact lt_of_lt_of_le p.2.2.2 hd.2.2
      have htq : h d'.fst < (q.2 : ℝ) := by
        dsimp [d']
        exact lt_of_le_of_lt hd'.2.1 q.2.2.1
      have hsq : (q.2 : ℝ) < h d'.snd := by
        exact lt_of_lt_of_le q.2.2.2 hd'.2.2
      have hden : 0 < h d.snd - h d.fst := by linarith
      have hden' : 0 < h d'.snd - h d'.fst := by linarith
      have ht₀ :
          (⟨((p.2 : ℝ) - h d.fst) / (h d.snd - h d.fst), by
            refine ⟨div_nonneg (by linarith) hden.le, (div_le_one hden).2 (by linarith)⟩⟩ :
            unitInterval) ≠ 0 := by
        apply unitInterval.coe_ne_zero.mp
        exact div_ne_zero (sub_ne_zero.mpr htp.ne') hden.ne'
      have ht₁ :
          (⟨((p.2 : ℝ) - h d.fst) / (h d.snd - h d.fst), by
            refine ⟨div_nonneg (by linarith) hden.le, (div_le_one hden).2 (by linarith)⟩⟩ :
            unitInterval) ≠ 1 := by
        apply unitInterval.coe_ne_one.mp
        intro hone
        have := (div_eq_one_iff_eq hden.ne').1 hone
        linarith
      have hpp : edgePoint G d
            ⟨((p.2 : ℝ) - h d.fst) / (h d.snd - h d.fst), by
              refine ⟨div_nonneg (by linarith) hden.le, (div_le_one hden).2 (by linarith)⟩⟩ =
          edgePoint G d'
            ⟨((q.2 : ℝ) - h d'.fst) / (h d'.snd - h d'.fst), by
              refine ⟨div_nonneg (by linarith) hden'.le, (div_le_one hden').2 (by linarith)⟩⟩ := by
        simpa [spanPoint, spanParam, d, d', CylinderPresentation.gapIncl] using hpoint
      rcases (edgePoint_eq_edgePoint_iff G ht₀ ht₁).1 hpp with hdart | hdart
      · have hy : p.1 = q.1 := by
          apply Subtype.ext
          exact hd.1.symm.trans ((congrArg dartEdge hdart.1.symm).trans hd'.1)
        apply congrArg ((graphPLPresentation G h S).ofStrip S e)
        apply Prod.ext hy
        exact Subtype.ext hh
      · have hy : p.1 = q.1 := by
          apply Subtype.ext
          exact hd.1.symm.trans ((dartEdge_symm d).symm.trans
            ((congrArg dartEdge hdart.1.symm).trans hd'.1))
        apply congrArg ((graphPLPresentation G h S).ofStrip S e)
        apply Prod.ext hy
        exact Subtype.ext hh

/-- The presentation map is surjective when every vertex height is covered. -/
theorem graphPLPresentationMap_surjective {S : CriticalValues n} (hS : CoversVertexHeights S h) :
    Function.Surjective (graphPLPresentationMap G h S) := by
  intro z
  induction z using ind G with
  | vertex v =>
      obtain ⟨i, hi⟩ := hS v
      refine ⟨(graphPLPresentation G h S).ofVertex S i
        ⟨vertex G v, by simpa [plHeight_vertex] using hi.symm⟩, ?_⟩
      rw [graphPLPresentationMap_ofVertex]
  | edgePoint d t =>
      let c : ℝ := dartHeight h d t
      by_cases hlevel : ∃ i, S.value i = c
      · obtain ⟨i, hi⟩ := hlevel
        refine ⟨(graphPLPresentation G h S).ofVertex S i
          ⟨edgePoint G d t, by
            change plHeight G h (edgePoint G d t) = S.value i
            rw [plHeight_edgePoint, hi]⟩, ?_⟩
        rw [graphPLPresentationMap_ofVertex]
      · have hnot_level : ∀ i, S.value i ≠ c := by
          intro i hi
          exact hlevel ⟨i, hi⟩
        have hvbounds : ∀ v, h v ∈ Icc (S.value 0) (S.value (Fin.last n)) := by
          intro v
          obtain ⟨i, hi⟩ := hS v
          rw [← hi]
          exact ⟨S.strictMono.monotone (Fin.zero_le i),
            S.strictMono.monotone (Fin.le_last i)⟩
        have hrange := plHeight_mem_Icc_of_forall hvbounds (edgePoint G d t)
        have hcrange : c ∈ Icc (S.value 0) (S.value (Fin.last n)) := by
          simpa [c, plHeight_edgePoint] using hrange
        obtain ⟨piece, hpiece, huniq⟩ := S.exists_piece c
        have hcK : ∃ e : Fin n, c ∈ (S.K e : Set ℝ) := by
          cases piece with
          | star i => exact False.elim (hnot_level i (huniq i (S.value_mem_J i)))
          | gap e => exact ⟨e, hpiece⟩
          | lowerTail => exact (not_lt_of_ge hcrange.1 hpiece).elim
          | upperTail => exact (not_lt_of_ge hcrange.2 hpiece).elim
        obtain ⟨e, hce⟩ := hcK
        have hact : EdgeActive G h (S.K e) (dartEdge d) := by
          exact edgeActive_dartEdge_of_mem (I := S.K e) (by simpa [c] using hce)
        have hspan : EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d) := by
          let a : {a : G.edgeSet // EdgeActive G h (S.K e) a} :=
            ⟨dartEdge d, hact⟩
          exact (activeEdgeEquivSpans (G := G) (h := h) (S.value_castSucc_lt_succ e)
            (fun v => hS.notMem_K e v) a).2
        let y : SpanEdge G h (S.value e.castSucc) (S.value e.succ) := ⟨dartEdge d, hspan⟩
        refine ⟨(graphPLPresentation G h S).ofStrip S e (y, ⟨c, hce⟩), ?_⟩
        rw [CylinderPresentation.ofStrip_eq_ofCylinder,
          graphPLPresentationMap_ofCylinder]
        have hne : h d.fst ≠ h d.snd := by
          intro heq
          obtain ⟨i, hi⟩ := hS d.fst
          apply hnot_level i
          calc
            S.value i = h d.fst := hi
            _ = dartHeight h d t := (dartHeight_of_eq h heq t).symm
        have hsheight := plHeight_spanPoint G h (S.value_castSucc_lt_succ e) y
          (CylinderPresentation.gapIncl S e ⟨c, hce⟩)
        rw [spanPoint_apply, plHeight_edgePoint] at hsheight
        rw [spanPoint_apply]
        have hd' := spanDart_spec G h (S.value_castSucc_lt_succ e) y
        generalize spanParam G h (S.value_castSucc_lt_succ e) y
          (CylinderPresentation.gapIncl S e ⟨c, hce⟩) = s at hsheight ⊢
        generalize spanDart G h (S.value_castSucc_lt_succ e) y = d' at hsheight hd' ⊢
        have hsc : dartHeight h d' s = dartHeight h d t := hsheight
        have hde : dartEdge d' = dartEdge d := hd'.1
        rcases dartEdge_eq_iff.1 hde with rfl | rfl
        · exact congrArg (edgePoint G d') (dartHeight_injective h hne hsc)
        · have hst : s = unitInterval.symm t :=
            dartHeight_injective h (d := d.symm) hne.symm
              (hsc.trans (dartHeight_symm h d t).symm)
          rw [hst, edgePoint_symm]

/-- The compact Hausdorff homeomorphism induced by the presentation map. -/
noncomputable def graphPLPresentationHomeomorph [Finite V] {S : CriticalValues n}
    (hS : CoversVertexHeights S h) :
    (graphPLPresentation G h S).Realization S ≃ₜ Realization G := by
  letI : CompactSpace ((graphPLPresentation G h S).Realization S) :=
    (graphPLPresentation G h S).compactSpace S
  letI : T2Space (Realization G) := t2Space_realization G
  exact (graphPLPresentationMap G h S).continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨graphPLPresentationMap_injective G h S,
      graphPLPresentationMap_surjective G h hS⟩)

/-- Evaluation of `graphPLPresentationHomeomorph` is the presentation map. -/
theorem graphPLPresentationHomeomorph_apply [Finite V] {S : CriticalValues n}
    (hS : CoversVertexHeights S h) (x) :
    graphPLPresentationHomeomorph G h hS x = graphPLPresentationMap G h S x := by
  rfl

end presentation

/-! (D) component data and the identification -/
section identification

variable {V : Type u} [Finite V] (G : SimpleGraph V) (h : V → ℝ) {n : ℕ}
  (S : CriticalValues n)

private instance instFiniteGraphPLPresentationComponentV (i : Fin (n + 1)) :
    Finite (ZerothHomotopy ((graphPLPresentation G h S).V i)) := by
  change Finite (ZerothHomotopy (ClosedLevel G h (S.value i)))
  exact Finite.of_equiv _ (closedLevelComponentsEquiv G h (S.value i)).symm

private instance instFiniteGraphPLPresentationComponentE (e : Fin n) :
    Finite (ZerothHomotopy ((graphPLPresentation G h S).E e)) := by
  exact Finite.of_equiv _ (zerothHomotopyEquivOfDiscrete _).symm

private theorem zerothHomotopyEquivOfDiscrete_mk {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (x : A) :
    zerothHomotopyEquivOfDiscrete A (ZerothHomotopy.mk x) = x := by
  have hb : Function.Bijective (ZerothHomotopy.mk : A → ZerothHomotopy A) :=
    ⟨fun _ _ hx => joined_eq_of_discrete (Quotient.exact hx), ZerothHomotopy.mk_surjective⟩
  change (Equiv.ofBijective ZerothHomotopy.mk hb).symm
      (ZerothHomotopy.mk x) = x
  exact Equiv.ofBijective_symm_apply_apply _ hb x

private theorem graphPLReebData_left_eq (e : Fin n)
    (y : SpanEdge G h (S.value e.castSucc) (S.value e.succ)) :
    (graphPLReebData G h S).left e y =
      closedLevelComponentsEquiv G h (S.value e.castSucc)
        (ZerothHomotopy.mk ((graphPLPresentation G h S).left e y)) := by
  have hd := spanDart_spec G h (S.value_castSucc_lt_succ e) y
  have hval : ((graphPLPresentation G h S).left e y).1 =
      edgePoint G (spanDart G h (S.value_castSucc_lt_succ e) y)
        (spanParam G h (S.value_castSucc_lt_succ e) y (CylinderPresentation.segBot S e)) := rfl
  have hheight := plHeight_spanPoint G h (S.value_castSucc_lt_succ e) y
    (CylinderPresentation.segBot S e)
  rw [spanPoint_apply, plHeight_edgePoint] at hheight
  have hcoe := coe_spanParam G h (S.value_castSucc_lt_succ e) y
    (CylinderPresentation.segBot S e)
  generalize spanParam G h (S.value_castSucc_lt_succ e) y
    (CylinderPresentation.segBot S e) = s at hval hheight hcoe
  generalize spanDart G h (S.value_castSucc_lt_succ e) y = d at hd hval hheight hcoe
  have hheight' : dartHeight h d s = S.value e.castSucc := hheight
  by_cases hfst : h d.fst = S.value e.castSucc
  · have hs : s = 0 := by
      apply Subtype.ext
      rw [hcoe, Set.Icc.coe_zero]
      change (S.value e.castSucc - h d.fst) / (h d.snd - h d.fst) = 0
      rw [hfst, sub_self, zero_div]
    have hl : (graphPLPresentation G h S).left e y =
        (⟨vertex G d.fst, by
          rw [plHeight_vertex, hfst]
          exact Set.mem_singleton _⟩ : ClosedLevel G h (S.value e.castSucc)) := by
      apply Subtype.ext
      rw [hval, hs, edgePoint_zero]
    have hmem : d.fst ∈ (y.1 : Sym2 V) := by
      rw [← hd.1]
      exact fst_mem_dartEdge d
    rw [hl, closedLevelComponentsEquiv_mk_vertex G h d.fst hfst]
    exact graphPLReebData_left_of_mem G h S e y hmem hfst
  · have hne : ∀ v ∈ (y.1 : Sym2 V), h v ≠ S.value e.castSucc := by
      intro v hv hvp
      have hv' : v ∈ (dartEdge d : Sym2 V) := by
        rw [hd.1]
        exact hv
      rcases mem_dartEdge.mp hv' with rfl | rfl
      · exact hfst hvp
      · linarith [S.value_castSucc_lt_succ e, hd.2.2]
    let a : {a : G.edgeSet // EdgeCrosses G h (S.value e.castSucc) a} :=
      ⟨y.1, y.2.crosses_left (S.value_castSucc_lt_succ e) hne⟩
    have hl : (graphPLPresentation G h S).left e y = crossingPoint G h a := by
      apply Subtype.ext
      rw [hval]
      exact eq_crossingPoint G h a d hd.1 s hheight'
    rw [hl, closedLevelComponentsEquiv_crossingPoint]
    exact graphPLReebData_left_of_forall_ne G h S e y hne

private theorem graphPLReebData_right_eq (e : Fin n)
    (y : SpanEdge G h (S.value e.castSucc) (S.value e.succ)) :
    (graphPLReebData G h S).right e y =
      closedLevelComponentsEquiv G h (S.value e.succ)
        (ZerothHomotopy.mk ((graphPLPresentation G h S).right e y)) := by
  have hd := spanDart_spec G h (S.value_castSucc_lt_succ e) y
  have hden := spanDart_den_pos G h (S.value_castSucc_lt_succ e) y
  have hval : ((graphPLPresentation G h S).right e y).1 =
      edgePoint G (spanDart G h (S.value_castSucc_lt_succ e) y)
        (spanParam G h (S.value_castSucc_lt_succ e) y (CylinderPresentation.segTop S e)) := rfl
  have hheight := plHeight_spanPoint G h (S.value_castSucc_lt_succ e) y
    (CylinderPresentation.segTop S e)
  rw [spanPoint_apply, plHeight_edgePoint] at hheight
  have hcoe := coe_spanParam G h (S.value_castSucc_lt_succ e) y
    (CylinderPresentation.segTop S e)
  generalize spanParam G h (S.value_castSucc_lt_succ e) y
    (CylinderPresentation.segTop S e) = s at hval hheight hcoe
  generalize spanDart G h (S.value_castSucc_lt_succ e) y = d at hd hden hval hheight hcoe
  have hheight' : dartHeight h d s = S.value e.succ := hheight
  by_cases hsnd : h d.snd = S.value e.succ
  · have hs : s = 1 := by
      apply Subtype.ext
      rw [hcoe, Set.Icc.coe_one]
      change (S.value e.succ - h d.fst) / (h d.snd - h d.fst) = 1
      rw [← hsnd]
      exact div_self hden.ne'
    have hr : (graphPLPresentation G h S).right e y =
        (⟨vertex G d.snd, by
          rw [plHeight_vertex, hsnd]
          exact Set.mem_singleton _⟩ : ClosedLevel G h (S.value e.succ)) := by
      apply Subtype.ext
      rw [hval, hs, edgePoint_one]
    have hmem : d.snd ∈ (y.1 : Sym2 V) := by
      rw [← hd.1]
      exact snd_mem_dartEdge d
    rw [hr, closedLevelComponentsEquiv_mk_vertex G h d.snd hsnd]
    exact graphPLReebData_right_of_mem G h S e y hmem hsnd
  · have hne : ∀ v ∈ (y.1 : Sym2 V), h v ≠ S.value e.succ := by
      intro v hv hvq
      have hv' : v ∈ (dartEdge d : Sym2 V) := by
        rw [hd.1]
        exact hv
      rcases mem_dartEdge.mp hv' with rfl | rfl
      · linarith [hd.2.1, S.value_castSucc_lt_succ e]
      · exact hsnd hvq
    let a : {a : G.edgeSet // EdgeCrosses G h (S.value e.succ) a} :=
      ⟨y.1, y.2.crosses_right (S.value_castSucc_lt_succ e) hne⟩
    have hr : (graphPLPresentation G h S).right e y = crossingPoint G h a := by
      apply Subtype.ext
      rw [hval]
      exact eq_crossingPoint G h a d hd.1 s hheight'
    rw [hr, closedLevelComponentsEquiv_crossingPoint]
    exact graphPLReebData_right_of_forall_ne G h S e y hne

private noncomputable def graphPLComponentDataHom :
    (graphPLPresentation G h S).componentData.Hom (graphPLReebData G h S) where
  v i := closedLevelComponentsEquiv G h (S.value i)
  e i := zerothHomotopyEquivOfDiscrete ((graphPLPresentation G h S).E i)
  left_comm := by
    intro e z
    induction z using ZerothHomotopy.rec with
    | mk y =>
        change (graphPLReebData G h S).left e
              (zerothHomotopyEquivOfDiscrete ((graphPLPresentation G h S).E e)
                (ZerothHomotopy.mk y)) =
          closedLevelComponentsEquiv G h (S.value e.castSucc)
            (TDA.Topology.componentMap ((graphPLPresentation G h S).left e)
              (ZerothHomotopy.mk y))
        rw [zerothHomotopyEquivOfDiscrete_mk]
        exact graphPLReebData_left_eq G h S e y
  right_comm := by
    intro e z
    induction z using ZerothHomotopy.rec with
    | mk y =>
        change (graphPLReebData G h S).right e
              (zerothHomotopyEquivOfDiscrete ((graphPLPresentation G h S).E e)
                (ZerothHomotopy.mk y)) =
          closedLevelComponentsEquiv G h (S.value e.succ)
            (TDA.Topology.componentMap ((graphPLPresentation G h S).right e)
              (ZerothHomotopy.mk y))
        rw [zerothHomotopyEquivOfDiscrete_mk]
        exact graphPLReebData_right_eq G h S e y

/-- Vertex components of the graph-PL presentation and graph-PL Reeb data are identified by the
closed-level component equivalences; edge components are identified with their discrete types. -/
noncomputable def graphPLComponentDataIso :
    (graphPLPresentation G h S).componentData ≅ graphPLReebData G h S where
  hom := graphPLComponentDataHom G h S
  inv := (graphPLComponentDataHom G h S).inv
    (fun i => (closedLevelComponentsEquiv G h (S.value i)).bijective)
    (fun e => (zerothHomotopyEquivOfDiscrete ((graphPLPresentation G h S).E e)).bijective)
  hom_inv_id := (graphPLComponentDataHom G h S).comp_inv _ _
  inv_hom_id := (graphPLComponentDataHom G h S).inv_comp _ _

/-- The vertex component of `graphPLComponentDataIso` is the closed-level classification map. -/
theorem graphPLComponentDataIso_hom_v (i : Fin (n + 1)) (z) :
    (graphPLComponentDataIso G h S).hom.v i z =
      closedLevelComponentsEquiv G h (S.value i) z := by
  rfl

/-- The graph-PL Reeb map agrees pointwise with the presentation map followed by the component
data identification. -/
theorem graphPLReebMap_graphPLPresentationMap {S : CriticalValues n}
    (hS : CoversVertexHeights S h)
    (x : (graphPLPresentation G h S).Realization S) :
    graphPLReebMap G h hS (graphPLPresentationMap G h S x) =
      CylinderPresentation.realizeHom S (graphPLComponentDataIso G h S).hom
        ((graphPLPresentation G h S).componentGraphMap S x) := by
  rcases (graphPLPresentation G h S).exists_rep S x with ⟨i, p, rfl⟩ | ⟨e, ⟨y, t⟩, rfl⟩
  · exact graphPLReebMap_of_level G h hS i p
  · let d := spanDart G h (S.value_castSucc_lt_succ e) y
    have hd := spanDart_spec G h (S.value_castSucc_lt_succ e) y
    have hsp : EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d) := by
      rw [hd.1]
      exact y.2
    have hheight :
        dartHeight h d (spanParam G h (S.value_castSucc_lt_succ e) y
          (CylinderPresentation.gapIncl S e t)) = (t : ℝ) := by
      have ht := plHeight_spanPoint G h (S.value_castSucc_lt_succ e) y
        (CylinderPresentation.gapIncl S e t)
      erw [spanPoint_apply, plHeight_edgePoint] at ht
      exact ht
    have hmap :
        graphPLReebMap G h hS
            (spanPoint G h (S.value_castSucc_lt_succ e) y
              (CylinderPresentation.gapIncl S e t)) =
          (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
            (⟨dartEdge d, hsp⟩, ⟨dartHeight h d (spanParam G h
              (S.value_castSucc_lt_succ e) y (CylinderPresentation.gapIncl S e t)), by
                rw [hheight]
                exact t.2⟩) := by
      erw [spanPoint_apply]
      exact graphPLReebMap_edgePoint_of_mem_K G h hS d
        (spanParam G h (S.value_castSucc_lt_succ e) y
          (CylinderPresentation.gapIncl S e t))
        (by rw [hheight]; exact t.2) hsp
    rw [graphPLPresentationMap_ofStrip, hmap]
    rw [CylinderPresentation.componentGraphMap_ofStrip]
    change _ = (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
      ((graphPLComponentDataIso G h S).hom.e e (ZerothHomotopy.mk y), t)
    apply congrArg ((CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e)
    apply Prod.ext
    · apply Subtype.ext
      change dartEdge d =
        (zerothHomotopyEquivOfDiscrete ((graphPLPresentation G h S).E e)
          (ZerothHomotopy.mk y)).1
      rw [zerothHomotopyEquivOfDiscrete_mk]
      exact hd.1
    · exact Subtype.ext hheight

end identification

section slice

variable {V : Type} [Finite V] (G : SimpleGraph V) (h : V → ℝ) {n : ℕ}
  {S : CriticalValues n}

noncomputable def graphPLPresentationIso (hS : CoversVertexHeights S h) :
    graphPLOver G h ≅ Over.mk (TopCat.ofHom ((graphPLPresentation G h S).height S)) :=
  (Over.isoMk (TopCat.isoOfHomeo (graphPLPresentationHomeomorph G h hS)) (by
    ext x
    change plHeight G h (graphPLPresentationHomeomorph G h hS x) =
      (graphPLPresentation G h S).height S x
    rw [graphPLPresentationHomeomorph_apply, plHeight_graphPLPresentationMap])).symm

/-- The graph-PL slice object is constructible, using any critical list covering vertex heights. -/
theorem isConstructibleSpace_graphPLOver : IsConstructibleSpace (graphPLOver G h) := by
  obtain ⟨n, S, hS⟩ := exists_coversVertexHeights h
  refine ⟨n, S, graphPLPresentation G h S, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    infer_instance
  · intro i
    infer_instance
  · intro e
    infer_instance
  · intro e
    infer_instance
  · exact ⟨graphPLPresentationIso G h hS⟩

/-- **(D) The identification of isomorphisms.** -/
theorem graphPLReebQuotientIsoOfIso_graphPLComponentDataIso
    (hS : CoversVertexHeights S h) :
    graphPLReebQuotientIsoOfIso G h hS (graphPLComponentDataIso G h S) =
      (graphPLPresentation G h S).quotientIsoOfIso S
        (graphPLPresentationIso G h hS) := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  ext q
  induction q using ReebQuotient.ind with
  | h a =>
      obtain ⟨x, rfl⟩ := graphPLPresentationMap_surjective G h hS a
      change CylinderPresentation.realizeHom S (graphPLComponentDataIso G h S).inv
          (graphPLReebQuotientHomeomorph G h hS
            (ReebQuotient.mk _ (graphPLPresentationMap G h S x))) =
        (graphPLPresentation G h S).quotientComponentGraphHomeomorph S
          (ReebQuotient.mk _
            ((graphPLPresentationHomeomorph G h hS).symm
              (graphPLPresentationMap G h S x)))
      rw [graphPLReebQuotientHomeomorph_mk,
        graphPLReebMap_graphPLPresentationMap G h hS,
        CylinderPresentation.quotientComponentGraphHomeomorph_mk]
      rw [← graphPLPresentationHomeomorph_apply G h hS x,
        Homeomorph.symm_apply_apply]
      have hc : (graphPLComponentDataIso G h S).hom.comp (graphPLComponentDataIso G h S).inv =
          FiniteReebData.Hom.id _ := (graphPLComponentDataIso G h S).hom_inv_id
      rw [← ContinuousMap.comp_apply, ← CylinderPresentation.realizeHom_comp S
        (graphPLComponentDataIso G h S).hom (graphPLComponentDataIso G h S).inv,
        hc, CylinderPresentation.realizeHom_id]
      rfl

/-! (E) consequences -/

/-- The graph realization with its graph-PL height, regarded as a constructible ℝ-space. -/
noncomputable def graphPLSpace : ConstructibleSpaceCat :=
  ⟨graphPLOver G h, isConstructibleSpace_graphPLOver G h⟩

/-- The restricted quotient functor sends `graphPLSpace` to `graphPLReebGraph`. -/
theorem quotientRGraphFunctor_obj_graphPLSpace :
    quotientRGraphFunctor.obj (graphPLSpace G h) = graphPLReebGraph G h :=
  rfl

/-- The structure map of `graphPLSpace` is the graph-PL height. -/
theorem overBaseMap_graphPLSpace : overBaseMap (graphPLSpace G h).obj = plHeight G h :=
  rfl

/-- The Reeb quotient of every geometric thickening of the graph-PL slice object is a graph. -/
theorem isRGraph_quotient_thickening_graphPLOver (ε : ℝ≥0) :
    RGraph.IsRGraph ((ReebQuotient.quotientFunctor ℝ).obj
      ((GeometricThickening.functor ε).obj (graphPLOver G h))) :=
  RGraph.isRGraph_quotient_thickening_of_isConstructibleSpace
    (isConstructibleSpace_graphPLOver G h) ε

end slice

end

end TDA.Mapper.GraphPL
