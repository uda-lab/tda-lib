import TDA.Reeb.GraphRealization
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Hausdorff

/-! # Topology of graph realizations

For `V : Type u` and `G : SimpleGraph V`, barycentric coordinates give a continuous injective map
`barycentric G : C(Realization G, V → ℝ)`, so the realization is Hausdorff. Two points of the
realization are identified only as the cell relation forces: an edge point is a vertex exactly at
an endpoint, and interior edge points agree exactly up to reversal. The realization is locally
path-connected, a graph embedding induces an injective map on realizations, and the realization is
compact when `V` is finite. Only compactness uses a finiteness hypothesis. These are library
results and make no external source claim.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph Filter
open TDA.Reeb TDA.Reeb.GraphRealization

noncomputable section

universe u v

section realization

variable {V : Type u} (G : SimpleGraph V)

private local instance realizationTopologyDecidableEq : DecidableEq V := Classical.decEq V

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

private theorem mem_dart_edge {d : G.Dart} {v : V} : v ∈ d.edge ↔ v = d.fst ∨ v = d.snd :=
  Sym2.mem_iff

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
  have hedge : d.edge = d'.edge := by
    apply Sym2.ext
    intro i
    constructor
    · intro hi
      have hpos : 0 < barycentric G (edgePoint G d t) i := by
        rcases (mem_dart_edge G).mp hi with rfl | rfl
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
      exact (mem_dart_edge G).mpr (barycentric_edge_coord_pos G htpos' htlt' hpos')
    · intro hi
      have hpos : 0 < barycentric G (edgePoint G d' t') i := by
        rcases (mem_dart_edge G).mp hi with rfl | rfl
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
      exact (mem_dart_edge G).mpr (barycentric_edge_coord_pos G htpos htlt hpos')
  rcases (dart_edge_eq_iff d d').mp hedge with hd | hd
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

section compact

variable {V : Type u} [Finite V] (G : SimpleGraph V)

/-- The graph realization is compact when its vertex type is finite. -/
theorem compactSpace_realization : CompactSpace (Realization G) := by
  classical
  let _ : TopologicalSpace V := ⊥
  let _ : Fintype V := Fintype.ofFinite V
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let _ : Fintype G.Dart := SimpleGraph.Dart.fintype
  let _ : CompactSpace V := @Finite.compactSpace V ⊥ inferInstance
  let _ : CompactSpace (Σ _ : G.Dart, unitInterval) := by
    constructor
    rw [Sigma.univ]
    exact isCompact_iUnion fun d => isCompact_range continuous_sigmaMk
  let _ : CompactSpace (Cells G) := by
    constructor
    change IsCompact (Set.univ : Set (V ⊕ Σ _ : G.Dart, unitInterval))
    rw [← range_inl_union_range_inr]
    exact (isCompact_range continuous_inl).union (isCompact_range continuous_inr)
  exact Quot.compactSpace

end compact

end

end TDA.Mapper.GraphPL
