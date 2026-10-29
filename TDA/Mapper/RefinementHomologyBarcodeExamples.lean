import TDA.Mapper.RefinementHomologyBarcode
import TDA.Mapper.RefinementHomologyExamples
import TDA.Mapper.MapperReebApproximationExamples
import TDA.Persistence.LogScaleDiagram
import TDA.Simplicial.H0Augmentation
import TDA.Simplicial.Cone
import TDA.Simplicial.FiniteCoordinates

/-!
# Mapper barcode fixtures

* **No stages and an empty domain.** On `Fin 0` every Mapper barcode is empty, and on the empty
  domain every barcode is empty for all chains, covers, orders, refinements and degrees.
* **Two-stage merge.** On the single edge with heights `0, 1`, the members `(-1, 1/3)` and
  `(2/3, 2)` refine by a constant selector to `(-1, 2)`.  Over `ℚ` the degree-zero barcode is
  `{[0, 2), [0, 1)}` and the degree-one barcode is empty; the bar `[0, 2)` ends at the last
  observed stage.
* **Skew three-stage family.** On `Fin 3`, the three-stage family over the one-point space whose
  direct first-to-last selector is not the composite of its adjacent selectors has the same
  degree-zero barcode `{[0, 3)}` as the strictly coherent tower, whose strict Mapper maps have
  rank one in every comparison.
* **Loop.** On the 4-cycle with heights `0, 1, 2, 1`, the two members `(-1, 3/2)` and `(1/2, 3)`
  meet in two components, but ordinary Mapper is a single edge with no degree-one homology.
  The three members `(-1, 3/4)`, `(1/2, 3/2)`, `(5/4, 3)` of
  `TDA.Mapper.MapperReebApproximationExamples` give a Mapper 4-cycle with degree-one homology of
  rank one; refined by a constant selector to the one member `(-1, 3)`, the degree-one barcode
  over `ℚ` is the single bar `[0, 1)`.
* **Negative control.** For the constant map from discrete `ℕ` with one full member, the Mapper
  complex has infinitely many vertices and its degree-zero homology is not finite-dimensional
  for any component order and field, so the finiteness hypothesis fails in degree zero and no
  degree-zero barcode is defined.  Degree one has no faces, so that degree is unaffected.

The component orders of the graph fixtures are arbitrary well orders; the homology computations
do not depend on the orientation signs.
-/

namespace TDA.Mapper.RefinementHomologyBarcodeExamples

open CategoryTheory Set SimpleGraph
open TDA.Topology TDA.Simplicial TDA.Persistence
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀)
open TDA.Mapper.TowerExamples
open TDA.Mapper.RefinementHomologyExamples

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## Homology ranks of small complexes -/

section Ranks

variable {V : Type} [LinearOrder V] (K : PreAbstractSimplicialComplex V) (k : Type) [Field k]

private theorem finrank_homology_eq_zero (n : ℕ) [IsEmpty (Face K n)] :
    Module.finrank k (simplicialHomology K k n) = 0 :=
  have : Subsingleton (simplicialHomology K k n) :=
    ModuleCat.subsingleton_of_isZero (isZero_simplicialHomology_of_isEmpty_face k n)
  Module.finrank_zero_of_subsingleton

private theorem finrank_range_id (n : ℕ) :
    Module.finrank k (LinearMap.range (ModuleCat.Hom.hom (𝟙 (simplicialHomology K k n)))) =
      Module.finrank k (simplicialHomology K k n) := by
  rw [ModuleCat.hom_id, LinearMap.range_id, finrank_top]

/-- Over a field, the `H₀` map of a vertex map sends a vertex class to a nonzero class. -/
private theorem finrank_range_homologyMap_zero_pos {W : Type} [LinearOrder W]
    {L : PreAbstractSimplicialComplex W} [Finite (Face L 0)] (g : VertexMap K L) (σ : Face K 0) :
    0 < Module.finrank k (LinearMap.range (simplicialHomologyMap k g 0).hom) := by
  let τ := vertexImageFace g σ (fun i j _ => Fin.ext (by omega))
  have hclass := simplicialHomologyMap_class k g 0 (zeroVertexCycle K k σ)
    (zeroVertexCycle L k τ) (vertexChainMap_vertex k g σ 1)
  have hne := simplicialHomologyClass_zeroVertexCycle_ne_zero L k τ
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨_, ⟨_, hclass⟩⟩, ?_⟩
  intro hz
  exact hne (congrArg Subtype.val hz)

end Ranks

/-! ## Vertices and edges of Mapper complexes -/

section MapperFaces

variable {X Y I : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U : I → Set Y)

/-- The degree-zero faces of a Mapper complex are its component indices. -/
private def faceZeroEquiv : Face (mapper f U) 0 ≃ ComponentIndex f U :=
  (Equiv.ofBijective
    (fun a => (⟨{a}, componentIndex_supported f U a, Finset.card_singleton a⟩ :
      Face (mapper f U) 0))
    ⟨fun a b hab => Finset.singleton_injective (congrArg Subtype.val hab), fun σ => by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 σ.2.2
      exact ⟨a, Subtype.ext ha.symm⟩⟩).symm

/-- If every member has exactly one path component in its inverse image, the component
indices are the cover indices. -/
private theorem natCard_componentIndex
    (hsub : ∀ i, Subsingleton (ZerothHomotopy (PullbackSpace f U i)))
    (hne : ∀ i, Nonempty (PullbackSpace f U i)) :
    Nat.card (ComponentIndex f U) = Nat.card I :=
  Nat.card_congr (Equiv.ofBijective (fun a : ComponentIndex f U => a.1)
    ⟨fun a b h => Sigma.ext h (Subsingleton.helim
      (congrArg (fun i => ZerothHomotopy (PullbackSpace f U i)) h) a.2 b.2),
      fun i => ⟨⟨i, ZerothHomotopy.mk (hne i).some⟩, rfl⟩⟩)

/-- Pairwise disjoint members give a Mapper complex without edges. -/
private theorem isEmpty_face_one_of_disjoint (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    IsEmpty (Face (mapper f U) 1) :=
  ⟨fun σ => by
    classical
    obtain ⟨a, b, hab, hσ⟩ := Finset.card_eq_two.1 σ.2.2
    obtain ⟨_, x, hx⟩ := (mem_mapper_iff f U σ.1).1 σ.2.1
    have ha : a ∈ σ.1 := by simp [hσ]
    have hb : b ∈ σ.1 := by simp [hσ]
    by_cases hi : a.1 = b.1
    · exact hab (eq_of_mem_mapper_face_of_fst_eq f U σ.2.1 ha hb hi)
    · obtain ⟨hxa, _⟩ := hx a ha
      obtain ⟨hxb, _⟩ := hx b hb
      exact Set.disjoint_left.1 (hU _ _ hi) hxa hxb⟩

end MapperFaces

/-! ## Inverse images with one path component -/

/-- If every surviving vertex lies in the incidence class of `v₀` and every active edge has a
surviving endpoint, the inverse image of the interval has at most one path component. -/
private theorem preimage_subsingleton {V : Type} {G : SimpleGraph V} {h : V → ℝ}
    {K : OpenInterval} (v₀ : V) (hv₀ : h v₀ ∈ K)
    (hv : ∀ (v : V) (hv : h v ∈ K),
      (cellGraph G h K).connectedComponentMk (Sum.inl ⟨v, hv⟩) =
        (cellGraph G h K).connectedComponentMk (Sum.inl ⟨v₀, hv₀⟩))
    (hcov : EndpointCoverage G h K) :
    Subsingleton (ZerothHomotopy {p : Realization G // plHeight G h p ∈ K}) := by
  have hcell : ∀ x : Cell G h K, (cellGraph G h K).connectedComponentMk x =
      (cellGraph G h K).connectedComponentMk (Sum.inl ⟨v₀, hv₀⟩) := by
    rintro (⟨v, hvK⟩ | ⟨e, hact⟩)
    · exact hv v hvK
    · obtain ⟨w, hw, hwK⟩ := hcov e hact
      exact (connectedComponentMk_inl_eq_inr G h K (v := ⟨w, hwK⟩) (e := ⟨e, hact⟩)
        hw).symm.trans (hv w hwK)
  have : Subsingleton (cellGraph G h K).ConnectedComponent :=
    ⟨ConnectedComponent.ind₂ fun x y => by rw [hcell x, hcell y]⟩
  exact ⟨fun c d => (preimageComponentsEquiv G h K).injective (Subsingleton.elim _ _)⟩

/-- Both vertices of the single edge lie on its only edge. -/
private theorem edgeGraph_mem_edge (b : Bool) (e : edgeGraph.edgeSet) : b ∈ (e : Sym2 Bool) := by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
  rcases TDA.Reeb.Examples.GraphRealization.edgeGraph_dart d with rfl | rfl <;> cases b
  · exact fst_mem_dartEdge d₀
  · exact snd_mem_dartEdge d₀
  · exact snd_mem_dartEdge d₀.symm
  · exact fst_mem_dartEdge d₀.symm

/-- On the single edge, the inverse image of an interval containing a vertex height is path
connected. -/
private theorem edge_preimage_subsingleton (h : Bool → ℝ) {K : OpenInterval} (b : Bool)
    (hb : h b ∈ K) :
    Subsingleton (ZerothHomotopy {p : Realization edgeGraph // plHeight edgeGraph h p ∈ K}) :=
  preimage_subsingleton b hb
    (fun v hv => by
      by_cases hvb : v = b
      · subst hvb
        rfl
      · exact connectedComponentMk_inl_eq_of_adj edgeGraph h K (u := ⟨v, hv⟩) (w := ⟨b, hb⟩) hvb)
    (fun e _ => ⟨b, edgeGraph_mem_edge b e, hb⟩)

/-! ## Degree-one homology of a complex without triangles -/

section DegreeOne

variable {V : Type} [LinearOrder V] (K : PreAbstractSimplicialComplex V)

/-- Without `2`-faces, degree-one homology is the kernel of the edge boundary. -/
private theorem finrank_homology_one [IsEmpty (Face K 2)] :
    Module.finrank ℚ (simplicialHomology K ℚ 1) =
      Module.finrank ℚ (LinearMap.ker (boundary K ℚ 0)) := by
  let : HasQuotient (simplicialCycles K ℚ 1) (Submodule ℚ (simplicialCycles K ℚ 1)) :=
    Submodule.hasQuotient (R := ℚ) (M := simplicialCycles K ℚ 1)
  have hhom := (homologyKernelQuotient.{0, 0, 0} ℚ (simplicialChainComplex K ℚ) 1).toLinearEquiv.finrank_eq
  change Module.finrank ℚ (simplicialHomology K ℚ 1) =
    Module.finrank ℚ (simplicialCycles K ℚ 1 ⧸ simplicialBoundaries K ℚ 1) at hhom
  have hB : simplicialBoundaries K ℚ 1 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨c, hc⟩ := (mem_simplicialBoundaries_iff ℚ K 1 z).1 hz
    have hc0 : c = 0 := Finsupp.ext fun σ => isEmptyElim σ
    rw [hc0, map_zero] at hc
    exact (Submodule.mem_bot ℚ).2 (Subtype.ext hc.symm)
  rw [hhom, (Submodule.quotEquivOfEqBot _ hB).finrank_eq]
  exact congrArg (fun S : Submodule ℚ (Chain K ℚ 1) => Module.finrank ℚ S)
    (simplicialCycles_succ (R := ℚ) K 0)

variable [Fintype (Face K 1)] [DecidableEq (Face K 1)] [Finite (Face K 0)]

/-- The boundary of an edge chain at a vertex sums the incidence coefficients. -/
private theorem boundary_apply_vertex (z : Chain K ℚ 1) (τ : Face K 0) :
    boundary K ℚ 0 z τ = ∑ σ, boundaryMatrix K ℚ 0 τ σ * z σ := by
  have h := congrFun (boundaryMatrix_mulVec K ℚ 0 z) τ
  rw [chainCoordinates_apply] at h
  rw [← h]
  simp [Matrix.mulVec, dotProduct, chainCoordinates_apply]

/-- A vertex outside an edge has incidence coefficient zero. -/
private theorem boundaryMatrix_vertex_eq_zero (τ : Face K 0) (σ : Face K 1) {w : V}
    (hτ : τ.1 = {w}) (hw : w ∉ σ.1) : boundaryMatrix K ℚ 0 τ σ = 0 := by
  apply boundaryMatrix_eq_zero_of_not_deletedFace
  intro i hi
  apply hw
  have hsub : (deletedFace K 0 σ i).1 ⊆ σ.1 := Finset.erase_subset _ _
  rw [hi, hτ] at hsub
  exact hsub (Finset.mem_singleton_self w)

/-- A vertex of an edge has nonzero incidence coefficient. -/
private theorem boundaryMatrix_vertex_ne_zero (τ : Face K 0) (σ : Face K 1) {w : V}
    (hτ : τ.1 = {w}) (hw : w ∈ σ.1) : boundaryMatrix K ℚ 0 τ σ ≠ 0 := by
  obtain ⟨u, hu, huw⟩ := Finset.exists_mem_ne (by rw [σ.2.2]; omega) w
  obtain ⟨i, hi⟩ : u ∈ Set.range (σ.1.orderEmbOfFin σ.2.2) := by
    rw [Finset.range_orderEmbOfFin]
    exact hu
  have hdel : deletedFace K 0 σ i = τ := by
    apply Subtype.ext
    change σ.1.erase (σ.1.orderEmbOfFin σ.2.2 i) = τ.1
    rw [hi, hτ]
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.singleton_subset_iff.2 (Finset.mem_erase.2 ⟨huw.symm, hw⟩)
    · rw [Finset.card_erase_of_mem hu, σ.2.2, Finset.card_singleton]
  rw [← hdel, boundaryMatrix_deletedFace]
  exact pow_ne_zero _ (by norm_num)

end DegreeOne

/-! ## No stages and an empty domain -/

/-- On the empty chain `Fin 0` every Mapper barcode is empty; no nonemptiness hypothesis is
used. -/
theorem mapperBarcode_fin_zero {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : Type) [Field k] (f : C(X, Y)) {Index : Fin 0 → Type} (cover : (q : Fin 0) → Index q → Set Y)
    [∀ q, LinearOrder (ComponentIndex f (cover q))]
    (r : ∀ {q t : Fin 0}, q ≤ t → Refinement (cover q) (cover t)) (n : ℕ)
    [∀ q, Finite (Face (mapper f (cover q)) n)] :
    mapperBarcode k f cover r n = 0 := by
  simp [mapperBarcode, rankBarcode]

private instance emptyMap_componentIndex_isEmpty {I : Type} (U : I → Set Unit) :
    IsEmpty (ComponentIndex emptyMap U) :=
  ⟨fun a => by
    induction a.2 using ZerothHomotopy.rec with
    | mk x => exact x.1.elim⟩

private instance emptyMap_face_isEmpty {I : Type} (U : I → Set Unit) (n : ℕ) :
    IsEmpty (Face (mapper emptyMap U) n) :=
  ⟨fun σ => by
    obtain ⟨a, _⟩ := ((mem_mapper_iff emptyMap U σ.1).1 σ.2.1).1
    exact isEmptyElim a⟩

/-- The empty domain gives the empty barcode on every chain, for all covers, component orders,
refinements and degrees. -/
theorem emptyDomain_mapperBarcode {N : ℕ} {Index : Fin N → Type}
    (cover : (q : Fin N) → Index q → Set Unit)
    [∀ q, LinearOrder (ComponentIndex emptyMap (cover q))]
    (r : ∀ {q t : Fin N}, q ≤ t → Refinement (cover q) (cover t)) (k : Type) [Field k]
    (n : ℕ) :
    mapperBarcode k emptyMap cover r n = 0 := by
  rw [mapperBarcode_eq_iff]
  intro q t h
  rw [Multiset.countP_zero]
  apply Nat.eq_zero_of_le_zero
  calc _ ≤ Module.finrank k (simplicialHomology (mapper emptyMap (cover q)) k n) :=
        LinearMap.finrank_range_le _
    _ = 0 := finrank_homology_eq_zero _ k n

/-! ## A two-stage merge over `ℚ` -/

section Merge

/-- Heights `0` and `1` on the two vertices of the single edge. -/
def h01 : Bool → ℝ
  | false => 0
  | true => 1

/-- Two labels at the fine stage and one at the coarse stage. -/
def mergeIndex : Fin 2 → Type
  | 0 => Fin 2
  | 1 => Unit

/-- The fine members `(-1, 1/3)` and `(2/3, 2)`. -/
def mergeFine : Fin 2 → OpenInterval
  | 0 => ioo (-1) (1 / 3)
  | 1 => ioo (2 / 3) 2

/-- The fine stage `(-1, 1/3)`, `(2/3, 2)` and the coarse stage `(-1, 2)`. -/
def mergeIntervals : (q : Fin 2) → mergeIndex q → OpenInterval
  | 0 => mergeFine
  | 1 => fun _ => ioo (-1) 2

/-- The cover families of the merge as subsets of `ℝ`. -/
abbrev mergeCover (q : Fin 2) (i : mergeIndex q) : Set ℝ := (mergeIntervals q i : Set ℝ)

private theorem mergeFine_subset (i : Fin 2) : (mergeFine i : Set ℝ) ⊆ (ioo (-1) 2 : Set ℝ) := by
  intro x hx
  fin_cases i <;> simp only [mergeFine, coe_ioo, Set.mem_Ioo] at hx ⊢ <;>
    constructor <;> linarith [hx.1, hx.2]

/-- The refinements of the merge; the selector to the coarse stage is constant. -/
def mergeRefinement : ∀ {q t : Fin 2}, q ≤ t → Refinement (mergeCover q) (mergeCover t)
  | 0, 0, _ => Refinement.id _
  | 0, 1, _ => ⟨fun _ => (), mergeFine_subset⟩
  | 1, 0, h => absurd h (by decide)
  | 1, 1, _ => Refinement.id _

local instance (q : Fin 2) :
    LinearOrder (ComponentIndex (plHeight edgeGraph h01) (mergeCover q)) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

private instance (q : Fin 2) : Finite (mergeIndex q) := by
  fin_cases q <;> dsimp [mergeIndex] <;> infer_instance

private theorem merge_disjoint (q : Fin 2) (i j : mergeIndex q) (hij : i ≠ j) :
    Disjoint (mergeCover q i) (mergeCover q j) := by
  fin_cases q
  · change Fin 2 at i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | (rw [Set.disjoint_left]
         intro x hx hy
         simp only [mergeCover, mergeIntervals, mergeFine, coe_ioo, Set.mem_Ioo] at hx hy
         linarith [hx.1, hx.2, hy.1, hy.2])
  · exact absurd (Subsingleton.elim (α := Unit) i j) hij

private instance merge_noEdges (q : Fin 2) :
    IsEmpty (Face (mapper (plHeight edgeGraph h01) (mergeCover q)) 1) :=
  isEmpty_face_one_of_disjoint _ _ (merge_disjoint q)

private theorem merge_member_vertex (q : Fin 2) (i : mergeIndex q) :
    ∃ b : Bool, h01 b ∈ mergeIntervals q i := by
  fin_cases q
  · change Fin 2 at i
    fin_cases i
    · exact ⟨false, by norm_num [h01, mergeIntervals, mergeFine, mem_ioo]⟩
    · exact ⟨true, by norm_num [h01, mergeIntervals, mergeFine, mem_ioo]⟩
  · exact ⟨false, by norm_num [h01, mergeIntervals, mem_ioo]⟩

private theorem merge_natCard (q : Fin 2) :
    Nat.card (ComponentIndex (plHeight edgeGraph h01) (mergeCover q)) =
      Nat.card (mergeIndex q) :=
  natCard_componentIndex _ _
    (fun i => edge_preimage_subsingleton h01 _ (merge_member_vertex q i).choose_spec)
    (fun i => ⟨⟨vertex edgeGraph _, (merge_member_vertex q i).choose_spec⟩⟩)

private theorem merge_finrank_H0 (q : Fin 2) :
    Module.finrank ℚ (simplicialHomology (mapper (plHeight edgeGraph h01) (mergeCover q)) ℚ 0) =
      Nat.card (mergeIndex q) := by
  have := Fintype.ofFinite (Face (mapper (plHeight edgeGraph h01) (mergeCover q)) 0)
  rw [finrank_zeroHomology_of_no_edges, Fintype.card_eq_nat_card,
    Nat.card_congr (faceZeroEquiv _ _), merge_natCard]

/-- Stage `0` has two vertices and stage `1` one. -/
theorem merge_finrank_H0_values :
    Module.finrank ℚ (simplicialHomology (mapper (plHeight edgeGraph h01) (mergeCover 0)) ℚ 0) =
        2 ∧
      Module.finrank ℚ
        (simplicialHomology (mapper (plHeight edgeGraph h01) (mergeCover 1)) ℚ 0) = 1 := by
  rw [merge_finrank_H0, merge_finrank_H0]
  exact ⟨by change Nat.card (Fin 2) = 2; simp, by change Nat.card Unit = 1; simp⟩

/-- The bar `[0, 2)`: a component present at both stages. -/
def mergeBar02 : FiniteInterval 2 := ⟨0, 2, by omega, le_rfl⟩

/-- The bar `[0, 1)`: a component that merges at stage `1`. -/
def mergeBar01 : FiniteInterval 2 := ⟨0, 1, by omega, by omega⟩

/-- The degree-zero barcode of the merge over `ℚ` is `{[0, 2), [0, 1)}`, and its degree-one
barcode is empty. -/
theorem merge_mapperBarcode :
    mapperBarcode ℚ (plHeight edgeGraph h01) mergeCover mergeRefinement 0 =
        {mergeBar02, mergeBar01} ∧
      mapperBarcode ℚ (plHeight edgeGraph h01) mergeCover mergeRefinement 1 = 0 := by
  obtain ⟨h0, h1⟩ := merge_finrank_H0_values
  constructor
  · rw [mapperBarcode_eq_iff]
    intro q t h
    fin_cases q <;> fin_cases t
    · rw [mapperHomologyMap_eq_id, finrank_range_id]
      exact h0.trans (by decide)
    · apply le_antisymm
      · calc _ ≤ Module.finrank ℚ
              (simplicialHomology (mapper (plHeight edgeGraph h01) (mergeCover 1)) ℚ 0) :=
              Submodule.finrank_le _
          _ = _ := h1.trans (by decide)
      · let i : mergeIndex 0 := (0 : Fin 2)
        have hb := (merge_member_vertex 0 i).choose_spec
        let a : ComponentIndex (plHeight edgeGraph h01) (mergeCover 0) :=
          ⟨i, ZerothHomotopy.mk ⟨vertex edgeGraph _, hb⟩⟩
        calc _ = 1 := by decide
          _ ≤ _ := finrank_range_homologyMap_zero_pos _ ℚ _
            ⟨{a}, componentIndex_supported _ _ a, Finset.card_singleton a⟩
    · exact absurd h (by decide)
    · rw [mapperHomologyMap_eq_id, finrank_range_id]
      exact h1.trans (by decide)
  · rw [mapperBarcode_eq_iff]
    intro q t h
    rw [Multiset.countP_zero]
    apply Nat.eq_zero_of_le_zero
    calc _ ≤ Module.finrank ℚ
          (simplicialHomology (mapper (plHeight edgeGraph h01) (mergeCover q)) ℚ 1) :=
          LinearMap.finrank_range_le _
      _ = 0 := finrank_homology_eq_zero _ ℚ 1

end Merge

/-! ## Refinement independence on the skew three-stage family -/

section Skew

/-- The three stages of the skew family as the chain `Fin 3`. -/
def skewStage : Fin 3 → ThreeStage
  | 0 => .first
  | 1 => .middle
  | 2 => .last

/-- `skewStage` is monotone. -/
theorem skewStage_le {q t : Fin 3} (h : q ≤ t) : skewStage q ≤ skewStage t := by
  fin_cases q <;> fin_cases t
  all_goals first
    | exact absurd h (by decide)
    | exact ThreeStageLE.first_refl
    | exact ThreeStageLE.middle_refl
    | exact ThreeStageLE.last_refl
    | exact ThreeStageLE.first_middle
    | exact ThreeStageLE.middle_last
    | exact ThreeStageLE.first_last

/-- The three-stage cover families over the one-point space, indexed by `Fin 3`. -/
abbrev skewCover (q : Fin 3) : threeStageIndex (skewStage q) → Set Unit :=
  threeStageCover (skewStage q)

/-- The skew refinements, whose direct first-to-last selector is not the composite. -/
def skewFin {q t : Fin 3} (h : q ≤ t) : Refinement (skewCover q) (skewCover t) :=
  skewRefinement (skewStage_le h)

/-- The refinements of the strictly coherent three-stage tower. -/
def coherentFin {q t : Fin 3} (h : q ≤ t) : Refinement (skewCover q) (skewCover t) :=
  threeStageRefinement (skewStage_le h)

local instance (q : Fin 3) : LinearOrder (ComponentIndex threeStageMap (skewCover q)) :=
  componentIndexLinearOrder threeStageMap _

private instance (p : ThreeStage) : Finite (threeStageIndex p) := by
  cases p <;> dsimp [threeStageIndex] <;> infer_instance

private instance {I : Type} [Finite I] (U : I → Set Unit) :
    Finite (ComponentIndex threeStageMap U) :=
  have : ∀ i, Finite (ZerothHomotopy (PullbackSpace threeStageMap U i)) := fun i =>
    have := subsingleton_zerothHomotopy (Z := PullbackSpace threeStageMap U i)
    inferInstance
  inferInstanceAs (Finite (Σ i, ZerothHomotopy (PullbackSpace threeStageMap U i)))

/-- Over the one-point space, a cover by full members gives the full complex. -/
private theorem threeStage_mapper_eq_top (p : ThreeStage) :
    mapper threeStageMap (threeStageCover p) = ⊤ := by
  ext s
  constructor
  · intro hs
    exact ((mem_mapper_iff _ _ s).1 hs).1
  · intro hs
    refine (mem_mapper_iff _ _ s).2 ⟨hs, (), ?_⟩
    rintro ⟨i, c⟩ _
    have := subsingleton_zerothHomotopy (Z := PullbackSpace threeStageMap (threeStageCover p) i)
    exact ⟨Set.mem_univ (), Subsingleton.elim _ _⟩

private theorem skew_finrank_H0 (q : Fin 3) :
    Module.finrank ℚ (simplicialHomology (mapper threeStageMap (skewCover q)) ℚ 0) = 1 := by
  have : Nonempty (ComponentIndex threeStageMap (skewCover q)) := by
    fin_cases q
    · exact ⟨threeStageComponentIndex .first false⟩
    · exact ⟨threeStageComponentIndex .middle ()⟩
    · exact ⟨threeStageComponentIndex .last (0 : Fin 2)⟩
  rw [threeStage_mapper_eq_top]
  exact finrank_simplicialHomology_top_zero ℚ

/-- The bar `[0, 3)` of the skew family. -/
def skewBar : FiniteInterval 3 := ⟨0, 3, by omega, le_rfl⟩

/-- The direct selector of the skew family differs from the composite of its adjacent
selectors, while its degree-zero barcode over `ℚ` is `{[0, 3)}`, the barcode of the strictly
coherent tower. -/
theorem skew_mapperBarcode :
    (skewFin (q := 0) (t := 2) (by decide)).selector ≠
        (skewFin (q := 1) (t := 2) (by decide)).selector ∘
          (skewFin (q := 0) (t := 1) (by decide)).selector ∧
      mapperBarcode ℚ threeStageMap skewCover skewFin 0 = {skewBar} ∧
      mapperBarcode ℚ threeStageMap skewCover skewFin 0 =
        mapperBarcode ℚ threeStageMap skewCover coherentFin 0 := by
  have hbar : mapperBarcode ℚ threeStageMap skewCover skewFin 0 = {skewBar} := by
    rw [mapperBarcode_eq_iff]
    intro q t h
    have hcount : ({skewBar} : Multiset (FiniteInterval 3)).countP
        (fun I => I.birth ≤ q.val ∧ t.val < I.death) = 1 := by
      rw [Multiset.countP_eq_card.mpr]
      · rfl
      · intro I hI
        rw [Multiset.mem_singleton] at hI
        subst hI
        exact ⟨Nat.zero_le _, t.isLt⟩
    rw [hcount]
    apply le_antisymm
    · calc _ ≤ Module.finrank ℚ (simplicialHomology (mapper threeStageMap (skewCover t)) ℚ 0) :=
            Submodule.finrank_le _
        _ = 1 := skew_finrank_H0 t
    · obtain ⟨a⟩ : Nonempty (ComponentIndex threeStageMap (skewCover q)) := by
        fin_cases q
        · exact ⟨threeStageComponentIndex .first false⟩
        · exact ⟨threeStageComponentIndex .middle ()⟩
        · exact ⟨threeStageComponentIndex .last (0 : Fin 2)⟩
      exact finrank_range_homologyMap_zero_pos _ ℚ _
        ⟨{a}, componentIndex_supported _ _ a, Finset.card_singleton a⟩
  exact ⟨skew_not_coherent.1, hbar, mapperBarcode_eq ℚ threeStageMap skewCover skewFin 0 _⟩

/-- The strictly coherent three-stage tower on the chain `Fin 3`. -/
def coherentTowerFin : CoherentCoverTower Unit (Fin 3) where
  Index q := threeStageIndex (skewStage q)
  cover := skewCover
  refinement := coherentFin
  selector_refl q := threeStageTower.selector_refl (skewStage q)
  selector_trans h k := threeStageTower.selector_trans (skewStage_le h) (skewStage_le k)

local instance (q : Fin 3) :
    LinearOrder (ComponentIndex threeStageMap (coherentTowerFin.cover q)) :=
  inferInstanceAs (LinearOrder (ComponentIndex threeStageMap (skewCover q)))

private instance (q : Fin 3) (n : ℕ) :
    Finite (Face (mapper threeStageMap (coherentTowerFin.cover q)) n) :=
  inferInstanceAs (Finite (Face (mapper threeStageMap (skewCover q)) n))

/-- Every homology map of the strict Mapper maps of the coherent tower has rank one in
degree zero, read off from the barcode `{[0, 3)}`. -/
theorem coherentTowerFin_finrank_range {q t : Fin 3} (h : q ≤ t) :
    Module.finrank ℚ (LinearMap.range
      (simplicialHomologyMap ℚ (coherentTowerFin.mapperMap threeStageMap h) 0).hom) = 1 := by
  rw [CoherentCoverTower.finrank_range_simplicialHomologyMap]
  change (mapperBarcode ℚ threeStageMap skewCover coherentFin 0).countP _ = 1
  rw [← skew_mapperBarcode.2.2, skew_mapperBarcode.2.1, Multiset.countP_eq_card.mpr]
  · rfl
  · intro I hI
    rw [Multiset.mem_singleton] at hI
    subst hI
    exact ⟨Nat.zero_le _, t.isLt⟩

end Skew

/-! ## A loop seen by a three-member cover of the 4-cycle -/

section Loop

open TDA.Mapper.MapperReebApproximationExamples (cycleFineLeft cycleFineRight)

/-! ### The two-member cover sees no loop -/

section TwoMember

open TDA.Mapper.GraphPL.Examples (overlappingIntervals overlappingIntervals_multiplicity_two)
open TDA.Mapper.MapperReebApproximationExamples (cycle_categorical_pair_distinguishes_ordinary_edge)

/-- The two members `(-1, 3/2)` and `(1/2, 3)` as subsets of `ℝ`. -/
abbrev pairCover : Bool → Set ℝ := fun i => (overlappingIntervals i : Set ℝ)

local instance : LinearOrder (ComponentIndex (plHeight C4 h4) pairCover) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

private instance pair_noTriangles : IsEmpty (Face (mapper (plHeight C4 h4) pairCover) 2) :=
  ⟨fun σ => by
    have := mapper_face_card_le_of_multiplicity _ _
      (overlappingIntervals_multiplicity_two C4 h4) σ.2.1
    rw [σ.2.2] at this
    omega⟩

/-- With the two members `(-1, 3/2)` and `(1/2, 3)`, whose intersection has two components
over the 4-cycle, ordinary Mapper is a single edge and has no degree-one homology over `ℚ`. -/
theorem pair_finrank_H1 :
    Module.finrank ℚ (simplicialHomology (mapper (plHeight C4 h4) pairCover) ℚ 1) = 0 := by
  let K := mapper (plHeight C4 h4) pairCover
  let _ := Fintype.ofFinite (Face K 1)
  obtain ⟨-, hcard2, hmem, hcard⟩ := cycle_categorical_pair_distinguishes_ordinary_edge
  let e : Face K 1 := ⟨_, hmem, hcard2⟩
  have he : ∀ σ : Face K 1, σ = e := fun σ => Subtype.ext (hcard σ.1 σ.2.1 σ.2.2)
  let a := TDA.Mapper.MultiNerveExamples.cycleIndex false
  have ha : a ∈ e.1 := @Finset.mem_insert_self _ (Classical.decEq _) _ _
  let τ : Face K 0 := ⟨{a}, componentIndex_supported _ _ a, Finset.card_singleton a⟩
  rw [finrank_homology_one, Submodule.finrank_eq_zero, eq_bot_iff]
  intro z hz
  have hz' : boundary K ℚ 0 z = 0 := hz
  have hsum := boundary_apply_vertex K z τ
  rw [hz', Finsupp.zero_apply, Finset.sum_eq_single e (fun σ _ hσ => absurd (he σ) hσ)
    (fun h => absurd (Finset.mem_univ e) h)] at hsum
  have hze : z e = 0 :=
    (mul_eq_zero.1 hsum.symm).resolve_left (boundaryMatrix_vertex_ne_zero K τ e rfl ha)
  refine (Submodule.mem_bot ℚ).2 (Finsupp.ext fun σ => ?_)
  rw [he σ, hze, Finsupp.zero_apply]

end TwoMember

/-- The three members `(-1, 3/4)`, `(1/2, 3/2)` and `(5/4, 3)`. -/
def loopFine : Fin 3 → OpenInterval
  | 0 => ioo (-1) (3 / 4)
  | 1 => I4
  | 2 => ioo (5 / 4) 3

/-- The fine stage is the three-member cover `cycleFineLeft`, `cycleFineRight`. -/
theorem loopFine_eq : loopFine = fun i => ioo (cycleFineLeft i) (cycleFineRight i) := by
  funext i
  fin_cases i <;> simp [loopFine, cycleFineLeft, cycleFineRight, I4]

/-- Three labels at the fine stage and one at the coarse stage. -/
def loopIndex : Fin 2 → Type
  | 0 => Fin 3
  | 1 => Unit

/-- The fine three-member cover and the coarse member `(-1, 3)`. -/
def loopIntervals : (q : Fin 2) → loopIndex q → OpenInterval
  | 0 => loopFine
  | 1 => fun _ => ioo (-1) 3

/-- The cover families of the loop as subsets of `ℝ`. -/
abbrev loopCover (q : Fin 2) (i : loopIndex q) : Set ℝ := (loopIntervals q i : Set ℝ)

private theorem loopFine_subset (i : Fin 3) : (loopFine i : Set ℝ) ⊆ (ioo (-1) 3 : Set ℝ) := by
  intro x hx
  fin_cases i <;> simp only [loopFine, I4, coe_ioo, Set.mem_Ioo] at hx ⊢ <;>
    constructor <;> linarith [hx.1, hx.2]

/-- The refinements of the loop family; the selector to the coarse stage is constant. -/
def loopRefinement : ∀ {q t : Fin 2}, q ≤ t → Refinement (loopCover q) (loopCover t)
  | 0, 0, _ => Refinement.id _
  | 0, 1, _ => ⟨fun _ => (), loopFine_subset⟩
  | 1, 0, h => absurd h (by decide)
  | 1, 1, _ => Refinement.id _

local instance (q : Fin 2) :
    LinearOrder (ComponentIndex (plHeight C4 h4) (loopCover q)) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

private instance (q : Fin 2) : Finite (loopIndex q) := by
  fin_cases q <;> dsimp [loopIndex] <;> infer_instance

/-- The fine Mapper complex. -/
abbrev loopK : PreAbstractSimplicialComplex (ComponentIndex (plHeight C4 h4) (loopCover 0)) :=
  mapper (plHeight C4 h4) (loopCover 0)

private theorem h4_ge_one {v : Fin 4} (hv : v ≠ 0) : 1 ≤ h4 v := by
  fin_cases v <;> first | exact absurd rfl hv | norm_num [h4]

private theorem h4_le_one {v : Fin 4} (hv : v ≠ 2) : h4 v ≤ 1 := by
  fin_cases v <;> first | exact absurd rfl hv | norm_num [h4]

private theorem h4_mem_Icc (v : Fin 4) : 0 ≤ h4 v ∧ h4 v ≤ 2 := by
  fin_cases v <;> norm_num [h4]

private theorem dartHeight_mem_Icc (d : C4.Dart) (t : unitInterval) {m M : ℝ}
    (hm : m ≤ h4 d.fst ∧ m ≤ h4 d.snd) (hM : h4 d.fst ≤ M ∧ h4 d.snd ≤ M) :
    m ≤ dartHeight h4 d t ∧ dartHeight h4 d t ≤ M := by
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  unfold dartHeight
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hm.1),
    mul_nonneg ht0 (sub_nonneg.2 hm.2), mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hM.1),
    mul_nonneg ht0 (sub_nonneg.2 hM.2)]

/-- Every active edge has an endpoint `w` when the edges avoiding `w` stay outside `K`. -/
private theorem C4_coverage {K : OpenInterval} (w : Fin 4) (hw : h4 w ∈ K)
    (hfar : ∀ d : C4.Dart, d.fst ≠ w → d.snd ≠ w → ∀ t, dartHeight h4 d t ∉ K) :
    EndpointCoverage C4 h4 K := by
  rintro e ⟨d, hd, t, -, -, ht⟩
  refine ⟨w, ?_, hw⟩
  rw [← hd]
  by_cases h1 : d.fst = w
  · exact h1 ▸ fst_mem_dartEdge d
  · by_cases h2 : d.snd = w
    · exact h2 ▸ snd_mem_dartEdge d
    · exact absurd ht (hfar d h1 h2 t)

private theorem loop_sub0 :
    Subsingleton (ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ loopFine 0}) :=
  preimage_subsingleton 0 (by norm_num [loopFine, mem_ioo])
    (fun v hv => by
      have : v = 0 := by
        by_contra hv0
        have := h4_ge_one hv0
        rw [loopFine, mem_ioo] at hv
        linarith [hv.2]
      subst this
      rfl)
    (C4_coverage 0 (by norm_num [loopFine, mem_ioo]) fun d h1 h2 t ht => by
      have := (dartHeight_mem_Icc d t (m := 1) (M := 2) ⟨h4_ge_one h1, h4_ge_one h2⟩
        ⟨(h4_mem_Icc _).2, (h4_mem_Icc _).2⟩).1
      rw [loopFine, mem_ioo] at ht
      linarith [ht.2])

private theorem loop_sub2 :
    Subsingleton (ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ loopFine 2}) :=
  preimage_subsingleton 2 (by norm_num [loopFine, mem_ioo])
    (fun v hv => by
      have : v = 2 := by
        by_contra hv2
        have := h4_le_one hv2
        rw [loopFine, mem_ioo] at hv
        linarith [hv.1]
      subst this
      rfl)
    (C4_coverage 2 (by norm_num [loopFine, mem_ioo]) fun d h1 h2 t ht => by
      have := (dartHeight_mem_Icc d t (m := 0) (M := 1)
        ⟨(h4_mem_Icc _).1, (h4_mem_Icc _).1⟩ ⟨h4_le_one h1, h4_le_one h2⟩).2
      rw [loopFine, mem_ioo] at ht
      linarith [ht.1])

/-- The fine-stage vertex over `(-1, 3/4)`. -/
def loopA : ComponentIndex (plHeight C4 h4) (loopCover 0) :=
  ⟨(0 : Fin 3), ZerothHomotopy.mk ⟨vertex C4 0, by norm_num [loopIntervals, loopFine, mem_ioo]⟩⟩

/-- The fine-stage vertex over `(1/2, 3/2)` through the vertex `1`. -/
def loopB1 : ComponentIndex (plHeight C4 h4) (loopCover 0) := ⟨(1 : Fin 3), x1⟩

/-- The fine-stage vertex over `(1/2, 3/2)` through the vertex `3`. -/
def loopB3 : ComponentIndex (plHeight C4 h4) (loopCover 0) := ⟨(1 : Fin 3), x3⟩

/-- The fine-stage vertex over `(5/4, 3)`. -/
def loopC : ComponentIndex (plHeight C4 h4) (loopCover 0) :=
  ⟨(2 : Fin 3), ZerothHomotopy.mk ⟨vertex C4 2, by norm_num [loopIntervals, loopFine, mem_ioo]⟩⟩

private theorem loop_vertex_cases (a : ComponentIndex (plHeight C4 h4) (loopCover 0)) :
    a = loopA ∨ a = loopB1 ∨ a = loopB3 ∨ a = loopC := by
  rcases a with ⟨i, c⟩
  change Fin 3 at i
  fin_cases i
  · exact .inl (Sigma.ext rfl (heq_of_eq (@Subsingleton.elim _ loop_sub0 _ _)))
  · rcases c4_preimage_classification c with rfl | rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (Sigma.ext rfl (heq_of_eq (@Subsingleton.elim _ loop_sub2 _ _)))))

private theorem loopA_ne_B1 : loopA ≠ loopB1 :=
  componentIndex_ne_of_index_ne (plHeight C4 h4) (loopCover 0) (i := (0 : Fin 3))
    (j := (1 : Fin 3)) (show (0 : Fin 3) ≠ 1 by decide) loopA.2 loopB1.2
private theorem loopA_ne_B3 : loopA ≠ loopB3 :=
  componentIndex_ne_of_index_ne (plHeight C4 h4) (loopCover 0) (i := (0 : Fin 3))
    (j := (1 : Fin 3)) (show (0 : Fin 3) ≠ 1 by decide) loopA.2 loopB3.2
private theorem loopA_ne_C : loopA ≠ loopC :=
  componentIndex_ne_of_index_ne (plHeight C4 h4) (loopCover 0) (i := (0 : Fin 3))
    (j := (2 : Fin 3)) (show (0 : Fin 3) ≠ 2 by decide) loopA.2 loopC.2
private theorem loopB1_ne_C : loopB1 ≠ loopC :=
  componentIndex_ne_of_index_ne (plHeight C4 h4) (loopCover 0) (i := (1 : Fin 3))
    (j := (2 : Fin 3)) (show (1 : Fin 3) ≠ 2 by decide) loopB1.2 loopC.2
private theorem loopB3_ne_C : loopB3 ≠ loopC :=
  componentIndex_ne_of_index_ne (plHeight C4 h4) (loopCover 0) (i := (1 : Fin 3))
    (j := (2 : Fin 3)) (show (1 : Fin 3) ≠ 2 by decide) loopB3.2 loopC.2
private theorem loopB1_ne_B3 : loopB1 ≠ loopB3 := fun h =>
  c4_x1_ne_x3 (eq_of_heq (Sigma.mk.inj_iff.1 h).2)

/-- The dart `0 → 3`. -/
def d03 : C4.Dart := ⟨(0, 3), by decide⟩

/-- The dart `2 → 1`. -/
def d21 : C4.Dart := ⟨(2, 1), by decide⟩

/-- The parameter `5/8`. -/
def fiveEighths : unitInterval := ⟨5 / 8, by norm_num, by norm_num⟩

private theorem edgePoint_fiveEighths_mem (d : C4.Dart) {a b : ℝ}
    (h : a < 3 / 8 * h4 d.fst + 5 / 8 * h4 d.snd ∧ 3 / 8 * h4 d.fst + 5 / 8 * h4 d.snd < b) :
    plHeight C4 h4 (edgePoint C4 d fiveEighths) ∈ ioo a b := by
  rw [plHeight_edgePoint, mem_ioo]
  change a < (1 - 5 / 8) * h4 d.fst + 5 / 8 * h4 d.snd ∧
    (1 - 5 / 8) * h4 d.fst + 5 / 8 * h4 d.snd < b
  constructor <;> linarith [h.1, h.2]

private theorem loop_mem_A (x : Realization C4) (hx : plHeight C4 h4 x ∈ loopFine 0) :
    x ∈ componentCover (plHeight C4 h4) (loopCover 0) loopA :=
  (mem_componentCover_iff _ _ (i := (0 : Fin 3)) loopA.2 hx).2 (@Subsingleton.elim _ loop_sub0 _ _)

private theorem loop_mem_C (x : Realization C4) (hx : plHeight C4 h4 x ∈ loopFine 2) :
    x ∈ componentCover (plHeight C4 h4) (loopCover 0) loopC :=
  (mem_componentCover_iff _ _ (i := (2 : Fin 3)) loopC.2 hx).2 (@Subsingleton.elim _ loop_sub2 _ _)

private theorem loop_mem_B1 (d : C4.Dart) (hd : d.snd = 1)
    (hx : plHeight C4 h4 (edgePoint C4 d fiveEighths) ∈ I4) :
    edgePoint C4 d fiveEighths ∈ componentCover (plHeight C4 h4) (loopCover 0) loopB1 := by
  refine (mem_componentCover_iff (plHeight C4 h4) (loopCover 0) (i := (1 : Fin 3)) x1 hx).2 ?_
  apply (preimageComponentsEquiv C4 h4 I4).injective
  rw [preimageComponentsEquiv_mk_edgePoint_of_snd_mem C4 h4 I4 hx (hd ▸ one_mem_I4), c4_equiv_x1]
  exact congrArg (fun v => (cellGraph C4 h4 I4).connectedComponentMk (Sum.inl v)) (Subtype.ext hd)

private theorem loop_mem_B3 (d : C4.Dart) (hd : d.snd = 3)
    (hx : plHeight C4 h4 (edgePoint C4 d fiveEighths) ∈ I4) :
    edgePoint C4 d fiveEighths ∈ componentCover (plHeight C4 h4) (loopCover 0) loopB3 := by
  refine (mem_componentCover_iff (plHeight C4 h4) (loopCover 0) (i := (1 : Fin 3)) x3 hx).2 ?_
  apply (preimageComponentsEquiv C4 h4 I4).injective
  rw [preimageComponentsEquiv_mk_edgePoint_of_snd_mem C4 h4 I4 hx (hd ▸ three_mem_I4), c4_equiv_x3]
  exact congrArg (fun v => (cellGraph C4 h4 I4).connectedComponentMk (Sum.inl v)) (Subtype.ext hd)

private theorem loop_pair_mem {a b : ComponentIndex (plHeight C4 h4) (loopCover 0)}
    (x : Realization C4) (ha : x ∈ componentCover (plHeight C4 h4) (loopCover 0) a)
    (hb : x ∈ componentCover (plHeight C4 h4) (loopCover 0) b) : ({a, b} : Finset _) ∈ loopK :=
  (mem_mapper_iff _ _ _).2 ⟨Finset.insert_nonempty _ _, x, fun c hc => by
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact ha
    · rw [Finset.mem_singleton.1 hc]
      exact hb⟩

/-- The edge between the vertices over `(-1, 3/4)` and through `1`. -/
def loopE1 : Face loopK 1 :=
  ⟨{loopA, loopB1}, loop_pair_mem (edgePoint C4 d01 fiveEighths)
    (loop_mem_A _ (edgePoint_fiveEighths_mem d01 (by norm_num [d01])))
    (loop_mem_B1 d01 rfl (edgePoint_fiveEighths_mem d01 (by norm_num [d01]))),
    Finset.card_pair loopA_ne_B1⟩

/-- The edge between the vertices over `(-1, 3/4)` and through `3`. -/
def loopE2 : Face loopK 1 :=
  ⟨{loopA, loopB3}, loop_pair_mem (edgePoint C4 d03 fiveEighths)
    (loop_mem_A _ (edgePoint_fiveEighths_mem d03 (by norm_num [d03])))
    (loop_mem_B3 d03 rfl (edgePoint_fiveEighths_mem d03 (by norm_num [d03]))),
    Finset.card_pair loopA_ne_B3⟩

/-- The edge between the vertices through `1` and over `(5/4, 3)`. -/
def loopE3 : Face loopK 1 :=
  ⟨{loopB1, loopC}, loop_pair_mem (edgePoint C4 d21 fiveEighths)
    (loop_mem_B1 d21 rfl (edgePoint_fiveEighths_mem d21 (by norm_num [d21])))
    (loop_mem_C _ (edgePoint_fiveEighths_mem d21 (by norm_num [d21]))),
    Finset.card_pair loopB1_ne_C⟩

/-- The edge between the vertices through `3` and over `(5/4, 3)`. -/
def loopE4 : Face loopK 1 :=
  ⟨{loopB3, loopC}, loop_pair_mem (edgePoint C4 d23 fiveEighths)
    (loop_mem_B3 d23 rfl (edgePoint_fiveEighths_mem d23 (by norm_num [d23])))
    (loop_mem_C _ (edgePoint_fiveEighths_mem d23 (by norm_num [d23]))),
    Finset.card_pair loopB3_ne_C⟩

private theorem loop_not_AC (s : Finset (ComponentIndex (plHeight C4 h4) (loopCover 0)))
    (hs : s ∈ loopK) : ¬ (loopA ∈ s ∧ loopC ∈ s) := by
  rintro ⟨hA, hC⟩
  obtain ⟨_, x, hx⟩ := (mem_mapper_iff _ _ s).1 hs
  obtain ⟨h0, _⟩ := hx loopA hA
  obtain ⟨h2, _⟩ := hx loopC hC
  change plHeight C4 h4 x ∈ loopFine 0 at h0
  change plHeight C4 h4 x ∈ loopFine 2 at h2
  rw [loopFine, mem_ioo] at h0
  rw [loopFine, mem_ioo] at h2
  linarith [h0.2, h2.1]

private theorem loop_not_B1B3 (s : Finset (ComponentIndex (plHeight C4 h4) (loopCover 0)))
    (hs : s ∈ loopK) : ¬ (loopB1 ∈ s ∧ loopB3 ∈ s) := fun h =>
  loopB1_ne_B3 (eq_of_mem_mapper_face_of_fst_eq _ _ hs h.1 h.2 rfl)

private theorem loop_face_one_cases (σ : Face loopK 1) :
    σ = loopE1 ∨ σ = loopE2 ∨ σ = loopE3 ∨ σ = loopE4 := by
  obtain ⟨a, b, hab, hσ⟩ := Finset.card_eq_two.1 σ.2.2
  have hface : ({a, b} : Finset _) ∈ loopK := hσ ▸ σ.2.1
  rcases loop_vertex_cases a with rfl | rfl | rfl | rfl <;>
    rcases loop_vertex_cases b with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | (refine (loop_not_AC _ hface ⟨?_, ?_⟩).elim <;> simp <;> done)
    | (refine (loop_not_B1B3 _ hface ⟨?_, ?_⟩).elim <;> simp <;> done)
    | (left; apply Subtype.ext; rw [hσ]; rfl)
    | (left; apply Subtype.ext; rw [hσ, Finset.pair_comm]; rfl)
    | (right; left; apply Subtype.ext; rw [hσ]; rfl)
    | (right; left; apply Subtype.ext; rw [hσ, Finset.pair_comm]; rfl)
    | (right; right; left; apply Subtype.ext; rw [hσ]; rfl)
    | (right; right; left; apply Subtype.ext; rw [hσ, Finset.pair_comm]; rfl)
    | (right; right; right; apply Subtype.ext; rw [hσ]; rfl)
    | (right; right; right; apply Subtype.ext; rw [hσ, Finset.pair_comm]; rfl)

private instance loop_noTriangles : IsEmpty (Face loopK 2) := ⟨fun σ => by
  have h1 := loop_not_AC σ.1 σ.2.1
  have h2 := loop_not_B1B3 σ.1 σ.2.1
  obtain ⟨p, q, hpq⟩ : ∃ p q, σ.1 ⊆ {p, q} := by
    by_cases hA : loopA ∈ σ.1 <;> by_cases hB : loopB1 ∈ σ.1
    · refine ⟨loopA, loopB1, fun y hy => ?_⟩
      rcases loop_vertex_cases y with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact absurd ⟨hB, hy⟩ h2
      · exact absurd ⟨hA, hy⟩ h1
    · refine ⟨loopA, loopB3, fun y hy => ?_⟩
      rcases loop_vertex_cases y with rfl | rfl | rfl | rfl
      · simp
      · exact absurd hy hB
      · simp
      · exact absurd ⟨hA, hy⟩ h1
    · refine ⟨loopB1, loopC, fun y hy => ?_⟩
      rcases loop_vertex_cases y with rfl | rfl | rfl | rfl
      · exact absurd hy hA
      · simp
      · exact absurd ⟨hB, hy⟩ h2
      · simp
    · refine ⟨loopB3, loopC, fun y hy => ?_⟩
      rcases loop_vertex_cases y with rfl | rfl | rfl | rfl
      · exact absurd hy hA
      · exact absurd hy hB
      · simp
      · simp
  have hc := Finset.card_le_card hpq
  have hpq2 := Finset.card_le_two (a := p) (b := q)
  rw [σ.2.2] at hc
  omega⟩

private theorem loop_card_componentIndex :
    Nat.card (ComponentIndex (plHeight C4 h4) (loopCover 0)) = 4 := by
  classical
  have := GraphPL.finite_componentIndex C4 h4 (loopIntervals 0)
  let _ := Fintype.ofFinite (ComponentIndex (plHeight C4 h4) (loopCover 0))
  have huniv : (Finset.univ : Finset (ComponentIndex (plHeight C4 h4) (loopCover 0))) =
      {loopA, loopB1, loopB3, loopC} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact loop_vertex_cases a
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, huniv,
    Finset.card_insert_of_notMem (by simp [loopA_ne_B1, loopA_ne_B3, loopA_ne_C]),
    Finset.card_insert_of_notMem (by simp [loopB1_ne_B3, loopB1_ne_C]),
    Finset.card_pair loopB3_ne_C]

private theorem loopE_mem (a : ComponentIndex (plHeight C4 h4) (loopCover 0)) :
    (a ∈ loopE1.1 ↔ a = loopA ∨ a = loopB1) ∧ (a ∈ loopE2.1 ↔ a = loopA ∨ a = loopB3) ∧
      (a ∈ loopE3.1 ↔ a = loopB1 ∨ a = loopC) ∧ (a ∈ loopE4.1 ↔ a = loopB3 ∨ a = loopC) := by
  simp [loopE1, loopE2, loopE3, loopE4]

private theorem loopE_ne :
    loopE1 ≠ loopE2 ∧ loopE1 ≠ loopE3 ∧ loopE1 ≠ loopE4 ∧ loopE2 ≠ loopE3 ∧ loopE2 ≠ loopE4 ∧
      loopE3 ≠ loopE4 := by
  have hm := loopE_mem
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := (hm loopB1).2.1.1 (h ▸ (hm loopB1).1.2 (.inr rfl))
    rcases this with h' | h'
    exacts [loopA_ne_B1 h'.symm, loopB1_ne_B3 h']
  · have := (hm loopA).2.2.1.1 (h ▸ (hm loopA).1.2 (.inl rfl))
    rcases this with h' | h'
    exacts [loopA_ne_B1 h', loopA_ne_C h']
  · have := (hm loopA).2.2.2.1 (h ▸ (hm loopA).1.2 (.inl rfl))
    rcases this with h' | h'
    exacts [loopA_ne_B3 h', loopA_ne_C h']
  · have := (hm loopA).2.2.1.1 (h ▸ (hm loopA).2.1.2 (.inl rfl))
    rcases this with h' | h'
    exacts [loopA_ne_B1 h', loopA_ne_C h']
  · have := (hm loopA).2.2.2.1 (h ▸ (hm loopA).2.1.2 (.inl rfl))
    rcases this with h' | h'
    exacts [loopA_ne_B3 h', loopA_ne_C h']
  · have := (hm loopB1).2.2.2.1 (h ▸ (hm loopB1).2.2.1.2 (.inl rfl))
    rcases this with h' | h'
    exacts [loopB1_ne_B3 h', loopB1_ne_C h']

/-- The vertex face of a fine-stage vertex. -/
private def loopVertex (a : ComponentIndex (plHeight C4 h4) (loopCover 0)) : Face loopK 0 :=
  ⟨{a}, componentIndex_supported _ _ a, Finset.card_singleton a⟩

/-- The fine Mapper complex is a 4-cycle: its degree-one homology over `ℚ` has rank one. -/
theorem loop_finrank_H1 : Module.finrank ℚ (simplicialHomology loopK ℚ 1) = 1 := by
  classical
  let _ := Fintype.ofFinite (Face loopK 1)
  let _ := Fintype.ofFinite (Face loopK 0)
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := loopE_ne
  have hm := loopE_mem
  have huniv : (Finset.univ : Finset (Face loopK 1)) = {loopE1, loopE2, loopE3, loopE4} := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact loop_face_one_cases σ
  have hsum : ∀ (z : Chain loopK ℚ 1) (τ : Face loopK 0), boundary loopK ℚ 0 z τ =
      boundaryMatrix loopK ℚ 0 τ loopE1 * z loopE1 + boundaryMatrix loopK ℚ 0 τ loopE2 * z loopE2 +
        boundaryMatrix loopK ℚ 0 τ loopE3 * z loopE3 +
          boundaryMatrix loopK ℚ 0 τ loopE4 * z loopE4 := by
    intro z τ
    rw [boundary_apply_vertex, huniv, Finset.sum_insert (by simp [h12, h13, h14]),
      Finset.sum_insert (by simp [h23, h24]), Finset.sum_pair h34]
    ring
  have hz0 : ∀ (a : ComponentIndex (plHeight C4 h4) (loopCover 0)) (σ : Face loopK 1),
      a ∉ σ.1 → boundaryMatrix loopK ℚ 0 (loopVertex a) σ = 0 := fun a σ ha =>
    boundaryMatrix_vertex_eq_zero loopK _ σ rfl ha
  have hnz : ∀ (a : ComponentIndex (plHeight C4 h4) (loopCover 0)) (σ : Face loopK 1),
      a ∈ σ.1 → boundaryMatrix loopK ℚ 0 (loopVertex a) σ ≠ 0 := fun a σ ha =>
    boundaryMatrix_vertex_ne_zero loopK _ σ rfl ha
  have hcard1 : Fintype.card (Face loopK 1) = 4 := by
    rw [← Finset.card_univ, huniv, Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_insert_of_notMem (by simp [h23, h24]), Finset.card_pair h34]
  have hcard0 : Fintype.card (Face loopK 0) = 4 := by
    rw [Fintype.card_eq_nat_card, Nat.card_congr (faceZeroEquiv _ _), loop_card_componentIndex]
  rw [finrank_homology_one]
  apply le_antisymm
  · -- A cycle vanishing on the first edge vanishes on the whole loop.
    let φ : LinearMap.ker (boundary loopK ℚ 0) →ₗ[ℚ] ℚ :=
      (Finsupp.lapply loopE1).comp (LinearMap.ker (boundary loopK ℚ 0)).subtype
    have hφ : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      rintro ⟨z, hz⟩ hφz
      have hz' : boundary loopK ℚ 0 z = 0 := hz
      have h1 : z loopE1 = 0 := hφz
      have hB1 := hsum z (loopVertex loopB1)
      rw [hz', Finsupp.zero_apply, h1, hz0 _ loopE2 (by simp [hm, loopA_ne_B1.symm, loopB1_ne_B3]),
        hz0 _ loopE4 (by simp [hm, loopB1_ne_B3, loopB1_ne_C])] at hB1
      have h3 : z loopE3 = 0 := by
        have := hnz loopB1 loopE3 (by simp [hm])
        have h : boundaryMatrix loopK ℚ 0 (loopVertex loopB1) loopE3 * z loopE3 = 0 := by
          linarith
        exact (mul_eq_zero.1 h).resolve_left this
      have hC := hsum z (loopVertex loopC)
      rw [hz', Finsupp.zero_apply, h3, hz0 _ loopE1 (by simp [hm, loopA_ne_C.symm, loopB1_ne_C.symm]),
        hz0 _ loopE2 (by simp [hm, loopA_ne_C.symm, loopB3_ne_C.symm])] at hC
      have h4 : z loopE4 = 0 := by
        have := hnz loopC loopE4 (by simp [hm])
        have h : boundaryMatrix loopK ℚ 0 (loopVertex loopC) loopE4 * z loopE4 = 0 := by
          linarith
        exact (mul_eq_zero.1 h).resolve_left this
      have hB3 := hsum z (loopVertex loopB3)
      rw [hz', Finsupp.zero_apply, h4, hz0 _ loopE1 (by simp [hm, loopA_ne_B3.symm, loopB1_ne_B3.symm]),
        hz0 _ loopE3 (by simp [hm, loopB1_ne_B3.symm, loopB3_ne_C])] at hB3
      have h2 : z loopE2 = 0 := by
        have := hnz loopB3 loopE2 (by simp [hm])
        have h : boundaryMatrix loopK ℚ 0 (loopVertex loopB3) loopE2 * z loopE2 = 0 := by
          linarith
        exact (mul_eq_zero.1 h).resolve_left this
      have hzero : z = 0 := by
        ext σ
        rcases loop_face_one_cases σ with rfl | rfl | rfl | rfl
        exacts [h1, h2, h3, h4]
      exact (Submodule.mem_bot ℚ).2 (Subtype.ext hzero)
    calc _ ≤ Module.finrank ℚ ℚ := LinearMap.finrank_le_finrank_of_injective hφ
      _ = 1 := Module.finrank_self ℚ
  · -- Rank–nullity: the edge boundary lands in the augmentation kernel, of rank three.
    have hrn := LinearMap.finrank_range_add_finrank_ker (boundary loopK ℚ 0)
    have hsn := LinearMap.finrank_range_add_finrank_ker (zeroChainSum loopK ℚ)
    have hC1 : Module.finrank ℚ (Chain loopK ℚ (0 + 1)) = 4 := by
      rw [Module.finrank_finsupp_self, hcard1]
    have hC0 : Module.finrank ℚ (Chain loopK ℚ 0) = 4 := by
      rw [Module.finrank_finsupp_self, hcard0]
    have hsurj : LinearMap.range (zeroChainSum loopK ℚ) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨Finsupp.single (loopVertex loopA) c, zeroChainSum_single _ ℚ _ c⟩
    have hle : LinearMap.range (boundary loopK ℚ 0) ≤ LinearMap.ker (zeroChainSum loopK ℚ) :=
      LinearMap.range_le_ker_iff.2 (zeroChainSum_boundary loopK ℚ)
    have hmono := Submodule.finrank_mono hle
    rw [hsurj, finrank_top, Module.finrank_self] at hsn
    omega

/-- The coarse stage has one vertex and no edge. -/
private instance loop_coarse_noEdges :
    IsEmpty (Face (mapper (plHeight C4 h4) (loopCover 1)) 1) :=
  isEmpty_face_one_of_disjoint _ _ fun i j hij => absurd (Subsingleton.elim (α := Unit) i j) hij

/-- The bar `[0, 1)`: a loop that dies at the coarse stage. -/
def loopBar : FiniteInterval 2 := ⟨0, 1, by omega, by omega⟩

/-- With the three-member cover, the degree-one Mapper barcode of the 4-cycle over `ℚ` is the
single bar `[0, 1)` ending at the coarse one-member stage. -/
theorem loop_mapperBarcode :
    mapperBarcode ℚ (plHeight C4 h4) loopCover loopRefinement 1 = {loopBar} := by
  have hcoarse := finrank_homology_eq_zero (mapper (plHeight C4 h4) (loopCover 1)) ℚ 1
  rw [mapperBarcode_eq_iff]
  intro q t h
  fin_cases q <;> fin_cases t
  · rw [mapperHomologyMap_eq_id, finrank_range_id]
    exact loop_finrank_H1.trans (by decide)
  · refine (Nat.le_zero.1 ?_).trans (by decide)
    calc _ ≤ Module.finrank ℚ
          (simplicialHomology (mapper (plHeight C4 h4) (loopCover 1)) ℚ 1) :=
          Submodule.finrank_le _
      _ = 0 := hcoarse
  · exact absurd h (by decide)
  · rw [mapperHomologyMap_eq_id, finrank_range_id]
    exact hcoarse.trans (by decide)


end Loop

/-! ## Negative control: infinitely many components -/

section NatComponents

open TDA.Mapper.GraphPL.Examples (natToUnit natMapperVertexEquiv)
open TDA.Mapper.Examples (unitCover)

/-- The constant map from discrete `ℕ` with the one-member full cover has infinitely many
Mapper vertices, so the face-finiteness hypothesis of `mapperBarcode` fails in degree `0`. -/
theorem natToUnit_not_finite_face : ¬ Finite (Face (mapper natToUnit unitCover) 0) := by
  intro hfin
  let g : ℕ → Face (mapper natToUnit unitCover) 0 := fun m =>
    ⟨{(natMapperVertexEquiv.symm m).1}, (natMapperVertexEquiv.symm m).2,
      Finset.card_singleton _⟩
  have hg : Function.Injective g := by
    intro m m' hm
    have h1 : (natMapperVertexEquiv.symm m).1 = (natMapperVertexEquiv.symm m').1 :=
      Finset.singleton_injective (congrArg Subtype.val hm)
    exact natMapperVertexEquiv.symm.injective (Subtype.ext h1)
  have := Finite.of_injective g hg
  exact not_finite ℕ

/-- For every linear order on its component indices, the degree-zero homology of this Mapper
complex is not finite-dimensional over any field, so no degree-zero Mapper homology module with
this stage has a barcode. -/
theorem natToUnit_not_finiteDimensional [LinearOrder (ComponentIndex natToUnit unitCover)]
    (k : Type) [Field k] :
    ¬ FiniteDimensional k (simplicialHomology (mapper natToUnit unitCover) k 0) := by
  have : IsEmpty (Face (mapper natToUnit unitCover) 1) := ⟨fun σ => by
    obtain ⟨a, b, hab, hσ⟩ := Finset.card_eq_two.1 σ.2.2
    apply hab
    exact eq_of_mem_mapper_face_of_fst_eq natToUnit unitCover σ.2.1 (by simp [hσ])
      (by simp [hσ]) rfl⟩
  intro hfd
  have hchain : Module.Finite k (Chain (mapper natToUnit unitCover) k 0) :=
    Module.Finite.equiv (zeroHomologyEquivOfNoEdges _ k)
  rcases Module.finite_finsupp_self_iff.1 hchain with hk | hface
  · exact not_subsingleton k hk
  · exact natToUnit_not_finite_face hface

end NatComponents

end

end TDA.Mapper.RefinementHomologyBarcodeExamples
