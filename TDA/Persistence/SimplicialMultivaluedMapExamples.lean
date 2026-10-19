import TDA.Persistence.SimplicialMultivaluedMap
import TDA.Simplicial.H0Augmentation
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Actual shifted maps, selector independence and controls on support and coefficients. -/

namespace TDA.Persistence.SimplicialMultivaluedMapExamples

open CategoryTheory TDA.Filtration TDA.Simplicial
open scoped Matrix NNReal

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

@[simp] private theorem mem_full {V : Type} (s : Finset V) :
    s ∈ (⊤ : PreAbstractSimplicialComplex V) ↔ s.Nonempty := Iff.rfl

private def birth {V : Type} (a : ℝ) (K : PreAbstractSimplicialComplex V) :
    SimplicialFiltration ℝ V where
  toFun t := if a ≤ t then K else ⊥
  monotone' := by
    intro s t hst
    by_cases hs : a ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst)]
      exact le_rfl
    · simp only [if_neg hs]
      exact bot_le

private def constF {V : Type} (K : PreAbstractSimplicialComplex V) :
    SimplicialFiltration ℝ V := OrderHom.const _ K

private def vertex {V : Type} (K : PreAbstractSimplicialComplex V) (x : V)
    (hx : ({x} : Finset V) ∈ K) : Face K 0 := ⟨{x}, hx, by simp⟩

private def vCycle {V : Type} [LinearOrder V] (R : Type) [Ring R]
    (K : PreAbstractSimplicialComplex V) (x : V) (hx : ({x} : Finset V) ∈ K) (a : R) :
    simplicialCycles K R 0 :=
  ⟨Finsupp.single (vertex K x hx) a, by rw [simplicialCycles_zero]; trivial⟩

private def vClass {V : Type} [LinearOrder V] (R : Type) [Ring R]
    (K : PreAbstractSimplicialComplex V) (x : V) (hx : ({x} : Finset V) ∈ K) (a : R) :=
  simplicialHomologyClass R K 0 (vCycle R K x hx a)

private theorem vertex_chain {V W : Type} [LinearOrder V] [LinearOrder W]
    (R : Type) [Ring R] {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (f : VertexMap K L) (x : V)
    (hx : ({x} : Finset V) ∈ K) (hy : ({f x} : Finset W) ∈ L) (a : R) :
    vertexChainMap R f 0 (Finsupp.single (vertex K x hx) a) =
      Finsupp.single (vertex L (f x) hy) a := by
  rw [vertexChainMap_vertex]
  congr 1
  apply Subtype.ext
  simp only [vertexImageFace, tupleFace]
  dsimp
  rw [← Finset.image_image, Finset.image_orderEmbOfFin_univ]
  simp [vertex]

private theorem vClass_map {V W : Type} [LinearOrder V] [LinearOrder W]
    (R : Type) [Ring R] {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (f : VertexMap K L) (x : V)
    (hx : ({x} : Finset V) ∈ K) (hy : ({f x} : Finset W) ∈ L) (a : R) :
    (simplicialHomologyMap R f 0).hom (vClass R K x hx a) = vClass R L (f x) hy a :=
  simplicialHomologyMap_class R f 0 _ _ (vertex_chain R f x hx hy a)

private theorem vClass_nonzero {V : Type} [LinearOrder V]
    (K : PreAbstractSimplicialComplex V) (x : V) (hx : ({x} : Finset V) ∈ K) :
    vClass ℚ K x hx 1 ≠ 0 := by
  intro hz
  have hq := congrArg (homologyKernelQuotient ℚ (simplicialChainComplex K ℚ) 0).hom.hom hz
  unfold vClass at hq
  rw [simplicialHomologyClass_quotient, map_zero] at hq
  exact zeroVertexCycle_not_boundary K ℚ (vertex K x hx)
    ((Submodule.Quotient.mk_eq_zero _).mp hq)

private theorem univTotal {V W : Type} (w : W) :
    Relator.LeftTotal (fun x y => (x,y) ∈ (Set.univ : SetRel V W)) :=
  fun _ => ⟨w, Set.mem_univ _⟩

private theorem subordinate_univ {V W : Type} (f : V → W) :
    Function.graph f ⊆ (Set.univ : SetRel V W) := Set.subset_univ _

private theorem univBirth {V W : Type} (a b : ℝ) (K : PreAbstractSimplicialComplex V) :
    IsShiftedSimplicialRelation (birth a K) (birth b (⊤ : PreAbstractSimplicialComplex W))
      (b-a) Set.univ := by
  intro t σ hσ τ hτ _
  by_cases ht : a ≤ t
  · have hb : b ≤ t + (b-a) := by linarith
    simpa [birth, hb] using hτ
  · simp [birth, ht] at hσ

private theorem fullRelation {V W : Type} (K : PreAbstractSimplicialComplex V) :
    IsShiftedSimplicialRelation (constF K)
      (constF (⊤ : PreAbstractSimplicialComplex W)) 0 Set.univ := by
  intro _ _ _ _ hτ _
  exact hτ

private abbrev pointK := (⊤ : PreAbstractSimplicialComplex (Fin 1))
private abbrev edgeK := (⊤ : PreAbstractSimplicialComplex (Fin 2))
private theorem point_vertex : ({(0 : Fin 1)} : Finset (Fin 1)) ∈ pointK := by simp
private theorem edge_vertex (i : Fin 2) : ({i} : Finset (Fin 2)) ∈ edgeK := by simp

/-! A genuine degree-one shifted map with distinct endpoint selectors. -/

private abbrev pointBirth := birth 0 pointK
private abbrev edgeBirth := birth 1 edgeK
private theorem shiftedEdgeRelation :
    IsShiftedSimplicialRelation pointBirth edgeBirth 1 (Set.univ : SetRel (Fin 1) (Fin 2)) := by
  simpa using univBirth (W := Fin 2) 0 1 pointK

private def shiftedEndpoint (i : Fin 2) :=
  shiftedSimplicialHomologyMap ℚ
    (shiftedEdgeRelation.of_subordinate (subordinate_univ (fun _ : Fin 1 => i))) 0

private def shiftedCanonical :=
  multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 1) (0 : Fin 2)) shiftedEdgeRelation 0

private theorem shifted_selectors_equal :
    shiftedCanonical = shiftedEndpoint 0 ∧ shiftedCanonical = shiftedEndpoint 1 := by
  constructor <;> exact multivaluedSimplicialHomologyMap_eq ℚ _ _ (subordinate_univ _) 0

private theorem shifted_chainmaps_differ :
    vertexChainMap ℚ
      ((shiftedEdgeRelation.of_subordinate (subordinate_univ (fun _ : Fin 1 => (0 : Fin 2)))).vertexMap 0) 0 ≠
    vertexChainMap ℚ
      ((shiftedEdgeRelation.of_subordinate (subordinate_univ (fun _ : Fin 1 => (1 : Fin 2)))).vertexMap 0) 0 := by
  intro he
  have hv : ({(0 : Fin 1)} : Finset (Fin 1)) ∈ pointBirth 0 := by norm_num [birth]
  have hc := LinearMap.congr_fun he (Finsupp.single (vertex _ 0 hv) 1)
  rw [vertex_chain ℚ _ 0 hv (by norm_num [birth]),
    vertex_chain ℚ _ 0 hv (by norm_num [birth])] at hc
  have hs := congrArg (fun c => c (vertex (edgeBirth (0+1)) 0 (by norm_num [birth]))) hc
  norm_num [vertex, IsShiftedSimplicial.vertexMap] at hs

private theorem shifted_common_image_nonzero :
    (shiftedCanonical.app 0).hom
      (vClass ℚ (pointBirth 0) 0 (by norm_num [birth]) 1) ≠ 0 := by
  intro hz
  have hc := congrArg (fun m => m.hom
      (vClass ℚ (pointBirth 0) 0 (by norm_num [birth]) 1))
    (multivaluedSimplicialHomologyMap_app ℚ (univTotal (V := Fin 1) (0 : Fin 2))
      shiftedEdgeRelation (subordinate_univ (fun _ : Fin 1 => (0 : Fin 2))) 0 0)
  have hm := vClass_map ℚ
    ((shiftedEdgeRelation.of_subordinate (subordinate_univ (fun _ : Fin 1 => (0 : Fin 2)))).vertexMap 0)
      0 (by norm_num [birth]) (by norm_num [birth]) 1
  exact vClass_nonzero _ _ _ (hm.symm.trans (hc.symm.trans hz))

private theorem shifted_before_birth : pointBirth (-1) = ⊥ := by norm_num [birth]

private theorem shifted_before_birth_map_zero : shiftedCanonical.app (-1) = 0 := by
  apply ModuleCat.hom_ext
  ext z
  have source_zero : ∀ (K : PreAbstractSimplicialComplex (Fin 1)) (hK : K = ⊥)
      (w : simplicialHomology K ℚ 0), w = 0 := by
    intro K hK w
    subst K
    exact simplicialHomology_bot_zero ℚ w
  have hz : z = 0 := source_zero _ shifted_before_birth z
  rw [hz]
  exact map_zero _

private theorem shifted_naturality_on_class :
    (simplicialHomologyIncl ℚ (pointBirth.monotone (show (0 : ℝ) ≤ 1 by norm_num)) 0 ≫
        shiftedCanonical.app 1).hom (vClass ℚ (pointBirth 0) 0 (by norm_num [birth]) 1) =
      (shiftedCanonical.app 0 ≫ simplicialHomologyIncl ℚ
        (edgeBirth.monotone (show (0 : ℝ)+1 ≤ 1+1 by norm_num)) 0).hom
          (vClass ℚ (pointBirth 0) 0 (by norm_num [birth]) 1) := by
  exact congrArg (fun m => m.hom (vClass ℚ (pointBirth 0) 0 (by norm_num [birth]) 1))
    (shiftedCanonical.naturality (homOfLE (show (0 : ℝ) ≤ 1 by norm_num)))

/-! A negative real shift is a genuine degree map, with the positive evaluation direction. -/

private theorem negative_identity :
    IsShiftedSimplicial (birth 1 pointK) (birth 0 pointK) (-1) id := by
  intro t σ hσ
  by_cases ht : (1 : ℝ) ≤ t
  · have hh : (0 : ℝ) ≤ t + -1 := by linarith
    simpa [birth, hh] using (show σ ∈ pointK by simpa [birth, ht] using hσ)
  · simp [birth, ht] at hσ

private theorem negative_actual_image :
    ((multivaluedSimplicialHomologyMap ℚ (C := Function.graph (id : Fin 1 → Fin 1))
      (fun x => ⟨x, rfl⟩) ((isShiftedSimplicialRelation_graph_iff _).mpr negative_identity) 0).app 1).hom
        (vClass ℚ (birth 1 pointK 1) 0 (by norm_num [birth]) 1) ≠ 0 := by
  intro hz
  have hc := congrArg (fun m => m.hom
      (vClass ℚ (birth 1 pointK 1) 0 (by norm_num [birth]) 1))
    (multivaluedSimplicialHomologyMap_app ℚ (C := Function.graph (id : Fin 1 → Fin 1))
      (fun x => ⟨x, rfl⟩) ((isShiftedSimplicialRelation_graph_iff _).mpr negative_identity)
      (Set.Subset.refl _) 0 1)
  have hm := vClass_map ℚ (negative_identity.vertexMap 1) 0
    (by norm_num [birth]) (by norm_num [birth]) 1
  exact vClass_nonzero _ _ _ (hm.symm.trans (hc.symm.trans hz))

private theorem positive_identity :
    IsShiftedSimplicial (birth 0 pointK) (birth 1 pointK) 1 id := by
  intro t σ hσ
  by_cases ht : (0 : ℝ) ≤ t
  · have hh : (1 : ℝ) ≤ t + 1 := by linarith
    simpa [birth, hh] using (show σ ∈ pointK by simpa [birth, ht] using hσ)
  · simp [birth, ht] at hσ

private theorem wrong_shift_fails :
    ¬IsShiftedSimplicial (birth 0 pointK) (birth 1 pointK) (-1) id := by
  intro h
  have hf := h 0 {(0 : Fin 1)} (by norm_num [birth])
  norm_num [birth] at hf

/-! Infinite fibers still admit all finite joint-face tests. -/

private theorem infinite_image :
    SetRel.image (Set.univ : SetRel (Fin 1) ℕ) ({(0 : Fin 1)} : Set (Fin 1)) = Set.univ := by
  ext y
  constructor
  · intro _; trivial
  · intro _; exact ⟨0, Set.mem_singleton 0, Set.mem_univ _⟩

private theorem infinite_image_is_infinite :
    (SetRel.image (Set.univ : SetRel (Fin 1) ℕ) ({(0 : Fin 1)} : Set (Fin 1))).Infinite := by
  rw [infinite_image]
  exact Set.infinite_univ

private abbrev infiniteRelation := fullRelation (W := ℕ) pointK
private def infiniteCanonical :=
  multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 1) (0 : ℕ)) infiniteRelation 0

private theorem infinite_selector_components :
    infiniteCanonical = shiftedSimplicialHomologyMap ℚ
      (infiniteRelation.of_subordinate (subordinate_univ (fun _ : Fin 1 => (0 : ℕ)))) 0 ∧
    infiniteCanonical = shiftedSimplicialHomologyMap ℚ
      (infiniteRelation.of_subordinate (subordinate_univ (fun _ : Fin 1 => (1 : ℕ)))) 0 := by
  constructor <;> exact multivaluedSimplicialHomologyMap_eq ℚ _ _ (subordinate_univ _) 0

private theorem infinite_nonzero_image :
    (infiniteCanonical.app 0).hom
      (vClass ℚ ((constF pointK) 0) 0 point_vertex 1) ≠ 0 := by
  rw [infinite_selector_components.1, shiftedSimplicialHomologyMap_app]
  change (simplicialHomologyMap ℚ _ 0).hom _ ≠ 0
  rw [vClass_map ℚ _ 0 _ (by simp [constF])]
  exact vClass_nonzero _ _ _

/-! The joint finite-image premise cannot be replaced by individual selector facehood. -/

private def isolatedK : PreAbstractSimplicialComplex (Fin 2) where
  faces := {s | s.Nonempty ∧ s.card ≤ 1}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts htn => ⟨htn, (Finset.card_le_card hts).trans hs.2⟩⟩

private theorem isolated_vertex (i : Fin 2) : ({i} : Finset (Fin 2)) ∈ isolatedK := by
  constructor <;> simp

private instance isolated_no_edges : IsEmpty (Face isolatedK 1) := ⟨by
  intro σ
  have hle : σ.1.card ≤ 1 := σ.2.1.2
  have heq := σ.2.2
  omega⟩

private theorem isolated_classes_differ :
    vClass ℚ isolatedK 0 (isolated_vertex 0) 1 ≠
      vClass ℚ isolatedK 1 (isolated_vertex 1) 1 := by
  intro hc
  have hq := congrArg (homologyKernelQuotient ℚ (simplicialChainComplex isolatedK ℚ) 0).hom.hom hc
  unfold vClass at hq
  rw [simplicialHomologyClass_quotient, simplicialHomologyClass_quotient] at hq
  have hb := (Submodule.Quotient.eq _).mp hq
  obtain ⟨c, hcb⟩ := (mem_simplicialBoundaries_iff ℚ isolatedK 0 _).mp hb
  have hz : c = 0 := by
    apply Finsupp.ext
    intro σ
    exact isEmptyElim σ
  rw [hz, map_zero] at hcb
  have hv := congrArg (fun c : Chain isolatedK ℚ 0 => c (vertex isolatedK 0 (isolated_vertex 0))) hcb
  norm_num [vCycle, vertex] at hv

private theorem isolated_shift (i : Fin 2) :
    IsShiftedSimplicial (constF pointK) (constF isolatedK) 0 (fun _ : Fin 1 => i) := by
  classical
  intro t σ hσ
  have hn : σ.Nonempty := hσ
  simpa [constF, OrderHom.const, Finset.image_const hn] using isolated_vertex i

private theorem isolated_maps_differ :
    simplicialHomologyMap ℚ ((isolated_shift 0).vertexMap 0) 0 ≠
      simplicialHomologyMap ℚ ((isolated_shift 1).vertexMap 0) 0 := by
  intro he
  have hc := congrArg (fun m => m.hom (vClass ℚ pointK 0 point_vertex 1)) he
  have h₀ := vClass_map ℚ ((isolated_shift 0).vertexMap 0) 0 point_vertex (isolated_vertex 0) 1
  have h₁ := vClass_map ℚ ((isolated_shift 1).vertexMap 0) 0 point_vertex (isolated_vertex 1) 1
  exact isolated_classes_differ (h₀.symm.trans (hc.trans h₁))

private theorem individual_selectors_insufficient :
    ¬IsShiftedSimplicialRelation (constF pointK) (constF isolatedK) 0
      (Set.univ : SetRel (Fin 1) (Fin 2)) := by
  intro h
  have ht := h 0 {0} point_vertex {0,1} (by simp) (by
    intro y _
    exact ⟨0, by simp, Set.mem_univ _⟩)
  have hc := ht.2
  norm_num at hc

private theorem no_common_valid_relation {C : SetRel (Fin 1) (Fin 2)}
    (h₀ : Function.graph (fun _ : Fin 1 => (0 : Fin 2)) ⊆ C)
    (h₁ : Function.graph (fun _ : Fin 1 => (1 : Fin 2)) ⊆ C) :
    ¬IsShiftedSimplicialRelation (constF pointK) (constF isolatedK) 0 C := by
  intro hC
  have he := Contiguous.simplicialHomologyMap_eq ℚ (hC.contiguous h₀ h₁ 0) 0
  exact isolated_maps_differ he

private def switching (t : ℝ) : simplicialHomology pointK ℚ 0 ⟶ simplicialHomology isolatedK ℚ 0 :=
  if t < 0 then simplicialHomologyMap ℚ ((isolated_shift 0).vertexMap 0) 0
    else simplicialHomologyMap ℚ ((isolated_shift 1).vertexMap 0) 0

private theorem switching_fails_naturality :
    simplicialHomologyIncl ℚ (show (constF pointK) (-1) ≤ (constF pointK) 0 from le_rfl) 0 ≫
        switching 0 ≠ switching (-1) ≫
          simplicialHomologyIncl ℚ (show (constF isolatedK) (-1) ≤ (constF isolatedK) 0 from le_rfl) 0 := by
  change simplicialHomologyIncl ℚ (show pointK ≤ pointK from le_rfl) 0 ≫ switching 0 ≠
    switching (-1) ≫ simplicialHomologyIncl ℚ (show isolatedK ≤ isolatedK from le_rfl) 0
  rw [simplicialHomologyIncl_id, simplicialHomologyIncl_id, Category.id_comp, Category.comp_id]
  norm_num [switching]
  exact Ne.symm isolated_maps_differ

/-! The same global collapse remains natural while a new edge kills a nonzero H0 difference. -/

private def changing : SimplicialFiltration ℝ (Fin 2) where
  toFun t := if 1 ≤ t then edgeK else if 0 ≤ t then isolatedK else ⊥
  monotone' := by
    intro s t hst
    by_cases ht : (1 : ℝ) ≤ t
    · simp only [if_pos ht]
      exact le_top
    · have hs : ¬(1 : ℝ) ≤ s := fun h => ht (h.trans hst)
      simp only [if_neg ht, if_neg hs]
      by_cases hs0 : (0 : ℝ) ≤ s
      · simp only [if_pos hs0, if_pos (hs0.trans hst)]
        exact le_rfl
      · simp only [if_neg hs0]
        exact bot_le

private theorem changing_zero : changing 0 = isolatedK := by norm_num [changing]
private theorem changing_one : changing 1 = edgeK := by norm_num [changing]

private theorem collapse_shift : IsShiftedSimplicial changing (birth 0 pointK) 0
    (fun _ : Fin 2 => (0 : Fin 1)) := by
  intro t σ hσ
  have ht : (0 : ℝ) ≤ t := by
    by_contra hh
    have hh1 : ¬(1 : ℝ) ≤ t := by linarith
    simp [changing, hh, hh1] at hσ
  have hn := (changing t).isRelLowerSet_faces hσ |>.1
  have hi : (σ.image (fun _ : Fin 2 => (0 : Fin 1))).Nonempty := Finset.image_nonempty.mpr hn
  simpa [birth, ht] using hi

private def collapseCanonical :=
  multivaluedSimplicialHomologyMap ℚ (C := Function.graph (fun _ : Fin 2 => (0 : Fin 1)))
    (fun _ => ⟨0,rfl⟩) ((isShiftedSimplicialRelation_graph_iff _).mpr collapse_shift) 0

private theorem collapse_graph_agrees : collapseCanonical = shiftedSimplicialHomologyMap ℚ collapse_shift 0 :=
  multivaluedSimplicialHomologyMap_graph ℚ collapse_shift 0

private theorem collapse_naturality :
    simplicialHomologyIncl ℚ (changing.monotone (show (0 : ℝ) ≤ 1 by norm_num)) 0 ≫
      collapseCanonical.app 1 = collapseCanonical.app 0 ≫
        simplicialHomologyIncl ℚ ((birth 0 pointK).monotone
          (show (0 : ℝ)+0 ≤ 1+0 by norm_num)) 0 :=
  collapseCanonical.naturality (homOfLE (show (0 : ℝ) ≤ 1 by norm_num))

private theorem collapse_vertex_nonzero (i : Fin 2) :
    (collapseCanonical.app 0).hom
      (vClass ℚ (changing 0) i (by rw [changing_zero]; exact isolated_vertex i) 1) ≠ 0 := by
  intro hz
  have he := multivaluedSimplicialHomologyMap_app ℚ
    (C := Function.graph (fun _ : Fin 2 => (0 : Fin 1)))
    (fun _ => ⟨0,rfl⟩) ((isShiftedSimplicialRelation_graph_iff _).mpr collapse_shift)
    (Set.Subset.refl _) 0 0
  have hc := congrArg (fun m => m.hom
    (vClass ℚ (changing 0) i (by rw [changing_zero]; exact isolated_vertex i) 1)) he
  have hm := vClass_map ℚ (collapse_shift.vertexMap 0) i
    (by rw [changing_zero]; exact isolated_vertex i) (by norm_num [birth]) 1
  exact vClass_nonzero _ _ _ (hm.symm.trans (hc.symm.trans hz))

private theorem early_difference_nonzero :
    vClass ℚ (changing 0) 1 (by rw [changing_zero]; exact isolated_vertex 1) 1 -
      vClass ℚ (changing 0) 0 (by rw [changing_zero]; exact isolated_vertex 0) 1 ≠ 0 := by
  rw [sub_ne_zero]
  have transport : ∀ (K : PreAbstractSimplicialComplex (Fin 2)) (hK : K = isolatedK)
      (h₁ : ({(1 : Fin 2)} : Finset (Fin 2)) ∈ K) (h₀ : ({(0 : Fin 2)} : Finset (Fin 2)) ∈ K),
      vClass ℚ K 1 h₁ 1 ≠ vClass ℚ K 0 h₀ 1 := by
    intro K hK h₁ h₀
    subst K
    exact Ne.symm isolated_classes_differ
  exact transport _ changing_zero _ _

private theorem edge_boundary_explicit :
    boundary edgeK ℚ 0 (orientedTuple edgeK ℚ ![0,1]) =
      Finsupp.single (vertex edgeK 1 (edge_vertex 1)) 1 -
        Finsupp.single (vertex edgeK 0 (edge_vertex 0)) 1 := by
  rw [boundary_orientedTuple edgeK ℚ (n := 0) (![0,1] : Fin 2 → Fin 2) (by simp)]
  unfold tupleBoundarySum
  rw [Fin.sum_univ_two]
  have h0 : ((![0,1] : Fin 2 → Fin 2) ∘ (0 : Fin 2).succAbove) = fun _ : Fin 1 => (1 : Fin 2) := by
    funext i; fin_cases i; rfl
  have h1 : ((![0,1] : Fin 2 → Fin 2) ∘ (1 : Fin 2).succAbove) = fun _ : Fin 1 => (0 : Fin 2) := by
    funext i; fin_cases i; rfl
  rw [h0,h1]
  have hv (i : Fin 2) : orientedTuple edgeK ℚ (fun _ : Fin 1 => i) =
      Finsupp.single (vertex edgeK i (edge_vertex i)) 1 := by
    rw [orientedTuple_of_monotone edgeK ℚ _
      (fun a b _ => Fin.ext (by omega)) (by simp)
      (fun _ _ _ => le_rfl)]
    congr 1
  simp [hv, sub_eq_add_neg]

private theorem edge_classes_equal :
    vClass ℚ edgeK 1 (edge_vertex 1) 1 = vClass ℚ edgeK 0 (edge_vertex 0) 1 := by
  apply (homologyKernelQuotient ℚ (simplicialChainComplex edgeK ℚ) 0).toLinearEquiv.injective
  change (homologyKernelQuotient ℚ (simplicialChainComplex edgeK ℚ) 0).hom.hom
      (vClass ℚ edgeK 1 (edge_vertex 1) 1) =
    (homologyKernelQuotient ℚ (simplicialChainComplex edgeK ℚ) 0).hom.hom
      (vClass ℚ edgeK 0 (edge_vertex 0) 1)
  unfold vClass
  rw [simplicialHomologyClass_quotient, simplicialHomologyClass_quotient]
  apply (Submodule.Quotient.eq _).mpr
  apply (mem_simplicialBoundaries_iff ℚ edgeK 0 _).mpr
  exact ⟨orientedTuple edgeK ℚ ![0,1], edge_boundary_explicit⟩

private theorem actual_inclusion_kills_early_difference :
    (simplicialHomologyIncl ℚ (changing.monotone (show (0 : ℝ) ≤ 1 by norm_num)) 0).hom
      (vClass ℚ (changing 0) 1 (by rw [changing_zero]; exact isolated_vertex 1) 1 -
        vClass ℚ (changing 0) 0 (by rw [changing_zero]; exact isolated_vertex 0) 1) = 0 := by
  rw [map_sub, ← simplicialHomologyMap_inclusion,
    vClass_map ℚ _ 1 _ (by change ({(1 : Fin 2)} : Finset (Fin 2)) ∈ changing 1; rw [changing_one]; exact edge_vertex 1),
    vClass_map ℚ _ 0 _ (by change ({(0 : Fin 2)} : Finset (Fin 2)) ∈ changing 1; rw [changing_one]; exact edge_vertex 0)]
  apply sub_eq_zero.mpr
  have transport : ∀ (K : PreAbstractSimplicialComplex (Fin 2)) (hK : K = edgeK)
      (h₁ : ({(1 : Fin 2)} : Finset (Fin 2)) ∈ K) (h₀ : ({(0 : Fin 2)} : Finset (Fin 2)) ∈ K),
      vClass ℚ K 1 h₁ 1 = vClass ℚ K 0 h₀ 1 := by
    intro K hK h₁ h₀
    subst K
    exact edge_classes_equal
  exact transport _ changing_one _ _

private theorem graph_identity_fixture :
    multivaluedSimplicialHomologyMap ℚ (C := Function.graph (id : Fin 2 → Fin 2))
      (fun x => ⟨x,rfl⟩) ((isShiftedSimplicialRelation_graph_iff _).mpr (isShiftedSimplicial_id changing)) 0 ≫
      (RealShift.zeroIso (simplicialHomologyPModule ℚ changing 0)).hom = 𝟙 _ := by
  rw [multivaluedSimplicialHomologyMap_graph]
  exact shiftedSimplicialHomologyMap_id ℚ changing 0

/-! Ambient totality includes ghosts; only actual faces impose target facehood. -/

private def ghostEdge : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s ⊆ {0,1}}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts htn => ⟨htn, hts.trans hs.2⟩⟩

private def ghostC : SetRel (Fin 2) (Fin 3) :=
  {p | if p.1 = 0 then p.2 = 0 ∨ p.2 = 1 else p.2 = 2}

private theorem ghost_total : Relator.LeftTotal (fun x y => (x,y) ∈ ghostC) := by
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by simp [ghostC, hx]⟩
  · exact ⟨2, by simp [ghostC, hx]⟩

private theorem ghost_relation :
    IsShiftedSimplicialRelation (constF (singletonFace (0 : Fin 2))) (constF ghostEdge) 0 ghostC := by
  intro t σ hσ τ hτ hsub
  have hσ0 : σ = {0} := hσ
  refine ⟨hτ, ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hsub hy
  have hx0 : x = 0 := by simpa [hσ0] using hx
  have hy01 : y = 0 ∨ y = 1 := by simpa [ghostC, hx0] using hxy
  simpa using hy01

private def ghostSelector (i : Fin 2) : Fin 2 → Fin 3 :=
  fun x => if x = 0 then i.castSucc else 2

private theorem ghost_subordinate (i : Fin 2) : Function.graph (ghostSelector i) ⊆ ghostC := by
  intro ⟨x,y⟩ hxy
  change ghostSelector i x = y at hxy
  subst y
  by_cases hx : x = 0
  · fin_cases i <;> simp [ghostC, ghostSelector, hx]
  · simp [ghostC, ghostSelector, hx]

private def ghostCanonical := multivaluedSimplicialHomologyMap ℚ ghost_total ghost_relation 0

private theorem ghost_selectors_agree :
    ghostCanonical = shiftedSimplicialHomologyMap ℚ (ghost_relation.of_subordinate (ghost_subordinate 0)) 0 ∧
    ghostCanonical = shiftedSimplicialHomologyMap ℚ (ghost_relation.of_subordinate (ghost_subordinate 1)) 0 := by
  constructor <;> exact multivaluedSimplicialHomologyMap_eq ℚ _ _ (ghost_subordinate _) 0

private theorem ghost_nonzero_image :
    (ghostCanonical.app 0).hom
      (vClass ℚ ((constF (singletonFace (0 : Fin 2))) 0) 0 rfl 1) ≠ 0 := by
  intro hz
  have hc := congrArg (fun m => m.hom
    (vClass ℚ ((constF (singletonFace (0 : Fin 2))) 0) 0 rfl 1))
    (multivaluedSimplicialHomologyMap_app ℚ ghost_total ghost_relation (ghost_subordinate 0) 0 0)
  have hm := vClass_map ℚ ((ghost_relation.of_subordinate (ghost_subordinate 0)).vertexMap 0)
    0 rfl (by constructor <;> simp [ghostSelector]) 1
  exact vClass_nonzero _ _ _ (hm.symm.trans (hc.symm.trans hz))

private theorem ghost_support_control :
    ({(2 : Fin 3)} : Finset (Fin 3)) ∉ ghostEdge ∧
    ({(1 : Fin 2)} : Finset (Fin 2)) ∉ singletonFace (0 : Fin 2) ∧ (1,2) ∈ ghostC := by
  constructor
  · intro h
    have hh : ({(2 : Fin 3)} : Finset (Fin 3)) ⊆ {0,1} := h.2
    have := hh (by simp : (2 : Fin 3) ∈ ({2} : Finset (Fin 3)))
    exact (by decide : (2 : Fin 3) ∉ ({0,1} : Finset (Fin 3))) this
  constructor
  · simp [mem_singletonFace_iff]
  · simp [ghostC]

/-! Empty target needs no inhabitation instance, but ambient totality is indispensable. -/

private theorem empty_total :
    Relator.LeftTotal (fun x y : Fin 0 => (x,y) ∈ (∅ : SetRel (Fin 0) (Fin 0))) :=
  fun x => Fin.elim0 x

private theorem empty_relation :
    IsShiftedSimplicialRelation (constF (⊥ : PreAbstractSimplicialComplex (Fin 0)))
      (constF (⊥ : PreAbstractSimplicialComplex (Fin 0))) (-3) ∅ := by
  intro t σ hσ
  exact False.elim hσ

private theorem empty_canonical_zero :
    multivaluedSimplicialHomologyMap ℤ empty_total empty_relation 0 = 0 := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  ext z
  have hz : z = 0 := simplicialHomology_bot_zero ℤ z
  rw [hz]
  exact map_zero _

private theorem bottom_relation :
    IsShiftedSimplicialRelation (constF (⊥ : PreAbstractSimplicialComplex (Fin 1)))
      (constF edgeK) 0 (Set.univ : SetRel (Fin 1) (Fin 2)) := by
  intro t σ hσ
  exact False.elim hσ

private theorem bottom_canonical_zero :
    multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 1) (0 : Fin 2)) bottom_relation 0 = 0 := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  ext z
  have hz : z = 0 := simplicialHomology_bot_zero ℚ z
  rw [hz]
  exact map_zero _

private theorem nonempty_to_empty_not_total (C : SetRel (Fin 1) (Fin 0)) :
    ¬Relator.LeftTotal (fun x y => (x,y) ∈ C) := by
  intro h
  obtain ⟨y,_⟩ := h 0
  exact Fin.elim0 y

/-! Actual canonical components retain a noncentral coefficient over a noncommutative ring. -/

private theorem singletonIdentity :
    IsShiftedSimplicial (constF (singletonFace (0 : Fin 1)))
      (constF (singletonFace (0 : Fin 1))) 0 id :=
  isShiftedSimplicial_id _

private theorem canonical_singleton_coefficient (R : Type) [Ring R] (a : R) :
    simplicialSingletonH0Equiv R (0 : Fin 1)
      (((multivaluedSimplicialHomologyMap R (C := Function.graph (id : Fin 1 → Fin 1))
        (fun x => ⟨x,rfl⟩) ((isShiftedSimplicialRelation_graph_iff _).mpr singletonIdentity) 0).app 0).hom
          (vClass R (singletonFace (0 : Fin 1)) 0 rfl a)) = a := by
  have hc := congrArg (fun m => m.hom (vClass R (singletonFace (0 : Fin 1)) 0 rfl a))
    (multivaluedSimplicialHomologyMap_app R (C := Function.graph (id : Fin 1 → Fin 1))
      (fun x => ⟨x,rfl⟩) ((isShiftedSimplicialRelation_graph_iff _).mpr singletonIdentity)
      (Set.Subset.refl _) 0 0)
  have hm := vClass_map R (singletonIdentity.vertexMap 0) 0 rfl rfl a
  calc
    _ = simplicialSingletonH0Equiv R 0 (vClass R (singletonFace (0 : Fin 1)) 0 rfl a) :=
      congrArg (simplicialSingletonH0Equiv R (0 : Fin 1)) (hc.trans hm)
    _ = a := simplicialSingletonH0Equiv_class R (0 : Fin 1) a

private theorem matrix_noncentral :
    (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,0;0,0] ≠
      !![1,0;0,0] * !![0,1;0,0] := by
  intro he
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) he
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hc

private theorem matrix_canonical_coefficient :
    let R := Matrix (Fin 2) (Fin 2) ℤ
    let A : R := !![0,1;0,0]
    simplicialSingletonH0Equiv R (0 : Fin 1)
      (((multivaluedSimplicialHomologyMap R (C := Function.graph (id : Fin 1 → Fin 1))
        (fun x => ⟨x,rfl⟩) ((isShiftedSimplicialRelation_graph_iff _).mpr singletonIdentity) 0).app 0).hom
          (vClass R (singletonFace (0 : Fin 1)) 0 rfl A)) = A :=
  canonical_singleton_coefficient (Matrix (Fin 2) (Fin 2) ℤ) !![0,1;0,0]

private theorem trivial_ring_canonical_coefficient :
    simplicialSingletonH0Equiv (ZMod 1) (0 : Fin 1)
      (((multivaluedSimplicialHomologyMap (ZMod 1) (C := Function.graph (id : Fin 1 → Fin 1))
        (fun x => ⟨x,rfl⟩) ((isShiftedSimplicialRelation_graph_iff _).mpr singletonIdentity) 0).app 0).hom
          (vClass (ZMod 1) (singletonFace (0 : Fin 1)) 0 rfl 0)) = 0 :=
  canonical_singleton_coefficient (ZMod 1) 0

end
end TDA.Persistence.SimplicialMultivaluedMapExamples
