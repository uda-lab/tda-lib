import TDA.Persistence.SimplicialMultivaluedInterleaving
import TDA.Simplicial.H0Augmentation
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Canonical interleavings, nonzero maps, round-trip obstruction and coefficient controls. -/

namespace TDA.Persistence.SimplicialMultivaluedInterleavingExamples

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

private theorem compSub {V W U : Type} {C : SetRel V W} {D : SetRel W U}
    {f : V → W} {g : W → U} (hf : Function.graph f ⊆ C) (hg : Function.graph g ⊆ D) :
    Function.graph (g ∘ f) ⊆ C.comp D := by
  intro ⟨x,z⟩ h
  change g (f x) = z at h
  subst z
  exact ⟨f x,hf rfl,hg rfl⟩

private theorem composite_image {V W U : Type} [LinearOrder V] [LinearOrder W] [LinearOrder U]
    (R : Type) [Ring R]
    {F : SimplicialFiltration ℝ V} {G : SimplicialFiltration ℝ W}
    {H : SimplicialFiltration ℝ U} {ε δ : ℝ} {C : SetRel V W} {D : SetRel W U}
    (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hDT : Relator.LeftTotal (fun y z => (y,z) ∈ D))
    (hC : IsShiftedSimplicialRelation F G ε C) (hD : IsShiftedSimplicialRelation G H δ D)
    {f : V → W} {g : W → U} (hf : Function.graph f ⊆ C) (hg : Function.graph g ⊆ D)
    (t : ℝ) (x : V) (hx : ({x} : Finset V) ∈ F t)
    (hy : ({g (f x)} : Finset U) ∈ H (t + (ε + δ))) (a : R) :
    ((multivaluedSimplicialHomologyMap R hCT hC 0 ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight ε))
        (multivaluedSimplicialHomologyMap R hDT hD 0) ≫
      (shiftedSimplicialHomologyCompIso R H ε δ 0).hom).app t).hom
      (vClass R (F t) x hx a) = vClass R (H (t + (ε + δ))) (g (f x)) hy a := by
  rw [multivaluedSimplicialHomologyMap_comp,
    multivaluedSimplicialHomologyMap_app R _ (hC.comp hD) (compSub hf hg)]
  exact vClass_map R _ x hx hy a


private theorem canonical_image {V W : Type} [LinearOrder V] [LinearOrder W]
    (R : Type) [Ring R] {F : SimplicialFiltration ℝ V} {G : SimplicialFiltration ℝ W}
    {a : ℝ} {C : SetRel V W} (hT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hC : IsShiftedSimplicialRelation F G a C) {f : V → W}
    (hf : Function.graph f ⊆ C) (t : ℝ) (x : V)
    (hx : ({x} : Finset V) ∈ F t) (hy : ({f x} : Finset W) ∈ G (t+a)) (r : R) :
    ((multivaluedSimplicialHomologyMap R hT hC 0).app t).hom (vClass R (F t) x hx r) =
      vClass R (G (t+a)) (f x) hy r := by
  rw [multivaluedSimplicialHomologyMap_app R hT hC hf]
  exact vClass_map R _ x hx hy r

private theorem transition_image {V : Type} [LinearOrder V] (R : Type) [Ring R]
    (F : SimplicialFiltration ℝ V) (γ : ℝ≥0) (t : ℝ) (x : V)
    (hx : ({x} : Finset V) ∈ F t) (hy : ({x} : Finset V) ∈ F (t+(γ:ℝ))) (r : R) :
    ((RealShift.transition γ (simplicialHomologyPModule R F 0)).app t).hom
      (vClass R (F t) x hx r) = vClass R (F (t+(γ:ℝ))) x hy r := by
  change (simplicialHomologyIncl R (F.monotone (le_add_of_nonneg_right γ.coe_nonneg)) 0).hom _ = _
  rw [← simplicialHomologyMap_inclusion]
  exact vClass_map R _ x hx hy r

private theorem zeroIso_image {V : Type} [LinearOrder V] (R : Type) [Ring R]
    (F : SimplicialFiltration ℝ V) (t : ℝ) (x : V)
    (hx : ({x} : Finset V) ∈ F (t+0)) (hy : ({x} : Finset V) ∈ F t) (r : R) :
    ((RealShift.zeroIso (simplicialHomologyPModule R F 0)).hom.app t).hom
      (vClass R (F (t+0)) x hx r) = vClass R (F t) x hy r := by
  change (simplicialHomologyIncl R (F.monotone (le_of_eq (add_zero t))) 0).hom _ = _
  rw [← simplicialHomologyMap_inclusion]
  exact vClass_map R _ x hx hy r

private abbrev pointK := (⊤ : PreAbstractSimplicialComplex (Fin 1))
private abbrev edgeK := (⊤ : PreAbstractSimplicialComplex (Fin 2))
private abbrev point0 := birth 0 pointK
private abbrev edge1 := birth 1 edgeK

/-! A genuinely multivalued birth-shifted correspondence has two nonzero maps and triangles. -/

private theorem bornForward : IsShiftedSimplicialRelation point0 edge1 1
    (Set.univ : SetRel (Fin 1) (Fin 2)) := by
  simpa using univBirth (W := Fin 2) 0 1 pointK

private theorem bornBackward : IsShiftedSimplicialRelation edge1 point0 1
    (Set.univ : SetRel (Fin 2) (Fin 1)) := by
  intro t σ hσ τ hτ _
  by_cases ht : 1 ≤ t
  · have hp : 0 ≤ t+1 := by linarith
    simpa [birth,hp] using hτ
  · simp [birth,ht] at hσ

private def bornI (R : Type) [Ring R] :=
  multivaluedSimplicialHomologyConverseInterleaving R (ε := (1 : ℝ≥0))
    (univTotal (V := Fin 1) (0 : Fin 2)) (univTotal (V := Fin 2) (0 : Fin 1))
    bornForward bornBackward 0

private theorem born_forward_image :
    ((bornI ℚ).φ.app 0).hom (vClass ℚ (point0 0) 0 (by norm_num [birth]) 1) =
      vClass ℚ (edge1 (0+1)) 0 (by norm_num [birth]) 1 := by
  exact canonical_image ℚ _ bornForward (subordinate_univ (fun _ : Fin 1 => (0 : Fin 2)))
    0 0 _ _ 1

private theorem born_backward_image :
    ((bornI ℚ).ψ.app 1).hom (vClass ℚ (edge1 1) 1 (by norm_num [birth]) 1) =
      vClass ℚ (point0 (1+1)) 0 (by norm_num [birth]) 1 := by
  exact canonical_image ℚ _ bornBackward (subordinate_univ (fun _ : Fin 2 => (0 : Fin 1)))
    1 1 _ _ 1

private theorem born_images_nonzero :
    ((bornI ℚ).φ.app 0).hom (vClass ℚ (point0 0) 0 (by norm_num [birth]) 1) ≠ 0 ∧
    ((bornI ℚ).ψ.app 1).hom (vClass ℚ (edge1 1) 1 (by norm_num [birth]) 1) ≠ 0 := by
  rw [born_forward_image,born_backward_image]
  exact ⟨vClass_nonzero _ _ _,vClass_nonzero _ _ _⟩

private theorem born_triangles :
    ((((bornI ℚ).φ ≫ (RealShift.shift 1).map (bornI ℚ).ψ ≫
      (RealShift.compIso 1 1 (simplicialHomologyPModule ℚ point0 0)).hom).app 0).hom
        (vClass ℚ (point0 0) 0 (by norm_num [birth]) 1)) =
      vClass ℚ (point0 (0+((1+1:ℝ≥0):ℝ))) 0 (by norm_num [birth]) 1 ∧
    ((((bornI ℚ).ψ ≫ (RealShift.shift 1).map (bornI ℚ).φ ≫
      (RealShift.compIso 1 1 (simplicialHomologyPModule ℚ edge1 0)).hom).app 1).hom
        (vClass ℚ (edge1 1) 1 (by norm_num [birth]) 1)) =
      vClass ℚ (edge1 (1+((1+1:ℝ≥0):ℝ))) 1 (by norm_num [birth]) 1 := by
  rw [(bornI ℚ).φ_ψ,(bornI ℚ).ψ_φ]
  exact ⟨transition_image ℚ point0 (1+1) 0 0 _ _ 1,
    transition_image ℚ edge1 (1+1) 1 1 _ _ 1⟩

private theorem born_selector_comparison :
    (bornI ℚ).φ = shiftedSimplicialHomologyMap ℚ
      (bornForward.of_subordinate (subordinate_univ (fun _ : Fin 1 => (0 : Fin 2)))) 0 ∧
    (bornI ℚ).φ = shiftedSimplicialHomologyMap ℚ
      (bornForward.of_subordinate (subordinate_univ (fun _ : Fin 1 => (1 : Fin 2)))) 0 := by
  constructor <;> exact multivaluedSimplicialHomologyMap_eq ℚ
    (univTotal (V := Fin 1) (0 : Fin 2)) bornForward (subordinate_univ _) 0

private theorem born_selectors_distinct :
    (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ : Fin 1 => (1 : Fin 2)) := by
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (congrFun h 0)

/-! Subrelations retain maps at negative degrees; a missing birth cannot be ignored. -/

private abbrev point2 := birth 2 pointK
private theorem negativeRelation : IsShiftedSimplicialRelation point2 edge1 (-1)
    (Set.univ : SetRel (Fin 1) (Fin 2)) := by
  simpa only [show (1 : ℝ)-2 = -1 by norm_num] using univBirth (W := Fin 2) 2 1 pointK

private abbrev endpointGraph : SetRel (Fin 1) (Fin 2) := Function.graph (fun _ => 0)
private theorem endpoint_total : Relator.LeftTotal (fun x y => (x,y) ∈ endpointGraph) :=
  fun _ => ⟨0,rfl⟩
private theorem endpoint_sub : endpointGraph ⊆ Set.univ := Set.subset_univ _

private theorem endpoint_proper : endpointGraph ≠ Set.univ := by
  intro h
  have hh : ((0 : Fin 1),(1 : Fin 2)) ∈ endpointGraph := by rw [h]; trivial
  exact (by decide : (0 : Fin 2) ≠ 1) hh

private theorem negative_subrelation_equality :
    multivaluedSimplicialHomologyMap ℚ endpoint_total (negativeRelation.of_subset endpoint_sub) 0 =
      multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 1) (0 : Fin 2)) negativeRelation 0 :=
  multivaluedSimplicialHomologyMap_of_subset ℚ _ _ negativeRelation endpoint_sub 0

private theorem negative_subrelation_nonzero :
    ((multivaluedSimplicialHomologyMap ℚ endpoint_total
      (negativeRelation.of_subset endpoint_sub) 0).app 2).hom
        (vClass ℚ (point2 2) 0 (by norm_num [birth]) 1) ≠ 0 := by
  rw [canonical_image ℚ endpoint_total (negativeRelation.of_subset endpoint_sub)
    (f := fun _ => 0) (Set.Subset.refl _) 2 0 _ (by norm_num [birth]) 1]
  exact vClass_nonzero _ _ _

private theorem missing_birth_degree_zero :
    ¬IsShiftedSimplicialRelation point0 edge1 0 (Set.univ : SetRel (Fin 1) (Fin 2)) := by
  intro h
  have hh := h 0 {0} (by norm_num [birth]) {0} (by simp)
    (by intro y _; exact ⟨0,by simp,trivial⟩)
  norm_num [birth] at hh

/-! Two individually simplicial total maps can fail one round-trip triangle. -/

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


private abbrev isolatedF := constF isolatedK
private abbrev pointF := constF pointK
private def collapse : Fin 2 → Fin 1 := fun _ => 0
private def chooseZero : Fin 1 → Fin 2 := fun _ => 0
private abbrev collapseC := Function.graph collapse
private abbrev chooseD := Function.graph chooseZero
private theorem collapseTotal : Relator.LeftTotal (fun x y => (x,y) ∈ collapseC) :=
  fun x => ⟨collapse x,rfl⟩
private theorem chooseTotal : Relator.LeftTotal (fun x y => (x,y) ∈ chooseD) :=
  fun x => ⟨chooseZero x,rfl⟩

private theorem collapseGeometry : IsShiftedSimplicialRelation isolatedF pointF 0 collapseC := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  apply (isShiftedSimplicialRelation_graph_iff collapse).mpr
  intro t σ hσ
  change (σ.image collapse).Nonempty
  exact Finset.image_nonempty.mpr hσ.1

private theorem chooseGeometry : IsShiftedSimplicialRelation pointF isolatedF 0 chooseD := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  apply (isShiftedSimplicialRelation_graph_iff chooseZero).mpr
  intro t σ hσ
  change σ.Nonempty at hσ
  change σ.image chooseZero ∈ isolatedK
  have he : σ.image chooseZero = {0} := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hx
      exact Finset.mem_singleton.mpr hy.symm
    · intro hx
      obtain ⟨y,hy⟩ := hσ
      exact Finset.mem_image.mpr ⟨y,hy,(Finset.mem_singleton.mp hx).symm⟩
  rw [he]
  exact isolated_vertex 0

private theorem point_roundTrip_contains_identity : SetRel.id ⊆ chooseD.comp collapseC := by
  rintro ⟨x,x'⟩ rfl
  exact ⟨0,rfl,Subsingleton.elim _ _⟩

private theorem isolated_roundTrip_missing_identity :
    ¬SetRel.id ⊆ collapseC.comp chooseD := by
  intro h
  obtain ⟨y,_,hy⟩ := h (show ((1 : Fin 2),(1 : Fin 2)) ∈ SetRel.id from rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) hy

private def badComposite :=
  multivaluedSimplicialHomologyMapNNReal ℚ (δ := (0 : ℝ≥0)) collapseTotal collapseGeometry 0 ≫
    (RealShift.shift 0).map
      (multivaluedSimplicialHomologyMapNNReal ℚ (δ := (0 : ℝ≥0)) chooseTotal chooseGeometry 0) ≫
    (RealShift.compIso 0 0 (simplicialHomologyPModule ℚ isolatedF 0)).hom

private theorem bad_roundTrip_image :
    (badComposite.app 0).hom (vClass ℚ isolatedK 1 (isolated_vertex 1) 1) =
      vClass ℚ isolatedK 0 (isolated_vertex 0) 1 := by
  exact composite_image ℚ collapseTotal chooseTotal collapseGeometry chooseGeometry
    (f := collapse) (g := chooseZero) (Set.Subset.refl _) (Set.Subset.refl _)
    0 1 (isolated_vertex 1) (isolated_vertex 0) 1

private theorem bad_triangle_fails :
    badComposite ≠ RealShift.transition (0+0) (simplicialHomologyPModule ℚ isolatedF 0) := by
  intro he
  have hc := congrArg (fun m => (m.app 0).hom
    (vClass ℚ isolatedK 1 (isolated_vertex 1) 1)) he
  rw [bad_roundTrip_image] at hc
  exact isolated_classes_differ (hc.trans (transition_image ℚ isolatedF (0+0) 0 1
    (isolated_vertex 1) (isolated_vertex 1) 1))

/-! Infinite relational images still yield zero-interleavings and an isomorphism. -/

private abbrev naturalF := constF (⊤ : PreAbstractSimplicialComplex ℕ)
private theorem infiniteForward : IsShiftedSimplicialRelation pointF naturalF 0 Set.univ :=
  fullRelation pointK
private theorem infiniteBackward : IsShiftedSimplicialRelation naturalF pointF 0 Set.univ :=
  fullRelation _
private def infiniteI (R : Type) [Ring R] :=
  multivaluedSimplicialHomologyConverseInterleaving R (ε := (0 : ℝ≥0))
    (univTotal (V := Fin 1) (0 : ℕ)) (univTotal (V := ℕ) (0 : Fin 1))
    infiniteForward infiniteBackward 0

private theorem infinite_image :
    (SetRel.image (Set.univ : SetRel (Fin 1) ℕ) ({0} : Set (Fin 1))).Infinite := by
  have h : SetRel.image (Set.univ : SetRel (Fin 1) ℕ) ({0} : Set (Fin 1)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _; exact ⟨0,by simp,trivial⟩
  rw [h]
  exact Set.infinite_univ

private theorem infinite_forward_image :
    ((infiniteI ℚ).φ.app 0).hom (vClass ℚ pointK 0 (by simp) 1) =
      vClass ℚ (⊤ : PreAbstractSimplicialComplex ℕ) 0 (by simp) 1 :=
  canonical_image ℚ _ infiniteForward (subordinate_univ (fun _ : Fin 1 => (0 : ℕ)))
    0 0 (by simp [constF]) (by simp [constF]) 1

private theorem infinite_forward_nonzero :
    ((infiniteI ℚ).φ.app 0).hom (vClass ℚ pointK 0 (by simp) 1) ≠ 0 := by
  rw [infinite_forward_image]
  exact vClass_nonzero _ _ _

private theorem infinite_isomorphism_nonzero :
    (((RealInterleaving.toIso (infiniteI ℚ)).hom.app 0).hom
      (vClass ℚ pointK 0 (by simp) 1)) ≠ 0 := by
  have he : (((RealInterleaving.toIso (infiniteI ℚ)).hom.app 0).hom
      (vClass ℚ pointK 0 (by simp) 1)) =
      vClass ℚ (⊤ : PreAbstractSimplicialComplex ℕ) 0 (by simp) 1 := by
    change ((RealShift.zeroIso (simplicialHomologyPModule ℚ naturalF 0)).hom.app 0).hom
      (((infiniteI ℚ).φ.app 0).hom (vClass ℚ pointK 0 (by simp) 1)) = _
    rw [infinite_forward_image]
    exact zeroIso_image ℚ naturalF 0 0 (by simp [constF]) (by simp [constF]) 1
  rw [he]
  exact vClass_nonzero _ _ _

private theorem infinite_roundTrip_nonzero :
    ((((infiniteI ℚ).φ ≫ (RealShift.shift 0).map (infiniteI ℚ).ψ ≫
      (RealShift.compIso 0 0 (simplicialHomologyPModule ℚ pointF 0)).hom).app 0).hom
        (vClass ℚ pointK 0 (by simp) 1)) ≠ 0 := by
  rw [(infiniteI ℚ).φ_ψ]
  have he := transition_image ℚ pointF (0+0) 0 0 (by simp [constF]) (by simp [constF]) 1
  intro hz
  exact vClass_nonzero pointK 0 (by simp) (he.symm.trans hz)

/-! Ambient ghost pairs are retained without adding ghost singleton faces. -/

private def supported {V : Type} [DecidableEq V] (s : Finset V) :
    PreAbstractSimplicialComplex V where
  faces := {σ | σ.Nonempty ∧ σ ⊆ s}
  isRelLowerSet_faces := by
    intro σ hσ
    exact ⟨hσ.1,fun τ hτσ hτ => ⟨hτ,hτσ.trans hσ.2⟩⟩

private abbrev ghostSource := supported ({0} : Finset (Fin 2))
private abbrev ghostTarget := supported ({0,1} : Finset (Fin 3))
private def ghostRelation : SetRel (Fin 2) (Fin 3) :=
  {p | (p.1=0 ∧ (p.2=0 ∨ p.2=1)) ∨ (p.1=1 ∧ p.2=2)}

private theorem ghostTotal : Relator.LeftTotal (fun x y => (x,y) ∈ ghostRelation) := by
  intro x
  fin_cases x
  · exact ⟨0,by simp [ghostRelation]⟩
  · exact ⟨2,by simp [ghostRelation]⟩

private theorem ghostInvTotal : Relator.LeftTotal (fun y x => (y,x) ∈ ghostRelation.inv) := by
  intro y
  fin_cases y
  · exact ⟨0,by simp [ghostRelation]⟩
  · exact ⟨0,by simp [ghostRelation]⟩
  · exact ⟨1,by simp [ghostRelation]⟩

private theorem ghostGeometry : IsShiftedSimplicialRelation
    (constF ghostSource) (constF ghostTarget) 0 ghostRelation := by
  intro t σ hσ τ hτ hsub
  change σ.Nonempty ∧ σ ⊆ {0} at hσ
  change τ.Nonempty ∧ τ ⊆ {0,1}
  refine ⟨hτ,?_⟩
  intro y hy
  obtain ⟨x,hx,hxy⟩ := hsub hy
  have hxs : x=0 := Finset.mem_singleton.mp (hσ.2 hx)
  rcases hxy with ⟨_,hy0|hy1⟩ | ⟨hx1,_⟩
  · apply Finset.mem_insert.mpr
    exact Or.inl hy0
  · apply Finset.mem_insert.mpr
    exact Or.inr (Finset.mem_singleton.mpr hy1)
  · exact False.elim ((by decide : (0 : Fin 2) ≠ 1) (hxs.symm.trans hx1))

private theorem ghostInvGeometry : IsShiftedSimplicialRelation
    (constF ghostTarget) (constF ghostSource) 0 ghostRelation.inv := by
  intro t σ hσ τ hτ hsub
  change σ.Nonempty ∧ σ ⊆ {0,1} at hσ
  change τ.Nonempty ∧ τ ⊆ {0}
  refine ⟨hτ,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := hsub hx
  change (x=0 ∧ (y=0 ∨ y=1)) ∨ (x=1 ∧ y=2) at hxy
  rcases hxy with ⟨hx0,_⟩ | ⟨_,hy2⟩
  · exact Finset.mem_singleton.mpr hx0
  · have hn : (2 : Fin 3) ∉ ({0,1} : Finset (Fin 3)) := by decide
    exact False.elim (hn (hy2 ▸ hσ.2 hy))

private def ghostI (R : Type) [Ring R] :=
  multivaluedSimplicialHomologyConverseInterleaving R (ε := (0 : ℝ≥0)) ghostTotal ghostInvTotal
    ghostGeometry ghostInvGeometry 0

private theorem ghost_support :
    ((1 : Fin 2),(2 : Fin 3)) ∈ ghostRelation ∧
    ({(1 : Fin 2)} : Finset (Fin 2)) ∉ ghostSource ∧
    ({(2 : Fin 3)} : Finset (Fin 3)) ∉ ghostTarget := by
  refine ⟨Or.inr ⟨rfl,rfl⟩,?_,?_⟩
  · change ¬(({1} : Finset (Fin 2)).Nonempty ∧ ({1} : Finset (Fin 2)) ⊆ {0})
    decide
  · change ¬(({2} : Finset (Fin 3)).Nonempty ∧ ({2} : Finset (Fin 3)) ⊆ {0,1})
    decide

private theorem ghost_source_vertex : ({(0 : Fin 2)} : Finset (Fin 2)) ∈ ghostSource := by
  change ({0} : Finset (Fin 2)).Nonempty ∧ ({0} : Finset (Fin 2)) ⊆ {0}
  decide
private theorem ghost_target_vertex : ({(0 : Fin 3)} : Finset (Fin 3)) ∈ ghostTarget := by
  change ({0} : Finset (Fin 3)).Nonempty ∧ ({0} : Finset (Fin 3)) ⊆ {0,1}
  decide

private def ghostSelector (x : Fin 2) : Fin 3 := if x=0 then 0 else 2
private theorem ghostSelector_subordinate : Function.graph ghostSelector ⊆ ghostRelation := by
  rintro ⟨x,y⟩ hxy
  change ghostSelector x=y at hxy
  subst y
  fin_cases x <;> norm_num [ghostSelector,ghostRelation]

private theorem ghost_active_image_nonzero :
    ((ghostI ℚ).φ.app 0).hom
      (vClass ℚ ghostSource 0 ghost_source_vertex 1) ≠ 0 := by
  have he := canonical_image ℚ ghostTotal ghostGeometry ghostSelector_subordinate 0 0
    ghost_source_vertex ghost_target_vertex 1
  intro hz
  exact vClass_nonzero ghostTarget 0 ghost_target_vertex (he.symm.trans hz)

private theorem emptyTotal :
    Relator.LeftTotal (fun x y => (x,y) ∈ (∅ : SetRel (Fin 0) (Fin 0))) := by
  intro x
  exact Fin.elim0 x

private theorem emptyGeometry (ε : ℝ≥0) : IsShiftedSimplicialRelation
    (constF (⊥ : PreAbstractSimplicialComplex (Fin 0))) (constF ⊥) (ε : ℝ)
    (∅ : SetRel (Fin 0) (Fin 0)) := by
  intro t σ hσ
  simp [constF] at hσ

private def emptyI (R : Type) [Ring R] (ε : ℝ≥0) (n : ℕ) :=
  multivaluedSimplicialHomologyConverseInterleaving R (ε := ε) emptyTotal emptyTotal
    (emptyGeometry ε) (emptyGeometry ε) n

private theorem empty_target_control (C : SetRel (Fin 1) (Fin 0)) :
    IsShiftedSimplicialRelation (constF (⊥ : PreAbstractSimplicialComplex (Fin 1)))
      (constF (⊥ : PreAbstractSimplicialComplex (Fin 0))) 0 C ∧
    ¬Relator.LeftTotal (fun x y => (x,y) ∈ C) := by
  constructor
  · intro t σ hσ
    simp [constF] at hσ
  · intro h
    obtain ⟨y,_⟩ := h 0
    exact Fin.elim0 y

/-! Fields and triangles retain a noncentral matrix coefficient, and allow the zero ring. -/

private abbrev singletonF := constF (singletonFace (0 : Fin 1))
private theorem singletonTotal :
    Relator.LeftTotal (fun x y => (x,y) ∈ (SetRel.id : SetRel (Fin 1) (Fin 1))) :=
  fun x => ⟨x,rfl⟩
private theorem singletonRelation : IsShiftedSimplicialRelation singletonF singletonF 1
    (SetRel.id : SetRel (Fin 1) (Fin 1)) := by
  apply (isShiftedSimplicialRelation_graph_iff id).mpr
  intro t σ hσ
  exact (inclusionVertexMap (show singletonF t ≤ singletonF (t+1) from le_rfl)).map_face σ hσ
private theorem singletonRoundTrip :
    SetRel.id ⊆ (SetRel.id : SetRel (Fin 1) (Fin 1)).comp SetRel.id := by
  rintro ⟨x,y⟩ rfl
  exact ⟨x,rfl,rfl⟩
private def coefficientI (R : Type) [Ring R] :=
  multivaluedSimplicialHomologyInterleaving R (ε := (1 : ℝ≥0)) singletonTotal singletonTotal
    singletonRelation singletonRelation singletonRoundTrip singletonRoundTrip 0

private theorem coefficient_fields (R : Type) [Ring R] (a : R) :
    simplicialSingletonH0Equiv R (0 : Fin 1)
      (((coefficientI R).φ.app 0).hom (vClass R (singletonFace (0 : Fin 1)) 0 rfl a)) = a ∧
    simplicialSingletonH0Equiv R (0 : Fin 1)
      (((coefficientI R).ψ.app 0).hom (vClass R (singletonFace (0 : Fin 1)) 0 rfl a)) = a := by
  have he := canonical_image R singletonTotal singletonRelation (f := id) (Set.Subset.refl _)
    0 0 rfl rfl a
  constructor
  · calc
      _ = simplicialSingletonH0Equiv R 0 (vClass R (singletonFace (0 : Fin 1)) 0 rfl a) :=
        congrArg (simplicialSingletonH0Equiv R (0 : Fin 1)) he
      _ = a := simplicialSingletonH0Equiv_class R (0 : Fin 1) a
  · calc
      _ = simplicialSingletonH0Equiv R 0 (vClass R (singletonFace (0 : Fin 1)) 0 rfl a) :=
        congrArg (simplicialSingletonH0Equiv R (0 : Fin 1)) he
      _ = a := simplicialSingletonH0Equiv_class R (0 : Fin 1) a

private theorem coefficient_triangles (R : Type) [Ring R] (a : R) :
    simplicialSingletonH0Equiv R (0 : Fin 1)
      ((((coefficientI R).φ ≫ (RealShift.shift 1).map (coefficientI R).ψ ≫
        (RealShift.compIso 1 1 (simplicialHomologyPModule R singletonF 0)).hom).app 0).hom
          (vClass R (singletonFace (0 : Fin 1)) 0 rfl a)) = a ∧
    simplicialSingletonH0Equiv R (0 : Fin 1)
      ((((coefficientI R).ψ ≫ (RealShift.shift 1).map (coefficientI R).φ ≫
        (RealShift.compIso 1 1 (simplicialHomologyPModule R singletonF 0)).hom).app 0).hom
          (vClass R (singletonFace (0 : Fin 1)) 0 rfl a)) = a := by
  constructor
  · rw [(coefficientI R).φ_ψ]
    exact (congrArg (simplicialSingletonH0Equiv R (0 : Fin 1))
      (transition_image R singletonF (1+1) 0 0 rfl rfl a)).trans
      (simplicialSingletonH0Equiv_class R (0 : Fin 1) a)
  · rw [(coefficientI R).ψ_φ]
    exact (congrArg (simplicialSingletonH0Equiv R (0 : Fin 1))
      (transition_image R singletonF (1+1) 0 0 rfl rfl a)).trans
      (simplicialSingletonH0Equiv_class R (0 : Fin 1) a)

private theorem matrix_noncentral :
    (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,0;0,0] ≠
      !![1,0;0,0] * !![0,1;0,0] := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  norm_num [Matrix.mul_apply,Fin.sum_univ_two] at hh

private theorem matrix_fields_and_triangles :
    let R := Matrix (Fin 2) (Fin 2) ℤ
    let A : R := !![0,1;0,0]
    (simplicialSingletonH0Equiv R (0 : Fin 1)
      (((coefficientI R).φ.app 0).hom (vClass R (singletonFace (0 : Fin 1)) 0 rfl A)) = A ∧
    simplicialSingletonH0Equiv R (0 : Fin 1)
      (((coefficientI R).ψ.app 0).hom (vClass R (singletonFace (0 : Fin 1)) 0 rfl A)) = A) ∧
    (simplicialSingletonH0Equiv R (0 : Fin 1)
      ((((coefficientI R).φ ≫ (RealShift.shift 1).map (coefficientI R).ψ ≫
        (RealShift.compIso 1 1 (simplicialHomologyPModule R singletonF 0)).hom).app 0).hom
          (vClass R (singletonFace (0 : Fin 1)) 0 rfl A)) = A ∧
    simplicialSingletonH0Equiv R (0 : Fin 1)
      ((((coefficientI R).ψ ≫ (RealShift.shift 1).map (coefficientI R).φ ≫
        (RealShift.compIso 1 1 (simplicialHomologyPModule R singletonF 0)).hom).app 0).hom
          (vClass R (singletonFace (0 : Fin 1)) 0 rfl A)) = A) :=
  ⟨coefficient_fields _ _,coefficient_triangles _ _⟩

private theorem trivial_ring_fields_and_triangles :
    let R := ZMod 1
    (simplicialSingletonH0Equiv R (0 : Fin 1)
      (((coefficientI R).φ.app 0).hom (vClass R (singletonFace (0 : Fin 1)) 0 rfl 0)) = 0 ∧
    simplicialSingletonH0Equiv R (0 : Fin 1)
      (((coefficientI R).ψ.app 0).hom (vClass R (singletonFace (0 : Fin 1)) 0 rfl 0)) = 0) ∧
    (simplicialSingletonH0Equiv R (0 : Fin 1)
      ((((coefficientI R).φ ≫ (RealShift.shift 1).map (coefficientI R).ψ ≫
        (RealShift.compIso 1 1 (simplicialHomologyPModule R singletonF 0)).hom).app 0).hom
          (vClass R (singletonFace (0 : Fin 1)) 0 rfl 0)) = 0 ∧
    simplicialSingletonH0Equiv R (0 : Fin 1)
      ((((coefficientI R).ψ ≫ (RealShift.shift 1).map (coefficientI R).φ ≫
        (RealShift.compIso 1 1 (simplicialHomologyPModule R singletonF 0)).hom).app 0).hom
          (vClass R (singletonFace (0 : Fin 1)) 0 rfl 0)) = 0) :=
  ⟨coefficient_fields _ _,coefficient_triangles _ _⟩

end
end TDA.Persistence.SimplicialMultivaluedInterleavingExamples
