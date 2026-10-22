import TDA.Persistence.RipsRelationInterleaving
import TDA.Simplicial.H0Augmentation
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Rips relation maps, finite diagrams, quantitative obstructions and coefficient controls. -/

namespace TDA.Persistence.RipsRelationInterleavingExamples

open CategoryTheory TDA.Filtration TDA.Simplicial
open scoped Matrix NNReal ENNReal

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

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

private abbrev discreteMetric (V : Type) (c : ℝ) (hc : 0 < c) : MetricSpace V where
  dist x y := @ite ℝ (x = y) (Classical.propDecidable _) 0 c
  dist_self _ := if_pos rfl
  dist_comm x y := by
    classical
    by_cases hxy : x = y
    · subst y; rfl
    · rw [if_neg hxy, if_neg (Ne.symm hxy)]
  dist_triangle x y z := by
    classical
    by_cases hxy : x = y
    · subst y; simp
    · by_cases hyz : y = z
      · subst z; simp
      · simp only [if_neg hxy, if_neg hyz]
        split_ifs <;> linarith
  eq_of_dist_eq_zero := by
    intro x y h
    by_contra hxy
    simp only [if_neg hxy] at h
    exact hc.ne' h

@[simp] private theorem discrete_dist (V : Type) (c : ℝ) (hc : 0 < c) (x y : V) :
    (discreteMetric V c hc).dist x y = @ite ℝ (x = y) (Classical.propDecidable _) 0 c := rfl

private abbrev rf {V : Type} (d : MetricSpace V) := (Rips.filter d).sublevelFiltration

private theorem rv {V : Type} (d : MetricSpace V) (t : ℝ) (x : V) (ht : 0 ≤ t) :
    ({x} : Finset V) ∈ rf d t := by
  apply (Rips.mem_sublevel_iff d t _).mpr
  exact ⟨by simp, by simpa only [Finset.mem_singleton, forall_eq, d.dist_self] using ht⟩

private abbrev rc {V : Type} [LinearOrder V] (R : Type) [Ring R]
    (d : MetricSpace V) (t : ℝ) (x : V) (ht : 0 ≤ t) (a : R) :=
  vClass R (rf d t) x (rv d t x ht) a

private theorem discrete_no_edges {V : Type} (c : ℝ) (hc : 0 < c)
    (t : ℝ) (ht : t < c) : IsEmpty (Face (rf (discreteMetric V c hc) t) 1) := ⟨by
  classical
  intro σ
  have hcard := σ.2.2
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < σ.1.card)
  have h := ((Rips.mem_sublevel_iff _ _ _).mp σ.2.1).2 x hx y hy
  change (if x = y then 0 else c) ≤ t at h
  rw [if_neg hxy] at h
  exact (not_le.mpr ht) h⟩

private theorem classes_differ {V : Type} [LinearOrder V]
    (K : PreAbstractSimplicialComplex V) [IsEmpty (Face K 1)] (x y : V)
    (hxy : x ≠ y) (hx : ({x} : Finset V) ∈ K) (hy : ({y} : Finset V) ∈ K) :
    vClass ℚ K x hx 1 ≠ vClass ℚ K y hy 1 := by
  intro hc
  have hq := congrArg (homologyKernelQuotient ℚ (simplicialChainComplex K ℚ) 0).hom.hom hc
  unfold vClass at hq
  rw [simplicialHomologyClass_quotient, simplicialHomologyClass_quotient] at hq
  obtain ⟨c,hc⟩ := (mem_simplicialBoundaries_iff ℚ K 0 _).mp ((Submodule.Quotient.eq _).mp hq)
  have hz : c = 0 := by
    ext σ
    exact isEmptyElim σ
  rw [hz,map_zero] at hc
  have hv : vertex K y hy ≠ vertex K x hx := by
    intro he
    exact hxy (Finset.singleton_injective (congrArg Subtype.val he).symm)
  have hh := congrArg (fun c : Chain K ℚ 0 => c (vertex K x hx)) hc
  simp [vCycle, hv] at hh

private theorem forward_image {V W : Type} [LinearOrder V] [LinearOrder W]
    (R : Type) [Ring R] (dV : MetricSpace V) (dW : MetricSpace W)
    {C : SetRel V W} {ε : ℝ≥0}
    (hT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hI : Relator.LeftTotal (fun y x => (y,x) ∈ C.inv))
    (h : ∀ x x' y y', (x,y) ∈ C → (x',y') ∈ C →
      |dV.dist x x' - dW.dist y y'| ≤ (ε : ℝ))
    {f : V → W} (hf : Function.graph f ⊆ C) (t : ℝ) (x : V)
    (ht : 0 ≤ t) (hs : 0 ≤ t+(ε:ℝ)) (a : R) :
    (((Rips.relationInterleaving R dV dW hT hI h 0).φ).app t).hom
      (rc R dV t x ht a) = rc R dW (t+(ε:ℝ)) (f x) hs a :=
  canonical_image R hT (Rips.isShiftedSimplicialRelation_of_distortion dV dW h) hf
    t x (rv dV t x ht) (rv dW _ _ hs) a

private theorem backward_image {V W : Type} [LinearOrder V] [LinearOrder W]
    (R : Type) [Ring R] (dV : MetricSpace V) (dW : MetricSpace W)
    {C : SetRel V W} {ε : ℝ≥0}
    (hT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hI : Relator.LeftTotal (fun y x => (y,x) ∈ C.inv))
    (h : ∀ x x' y y', (x,y) ∈ C → (x',y') ∈ C →
      |dV.dist x x' - dW.dist y y'| ≤ (ε : ℝ))
    {g : W → V} (hg : Function.graph g ⊆ C.inv) (t : ℝ) (y : W)
    (ht : 0 ≤ t) (hs : 0 ≤ t+(ε:ℝ)) (a : R) :
    (((Rips.relationInterleaving R dV dW hT hI h 0).ψ).app t).hom
      (rc R dW t y ht a) = rc R dV (t+(ε:ℝ)) (g y) hs a := by
  exact canonical_image R hI
    (Rips.isShiftedSimplicialRelation_of_distortion dW dV (by
      intro y y' x x' hy hy'
      simpa only [abs_sub_comm] using h x x' y y' hy hy'))
    hg t y (rv dW t y ht) (rv dV _ _ hs) a

/-! Distances two and three on different two-point label types. -/

private abbrev dTwo : MetricSpace (Fin 2) := discreteMetric (Fin 2) 2 (by norm_num)
private abbrev dThree : MetricSpace Bool := discreteMetric Bool 3 (by norm_num)
private abbrev pairC : SetRel (Fin 2) Bool := Function.graph finTwoEquiv
private theorem pairTotal : Relator.LeftTotal (fun x y => (x,y) ∈ pairC) :=
  fun x => ⟨finTwoEquiv x,rfl⟩
private theorem pairInvTotal : Relator.LeftTotal (fun y x => (y,x) ∈ pairC.inv) :=
  fun y => ⟨finTwoEquiv.symm y,finTwoEquiv.apply_symm_apply y⟩
private theorem pairInvGraph : Function.graph finTwoEquiv.symm ⊆ pairC.inv := by
  rintro ⟨y,x⟩ rfl
  exact finTwoEquiv.apply_symm_apply y
private theorem pairBound : ∀ x x' y y', (x,y) ∈ pairC → (x',y') ∈ pairC →
    |dTwo.dist x x' - dThree.dist y y'| ≤ ((1:ℝ≥0):ℝ) := by
  rintro x x' y y' rfl rfl
  by_cases hx : x = x'
  · subst x'; simp [dTwo,dThree,discreteMetric]
  · have hy : finTwoEquiv x ≠ finTwoEquiv x' := fun he => hx (finTwoEquiv.injective he)
    norm_num [dTwo,dThree,discreteMetric,hx,hy]
private def pairI := Rips.relationInterleaving ℚ dTwo dThree pairTotal pairInvTotal pairBound 0

private theorem edge_thresholds :
    Rips.diameter dTwo {0,1} = 2 ∧ Rips.diameter dThree {false,true} = 3 := by
  constructor <;> rw [Rips.diameter_pair] <;> norm_num [dTwo,dThree,discreteMetric]

private theorem pair_fields :
    ((pairI.φ.app 0).hom (rc ℚ dTwo 0 0 (by norm_num) 1) =
      rc ℚ dThree (0+((1:ℝ≥0):ℝ)) false (by norm_num) 1) ∧
    ((pairI.ψ.app 0).hom (rc ℚ dThree 0 true (by norm_num) 1) =
      rc ℚ dTwo (0+((1:ℝ≥0):ℝ)) 1 (by norm_num) 1) := by
  constructor
  · exact forward_image ℚ dTwo dThree pairTotal pairInvTotal pairBound
      (Set.Subset.refl _) 0 0 (by norm_num) (by norm_num) 1
  · exact backward_image ℚ dTwo dThree pairTotal pairInvTotal pairBound
      pairInvGraph 0 true (by norm_num) (by norm_num) 1

private theorem pair_images_nonzero :
    (pairI.φ.app 0).hom (rc ℚ dTwo 0 0 (by norm_num) 1) ≠ 0 ∧
    (pairI.ψ.app 0).hom (rc ℚ dThree 0 true (by norm_num) 1) ≠ 0 := by
  rw [pair_fields.1,pair_fields.2]
  exact ⟨vClass_nonzero _ _ _,vClass_nonzero _ _ _⟩

private theorem pair_difference_survives :
    (pairI.φ.app 0).hom
      (rc ℚ dTwo 0 0 (by norm_num) 1 - rc ℚ dTwo 0 1 (by norm_num) 1) =
        rc ℚ dThree (0+((1:ℝ≥0):ℝ)) false (by norm_num) 1 - rc ℚ dThree (0+((1:ℝ≥0):ℝ)) true (by norm_num) 1 ∧
    (pairI.φ.app 0).hom
      (rc ℚ dTwo 0 0 (by norm_num) 1 - rc ℚ dTwo 0 1 (by norm_num) 1) ≠ 0 := by
  have he : (pairI.φ.app 0).hom
      (rc ℚ dTwo 0 0 (by norm_num) 1 - rc ℚ dTwo 0 1 (by norm_num) 1) =
        rc ℚ dThree (0+((1:ℝ≥0):ℝ)) false (by norm_num) 1 - rc ℚ dThree (0+((1:ℝ≥0):ℝ)) true (by norm_num) 1 := by
    rw [map_sub,pair_fields.1]
    congr 1
    exact forward_image ℚ dTwo dThree pairTotal pairInvTotal pairBound
      (Set.Subset.refl _) 0 1 (by norm_num) (by norm_num) 1
  refine ⟨he, ?_⟩
  rw [he,sub_ne_zero]
  letI := discrete_no_edges (V := Bool) 3 (by norm_num) (0+((1:ℝ≥0):ℝ)) (by norm_num)
  exact classes_differ _ false true Bool.false_ne_true _ _

private theorem pair_triangles :
    ((((pairI.φ ≫ (RealShift.shift 1).map pairI.ψ ≫
      (RealShift.compIso 1 1 (sublevelModule ℚ (Rips.filter dTwo) 0)).hom).app 0).hom
        (rc ℚ dTwo 0 0 (by norm_num) 1)) = rc ℚ dTwo (0+((1+1:ℝ≥0):ℝ)) 0 (by norm_num) 1) ∧
    ((((pairI.ψ ≫ (RealShift.shift 1).map pairI.φ ≫
      (RealShift.compIso 1 1 (sublevelModule ℚ (Rips.filter dThree) 0)).hom).app 0).hom
        (rc ℚ dThree 0 true (by norm_num) 1)) = rc ℚ dThree (0+((1+1:ℝ≥0):ℝ)) true (by norm_num) 1) := by
  constructor
  · rw [pairI.φ_ψ]
    exact transition_image ℚ (rf dTwo) (1+1) 0 0 _ _ 1
  · rw [pairI.ψ_φ]
    exact transition_image ℚ (rf dThree) (1+1) 0 true _ _ 1

private theorem pair_diagrams (n : ℕ) :
    bottleneck (dgm ℚ (Rips.filter dTwo) n) (dgm ℚ (Rips.filter dThree) n) ≤ 1 :=
  Rips.bottleneck_dgm_le_of_relation dTwo dThree pairTotal pairInvTotal pairBound ℚ n

/-! A genuinely multivalued singleton fiber and a collapsing difference class. -/

private abbrev dPoint : MetricSpace (Fin 1) := discreteMetric (Fin 1) 1 (by norm_num)
private abbrev multiC : SetRel (Fin 1) (Fin 2) := Set.univ
private theorem multiTotal : Relator.LeftTotal (fun x y => (x,y) ∈ multiC) :=
  fun _ => ⟨0,Set.mem_univ _⟩
private theorem multiInvTotal : Relator.LeftTotal (fun y x => (y,x) ∈ multiC.inv) :=
  fun _ => ⟨0,Set.mem_univ _⟩
private theorem multiBound : ∀ x x' y y', (x,y) ∈ multiC → (x',y') ∈ multiC →
    |dPoint.dist x x' - dTwo.dist y y'| ≤ ((2:ℝ≥0):ℝ) := by
  intro x x' y y' _ _
  have hx : x = x' := Subsingleton.elim _ _
  by_cases hy : y = y' <;> norm_num [dPoint,dTwo,discreteMetric,hx,hy]
private theorem multiForwardGraph : Function.graph (fun _ : Fin 1 => (0 : Fin 2)) ⊆ multiC :=
  Set.subset_univ _
private theorem multiBackwardGraph : Function.graph (fun _ : Fin 2 => (0 : Fin 1)) ⊆ multiC.inv :=
  Set.subset_univ _
private def multiI := Rips.relationInterleaving ℚ dPoint dTwo multiTotal multiInvTotal multiBound 0

private theorem multi_forward :
    (multiI.φ.app 0).hom (rc ℚ dPoint 0 0 (by norm_num) 1) =
      rc ℚ dTwo (0+((2:ℝ≥0):ℝ)) 0 (by norm_num) 1 :=
  forward_image ℚ dPoint dTwo multiTotal multiInvTotal multiBound multiForwardGraph
    0 0 (by norm_num) (by norm_num) 1

private theorem multi_forward_nonzero :
    (multiI.φ.app 0).hom (rc ℚ dPoint 0 0 (by norm_num) 1) ≠ 0 := by
  rw [multi_forward]
  exact vClass_nonzero _ _ _

private theorem multi_difference_collapses :
    (multiI.ψ.app 0).hom
      (rc ℚ dTwo 0 0 (by norm_num) 1 - rc ℚ dTwo 0 1 (by norm_num) 1) = 0 := by
  have h0 := backward_image ℚ dPoint dTwo multiTotal multiInvTotal multiBound multiBackwardGraph
    0 0 (by norm_num) (by norm_num) 1
  have h1 := backward_image ℚ dPoint dTwo multiTotal multiInvTotal multiBound multiBackwardGraph
    0 1 (by norm_num) (by norm_num) 1
  exact (map_sub (multiI.ψ.app 0).hom _ _).trans
    ((congrArg₂ (fun a b => a-b) h0 h1).trans (sub_self _))

private theorem multi_difference_nonzero_before_edge :
    rc ℚ dTwo 0 0 (by norm_num) 1 - rc ℚ dTwo 0 1 (by norm_num) 1 ≠ 0 := by
  rw [sub_ne_zero]
  letI := discrete_no_edges (V := Fin 2) 2 (by norm_num) 0 (by norm_num)
  exact classes_differ _ 0 1 (by decide) _ _

private theorem multi_common_vertex_persists (γ : ℝ≥0) :
    ((RealShift.transition γ (sublevelModule ℚ (Rips.filter dPoint) 0)).app 0).hom
      (rc ℚ dPoint 0 0 (by norm_num) 1) ≠ 0 := by
  have he := transition_image ℚ (rf dPoint) γ 0 0 (rv dPoint 0 0 (by norm_num))
    (rv dPoint _ 0 (by positivity)) 1
  rw [he]
  exact vClass_nonzero _ _ _

private theorem multi_transition_kills_difference :
    ((RealShift.transition (2+2) (sublevelModule ℚ (Rips.filter dTwo) 0)).app 0).hom
      (rc ℚ dTwo 0 0 (by norm_num) 1 - rc ℚ dTwo 0 1 (by norm_num) 1) = 0 := by
  have he := congrArg (fun m => (m.app 0).hom
    (rc ℚ dTwo 0 0 (by norm_num) 1 - rc ℚ dTwo 0 1 (by norm_num) 1)) multiI.ψ_φ
  rw [← he]
  change ((RealShift.compIso 2 2 (sublevelModule ℚ (Rips.filter dTwo) 0)).hom.app 0).hom
    ((multiI.φ.app (0+((2:ℝ≥0):ℝ))).hom ((multiI.ψ.app 0).hom _)) = 0
  rw [multi_difference_collapses,map_zero,map_zero]

private theorem multi_triangles :
    ((((multiI.φ ≫ (RealShift.shift 2).map multiI.ψ ≫
      (RealShift.compIso 2 2 (sublevelModule ℚ (Rips.filter dPoint) 0)).hom).app 0).hom
        (rc ℚ dPoint 0 0 (by norm_num) 1)) = rc ℚ dPoint (0+((2+2:ℝ≥0):ℝ)) 0 (by norm_num) 1) ∧
    ((((multiI.ψ ≫ (RealShift.shift 2).map multiI.φ ≫
      (RealShift.compIso 2 2 (sublevelModule ℚ (Rips.filter dTwo) 0)).hom).app 0).hom
        (rc ℚ dTwo 0 1 (by norm_num) 1)) = rc ℚ dTwo (0+((2+2:ℝ≥0):ℝ)) 1 (by norm_num) 1) := by
  constructor
  · rw [multiI.φ_ψ]
    exact transition_image ℚ (rf dPoint) (2+2) 0 0 _ _ 1
  · rw [multiI.ψ_φ]
    exact transition_image ℚ (rf dTwo) (2+2) 0 1 _ _ 1

private theorem multi_diagrams (n : ℕ) :
    bottleneck (dgm ℚ (Rips.filter dPoint) n) (dgm ℚ (Rips.filter dTwo) n) ≤ 2 :=
  Rips.bottleneck_dgm_le_of_relation dPoint dTwo multiTotal multiInvTotal multiBound ℚ n

/-! Pairwise bounds must control two images of the same source vertex. -/

private theorem multi_bound_one_fails :
    ¬ ∀ x x' y y', (x,y) ∈ multiC → (x',y') ∈ multiC →
      |dPoint.dist x x' - dTwo.dist y y'| ≤ (1:ℝ) := by
  intro h
  have hh := h 0 0 0 1 (Set.mem_univ _) (Set.mem_univ _)
  norm_num [dPoint,dTwo,discreteMetric] at hh

private theorem multi_geometry_one_fails :
    ¬ IsShiftedSimplicialRelation (rf dPoint) (rf dTwo) 1 multiC := by
  intro h
  have hh := h 0 {0} (rv dPoint 0 0 (by norm_num)) {0,1} (by simp) (by
    intro y _
    exact ⟨0,by simp,Set.mem_univ _⟩)
  have hd := ((Rips.mem_sublevel_iff dTwo _ _).mp hh).2 0 (by simp) 1 (by simp)
  norm_num [dTwo,discreteMetric] at hd

private theorem pair_bound_zero_fails :
    ¬ ∀ x x' y y', (x,y) ∈ pairC → (x',y') ∈ pairC →
      |dTwo.dist x x' - dThree.dist y y'| ≤ (0:ℝ) := by
  intro h
  have hh := h 0 1 false true (by change finTwoEquiv 0 = false; rfl) (by change finTwoEquiv 1 = true; rfl)
  norm_num [dTwo,dThree,discreteMetric] at hh

private theorem pair_geometry_zero_fails :
    ¬ IsShiftedSimplicialRelation (rf dTwo) (rf dThree) 0 pairC := by
  intro h
  have hσ : ({0,1} : Finset (Fin 2)) ∈ rf dTwo 2 := by
    apply (Rips.mem_sublevel_iff dTwo 2 _).mpr
    refine ⟨by simp, ?_⟩
    intro x _ y _
    rw [discrete_dist]
    split_ifs <;> norm_num
  have hh := h 2 {0,1} hσ {false,true} (by simp) (by
    intro y hy
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ⟨0,by simp,by change finTwoEquiv 0 = false; rfl⟩
    · exact ⟨1,by simp,by change finTwoEquiv 1 = true; rfl⟩)
  have hd := ((Rips.mem_sublevel_iff dThree _ _).mp hh).2 false (by simp) true (by simp)
  norm_num [dThree,discreteMetric] at hd

/-! Empty carriers, genuine metric separation and the zero left tail. -/

private abbrev dEmpty : MetricSpace (Fin 0) := discreteMetric (Fin 0) 1 (by norm_num)
private theorem emptyTotal : Relator.LeftTotal (fun x y =>
    (x,y) ∈ (∅ : SetRel (Fin 0) (Fin 0))) := fun x => isEmptyElim x
private theorem emptyInvTotal : Relator.LeftTotal (fun y x =>
    (y,x) ∈ (∅ : SetRel (Fin 0) (Fin 0)).inv) := fun y => isEmptyElim y
private theorem emptyBound (ε : ℝ≥0) : ∀ x x' y y',
    (x,y) ∈ (∅ : SetRel (Fin 0) (Fin 0)) → (x',y') ∈ (∅ : SetRel (Fin 0) (Fin 0)) →
      |dEmpty.dist x x' - dEmpty.dist y y'| ≤ (ε:ℝ) := by
  intro x
  exact isEmptyElim x
private def emptyI (R : Type) [Ring R] (ε : ℝ≥0) (n : ℕ) :=
  Rips.relationInterleaving R dEmpty dEmpty emptyTotal emptyInvTotal (emptyBound ε) n
private theorem empty_diagrams (k : Type) [Field k] (ε : ℝ≥0) (n : ℕ) :
    bottleneck (dgm k (Rips.filter dEmpty) n) (dgm k (Rips.filter dEmpty) n) ≤ (ε:ℝ≥0∞) :=
  Rips.bottleneck_dgm_le_of_relation dEmpty dEmpty emptyTotal emptyInvTotal (emptyBound ε) k n
private theorem no_total_nonempty_empty (C : SetRel (Fin 1) (Fin 0)) :
    ¬ Relator.LeftTotal (fun x y => (x,y) ∈ C) := by
  intro h
  obtain ⟨y,_⟩ := h 0
  exact isEmptyElim y
private theorem no_inverse_total_empty_nonempty (C : SetRel (Fin 0) (Fin 1)) :
    ¬ Relator.LeftTotal (fun y x => (y,x) ∈ C.inv) := no_total_nonempty_empty C.inv
private theorem scale_conventions :
    ({0} : Finset (Fin 1)) ∈ rf dPoint 0 ∧
    ({0} : Finset (Fin 1)) ∉ rf dPoint (-1) ∧
    rf dPoint (-1) = ⊥ := by
  have he := Rips.sublevel_eq_bot_of_neg dPoint (r := -1) (by norm_num)
  exact ⟨rv dPoint 0 0 (by norm_num),by rw [show rf dPoint (-1) = ⊥ from he]; simp,he⟩
private theorem repeated_points_do_not_define_a_label_metric :
    ¬ ∃ d : MetricSpace (Fin 2), ∀ i j, d.dist i j =
      dist ((fun _ : Fin 2 => (0:ℝ)) i) ((fun _ : Fin 2 => (0:ℝ)) j) := by
  rintro ⟨d,h⟩
  have hz : d.dist 0 1 = 0 := by simpa using h 0 1
  have he := d.eq_of_dist_eq_zero hz
  exact (by decide : (0 : Fin 2) ≠ 1) he

/-! Different infinite carriers give a zero-interleaving isomorphism. -/

private abbrev NatCopy := {n : ℕ // True}
private def natCopyEquiv : ℕ ≃ NatCopy where
  toFun n := ⟨n,True.intro⟩
  invFun n := n.1
  left_inv _ := rfl
  right_inv _ := rfl
private instance : Infinite NatCopy := Infinite.of_injective natCopyEquiv natCopyEquiv.injective
private abbrev dNat : MetricSpace ℕ := discreteMetric ℕ 1 (by norm_num)
private abbrev dNatCopy : MetricSpace NatCopy := discreteMetric NatCopy 1 (by norm_num)
private abbrev natC := Function.graph natCopyEquiv
private theorem natTotal : Relator.LeftTotal (fun x y => (x,y) ∈ natC) :=
  fun x => ⟨natCopyEquiv x,rfl⟩
private theorem natInvTotal : Relator.LeftTotal (fun y x => (y,x) ∈ natC.inv) :=
  fun y => ⟨natCopyEquiv.symm y,natCopyEquiv.apply_symm_apply y⟩
private theorem natBound : ∀ x x' y y', (x,y) ∈ natC → (x',y') ∈ natC →
    |dNat.dist x x' - dNatCopy.dist y y'| ≤ ((0:ℝ≥0):ℝ) := by
  rintro x x' y y' rfl rfl
  by_cases hx : x = x'
  · subst x'; simp [dNat,dNatCopy,discreteMetric]
  · have hy : natCopyEquiv x ≠ natCopyEquiv x' := fun he => hx (natCopyEquiv.injective he)
    simp [dNat,dNatCopy,discreteMetric,hx,hy]
private theorem nat_isometry :
    @Isometry ℕ NatCopy dNat.toPseudoMetricSpace.toPseudoEMetricSpace
      dNatCopy.toPseudoMetricSpace.toPseudoEMetricSpace natCopyEquiv := by
  apply @Isometry.of_dist_eq ℕ NatCopy dNat.toPseudoMetricSpace dNatCopy.toPseudoMetricSpace
  intro x x'
  have h := natBound x x' (natCopyEquiv x) (natCopyEquiv x') rfl rfl
  have he := abs_nonpos_iff.mp h
  exact (sub_eq_zero.mp he).symm

private def natI := Rips.relationInterleaving ℚ dNat dNatCopy natTotal natInvTotal natBound 0
private theorem infinite_carriers :
    Set.Infinite (Set.univ : Set ℕ) ∧ Set.Infinite (Set.univ : Set NatCopy) :=
  ⟨Set.infinite_univ,Set.infinite_univ⟩
private theorem nat_image :
    (natI.φ.app 0).hom (rc ℚ dNat 0 0 (by norm_num) 1) =
      rc ℚ dNatCopy (0+((0:ℝ≥0):ℝ)) (natCopyEquiv 0) (by norm_num) 1 := by
  exact forward_image ℚ dNat dNatCopy natTotal natInvTotal natBound (Set.Subset.refl _)
    0 0 (by norm_num) (by norm_num) 1
private theorem nat_image_nonzero :
    (natI.φ.app 0).hom (rc ℚ dNat 0 0 (by norm_num) 1) ≠ 0 := by
  rw [nat_image]
  exact vClass_nonzero _ _ _
private theorem nat_isomorphism_nonzero :
    (((RealInterleaving.toIso natI).hom.app 0).hom
      (rc ℚ dNat 0 0 (by norm_num) 1)) ≠ 0 := by
  have he : (((RealInterleaving.toIso natI).hom.app 0).hom
      (rc ℚ dNat 0 0 (by norm_num) 1)) =
      rc ℚ dNatCopy 0 (natCopyEquiv 0) (by norm_num) 1 := by
    change ((RealShift.zeroIso (sublevelModule ℚ (Rips.filter dNatCopy) 0)).hom.app 0).hom
      ((natI.φ.app 0).hom (rc ℚ dNat 0 0 (by norm_num) 1)) = _
    rw [nat_image]
    exact zeroIso_image ℚ (rf dNatCopy) 0 (natCopyEquiv 0) _ _ 1
  rw [he]
  exact vClass_nonzero _ _ _

/-! Fields and positive-shift triangles retain noncentral coefficients. -/

private abbrev dUnit : MetricSpace Unit := discreteMetric Unit 1 (by norm_num)
private abbrev coefficientC : SetRel Unit (Fin 1) := Function.graph (fun _ => 0)
private theorem coefficientTotal : Relator.LeftTotal (fun x y => (x,y) ∈ coefficientC) :=
  fun _ => ⟨0,rfl⟩
private theorem coefficientInvTotal : Relator.LeftTotal (fun y x => (y,x) ∈ coefficientC.inv) :=
  fun y => ⟨(),Subsingleton.elim _ _⟩
private theorem coefficientBound : ∀ x x' y y', (x,y) ∈ coefficientC → (x',y') ∈ coefficientC →
    |dUnit.dist x x' - dPoint.dist y y'| ≤ ((1:ℝ≥0):ℝ) := by
  intro x x' y y' _ _
  have hx : x = x' := Subsingleton.elim _ _
  have hy : y = y' := Subsingleton.elim _ _
  simp [dUnit,dPoint,discreteMetric,hx,hy]
private def coefficientI (R : Type) [Ring R] :=
  Rips.relationInterleaving R dUnit dPoint coefficientTotal coefficientInvTotal coefficientBound 0

private theorem singleton_stage {V : Type} [Subsingleton V] (d : MetricSpace V)
    (t : ℝ) (x : V) (ht : 0 ≤ t) : rf d t = singletonFace x := by
  apply le_antisymm
  · intro σ hσ
    change σ = {x}
    obtain ⟨z,hz⟩ := ((Rips.mem_sublevel_iff d t σ).mp hσ).1
    ext y
    simp only [Finset.mem_singleton]
    constructor
    · intro _; exact Subsingleton.elim _ _
    · intro _; simpa only [Subsingleton.elim z y] using hz
  · intro σ hσ
    change σ = {x} at hσ
    subst σ
    exact rv d t x ht

private def classEquiv {V : Type} [LinearOrder V] (R : Type) [Ring R]
    (K : PreAbstractSimplicialComplex V) (x : V) (hK : K = singletonFace x) :
    simplicialHomology K R 0 ≃ₗ[R] R :=
  (eqToIso (congrArg (fun L => simplicialHomology L R 0) hK)).toLinearEquiv.trans
    (simplicialSingletonH0Equiv R x)
private theorem classEquiv_class {V : Type} [LinearOrder V] (R : Type) [Ring R]
    (K : PreAbstractSimplicialComplex V) (x : V) (hK : K = singletonFace x)
    (hx : ({x} : Finset V) ∈ K) (a : R) : classEquiv R K x hK (vClass R K x hx a) = a := by
  subst K
  change simplicialSingletonH0Equiv R x (vClass R (singletonFace x) x rfl a) = a
  exact simplicialSingletonH0Equiv_class R x a
private def singletonAt {V : Type} [LinearOrder V] [Subsingleton V] (R : Type) [Ring R]
    (d : MetricSpace V) (t : ℝ) (x : V) (ht : 0 ≤ t) :
    simplicialHomology (rf d t) R 0 ≃ₗ[R] R :=
  classEquiv R _ x (singleton_stage d t x ht)

private def coefficientEvaluations (R : Type) [Ring R] (a : R) : Prop :=
    (singletonAt R dPoint (0+((1:ℝ≥0):ℝ)) 0 (by norm_num)
      (((coefficientI R).φ.app 0).hom (rc R dUnit 0 () (by norm_num) a)) = a ∧
    singletonAt R dUnit (0+((1:ℝ≥0):ℝ)) () (by norm_num)
      (((coefficientI R).ψ.app 0).hom (rc R dPoint 0 0 (by norm_num) a)) = a) ∧
    (singletonAt R dUnit (0+((1+1:ℝ≥0):ℝ)) () (by norm_num)
      ((((coefficientI R).φ ≫ (RealShift.shift 1).map (coefficientI R).ψ ≫
        (RealShift.compIso 1 1 (sublevelModule R (Rips.filter dUnit) 0)).hom).app 0).hom
          (rc R dUnit 0 () (by norm_num) a)) = a ∧
    singletonAt R dPoint (0+((1+1:ℝ≥0):ℝ)) 0 (by norm_num)
      ((((coefficientI R).ψ ≫ (RealShift.shift 1).map (coefficientI R).φ ≫
        (RealShift.compIso 1 1 (sublevelModule R (Rips.filter dPoint) 0)).hom).app 0).hom
          (rc R dPoint 0 0 (by norm_num) a)) = a)

private theorem coefficient_evaluations (R : Type) [Ring R] (a : R) :
    coefficientEvaluations R a := by
  have hf := forward_image R dUnit dPoint coefficientTotal coefficientInvTotal coefficientBound
    (Set.Subset.refl _) 0 () (by norm_num) (by norm_num) a
  have hg := backward_image R dUnit dPoint coefficientTotal coefficientInvTotal coefficientBound
    (g := fun _ => ()) (by intro p _; exact Subsingleton.elim _ _)
    0 0 (by norm_num) (by norm_num) a
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact (congrArg (singletonAt R dPoint (0+((1:ℝ≥0):ℝ)) 0 (by norm_num)) hf).trans
      (classEquiv_class R _ 0 _ _ a)
  · exact (congrArg (singletonAt R dUnit (0+((1:ℝ≥0):ℝ)) () (by norm_num)) hg).trans
      (classEquiv_class R _ () _ _ a)
  · rw [(coefficientI R).φ_ψ]
    exact (congrArg (singletonAt R dUnit (0+((1+1:ℝ≥0):ℝ)) () (by norm_num))
      (transition_image R (rf dUnit) (1+1) 0 ()
        (rv dUnit 0 () (by norm_num)) (rv dUnit _ () (by norm_num)) a)).trans
      (classEquiv_class R _ () _ _ a)
  · rw [(coefficientI R).ψ_φ]
    exact (congrArg (singletonAt R dPoint (0+((1+1:ℝ≥0):ℝ)) 0 (by norm_num))
      (transition_image R (rf dPoint) (1+1) 0 0
        (rv dPoint 0 0 (by norm_num)) (rv dPoint _ 0 (by norm_num)) a)).trans
      (classEquiv_class R _ 0 _ _ a)

private theorem matrix_noncentral :
    (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,0;0,0] ≠
      !![1,0;0,0] * !![0,1;0,0] := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  norm_num [Matrix.mul_apply,Fin.sum_univ_two] at hh
private theorem matrix_fields_and_triangles :
    coefficientEvaluations (Matrix (Fin 2) (Fin 2) ℤ) !![0,1;0,0] :=
  coefficient_evaluations _ _
private theorem trivial_ring_fields_and_triangles : coefficientEvaluations (ZMod 1) 0 :=
  coefficient_evaluations _ _

end
end TDA.Persistence.RipsRelationInterleavingExamples

