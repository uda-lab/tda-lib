import TDA.Persistence.SimplicialMultivaluedMapComposition
import TDA.Simplicial.H0Augmentation
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Actual nonzero composition, signed orientation, infinite images and support controls. -/

namespace TDA.Persistence.SimplicialMultivaluedMapCompositionExamples

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


private theorem compTotal {V W U : Type} {C : SetRel V W} {D : SetRel W U}
    (hC : Relator.LeftTotal (fun x y => (x,y) ∈ C))
    (hD : Relator.LeftTotal (fun y z => (y,z) ∈ D)) :
    Relator.LeftTotal (fun x z => (x,z) ∈ C.comp D) :=
  Relator.LeftTotal.trans (r₁₃ := fun x z => (x,z) ∈ C.comp D)
    (fun _ y _ hxy hyz => ⟨y,hxy,hyz⟩) hC hD

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

private abbrev pointK := (⊤ : PreAbstractSimplicialComplex (Fin 1))
private abbrev edgeK := (⊤ : PreAbstractSimplicialComplex (Fin 2))
private abbrev triangleK := (⊤ : PreAbstractSimplicialComplex (Fin 3))

/-! A point born at zero maps through an edge born at one to a triangle born at three. -/

private abbrev point0 := birth 0 pointK
private abbrev edge1 := birth 1 edgeK
private abbrev triangle3 := birth 3 triangleK

private theorem firstRelation : IsShiftedSimplicialRelation point0 edge1 1
    (Set.univ : SetRel (Fin 1) (Fin 2)) := by
  simpa using univBirth (W := Fin 2) 0 1 pointK
private theorem secondRelation : IsShiftedSimplicialRelation edge1 triangle3 2
    (Set.univ : SetRel (Fin 2) (Fin 3)) := by
  simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using univBirth (W := Fin 3) 1 3 edgeK

private def bornComposite (R : Type) [Ring R] :=
  multivaluedSimplicialHomologyMap R (univTotal (V := Fin 1) (0 : Fin 2)) firstRelation 0 ≫
    reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (1 : ℝ)))
      (multivaluedSimplicialHomologyMap R (univTotal (V := Fin 2) (0 : Fin 3)) secondRelation 0) ≫
    (shiftedSimplicialHomologyCompIso R triangle3 1 2 0).hom

private theorem born_whole_composition (R : Type) [Ring R] :
    bornComposite R = multivaluedSimplicialHomologyMap R
      (compTotal (univTotal (V := Fin 1) (0 : Fin 2)) (univTotal (V := Fin 2) (0 : Fin 3)))
      (firstRelation.comp secondRelation) 0 :=
  multivaluedSimplicialHomologyMap_comp R _ _ _ _ 0

private theorem born_image (i : Fin 2) (j : Fin 3) :
    ((bornComposite ℚ).app 0).hom (vClass ℚ (point0 0) 0 (by norm_num [birth]) 1) =
      vClass ℚ (triangle3 (0 + (1 + 2))) j (by norm_num [birth]) 1 :=
  composite_image ℚ _ _ firstRelation secondRelation
    (subordinate_univ (fun _ : Fin 1 => i))
    (subordinate_univ (fun _ : Fin 2 => j)) 0 0 _ _ 1

private theorem born_nonzero :
    ((bornComposite ℚ).app 0).hom (vClass ℚ (point0 0) 0 (by norm_num [birth]) 1) ≠ 0 := by
  rw [born_image 0 0]
  exact vClass_nonzero _ _ _

private theorem born_canonical_composite_nonzero :
    ((multivaluedSimplicialHomologyMap ℚ
      (compTotal (univTotal (V := Fin 1) (0 : Fin 2)) (univTotal (V := Fin 2) (0 : Fin 3)))
      (firstRelation.comp secondRelation) 0).app 0).hom
      (vClass ℚ (point0 0) 0 (by norm_num [birth]) 1) ≠ 0 := by
  rw [← born_whole_composition]
  exact born_nonzero

private theorem born_selector_comparison :
    vClass ℚ (triangle3 (0 + (1 + 2))) 0 (by norm_num [birth]) 1 =
      vClass ℚ (triangle3 (0 + (1 + 2))) 2 (by norm_num [birth]) 1 :=
  (born_image 0 0).symm.trans (born_image 1 2)

private theorem born_selectors_distinct :
    (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ : Fin 1 => (1 : Fin 2)) ∧
    (fun _ : Fin 2 => (0 : Fin 3)) ≠ (fun _ : Fin 2 => (2 : Fin 3)) := by
  constructor
  · intro h; exact (by decide : (0 : Fin 2) ≠ 1) (congrFun h 0)
  · intro h; exact (by decide : (0 : Fin 3) ≠ 2) (congrFun h 0)

/-! Negative then positive degrees evaluate the second component at the earlier level. -/

private abbrev point2 := birth 2 pointK
private abbrev point3 := birth 3 pointK
private theorem negativeRelation : IsShiftedSimplicialRelation point2 edge1 (-1)
    (Set.univ : SetRel (Fin 1) (Fin 2)) := by
  simpa only [show (1 : ℝ) - 2 = -1 by norm_num] using univBirth (W := Fin 2) 2 1 pointK
private theorem collapseRelation : IsShiftedSimplicialRelation edge1 point3 2
    (Set.univ : SetRel (Fin 2) (Fin 1)) := by
  simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using univBirth (W := Fin 1) 1 3 edgeK

private theorem negative_positive_image :
    ((multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 1) (0 : Fin 2)) negativeRelation 0 ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (-1 : ℝ)))
        (multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 2) (0 : Fin 1)) collapseRelation 0) ≫
      (shiftedSimplicialHomologyCompIso ℚ point3 (-1) 2 0).hom).app 2).hom
        (vClass ℚ (point2 2) 0 (by norm_num [birth]) 1) =
      vClass ℚ (point3 (2 + (-1 + 2))) 0 (by norm_num [birth]) 1 :=
  composite_image ℚ _ _ negativeRelation collapseRelation
    (subordinate_univ (fun _ : Fin 1 => (0 : Fin 2)))
    (subordinate_univ (fun _ : Fin 2 => (0 : Fin 1))) 2 0 _ _ 1

private theorem negative_positive_target_nonzero :
    vClass ℚ (point3 (2 + (-1 + 2))) 0 (by norm_num [birth]) 1 ≠ 0 :=
  vClass_nonzero _ _ _

private theorem mixed_sign_degree_one :
    IsShiftedSimplicial point2 point3 1 (fun _ : Fin 1 => (0 : Fin 1)) := by
  simpa only [Function.comp_def, show (-1 : ℝ) + 2 = 1 by norm_num] using
    (negativeRelation.of_subordinate (subordinate_univ (fun _ : Fin 1 => (0 : Fin 2)))).comp
      (collapseRelation.of_subordinate (subordinate_univ (fun _ : Fin 2 => (0 : Fin 1))))

private theorem negative_second_level :
    (2 : ℝ) + (-1) = 1 ∧
    (reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (-1 : ℝ)))
      (multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 2) (0 : Fin 1)) collapseRelation 0)).app 2 =
    (multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 2) (0 : Fin 1)) collapseRelation 0).app (2 + (-1)) := by
  exact ⟨by norm_num, rfl⟩

private theorem mixed_sign_degree_zero_fails :
    ¬IsShiftedSimplicial point2 point3 0 (fun _ : Fin 1 => (0 : Fin 1)) := by
  intro h
  have hh := h 2 {0} (by norm_num [birth])
  norm_num [birth] at hh

/-! Infinite intermediate images: the second relation is a parity graph. -/

private def parity (k : ℕ) : Fin 2 := ⟨k % 2, Nat.mod_lt _ (by decide)⟩
private theorem parityShift : IsShiftedSimplicial (constF (⊤ : PreAbstractSimplicialComplex ℕ))
    (constF edgeK) 0 parity := by
  let : DecidableEq (Fin 2) := Classical.decEq _
  intro t σ hσ
  exact Finset.image_nonempty.mpr hσ
private abbrev infiniteC := fullRelation (W := ℕ) pointK
private abbrev parityD := (isShiftedSimplicialRelation_graph_iff parity).mpr parityShift

private theorem intermediate_image_infinite :
    (SetRel.image (Set.univ : SetRel (Fin 1) ℕ) ({(0 : Fin 1)} : Set (Fin 1))).Infinite := by
  have he : SetRel.image (Set.univ : SetRel (Fin 1) ℕ) ({(0 : Fin 1)} : Set (Fin 1)) = Set.univ := by
    ext k
    constructor
    · intro _; trivial
    · intro _; exact ⟨0, by simp, Set.mem_univ _⟩
  rw [he]
  exact Set.infinite_univ

private theorem parity_composite_endpoints (i : Fin 2) :
    i ∈ SetRel.image (SetRel.comp (Set.univ : SetRel (Fin 1) ℕ) (Function.graph parity))
      ({(0 : Fin 1)} : Set (Fin 1)) := by
  refine ⟨0, by simp, (i : ℕ), Set.mem_univ _, ?_⟩
  change parity (i : ℕ) = i
  exact Fin.ext (Nat.mod_eq_of_lt i.2)

private theorem infinite_actual_composition_image :
    ((multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 1) (0 : ℕ)) infiniteC 0 ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (0 : ℝ)))
        (multivaluedSimplicialHomologyMap ℚ (fun k => ⟨parity k,rfl⟩) parityD 0) ≫
      (shiftedSimplicialHomologyCompIso ℚ (constF edgeK) 0 0 0).hom).app 0).hom
      (vClass ℚ ((constF pointK) 0) 0 (by simp [constF]) 1) =
    vClass ℚ ((constF edgeK) (0 + (0 + 0))) 1 (by simp [constF]) 1 := by
  exact composite_image ℚ _ _ infiniteC parityD
    (subordinate_univ (fun _ : Fin 1 => (1 : ℕ))) (Set.Subset.refl _) 0 0 _ _ 1

private theorem infinite_target_nonzero :
    vClass ℚ ((constF edgeK) (0 + (0 + 0))) 1 (by simp [constF]) 1 ≠ 0 :=
  vClass_nonzero _ _ _


/-! Native graph direction, signed reversal followed by injection, and collapse. -/

private def fullMap {V W : Type} (f : V → W) :
    VertexMap (⊤ : PreAbstractSimplicialComplex V) (⊤ : PreAbstractSimplicialComplex W) where
  toFun := f
  map_face s hs := by
    classical
    exact Finset.image_nonempty.mpr hs

private def rev : Fin 2 → Fin 2 := Equiv.swap 0 1
private def inj : Fin 2 → Fin 3 := Fin.castSucc
private def collapse : Fin 3 → Fin 1 := fun _ => 0

private theorem graph_direction :
    (Function.graph rev).comp (Function.graph inj) = Function.graph (inj ∘ rev) ∧
    (Function.graph inj).comp (Function.graph collapse) = Function.graph (collapse ∘ inj) := by
  constructor <;> exact (Function.graph_comp _ _).symm

private theorem signed_reversal_injection :
    vertexChainMap ℤ (VertexMap.comp (fullMap rev) (fullMap inj)) 1
      (orientedTuple edgeK ℤ (id : Fin 2 → Fin 2)) =
      -orientedTuple triangleK ℤ inj := by
  rw [vertexChainMap_comp]
  change vertexChainMap ℤ (fullMap inj) 1
    (vertexChainMap ℤ (fullMap rev) 1 (orientedTuple edgeK ℤ id)) = _
  rw [vertexChainMap_orientedTuple ℤ _ _ (by simp),
    vertexChainMap_orientedTuple ℤ _ _ (by simp [rev])]
  have hp := orientedTuple_comp_perm triangleK ℤ inj (Equiv.swap (0 : Fin 2) 1)
  simpa [rev, inj, fullMap, Function.comp_def,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)] using hp

private theorem injection_chain_nonzero : orientedTuple triangleK ℤ inj ≠ 0 := by
  rw [orientedTuple_of_monotone triangleK ℤ inj
    (Fin.castSucc_injective 2) (by simp only [mem_full, Finset.image_nonempty]; exact Finset.univ_nonempty) (fun _ _ h => h)]
  simp

private theorem signed_image_nonzero :
    vertexChainMap ℤ (VertexMap.comp (fullMap rev) (fullMap inj)) 1
      (orientedTuple edgeK ℤ (id : Fin 2 → Fin 2)) ≠ 0 := by
  rw [signed_reversal_injection]
  exact neg_ne_zero.mpr injection_chain_nonzero

private theorem actual_collapse_after_injection :
    vertexChainMap ℤ (VertexMap.comp (fullMap inj) (fullMap collapse)) 1
      (orientedTuple edgeK ℤ (id : Fin 2 → Fin 2)) = 0 := by
  rw [vertexChainMap_orientedTuple ℤ _ _ (by simp)]
  apply orientedTuple_of_not_injective
  intro h
  have hh : (0 : Fin 2) = 1 := h rfl
  exact (by decide : (0 : Fin 2) ≠ 1) hh

private theorem fullShift {V W : Type} (f : V → W) :
    IsShiftedSimplicial (constF (⊤ : PreAbstractSimplicialComplex V))
      (constF (⊤ : PreAbstractSimplicialComplex W)) 0 f := by
  classical
  intro t σ hσ
  exact Finset.image_nonempty.mpr hσ

private abbrev revRelation := (isShiftedSimplicialRelation_graph_iff rev).mpr (fullShift rev)
private abbrev injRelation := (isShiftedSimplicialRelation_graph_iff inj).mpr (fullShift inj)

private theorem signed_graph_h0_composition :
    ((multivaluedSimplicialHomologyMap ℚ (fun x => ⟨rev x,rfl⟩) revRelation 0 ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (0 : ℝ)))
        (multivaluedSimplicialHomologyMap ℚ (fun x => ⟨inj x,rfl⟩) injRelation 0) ≫
      (shiftedSimplicialHomologyCompIso ℚ (constF triangleK) 0 0 0).hom).app 0).hom
      (vClass ℚ ((constF edgeK) 0) 0 (by simp [constF]) 1) =
    vClass ℚ ((constF triangleK) (0 + (0 + 0))) 1 (by simp [constF]) 1 :=
  composite_image ℚ _ _ revRelation injRelation (Set.Subset.refl _) (Set.Subset.refl _)
    0 0 _ _ 1

private theorem signed_graph_target_nonzero :
    vClass ℚ ((constF triangleK) (0 + (0 + 0))) 1 (by simp [constF]) 1 ≠ 0 :=
  vClass_nonzero _ _ _

/-! Ghost vertices remain ambient-total without becoming faces. -/

private def ghostEdge : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s ⊆ {0,1}}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts htn => ⟨htn, hts.trans hs.2⟩⟩

private def ghostC : SetRel (Fin 2) (Fin 3) :=
  {p | if p.1 = 0 then p.2 = 0 ∨ p.2 = 1 else p.2 = 2}
private def ghostCollapse : Fin 3 → Fin 2 := fun y => if y = 2 then 1 else 0

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

private theorem ghostCollapse_shift : IsShiftedSimplicial (constF ghostEdge)
    (constF (singletonFace (0 : Fin 2))) 0 ghostCollapse := by
  let : DecidableEq (Fin 2) := Classical.decEq _
  intro t σ hσ
  change σ.image ghostCollapse = {0}
  ext z
  constructor
  · intro hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    have hy01 : y = 0 ∨ y = 1 := by simpa using hσ.2 hy
    rcases hy01 with rfl | rfl <;> simp [ghostCollapse]
  · intro hz
    have hz0 : z = 0 := by simpa using hz
    subst z
    obtain ⟨y,hy⟩ := hσ.1
    have hy01 : y = 0 ∨ y = 1 := by simpa using hσ.2 hy
    refine Finset.mem_image.mpr ⟨y,hy,?_⟩
    rcases hy01 with rfl | rfl <;> simp [ghostCollapse]

private abbrev ghostD := (isShiftedSimplicialRelation_graph_iff ghostCollapse).mpr ghostCollapse_shift
private def ghostSelect : Fin 2 → Fin 3 := fun x => if x = 0 then 0 else 2
private theorem ghostSub : Function.graph ghostSelect ⊆ ghostC := by
  intro ⟨x,y⟩ h
  change ghostSelect x = y at h
  subst y
  by_cases hx : x = 0 <;> simp [ghostC, ghostSelect, hx]

private theorem ghost_composite_nonzero :
    ((multivaluedSimplicialHomologyMap ℚ ghost_total ghost_relation 0 ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (0 : ℝ)))
        (multivaluedSimplicialHomologyMap ℚ (fun y => ⟨ghostCollapse y,rfl⟩) ghostD 0) ≫
      (shiftedSimplicialHomologyCompIso ℚ (constF (singletonFace (0 : Fin 2))) 0 0 0).hom).app 0).hom
        (vClass ℚ (singletonFace (0 : Fin 2)) 0 rfl 1) ≠ 0 := by
  have he := composite_image ℚ ghost_total (fun y => ⟨ghostCollapse y,rfl⟩)
    ghost_relation ghostD ghostSub (Set.Subset.refl _) 0 0 rfl
    (by simp [constF, ghostCollapse, ghostSelect, mem_singletonFace_iff]) 1
  intro hz
  exact vClass_nonzero _ _ _ (he.symm.trans hz)

private theorem ghost_support_and_totality :
    Relator.LeftTotal (fun x z => (x,z) ∈ ghostC.comp (Function.graph ghostCollapse)) ∧
    ({(2 : Fin 3)} : Finset (Fin 3)) ∉ ghostEdge ∧
    ({(1 : Fin 2)} : Finset (Fin 2)) ∉ singletonFace (0 : Fin 2) ∧
    (1,1) ∈ ghostC.comp (Function.graph ghostCollapse) := by
  refine ⟨compTotal ghost_total (fun y => ⟨ghostCollapse y,rfl⟩), ?_, ?_, ?_⟩
  · intro h
    have hh := h.2 (by simp : (2 : Fin 3) ∈ ({2} : Finset (Fin 3)))
    exact (by decide : (2 : Fin 3) ∉ ({0,1} : Finset (Fin 3))) hh
  · simp [mem_singletonFace_iff]
  · exact ⟨2, by simp [ghostC], by simp [ghostCollapse]⟩

private theorem empty_total : Relator.LeftTotal
    (fun x y : Fin 0 => (x,y) ∈ (∅ : SetRel (Fin 0) (Fin 0))) := fun x => Fin.elim0 x
private theorem empty_relation (ε : ℝ) :
    IsShiftedSimplicialRelation (constF (⊥ : PreAbstractSimplicialComplex (Fin 0)))
      (constF (⊥ : PreAbstractSimplicialComplex (Fin 0))) ε ∅ := by
  intro t σ hσ
  exact False.elim hσ

private theorem empty_actual_composition :
    multivaluedSimplicialHomologyMap ℤ empty_total (empty_relation (-3)) 0 ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (-3 : ℝ)))
        (multivaluedSimplicialHomologyMap ℤ empty_total (empty_relation 2) 0) ≫
      (shiftedSimplicialHomologyCompIso ℤ
        (constF (⊥ : PreAbstractSimplicialComplex (Fin 0))) (-3) 2 0).hom =
    multivaluedSimplicialHomologyMap ℤ (compTotal empty_total empty_total)
      ((empty_relation (-3)).comp (empty_relation 2)) 0 :=
  multivaluedSimplicialHomologyMap_comp ℤ _ _ _ _ 0

private theorem bottom_geometry_not_total (C : SetRel (Fin 1) (Fin 0)) :
    IsShiftedSimplicialRelation (constF (⊥ : PreAbstractSimplicialComplex (Fin 1)))
      (constF (⊥ : PreAbstractSimplicialComplex (Fin 0))) 0 C ∧
    ¬Relator.LeftTotal (fun x y => (x,y) ∈ C) := by
  constructor
  · intro t σ hσ; exact False.elim hσ
  · intro h; obtain ⟨y,_⟩ := h 0; exact Fin.elim0 y

/-! Unit relations, noncentral coefficients, the trivial ring, and the existing shift. -/

private theorem idRelation {V : Type} (F : SimplicialFiltration ℝ V) :
    IsShiftedSimplicialRelation F F 0 SetRel.id := by
  simpa only [Function.graph_id] using
    (isShiftedSimplicialRelation_graph_iff (id : V → V)).mpr (isShiftedSimplicial_id F)

private theorem native_units :
    (SetRel.id : SetRel (Fin 1) (Fin 1)).comp (Set.univ : SetRel (Fin 1) (Fin 2)) = Set.univ ∧
    SetRel.comp (Set.univ : SetRel (Fin 1) (Fin 2)) (SetRel.id : SetRel (Fin 2) (Fin 2)) = Set.univ := by
  simp

private theorem zero_identity_identification (R : Type) [Ring R] :
    multivaluedSimplicialHomologyMap R (C := SetRel.id) (fun x : Fin 1 => ⟨x,rfl⟩)
      (idRelation point0) 0 ≫ (RealShift.zeroIso (simplicialHomologyPModule R point0 0)).hom = 𝟙 _ := by
  rw [multivaluedSimplicialHomologyMap_eq R _ (idRelation point0)
    (f := id) (by intro p h; exact h)]
  exact shiftedSimplicialHomologyMap_id R point0 0

private theorem left_unit_nonzero :
    ((multivaluedSimplicialHomologyMap ℚ (C := SetRel.id) (fun x => ⟨x,rfl⟩) (idRelation point0) 0 ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (0 : ℝ)))
        (multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 1) (0 : Fin 2)) firstRelation 0) ≫
      (shiftedSimplicialHomologyCompIso ℚ edge1 0 1 0).hom).app 0).hom
        (vClass ℚ (point0 0) 0 (by norm_num [birth]) 1) ≠ 0 := by
  rw [composite_image ℚ _ _ (idRelation point0) firstRelation
    (f := id) (by intro p h; exact h) (subordinate_univ (fun _ : Fin 1 => (0 : Fin 2)))
    0 0 _ (by norm_num [birth]) 1]
  exact vClass_nonzero _ _ _

private theorem right_unit_nonzero :
    ((multivaluedSimplicialHomologyMap ℚ (univTotal (V := Fin 1) (0 : Fin 2)) firstRelation 0 ≫
      reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (1 : ℝ)))
        (multivaluedSimplicialHomologyMap ℚ (C := SetRel.id) (fun x => ⟨x,rfl⟩) (idRelation edge1) 0) ≫
      (shiftedSimplicialHomologyCompIso ℚ edge1 1 0 0).hom).app 0).hom
        (vClass ℚ (point0 0) 0 (by norm_num [birth]) 1) ≠ 0 := by
  rw [composite_image ℚ _ _ firstRelation (idRelation edge1)
    (subordinate_univ (fun _ : Fin 1 => (0 : Fin 2))) (g := id) (by intro p h; exact h)
    0 0 _ (by norm_num [birth]) 1]
  exact vClass_nonzero _ _ _

private abbrev singletonF := constF (singletonFace (0 : Fin 1))
private def coefficientComposite (R : Type) [Ring R] :=
  multivaluedSimplicialHomologyMap R (C := SetRel.id) (fun x => ⟨x,rfl⟩)
    (idRelation singletonF) 0 ≫
  reindexNatTrans (OrderHomClass.toOrderHom (OrderIso.addRight (0 : ℝ)))
    (multivaluedSimplicialHomologyMap R (C := SetRel.id) (fun x => ⟨x,rfl⟩)
      (idRelation singletonF) 0) ≫
  (shiftedSimplicialHomologyCompIso R singletonF 0 0 0).hom

private theorem coefficient_composition (R : Type) [Ring R] (a : R) :
    simplicialSingletonH0Equiv R (0 : Fin 1)
      (((coefficientComposite R).app 0).hom
        (vClass R (singletonFace (0 : Fin 1)) 0 rfl a)) = a := by
  have he := composite_image R (C := SetRel.id) (D := SetRel.id)
    (fun x => ⟨x,rfl⟩) (fun x => ⟨x,rfl⟩) (idRelation singletonF) (idRelation singletonF)
    (f := id) (g := id) (by intro p h; exact h) (by intro p h; exact h) 0 0 rfl rfl a
  calc
    _ = simplicialSingletonH0Equiv R 0 (vClass R (singletonFace (0 : Fin 1)) 0 rfl a) :=
      congrArg (simplicialSingletonH0Equiv R (0 : Fin 1)) he
    _ = a := simplicialSingletonH0Equiv_class R (0 : Fin 1) a

private theorem matrix_noncentral :
    (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,0;0,0] ≠
      !![1,0;0,0] * !![0,1;0,0] := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hh

private theorem matrix_composition :
    let R := Matrix (Fin 2) (Fin 2) ℤ
    let A : R := !![0,1;0,0]
    simplicialSingletonH0Equiv R (0 : Fin 1)
      (((coefficientComposite R).app 0).hom
        (vClass R (singletonFace (0 : Fin 1)) 0 rfl A)) = A :=
  coefficient_composition (Matrix (Fin 2) (Fin 2) ℤ) !![0,1;0,0]

private theorem trivial_ring_composition :
    simplicialSingletonH0Equiv (ZMod 1) (0 : Fin 1)
      (((coefficientComposite (ZMod 1)).app 0).hom
        (vClass (ZMod 1) (singletonFace (0 : Fin 1)) 0 rfl 0)) = 0 :=
  coefficient_composition (ZMod 1) 0

private theorem existing_nnreal_composition :
    multivaluedSimplicialHomologyMapNNReal ℚ (δ := (1 : ℝ≥0))
      (univTotal (V := Fin 1) (0 : Fin 2)) firstRelation 0 ≫
      (RealShift.shift (1 : ℝ≥0)).map
        (multivaluedSimplicialHomologyMapNNReal ℚ (δ := (2 : ℝ≥0))
          (univTotal (V := Fin 2) (0 : Fin 3)) secondRelation 0) ≫
      (RealShift.compIso 1 2 (simplicialHomologyPModule ℚ triangle3 0)).hom =
    multivaluedSimplicialHomologyMapNNReal ℚ (δ := (1 + 2 : ℝ≥0))
      (compTotal (univTotal (V := Fin 1) (0 : Fin 2)) (univTotal (V := Fin 2) (0 : Fin 3)))
      (show IsShiftedSimplicialRelation point0 triangle3 ((1 + 2 : ℝ≥0) : ℝ)
        (SetRel.comp (Set.univ : SetRel (Fin 1) (Fin 2)) (Set.univ : SetRel (Fin 2) (Fin 3))) from
        firstRelation.comp secondRelation) 0 :=
  multivaluedSimplicialHomologyMapNNReal_comp ℚ _ _ firstRelation secondRelation 0

end
end TDA.Persistence.SimplicialMultivaluedMapCompositionExamples
