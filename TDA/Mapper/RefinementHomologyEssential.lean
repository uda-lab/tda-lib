import TDA.Mapper.RefinementHomologyDiagram
import TDA.Mapper.RefinementHomologyCappedTower
import TDA.Simplicial.Cone
import TDA.Persistence.EssentialVanishing
import TDA.Simplicial.H0Augmentation

/-!
# Essential bars of step Mapper diagrams

For step data with an empty initial family and finitely many faces in the chosen degree,
the essential multiplicity is the homology dimension of the last Mapper complex. Thus two
step diagrams, even for maps on different spaces, are at finite bottleneck distance exactly
when these dimensions agree.

The full family on a path-connected space gives a full simplex on its component indices,
which are in bijection with the labels. For a finite nonempty label window and a nonempty
grid, capped centred diagrams consequently have one essential bar in degree zero and none
in positive degree. With a single label, the degree-zero count is the number of path
components, without a path-connectedness assumption. Birth values and finite bars are not
computed. These are library specialisations of the finite step-diagram convention.
-/

namespace TDA.Mapper

open CategoryTheory CategoryTheory.Limits
open TDA.Topology TDA.Simplicial TDA.Persistence TDA.Persistence.FiniteConstructible
open scoped ENNReal

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w z

private theorem finrank_homology_range_id {V : Type u} [LinearOrder V]
    (K : PreAbstractSimplicialComplex V) (k : Type u) [Field k] (n : ℕ) :
    Module.finrank k (LinearMap.range (ModuleCat.Hom.hom (𝟙 (simplicialHomology K k n)))) =
      Module.finrank k (simplicialHomology K k n) := by
  rw [ModuleCat.hom_id, LinearMap.range_id, finrank_top]

section Step

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (k : Type u) [Field k] (f : C(X, Y)) {m : ℕ} (c : Fin m ↪o ℝ)
  {Index : Fin (m + 1) → Type u} (cover : (i : Fin (m + 1)) → Index i → Set Y)
  [∀ i, LinearOrder (ComponentIndex f (cover i))]
  (r : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j))
  (n : ℕ) [∀ i, Finite (Face (mapper f (cover i)) n)] [IsEmpty (Index 0)]

/-- Essential bars count the homology of the last stage, including the empty-grid case. -/
theorem card_essentialPart_stepMapperDiagram :
    (essentialPart (stepMapperDiagram k f c cover r n).points).card =
      Module.finrank k (simplicialHomology (mapper f (cover (Fin.last m))) k n) := by
  classical
  cases m with
  | zero =>
    have hz := isZero_simplicialHomology_mapper_of_isEmpty k f (cover 0) n
    have := ModuleCat.subsingleton_of_isZero hz
    rw [show Fin.last 0 = (0 : Fin 1) from rfl, Module.finrank_zero_of_subsingleton]
    have hp := moduleDiagram_empty_grid c
      (mapperHomologyPModule k f (stepTower c cover) (stepRefinement c cover r) n)
    change (essentialPart (moduleDiagram c _ _).points).card = 0
    rw [hp]
    simp [essentialPart]
  | succ m =>
    rw [stepMapperDiagram_eq_ofIndexBars_succ, card_essentialPart_eq_countP,
      RealBarcode.ofIndexBars_points, Multiset.countP_map, ← Multiset.countP_eq_card_filter]
    have hr := finrank_range_mapperHomologyMap k f
      (fun j : Fin (m + 1) => cover j.succ)
      (fun h => r (Fin.succ_le_succ_iff.mpr h)) n (le_refl (Fin.last m))
    rw [mapperHomologyMap_eq_id, finrank_homology_range_id] at hr
    refine (Multiset.countP_congr rfl fun I _ => propext ?_).trans hr.symm
    have hb := I.birth_lt_death
    have hd := I.death_le_size
    simp only [RealBarcode.endpoints, Fin.val_last]
    split_ifs with h
    · simp only [WithTop.coe_ne_top, false_iff, not_and]
      omega
    · simp only [true_iff]
      omega

variable {X' : Type u} {Y' : Type w} [TopologicalSpace X'] [TopologicalSpace Y']
  (f' : C(X', Y')) {m' : ℕ} (d : Fin m' ↪o ℝ)
  {Index' : Fin (m' + 1) → Type u} (cover' : (i : Fin (m' + 1)) → Index' i → Set Y')
  [∀ i, LinearOrder (ComponentIndex f' (cover' i))]
  (r' : ∀ {i j : Fin (m' + 1)}, i ≤ j → Refinement (cover' i) (cover' j))
  [∀ i, Finite (Face (mapper f' (cover' i)) n)] [IsEmpty (Index' 0)]

/-- Finite bottleneck distance is equivalent to equality of the last-stage homology dimensions;
the maps, spaces and grids may differ. -/
theorem bottleneck_stepMapperDiagram_lt_top_iff :
    bottleneck (stepMapperDiagram k f c cover r n) (stepMapperDiagram k f' d cover' r' n) < ⊤ ↔
      Module.finrank k (simplicialHomology (mapper f (cover (Fin.last m))) k n) =
        Module.finrank k (simplicialHomology (mapper f' (cover' (Fin.last m'))) k n) := by
  rw [bottleneck_lt_top_iff, card_essentialPart_stepMapperDiagram,
    card_essentialPart_stepMapperDiagram]

end Step

section FullFamily

variable {X : Type u} {Y : Type v} {I : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))

private def fullPullbackComponentsEquiv (i : I) :
    ZerothHomotopy (PullbackSpace f (fun _ : I => Set.univ) i) ≃ ZerothHomotopy X where
  toFun := componentMap ⟨Subtype.val, continuous_subtype_val⟩
  invFun := componentMap ⟨fun x => ⟨x, Set.mem_univ _⟩, continuous_id.subtype_mk _⟩
  left_inv c := by induction c using ZerothHomotopy.rec with | mk x => rfl
  right_inv c := by induction c using ZerothHomotopy.rec with | mk x => rfl

/-- A full-family vertex consists of a label and a path component of the domain. -/
def fullComponentIndexEquiv :
    ComponentIndex f (fun _ : I => Set.univ) ≃ I × ZerothHomotopy X :=
  Equiv.sigmaEquivProdOfEquiv (fullPullbackComponentsEquiv f)

/-- On a path-connected domain, projection to the label identifies full-family vertices. -/
def componentIndexFullEquiv [PathConnectedSpace X] :
    ComponentIndex f (fun _ : I => Set.univ) ≃ I := by
  letI : Unique (ZerothHomotopy X) := uniqueOfSubsingleton (Classical.arbitrary _)
  exact (fullComponentIndexEquiv f).trans (Equiv.prodUnique _ _)

/-- Every nonempty finite set of full-family vertices has a common domain point. -/
theorem mapper_full_eq_top [PathConnectedSpace X] :
    mapper f (fun _ : I => Set.univ) = ⊤ := by
  classical
  apply PreAbstractSimplicialComplex.ext
  ext t
  change t.Nonempty ∧ (∃ x : X, ∀ a ∈ t, x ∈ componentCover f _ a) ↔ t.Nonempty
  refine ⟨And.left, fun ht => ⟨ht, Classical.arbitrary X, fun a _ => ?_⟩⟩
  refine ⟨Set.mem_univ _, ?_⟩
  apply (fullPullbackComponentsEquiv f a.1).injective
  exact Subsingleton.elim _ _

/-- The label bijection induces an isomorphism with the homology of the full simplex. -/
def fullMapperHomologyIso [PathConnectedSpace X]
    [LinearOrder (ComponentIndex f (fun _ : I => Set.univ))] [LinearOrder I]
    (R : Type z) [Ring R] (n : ℕ) :
    simplicialHomology (mapper f (fun _ : I => Set.univ)) R n ≅
      simplicialHomology (⊤ : PreAbstractSimplicialComplex I) R n := by
  classical
  let e := componentIndexFullEquiv (I := I) f
  let p : VertexMap (mapper f (fun _ : I => Set.univ)) ⊤ :=
    ⟨e, fun t ht => by
      change (@Finset.image _ _ (Classical.decEq I) e t).Nonempty
      simpa only [Finset.image_nonempty] using ((mem_mapper_iff f _ t).mp ht).1⟩
  let q : VertexMap ⊤ (mapper f (fun _ : I => Set.univ)) :=
    ⟨e.symm, fun t ht => by
      rw [mapper_full_eq_top]
      change (@Finset.image _ _ (Classical.decEq _) e.symm t).Nonempty
      change t.Nonempty at ht
      simpa only [Finset.image_nonempty] using ht⟩
  refine ⟨simplicialHomologyMap R p n, simplicialHomologyMap R q n, ?_, ?_⟩
  · rw [← simplicialHomologyMap_comp, show VertexMap.comp p q = VertexMap.id _ from
      VertexMap.ext fun a => e.symm_apply_apply a, simplicialHomologyMap_id]
  · rw [← simplicialHomologyMap_comp, show VertexMap.comp q p = VertexMap.id _ from
      VertexMap.ext fun a => e.apply_symm_apply a, simplicialHomologyMap_id]

variable [LinearOrder (ComponentIndex f (fun _ : I => Set.univ))]

/-- A finite nonempty full family on a path-connected domain has one degree-zero class. -/
theorem finrank_simplicialHomology_mapper_full_zero [PathConnectedSpace X]
    [Finite I] [Nonempty I] (k : Type z) [Field k] :
    Module.finrank k (simplicialHomology (mapper f (fun _ : I => Set.univ)) k 0) = 1 := by
  let e := componentIndexFullEquiv (I := I) f
  let : LinearOrder I := LinearOrder.lift' e.symm e.symm.injective
  exact (fullMapperHomologyIso f k 0).toLinearEquiv.finrank_eq.trans
    (finrank_simplicialHomology_top_zero k)

/-- Positive-degree homology of a finite full family on a path-connected domain vanishes. -/
theorem isZero_simplicialHomology_mapper_full_succ [PathConnectedSpace X]
    [Finite I] (R : Type z) [Ring R] (n : ℕ) :
    IsZero (simplicialHomology (mapper f (fun _ : I => Set.univ)) R (n + 1)) := by
  let e := componentIndexFullEquiv (I := I) f
  let : LinearOrder I := LinearOrder.lift' e.symm e.symm.injective
  exact (isZero_simplicialHomology_top_succ (V := I) R n).of_iso
    (fullMapperHomologyIso f R (n + 1))

omit [LinearOrder (ComponentIndex f (fun _ : I => Set.univ))] in
/-- A one-label Mapper complex has no edges, for any target member or domain. -/
theorem isEmpty_mapper_face_one_of_unique [Unique I] (U : I → Set Y)
    [LinearOrder (ComponentIndex f U)] : IsEmpty (Face (mapper f U) 1) := by
  classical
  refine ⟨fun F => ?_⟩
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp F.2.2
  have hs := F.2.1
  rw [he] at hs
  exact hab (eq_of_mem_mapper_face_of_fst_eq f U hs (by simp) (by simp)
    (Subsingleton.elim _ _))

/-- For one full member, degree-zero homology counts the finitely many path components. -/
theorem finrank_simplicialHomology_mapper_full_zero_of_unique [Unique I]
    [Finite (ZerothHomotopy X)] (k : Type z) [Field k] :
    Module.finrank k (simplicialHomology (mapper f (fun _ : I => Set.univ)) k 0) =
      Nat.card (ZerothHomotopy X) := by
  classical
  let e := (fullComponentIndexEquiv (I := I) f).trans (Equiv.uniqueProd _ _)
  have : Finite (ComponentIndex f (fun _ : I => Set.univ)) := Finite.of_equiv _ e.symm
  let vertex (a : ComponentIndex f (fun _ : I => Set.univ)) :
      Face (mapper f (fun _ : I => Set.univ)) 0 :=
    ⟨{a}, componentIndex_supported f _ a, by simp⟩
  have hv : Function.Bijective vertex := by
    refine ⟨fun a b h => Finset.singleton_injective (congrArg Subtype.val h), fun F => ?_⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp F.2.2
    exact ⟨a, Subtype.ext ha.symm⟩
  let eF := (Equiv.ofBijective vertex hv).symm.trans e
  let : Fintype (Face (mapper f (fun _ : I => Set.univ)) 0) := Fintype.ofFinite _
  have := isEmpty_mapper_face_one_of_unique f (fun _ : I => Set.univ)
  rw [finrank_zeroHomology_of_no_edges, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr eF

omit [LinearOrder (ComponentIndex f (fun _ : I => Set.univ))] in
private theorem finrank_mapper_eq_full_zero [PathConnectedSpace X] [Finite I] [Nonempty I]
    (U : I → Set Y) [LinearOrder (ComponentIndex f U)] (hU : U = fun _ => Set.univ)
    (k : Type z) [Field k] :
    Module.finrank k (simplicialHomology (mapper f U) k 0) = 1 := by
  subst U
  exact finrank_simplicialHomology_mapper_full_zero f k

omit [LinearOrder (ComponentIndex f (fun _ : I => Set.univ))] in
private theorem isZero_mapper_eq_full_succ [PathConnectedSpace X] [Finite I]
    (U : I → Set Y) [LinearOrder (ComponentIndex f U)] (hU : U = fun _ => Set.univ)
    (k : Type z) [Field k] (n : ℕ) :
    IsZero (simplicialHomology (mapper f U) k (n + 1)) := by
  subst U
  exact isZero_simplicialHomology_mapper_full_succ f k n

omit [LinearOrder (ComponentIndex f (fun _ : I => Set.univ))] in
private theorem finrank_mapper_eq_full_zero_of_unique [Unique I] [Finite (ZerothHomotopy X)]
    (U : I → Set Y) [LinearOrder (ComponentIndex f U)] (hU : U = fun _ => Set.univ)
    (k : Type z) [Field k] :
    Module.finrank k (simplicialHomology (mapper f U) k 0) = Nat.card (ZerothHomotopy X) := by
  subst U
  exact finrank_simplicialHomology_mapper_full_zero_of_unique f k

end FullFamily

section Capped

variable {X : Type u} [TopologicalSpace X] {W : Type u} (k : Type u) [Field k]
  (f : C(X, ℝ)) (a s : ℝ) (ℓ : W → ℤ) {m : ℕ} (c : Fin (m + 1) ↪o ℝ)
  [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]

private theorem cappedLast_full :
    (fun w => (cappedCentredCover a s ℓ c (Fin.last (m + 1)) w : Set ℝ)) =
      fun _ => Set.univ := by
  funext w
  change (cappedCentredCover a s ℓ c (Fin.last m).succ w : Set ℝ) = Set.univ
  rw [cappedCentredCover_last a s ℓ c (Fin.last m) (by simp)]
  rfl

/-- On a path-connected domain, every capped centred diagram on a nonempty grid and finite
nonempty label window has one degree-zero essential bar. -/
theorem card_essentialPart_cappedCentredDiagram_zero [PathConnectedSpace X]
    [Finite W] [Nonempty W]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) 0)] :
    (essentialPart (cappedCentredDiagram k f a s ℓ c 0).points).card = 1 := by
  rw [cappedCentredDiagram, card_essentialPart_stepMapperDiagram]
  have : Nonempty (cappedIndex W (Fin.last (m + 1))) := inferInstanceAs (Nonempty W)
  exact finrank_mapper_eq_full_zero f _ (cappedLast_full a s ℓ c) k

/-- On a path-connected domain, a finite full cap kills every positive-degree essential bar. -/
theorem card_essentialPart_cappedCentredDiagram_succ [PathConnectedSpace X] [Finite W]
    (n : ℕ)
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) (n + 1))] :
    (essentialPart (cappedCentredDiagram k f a s ℓ c (n + 1)).points).card = 0 := by
  rw [cappedCentredDiagram, card_essentialPart_stepMapperDiagram]
  have := ModuleCat.subsingleton_of_isZero
    (isZero_mapper_eq_full_succ f _ (cappedLast_full a s ℓ c) k n)
  exact Module.finrank_zero_of_subsingleton

/-- For a single label, a nonempty capped grid records the number of path components in
its degree-zero essential multiplicity. -/
theorem card_essentialPart_cappedCentredDiagram_zero_of_unique [Unique W]
    [Finite (ZerothHomotopy X)]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) 0)] :
    (essentialPart (cappedCentredDiagram k f a s ℓ c 0).points).card =
      Nat.card (ZerothHomotopy X) := by
  rw [cappedCentredDiagram, card_essentialPart_stepMapperDiagram]
  let : Unique (cappedIndex W (Fin.last (m + 1))) := inferInstanceAs (Unique W)
  exact finrank_mapper_eq_full_zero_of_unique f _ (cappedLast_full a s ℓ c) k

variable [PathConnectedSpace X] [Finite W] [Nonempty W]
  {X' : Type u} [TopologicalSpace X'] [PathConnectedSpace X']
  {W' : Type u} [Finite W'] [Nonempty W'] (g : C(X', ℝ))
  (a' s' : ℝ) (ℓ' : W' → ℤ) {m' : ℕ} (d : Fin (m' + 1) ↪o ℝ)
  [∀ i, LinearOrder (ComponentIndex g fun w => (cappedCentredCover a' s' ℓ' d i w : Set ℝ))]
  (n : ℕ)
  [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
  [∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a' s' ℓ' d i w : Set ℝ)) n)]

/-- Capped centred diagrams of path-connected inputs have finite bottleneck distance in every
degree, for any nonempty grids and finite nonempty label windows. -/
theorem bottleneck_cappedCentredDiagram_lt_top :
    bottleneck (cappedCentredDiagram k f a s ℓ c n)
      (cappedCentredDiagram k g a' s' ℓ' d n) < ⊤ := by
  rw [bottleneck_lt_top_iff]
  cases n with
  | zero => rw [card_essentialPart_cappedCentredDiagram_zero,
      card_essentialPart_cappedCentredDiagram_zero]
  | succ n => rw [card_essentialPart_cappedCentredDiagram_succ,
      card_essentialPart_cappedCentredDiagram_succ]

end Capped

section GraphPL

variable {V : Type u} [Finite V] (G : SimpleGraph V) (h : V → ℝ)
  {W : Type u} [Finite W] (k : Type u) [Field k]
  (a s : ℝ) (ℓ : W → ℤ) {m : ℕ} (c : Fin (m + 1) ↪o ℝ)
  [∀ i, LinearOrder (ComponentIndex (TDA.Reeb.GraphPL.plHeight G h)
    fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]

/-- For connected finite graph input, the full cap leaves one degree-zero essential bar and
no positive-degree essential bars; all face-finiteness instances are synthesized. -/
theorem card_essentialPart_cappedCentredDiagram_plHeight [Nonempty W]
    (hG : G.Connected) (n : ℕ) :
    (essentialPart (cappedCentredDiagram k (TDA.Reeb.GraphPL.plHeight G h)
      a s ℓ c n).points).card = if n = 0 then 1 else 0 := by
  have : PathConnectedSpace (TDA.Reeb.GraphRealization.Realization G) :=
    (TDA.Reeb.GraphRealization.connected_iff_pathConnectedSpace G).mp hG
  cases n with
  | zero => exact card_essentialPart_cappedCentredDiagram_zero k _ a s ℓ c
  | succ n => exact card_essentialPart_cappedCentredDiagram_succ k _ a s ℓ c n

/-- With one label, the full cap counts the connected components of a finite graph. -/
theorem card_essentialPart_cappedCentredDiagram_plHeight_zero_of_unique [Unique W] :
    (essentialPart (cappedCentredDiagram k (TDA.Reeb.GraphPL.plHeight G h)
      a s ℓ c 0).points).card = Nat.card G.ConnectedComponent := by
  have : Finite (ZerothHomotopy (TDA.Reeb.GraphRealization.Realization G)) :=
    Finite.of_equiv _ (TDA.Reeb.GraphRealization.componentsEquiv G).symm
  exact (card_essentialPart_cappedCentredDiagram_zero_of_unique k _ a s ℓ c).trans
    (Nat.card_congr (TDA.Reeb.GraphRealization.componentsEquiv G))

end GraphPL

end
end TDA.Mapper
