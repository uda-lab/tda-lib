import TDA.Reeb.ConstructibleComparison
import TDA.Reeb.ConstructibleQuotientExamples

/-!
# Fixtures for the comparison on constructible inputs

Acceptance fixtures for `TDA.Reeb.ConstructibleComparison`, built on the constructible-space,
cylinder, finite-graph and quotient fixtures:

* **Constant-height interval.** For `[0, 1]` at one level the quotient projection `q` is not
  injective, while the comparison is an isomorphism with one element on each side over `ℝ`.
* **`∅`, rays and `ℝ`.** For two unattached pieces at one level, the quotient values have two
  elements over `ℝ` and over the rays that contain the level, and are empty over the rays that miss
  it. At `⊥` both values are empty and the comparison is bijective.
* **Empty space.** The comparison is an isomorphism and every quotient value is empty.
* **Branch and merge.** The thickened cycle over `0 < 1 < 2` has quotient counts `1, 2, 1` on the
  stars, whose end stars are rays, and `2` on each gap; the quotient's incidence maps into the
  bottom and top stars are not injective.
* **Branching at equal cardinality.** For the thickened pinch, the gap-to-star map is not injective
  although both sides have two elements, in the source and, through the comparison, in the quotient.
* **Graph case.** For parallel edges the comparison and its inverse are the path-component maps of
  the projection homeomorphism and its inverse, and the functor-level component is `𝒞` of the
  projection isomorphism.
* **Transport.** A refined single edge is constructible through an isomorphism to a presentation
  over a different list, and the comparison there is an isomorphism.
* **Height-dependent map.** The twist of the thickened parallel edges swaps the two edge components
  over the gap; its naturality squares hold for the comparison, its inverse and the functor-level
  isomorphism.

The general helpers `natCard_quotient` and `quotient_map_injective_iff` transfer cardinalities and
injectivity of structure maps from the source cosheaf to the quotient cosheaf.
-/

open Set Topology CategoryTheory

namespace TDA.Reeb

noncomputable section

namespace Examples.ConstructibleComparison

open CylinderPresentation TDA.Reeb.Examples.Cylinder TDA.Reeb.Examples.ConstructibleQuotient
open TDA.Reeb.Examples.ConstructibleCylinder (S0 D0 S012 natCard_zerothHomotopy_discrete)
open RGraph.Examples (cycleData singleEdge Shalf S01_sub_Shalf)

attribute [local instance] locallyPathConnectedSpace_unitInterval pathConnectedSpace_unitInterval

/-! ### Helpers -/

section helpers

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{0} n)
  [∀ i, Finite (ZerothHomotopy (P.V i))] [∀ e, Finite (ZerothHomotopy (P.E e))]
  [∀ i, LocallyPathConnectedSpace (P.V i)] [∀ e, LocallyPathConnectedSpace (P.E e)]

/-- The quotient cosheaf has the cardinalities of the source cosheaf. -/
theorem natCard_quotient (I : OpenInterval) :
    Nat.card ((intervalComponents (ReebQuotient.height (P.height S))).obj I) =
      Nat.card ((intervalComponents (P.height S)).obj I) :=
  (Nat.card_congr (Equiv.ofBijective _ (P.bijective_intervalComponentComparison_app S I))).symm

/-- A structure map of the quotient cosheaf is injective exactly when that of the source is. -/
theorem quotient_map_injective_iff {I J : OpenInterval} (hIJ : I ≤ J) :
    Function.Injective
        ((intervalComponents (ReebQuotient.height (P.height S))).map (homOfLE hIJ)) ↔
      Function.Injective ((intervalComponents (P.height S)).map (homOfLE hIJ)) := by
  have key : ∀ x, (intervalComponents (ReebQuotient.height (P.height S))).map (homOfLE hIJ)
      ((ReebQuotient.intervalComponentComparison (P.height S)).app I x) =
      (ReebQuotient.intervalComponentComparison (P.height S)).app J
        ((intervalComponents (P.height S)).map (homOfLE hIJ) x) := fun x =>
    (NatTrans.naturality_apply (ReebQuotient.intervalComponentComparison (P.height S))
      (homOfLE hIJ) x).symm
  have hI := P.bijective_intervalComponentComparison_app S I
  have hJ := P.bijective_intervalComponentComparison_app S J
  constructor
  · intro h x y hxy
    exact hI.1 (h (by rw [key, key, hxy]))
  · intro h x y hxy
    obtain ⟨x, rfl⟩ := hI.2 x
    obtain ⟨y, rfl⟩ := hI.2 y
    rw [key, key] at hxy
    exact congrArg _ (h (hJ.1 hxy))

theorem natCard_bool : Nat.card Bool = 2 := by simp

end helpers

section thickenCards

variable {n : ℕ} (S : CriticalValues n) (D : FiniteReebData.{0} n)

/-- For a thickening, the quotient cosheaf at the star `J i` has as many elements as `D.V i`. -/
theorem thicken_quotient_card_J (i : Fin (n + 1)) :
    Nat.card ((intervalComponents (ReebQuotient.height ((thicken D).height S))).obj (S.J i)) =
      Nat.card (D.V i) := by
  rw [natCard_quotient, ← Nat.card_congr ((thicken D).vertexComponentsEquiv S i)]
  exact (Nat.card_congr (Equiv.ofBijective _ (mk_prod_zero_bijective ((ofFiniteData D).V i)))).symm

/-- For a thickening, the quotient cosheaf at the gap `K e` has as many elements as `D.E e`. -/
theorem thicken_quotient_card_K (e : Fin n) :
    Nat.card ((intervalComponents (ReebQuotient.height ((thicken D).height S))).obj (S.K e)) =
      Nat.card (D.E e) := by
  rw [natCard_quotient,
    ← Nat.card_congr ((thicken D).edgeComponentsEquiv S e (RGraph.basePt S e))]
  exact (Nat.card_congr (Equiv.ofBijective _ (mk_prod_zero_bijective ((ofFiniteData D).E e)))).symm

end thickenCards

/-! ### A constant-height interval: `q` is not injective, the comparison is an isomorphism -/

/-- The quotient projection of `[0, 1]` at one level is not injective. -/
theorem interval_proj_not_injective :
    ¬ Function.Injective (ReebQuotient.mk (intervalPres.height S0)) :=
  fun h => interval_ofVertex_zero_ne_one (h (interval_collapse 0 1))

theorem interval_isIso :
    IsIso (ReebQuotient.intervalComponentComparison (intervalPres.height S0)) :=
  inferInstance

/-- Over `ℝ`, the source has one component ... -/
theorem interval_card_top :
    Nat.card ((intervalComponents (intervalPres.height S0)).obj ⊤) = 1 := by
  rw [← S0.J_eq_top_of_zero, ← Nat.card_congr (intervalPres.vertexComponentsEquiv S0 0)]
  exact interval_componentData_card

/-- ... and so has the quotient. -/
theorem interval_quotient_card_top :
    Nat.card ((intervalComponents (ReebQuotient.height (intervalPres.height S0))).obj ⊤) = 1 :=
  (natCard_quotient S0 intervalPres ⊤).trans interval_card_top

/-! ### `∅`, rays and `ℝ`: two unattached pieces at one level -/

/-- `ℝ`: the quotient cosheaf has two elements. -/
theorem twoPieces_quotient_card_top :
    Nat.card ((intervalComponents (ReebQuotient.height (twoPieces.height S0))).obj ⊤) = 2 := by
  rw [← S0.J_eq_top_of_zero]
  exact (thicken_quotient_card_J S0 D0 0).trans (Nat.card_fin 2)

/-- The ray `(-∞, 1)` contains the level. -/
theorem twoPieces_quotient_card_iio :
    Nat.card ((intervalComponents (ReebQuotient.height (twoPieces.height S0))).obj
      (OpenInterval.iio 1)) = 2 :=
  (Nat.card_congr (Equiv.ofBijective _
    ((twoPieces.isConstructibleAt_intervalComponents_reebQuotient S0).bijective
      (le_top : OpenInterval.iio 1 ≤ ⊤) ⟨0, show (0 : ℝ) < 1 by norm_num⟩
      fun _ => iff_of_true (show (0 : ℝ) < 1 by norm_num) trivial))).trans
    twoPieces_quotient_card_top

/-- The ray `(-1, ∞)` contains the level. -/
theorem twoPieces_quotient_card_ioi :
    Nat.card ((intervalComponents (ReebQuotient.height (twoPieces.height S0))).obj
      (OpenInterval.ioi (-1))) = 2 :=
  (Nat.card_congr (Equiv.ofBijective _
    ((twoPieces.isConstructibleAt_intervalComponents_reebQuotient S0).bijective
      (le_top : OpenInterval.ioi (-1) ≤ ⊤) ⟨0, show (-1 : ℝ) < 0 by norm_num⟩
      fun _ => iff_of_true (show (-1 : ℝ) < 0 by norm_num) trivial))).trans
    twoPieces_quotient_card_top

/-- The rays `(-∞, 0)` and `(0, ∞)` miss the level: empty quotient values. -/
theorem twoPieces_quotient_iio_zero_isEmpty :
    IsEmpty ((intervalComponents (ReebQuotient.height (twoPieces.height S0))).obj
      (OpenInterval.iio 0)) :=
  (twoPieces.isConstructibleAt_intervalComponents_reebQuotient S0).isEmpty_lowerTail

theorem twoPieces_quotient_ioi_zero_isEmpty :
    IsEmpty ((intervalComponents (ReebQuotient.height (twoPieces.height S0))).obj
      (OpenInterval.ioi 0)) :=
  (twoPieces.isConstructibleAt_intervalComponents_reebQuotient S0).isEmpty_upperTail

/-- `∅`: both values are empty and the comparison is bijective. -/
theorem twoPieces_bot :
    IsEmpty ((intervalComponents (twoPieces.height S0)).obj ⊥) ∧
      IsEmpty ((intervalComponents (ReebQuotient.height (twoPieces.height S0))).obj ⊥) ∧
        Function.Bijective
          ((ReebQuotient.intervalComponentComparison (twoPieces.height S0)).app ⊥) :=
  ⟨inferInstance, inferInstance, twoPieces.bijective_intervalComponentComparison_app S0 ⊥⟩

/-! ### The empty space -/

theorem emptyThick_isIso :
    IsIso (ReebQuotient.intervalComponentComparison ((thicken (emptyData 1)).height S01)) :=
  inferInstance

theorem emptyThick_quotient_isEmpty_obj (I : OpenInterval) :
    IsEmpty ((intervalComponents
      (ReebQuotient.height ((thicken (emptyData 1)).height S01))).obj I) :=
  have := emptyThick_quotient_isEmpty
  componentFunctor_obj_isEmpty_of_isEmpty _ _

/-! ### Branch and merge: the thickened cycle over `0 < 1 < 2` -/

/-- The cycle with one vertex at `0`, two at `1`, one at `2` and two edges per gap, thickened by
`[0, 1]`: a branch at level `0` and a merge at level `2`. -/
abbrev cycleI : CylinderPresentation.{0} 2 := thicken cycleData

theorem cycleI_isConstructibleSpace :
    IsConstructibleSpace (Over.mk (TopCat.ofHom (cycleI.height S012))) :=
  thicken_isConstructibleSpace S012 cycleData

theorem cycleI_isIso : IsIso (ReebQuotient.intervalComponentComparison (cycleI.height S012)) :=
  inferInstance

/-- The star `J 0 = (-∞, 1)` is a ray. -/
theorem S012_J0_mem_iff (x : ℝ) : x ∈ S012.J 0 ↔ x < 1 := by
  rw [S012.mem_J_iff]
  constructor
  · intro h
    simpa [S012] using h.2 1 rfl
  · intro h
    refine ⟨fun k hk => by simp at hk, fun k hk => ?_⟩
    obtain rfl : k = 1 := Fin.ext (by simpa using hk.symm)
    simpa [S012] using h

/-- The star `J 2 = (1, ∞)` is a ray. -/
theorem S012_J2_mem_iff (x : ℝ) : x ∈ S012.J 2 ↔ 1 < x := by
  rw [S012.mem_J_iff]
  constructor
  · intro h
    simpa [S012] using h.1 1 rfl
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => by have := k.isLt; simp at hk; omega⟩
    obtain rfl : k = 1 := Fin.ext (by simpa using hk)
    simpa [S012] using h

/-- Branch vertex: one component on the ray `J 0`. -/
theorem cycleI_quotient_card_J0 :
    Nat.card ((intervalComponents (ReebQuotient.height (cycleI.height S012))).obj (S012.J 0)) =
      1 :=
  (thicken_quotient_card_J S012 cycleData 0).trans (Nat.card_fin _)

theorem cycleI_quotient_card_J1 :
    Nat.card ((intervalComponents (ReebQuotient.height (cycleI.height S012))).obj (S012.J 1)) =
      2 :=
  (thicken_quotient_card_J S012 cycleData 1).trans (Nat.card_fin _)

/-- Merge vertex: one component on the ray `J 2`. -/
theorem cycleI_quotient_card_J2 :
    Nat.card ((intervalComponents (ReebQuotient.height (cycleI.height S012))).obj (S012.J 2)) =
      1 :=
  (thicken_quotient_card_J S012 cycleData 2).trans (Nat.card_fin _)

theorem cycleI_quotient_card_K0 :
    Nat.card ((intervalComponents (ReebQuotient.height (cycleI.height S012))).obj (S012.K 0)) =
      2 :=
  (thicken_quotient_card_K S012 cycleData 0).trans (Nat.card_fin _)

theorem cycleI_quotient_card_K1 :
    Nat.card ((intervalComponents (ReebQuotient.height (cycleI.height S012))).obj (S012.K 1)) =
      2 :=
  (thicken_quotient_card_K S012 cycleData 1).trans (Nat.card_fin _)

/-- The incidence inclusion of the lower gap into the bottom star. -/
theorem S012_K0_le_J0 : S012.K 0 ≤ S012.J 0 := S012.K_le_J_castSucc 0

/-- The incidence inclusion of the upper gap into the top star. -/
theorem S012_K1_le_J2 : S012.K 1 ≤ S012.J 2 := S012.K_le_J_succ 1

/-- The two lower branches meet in the star of the bottom vertex. -/
theorem cycleI_quotient_branch_not_injective :
    ¬ Function.Injective ((intervalComponents (ReebQuotient.height (cycleI.height S012))).map
      (homOfLE S012_K0_le_J0)) := fun h => by
  have := (cycleI.isConstructibleAt_intervalComponents_reebQuotient S012).finite (S012.J 0)
  have hle : Nat.card ((intervalComponents
        (ReebQuotient.height (cycleI.height S012))).obj (S012.K 0)) ≤
      Nat.card ((intervalComponents (ReebQuotient.height (cycleI.height S012))).obj (S012.J 0)) :=
    Nat.card_le_card_of_injective _ h
  rw [cycleI_quotient_card_K0, cycleI_quotient_card_J0] at hle
  omega

/-- The two upper branches meet in the star of the top vertex. -/
theorem cycleI_quotient_merge_not_injective :
    ¬ Function.Injective ((intervalComponents (ReebQuotient.height (cycleI.height S012))).map
      (homOfLE S012_K1_le_J2)) := fun h => by
  have := (cycleI.isConstructibleAt_intervalComponents_reebQuotient S012).finite (S012.J 2)
  have hle : Nat.card ((intervalComponents
        (ReebQuotient.height (cycleI.height S012))).obj (S012.K 1)) ≤
      Nat.card ((intervalComponents (ReebQuotient.height (cycleI.height S012))).obj (S012.J 2)) :=
    Nat.card_le_card_of_injective _ h
  rw [cycleI_quotient_card_K1, cycleI_quotient_card_J2] at hle
  omega

/-! ### Branching at equal cardinality: the thickened pinch -/

theorem pinchI_isIso : IsIso (ReebQuotient.intervalComponentComparison (pinchI.height S01)) :=
  inferInstance

theorem pinchI_quotient_card_J0 :
    Nat.card ((intervalComponents (ReebQuotient.height (pinchI.height S01))).obj (S01.J 0)) = 2 :=
  (thicken_quotient_card_J S01 pinchData 0).trans natCard_bool

theorem pinchI_quotient_card_K0 :
    Nat.card ((intervalComponents (ReebQuotient.height (pinchI.height S01))).obj (S01.K 0)) = 2 :=
  (thicken_quotient_card_K S01 pinchData 0).trans natCard_bool

/-- In the source, both edges reach the bottom vertex `false`: the gap-to-star map is not
injective although both sides have two elements. -/
theorem pinchI_source_branch_not_injective :
    ¬ Function.Injective ((intervalComponents (pinchI.height S01)).map
      (homOfLE (S01.K_le_J_castSucc 0))) := fun h => by
  have e1 := pinchI.map_K_le_J_castSucc_edgeComponentsEquiv S01 0 half
    (ZerothHomotopy.mk ((false : Bool), (0 : unitInterval)))
  have e2 := pinchI.map_K_le_J_castSucc_edgeComponentsEquiv S01 0 half
    (ZerothHomotopy.mk ((true : Bool), (0 : unitInterval)))
  have hmk := (pinchI.edgeComponentsEquiv S01 0 half).injective (h (e1.trans e2.symm))
  exact Bool.false_ne_true ((thicken_edgeClass_eq_iff pinchData 0 false true 0 0).1 hmk)

/-- The quotient cosheaf has the same branching, through the comparison. -/
theorem pinchI_quotient_branch_not_injective :
    ¬ Function.Injective ((intervalComponents (ReebQuotient.height (pinchI.height S01))).map
      (homOfLE (S01.K_le_J_castSucc 0))) := fun h =>
  pinchI_source_branch_not_injective ((quotient_map_injective_iff S01 pinchI _).1 h)

/-! ### The graph case agrees with the projection isomorphism -/

theorem parallel_comparison_eq_projHomeomorph :
    ReebQuotient.intervalComponentComparison ((ofFiniteData parallelData).height S01) =
      intervalComponentNatTrans (RGraph.projHomeomorph S01 parallelData : C(_, _))
        (RGraph.height_projHomeomorph S01 parallelData) :=
  intervalComponentComparison_ofFiniteData S01 parallelData

theorem parallel_inv_comparison_eq_projInv :
    inv (ReebQuotient.intervalComponentComparison ((ofFiniteData parallelData).height S01)) =
      intervalComponentNatTrans (RGraph.projInv S01 parallelData)
        (height_projInv S01 parallelData) :=
  inv_intervalComponentComparison_ofFiniteData S01 parallelData

theorem parallel_isRGraph : RGraph.IsRGraph (RGraph.toOver S01 parallelData) :=
  ⟨1, S01, parallelData, ⟨Iso.refl _⟩⟩

theorem parallel_comparisonIso_eq_projNatIso :
    constructibleComponentComparisonIso.app
        ⟨RGraph.toOver S01 parallelData, isConstructibleSpace_of_isRGraph parallel_isRGraph⟩ =
      intervalComponentsOver.mapIso
        (RGraph.projNatIso.app ⟨_, parallel_isRGraph⟩) :=
  constructibleComponentComparisonIso_app_of_isRGraph parallel_isRGraph

/-- The two parallel edges remain two components of the quotient over the gap. -/
theorem parallel_quotient_card_K0 :
    Nat.card ((intervalComponents
      (ReebQuotient.height ((ofFiniteData parallelData).height S01))).obj (S01.K 0)) = 2 := by
  rw [natCard_quotient,
    ← Nat.card_congr ((ofFiniteData parallelData).edgeComponentsEquiv S01 0 half),
    natCard_zerothHomotopy_discrete]
  exact natCard_bool

/-! ### Transport: an object presented through an isomorphism over a different list -/

/-- The single edge refined over `0 < 1/2 < 1` is constructible through the refinement
isomorphism `RGraph.refineIso` to the single edge over `0 < 1`. -/
theorem refinedSingleEdge_isConstructibleSpace :
    IsConstructibleSpace (RGraph.toOver Shalf (RGraph.refineData S01_sub_Shalf singleEdge)) :=
  ⟨1, S01, ofFiniteData singleEdge, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance,
    ⟨RGraph.refineIso S01_sub_Shalf singleEdge⟩⟩

theorem refinedSingleEdge_isIso :
    IsIso (ReebQuotient.intervalComponentComparison
      (overBaseMap (RGraph.toOver Shalf (RGraph.refineData S01_sub_Shalf singleEdge)))) :=
  isIso_intervalComponentComparison_of_constructible refinedSingleEdge_isConstructibleSpace

/-! ### Naturality for a height-dependent map: the twist of the thickened parallel edges -/

theorem twist_comparison_natural :
    intervalComponentNatTrans twist height_twist ≫
        ReebQuotient.intervalComponentComparison (parallelI.height S01) =
      ReebQuotient.intervalComponentComparison (parallelI.height S01) ≫
        intervalComponentNatTrans (ReebQuotient.map twist height_twist)
          (ReebQuotient.height_map_apply twist height_twist) :=
  ReebQuotient.intervalComponentComparison_natural twist height_twist

theorem twist_inv_comparison_natural :
    intervalComponentNatTrans (ReebQuotient.map twist height_twist)
          (ReebQuotient.height_map_apply twist height_twist) ≫
        inv (ReebQuotient.intervalComponentComparison (parallelI.height S01)) =
      inv (ReebQuotient.intervalComponentComparison (parallelI.height S01)) ≫
        intervalComponentNatTrans twist height_twist :=
  ReebQuotient.inv_intervalComponentComparison_natural twist height_twist

/-- On the gap, the twist swaps the two edge components of the source ... -/
theorem twist_source_gap (b : Bool) (s : unitInterval) :
    (componentNatTrans twist height_twist).app (OpenInterval.toOpens (S01.K 0))
        (parallelI.edgeComponentsEquiv S01 0 half (ZerothHomotopy.mk (b, s))) =
      parallelI.edgeComponentsEquiv S01 0 half (ZerothHomotopy.mk (!b, s)) := by
  rw [componentNatTrans_edgeComponentsEquiv]
  congr 1
  show ZerothHomotopy.mk (regularFiberMap S01 twist height_twist 0 half (b, s)) = _
  rw [twist_regularFiberMap]
  exact (thicken_edgeClass_eq_iff parallelData 0 _ _ _ _).2 rfl

/-- ... and, through the comparison, those of the quotient. -/
theorem twist_quotient_gap (b : Bool) (s : unitInterval) :
    (componentNatTrans (ReebQuotient.map twist height_twist)
        (ReebQuotient.height_map_apply twist height_twist)).app (OpenInterval.toOpens (S01.K 0))
        ((ReebQuotient.intervalComponentComparison (parallelI.height S01)).app (S01.K 0)
          (parallelI.edgeComponentsEquiv S01 0 half (ZerothHomotopy.mk (b, s)))) =
      (ReebQuotient.intervalComponentComparison (parallelI.height S01)).app (S01.K 0)
        (parallelI.edgeComponentsEquiv S01 0 half (ZerothHomotopy.mk (!b, s))) :=
  congrArg ((ReebQuotient.intervalComponentComparison (parallelI.height S01)).app (S01.K 0))
    (twist_source_gap b s)

/-- The thickened parallel edges as a constructible ℝ-space. -/
def parallelIObj : ConstructibleSpaceCat :=
  ⟨_, thicken_isConstructibleSpace S01 parallelData⟩

/-- The twist as a morphism of constructible ℝ-spaces. -/
def twistHom : parallelIObj ⟶ parallelIObj := ObjectProperty.homMk twistOver

theorem twist_constructible_natural :
    intervalComponentsOver.map twistHom.hom ≫
        constructibleComponentComparisonIso.hom.app parallelIObj =
      constructibleComponentComparisonIso.hom.app parallelIObj ≫
        intervalComponentsOver.map
          ((ReebQuotient.quotientFunctor ℝ).map twistHom.hom) :=
  constructibleComponentComparison_naturality twistHom

end Examples.ConstructibleComparison

end

end TDA.Reeb
