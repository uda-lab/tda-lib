import TDA.Mapper.GraphPLReebData
import TDA.Mapper.GraphPLLevelSets
import TDA.Reeb.ConstructibleRepresentation
import TDA.Reeb.RGraphCosheafEquivalence
import TDA.Reeb.GeometricInterleavingEquivalence
import TDA.Reeb.InterleavingDistance

/-!
# Constructibility and cosheaf identification for graph-PL height

For a graph-PL height, the path-component precosheaf is constructible at every covering list:
the key comparison is the cell-graph isomorphism for nested intervals with the same levels.  The
same comparison identifies it with the cosheaf of the finite Reeb data as the labelled lift
`toCosheafLift`, and gives the corresponding constructible-cosheaf, functorial, and distance
corollaries.  The statements using finite Reeb data and `IsIntervalCosheaf.{0}` are restricted to
universe `0`.

The shapes used here are DMP Definition 3.9, with the library's nonempty-source correction, and
Proposition 3.18.  The graph-PL statements are library results and make no external source claim.
The Reeb quotient homeomorphism of the realization is proved in `TDA.Mapper.GraphPLReebQuotient`.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Reeb.RGraph

noncomputable section

variable {V : Type} (G : SimpleGraph V) (h : V → ℝ) {n : ℕ}
  {S : CriticalValues n}

/-! ## Constructibility -/

section without_finite

/-- A covering list sees the same vertex heights in nested intervals with the same levels. -/
theorem CoversVertexHeights.vertex_mem_iff (hS : CoversVertexHeights S h) {I J : OpenInterval}
    (hIJ : I ≤ J) (hlev : ∀ i, S.value i ∈ I ↔ S.value i ∈ J) (v : V) :
    h v ∈ I ↔ h v ∈ J := by
  obtain ⟨i, hi⟩ := hS v
  simpa [hi] using hlev i

/-- Under a covering list, edge activity is unchanged by a same-level interval enlargement. -/
theorem CoversVertexHeights.edgeActive_iff (hS : CoversVertexHeights S h) {I J : OpenInterval}
    (hIJ : I ≤ J) (hI : (I : Set ℝ).Nonempty) (hlev : ∀ i, S.value i ∈ I ↔ S.value i ∈ J)
    (e : G.edgeSet) : EdgeActive G h I e ↔ EdgeActive G h J e := by
  have hlevel : ∀ v, h v ∈ J → h v ∈ I := by
    intro v hv
    obtain ⟨i, hi⟩ := hS v
    rw [← hi] at hv ⊢
    exact (hlev i).2 hv
  constructor
  · exact EdgeActive.mono hIJ
  · intro he
    obtain ⟨x, hxI⟩ := hI
    have hxJ : x ∈ J := OpenInterval.le_iff_subset.1 hIJ hxI
    obtain ⟨d, hd⟩ := exists_dartEdge_eq e
    have handle : ∀ (d : G.Dart), dartEdge d = e →
        h d.fst ≤ h d.snd →
        (∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h d t ∈ J) →
        EdgeActive G h I e := by
      intro d hd hpq ht
      obtain ⟨t, ht₀, ht₁, hyt⟩ := ht
      have hyseg : h d.fst ≤ dartHeight h d t ∧ dartHeight h d t ≤ h d.snd := by
        change h d.fst ≤ (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ∧
          (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ≤ h d.snd
        have ht_nonneg : 0 ≤ (t : ℝ) := ht₀.le
        have hone_minus_t_nonneg : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr ht₁.le
        have hgap : 0 ≤ h d.snd - h d.fst := sub_nonneg.mpr hpq
        have hmul_t := mul_nonneg ht_nonneg hgap
        have hmul_one_minus_t := mul_nonneg hone_minus_t_nonneg hgap
        constructor <;> linarith
      by_cases hpI : h d.fst ∈ I
      · rw [← hd]
        exact edgeActive_of_mem (fst_mem_dartEdge d) hpI
      by_cases hqI : h d.snd ∈ I
      · rw [← hd]
        exact edgeActive_of_mem (snd_mem_dartEdge d) hqI
      by_cases hxp : x ≤ h d.fst
      · have hpJ : h d.fst ∈ J :=
          mem_of_le_of_le hxJ hyt hxp hyseg.1
        exact False.elim (hpI (hlevel d.fst hpJ))
      by_cases hqx : h d.snd ≤ x
      · have hqJ : h d.snd ∈ J :=
          mem_of_le_of_le hyt hxJ hyseg.2 hqx
        exact False.elim (hqI (hlevel d.snd hqJ))
      · have hpx : h d.fst < x := lt_of_not_ge hxp
        have hxq : x < h d.snd := lt_of_not_ge hqx
        have hcross : dartHeight h d (crossingParam G h hpx hxq) ∈ I := by
          rw [dartHeight_crossingParam]
          exact hxI
        rw [← hd]
        exact edgeActive_dartEdge_of_mem hcross
    rcases le_total (h d.fst) (h d.snd) with hpq | hqp
    · exact handle d hd hpq (he.exists_mem hd)
    · have hd' : dartEdge d.symm = e := by simpa [dartEdge_symm] using hd
      exact handle d.symm hd' (by simpa using hqp) (he.exists_mem hd')

/-- The cell inclusion is an isomorphism when the two intervals contain the same levels. -/
def cellGraphIsoOfSameLevels (hS : CoversVertexHeights S h) {I J : OpenInterval} (hIJ : I ≤ J)
    (hI : (I : Set ℝ).Nonempty) (hlev : ∀ i, S.value i ∈ I ↔ S.value i ∈ J) :
    cellGraph G h I ≃g cellGraph G h J :=
  { toEquiv :=
      { toFun := fun x => cellInclusion G h hIJ x
        invFun := Sum.map
          (fun v => ⟨v.1, (CoversVertexHeights.vertex_mem_iff h hS hIJ hlev v.1).2 v.2⟩)
          (fun e =>
            ⟨e.1, (CoversVertexHeights.edgeActive_iff G h hS hIJ hI hlev e.1).2 e.2⟩)
        left_inv := by
          intro x
          cases x <;> rfl
        right_inv := by
          intro x
          cases x <;> rfl }
    map_rel_iff' := by
      intro x y
      cases x <;> cases y <;> rfl }

/-- The underlying function of the same-level cell isomorphism is the cell inclusion. -/
theorem cellGraphIsoOfSameLevels_apply (hS : CoversVertexHeights S h) {I J : OpenInterval}
    (hIJ : I ≤ J) (hI : (I : Set ℝ).Nonempty) (hlev : ∀ i, S.value i ∈ I ↔ S.value i ∈ J) :
    ⇑(cellGraphIsoOfSameLevels G h hS hIJ hI hlev) = cellInclusion G h hIJ := rfl

/-- The interval-component map is bijective across same-level intervals. -/
theorem intervalComponents_plHeight_map_bijective (hS : CoversVertexHeights S h)
    {I J : OpenInterval} (hIJ : I ≤ J) (hI : (I : Set ℝ).Nonempty)
    (hlev : ∀ i, S.value i ∈ I ↔ S.value i ∈ J) :
    Function.Bijective ((intervalComponents (plHeight G h)).map (homOfLE hIJ)) := by
  let e := cellGraphIsoOfSameLevels G h hS hIJ hI hlev
  have hcell : Function.Bijective ((cellComponentFunctor G h).map (homOfLE hIJ)) := by
    have hcell_eq :
        ((cellComponentFunctor G h).map (homOfLE hIJ) :
          (cellGraph G h I).ConnectedComponent → (cellGraph G h J).ConnectedComponent) =
          e.connectedComponentEquiv := by
      funext c
      exact (cellComponentFunctor_map_apply G h (homOfLE hIJ) c).trans rfl
    rw [hcell_eq]
    exact e.connectedComponentEquiv.bijective
  let e' := (intervalComponentsIso G h).symm
  have hmap' :
      ⇑((intervalComponents (plHeight G h)).map (homOfLE hIJ)) =
        e'.hom.app J ∘
          (cellComponentFunctor G h).map (homOfLE hIJ) ∘ e'.inv.app I := by
    funext x
    simp only [Function.comp_apply]
    rw [NatTrans.naturality_apply, Iso.inv_hom_id_app_apply]
  have hmap :
      ⇑((intervalComponents (plHeight G h)).map (homOfLE hIJ)) =
        (intervalComponentsIso G h).inv.app J ∘
          (cellComponentFunctor G h).map (homOfLE hIJ) ∘
            (intervalComponentsIso G h).hom.app I := by
    simpa [e'] using hmap'
  rw [hmap]
  exact ((isIso_iff_bijective ((intervalComponentsIso G h).inv.app J)).1 inferInstance).comp
    (hcell.comp
      ((isIso_iff_bijective ((intervalComponentsIso G h).hom.app I)).1 inferInstance))

private theorem graphPL_vertex_mem_Icc (hS : CoversVertexHeights S h) (v : V) :
    h v ∈ Set.Icc (S.value 0) (S.value (Fin.last n)) := by
  obtain ⟨i, hi⟩ := hS v
  simpa [hi] using
    (⟨S.strictMono.monotone (Fin.zero_le i), S.strictMono.monotone (Fin.le_last i)⟩ :
      S.value 0 ≤ S.value i ∧ S.value i ≤ S.value (Fin.last n))

end without_finite

section with_finite

variable [Finite V]

/-- The graph-PL path-component precosheaf is constructible at every covering list. -/
theorem isConstructibleAt_intervalComponents_plHeight (hS : CoversVertexHeights S h) :
    S.IsConstructibleAt (intervalComponents (plHeight G h)) where
  finite := fun I => finite_zerothHomotopy G h I
  bijective := fun _ _ hIJ hI hlev =>
    intervalComponents_plHeight_map_bijective G h hS hIJ hI hlev
  isEmpty_lowerTail := ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x =>
      have hx := x.2
      exact (not_lt_of_ge (plHeight_mem_Icc_of_forall
        (fun v => graphPL_vertex_mem_Icc h hS v) x.1).1) (mem_iio.1 hx)⟩
  isEmpty_upperTail := ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x =>
      have hx := x.2
      exact (not_lt_of_ge (plHeight_mem_Icc_of_forall
        (fun v => graphPL_vertex_mem_Icc h hS v) x.1).2) (mem_ioi.1 hx)⟩

/-! ## Identification with finite Reeb data -/

/-- Every vertex component of an isomorphism of finite Reeb data is bijective. -/
theorem _root_.TDA.Reeb.FiniteReebData.Hom.bijective_v_of_iso
    {D D' : FiniteReebData.{0} n} (e : D ≅ D') (i) :
    Function.Bijective (e.hom.v i) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.v i, ?_, ?_⟩
  · intro x
    change (e.hom ≫ e.inv).v i x = (𝟙 D : D ⟶ D).v i x
    rw [e.hom_inv_id]
  · intro x
    change (e.inv ≫ e.hom).v i x = (𝟙 D' : D' ⟶ D').v i x
    rw [e.inv_hom_id]

/-- Every edge component of an isomorphism of finite Reeb data is bijective. -/
theorem _root_.TDA.Reeb.FiniteReebData.Hom.bijective_e_of_iso
    {D D' : FiniteReebData.{0} n} (e : D ≅ D') (k) :
    Function.Bijective (e.hom.e k) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.e k, ?_, ?_⟩
  · intro x
    change (e.hom ≫ e.inv).e k x = (𝟙 D : D ⟶ D).e k x
    rw [e.hom_inv_id]
  · intro x
    change (e.inv ≫ e.hom).e k x = (𝟙 D' : D' ⟶ D').e k x
    rw [e.inv_hom_id]

private theorem graphPLExtractIso_inv_v (hS : CoversVertexHeights S h)
    (i : Fin (n + 1)) (x : LevelVertex G h (S.value i)) :
    (graphPLExtractIso G h S hS).inv.v i x = (graphPLStarEquiv G h S hS i).symm x := by
  change (Equiv.ofBijective (graphPLStarEquiv G h S hS i) _).symm x = _
  apply (graphPLStarEquiv G h S hS i).injective
  exact (Equiv.ofBijective_apply_symm_apply
      (graphPLStarEquiv G h S hS i) (graphPLStarEquiv G h S hS i).bijective x).trans
    ((graphPLStarEquiv G h S hS i).apply_symm_apply x).symm

private theorem graphPLExtractIso_inv_e (hS : CoversVertexHeights S h)
    (k : Fin n) (x : SpanEdge G h (S.value k.castSucc) (S.value k.succ)) :
    (graphPLExtractIso G h S hS).inv.e k x = (graphPLGapEquiv G h S hS k).symm x := by
  change (Equiv.ofBijective (graphPLGapEquiv G h S hS k) _).symm x = _
  apply (graphPLGapEquiv G h S hS k).injective
  exact (Equiv.ofBijective_apply_symm_apply
      (graphPLGapEquiv G h S hS k) (graphPLGapEquiv G h S hS k).bijective x).trans
    ((graphPLGapEquiv G h S hS k).apply_symm_apply x).symm

private def graphPLLift (hS : CoversVertexHeights S h)
    {D : FiniteReebData.{0} n} (e : D ≅ graphPLReebData G h S) :
    D.toCosheaf S ⟶ intervalComponents (plHeight G h) :=
  D.toCosheafLift
    (isConstructibleAt_intervalComponents_plHeight G h hS)
    (intervalComponents_isIntervalCosheaf _)
    (e.hom ≫ (graphPLExtractIso G h S hS).inv)

private theorem isIso_graphPLLift (hS : CoversVertexHeights S h)
    {D : FiniteReebData.{0} n} (e : D ≅ graphPLReebData G h S) :
    IsIso (graphPLLift G h hS e) := by
  let hF := isConstructibleAt_intervalComponents_plHeight G h hS
  let hFc : IsIntervalCosheaf.{0} (intervalComponents (plHeight G h)) :=
    intervalComponents_isIntervalCosheaf _
  let j : D.Hom (S.extract (intervalComponents (plHeight G h)) hF.finite) :=
    e.hom ≫ (graphPLExtractIso G h S hS).inv
  change IsIso (D.toCosheafLift hF hFc j)
  apply D.isIso_toCosheafLift hF hFc j
  · intro i
    simpa [j] using
      (_root_.TDA.Reeb.FiniteReebData.Hom.bijective_v_of_iso
        (e ≪≫ (graphPLExtractIso G h S hS).symm) i)
  · intro k
    simpa [j] using
      (_root_.TDA.Reeb.FiniteReebData.Hom.bijective_e_of_iso
        (e ≪≫ (graphPLExtractIso G h S hS).symm) k)

/-- The labelled lift identifies arbitrary finite Reeb data with graph-PL components. -/
noncomputable def graphPLCosheafIsoOfIso (hS : CoversVertexHeights S h)
    {D : FiniteReebData.{0} n} (e : D ≅ graphPLReebData G h S) :
    D.toCosheaf S ≅ intervalComponents (plHeight G h) :=
  @asIso _ _ _ _ (graphPLLift G h hS e) (isIso_graphPLLift G h hS e)

private theorem graphPLCosheafIsoOfIso_hom (hS : CoversVertexHeights S h)
    {D : FiniteReebData.{0} n} (e : D ≅ graphPLReebData G h S) :
    (graphPLCosheafIsoOfIso G h hS e).hom = graphPLLift G h hS e := rfl

/-- The graph-PL finite Reeb data has the canonical component-cosheaf identification. -/
noncomputable def graphPLCosheafIso (hS : CoversVertexHeights S h) :
    (graphPLReebData G h S).toCosheaf S ≅ intervalComponents (plHeight G h) :=
  graphPLCosheafIsoOfIso G h hS (CategoryTheory.Iso.refl _)

/-- The graph-PL identification sends a vertex label to the inverse star bijection. -/
theorem graphPLCosheafIso_hom_app_J (hS : CoversVertexHeights S h) (i : Fin (n + 1))
    (x : LevelVertex G h (S.value i)) :
    (graphPLCosheafIso G h hS).hom.app (S.J i)
        ((graphPLReebData G h S).vertexLabel S i x) =
      (graphPLStarEquiv G h S hS i).symm x := by
  let hF := isConstructibleAt_intervalComponents_plHeight G h hS
  let hFc : IsIntervalCosheaf.{0} (intervalComponents (plHeight G h)) :=
    intervalComponents_isIntervalCosheaf _
  let j : (graphPLReebData G h S).Hom
      (S.extract (intervalComponents (plHeight G h)) hF.finite) :=
    (CategoryTheory.Iso.refl _).hom ≫ (graphPLExtractIso G h S hS).inv
  change (graphPLCosheafIsoOfIso G h hS (CategoryTheory.Iso.refl _)).hom.app (S.J i)
      ((graphPLReebData G h S).vertexLabel S i x) = _
  rw [graphPLCosheafIsoOfIso_hom]
  change ((graphPLReebData G h S).toCosheafLift hF hFc j).app (S.J i)
    ((graphPLReebData G h S).vertexLabel S i x) = _
  exact ((graphPLReebData G h S).toCosheafLift_app_J hF hFc j i x).trans
    (graphPLExtractIso_inv_v G h hS i x)

/-- The graph-PL identification sends an edge label to the inverse gap bijection. -/
theorem graphPLCosheafIso_hom_app_K (hS : CoversVertexHeights S h) (k : Fin n)
    (y : (graphPLReebData G h S).E k) :
    (graphPLCosheafIso G h hS).hom.app (S.K k)
        ((graphPLReebData G h S).edgeLabel S k y) =
      (graphPLGapEquiv G h S hS k).symm y := by
  let hF := isConstructibleAt_intervalComponents_plHeight G h hS
  let hFc : IsIntervalCosheaf.{0} (intervalComponents (plHeight G h)) :=
    intervalComponents_isIntervalCosheaf _
  let j : (graphPLReebData G h S).Hom
      (S.extract (intervalComponents (plHeight G h)) hF.finite) :=
    (CategoryTheory.Iso.refl _).hom ≫ (graphPLExtractIso G h S hS).inv
  change (graphPLCosheafIsoOfIso G h hS (CategoryTheory.Iso.refl _)).hom.app (S.K k)
      ((graphPLReebData G h S).edgeLabel S k y) = _
  rw [graphPLCosheafIsoOfIso_hom]
  change ((graphPLReebData G h S).toCosheafLift hF hFc j).app (S.K k)
    ((graphPLReebData G h S).edgeLabel S k y) = _
  exact ((graphPLReebData G h S).toCosheafLift_app_K hF hFc j k y).trans
    (graphPLExtractIso_inv_e G h hS k y)

/-- The graph-PL identification is the unique labelled natural transformation. -/
theorem graphPLCosheafIso_hom_unique (hS : CoversVertexHeights S h)
    (α : (graphPLReebData G h S).toCosheaf S ⟶ intervalComponents (plHeight G h))
    (hJ : ∀ i x, α.app (S.J i) ((graphPLReebData G h S).vertexLabel S i x) =
      (graphPLStarEquiv G h S hS i).symm x)
    (hK : ∀ k y, α.app (S.K k) ((graphPLReebData G h S).edgeLabel S k y) =
      (graphPLGapEquiv G h S hS k).symm y) :
    α = (graphPLCosheafIso G h hS).hom := by
  let hF := isConstructibleAt_intervalComponents_plHeight G h hS
  let hFc : IsIntervalCosheaf.{0} (intervalComponents (plHeight G h)) :=
    intervalComponents_isIntervalCosheaf _
  let j : (graphPLReebData G h S).Hom
      (S.extract (intervalComponents (plHeight G h)) hF.finite) :=
    (CategoryTheory.Iso.refl _).hom ≫ (graphPLExtractIso G h S hS).inv
  change α = (graphPLCosheafIsoOfIso G h hS (CategoryTheory.Iso.refl _)).hom
  rw [graphPLCosheafIsoOfIso_hom]
  change α = (graphPLReebData G h S).toCosheafLift hF hFc j
  apply (graphPLReebData G h S).toCosheafLift_unique hF hFc j α
  · intro i x
    exact (hJ i x).trans (graphPLExtractIso_inv_v G h hS i x).symm
  · intro k y
    exact (hK k y).trans (graphPLExtractIso_inv_e G h hS k y).symm

/-! ## Constructible-cosheaf and distance corollaries -/

/-- The graph-PL path-component precosheaf is a constructible interval cosheaf. -/
theorem isConstructibleCosheaf_intervalComponents_plHeight (hS : CoversVertexHeights S h) :
    IsConstructibleCosheaf (intervalComponents (plHeight G h)) :=
  IsConstructibleCosheaf.of_isConstructibleAt
    (isConstructibleAt_intervalComponents_plHeight G h hS)
    (intervalComponents_isIntervalCosheaf _)

/-- The component functor's graph-object value is identified with graph-PL components. -/
noncomputable def cosheafFunctorGraphPLIso (hS : CoversVertexHeights S h) :
    (cosheafFunctor.obj ((toRGraph S).obj (graphPLReebData G h S))).obj ≅
      intervalComponents (plHeight G h) := by
  change (graphPLReebData G h S).toCosheaf S ≅ intervalComponents (plHeight G h)
  exact graphPLCosheafIso G h hS

/-- The geometric distance between graph-PL objects is the distance between their component
cosheaves. -/
theorem geometricInterleavingDistance_graphPL {V' : Type} [Finite V'] (G' : SimpleGraph V')
    (h' : V' → ℝ) {m : ℕ} {T : CriticalValues m} (hS : CoversVertexHeights S h)
    (hT : CoversVertexHeights T h') :
    geometricInterleavingDistance ((toRGraph S).obj (graphPLReebData G h S))
        ((toRGraph T).obj (graphPLReebData G' h' T)) =
      interleavingDistance (intervalComponents (plHeight G h))
        (intervalComponents (plHeight G' h')) := by
  rw [geometricInterleavingDistance_eq_interleavingDistance]
  exact interleavingDistance_congr (cosheafFunctorGraphPLIso G h hS)
    (cosheafFunctorGraphPLIso G' h' hT)

end with_finite

end
end TDA.Mapper.GraphPL
