import TDA.Reeb.ConstructibleCylinder

/-!
# Constructible cosheaves from finite data

Existence and labelled uniqueness of a constructible cosheaf realizing finite incidence data, and
the reconstruction of every constructible cosheaf from its extracted finite data (de Silva, Munch
and Patel, *Categorified Reeb Graphs*, Proposition 3.18, with the map classification of
Proposition 3.12).

## Setting

`S : CriticalValues n` has levels `a 0 < ⋯ < a n`, and `D : FiniteReebData.{u} n` lives at an
arbitrary value universe `u`. Write `P = ofFiniteData D` for the realization data with discrete
pieces and `C_D = D.toCosheaf S`. By definition `C_D` is the path-component cosheaf
`intervalComponents (P.height S)` of the cylinder realization. It is constructible at `S`
(`toCosheaf_isConstructibleAt`) and an interval cosheaf for covers indexed in any universe
(`toCosheaf_isIntervalCosheaf`). No second combinatorial cosheaf is constructed.

## Labels

The labels run from the vertex and edge sets of `D` to components.

* `vertexLabel S i : D.V i ≃ C_D (J i)` is `(zerothHomotopyEquivOfDiscrete (P.V i)).symm`
  followed by `P.vertexComponentsEquiv S i`. A vertex `v` goes to the class of the vertex
  point `ofVertex S i v` (`vertexLabel_apply`).
* `edgeLabel S e : D.E e ≃ C_D (K e)` is the analogous composite with
  `P.edgeComponentsEquiv S e (S.gapMidpoint e)`. For every regular height `t ∈ K e` it equals the
  composite at `t` (`edgeLabel_eq`), so `y` goes to the class of the strip point `(y, t)`
  (`edgeLabel_apply`). The midpoint is therefore invisible in every statement about the labels.
  No retraction is claimed to be natural.
* Incidence: `C_D (K e ≤ J e.castSucc) (λE y) = λV (D.left e y)` and
  `C_D (K e ≤ J e.succ) (λE y) = λV (D.right e y)` (`map_K_le_J_castSucc_edgeLabel`,
  `map_K_le_J_succ_edgeLabel`).

## Finite round trip

`toExtractHom : D.Hom (S.extract C_D _)` has the labels as components. `fromExtractHom` is its
`Hom.inv`, with components the inverse labels (`fromExtractHom_v_apply`, `fromExtractHom_e_apply`).
`extract_toCosheaf_iso` states both composition laws, `Hom.comp_inv` and `Hom.inv_comp`. No
category instance on `FiniteReebData` is used.

## Labelled existence and uniqueness

Let `G` be constructible at `S` with `IsIntervalCosheaf.{0} G`, in the value universe of `D`, and
let `j : D.Hom (S.extract G hG.finite)` be any finite map. `toCosheafLift hG hGc j` is the `ShortMaps.extend` of the short maps `ShortMaps.ofHom (fromExtractHom.comp j)`. It is the unique
natural transformation `α : C_D ⟶ G` with `α (J i) (λV x) = j.v i x` and
`α (K e) (λE x) = j.e e x` (`existsUnique_natTrans_labelled`). Uniqueness uses the surjectivity of
the labels and `natTrans_ext`; it does not need bijectivity of `j`. If `j` has bijective
components, the transformation is an isomorphism (`isIso_toCosheafLift`). Different labellings may
give different transformations, so this is not uniqueness of all unlabelled automorphisms.

## Reconstruction

For `F` with `hF : S.IsConstructibleAt F` and `hFc : IsIntervalCosheaf.{0} F`,
`realizeExtractIso hF hFc : (S.extract F hF.finite).toCosheaf S ≅ F` is the labelled lift of the
identity of the extracted data. Its hom sends the canonical star and gap labels of `x` back to `x`,
its inverse is the label map on stars and gaps, and it is the unique transformation with these
star and gap values. These are natural transformations on the whole interval category, including
`⊥`, bounded intervals, rays and `⊤`. On an interval inside a star containing its level, or
inside a gap containing a regular height, the value of the reconstruction on the class of a vertex
or strip point maps to the original element in the star or gap
(`map_realizeExtractIso_hom_app_vertex`, `map_realizeExtractIso_hom_app_strip`). By
constructibility that inclusion is bijective, so this determines the value.

See `docs/math/reeb-constructible-representation.md`.
-/

open Set CategoryTheory

universe u w

namespace TDA.Reeb

noncomputable section

namespace CriticalValues

variable {n : ℕ} (S : CriticalValues n)

/-- The midpoint of the gap `K e`, the regular height used to define the edge labels. Every other
regular height gives the same labels (`FiniteReebData.edgeLabel_eq`). -/
def gapMidpoint (e : Fin n) : (S.K e : Set ℝ) :=
  ⟨(S.value e.castSucc + S.value e.succ) / 2, by
    have h := S.value_castSucc_lt_succ e
    exact S.mem_K.2 ⟨by linarith, by linarith⟩⟩

end CriticalValues

namespace FiniteReebData

open CylinderPresentation CriticalValues

variable {n : ℕ} (D : FiniteReebData.{u} n) (S : CriticalValues n)

/-! ### The cosheaf of finite data -/

/-- The cosheaf of finite data at the levels `S` (DMP Proposition 3.18, existence): the path-component cosheaf `intervalComponents` of the height of the cylinder realization of `D`. -/
def toCosheaf : OpenInterval ⥤ Type u :=
  intervalComponents ((ofFiniteData D).height S)

/-- `D.toCosheaf S` is by definition the path-component cosheaf of the realized height. -/
theorem toCosheaf_eq : D.toCosheaf S = intervalComponents ((ofFiniteData D).height S) := rfl

/-- `D.toCosheaf S` is constructible at `S` (`finiteData_isConstructibleAt`). -/
theorem toCosheaf_isConstructibleAt : S.IsConstructibleAt (D.toCosheaf S) :=
  finiteData_isConstructibleAt S D

/-- `D.toCosheaf S` is an interval cosheaf, for covers indexed in any universe. -/
theorem toCosheaf_isIntervalCosheaf : IsIntervalCosheaf.{w} (D.toCosheaf S) :=
  intervalComponents_isIntervalCosheaf _

/-! ### Labels -/

/-- Vertex labels `λV i : D.V i ≃ C_D (J i)`, from the labels of `D` to components. -/
def vertexLabel (i : Fin (n + 1)) : D.V i ≃ (D.toCosheaf S).obj (S.J i) :=
  (zerothHomotopyEquivOfDiscrete ((ofFiniteData D).V i)).symm.trans
    ((ofFiniteData D).vertexComponentsEquiv S i)

/-- Edge labels `λE e : D.E e ≃ C_D (K e)`, defined at the midpoint of the gap. -/
def edgeLabel (e : Fin n) : D.E e ≃ (D.toCosheaf S).obj (S.K e) :=
  (zerothHomotopyEquivOfDiscrete ((ofFiniteData D).E e)).symm.trans
    ((ofFiniteData D).edgeComponentsEquiv S e (S.gapMidpoint e))

/-- Generator formula: `λV i v` is the class of the vertex point at `v`. -/
theorem vertexLabel_apply (i : Fin (n + 1)) (v : D.V i) :
    D.vertexLabel S i v =
      ZerothHomotopy.mk (⟨(ofFiniteData D).ofVertex S i v, S.value_mem_J i⟩ :
        (ofFiniteData D).heightPreimage S (S.J i)) :=
  rfl

/-- Height independence: the edge labels are the composite at any regular height `t`. -/
theorem edgeLabel_eq (e : Fin n) (t : (S.K e : Set ℝ)) :
    D.edgeLabel S e = (zerothHomotopyEquivOfDiscrete ((ofFiniteData D).E e)).symm.trans
      ((ofFiniteData D).edgeComponentsEquiv S e t) := by
  rw [edgeLabel, (ofFiniteData D).edgeComponentsEquiv_indep S e (S.gapMidpoint e) t]
  rfl

/-- Generator formula: `λE e y` is the class of the strip point `(y, t)`, at any regular
height `t`. -/
theorem edgeLabel_apply (e : Fin n) (t : (S.K e : Set ℝ)) (y : D.E e) :
    D.edgeLabel S e y =
      ZerothHomotopy.mk (⟨(ofFiniteData D).ofStrip S e (y, t), t.2⟩ :
        (ofFiniteData D).heightPreimage S (S.K e)) := by
  rw [D.edgeLabel_eq S e t]
  rfl

/-- Left incidence of the labels. -/
theorem map_K_le_J_castSucc_edgeLabel (e : Fin n) (y : D.E e) :
    (D.toCosheaf S).map (homOfLE (S.K_le_J_castSucc e)) (D.edgeLabel S e y) =
      D.vertexLabel S e.castSucc (D.left e y) :=
  (ofFiniteData D).map_K_le_J_castSucc_edgeComponentsEquiv S e (S.gapMidpoint e) (.mk y)

/-- Right incidence of the labels. -/
theorem map_K_le_J_succ_edgeLabel (e : Fin n) (y : D.E e) :
    (D.toCosheaf S).map (homOfLE (S.K_le_J_succ e)) (D.edgeLabel S e y) =
      D.vertexLabel S e.succ (D.right e y) :=
  (ofFiniteData D).map_K_le_J_succ_edgeComponentsEquiv S e (S.gapMidpoint e) (.mk y)

/-! ### The finite round trip -/

/-- The canonical finite map `D → extract C_D`; its components are the labels. -/
def toExtractHom : D.Hom (S.extract (D.toCosheaf S) (D.toCosheaf_isConstructibleAt S).finite) where
  v i := D.vertexLabel S i
  e i := D.edgeLabel S i
  left_comm i y := D.map_K_le_J_castSucc_edgeLabel S i y
  right_comm i y := D.map_K_le_J_succ_edgeLabel S i y

/-- The vertex components of `toExtractHom` are the vertex labels. -/
theorem toExtractHom_v (i : Fin (n + 1)) : (D.toExtractHom S).v i = D.vertexLabel S i := rfl

/-- The edge components of `toExtractHom` are the edge labels. -/
theorem toExtractHom_e (e : Fin n) : (D.toExtractHom S).e e = D.edgeLabel S e := rfl

/-- The vertex components of `toExtractHom` are bijective. -/
theorem toExtractHom_v_bijective (i : Fin (n + 1)) :
    Function.Bijective ((D.toExtractHom S).v i) :=
  (D.vertexLabel S i).bijective

/-- The edge components of `toExtractHom` are bijective. -/
theorem toExtractHom_e_bijective (e : Fin n) : Function.Bijective ((D.toExtractHom S).e e) :=
  (D.edgeLabel S e).bijective

/-- The extracted-component-to-label identifications, by `Hom.inv`. -/
def fromExtractHom :
    (S.extract (D.toCosheaf S) (D.toCosheaf_isConstructibleAt S).finite).Hom D :=
  (D.toExtractHom S).inv (D.toExtractHom_v_bijective S) (D.toExtractHom_e_bijective S)

/-- The vertex components of `fromExtractHom` are the inverse vertex labels. -/
theorem fromExtractHom_v_apply (i : Fin (n + 1)) (x : (D.toCosheaf S).obj (S.J i)) :
    (D.fromExtractHom S).v i x = (D.vertexLabel S i).symm x :=
  (D.vertexLabel S i).injective (by
    rw [Equiv.apply_symm_apply]
    exact Equiv.ofBijective_apply_symm_apply _ (D.toExtractHom_v_bijective S i) x)

/-- The edge components of `fromExtractHom` are the inverse edge labels. -/
theorem fromExtractHom_e_apply (e : Fin n) (x : (D.toCosheaf S).obj (S.K e)) :
    (D.fromExtractHom S).e e x = (D.edgeLabel S e).symm x :=
  (D.edgeLabel S e).injective (by
    rw [Equiv.apply_symm_apply]
    exact Equiv.ofBijective_apply_symm_apply _ (D.toExtractHom_e_bijective S e) x)

/-- **Finite round trip.** The two finite maps are mutually inverse (`Hom.comp_inv`,
`Hom.inv_comp`); no category instance is used. -/
theorem extract_toCosheaf_iso :
    (D.toExtractHom S).comp (D.fromExtractHom S) = Hom.id D ∧
      (D.fromExtractHom S).comp (D.toExtractHom S) =
        Hom.id (S.extract (D.toCosheaf S) (D.toCosheaf_isConstructibleAt S).finite) :=
  ⟨Hom.comp_inv _ _ _, Hom.inv_comp _ _ _⟩

/-! ### Labelled existence and uniqueness -/

variable {S} {G : OpenInterval ⥤ Type u} (hG : S.IsConstructibleAt G)
  (hGc : IsIntervalCosheaf.{0} G)

/-- Short maps `C_D → G` from a finite map `j : D → extract G`: the inverse labels, then `j`. -/
def labelledShortMaps (j : D.Hom (S.extract G hG.finite)) : S.ShortMaps (D.toCosheaf S) G :=
  ShortMaps.ofHom ((D.fromExtractHom S).comp j)

/-- The natural transformation `C_D ⟶ G` with prescribed labels: the `ShortMaps.extend` of `labelledShortMaps`. -/
def toCosheafLift (j : D.Hom (S.extract G hG.finite)) : D.toCosheaf S ⟶ G :=
  (D.labelledShortMaps hG j).extend (D.toCosheaf_isConstructibleAt S)
    (D.toCosheaf_isIntervalCosheaf S) hG hGc

/-- The labelled transformation on a star label is the vertex component of `j`. -/
theorem toCosheafLift_app_J (j : D.Hom (S.extract G hG.finite)) (i : Fin (n + 1)) (x : D.V i) :
    (D.toCosheafLift hG hGc j).app (S.J i) (D.vertexLabel S i x) = j.v i x := by
  rw [toCosheafLift, ShortMaps.extend_app_J]
  show j.v i ((D.fromExtractHom S).v i (D.vertexLabel S i x)) = j.v i x
  rw [fromExtractHom_v_apply, Equiv.symm_apply_apply]

/-- The labelled transformation on a gap label is the edge component of `j`. -/
theorem toCosheafLift_app_K (j : D.Hom (S.extract G hG.finite)) (e : Fin n) (x : D.E e) :
    (D.toCosheafLift hG hGc j).app (S.K e) (D.edgeLabel S e x) = j.e e x := by
  rw [toCosheafLift, ShortMaps.extend_app_K]
  show j.e e ((D.fromExtractHom S).e e (D.edgeLabel S e x)) = j.e e x
  rw [fromExtractHom_e_apply, Equiv.symm_apply_apply]

/-- Uniqueness relative to the specified labels. -/
theorem toCosheafLift_unique (j : D.Hom (S.extract G hG.finite)) (α : D.toCosheaf S ⟶ G)
    (hJ : ∀ i x, α.app (S.J i) (D.vertexLabel S i x) = j.v i x)
    (hK : ∀ e x, α.app (S.K e) (D.edgeLabel S e x) = j.e e x) :
    α = D.toCosheafLift hG hGc j :=
  S.natTrans_ext (D.toCosheaf_isConstructibleAt S) (D.toCosheaf_isIntervalCosheaf S) hG hGc
    (fun i y => by
      obtain ⟨x, rfl⟩ := (D.vertexLabel S i).surjective y
      rw [hJ, toCosheafLift_app_J])
    (fun e y => by
      obtain ⟨x, rfl⟩ := (D.edgeLabel S e).surjective y
      rw [hK, toCosheafLift_app_K])

include hGc in
/-- **Labelled existence and uniqueness** (DMP Proposition 3.18 together with the map
classification of Proposition 3.12). For any finite map `j : D → extract G` there is exactly one
natural transformation `C_D ⟶ G` with the prescribed star and gap values on the labels.
Bijectivity of `j` is not needed here. -/
theorem existsUnique_natTrans_labelled (j : D.Hom (S.extract G hG.finite)) :
    ∃! α : D.toCosheaf S ⟶ G, (∀ i x, α.app (S.J i) (D.vertexLabel S i x) = j.v i x) ∧
      ∀ e x, α.app (S.K e) (D.edgeLabel S e x) = j.e e x :=
  ⟨D.toCosheafLift hG hGc j, ⟨D.toCosheafLift_app_J hG hGc j, D.toCosheafLift_app_K hG hGc j⟩,
    fun α hα => D.toCosheafLift_unique hG hGc j α hα.1 hα.2⟩

/-- The labelled transformation is an isomorphism when `j` has bijective components
(`ShortMaps.isIso_extend`, DMP Corollary 3.14). -/
theorem isIso_toCosheafLift (j : D.Hom (S.extract G hG.finite))
    (hv : ∀ i, Function.Bijective (j.v i)) (he : ∀ e, Function.Bijective (j.e e)) :
    IsIso (D.toCosheafLift hG hGc j) :=
  ShortMaps.isIso_extend S (D.labelledShortMaps hG j) (D.toCosheaf_isConstructibleAt S)
    (D.toCosheaf_isIntervalCosheaf S) hG hGc
    (fun i => (hv i).comp (Equiv.ofBijective _ (D.toExtractHom_v_bijective S i)).symm.bijective)
    (fun e => (he e).comp (Equiv.ofBijective _ (D.toExtractHom_e_bijective S e)).symm.bijective)

/-- The restriction of the labelled transformation to extracted data is `fromExtractHom ≫ j`. -/
theorem natTransEquivDiagramHom_toCosheafLift (j : D.Hom (S.extract G hG.finite)) :
    S.natTransEquivDiagramHom (D.toCosheaf_isConstructibleAt S) (D.toCosheaf_isIntervalCosheaf S)
      hG hGc (D.toCosheafLift hG hGc j) = (D.fromExtractHom S).comp j := by
  show (S.restrict (D.toCosheafLift hG hGc j)).toHom _ _ = _
  rw [toCosheafLift, ShortMaps.restrict_extend]
  rfl

end FiniteReebData

/-! ### Reconstruction -/

namespace CriticalValues

open CylinderPresentation FiniteReebData

variable {n : ℕ} {S : CriticalValues n} {F : OpenInterval ⥤ Type u}
  (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F)

/-- The labelled lift of the identity of the extracted data of `F` is an isomorphism. -/
theorem isIso_toCosheafLift_id :
    IsIso ((S.extract F hF.finite).toCosheafLift hF hFc
      (FiniteReebData.Hom.id (S.extract F hF.finite))) :=
  (S.extract F hF.finite).isIso_toCosheafLift hF hFc _ (fun _ => Function.bijective_id)
    (fun _ => Function.bijective_id)

/-- **Reconstruction** (DMP Proposition 3.18 applied to the extracted data of `F`). The direction
is `(S.extract F hF.finite).toCosheaf S ≅ F`; the hom sends canonical labels back to the
original elements of `F`. -/
def realizeExtractIso : (S.extract F hF.finite).toCosheaf S ≅ F :=
  haveI := isIso_toCosheafLift_id hF hFc
  asIso ((S.extract F hF.finite).toCosheafLift hF hFc
    (FiniteReebData.Hom.id (S.extract F hF.finite)))

/-- The hom of the reconstruction is the labelled lift of the identity. -/
theorem realizeExtractIso_hom :
    (realizeExtractIso hF hFc).hom = (S.extract F hF.finite).toCosheafLift hF hFc
      (FiniteReebData.Hom.id (S.extract F hF.finite)) :=
  rfl

/-- On a star, the reconstruction sends the canonical label of `x` back to `x`. -/
theorem realizeExtractIso_hom_app_J (i : Fin (n + 1)) (x : F.obj (S.J i)) :
    (realizeExtractIso hF hFc).hom.app (S.J i) ((S.extract F hF.finite).vertexLabel S i x) = x :=
  (S.extract F hF.finite).toCosheafLift_app_J hF hFc _ i x

/-- On a gap, the reconstruction sends the canonical label of `x` back to `x`. -/
theorem realizeExtractIso_hom_app_K (e : Fin n) (x : F.obj (S.K e)) :
    (realizeExtractIso hF hFc).hom.app (S.K e) ((S.extract F hF.finite).edgeLabel S e x) = x :=
  (S.extract F hF.finite).toCosheafLift_app_K hF hFc _ e x

/-- On a star, the inverse of the reconstruction is the vertex label map. -/
theorem realizeExtractIso_inv_app_J (i : Fin (n + 1)) (x : F.obj (S.J i)) :
    (realizeExtractIso hF hFc).inv.app (S.J i) x = (S.extract F hF.finite).vertexLabel S i x := by
  have h := Iso.hom_inv_id_app_apply (realizeExtractIso hF hFc) (S.J i)
    ((S.extract F hF.finite).vertexLabel S i x)
  rwa [realizeExtractIso_hom_app_J] at h

/-- On a gap, the inverse of the reconstruction is the edge label map. -/
theorem realizeExtractIso_inv_app_K (e : Fin n) (x : F.obj (S.K e)) :
    (realizeExtractIso hF hFc).inv.app (S.K e) x = (S.extract F hF.finite).edgeLabel S e x := by
  have h := Iso.hom_inv_id_app_apply (realizeExtractIso hF hFc) (S.K e)
    ((S.extract F hF.finite).edgeLabel S e x)
  rwa [realizeExtractIso_hom_app_K] at h

/-- The reconstruction is the unique transformation sending the canonical labels back. -/
theorem realizeExtractIso_hom_unique (α : (S.extract F hF.finite).toCosheaf S ⟶ F)
    (hJ : ∀ i x, α.app (S.J i) ((S.extract F hF.finite).vertexLabel S i x) = x)
    (hK : ∀ e x, α.app (S.K e) ((S.extract F hF.finite).edgeLabel S e x) = x) :
    α = (realizeExtractIso hF hFc).hom :=
  (S.extract F hF.finite).toCosheafLift_unique hF hFc _ α hJ hK

/-- On extracted data, the reconstruction is the extracted-component-to-label map. -/
theorem natTransEquivDiagramHom_realizeExtractIso :
    S.natTransEquivDiagramHom ((S.extract F hF.finite).toCosheaf_isConstructibleAt S)
      ((S.extract F hF.finite).toCosheaf_isIntervalCosheaf S) hF hFc
      (realizeExtractIso hF hFc).hom = (S.extract F hF.finite).fromExtractHom S :=
  (S.extract F hF.finite).natTransEquivDiagramHom_toCosheafLift hF hFc _

/-- Away from vertices: on an interval `I ≤ K e` containing the regular height `t`, the
reconstruction sends the class of the strip point over `z` at `t` to an element whose image in the
gap is `z`. -/
theorem map_realizeExtractIso_hom_app_strip {e : Fin n} {I : OpenInterval} (hI : I ≤ S.K e)
    (t : (S.K e : Set ℝ)) (ht : (t : ℝ) ∈ I) (z : F.obj (S.K e)) :
    F.map (homOfLE hI) ((realizeExtractIso hF hFc).hom.app I
      (ZerothHomotopy.mk (⟨(ofFiniteData (S.extract F hF.finite)).ofStrip S e (z, t), ht⟩ :
        (ofFiniteData (S.extract F hF.finite)).heightPreimage S I))) = z := by
  refine (NatTrans.naturality_apply (realizeExtractIso hF hFc).hom (homOfLE hI) _).symm.trans ?_
  refine (congrArg ((realizeExtractIso hF hFc).hom.app (S.K e)) ?_).trans
    (realizeExtractIso_hom_app_K hF hFc e z)
  exact ((S.extract F hF.finite).edgeLabel_apply S e t z).symm

/-- At a vertex: on an interval `I ≤ J i` containing the level `a i`, the reconstruction sends the
class of the vertex point over `x` to an element whose image in the star is `x`. -/
theorem map_realizeExtractIso_hom_app_vertex {i : Fin (n + 1)} {I : OpenInterval}
    (hI : I ≤ S.J i) (hi : S.value i ∈ I) (x : F.obj (S.J i)) :
    F.map (homOfLE hI) ((realizeExtractIso hF hFc).hom.app I
      (ZerothHomotopy.mk (⟨(ofFiniteData (S.extract F hF.finite)).ofVertex S i x, hi⟩ :
        (ofFiniteData (S.extract F hF.finite)).heightPreimage S I))) = x := by
  refine (NatTrans.naturality_apply (realizeExtractIso hF hFc).hom (homOfLE hI) _).symm.trans ?_
  refine (congrArg ((realizeExtractIso hF hFc).hom.app (S.J i)) ?_).trans
    (realizeExtractIso_hom_app_J hF hFc i x)
  exact ((S.extract F hF.finite).vertexLabel_apply S i x).symm

end CriticalValues

end

end TDA.Reeb
