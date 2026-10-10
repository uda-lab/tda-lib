import TDA.Reeb.ComponentsDiscrete
import TDA.Reeb.ComponentsHomotopy
import TDA.Reeb.ConstructibleCosheaf
import TDA.Reeb.ConstructibleSpace
import TDA.Reeb.IntervalComponents
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum

/-!
# Local cylinder comparisons and constructibility of path components

Let `S : CriticalValues n` have levels `a 0 < ⋯ < a n`, let `P : CylinderPresentation n` have
arbitrary topological pieces, and write `X = P.Realization S` and `h = P.height S`. For an open
interval `W`, `P.heightPreimage S W` is the subspace `{x : X // h x ∈ W}`; its path components are
`(intervalComponents h).obj W` by definition (`intervalComponents_obj_eq`). This file proves the
cylinder principle of de Silva–Munch–Patel (Lemma 2.4) and the constructibility of the
path-component cosheaf of a realization (Proposition 3.16).

## Hypotheses

* The homotopy equivalences, the component bijections, incidence compatibility, naturality and
  the bijectivity clause use no hypothesis on the pieces: no Hausdorffness, compactness, local
  path-connectedness or finiteness.
* Finiteness of the values uses only `Finite (ZerothHomotopy (P.V i))` and
  `Finite (ZerothHomotopy (P.E e))`. Compact locally path-connected pieces satisfy it by
  mathlib's instance (`isConstructibleAt_of_compact_lpc`), and realized finite data satisfy it
  because a discrete space is its own set of path components (`finiteData_isConstructibleAt`).
  Compactness of an open inverse image is never used; it fails in general, since
  `h⁻¹(K e) ≅ E e × K e`.
* Exterior values are empty by `height_preimage_lowerTail` and `height_preimage_upperTail`.

## The clamp homotopy

Clamp data `c : S.ClampData J` consist of `lo ≤ hi` with `[lo, hi] ⊆ J` such that every level in
`J` lies in `[lo, hi]`. Let `κ t = max lo (min hi t)` and `κ_s t = t + s (κ t − t)` for
`s ∈ [0, 1]`. On raw pieces a vertex point is fixed and a cylinder point `(y, t)` of edge `e`
goes to `(y, projIcc (κ_s t))`; curried per piece, this is continuous on the whole raw sum as a
map into `C([0,1], X)`. It respects the endpoint relation over `J`: an end of a cylinder whose
level lies in `J` has level in `[lo, hi]`, so `κ_s` fixes it and the end still goes to its vertex
image. The quotient map restricted to the open saturated set `h⁻¹ J` is a quotient map
(`IsQuotientMap.restrictPreimage_isOpen`), so the family descends to a continuous
`clampFamily c : C(heightPreimage J, C([0,1], X))`, which uncurries to a jointly continuous map
because `[0,1]` is locally compact. Inside `J`, `κ t` stays in the segment of the edge, so the
height of the image is `κ_s (h x)`, between `h x` and `κ (h x) ∈ [lo, hi]`. Hence for every open
interval `W` with `[lo, hi] ⊆ W ≤ J` the family is a homotopy of `heightPreimage W` from the
identity to the end map (`clampHomotopy`). It is an ordinary homotopy, not a homotopy over `ℝ`,
since heights move, and the end map is not a deformation retraction onto an open subspace.

* Vertex `i`: `J = J i` and `lo = hi = a i`. The end map lands in the critical fiber
  `h⁻¹{a i} ≅ V i` (`criticalFiberHomeomorph`), so the fiber inclusion
  `vertexFiberInclusion i : V i → heightPreimage (J i)` is a homotopy equivalence
  (`vertexHomotopyEquiv`).
* Regular gap `e` at a chosen `t ∈ K e`: `J = K e` and `lo = hi = t`, and no level lies in `K e`.
  The end map lands in `h⁻¹{t} ≅ E e` (`regularFiberHomeomorph`), so
  `regularFiberInclusion e t : E e → heightPreimage (K e)` is a homotopy equivalence
  (`regularHomotopyEquiv`).
* Nested `I ≤ J` with `I` nonempty and the same levels: `lo` and `hi` are the minimum and
  maximum of one point of `I` together with the levels in `I`. The end map is a map
  `heightPreimage J → heightPreimage I`, and both composites with the inclusion are end maps of
  the same homotopy restricted to `W = I` and `W = J` (`nestedHomotopyEquiv`). Bijectivity of the
  actual map `(intervalComponents h).map (homOfLE _)` follows.

Only the forward map of each homotopy equivalence, the actual fiber or interval inclusion, is
part of the interface. The homotopy inverses are chosen clamp retractions.

The parenthesis of DMP Lemma 2.4 indexes edges so that the first genuine edge set would be
empty. Here the incident edges of level `i` are the `e` with `e.castSucc = i` or `e.succ = i`,
and `n = 0` has no edge.

## Incidence, naturality, height independence and finiteness

* The cylinder line from `(y, t)` to `(y, a e)` stays in `J e.castSucc`, so the gap-to-star map
  carries `edgeComponentsEquiv` to `vertexComponentsEquiv ∘ componentMap (left e)`
  (`map_K_le_J_castSucc_edgeComponentsEquiv`; `right` through `J e.succ`), also in conjugated
  form (`vertexComponentsEquiv_symm_map_castSucc`, `vertexComponentsEquiv_symm_map_succ`).
* For two presentations over the same `S` and an arbitrary continuous
  `φ : P.Realization S → P'.Realization S` with `h' ∘ φ = h`, `φ` restricts to the fibers and
  defines `vertexFiberMap` and `regularFiberMap`. The actual fiber inclusions commute with `φ`
  on the nose (`vertexFiberInclusion_naturality`, `regularFiberInclusion_naturality`), hence the
  component bijections are natural for `componentNatTrans φ` and its restriction to intervals.
  The chosen retractions are not claimed to commute with `φ`.
* `edgeComponentsEquiv` does not depend on the chosen regular height, and on path components
  neither does `regularFiberMap` (`componentMap_regularFiberMap_indep`). Pointwise the regular
  fiber map does depend on the height in general: a height-dependent rotation of a circle strip.
* Every point over a nonempty `I` is joined inside `heightPreimage I` to a vertex point at a
  level of `I`, or, when `I` contains no endpoint level of its edge and hence `I ≤ K e`, to the
  strip point at one fixed height of `I`. This gives a surjection from a finite sum of piece
  component sets (`finite_intervalComponents`).

See `docs/math/reeb-constructible-cylinder.md`.
-/

open Set Topology CategoryTheory

universe u

namespace TDA.Reeb

noncomputable section

/-! ### Clamp data -/

namespace CriticalValues

variable {n : ℕ} (S : CriticalValues n)

/-- Clamp data in `J`: a closed interval `[lo, hi] ⊆ J` containing every level of `J`. -/
structure ClampData (J : OpenInterval) where
  /-- Lower clamp height. -/
  lo : ℝ
  /-- Upper clamp height. -/
  hi : ℝ
  lo_le_hi : lo ≤ hi
  Icc_subset : Icc lo hi ⊆ (J : Set ℝ)
  value_mem : ∀ k, S.value k ∈ J → S.value k ∈ Icc lo hi

namespace ClampData

variable {S} {J : OpenInterval} (c : S.ClampData J)

/-- The clamp `κ t = max lo (min hi t)`. -/
def clampHeight (t : ℝ) : ℝ := max c.lo (min c.hi t)

/-- The interpolation `κ_s t = t + s (κ t - t)`. -/
def interp (s t : ℝ) : ℝ := t + s * (c.clampHeight t - t)

theorem continuous_clampHeight : Continuous c.clampHeight :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clampHeight_mem_Icc (t : ℝ) : c.clampHeight t ∈ Icc c.lo c.hi :=
  ⟨le_max_left _ _, max_le c.lo_le_hi (min_le_left _ _)⟩

theorem clampHeight_of_mem {t : ℝ} (h : t ∈ Icc c.lo c.hi) : c.clampHeight t = t := by
  simp [clampHeight, min_eq_right h.2, max_eq_right h.1]

theorem interp_zero (t : ℝ) : c.interp 0 t = t := by simp [interp]

theorem interp_one (t : ℝ) : c.interp 1 t = c.clampHeight t := by simp [interp]

theorem interp_of_mem {t : ℝ} (h : t ∈ Icc c.lo c.hi) (s : ℝ) : c.interp s t = t := by
  simp [interp, c.clampHeight_of_mem h]

theorem interp_mem_uIcc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    c.interp s t ∈ uIcc t (c.clampHeight t) := by
  rw [mem_uIcc]
  unfold interp
  rcases le_total t (c.clampHeight t) with h | h
  · exact .inl ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  · exact .inr ⟨by nlinarith [hs.2], by nlinarith [hs.1]⟩

theorem lo_mem : c.lo ∈ (J : Set ℝ) := c.Icc_subset ⟨le_rfl, c.lo_le_hi⟩

theorem hi_mem : c.hi ∈ (J : Set ℝ) := c.Icc_subset ⟨c.lo_le_hi, le_rfl⟩

/-- Inside `J`, the clamp keeps a height of an edge segment in that segment. -/
theorem clampHeight_mem_seg {e : Fin n} {t : ℝ}
    (ht : t ∈ Icc (S.value e.castSucc) (S.value e.succ)) (htJ : t ∈ (J : Set ℝ)) :
    c.clampHeight t ∈ Icc (S.value e.castSucc) (S.value e.succ) := by
  have h₁ : c.lo ≤ S.value e.succ := by
    by_contra hlt
    push Not at hlt
    exact absurd (c.value_mem _ (J.ordConnected.out htJ c.lo_mem ⟨ht.2, hlt.le⟩)).1
      (not_le.2 hlt)
  have h₂ : S.value e.castSucc ≤ c.hi := by
    by_contra hlt
    push Not at hlt
    exact absurd (c.value_mem _ (J.ordConnected.out c.hi_mem htJ ⟨hlt.le, ht.1⟩)).2
      (not_le.2 hlt)
  exact ⟨le_max_of_le_right (le_min h₂ ht.1), max_le h₁ ((min_le_right _ _).trans ht.2)⟩

theorem interp_mem_seg {e : Fin n} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Icc (S.value e.castSucc) (S.value e.succ)) (htJ : t ∈ (J : Set ℝ)) :
    c.interp s t ∈ Icc (S.value e.castSucc) (S.value e.succ) :=
  ordConnected_Icc.uIcc_subset ht (c.clampHeight_mem_seg ht htJ) (c.interp_mem_uIcc hs t)

end ClampData

/-- Clamp data for a nested pair with the same levels: `[lo, hi] ⊆ I`. -/
theorem exists_clampData_of_le {I J : OpenInterval} (hIJ : I ≤ J) (hI : (I : Set ℝ).Nonempty)
    (hhit : ∀ i, S.value i ∈ I ↔ S.value i ∈ J) :
    ∃ c : S.ClampData J, Icc c.lo c.hi ⊆ (I : Set ℝ) := by
  classical
  obtain ⟨s, hs⟩ := hI
  set T : Finset ℝ := insert s ((Finset.univ.filter fun k => S.value k ∈ I).image S.value)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  have hTI : ∀ x ∈ T, x ∈ (I : Set ℝ) := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hs
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      exact (Finset.mem_filter.1 hk).2
  have hsub : Icc (T.min' hT) (T.max' hT) ⊆ (I : Set ℝ) :=
    I.ordConnected.out (hTI _ (T.min'_mem hT)) (hTI _ (T.max'_mem hT))
  refine ⟨⟨T.min' hT, T.max' hT, T.min'_le_max' hT, hsub.trans hIJ, fun k hk => ?_⟩, hsub⟩
  have hkT : S.value k ∈ T := Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, (hhit k).2 hk⟩))
  exact ⟨T.min'_le _ hkT, T.le_max' _ hkT⟩


end CriticalValues

namespace CylinderPresentation

/-! ### Preimage subtypes, cylinder paths, descent -/

section pre

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{u} n)

/-- The inverse-image subspace `h⁻¹ W`; its path components are `(intervalComponents h).obj W`. -/
abbrev heightPreimage (W : OpenInterval) : Type u := {x : P.Realization S // P.height S x ∈ W}

theorem intervalComponents_obj_eq (W : OpenInterval) :
    (intervalComponents (P.height S)).obj W = ZerothHomotopy (P.heightPreimage S W) := rfl

/-- A path along one cylinder line between two heights of its segment, with heights in between. -/
theorem joinedIn_cylinder (e : Fin n) (y : P.E e) (t t' : Seg S e) :
    JoinedIn (P.height S ⁻¹' uIcc (t : ℝ) t') (P.ofCylinder S e (y, t))
      (P.ofCylinder S e (y, t')) := by
  obtain ⟨γ, hγ⟩ := ((convex_uIcc (t : ℝ) (t' : ℝ) : Convex ℝ _).isPathConnected
    nonempty_uIcc).joinedIn _ left_mem_uIcc _ right_mem_uIcc
  have hsub : uIcc (t : ℝ) t' ⊆ Seg S e := ordConnected_Icc.uIcc_subset t.2 t'.2
  exact ⟨{ toFun := fun s => P.ofCylinder S e (y, ⟨γ s, hsub (hγ s)⟩)
           continuous_toFun := (P.continuous_ofCylinder S e).comp
             (continuous_const.prodMk (γ.continuous.subtype_mk _))
           source' := congrArg (fun z => P.ofCylinder S e (y, z)) (Subtype.ext γ.source)
           target' := congrArg (fun z => P.ofCylinder S e (y, z)) (Subtype.ext γ.target) },
    fun s => hγ s⟩

variable {S P} in
/-- A path inside `h⁻¹ W` joins the points in the subspace. -/
theorem joined_pre {W : OpenInterval} {a b : P.heightPreimage S W}
    (h : JoinedIn (P.height S ⁻¹' (W : Set ℝ)) a.1 b.1) : Joined a b := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨{ toFun := fun s => ⟨γ s, hγ s⟩
           continuous_toFun := γ.continuous.subtype_mk _
           source' := Subtype.ext γ.source
           target' := Subtype.ext γ.target }⟩

variable {S P} in
theorem mk_eq_of_joinedIn {W : OpenInterval} {a b : P.heightPreimage S W}
    (h : JoinedIn (P.height S ⁻¹' (W : Set ℝ)) a.1 b.1) :
    (ZerothHomotopy.mk a : ZerothHomotopy (P.heightPreimage S W)) = ZerothHomotopy.mk b :=
  ZerothHomotopy.sound (joined_pre h).somePath

theorem exists_quotMk {W : OpenInterval} (u : P.heightPreimage S W) :
    ∃ (x : P.Raw S) (hx : P.rawHeight S x ∈ W), u = ⟨P.quotMk S x, hx⟩ := by
  obtain ⟨q, hq⟩ := u
  obtain ⟨x, rfl⟩ := P.quotMk_surjective S q
  exact ⟨x, hq, rfl⟩

variable {S P}

/-- Descent over the open set `h⁻¹ J` of a continuous raw map that respects the normal form on
raw points over `J`. -/
def descend {Z : Type*} [TopologicalSpace Z] (J : OpenInterval) (g : P.Raw S → Z)
    (hg : Continuous g) (hresp : ∀ x, P.rawHeight S x ∈ J → g (P.nf S x) = g x) :
    C(P.heightPreimage S J, Z) where
  toFun u := g (Quotient.out (s := P.setoid S) u.1)
  continuous_toFun := by
    have hU : IsOpen (P.height S ⁻¹' (J : Set ℝ)) := J.isOpen.preimage (P.height S).continuous
    have hq := (P.isQuotientMap_quotMk S).restrictPreimage_isOpen hU
    refine hq.continuous_iff.2 ?_
    have key : ∀ x : P.Raw S, P.rawHeight S x ∈ J →
        g (Quotient.out (s := P.setoid S) (P.quotMk S x)) = g x := by
      intro x hx
      have h₁ : P.quotMk S (Quotient.out (s := P.setoid S) (P.quotMk S x)) = P.quotMk S x :=
        Quotient.out_eq _
      have h₂ := (P.quotMk_eq_iff S).1 h₁
      have hx' : P.rawHeight S (Quotient.out (s := P.setoid S) (P.quotMk S x)) ∈ J := by
        rw [← P.rawHeight_nf S, h₂, P.rawHeight_nf S]
        exact hx
      rw [← hresp _ hx', h₂, hresp x hx]
    have : (fun u : P.heightPreimage S J => g (Quotient.out (s := P.setoid S) u.1)) ∘
        (P.height S ⁻¹' (J : Set ℝ)).restrictPreimage (P.quotMk S) = fun x => g x.1 :=
      funext fun x => key x.1 x.2
    rw [this]
    exact hg.comp continuous_subtype_val

theorem descend_quotMk {Z : Type*} [TopologicalSpace Z] {J : OpenInterval} {g : P.Raw S → Z}
    {hg : Continuous g} {hresp : ∀ x, P.rawHeight S x ∈ J → g (P.nf S x) = g x}
    (x : P.Raw S) (hx : P.rawHeight S x ∈ J) :
    descend J g hg hresp ⟨P.quotMk S x, hx⟩ = g x := by
  have h₁ : P.quotMk S (Quotient.out (s := P.setoid S) (P.quotMk S x)) = P.quotMk S x :=
    Quotient.out_eq _
  have h₂ := (P.quotMk_eq_iff S).1 h₁
  have hx' : P.rawHeight S (Quotient.out (s := P.setoid S) (P.quotMk S x)) ∈ J := by
    rw [← P.rawHeight_nf S, h₂, P.rawHeight_nf S]
    exact hx
  show g (Quotient.out (s := P.setoid S) (P.quotMk S x)) = g x
  rw [← hresp _ hx', h₂, hresp x hx]

end pre

/-! ### The clamp homotopy -/

section clamp

variable {n : ℕ} {S : CriticalValues n} (P : CylinderPresentation.{u} n) {J : OpenInterval}
  (c : S.ClampData J)

/-- The clamp on a closed cylinder, with the homotopy parameter. -/
def clampCyl (e : Fin n) : C(P.Cylinder S e × unitInterval, P.Realization S) where
  toFun p := P.ofCylinder S e
    (p.1.1, projIcc _ _ (S.value_castSucc_lt_succ e).le (c.interp p.2 p.1.2))
  continuous_toFun := by
    have ht : Continuous fun p : P.Cylinder S e × unitInterval => (p.1.2 : ℝ) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
    have hs : Continuous fun p : P.Cylinder S e × unitInterval => (p.2 : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    have hi : Continuous fun p : P.Cylinder S e × unitInterval => c.interp p.2 p.1.2 :=
      ht.add (hs.mul ((c.continuous_clampHeight.comp ht).sub ht))
    exact (P.continuous_ofCylinder S e).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_projIcc.comp hi))

/-- The constant family on a vertex piece. -/
def clampVertex (i : Fin (n + 1)) : C(P.V i × unitInterval, P.Realization S) :=
  ⟨fun p => P.ofVertex S i p.1, (P.continuous_ofVertex S i).comp continuous_fst⟩

/-- The clamp family on the raw sum, as a map into paths. -/
def clampRaw : P.Raw S → C(unitInterval, P.Realization S) :=
  Sum.elim (fun p => (P.clampVertex p.1).curry p.2) fun q => (P.clampCyl c q.1).curry q.2

theorem continuous_clampRaw : Continuous (P.clampRaw c) :=
  Continuous.sumElim (continuous_sigma fun i => (P.clampVertex (S := S) i).curry.continuous)
    (continuous_sigma fun e => (P.clampCyl c e).curry.continuous)

theorem clampRaw_inl (p : P.VertexPiece) (s : unitInterval) :
    P.clampRaw c (.inl p) s = P.quotMk S (.inl p) := rfl

theorem clampRaw_inr (e : Fin n) (y : P.E e) (t : Seg S e) (s : unitInterval) :
    P.clampRaw c (.inr ⟨e, y, t⟩) s = P.ofCylinder S e
      (y, projIcc _ _ (S.value_castSucc_lt_succ e).le (c.interp s t)) := rfl

theorem clampRaw_nf (x : P.Raw S) (hx : P.rawHeight S x ∈ J) :
    P.clampRaw c (P.nf S x) = P.clampRaw c x := by
  rcases x with p | ⟨e, y, t⟩
  · rfl
  · have hxJ : (t : ℝ) ∈ (J : Set ℝ) := hx
    simp only [nf, Sum.elim_inr, nfCyl]
    split_ifs with h₁ h₂
    · have hm : (t : ℝ) ∈ Icc c.lo c.hi := by rw [h₁]; exact c.value_mem _ (h₁ ▸ hxJ)
      ext s
      rw [clampRaw_inl, clampRaw_inr, c.interp_of_mem hm, projIcc_val,
        show t = segBot S e from Subtype.ext h₁, ofCylinder_segBot]
      rfl
    · have hm : (t : ℝ) ∈ Icc c.lo c.hi := by rw [h₂]; exact c.value_mem _ (h₂ ▸ hxJ)
      ext s
      rw [clampRaw_inl, clampRaw_inr, c.interp_of_mem hm, projIcc_val,
        show t = segTop S e from Subtype.ext h₂, ofCylinder_segTop]
      rfl
    · rfl

/-- The descended clamp family `h⁻¹ J → C([0,1], X)`. -/
def clampFamily : C(P.heightPreimage S J, C(unitInterval, P.Realization S)) :=
  descend J (P.clampRaw c) (P.continuous_clampRaw c) fun x hx => P.clampRaw_nf c x hx

theorem clampFamily_quotMk (x : P.Raw S) (hx : P.rawHeight S x ∈ J) :
    P.clampFamily c ⟨P.quotMk S x, hx⟩ = P.clampRaw c x :=
  descend_quotMk x hx

theorem height_clampRaw (x : P.Raw S) (hx : P.rawHeight S x ∈ J) (s : unitInterval) :
    P.height S (P.clampRaw c x s) = c.interp s (P.rawHeight S x) := by
  rcases x with ⟨k, v⟩ | ⟨e, y, t⟩
  · exact (c.interp_of_mem (c.value_mem k hx) s).symm
  · rw [clampRaw_inr, height_ofCylinder,
      projIcc_of_mem _ (c.interp_mem_seg s.2 t.2 hx)]
    rfl

theorem clampRaw_zero (x : P.Raw S) : P.clampRaw c x 0 = P.quotMk S x := by
  rcases x with p | ⟨e, y, t⟩
  · rfl
  · rw [clampRaw_inr]
    simp only [Set.Icc.coe_zero, c.interp_zero, projIcc_val]
    rfl

theorem clampRaw_of_mem (x : P.Raw S) (hx : P.rawHeight S x ∈ Icc c.lo c.hi) (s : unitInterval) :
    P.clampRaw c x s = P.quotMk S x := by
  rcases x with p | ⟨e, y, t⟩
  · rfl
  · rw [clampRaw_inr, c.interp_of_mem (show (t : ℝ) ∈ Icc c.lo c.hi from hx), projIcc_val]
    rfl

theorem height_clampFamily (u : P.heightPreimage S J) (s : unitInterval) :
    P.height S (P.clampFamily c u s) = c.interp s (P.height S u.1) := by
  obtain ⟨x, hx, rfl⟩ := P.exists_quotMk S u
  rw [clampFamily_quotMk, height_clampRaw _ _ _ hx]
  rfl

theorem clampFamily_zero (u : P.heightPreimage S J) : P.clampFamily c u 0 = u.1 := by
  obtain ⟨x, hx, rfl⟩ := P.exists_quotMk S u
  rw [clampFamily_quotMk, clampRaw_zero]

theorem clampFamily_of_mem (u : P.heightPreimage S J) (hu : P.height S u.1 ∈ Icc c.lo c.hi)
    (s : unitInterval) : P.clampFamily c u s = u.1 := by
  obtain ⟨x, hx, rfl⟩ := P.exists_quotMk S u
  rw [clampFamily_quotMk, clampRaw_of_mem _ _ _ hu]

theorem height_clampFamily_one (u : P.heightPreimage S J) :
    P.height S (P.clampFamily c u 1) = c.clampHeight (P.height S u.1) := by
  rw [height_clampFamily]
  exact c.interp_one _

theorem continuous_clampFamily_one :
    Continuous fun u : P.heightPreimage S J => P.clampFamily c u 1 :=
  (continuous_eval_const (1 : unitInterval)).comp (P.clampFamily c).continuous

theorem height_clampFamily_mem {W : OpenInterval} (hW : Icc c.lo c.hi ⊆ (W : Set ℝ))
    (u : P.heightPreimage S J) (hu : P.height S u.1 ∈ W) (s : unitInterval) :
    P.height S (P.clampFamily c u s) ∈ W := by
  rw [height_clampFamily]
  exact W.ordConnected.uIcc_subset hu (hW (c.clampHeight_mem_Icc _)) (c.interp_mem_uIcc s.2 _)

theorem clampFamily_one_mem_Icc (u : P.heightPreimage S J) :
    P.height S (P.clampFamily c u 1) ∈ Icc c.lo c.hi := by
  rw [height_clampFamily_one]
  exact c.clampHeight_mem_Icc _

/-- The end map of the clamp, restricted to `h⁻¹ W` for `[lo, hi] ⊆ W ≤ J`. -/
def clampEnd (W : OpenInterval) (hW : Icc c.lo c.hi ⊆ (W : Set ℝ)) (hWJ : W ≤ J) :
    C(P.heightPreimage S W, P.heightPreimage S W) where
  toFun u := ⟨P.clampFamily c ⟨u.1, hWJ u.2⟩ 1, hW (P.clampFamily_one_mem_Icc c _)⟩
  continuous_toFun := ((P.continuous_clampFamily_one c).comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

/-- The clamp homotopy from the identity of `h⁻¹ W` to the end map. -/
def clampHomotopy (W : OpenInterval) (hW : Icc c.lo c.hi ⊆ (W : Set ℝ)) (hWJ : W ≤ J) :
    ContinuousMap.Homotopy (ContinuousMap.id (P.heightPreimage S W)) (P.clampEnd c W hW hWJ) where
  toFun p := ⟨P.clampFamily c ⟨p.2.1, hWJ p.2.2⟩ p.1,
    P.height_clampFamily_mem c hW _ p.2.2 p.1⟩
  continuous_toFun := by
    have h := ContinuousMap.continuous_uncurry_of_continuous (P.clampFamily c)
    exact (h.comp (((continuous_subtype_val.comp continuous_snd).subtype_mk _).prodMk
      continuous_fst)).subtype_mk _
  map_zero_left u := Subtype.ext (P.clampFamily_zero c _)
  map_one_left _ := rfl

end clamp

/-! ### Vertex, regular and nested homotopy equivalences -/

section equivalences

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{u} n)

/-- Clamp data at a level, inside its star. -/
def vertexClamp (i : Fin (n + 1)) : S.ClampData (S.J i) where
  lo := S.value i
  hi := S.value i
  lo_le_hi := le_rfl
  Icc_subset x hx := by
    obtain rfl : x = S.value i := le_antisymm hx.2 hx.1
    exact S.value_mem_J i
  value_mem k hk := by
    rw [S.value_mem_J_iff.1 hk]
    exact ⟨le_rfl, le_rfl⟩

/-- Clamp data at a regular height, inside its gap. -/
def regularClamp (e : Fin n) (t : (S.K e : Set ℝ)) : S.ClampData (S.K e) where
  lo := t
  hi := t
  lo_le_hi := le_rfl
  Icc_subset x hx := by
    obtain rfl : x = t := le_antisymm hx.2 hx.1
    exact t.2
  value_mem k hk := absurd hk (S.value_notMem_K e k)

/-- The vertex fiber inclusion `V i → h⁻¹(J i)`. -/
def vertexFiberInclusion (i : Fin (n + 1)) : C(P.V i, P.heightPreimage S (S.J i)) :=
  ⟨fun v => ⟨P.ofVertex S i v, S.value_mem_J i⟩, (P.continuous_ofVertex S i).subtype_mk _⟩

/-- The regular fiber inclusion `E e → h⁻¹(K e)` at the height `t`. -/
def regularFiberInclusion (e : Fin n) (t : (S.K e : Set ℝ)) :
    C(P.E e, P.heightPreimage S (S.K e)) :=
  ⟨fun y => ⟨P.ofStrip S e (y, t), t.2⟩,
    ((P.continuous_ofStrip S e).comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩

@[simp] theorem vertexFiberInclusion_apply (i : Fin (n + 1)) (v : P.V i) :
    (P.vertexFiberInclusion S i v : P.Realization S) = P.ofVertex S i v := rfl

@[simp] theorem regularFiberInclusion_apply (e : Fin n) (t : (S.K e : Set ℝ)) (y : P.E e) :
    (P.regularFiberInclusion S e t y : P.Realization S) = P.ofStrip S e (y, t) := rfl

theorem vertexClamp_one_mem (i : Fin (n + 1)) (u : P.heightPreimage S (S.J i)) :
    P.clampFamily (vertexClamp S i) u 1 ∈ P.height S ⁻¹' {S.value i} :=
  le_antisymm (P.clampFamily_one_mem_Icc (vertexClamp S i) u).2
    (P.clampFamily_one_mem_Icc (vertexClamp S i) u).1

theorem regularClamp_one_mem (e : Fin n) (t : (S.K e : Set ℝ)) (u : P.heightPreimage S (S.K e)) :
    P.clampFamily (regularClamp S e t) u 1 ∈ P.height S ⁻¹' {(t : ℝ)} :=
  le_antisymm (P.clampFamily_one_mem_Icc (regularClamp S e t) u).2
    (P.clampFamily_one_mem_Icc (regularClamp S e t) u).1

/-- The retraction of the star onto its vertex piece (the clamp end, read in the critical
fiber). -/
def vertexRetraction (i : Fin (n + 1)) : C(P.heightPreimage S (S.J i), P.V i) :=
  (⟨(P.criticalFiberHomeomorph S i).symm, (P.criticalFiberHomeomorph S i).symm.continuous⟩ : C(_, P.V i)).comp
    ⟨fun u => ⟨P.clampFamily (vertexClamp S i) u 1, P.vertexClamp_one_mem S i u⟩,
      (P.continuous_clampFamily_one _).subtype_mk _⟩

/-- The retraction of the gap onto the regular fiber at `t`. -/
def regularRetraction (e : Fin n) (t : (S.K e : Set ℝ)) : C(P.heightPreimage S (S.K e), P.E e) :=
  (⟨(P.regularFiberHomeomorph S e t).symm, (P.regularFiberHomeomorph S e t).symm.continuous⟩ : C(_, P.E e)).comp
    ⟨fun u => ⟨P.clampFamily (regularClamp S e t) u 1, P.regularClamp_one_mem S e t u⟩,
      (P.continuous_clampFamily_one _).subtype_mk _⟩

theorem vertexRetraction_comp_inclusion (i : Fin (n + 1)) :
    (P.vertexRetraction S i).comp (P.vertexFiberInclusion S i) = ContinuousMap.id _ := by
  ext v
  change (P.criticalFiberHomeomorph S i).symm
    ⟨P.clampFamily (vertexClamp S i) (P.vertexFiberInclusion S i v) 1, _⟩ = v
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext (P.clampFamily_of_mem (vertexClamp S i) _ ⟨le_rfl, le_rfl⟩ 1)

theorem vertexInclusion_comp_retraction (i : Fin (n + 1)) :
    (P.vertexFiberInclusion S i).comp (P.vertexRetraction S i) =
      P.clampEnd (vertexClamp S i) (S.J i) (vertexClamp S i).Icc_subset le_rfl := by
  refine ContinuousMap.ext fun u => Subtype.ext ?_
  have h := congrArg Subtype.val ((P.criticalFiberHomeomorph S i).apply_symm_apply
    ⟨P.clampFamily (vertexClamp S i) u 1, P.vertexClamp_one_mem S i u⟩)
  exact h

theorem regularRetraction_comp_inclusion (e : Fin n) (t : (S.K e : Set ℝ)) :
    (P.regularRetraction S e t).comp (P.regularFiberInclusion S e t) = ContinuousMap.id _ := by
  ext y
  change (P.regularFiberHomeomorph S e t).symm
    ⟨P.clampFamily (regularClamp S e t) (P.regularFiberInclusion S e t y) 1, _⟩ = y
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext (P.clampFamily_of_mem (regularClamp S e t) _ ⟨le_rfl, le_rfl⟩ 1)

theorem regularInclusion_comp_retraction (e : Fin n) (t : (S.K e : Set ℝ)) :
    (P.regularFiberInclusion S e t).comp (P.regularRetraction S e t) =
      P.clampEnd (regularClamp S e t) (S.K e) (regularClamp S e t).Icc_subset le_rfl := by
  refine ContinuousMap.ext fun u => Subtype.ext ?_
  have h := congrArg Subtype.val ((P.regularFiberHomeomorph S e t).apply_symm_apply
    ⟨P.clampFamily (regularClamp S e t) u 1, P.regularClamp_one_mem S e t u⟩)
  exact h

/-- `V i → h⁻¹(J i)` is a homotopy equivalence (DMP Lemma 2.4, vertex case). -/
def vertexHomotopyEquiv (i : Fin (n + 1)) :
    ContinuousMap.HomotopyEquiv (P.V i) (P.heightPreimage S (S.J i)) where
  toFun := P.vertexFiberInclusion S i
  invFun := P.vertexRetraction S i
  left_inv := by
    rw [vertexRetraction_comp_inclusion]
  right_inv := by
    rw [vertexInclusion_comp_retraction]
    exact ContinuousMap.Homotopic.symm ⟨P.clampHomotopy _ _ _ _⟩

/-- `E e → h⁻¹(K e)` at an interior height is a homotopy equivalence (DMP Lemma 2.4, edge
case). -/
def regularHomotopyEquiv (e : Fin n) (t : (S.K e : Set ℝ)) :
    ContinuousMap.HomotopyEquiv (P.E e) (P.heightPreimage S (S.K e)) where
  toFun := P.regularFiberInclusion S e t
  invFun := P.regularRetraction S e t
  left_inv := by
    rw [regularRetraction_comp_inclusion]
  right_inv := by
    rw [regularInclusion_comp_retraction]
    exact ContinuousMap.Homotopic.symm ⟨P.clampHomotopy _ _ _ _⟩

/-- Path components of the vertex piece are the values on the star. -/
def vertexComponentsEquiv (i : Fin (n + 1)) :
    ZerothHomotopy (P.V i) ≃ (intervalComponents (P.height S)).obj (S.J i) :=
  componentEquivOfHomotopyEquiv (P.vertexHomotopyEquiv S i)

/-- Path components of the edge piece are the values on the gap. -/
def edgeComponentsEquiv (e : Fin n) (t : (S.K e : Set ℝ)) :
    ZerothHomotopy (P.E e) ≃ (intervalComponents (P.height S)).obj (S.K e) :=
  componentEquivOfHomotopyEquiv (P.regularHomotopyEquiv S e t)

theorem vertexComponentsEquiv_mk (i : Fin (n + 1)) (v : P.V i) :
    P.vertexComponentsEquiv S i (.mk v) = .mk (P.vertexFiberInclusion S i v) := rfl

theorem edgeComponentsEquiv_mk (e : Fin n) (t : (S.K e : Set ℝ)) (y : P.E e) :
    P.edgeComponentsEquiv S e t (.mk y) = .mk (P.regularFiberInclusion S e t y) := rfl

/-- The inclusion `h⁻¹ I → h⁻¹ J`. -/
def nestedInclusion {I J : OpenInterval} (hIJ : I ≤ J) :
    C(P.heightPreimage S I, P.heightPreimage S J) :=
  ⟨fun u => ⟨u.1, hIJ u.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- For nonempty `I ≤ J` meeting the same levels, `h⁻¹ I → h⁻¹ J` is a homotopy equivalence
(not a deformation retraction onto the open subspace). -/
def nestedHomotopyEquiv {I J : OpenInterval} (hIJ : I ≤ J) (hI : (I : Set ℝ).Nonempty)
    (hhit : ∀ i, S.value i ∈ I ↔ S.value i ∈ J) :
    ContinuousMap.HomotopyEquiv (P.heightPreimage S I) (P.heightPreimage S J) :=
  let c := (S.exists_clampData_of_le hIJ hI hhit).choose
  have hc : Icc c.lo c.hi ⊆ (I : Set ℝ) := (S.exists_clampData_of_le hIJ hI hhit).choose_spec
  { toFun := P.nestedInclusion S hIJ
    invFun := ⟨fun u => ⟨P.clampFamily c u 1, hc (P.clampFamily_one_mem_Icc c u)⟩,
      (P.continuous_clampFamily_one c).subtype_mk _⟩
    left_inv := ContinuousMap.Homotopic.symm ⟨P.clampHomotopy c I hc hIJ⟩
    right_inv := ContinuousMap.Homotopic.symm ⟨P.clampHomotopy c J (hc.trans hIJ) le_rfl⟩ }

/-! ### Constructibility of `intervalComponents` -/

/-- Bijectivity clause: for nonempty `I ≤ J` meeting the same levels, the actual map is
bijective. -/
theorem intervalComponents_map_bijective {I J : OpenInterval} (hIJ : I ≤ J)
    (hI : (I : Set ℝ).Nonempty) (hhit : ∀ i, S.value i ∈ I ↔ S.value i ∈ J) :
    Function.Bijective ((intervalComponents (P.height S)).map (homOfLE hIJ)) := by
  have h : ⇑((intervalComponents (P.height S)).map (homOfLE hIJ)) =
      componentEquivOfHomotopyEquiv (P.nestedHomotopyEquiv S hIJ hI hhit) := by
    funext c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  rw [h]
  exact Equiv.bijective _

/-- Exterior values are empty. -/
theorem isEmpty_intervalComponents_lowerTail :
    IsEmpty ((intervalComponents (P.height S)).obj S.lowerTail) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x =>
      have hx : x.1 ∈ P.height S ⁻¹' (S.lowerTail : Set ℝ) := x.2
      rw [P.height_preimage_lowerTail S] at hx
      exact hx⟩

theorem isEmpty_intervalComponents_upperTail :
    IsEmpty ((intervalComponents (P.height S)).obj S.upperTail) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x =>
      have hx : x.1 ∈ P.height S ⁻¹' (S.upperTail : Set ℝ) := x.2
      rw [P.height_preimage_upperTail S] at hx
      exact hx⟩

/-- Finiteness from finitely many path components of every piece. -/
theorem finite_intervalComponents [∀ i, Finite (ZerothHomotopy (P.V i))]
    [∀ e, Finite (ZerothHomotopy (P.E e))] (I : OpenInterval) :
    Finite ((intervalComponents (P.height S)).obj I) := by
  by_cases hne : (I : Set ℝ).Nonempty
  swap
  · have : IsEmpty ((intervalComponents (P.height S)).obj I) :=
      ⟨fun c => by
        induction c using ZerothHomotopy.rec with
        | mk x => exact hne ⟨_, x.2⟩⟩
    infer_instance
  let vI : ∀ k : {k : Fin (n + 1) // S.value k ∈ I}, C(P.V k.1, P.heightPreimage S I) :=
    fun k =>
    ⟨fun v => ⟨P.ofVertex S k.1 v, k.2⟩, (P.continuous_ofVertex S k.1).subtype_mk _⟩
  let eI : ∀ e : {e : Fin n // I ≤ S.K e}, C(P.E e.1, P.heightPreimage S I) := fun e =>
    ⟨fun y => ⟨P.ofStrip S e.1 (y, ⟨hne.some, e.2 hne.some_mem⟩), hne.some_mem⟩,
      ((P.continuous_ofStrip S e.1).comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩
  let Φ : (Σ k : {k : Fin (n + 1) // S.value k ∈ I}, ZerothHomotopy (P.V k.1)) ⊕
      (Σ e : {e : Fin n // I ≤ S.K e}, ZerothHomotopy (P.E e.1)) →
        (intervalComponents (P.height S)).obj I :=
    Sum.elim (fun p => componentMap (vI p.1) p.2) fun p => componentMap (eI p.1) p.2
  refine Finite.of_surjective Φ fun c => ?_
  induction c using ZerothHomotopy.rec with
  | mk u =>
    obtain ⟨q, hq⟩ := u
    rcases P.exists_rep S q with ⟨k, v, rfl⟩ | ⟨e, ⟨y, t⟩, rfl⟩
    · exact ⟨.inl ⟨⟨k, hq⟩, .mk v⟩, rfl⟩
    · have htI : (t : ℝ) ∈ (I : Set ℝ) := hq
      by_cases ha : S.value e.castSucc ∈ I
      · refine ⟨.inl ⟨⟨e.castSucc, ha⟩, .mk (P.left e y)⟩, mk_eq_of_joinedIn ?_⟩
        have h := P.joinedIn_cylinder S e y (segBot S e) (gapIncl S e t)
        rw [ofCylinder_segBot] at h
        exact h.mono (preimage_mono (I.ordConnected.uIcc_subset ha htI))
      by_cases hb : S.value e.succ ∈ I
      · refine ⟨.inl ⟨⟨e.succ, hb⟩, .mk (P.right e y)⟩, mk_eq_of_joinedIn ?_⟩
        have h := P.joinedIn_cylinder S e y (segTop S e) (gapIncl S e t)
        rw [ofCylinder_segTop] at h
        exact h.mono (preimage_mono (I.ordConnected.uIcc_subset hb htI))
      have hIK : I ≤ S.K e := fun z hz => by
        refine ⟨lt_of_not_ge fun h => ha ?_, lt_of_not_ge fun h => hb ?_⟩
        · exact I.ordConnected.out hz htI ⟨h, t.2.1.le⟩
        · exact I.ordConnected.out htI hz ⟨t.2.2.le, h⟩
      refine ⟨.inr ⟨⟨e, hIK⟩, .mk y⟩, mk_eq_of_joinedIn ?_⟩
      exact (P.joinedIn_cylinder S e y (gapIncl S e ⟨hne.some, hIK hne.some_mem⟩)
        (gapIncl S e t)).mono (preimage_mono (I.ordConnected.uIcc_subset hne.some_mem htI))

/-- `intervalComponents` of a realization is constructible at its levels, when every piece has
finitely many path components. -/
theorem intervalComponents_isConstructibleAt [∀ i, Finite (ZerothHomotopy (P.V i))]
    [∀ e, Finite (ZerothHomotopy (P.E e))] :
    S.IsConstructibleAt (intervalComponents (P.height S)) where
  finite := P.finite_intervalComponents S
  bijective _ _ h hI hhit := P.intervalComponents_map_bijective S h hI hhit
  isEmpty_lowerTail := P.isEmpty_intervalComponents_lowerTail S
  isEmpty_upperTail := P.isEmpty_intervalComponents_upperTail S

/-- The DMP hypothesis (compact, locally path-connected pieces) suffices. -/
theorem isConstructibleAt_of_compact_lpc [∀ i, CompactSpace (P.V i)]
    [∀ i, LocallyPathConnectedSpace (P.V i)] [∀ e, CompactSpace (P.E e)]
    [∀ e, LocallyPathConnectedSpace (P.E e)] :
    S.IsConstructibleAt (intervalComponents (P.height S)) :=
  P.intervalComponents_isConstructibleAt S

instance finiteData_finite_V (D : FiniteReebData.{u} n) (i : Fin (n + 1)) :
    Finite (ZerothHomotopy ((ofFiniteData D).V i)) :=
  Finite.of_equiv _ (zerothHomotopyEquivOfDiscrete _).symm

instance finiteData_finite_E (D : FiniteReebData.{u} n) (e : Fin n) :
    Finite (ZerothHomotopy ((ofFiniteData D).E e)) :=
  Finite.of_equiv _ (zerothHomotopyEquivOfDiscrete _).symm

/-- Realized finite data are constructible. -/
theorem finiteData_isConstructibleAt (D : FiniteReebData.{u} n) :
    S.IsConstructibleAt (intervalComponents ((ofFiniteData D).height S)) :=
  (ofFiniteData D).intervalComponents_isConstructibleAt S

/-! ### Incidence compatibility -/

/-- The left gap-to-star map carries the edge components to the left endpoint map. -/
theorem map_K_le_J_castSucc_edgeComponentsEquiv (e : Fin n) (t : (S.K e : Set ℝ))
    (c : ZerothHomotopy (P.E e)) :
    (intervalComponents (P.height S)).map (homOfLE (S.K_le_J_castSucc e))
        (P.edgeComponentsEquiv S e t c) =
      P.vertexComponentsEquiv S e.castSucc (componentMap (P.left e) c) := by
  induction c using ZerothHomotopy.rec with
  | mk y =>
    refine mk_eq_of_joinedIn (W := S.J e.castSucc) ?_
    have h := P.joinedIn_cylinder S e y (gapIncl S e t) (segBot S e)
    rw [ofCylinder_segBot] at h
    exact h.mono (preimage_mono ((S.J e.castSucc).ordConnected.uIcc_subset
      (S.K_le_J_castSucc e t.2) (S.value_mem_J _)))

/-- The right gap-to-star map carries the edge components to the right endpoint map. -/
theorem map_K_le_J_succ_edgeComponentsEquiv (e : Fin n) (t : (S.K e : Set ℝ))
    (c : ZerothHomotopy (P.E e)) :
    (intervalComponents (P.height S)).map (homOfLE (S.K_le_J_succ e))
        (P.edgeComponentsEquiv S e t c) =
      P.vertexComponentsEquiv S e.succ (componentMap (P.right e) c) := by
  induction c using ZerothHomotopy.rec with
  | mk y =>
    refine mk_eq_of_joinedIn (W := S.J e.succ) ?_
    have h := P.joinedIn_cylinder S e y (gapIncl S e t) (segTop S e)
    rw [ofCylinder_segTop] at h
    exact h.mono (preimage_mono ((S.J e.succ).ordConnected.uIcc_subset
      (S.K_le_J_succ e t.2) (S.value_mem_J _)))

/-- Conjugated form: the component bijections carry `K e ≤ J e.castSucc` to
`componentMap (left e)`. -/
theorem vertexComponentsEquiv_symm_map_castSucc (e : Fin n) (t : (S.K e : Set ℝ))
    (c : ZerothHomotopy (P.E e)) :
    (P.vertexComponentsEquiv S e.castSucc).symm
        ((intervalComponents (P.height S)).map (homOfLE (S.K_le_J_castSucc e))
          (P.edgeComponentsEquiv S e t c)) = componentMap (P.left e) c := by
  rw [Equiv.symm_apply_eq]
  exact P.map_K_le_J_castSucc_edgeComponentsEquiv S e t c

theorem vertexComponentsEquiv_symm_map_succ (e : Fin n) (t : (S.K e : Set ℝ))
    (c : ZerothHomotopy (P.E e)) :
    (P.vertexComponentsEquiv S e.succ).symm
        ((intervalComponents (P.height S)).map (homOfLE (S.K_le_J_succ e))
          (P.edgeComponentsEquiv S e t c)) = componentMap (P.right e) c := by
  rw [Equiv.symm_apply_eq]
  exact P.map_K_le_J_succ_edgeComponentsEquiv S e t c

end equivalences

/-! ### Naturality under arbitrary height-preserving maps -/

section naturality

variable {n : ℕ} (S : CriticalValues n) {P P' : CylinderPresentation.{u} n}
  (φ : C(P.Realization S, P'.Realization S)) (hφ : ∀ x, P'.height S (φ x) = P.height S x)

/-- The map induced on vertex pieces by restriction to the critical fiber. -/
def vertexFiberMap (i : Fin (n + 1)) : C(P.V i, P'.V i) :=
  (⟨(P'.criticalFiberHomeomorph S i).symm, (P'.criticalFiberHomeomorph S i).symm.continuous⟩ : C(_, P'.V i)).comp
    ⟨fun v => ⟨φ (P.ofVertex S i v), hφ _⟩, (φ.continuous.comp (P.continuous_ofVertex S i)).subtype_mk _⟩

/-- The map induced on edge pieces by restriction to the regular fiber at `t`. -/
def regularFiberMap (e : Fin n) (t : (S.K e : Set ℝ)) : C(P.E e, P'.E e) :=
  (⟨(P'.regularFiberHomeomorph S e t).symm, (P'.regularFiberHomeomorph S e t).symm.continuous⟩ : C(_, P'.E e)).comp
    ⟨fun y => ⟨φ (P.ofStrip S e (y, t)), hφ _⟩,
      (φ.continuous.comp ((P.continuous_ofStrip S e).comp
        (continuous_id.prodMk continuous_const))).subtype_mk _⟩

theorem map_ofVertex_eq (i : Fin (n + 1)) (v : P.V i) :
    φ (P.ofVertex S i v) = P'.ofVertex S i (vertexFiberMap S φ hφ i v) := by
  have := congrArg Subtype.val
    ((P'.criticalFiberHomeomorph S i).apply_symm_apply ⟨φ (P.ofVertex S i v), hφ _⟩)
  rw [criticalFiberHomeomorph_apply] at this
  exact this.symm

theorem map_ofStrip_eq (e : Fin n) (t : (S.K e : Set ℝ)) (y : P.E e) :
    φ (P.ofStrip S e (y, t)) = P'.ofStrip S e (regularFiberMap S φ hφ e t y, t) := by
  have := congrArg Subtype.val
    ((P'.regularFiberHomeomorph S e t).apply_symm_apply ⟨φ (P.ofStrip S e (y, t)), hφ _⟩)
  rw [regularFiberHomeomorph_apply] at this
  exact this.symm

/-- The actual vertex fiber inclusions commute with `φ` on the nose. -/
theorem vertexFiberInclusion_naturality (i : Fin (n + 1)) :
    (preimageRestrict φ hφ (OpenInterval.toOpens (S.J i))).comp (P.vertexFiberInclusion S i) =
      (P'.vertexFiberInclusion S i).comp (vertexFiberMap S φ hφ i) := by
  ext v
  exact map_ofVertex_eq S φ hφ i v

/-- The actual regular fiber inclusions commute with `φ` on the nose. -/
theorem regularFiberInclusion_naturality (e : Fin n) (t : (S.K e : Set ℝ)) :
    (preimageRestrict φ hφ (OpenInterval.toOpens (S.K e))).comp (P.regularFiberInclusion S e t) =
      (P'.regularFiberInclusion S e t).comp (regularFiberMap S φ hφ e t) := by
  ext y
  exact map_ofStrip_eq S φ hφ e t y

/-- Naturality of the vertex component bijections for `componentNatTrans φ`. -/
theorem componentNatTrans_vertexComponentsEquiv (i : Fin (n + 1)) (c : ZerothHomotopy (P.V i)) :
    (componentNatTrans φ hφ).app (OpenInterval.toOpens (S.J i)) (P.vertexComponentsEquiv S i c) =
      P'.vertexComponentsEquiv S i (componentMap (vertexFiberMap S φ hφ i) c) := by
  induction c using ZerothHomotopy.rec with
  | mk v => exact congrArg ZerothHomotopy.mk (Subtype.ext (map_ofVertex_eq S φ hφ i v))

/-- Naturality of the edge component bijections for `componentNatTrans φ`. -/
theorem componentNatTrans_edgeComponentsEquiv (e : Fin n) (t : (S.K e : Set ℝ))
    (c : ZerothHomotopy (P.E e)) :
    (componentNatTrans φ hφ).app (OpenInterval.toOpens (S.K e)) (P.edgeComponentsEquiv S e t c) =
      P'.edgeComponentsEquiv S e t (componentMap (regularFiberMap S φ hφ e t) c) := by
  induction c using ZerothHomotopy.rec with
  | mk y => exact congrArg ZerothHomotopy.mk (Subtype.ext (map_ofStrip_eq S φ hφ e t y))

/-- The vertex square for the restriction of `componentNatTrans φ` to open intervals. -/
theorem whiskerLeft_componentNatTrans_vertexComponentsEquiv (i : Fin (n + 1))
    (c : ZerothHomotopy (P.V i)) :
    (Functor.whiskerLeft OpenInterval.toOpensFunctor (componentNatTrans φ hφ)).app (S.J i)
        (P.vertexComponentsEquiv S i c) =
      P'.vertexComponentsEquiv S i (componentMap (vertexFiberMap S φ hφ i) c) :=
  componentNatTrans_vertexComponentsEquiv S φ hφ i c

/-- The edge square for the restriction of `componentNatTrans φ` to open intervals. -/
theorem whiskerLeft_componentNatTrans_edgeComponentsEquiv (e : Fin n) (t : (S.K e : Set ℝ))
    (c : ZerothHomotopy (P.E e)) :
    (Functor.whiskerLeft OpenInterval.toOpensFunctor (componentNatTrans φ hφ)).app (S.K e)
        (P.edgeComponentsEquiv S e t c) =
      P'.edgeComponentsEquiv S e t (componentMap (regularFiberMap S φ hφ e t) c) :=
  componentNatTrans_edgeComponentsEquiv S φ hφ e t c

end naturality

/-! ### Independence of the regular height on path components -/

section indep

variable {n : ℕ} (S : CriticalValues n)

/-- The edge component bijection does not depend on the chosen regular height. -/
theorem edgeComponentsEquiv_indep (P : CylinderPresentation.{u} n) (e : Fin n)
    (t t' : (S.K e : Set ℝ)) : P.edgeComponentsEquiv S e t = P.edgeComponentsEquiv S e t' := by
  ext c
  induction c using ZerothHomotopy.rec with
  | mk y =>
    refine mk_eq_of_joinedIn (W := S.K e) ?_
    exact (P.joinedIn_cylinder S e y (gapIncl S e t) (gapIncl S e t')).mono
      (preimage_mono ((S.K e).ordConnected.uIcc_subset t.2 t'.2))

/-- On path components, the regular fiber map of a height-preserving map does not depend on the
height. (Pointwise it does in general: a height-dependent rotation of a circle strip.) -/
theorem componentMap_regularFiberMap_indep {P P' : CylinderPresentation.{u} n}
    (φ : C(P.Realization S, P'.Realization S)) (hφ : ∀ x, P'.height S (φ x) = P.height S x)
    (e : Fin n) (t t' : (S.K e : Set ℝ)) :
    componentMap (regularFiberMap S φ hφ e t) = componentMap (regularFiberMap S φ hφ e t') := by
  funext c
  apply (P'.edgeComponentsEquiv S e t).injective
  rw [← componentNatTrans_edgeComponentsEquiv, P'.edgeComponentsEquiv_indep S e t t',
    ← componentNatTrans_edgeComponentsEquiv, P.edgeComponentsEquiv_indep S e t t']

end indep

end CylinderPresentation

end

end TDA.Reeb
