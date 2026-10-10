import TDA.Reeb.RGraph
import Mathlib.Data.Finset.Sort
import Mathlib.CategoryTheory.HomCongr

/-!
# Refinement of finite ℝ-graph presentations

Let `S : CriticalValues n` and `T : CriticalValues m` with `range S.value ⊆ range T.value`, and
let `D : FiniteReebData n`. This file presents the realization of `D` over `S` as the realization
of finite data over the finer list `T`. It follows that the classification of maps between graph
objects does not depend on the chosen presentations (de Silva–Munch–Patel, Remark 2.3 and the
common critical set of Proposition 2.8).

## Refined data

The vertex set of `refineData hST D` at the `T`-level `t j` is the fiber of the realization over
`t j`, and the edge set of the `T`-gap `j` is the fiber over its base point `basePt T j`. A point
`y` of that base fiber lies on the open strip of an `S`-gap `e` whose closed segment contains the
whole closed `T`-segment of `j` (`Icc_subset_of_mem`). Following the cylinder of `y` gives a
continuous `edgePoint y` on the `T`-segment, and its two ends define the refined endpoint maps.

* The comparison `refineMap` from the refined realization comes from the universal property. It
  is height-preserving, injective and surjective by the normal forms, and a homeomorphism because
  the source is compact and the target Hausdorff (`refineHomeomorph`). In the real slice this is
  `refineIso hST D : toOver T (refineData hST D) ≅ toOver S D`.
* An inserted level `t j ∈ K e` has vertex set `E e` (`refineVEquiv`). Both adjacent `T`-gaps are
  based in `K e` (`basePt_mem_K_of_succ`, `basePt_mem_K_of_castSucc`) and have edge set `E e`
  (`refineEEquiv`), and both incidences are the identity (`refine_right_eq`, `refine_left_eq`).
  The endpoint maps into a level that is not an `S`-level are bijective (`right_bijective`,
  `left_bijective`).
* An old level `t j = a i` keeps its vertex set `V i` (`refineVEquivOld`). A `T`-gap based in
  `K e` can end at an old level only at `e.succ` and start at one only at `e.castSucc`
  (`old_level_succ`, `old_level_castSucc`); there the refined incidences are `D.right e` and
  `D.left e` (`refine_right_old`, `refine_left_old`).
* Exterior levels and gaps carry empty sets (`isEmpty_refine_V`, `isEmpty_refine_E`).

## Common refinements and coherence

The sorted union of two lists refines both (`exists_common_refinement`), so any two graph objects
are presented over one list (`exists_common_presentation`). For `S ⊆ T ⊆ U`, the two refinements
of `D` over `U` are related by the explicit data isomorphism `refineCoherentIso`, whose square
with the refinement isomorphisms commutes (`refineCoherentIso_comm`); it is the unique finite map
with that property (`refine_coherent`).

## Presentation independence

For presentations `iA : A ≅ toOver T DA` and `iB : B ≅ toOver T DB`, the bijection
`homEquivOfIso iA iB : (A ⟶ B) ≃ (DA ⟶ DB)` classifies slice morphisms, compatibly with identities
and composition (`homEquivOfIso_id`, `homEquivOfIso_comp`). Two presentations over the same `T`
give bijections conjugate by the data isomorphism `presIso` (`homEquivOfIso_conj`), and refining
both presentations commutes with the classification through `refineHom`
(`homEquivOfIso_refine`). Hence presentations over `T` and `T'`, transferred to a common
refinement `U`, give conjugate bijections (`homEquivOfIso_independent`). `refineHom`, `presIso`
and `refineCoherentIso` are obtained from full faithfulness of realization, and the lemmas above
determine them.

See `docs/math/reeb-rgraph.md`.
-/

open Set Topology CategoryTheory

universe u

namespace TDA.Reeb

noncomputable section

namespace RGraph

open CylinderPresentation

section refinement

variable {n m : ℕ} {S : CriticalValues n} {T : CriticalValues m}

variable (hST : Set.range S.value ⊆ Set.range T.value)

include hST in
/-- A point of a `T`-gap is not an `S`-level. -/
theorem value_ne {j : Fin m} {s : ℝ} (hs : s ∈ (T.K j : Set ℝ)) (i : Fin (n + 1)) :
    S.value i ≠ s := by
  intro h
  obtain ⟨k, hk⟩ := hST ⟨i, rfl⟩
  exact T.value_notMem_K j k (by rw [hk, h]; exact hs)

/-- A point of a closed `S`-segment that is not an `S`-level lies in the open gap. -/
theorem mem_K_of_ne {e : Fin n} {s : ℝ} (hs : s ∈ Icc (S.value e.castSucc) (S.value e.succ))
    (hne : ∀ i, S.value i ≠ s) : s ∈ (S.K e : Set ℝ) :=
  S.mem_K.2 ⟨lt_of_le_of_ne hs.1 (hne _), lt_of_le_of_ne hs.2 (hne _).symm⟩

include hST in
/-- A closed `T`-segment meeting the open `S`-gap `K e` lies in the closed `S`-segment of `e`. -/
theorem Icc_subset_of_mem {j : Fin m} {e : Fin n} {x : ℝ}
    (hx : x ∈ Icc (T.value j.castSucc) (T.value j.succ)) (hxe : x ∈ (S.K e : Set ℝ)) :
    Icc (T.value j.castSucc) (T.value j.succ) ⊆ Icc (S.value e.castSucc) (S.value e.succ) := by
  obtain ⟨k, hk⟩ := hST ⟨e.castSucc, rfl⟩
  obtain ⟨k', hk'⟩ := hST ⟨e.succ, rfl⟩
  have hxe' := S.mem_K.1 hxe
  have h1 : k < j.succ := T.strictMono.lt_iff_lt.1 (by rw [hk]; exact hxe'.1.trans_le hx.2)
  have h2 : j.castSucc < k' := T.strictMono.lt_iff_lt.1 (by rw [hk']; exact hx.1.trans_lt hxe'.2)
  have h1' : k ≤ j.castSucc := Fin.le_castSucc_iff.2 h1
  have h2' : j.succ ≤ k' := by
    rw [Fin.le_iff_val_le_val]
    have := Fin.lt_def.1 h2
    simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
    omega
  intro s hs
  refine ⟨?_, ?_⟩
  · rw [← hk]; exact (T.strictMono.monotone h1').trans hs.1
  · rw [← hk']; exact hs.2.trans (T.strictMono.monotone h2')

variable (D : FiniteReebData.{u} n)

/-- The point at height `t` on the cylinder of `(e, z)`, for `t` in the closed `T`-segment `j`
whose base point lies in `K e`. -/
def cylAt (j : Fin m) (e : Fin n) (z : D.E e) (h : (basePt T j : ℝ) ∈ (S.K e : Set ℝ))
    (t : Seg T j) : (ofFiniteData D).Realization S :=
  (ofFiniteData D).ofCylinder S e
    (z, ⟨t, Icc_subset_of_mem hST (Ioo_subset_Icc_self (basePt T j).2) h t.2⟩)

/-- Two descriptions of one base-fiber point give the same cylinder points. -/
theorem cylAt_congr (j : Fin m) {e e' : Fin n} (z : D.E e) (z' : D.E e')
    (h : (basePt T j : ℝ) ∈ (S.K e : Set ℝ)) (h' : (basePt T j : ℝ) ∈ (S.K e' : Set ℝ))
    (hzz : (ofFiniteData D).ofStrip S e (z, ⟨_, h⟩) =
      (ofFiniteData D).ofStrip S e' (z', ⟨_, h'⟩))
    (t : Seg T j) : cylAt hST D j e z h t = cylAt hST D j e' z' h' t := by
  obtain rfl : e = e' := S.eq_of_mem_K_of_mem_Icc h (Ioo_subset_Icc_self h')
  obtain rfl : z = z' := congrArg Prod.fst ((ofFiniteData D).ofStrip_injective S e hzz)
  rfl

include hST in
/-- Every point of the fiber over the base point of a `T`-gap is an open-strip point. -/
theorem exists_edge_rep (j : Fin m) (y : (ofFiniteData D).height S ⁻¹' {(basePt T j : ℝ)}) :
    ∃ (e : Fin n) (h : (basePt T j : ℝ) ∈ (S.K e : Set ℝ)) (z : D.E e),
      y.1 = (ofFiniteData D).ofStrip S e (z, ⟨_, h⟩) :=
  exists_strip_rep (ofFiniteData D) y.1 y.2 (value_ne hST (basePt T j).2)

/-- The point at height `t` on the edge through `y`. -/
def edgePoint (j : Fin m) (y : (ofFiniteData D).height S ⁻¹' {(basePt T j : ℝ)})
    (t : Seg T j) : (ofFiniteData D).Realization S :=
  cylAt hST D j (exists_edge_rep hST D j y).choose
    (exists_edge_rep hST D j y).choose_spec.choose_spec.choose
    (exists_edge_rep hST D j y).choose_spec.choose t

/-- `edgePoint` computed from any strip description of `y`. -/
theorem edgePoint_eq (j : Fin m) (y : (ofFiniteData D).height S ⁻¹' {(basePt T j : ℝ)})
    {e : Fin n} (z : D.E e) (h : (basePt T j : ℝ) ∈ (S.K e : Set ℝ))
    (hy : y.1 = (ofFiniteData D).ofStrip S e (z, ⟨_, h⟩)) (t : Seg T j) :
    edgePoint hST D j y t = cylAt hST D j e z h t :=
  cylAt_congr hST D j _ _ _ _
    ((exists_edge_rep hST D j y).choose_spec.choose_spec.choose_spec.symm.trans hy) t

/-- The edge through `y` is continuous on the closed `T`-segment. -/
theorem continuous_edgePoint (j : Fin m)
    (y : (ofFiniteData D).height S ⁻¹' {(basePt T j : ℝ)}) :
    Continuous (edgePoint hST D j y) :=
  ((ofFiniteData D).continuous_ofCylinder S _).comp
    (continuous_const.prodMk (continuous_subtype_val.subtype_mk _))

/-- At a height that is not an `S`-level, distinct edges through the base fiber stay apart. -/
theorem edgePoint_inj (j : Fin m) {y y' : (ofFiniteData D).height S ⁻¹' {(basePt T j : ℝ)}}
    (t : Seg T j) (hns : ∀ i, S.value i ≠ t)
    (hyy : edgePoint hST D j y t = edgePoint hST D j y' t) : y = y' := by
  obtain ⟨e, hs, z, hy⟩ := exists_edge_rep hST D j y
  obtain ⟨e', hs', z', hy'⟩ := exists_edge_rep hST D j y'
  rw [edgePoint_eq hST D j y z hs hy, edgePoint_eq hST D j y' z' hs' hy'] at hyy
  have hte : (t : ℝ) ∈ (S.K e : Set ℝ) :=
    mem_K_of_ne (Icc_subset_of_mem hST (Ioo_subset_Icc_self (basePt T j).2) hs t.2) hns
  have hte' : (t : ℝ) ∈ (S.K e' : Set ℝ) :=
    mem_K_of_ne (Icc_subset_of_mem hST (Ioo_subset_Icc_self (basePt T j).2) hs' t.2) hns
  obtain rfl : e = e' := S.eq_of_mem_K_of_mem_Icc hte (Ioo_subset_Icc_self hte')
  have h2 : (ofFiniteData D).ofStrip S e (z, ⟨t, hte⟩) =
      (ofFiniteData D).ofStrip S e (z', ⟨t, hte'⟩) := hyy
  obtain rfl : z = z' := congrArg Prod.fst ((ofFiniteData D).ofStrip_injective S e h2)
  exact Subtype.ext (hy.trans hy'.symm)

/-- **Refined data over a finer `T`**: vertex sets are the fibers at the `T`-levels, edge sets
the fibers at the base points of the `T`-gaps, endpoints by following the edge. -/
def refineData : FiniteReebData.{u} m where
  V j := (ofFiniteData D).height S ⁻¹' {T.value j}
  E j := (ofFiniteData D).height S ⁻¹' {(basePt T j : ℝ)}
  finiteV _ := finite_fiber S D _
  finiteE _ := finite_fiber S D _
  left j y := ⟨edgePoint hST D j y (segBot T j), rfl⟩
  right j y := ⟨edgePoint hST D j y (segTop T j), rfl⟩

/-- The comparison map from the refined realization, by the universal property. -/
def refineMap :
    C((ofFiniteData (refineData hST D)).Realization T, (ofFiniteData D).Realization S) :=
  lift
    { vertex := fun _ => ⟨fun v => v.1, continuous_of_discreteTopology⟩
      cylinder := fun j => ⟨fun p => edgePoint hST D j p.1 p.2,
        continuous_prod_of_discrete_left.2 fun y => continuous_edgePoint hST D j y⟩
      segBot_eq := fun _ _ => rfl
      segTop_eq := fun _ _ => rfl }

/-- The comparison map preserves height. -/
theorem height_refineMap (q : (ofFiniteData (refineData hST D)).Realization T) :
    (ofFiniteData D).height S (refineMap hST D q) =
      (ofFiniteData (refineData hST D)).height T q := by
  obtain ⟨x, rfl⟩ := (ofFiniteData (refineData hST D)).quotMk_surjective T q
  rcases x with ⟨j, v⟩ | ⟨j, y, t⟩
  · exact v.2
  · rfl

/-- The comparison map is injective. -/
theorem refineMap_injective : Function.Injective (refineMap hST D) := by
  intro p p' hpp
  have hh : (ofFiniteData (refineData hST D)).height T p =
      (ofFiniteData (refineData hST D)).height T p' := by
    rw [← height_refineMap, ← height_refineMap, hpp]
  rcases (ofFiniteData (refineData hST D)).exists_rep T p with ⟨j, v, rfl⟩ | ⟨j, a, rfl⟩ <;>
    rcases (ofFiniteData (refineData hST D)).exists_rep T p' with ⟨j', v', rfl⟩ | ⟨j', a', rfl⟩
  · have hj : T.value j = T.value j' := hh
    obtain rfl : j = j' := T.strictMono.injective hj
    obtain rfl : v = v' := Subtype.ext hpp
    rfl
  · have hj : T.value j = a'.2 := hh
    exact absurd (hj ▸ a'.2.2) (T.value_notMem_K j' j)
  · have hj : (a.2 : ℝ) = T.value j' := hh
    exact absurd (hj ▸ a.2.2) (T.value_notMem_K j j')
  · have hh' : (a.2 : ℝ) = a'.2 := hh
    obtain rfl : j = j' := T.eq_of_mem_K_of_mem_Icc a.2.2 (hh' ▸ Ioo_subset_Icc_self a'.2.2)
    obtain ⟨y, t⟩ := a
    obtain ⟨y', t'⟩ := a'
    obtain rfl : t = t' := Subtype.ext hh'
    obtain rfl : y = y' :=
      edgePoint_inj hST D j (y := y) (y' := y') (gapIncl T j t) (value_ne hST t.2) hpp
    rfl

/-- The comparison map is surjective. -/
theorem refineMap_surjective : Function.Surjective (refineMap hST D) := by
  intro q
  by_cases hT : ∃ j, T.value j = (ofFiniteData D).height S q
  · obtain ⟨j, hj⟩ := hT
    exact ⟨(ofFiniteData (refineData hST D)).ofVertex T j ⟨q, hj.symm⟩, rfl⟩
  · push Not at hT
    have hS : ∀ i, S.value i ≠ (ofFiniteData D).height S q := fun i h => by
      obtain ⟨k, hk⟩ := hST ⟨i, rfl⟩
      exact hT k (hk.trans h)
    obtain ⟨j, hj⟩ : ∃ j, (ofFiniteData D).height S q ∈ (T.K j : Set ℝ) := by
      obtain ⟨p, hp, hpl⟩ := T.exists_piece ((ofFiniteData D).height S q)
      cases p with
      | star i => exact absurd (hpl i (T.value_mem_J i)) (hT i)
      | gap j => exact ⟨j, hp⟩
      | lowerTail =>
        exfalso
        obtain ⟨k, hk⟩ := hST ⟨0, rfl⟩
        have h1 := ((ofFiniteData D).height_mem_Icc S q).1
        have h2 : T.value 0 ≤ T.value k := T.strictMono.monotone (Fin.zero_le k)
        exact absurd (T.mem_lowerTail.1 hp) (not_lt.2 (h2.trans (hk.le.trans h1)))
      | upperTail =>
        exfalso
        obtain ⟨k, hk⟩ := hST ⟨Fin.last n, rfl⟩
        have h1 := ((ofFiniteData D).height_mem_Icc S q).2
        have h2 : T.value k ≤ T.value (Fin.last m) := T.strictMono.monotone (Fin.le_last k)
        exact absurd (T.mem_upperTail.1 hp) (not_lt.2 (h1.trans (hk.ge.trans h2)))
    obtain ⟨e, he, z, hq⟩ := exists_strip_rep (ofFiniteData D) q rfl hS
    have hsub := Icc_subset_of_mem hST (Ioo_subset_Icc_self hj) he
    have hs : (basePt T j : ℝ) ∈ (S.K e : Set ℝ) :=
      mem_K_of_ne (hsub (Ioo_subset_Icc_self (basePt T j).2)) (value_ne hST (basePt T j).2)
    let y : (ofFiniteData D).height S ⁻¹' {(basePt T j : ℝ)} :=
      ⟨(ofFiniteData D).ofStrip S e (z, ⟨_, hs⟩), rfl⟩
    refine ⟨(ofFiniteData (refineData hST D)).ofStrip T j (y, ⟨_, hj⟩), ?_⟩
    show edgePoint hST D j y (gapIncl T j ⟨_, hj⟩) = q
    rw [edgePoint_eq hST D j y z hs rfl]
    exact hq.symm

/-- **Refinement homeomorphism** over `ℝ`: the realization of the refined data over `T` is
homeomorphic to the original realization over `S`, compatibly with the heights. -/
def refineHomeomorph :
    (ofFiniteData (refineData hST D)).Realization T ≃ₜ (ofFiniteData D).Realization S :=
  (refineMap hST D).continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (refineMap hST D)
      ⟨refineMap_injective hST D, refineMap_surjective hST D⟩)

/-- The refinement homeomorphism preserves height. -/
theorem height_refineHomeomorph (q : (ofFiniteData (refineData hST D)).Realization T) :
    (ofFiniteData D).height S (refineHomeomorph hST D q) =
      (ofFiniteData (refineData hST D)).height T q :=
  height_refineMap hST D q

/-- At a new level that is not an `S`-level, the incoming endpoint map is a bijection. -/
theorem right_bijective (j : Fin m) (hj : ∀ i, S.value i ≠ T.value j.succ) :
    Function.Bijective ((refineData hST D).right j) := by
  refine ⟨fun y y' h => edgePoint_inj hST D j (segTop T j) hj (congrArg Subtype.val h), ?_⟩
  intro w
  obtain ⟨e, he, z, hw⟩ := exists_strip_rep (ofFiniteData D) w.1 w.2 hj
  have hsub := Icc_subset_of_mem hST (right_mem_Icc.2 (T.value_castSucc_lt_succ j).le) he
  have hs : (basePt T j : ℝ) ∈ (S.K e : Set ℝ) :=
    mem_K_of_ne (hsub (Ioo_subset_Icc_self (basePt T j).2)) (value_ne hST (basePt T j).2)
  let y : (ofFiniteData D).height S ⁻¹' {(basePt T j : ℝ)} :=
    ⟨(ofFiniteData D).ofStrip S e (z, ⟨_, hs⟩), rfl⟩
  refine ⟨y, Subtype.ext ?_⟩
  show edgePoint hST D j y (segTop T j) = w.1
  rw [edgePoint_eq hST D j y z hs rfl, hw]
  rfl

/-- At a new level that is not an `S`-level, the outgoing endpoint map is a bijection. -/
theorem left_bijective (j : Fin m) (hj : ∀ i, S.value i ≠ T.value j.castSucc) :
    Function.Bijective ((refineData hST D).left j) := by
  refine ⟨fun y y' h => edgePoint_inj hST D j (segBot T j) hj (congrArg Subtype.val h), ?_⟩
  intro w
  obtain ⟨e, he, z, hw⟩ := exists_strip_rep (ofFiniteData D) w.1 w.2 hj
  have hsub := Icc_subset_of_mem hST (left_mem_Icc.2 (T.value_castSucc_lt_succ j).le) he
  have hs : (basePt T j : ℝ) ∈ (S.K e : Set ℝ) :=
    mem_K_of_ne (hsub (Ioo_subset_Icc_self (basePt T j).2)) (value_ne hST (basePt T j).2)
  let y : (ofFiniteData D).height S ⁻¹' {(basePt T j : ℝ)} :=
    ⟨(ofFiniteData D).ofStrip S e (z, ⟨_, hs⟩), rfl⟩
  refine ⟨y, Subtype.ext ?_⟩
  show edgePoint hST D j y (segBot T j) = w.1
  rw [edgePoint_eq hST D j y z hs rfl, hw]
  rfl

/-- Exterior levels carry empty vertex sets. -/
theorem isEmpty_refine_V (j : Fin (m + 1))
    (hj : T.value j ∉ Icc (S.value 0) (S.value (Fin.last n))) :
    IsEmpty ((refineData hST D).V j) :=
  isEmpty_fiber S (ofFiniteData D) hj

/-- Exterior gaps carry empty edge sets. -/
theorem isEmpty_refine_E (j : Fin m)
    (hj : (basePt T j : ℝ) ∉ Icc (S.value 0) (S.value (Fin.last n))) :
    IsEmpty ((refineData hST D).E j) :=
  isEmpty_fiber S (ofFiniteData D) hj

/-! ### Inserted regular levels: a new vertex set and two copies of the edge set -/

/-- An inserted level inside the gap `K e` has vertex set `E e` (the regular fiber). -/
def refineVEquiv (j : Fin (m + 1)) (e : Fin n) (h : T.value j ∈ (S.K e : Set ℝ)) :
    (refineData hST D).V j ≃ D.E e :=
  ((ofFiniteData D).regularFiberHomeomorph S e ⟨_, h⟩).toEquiv.symm

/-- A `T`-gap inside the gap `K e` has edge set `E e`. -/
def refineEEquiv (j : Fin m) (e : Fin n) (h : (basePt T j : ℝ) ∈ (S.K e : Set ℝ)) :
    (refineData hST D).E j ≃ D.E e :=
  ((ofFiniteData D).regularFiberHomeomorph S e ⟨_, h⟩).toEquiv.symm

/-- An old level `a i` keeps its vertex set `V i`. -/
def refineVEquivOld (j : Fin (m + 1)) (i : Fin (n + 1)) (h : T.value j = S.value i) :
    (refineData hST D).V j ≃ D.V i :=
  (Equiv.setCongr (by rw [h])).trans ((ofFiniteData D).criticalFiberHomeomorph S i).toEquiv.symm

include hST in
/-- The `T`-gap below a level inside `K e` is based in `K e`. -/
theorem basePt_mem_K_of_succ (j : Fin m) (e : Fin n) (h : T.value j.succ ∈ (S.K e : Set ℝ)) :
    (basePt T j : ℝ) ∈ (S.K e : Set ℝ) :=
  mem_K_of_ne (Icc_subset_of_mem hST (right_mem_Icc.2 (T.value_castSucc_lt_succ j).le) h
    (Ioo_subset_Icc_self (basePt T j).2)) (value_ne hST (basePt T j).2)

include hST in
/-- The `T`-gap above a level inside `K e` is based in `K e`. -/
theorem basePt_mem_K_of_castSucc (j : Fin m) (e : Fin n)
    (h : T.value j.castSucc ∈ (S.K e : Set ℝ)) : (basePt T j : ℝ) ∈ (S.K e : Set ℝ) :=
  mem_K_of_ne (Icc_subset_of_mem hST (left_mem_Icc.2 (T.value_castSucc_lt_succ j).le) h
    (Ioo_subset_Icc_self (basePt T j).2)) (value_ne hST (basePt T j).2)

/-- Identity incidence below an inserted level: under the identifications with `E e`, the
incoming endpoint map is the identity. -/
theorem refine_right_eq (j : Fin m) (e : Fin n) (h : T.value j.succ ∈ (S.K e : Set ℝ))
    (y : (refineData hST D).E j) :
    refineVEquiv hST D j.succ e h ((refineData hST D).right j y) =
      refineEEquiv hST D j e (basePt_mem_K_of_succ hST j e h) y := by
  have h' := basePt_mem_K_of_succ hST j e h
  set z := refineEEquiv hST D j e h' y
  have hy : y.1 = (ofFiniteData D).ofStrip S e (z, ⟨_, h'⟩) :=
    (congrArg Subtype.val
      (((ofFiniteData D).regularFiberHomeomorph S e ⟨_, h'⟩).apply_symm_apply y)).symm
  refine (Equiv.symm_apply_eq _).2 (Subtype.ext ?_)
  show edgePoint hST D j y (segTop T j) = (ofFiniteData D).ofStrip S e (z, ⟨_, h⟩)
  rw [edgePoint_eq hST D j y z h' hy]
  rfl

/-- Identity incidence above an inserted level. -/
theorem refine_left_eq (j : Fin m) (e : Fin n) (h : T.value j.castSucc ∈ (S.K e : Set ℝ))
    (y : (refineData hST D).E j) :
    refineVEquiv hST D j.castSucc e h ((refineData hST D).left j y) =
      refineEEquiv hST D j e (basePt_mem_K_of_castSucc hST j e h) y := by
  have h' := basePt_mem_K_of_castSucc hST j e h
  set z := refineEEquiv hST D j e h' y
  have hy : y.1 = (ofFiniteData D).ofStrip S e (z, ⟨_, h'⟩) :=
    (congrArg Subtype.val
      (((ofFiniteData D).regularFiberHomeomorph S e ⟨_, h'⟩).apply_symm_apply y)).symm
  refine (Equiv.symm_apply_eq _).2 (Subtype.ext ?_)
  show edgePoint hST D j y (segBot T j) = (ofFiniteData D).ofStrip S e (z, ⟨_, h⟩)
  rw [edgePoint_eq hST D j y z h' hy]
  rfl

/-! ### Old levels: the refined incidences are `D.left` and `D.right` -/

include hST in
/-- An old level at the top of a `T`-gap based in `K e` is the level `e.succ`. -/
theorem old_level_succ (j : Fin m) (e : Fin n) (h' : (basePt T j : ℝ) ∈ (S.K e : Set ℝ))
    (i : Fin (n + 1)) (hi : T.value j.succ = S.value i) : i = e.succ := by
  have hmem := Icc_subset_of_mem hST (Ioo_subset_Icc_self (basePt T j).2) h'
    (right_mem_Icc.2 (T.value_castSucc_lt_succ j).le)
  rw [hi] at hmem
  have h1 : i ≤ e.succ := S.strictMono.le_iff_le.1 hmem.2
  have h2 : e.castSucc < i := S.strictMono.lt_iff_lt.1
    ((S.mem_K.1 h').1.trans (hi ▸ (basePt T j).2.2))
  rw [Fin.le_iff_val_le_val] at h1
  rw [Fin.lt_def] at h2
  simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
  exact Fin.ext (by simp only [Fin.val_succ]; omega)

include hST in
/-- An old level at the bottom of a `T`-gap based in `K e` is the level `e.castSucc`. -/
theorem old_level_castSucc (j : Fin m) (e : Fin n) (h' : (basePt T j : ℝ) ∈ (S.K e : Set ℝ))
    (i : Fin (n + 1)) (hi : T.value j.castSucc = S.value i) : i = e.castSucc := by
  have hmem := Icc_subset_of_mem hST (Ioo_subset_Icc_self (basePt T j).2) h'
    (left_mem_Icc.2 (T.value_castSucc_lt_succ j).le)
  rw [hi] at hmem
  have h1 : e.castSucc ≤ i := S.strictMono.le_iff_le.1 hmem.1
  have h2 : i < e.succ := S.strictMono.lt_iff_lt.1
    ((hi ▸ (basePt T j).2.1).trans (S.mem_K.1 h').2)
  rw [Fin.le_iff_val_le_val] at h1
  rw [Fin.lt_def] at h2
  simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
  exact Fin.ext (by simp only [Fin.val_castSucc]; omega)

/-- Old-level incidence from below: under `refineVEquivOld` and `refineEEquiv`, the refined
`right` is `D.right e`. -/
theorem refine_right_old (j : Fin m) (e : Fin n) (h' : (basePt T j : ℝ) ∈ (S.K e : Set ℝ))
    (hi : T.value j.succ = S.value e.succ) (y : (refineData hST D).E j) :
    refineVEquivOld hST D j.succ e.succ hi ((refineData hST D).right j y) =
      D.right e (refineEEquiv hST D j e h' y) := by
  set z := refineEEquiv hST D j e h' y
  have hy : y.1 = (ofFiniteData D).ofStrip S e (z, ⟨_, h'⟩) :=
    (congrArg Subtype.val
      (((ofFiniteData D).regularFiberHomeomorph S e ⟨_, h'⟩).apply_symm_apply y)).symm
  have hpt : ((refineData hST D).right j y).1 =
      (ofFiniteData D).ofVertex S e.succ (D.right e z) :=
    calc edgePoint hST D j y (segTop T j) = cylAt hST D j e z h' (segTop T j) :=
          edgePoint_eq hST D j y z h' hy (segTop T j)
      _ = (ofFiniteData D).ofCylinder S e (z, segTop S e) :=
          congrArg (fun p => (ofFiniteData D).ofCylinder S e (z, p)) (Subtype.ext hi)
      _ = _ := (ofFiniteData D).ofCylinder_segTop S e z
  apply (ofFiniteData D).ofVertex_injective S e.succ
  refine Eq.trans ?_ hpt
  exact congrArg Subtype.val
    (((ofFiniteData D).criticalFiberHomeomorph S e.succ).apply_symm_apply _)

/-- Old-level incidence from above: the refined `left` is `D.left e`. -/
theorem refine_left_old (j : Fin m) (e : Fin n) (h' : (basePt T j : ℝ) ∈ (S.K e : Set ℝ))
    (hi : T.value j.castSucc = S.value e.castSucc) (y : (refineData hST D).E j) :
    refineVEquivOld hST D j.castSucc e.castSucc hi ((refineData hST D).left j y) =
      D.left e (refineEEquiv hST D j e h' y) := by
  set z := refineEEquiv hST D j e h' y
  have hy : y.1 = (ofFiniteData D).ofStrip S e (z, ⟨_, h'⟩) :=
    (congrArg Subtype.val
      (((ofFiniteData D).regularFiberHomeomorph S e ⟨_, h'⟩).apply_symm_apply y)).symm
  have hpt : ((refineData hST D).left j y).1 =
      (ofFiniteData D).ofVertex S e.castSucc (D.left e z) :=
    calc edgePoint hST D j y (segBot T j) = cylAt hST D j e z h' (segBot T j) :=
          edgePoint_eq hST D j y z h' hy (segBot T j)
      _ = (ofFiniteData D).ofCylinder S e (z, segBot S e) :=
          congrArg (fun p => (ofFiniteData D).ofCylinder S e (z, p)) (Subtype.ext hi)
      _ = _ := (ofFiniteData D).ofCylinder_segBot S e z
  apply (ofFiniteData D).ofVertex_injective S e.castSucc
  refine Eq.trans ?_ hpt
  exact congrArg Subtype.val
    (((ofFiniteData D).criticalFiberHomeomorph S e.castSucc).apply_symm_apply _)

/-- The refinement isomorphism of graph objects in the real slice. -/
def refineIso (D : FiniteReebData.{0} n) : toOver T (refineData hST D) ≅ toOver S D :=
  Over.isoMk (TopCat.isoOfHomeo (refineHomeomorph hST D))
    (by ext q; exact height_refineMap hST D q)

end refinement

/-- Any two critical-value lists have a common refinement. -/
theorem exists_common_refinement {n₁ n₂ : ℕ} (S₁ : CriticalValues n₁) (S₂ : CriticalValues n₂) :
    ∃ (m : ℕ) (T : CriticalValues m),
      Set.range S₁.value ⊆ Set.range T.value ∧ Set.range S₂.value ⊆ Set.range T.value := by
  classical
  let s : Finset ℝ := Finset.univ.image S₁.value ∪ Finset.univ.image S₂.value
  have hne : s.card ≠ 0 := Finset.card_ne_zero.2
    ⟨S₁.value 0, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
  refine ⟨m, ⟨s.orderEmbOfFin hm, (s.orderEmbOfFin hm).strictMono⟩, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    show S₁.value i ∈ Set.range (s.orderEmbOfFin hm)
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_coe.2
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  · rintro _ ⟨i, rfl⟩
    show S₂.value i ∈ Set.range (s.orderEmbOfFin hm)
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_coe.2
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))

/-- **Common presentation**: any two graph objects are presented over one critical list. -/
theorem exists_common_presentation (A B : RGraphCat) :
    ∃ (m : ℕ) (T : CriticalValues m) (DA DB : FiniteReebData.{0} m),
      Nonempty (A.obj ≅ toOver T DA) ∧ Nonempty (B.obj ≅ toOver T DB) := by
  obtain ⟨n₁, S₁, D₁, ⟨i₁⟩⟩ := A.property
  obtain ⟨n₂, S₂, D₂, ⟨i₂⟩⟩ := B.property
  obtain ⟨m, T, h₁, h₂⟩ := exists_common_refinement S₁ S₂
  exact ⟨m, T, refineData h₁ D₁, refineData h₂ D₂, ⟨i₁ ≪≫ (refineIso h₁ D₁).symm⟩,
    ⟨i₂ ≪≫ (refineIso h₂ D₂).symm⟩⟩

/-- Hom classification transported along presentations. -/
def homEquivOfIso {m : ℕ} {T : CriticalValues m} {A B : Over (TopCat.of ℝ)}
    {DA DB : FiniteReebData.{0} m} (iA : A ≅ toOver T DA) (iB : B ≅ toOver T DB) :
    (A ⟶ B) ≃ (DA ⟶ DB) :=
  (Iso.homCongr iA iB).trans (realizationFullyFaithful T).homEquiv.symm

section presentations

variable {m : ℕ} {T : CriticalValues m} {A B C : Over (TopCat.of ℝ)}
  {DA DB DC DA' DB' : FiniteReebData.{0} m}

/-- The realization of the classified finite map is the conjugated slice morphism. -/
theorem homEquivOfIso_apply (iA : A ≅ toOver T DA) (iB : B ≅ toOver T DB) (f : A ⟶ B) :
    (realizationFunctor T).map (homEquivOfIso iA iB f) = iA.inv ≫ f ≫ iB.hom :=
  (realizationFullyFaithful T).map_preimage _

/-- The classification preserves identities. -/
theorem homEquivOfIso_id (iA : A ≅ toOver T DA) : homEquivOfIso iA iA (𝟙 A) = 𝟙 DA := by
  apply (realizationFullyFaithful T).map_injective
  rw [homEquivOfIso_apply, CategoryTheory.Functor.map_id]
  simp

/-- The classification preserves composition. -/
theorem homEquivOfIso_comp (iA : A ≅ toOver T DA) (iB : B ≅ toOver T DB)
    (iC : C ≅ toOver T DC) (f : A ⟶ B) (g : B ⟶ C) :
    homEquivOfIso iA iC (f ≫ g) = homEquivOfIso iA iB f ≫ homEquivOfIso iB iC g := by
  apply (realizationFullyFaithful T).map_injective
  rw [CategoryTheory.Functor.map_comp, homEquivOfIso_apply, homEquivOfIso_apply,
    homEquivOfIso_apply]
  simp

/-- The data isomorphism between two presentations of one object over the same `T`. -/
def presIso (iA : A ≅ toOver T DA) (iA' : A ≅ toOver T DA') : DA ≅ DA' :=
  (realizationFullyFaithful T).preimageIso (iA.symm ≪≫ iA')

/-- Two presentations over the same `T` give conjugate bijections. -/
theorem homEquivOfIso_conj (iA : A ≅ toOver T DA) (iA' : A ≅ toOver T DA')
    (iB : B ≅ toOver T DB) (iB' : B ≅ toOver T DB') (f : A ⟶ B) :
    homEquivOfIso iA iB f ≫ (presIso iB iB').hom =
      (presIso iA iA').hom ≫ homEquivOfIso iA' iB' f := by
  apply (realizationFullyFaithful T).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, homEquivOfIso_apply,
    homEquivOfIso_apply, presIso, presIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
    Functor.FullyFaithful.map_preimage]
  simp

end presentations

/-- Transfer of finite maps along a refinement `T → U`. -/
def refineHom {m l : ℕ} {T : CriticalValues m} {U : CriticalValues l}
    (hTU : Set.range T.value ⊆ Set.range U.value) {DA DB : FiniteReebData.{0} m}
    (φ : DA ⟶ DB) : refineData hTU DA ⟶ refineData hTU DB :=
  (realizationFullyFaithful U).preimage
    ((refineIso hTU DA).hom ≫ (realizationFunctor T).map φ ≫ (refineIso hTU DB).inv)

/-- The classification commutes with refinement of the presentations. -/
theorem homEquivOfIso_refine {m l : ℕ} {T : CriticalValues m} {U : CriticalValues l}
    (hTU : Set.range T.value ⊆ Set.range U.value) {A B : Over (TopCat.of ℝ)}
    {DA DB : FiniteReebData.{0} m} (iA : A ≅ toOver T DA) (iB : B ≅ toOver T DB) (f : A ⟶ B) :
    homEquivOfIso (iA ≪≫ (refineIso hTU DA).symm) (iB ≪≫ (refineIso hTU DB).symm) f =
      refineHom hTU (homEquivOfIso iA iB f) := by
  apply (realizationFullyFaithful U).map_injective
  rw [homEquivOfIso_apply, refineHom, Functor.FullyFaithful.map_preimage, homEquivOfIso_apply]
  simp

/-- **Independence of presentations.** Presentations of `A`, `B` over `T` and over `T'`,
transferred to any common refinement `U`, give bijections conjugate by the data isomorphisms
between the transferred presentations. -/
theorem homEquivOfIso_independent {m m' l : ℕ} {T : CriticalValues m} {T' : CriticalValues m'}
    {U : CriticalValues l} (hTU : Set.range T.value ⊆ Set.range U.value)
    (hT'U : Set.range T'.value ⊆ Set.range U.value) {A B : Over (TopCat.of ℝ)}
    {DA DB : FiniteReebData.{0} m} {DA' DB' : FiniteReebData.{0} m'}
    (iA : A ≅ toOver T DA) (iB : B ≅ toOver T DB) (iA' : A ≅ toOver T' DA')
    (iB' : B ≅ toOver T' DB') (f : A ⟶ B) :
    refineHom hTU (homEquivOfIso iA iB f) ≫
        (presIso (iB ≪≫ (refineIso hTU DB).symm) (iB' ≪≫ (refineIso hT'U DB').symm)).hom =
      (presIso (iA ≪≫ (refineIso hTU DA).symm) (iA' ≪≫ (refineIso hT'U DA').symm)).hom ≫
        refineHom hT'U (homEquivOfIso iA' iB' f) := by
  rw [← homEquivOfIso_refine, ← homEquivOfIso_refine]
  exact homEquivOfIso_conj _ _ _ _ f

/-- **Coherence**: for `S ⊆ T ⊆ U`, there is exactly one finite map between the two
refinements over `U` compatible with the refinement isomorphisms; it is an isomorphism. -/
theorem refine_coherent {n m l : ℕ} {S : CriticalValues n} {T : CriticalValues m}
    {U : CriticalValues l} (hST : Set.range S.value ⊆ Set.range T.value)
    (hTU : Set.range T.value ⊆ Set.range U.value) (hSU : Set.range S.value ⊆ Set.range U.value)
    (D : FiniteReebData.{0} n) :
    ∃! φ : refineData hTU (refineData hST D) ⟶ refineData hSU D,
      (realizationFunctor U).map φ ≫ (refineIso hSU D).hom =
        (refineIso hTU (refineData hST D)).hom ≫ (refineIso hST D).hom := by
  refine ⟨(realizationFullyFaithful U).preimage
    ((refineIso hTU _).hom ≫ (refineIso hST D).hom ≫ (refineIso hSU D).inv), ?_, ?_⟩
  · beta_reduce
    rw [Functor.FullyFaithful.map_preimage]
    simp
  · intro ψ hψ
    apply (realizationFullyFaithful U).map_injective
    apply (cancel_mono (refineIso hSU D).hom).1
    rw [hψ, Functor.FullyFaithful.map_preimage]
    simp

/-- The coherence comparison as an explicit isomorphism of finite data. -/
def refineCoherentIso {n m l : ℕ} {S : CriticalValues n} {T : CriticalValues m}
    {U : CriticalValues l} (hST : Set.range S.value ⊆ Set.range T.value)
    (hTU : Set.range T.value ⊆ Set.range U.value) (hSU : Set.range S.value ⊆ Set.range U.value)
    (D : FiniteReebData.{0} n) : refineData hTU (refineData hST D) ≅ refineData hSU D :=
  (realizationFullyFaithful U).preimageIso
    (refineIso hTU (refineData hST D) ≪≫ refineIso hST D ≪≫ (refineIso hSU D).symm)

/-- The coherence isomorphism commutes with the refinement isomorphisms. -/
theorem refineCoherentIso_comm {n m l : ℕ} {S : CriticalValues n} {T : CriticalValues m}
    {U : CriticalValues l} (hST : Set.range S.value ⊆ Set.range T.value)
    (hTU : Set.range T.value ⊆ Set.range U.value) (hSU : Set.range S.value ⊆ Set.range U.value)
    (D : FiniteReebData.{0} n) :
    (realizationFunctor U).map (refineCoherentIso hST hTU hSU D).hom ≫ (refineIso hSU D).hom =
      (refineIso hTU (refineData hST D)).hom ≫ (refineIso hST D).hom := by
  rw [refineCoherentIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  simp

end RGraph

end

end TDA.Reeb
