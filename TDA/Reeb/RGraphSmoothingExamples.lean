import TDA.Reeb.RGraphSmoothing
import TDA.Reeb.ConstructibleSmoothingExamples
import TDA.Reeb.RGraphThickeningExamples

/-!
# Fixtures for the geometric smoothing of finite ℝ-graphs

Acceptance fixtures for `TDA.Reeb.RGraphSmoothing`, on actual graph objects:

* **Every kind of open interval.** For an arbitrary graph object, the representative comparison
  and unit formulas hold on bounded intervals, both rays and `ℝ`; the value at `⊥` is empty.
* **`ε = 0`.** The zero isomorphism and the zero comparison on the parallel-edge loop; `U_0` keeps
  the two components of the loop over `(1/4, 3/4)`.
* **The empty graph.** Every smoothed value is empty, for every `ε`.
* **A singleton at an arbitrary height `a`.** Every smoothed value has at most one element. Values
  are empty on the rays below `a - ε` and above `a + ε`, and nonempty just inside both ends of the
  support.
* **The parallel-edge loop over `0 < 1`, height span `1 ≤ 2ε`.** For every `ε ≥ 1/2`, every
  smoothed value has at most one element; values are nonempty on every interval meeting
  `[-ε, 1 + ε]` and empty on the rays below `-ε` and above `1 + ε`. Every actual height fiber of
  `U_ε` has at most one point, and the fiber over `t` is nonempty exactly when `t ∈ [-ε, 1 + ε]`.
  So every nonempty fiber is a single point, also in the equality case `ε = 1/2` and at both ends
  of the support. At `ε = 1/4` the loop survives: the value on `(1/4, 3/4)` has two elements, and
  the fiber over `1/2` has two points.
* **The single edge over `0 < 1`, for every `ε`.** The line is stretched to `[-ε, 1 + ε]`. Every
  smoothed value has at most one element, including, for `ε < 1/2`, on intervals whose thickening
  lies in the gap. Values are nonempty on every interval meeting `[-ε, 1 + ε]`, through interior
  edge points when `ε < 1/2`, and empty on both outer rays. The actual fibers have at most one
  point and are nonempty exactly over `[-ε, 1 + ε]`.
* **Two disjoint segments.** Their classes on `ℝ` stay distinct for every `ε`.
* **Graph maps.** Naturality holds at the non-identity edge swap, whose image under `U_(1/4)` is not
  the identity, and across the critical lists `0 < 1/2 < 1` and `0 < 1`.
* **The contraction corollary** holds on two fixtures.

The fiber statements use a bridge for graph objects: if every value of the component cosheaf has
at most one element, then so does every height fiber (`fiber_subsingleton_of_cosheaf`), through the
vertex and edge labels of a finite realization.
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.RGraphSmoothing

open OpenInterval CylinderPresentation FiniteReebData RGraph
open TDA.Reeb.Examples.Cylinder (S01 S01_value_zero S01_value_one parallelData twoSegData
  twoSegLabel emptyData_isEmpty height_zero homeomorphZero)
open TDA.Reeb.Examples.ConstructibleCylinder (S0 pinch_J0_mem_iff)
open TDA.Reeb.RGraph.Examples (singleEdge)
open TDA.Reeb.Examples.ConstructibleRepresentation (pt0)
open TDA.Reeb.Examples.RGraphCosheafEquivalence (parallelGraph swapGraph singleGraph
  singleHalfGraph subdivisionIso emptyGraph)
open TDA.Reeb.Examples.ConstructibleSmoothing (quarter coe_quarter quarter_thicken
  smoothedSwap_quarter_ne_id)
open TDA.Reeb.Examples.RGraphThickening (halfNN coe_halfNN single)

/-! ### Every kind of open interval, for an arbitrary graph object -/

section Intervals

variable (ε : ℝ≥0) (A : RGraphCat)

/-- At `⊥` the smoothed value is empty. -/
theorem smoothed_bot_isEmpty :
    IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj A)).obj.obj ⊥) :=
  intervalComponents_obj_bot_isEmpty (overBaseMap ((geometricSmoothing ε).obj A).obj)

/-- A bounded interval: representative comparison and unit formulas. -/
theorem rep_unit_ioo (a b : ℝ)
    (z : {z : A.obj.left × GeometricThickening.Band ε //
      GeometricThickening.height (overBaseMap A.obj) ε z ∈ ioo a b})
    (x : {x : A.obj.left // overBaseMap A.obj x ∈ ioo a b}) :
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app (ioo a b)
        (ZerothHomotopy.mk (⟨ReebQuotient.mk _ z.1, z.2⟩ :
          {q : ReebQuotient (GeometricThickening.height (overBaseMap A.obj) ε) //
            ReebQuotient.height _ q ∈ ioo a b})) =
      ZerothHomotopy.mk (⟨z.1.1, GeometricThickening.fst_mem_thicken z.2⟩ :
        {w : A.obj.left // overBaseMap A.obj w ∈ thicken ε (ioo a b)}) ∧
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app (ioo a b)
        ((cosheafFunctor.map ((geometricSmoothingUnit ε).app A)).hom.app (ioo a b)
          (ZerothHomotopy.mk x)) =
      ZerothHomotopy.mk (⟨x.1, OpenInterval.le_iff_subset.1 (le_thicken ε _) x.2⟩ :
        {y : A.obj.left // overBaseMap A.obj y ∈ thicken ε (ioo a b)}) :=
  ⟨geometricSmoothingComparisonIso_hom_app_hom_app_mk ε A _ z,
    geometricSmoothingComparisonIso_hom_app_hom_app_unit_mk ε A _ x⟩

/-- A lower ray: representative comparison and unit formulas. -/
theorem rep_unit_iio (b : ℝ)
    (z : {z : A.obj.left × GeometricThickening.Band ε //
      GeometricThickening.height (overBaseMap A.obj) ε z ∈ iio b})
    (x : {x : A.obj.left // overBaseMap A.obj x ∈ iio b}) :
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app (iio b)
        (ZerothHomotopy.mk (⟨ReebQuotient.mk _ z.1, z.2⟩ :
          {q : ReebQuotient (GeometricThickening.height (overBaseMap A.obj) ε) //
            ReebQuotient.height _ q ∈ iio b})) =
      ZerothHomotopy.mk (⟨z.1.1, GeometricThickening.fst_mem_thicken z.2⟩ :
        {w : A.obj.left // overBaseMap A.obj w ∈ thicken ε (iio b)}) ∧
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app (iio b)
        ((cosheafFunctor.map ((geometricSmoothingUnit ε).app A)).hom.app (iio b)
          (ZerothHomotopy.mk x)) =
      ZerothHomotopy.mk (⟨x.1, OpenInterval.le_iff_subset.1 (le_thicken ε _) x.2⟩ :
        {y : A.obj.left // overBaseMap A.obj y ∈ thicken ε (iio b)}) :=
  ⟨geometricSmoothingComparisonIso_hom_app_hom_app_mk ε A _ z,
    geometricSmoothingComparisonIso_hom_app_hom_app_unit_mk ε A _ x⟩

/-- An upper ray: representative comparison and unit formulas. -/
theorem rep_unit_ioi (a : ℝ)
    (z : {z : A.obj.left × GeometricThickening.Band ε //
      GeometricThickening.height (overBaseMap A.obj) ε z ∈ ioi a})
    (x : {x : A.obj.left // overBaseMap A.obj x ∈ ioi a}) :
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app (ioi a)
        (ZerothHomotopy.mk (⟨ReebQuotient.mk _ z.1, z.2⟩ :
          {q : ReebQuotient (GeometricThickening.height (overBaseMap A.obj) ε) //
            ReebQuotient.height _ q ∈ ioi a})) =
      ZerothHomotopy.mk (⟨z.1.1, GeometricThickening.fst_mem_thicken z.2⟩ :
        {w : A.obj.left // overBaseMap A.obj w ∈ thicken ε (ioi a)}) ∧
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app (ioi a)
        ((cosheafFunctor.map ((geometricSmoothingUnit ε).app A)).hom.app (ioi a)
          (ZerothHomotopy.mk x)) =
      ZerothHomotopy.mk (⟨x.1, OpenInterval.le_iff_subset.1 (le_thicken ε _) x.2⟩ :
        {y : A.obj.left // overBaseMap A.obj y ∈ thicken ε (ioi a)}) :=
  ⟨geometricSmoothingComparisonIso_hom_app_hom_app_mk ε A _ z,
    geometricSmoothingComparisonIso_hom_app_hom_app_unit_mk ε A _ x⟩

/-- `ℝ`: representative comparison and unit formulas. -/
theorem rep_unit_top
    (z : {z : A.obj.left × GeometricThickening.Band ε //
      GeometricThickening.height (overBaseMap A.obj) ε z ∈ (⊤ : OpenInterval)})
    (x : {x : A.obj.left // overBaseMap A.obj x ∈ (⊤ : OpenInterval)}) :
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app ⊤
        (ZerothHomotopy.mk (⟨ReebQuotient.mk _ z.1, z.2⟩ :
          {q : ReebQuotient (GeometricThickening.height (overBaseMap A.obj) ε) //
            ReebQuotient.height _ q ∈ (⊤ : OpenInterval)})) =
      ZerothHomotopy.mk (⟨z.1.1, GeometricThickening.fst_mem_thicken z.2⟩ :
        {w : A.obj.left // overBaseMap A.obj w ∈ thicken ε ⊤}) ∧
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app ⊤
        ((cosheafFunctor.map ((geometricSmoothingUnit ε).app A)).hom.app ⊤
          (ZerothHomotopy.mk x)) =
      ZerothHomotopy.mk (⟨x.1, OpenInterval.le_iff_subset.1 (le_thicken ε _) x.2⟩ :
        {y : A.obj.left // overBaseMap A.obj y ∈ thicken ε ⊤}) :=
  ⟨geometricSmoothingComparisonIso_hom_app_hom_app_mk ε A _ z,
    geometricSmoothingComparisonIso_hom_app_hom_app_unit_mk ε A _ x⟩

end Intervals

/-! ### `ε = 0` -/

/-- `U_0` of the parallel-edge loop is the loop. -/
def parallelZeroIso : (geometricSmoothing 0).obj parallelGraph ≅ parallelGraph :=
  geometricSmoothingZeroIso.app parallelGraph

/-- The zero comparison on the parallel-edge loop. -/
theorem parallel_zero_comparison :
    cosheafFunctor.map (geometricSmoothingZeroIso.hom.app parallelGraph) =
      (geometricSmoothingComparisonIso 0).hom.app parallelGraph ≫
        constructibleSmoothingZeroIso.hom.app (cosheafFunctor.obj parallelGraph) :=
  cosheafFunctor_map_geometricSmoothingZeroIso_hom_app parallelGraph

/-! ### The empty graph -/

/-- **The empty graph.** Every smoothed value is empty, for every `ε`. -/
theorem smoothedEmpty_isEmpty (ε : ℝ≥0) (I : OpenInterval) :
    IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj emptyGraph)).obj.obj I) := by
  have h : IsEmpty ((intervalComponents (overBaseMap emptyGraph.obj)).obj (thicken ε I)) :=
    ⟨fun c => by
      induction c using ZerothHomotopy.rec with
      | mk x => exact (emptyData_isEmpty 0 S0).false x.1⟩
  exact (geometricSmoothingValueEquiv ε emptyGraph I).isEmpty_congr.2 h

/-! ### A singleton at an arbitrary height -/

/-- One vertex at height `a`, as a graph object. -/
abbrev singletonGraph (a : ℝ) : RGraphCat := (toRGraph (single a)).obj pt0

theorem singleton_subsingleton (a : ℝ) : Subsingleton (singletonGraph a).obj.left := by
  have : Subsingleton ((ofFiniteData pt0).V 0) := inferInstanceAs (Subsingleton Unit)
  exact (homeomorphZero (single a) (ofFiniteData pt0)).symm.injective.subsingleton

/-- **Singleton.** Every smoothed value has at most one element, for every `ε` and `I`. -/
theorem singleton_smoothed_subsingleton (a : ℝ) (ε : ℝ≥0) (I : OpenInterval) :
    Subsingleton
      ((cosheafFunctor.obj ((geometricSmoothing ε).obj (singletonGraph a))).obj.obj I) := by
  have := singleton_subsingleton a
  have h : Subsingleton
      ((intervalComponents (overBaseMap (singletonGraph a).obj)).obj (thicken ε I)) :=
    ⟨fun c d => by
      induction c using ZerothHomotopy.rec with
      | mk x =>
        induction d using ZerothHomotopy.rec with
        | mk y => exact congrArg ZerothHomotopy.mk (Subtype.ext (Subsingleton.elim _ _))⟩
  exact (geometricSmoothingValueEquiv ε (singletonGraph a) I).subsingleton_congr.2 h

/-- **Singleton.** The smoothed value is empty on the ray below the support `[a - ε, a + ε]`. -/
theorem singleton_smoothed_isEmpty_iio (a : ℝ) (ε : ℝ≥0) :
    IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj (singletonGraph a))).obj.obj
      (iio (a - ε))) := by
  have h : IsEmpty ((intervalComponents (overBaseMap (singletonGraph a).obj)).obj
      (thicken ε (iio (a - ε)))) :=
    ⟨fun c => by
      induction c using ZerothHomotopy.rec with
      | mk x =>
        have hx : overBaseMap (singletonGraph a).obj x.1 ∈ thicken ε (iio (a - ε)) := x.2
        obtain ⟨y, hy, hxy⟩ := mem_thicken.1 hx
        have ha : overBaseMap (singletonGraph a).obj x.1 = a :=
          height_zero (single a) (ofFiniteData pt0) x.1
        have hy' : y < a - ε := hy
        rw [ha, abs_le] at hxy
        linarith [hxy.2]⟩
  exact (geometricSmoothingValueEquiv ε (singletonGraph a) _).isEmpty_congr.2 h

/-- **Singleton.** The smoothed value is empty on the ray above the support `[a - ε, a + ε]`. -/
theorem singleton_smoothed_isEmpty_ioi (a : ℝ) (ε : ℝ≥0) :
    IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj (singletonGraph a))).obj.obj
      (ioi (a + ε))) := by
  have h : IsEmpty ((intervalComponents (overBaseMap (singletonGraph a).obj)).obj
      (thicken ε (ioi (a + ε)))) :=
    ⟨fun c => by
      induction c using ZerothHomotopy.rec with
      | mk x =>
        have hx : overBaseMap (singletonGraph a).obj x.1 ∈ thicken ε (ioi (a + ε)) := x.2
        obtain ⟨y, hy, hxy⟩ := mem_thicken.1 hx
        have ha : overBaseMap (singletonGraph a).obj x.1 = a :=
          height_zero (single a) (ofFiniteData pt0) x.1
        have hy' : a + ε < y := hy
        rw [ha, abs_le] at hxy
        linarith [hxy.1]⟩
  exact (geometricSmoothingValueEquiv ε (singletonGraph a) _).isEmpty_congr.2 h

/-- **Singleton.** The support is sharp: just above its lower end the smoothed value contains
the class of `q (*, -ε)`. -/
theorem singleton_smoothed_nonempty_iio (a : ℝ) (ε : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty ((cosheafFunctor.obj ((geometricSmoothing ε).obj (singletonGraph a))).obj.obj
      (iio (a - ε + δ))) :=
  ⟨ZerothHomotopy.mk (⟨ReebQuotient.mk _ ((ofFiniteData pt0).ofVertex (single a) 0 (),
      ⟨-(ε : ℝ), le_refl _, GeometricThickening.neg_le_band ε⟩), by
        show a + -(ε : ℝ) < a - ε + δ
        linarith⟩ :
    {q : ReebQuotient (GeometricThickening.height (overBaseMap (singletonGraph a).obj) ε) //
      ReebQuotient.height _ q ∈ iio (a - ε + δ)})⟩
/-- **Singleton.** The support is sharp at its upper end too: just below it the smoothed value
contains the class of `q (*, ε)`. -/
theorem singleton_smoothed_nonempty_ioi (a : ℝ) (ε : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty ((cosheafFunctor.obj ((geometricSmoothing ε).obj (singletonGraph a))).obj.obj
      (ioi (a + ε - δ))) :=
  ⟨ZerothHomotopy.mk (⟨ReebQuotient.mk _ ((ofFiniteData pt0).ofVertex (single a) 0 (),
      ⟨ε, GeometricThickening.neg_le_band ε, le_refl _⟩), by
        show a + ε - δ < a + (ε : ℝ)
        linarith⟩ :
    {q : ReebQuotient (GeometricThickening.height (overBaseMap (singletonGraph a).obj) ε) //
      ReebQuotient.height _ q ∈ ioi (a + ε - δ)})⟩

/-! ### Two levels: stars, gluing on `ℝ` and long intervals -/

section TwoLevels

/-- The star `J 1 = (0, ∞)` of `0 < 1`. -/
theorem S01_J1_mem_iff (x : ℝ) : x ∈ S01.J 1 ↔ 0 < x := by
  rw [S01.mem_J_iff]
  constructor
  · intro h
    simpa using h.1 0 rfl
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · obtain rfl : k = 0 := Fin.ext (by simpa using hk)
      simpa using h
    · have := k.isLt
      simp at hk
      omega

variable (D : FiniteReebData.{0} 1)

/-- The two stars glue on `ℝ` along an edge `y`: the class of its lower vertex equals the class
of its upper vertex. -/
theorem top_glue (y : D.E 0) :
    (D.toCosheaf S01).map (homOfLE (le_top : S01.J (Fin.castSucc 0) ≤ ⊤))
        (D.vertexLabel S01 (Fin.castSucc 0) (D.left 0 y)) =
      (D.toCosheaf S01).map (homOfLE (le_top : S01.J (Fin.succ 0) ≤ ⊤))
        (D.vertexLabel S01 (Fin.succ 0) (D.right 0 y)) := by
  rw [← D.map_K_le_J_castSucc_edgeLabel S01 0 y, ← D.map_K_le_J_succ_edgeLabel S01 0 y,
    ← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact congrArg (fun f => (D.toCosheaf S01).map f (D.edgeLabel S01 0 y)) (Subsingleton.elim _ _)

/-- With one vertex per level and an edge, the value on `ℝ` has at most one element. -/
theorem subsingleton_top (h0 : Subsingleton (D.V 0)) (h1 : Subsingleton (D.V 1)) (y : D.E 0) :
    Subsingleton ((D.toCosheaf S01).obj ⊤) := by
  have := h0
  have := h1
  have hJ0 : Subsingleton ((D.toCosheaf S01).obj (S01.J 0)) :=
    (D.vertexLabel S01 0).symm.subsingleton
  have hJ1 : Subsingleton ((D.toCosheaf S01).obj (S01.J 1)) :=
    (D.vertexLabel S01 1).symm.subsingleton
  have key : ∀ c : (D.toCosheaf S01).obj ⊤, c =
      (D.toCosheaf S01).map (homOfLE (le_top : S01.J (Fin.castSucc 0) ≤ ⊤))
        (D.vertexLabel S01 (Fin.castSucc 0) (D.left 0 y)) := by
    intro c
    induction c using ZerothHomotopy.rec with
    | mk x =>
      rcases lt_or_ge ((ofFiniteData D).height S01 x.1) 1 with hx | hx
      · have hm : (ofFiniteData D).height S01 x.1 ∈ S01.J 0 := (pinch_J0_mem_iff _).2 hx
        exact congrArg ((D.toCosheaf S01).map (homOfLE (le_top : S01.J (Fin.castSucc 0) ≤ ⊤)))
          (hJ0.elim (ZerothHomotopy.mk (⟨x.1, hm⟩ :
            {z : (ofFiniteData D).Realization S01 // (ofFiniteData D).height S01 z ∈ S01.J 0}) :
              (D.toCosheaf S01).obj (S01.J 0))
            (D.vertexLabel S01 (Fin.castSucc 0) (D.left 0 y)))
      · have hm : (ofFiniteData D).height S01 x.1 ∈ S01.J 1 :=
          (S01_J1_mem_iff _).2 (by linarith)
        exact (congrArg ((D.toCosheaf S01).map (homOfLE (le_top : S01.J (Fin.succ 0) ≤ ⊤)))
          (hJ1.elim (ZerothHomotopy.mk (⟨x.1, hm⟩ :
            {z : (ofFiniteData D).Realization S01 // (ofFiniteData D).height S01 z ∈ S01.J 1}) :
              (D.toCosheaf S01).obj (S01.J 1))
            (D.vertexLabel S01 (Fin.succ 0) (D.right 0 y)))).trans (top_glue D y).symm
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- An interval meeting a level has at most one component, for one vertex per level and an
edge. -/
theorem subsingleton_of_mem (h0 : Subsingleton (D.V 0)) (h1 : Subsingleton (D.V 1)) (y : D.E 0)
    {L : OpenInterval} (hL : (0 : ℝ) ∈ L ∨ (1 : ℝ) ∈ L) :
    Subsingleton ((D.toCosheaf S01).obj L) := by
  have := h0
  have := h1
  have hF := D.toCosheaf_isConstructibleAt S01
  by_cases hz : (0 : ℝ) ∈ L <;> by_cases ho : (1 : ℝ) ∈ L
  · have := subsingleton_top D h0 h1 y
    exact (hF.bijective (le_top : L ≤ ⊤) ⟨0, hz⟩
      (fun i => ⟨fun _ => trivial, fun _ => by fin_cases i <;> simp [hz, ho]⟩)).injective
        |>.subsingleton
  · have hle : L ≤ S01.J 0 := OpenInterval.le_iff_subset.2 fun x hx => (pinch_J0_mem_iff x).2
      (not_le.1 fun hx1 => ho (L.ordConnected.out hz hx ⟨zero_le_one, hx1⟩))
    have : Subsingleton ((D.toCosheaf S01).obj (S01.J 0)) :=
      (D.vertexLabel S01 0).symm.subsingleton
    exact (hF.bijective hle ⟨0, hz⟩ (fun i => by
      rw [S01.value_mem_J_iff]
      fin_cases i <;> simp [hz, ho])).injective.subsingleton
  · have hle : L ≤ S01.J 1 := OpenInterval.le_iff_subset.2 fun x hx => (S01_J1_mem_iff x).2
      (not_le.1 fun hx0 => hz (L.ordConnected.out hx ho ⟨hx0, zero_le_one⟩))
    have : Subsingleton ((D.toCosheaf S01).obj (S01.J 1)) :=
      (D.vertexLabel S01 1).symm.subsingleton
    exact (hF.bijective hle ⟨1, ho⟩ (fun i => by
      rw [S01.value_mem_J_iff]
      fin_cases i <;> simp [hz, ho])).injective.subsingleton
  · exact absurd hL (by tauto)

/-- An interval below the level `0` has an empty value. -/
theorem isEmpty_of_lt {L : OpenInterval} (h : ∀ x ∈ L, x < 0) :
    IsEmpty ((D.toCosheaf S01).obj L) :=
  (D.toCosheaf_isConstructibleAt S01).isEmpty_of_le_lowerTail
    (OpenInterval.le_iff_subset.2 fun x hx => S01.mem_lowerTail.2 (by
      rw [S01_value_zero]
      exact h x hx))

/-- An interval above the level `1` has an empty value. -/
theorem isEmpty_of_gt {L : OpenInterval} (h : ∀ x ∈ L, 1 < x) :
    IsEmpty ((D.toCosheaf S01).obj L) :=
  (D.toCosheaf_isConstructibleAt S01).isEmpty_of_le_upperTail
    (OpenInterval.le_iff_subset.2 fun x hx => S01.mem_upperTail.2 (by
      rw [show Fin.last 1 = 1 from rfl, S01_value_one]
      exact h x hx))

/-- **Long intervals.** An interval containing `[c - 1/2, c + 1/2]` meets a level of `0 < 1` or
lies in a tail, so its value has at most one element (one vertex per level and an edge). -/
theorem subsingleton_of_long (h0 : Subsingleton (D.V 0)) (h1 : Subsingleton (D.V 1))
    (y : D.E 0) {L : OpenInterval} {c : ℝ} (ha : c - 1 / 2 ∈ L) (hb : c + 1 / 2 ∈ L) :
    Subsingleton ((D.toCosheaf S01).obj L) := by
  by_cases hz : (0 : ℝ) ∈ L
  · exact subsingleton_of_mem D h0 h1 y (.inl hz)
  by_cases ho : (1 : ℝ) ∈ L
  · exact subsingleton_of_mem D h0 h1 y (.inr ho)
  have hIcc := L.ordConnected.out ha hb
  rcases lt_or_ge c (1 / 2) with hc | hc
  · have hb0 : c + 1 / 2 < 0 := not_le.1 fun hn => hz (hIcc ⟨by linarith, hn⟩)
    have := isEmpty_of_lt D (L := L) fun x hx =>
      not_le.1 fun hn => hz (L.ordConnected.out hb hx ⟨hb0.le, hn⟩)
    infer_instance
  · have ha1 : 1 < c - 1 / 2 := not_le.1 fun hn => ho (hIcc ⟨hn, by linarith⟩)
    have := isEmpty_of_gt D (L := L) fun x hx =>
      not_le.1 fun hn => ho (L.ordConnected.out hx ha ⟨hn, ha1.le⟩)
    infer_instance

/-- For `1/2 ≤ ε`, every thickened interval is long or empty. -/
theorem thicken_subsingleton_of_half_le (h0 : Subsingleton (D.V 0)) (h1 : Subsingleton (D.V 1))
    (y : D.E 0) {ε : ℝ≥0} (hε : 1 / 2 ≤ (ε : ℝ)) (I : OpenInterval) :
    Subsingleton ((D.toCosheaf S01).obj (thicken ε I)) := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI | ⟨c, hc⟩
  · refine ⟨fun a _ => ?_⟩
    induction a using ZerothHomotopy.rec with
    | mk x =>
      exfalso
      have hx : (ofFiniteData D).height S01 x.1 ∈ thicken ε I := x.2
      obtain ⟨t, ht, -⟩ := mem_thicken.1 hx
      have ht' : t ∈ (I : Set ℝ) := ht
      rw [hI] at ht'
      exact ht'
  · refine subsingleton_of_long D h0 h1 y (c := c) ?_ ?_
    · exact mem_thicken.2 ⟨c, hc, by rw [abs_le]; constructor <;> linarith⟩
    · exact mem_thicken.2 ⟨c, hc, by rw [abs_le]; constructor <;> linarith⟩

/-- **Support, every `ε`.** For a graph object over `0 < 1`, the smoothed values on the rays below
`-ε` and above `1 + ε` are empty. -/
theorem smoothed_isEmpty_rays (ε : ℝ≥0) :
    IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj ((toRGraph S01).obj D))).obj.obj
        (iio (-(ε : ℝ)))) ∧
      IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj ((toRGraph S01).obj D))).obj.obj
        (ioi (1 + ε))) := by
  constructor
  · refine (geometricSmoothingValueEquiv ε ((toRGraph S01).obj D) _).isEmpty_congr.2
      (isEmpty_of_lt D fun x hx => ?_)
    obtain ⟨t, ht, hxt⟩ := mem_thicken.1 hx
    have ht' : t < -(ε : ℝ) := ht
    rw [abs_le] at hxt
    linarith [hxt.2]
  · refine (geometricSmoothingValueEquiv ε ((toRGraph S01).obj D) _).isEmpty_congr.2
      (isEmpty_of_gt D fun x hx => ?_)
    obtain ⟨t, ht, hxt⟩ := mem_thicken.1 hx
    have ht' : 1 + (ε : ℝ) < t := ht
    rw [abs_le] at hxt
    linarith [hxt.1]

/-- **Support, `ε ≥ 1/2`.** For a graph object over `0 < 1` with vertices `v₀`, `v₁` at both levels,
the smoothed value is nonempty on every interval meeting `[-ε, 1 + ε]`: a height `t` of that
interval is the height of `q (v₀, t)` or of `q (v₁, t - 1)`. -/
theorem smoothed_nonempty (v₀ : D.V 0) (v₁ : D.V 1) {ε : ℝ≥0} (hε : 1 / 2 ≤ (ε : ℝ))
    {I : OpenInterval} {t : ℝ} (ht : t ∈ I) (ht₁ : -(ε : ℝ) ≤ t) (ht₂ : t ≤ 1 + ε) :
    Nonempty ((cosheafFunctor.obj ((geometricSmoothing ε).obj ((toRGraph S01).obj D))).obj.obj
      I) := by
  rcases le_or_gt t ε with h | h
  · refine ⟨ZerothHomotopy.mk (⟨ReebQuotient.mk _ ((ofFiniteData D).ofVertex S01 0 v₀,
      ⟨t, ht₁, h⟩), ?_⟩ :
        {q : ReebQuotient
            (GeometricThickening.height (overBaseMap ((toRGraph S01).obj D).obj) ε) //
          ReebQuotient.height _ q ∈ I})⟩
    change S01.value 0 + t ∈ I
    rw [S01_value_zero, zero_add]
    exact ht
  · refine ⟨ZerothHomotopy.mk (⟨ReebQuotient.mk _ ((ofFiniteData D).ofVertex S01 1 v₁,
      ⟨t - 1, by linarith, by linarith⟩), ?_⟩ :
        {q : ReebQuotient
            (GeometricThickening.height (overBaseMap ((toRGraph S01).obj D).obj) ε) //
          ReebQuotient.height _ q ∈ I})⟩
    change S01.value 1 + (t - 1) ∈ I
    rw [S01_value_one, add_sub_cancel]
    exact ht
/-- **Every interval, one edge.** With one vertex per level and one edge, every value has at most
one element: an interval meeting a level is handled by `subsingleton_of_mem`; a nonempty interval
inside the gap `(0, 1)` maps bijectively to the gap value, which is labelled by the edge set; any
other interval has an empty value. -/
theorem subsingleton_of_unique (h0 : Subsingleton (D.V 0)) (h1 : Subsingleton (D.V 1))
    (hE : Subsingleton (D.E 0)) (y : D.E 0) (L : OpenInterval) :
    Subsingleton ((D.toCosheaf S01).obj L) := by
  by_cases hz : (0 : ℝ) ∈ L
  · exact subsingleton_of_mem D h0 h1 y (.inl hz)
  by_cases ho : (1 : ℝ) ∈ L
  · exact subsingleton_of_mem D h0 h1 y (.inr ho)
  rcases (L : Set ℝ).eq_empty_or_nonempty with hL | ⟨c, hc⟩
  · refine ⟨fun a _ => ?_⟩
    induction a using ZerothHomotopy.rec with
    | mk x =>
      exfalso
      have hx : (ofFiniteData D).height S01 x.1 ∈ (L : Set ℝ) := x.2
      rw [hL] at hx
      exact hx
  rcases lt_or_gt_of_ne (show c ≠ 0 from fun h => hz (h ▸ hc)) with hc0 | hc0
  · have := isEmpty_of_lt D (L := L) fun x hx =>
      not_le.1 fun hn => hz (L.ordConnected.out hc hx ⟨hc0.le, hn⟩)
    infer_instance
  rcases lt_or_gt_of_ne (show c ≠ 1 from fun h => ho (h ▸ hc)) with hc1 | hc1
  · have hle : L ≤ S01.K 0 := OpenInterval.le_iff_subset.2 fun x hx => by
      refine S01.mem_K.2 ?_
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
      exact ⟨not_le.1 fun hn => hz (L.ordConnected.out hx hc ⟨hn, hc0.le⟩),
        not_le.1 fun hn => ho (L.ordConnected.out hc hx ⟨hc1.le, hn⟩)⟩
    have : Subsingleton ((D.toCosheaf S01).obj (S01.K 0)) :=
      (D.edgeLabel S01 0).symm.subsingleton
    refine ((D.toCosheaf_isConstructibleAt S01).bijective hle ⟨c, hc⟩ fun i =>
      iff_of_false ?_ (S01.value_notMem_K 0 i)).injective.subsingleton
    fin_cases i
    · simpa using hz
    · simpa using ho
  · have := isEmpty_of_gt D (L := L) fun x hx =>
      not_le.1 fun hn => ho (L.ordConnected.out hx hc ⟨hn, hc1.le⟩)
    infer_instance

/-- **Support of the fibers, every `ε`.** For a graph object over `0 < 1` with an edge `y`, the
height fiber of `U_ε` over `t` is nonempty exactly when `t ∈ [-ε, 1 + ε]`. A point `q (x, s)` has
height `f x + s` with `f x ∈ [0, 1]` and `|s| ≤ ε`; conversely `q (v₀, t)`, `q (v₁, t - 1)` or, for
`ε < t < 1 - ε`, the class `q ((y, t), 0)` of an edge point has height `t`. -/
theorem smoothed_fiber_nonempty_iff (y : D.E 0) (ε : ℝ≥0) (t : ℝ) :
    (overBaseMap ((geometricSmoothing ε).obj ((toRGraph S01).obj D)).obj ⁻¹' {t}).Nonempty ↔
      t ∈ Icc (-(ε : ℝ)) (1 + ε) := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨z, rfl⟩ := ReebQuotient.mk_surjective _ q
    have hz : (ofFiniteData D).height S01 z.1 + (z.2 : ℝ) = t := hq
    have hx := (ofFiniteData D).height_mem_Icc S01 z.1
    rw [S01_value_zero, show Fin.last 1 = 1 from rfl, S01_value_one] at hx
    exact ⟨by linarith [hx.1, z.2.2.1], by linarith [hx.2, z.2.2.2]⟩
  · rintro ⟨ht₁, ht₂⟩
    rcases le_or_gt t ε with h | h
    · refine ⟨ReebQuotient.mk _ ((ofFiniteData D).ofVertex S01 0 (D.left 0 y), ⟨t, ht₁, h⟩), ?_⟩
      show S01.value 0 + t = t
      rw [S01_value_zero, zero_add]
    rcases le_or_gt (1 - (ε : ℝ)) t with h' | h'
    · refine ⟨ReebQuotient.mk _ ((ofFiniteData D).ofVertex S01 1 (D.right 0 y),
        ⟨t - 1, by linarith, by linarith⟩), ?_⟩
      show S01.value 1 + (t - 1) = t
      rw [S01_value_one, add_sub_cancel]
    · have hK : t ∈ S01.K 0 := by
        rw [S01.mem_K]
        simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
        exact ⟨by linarith [ε.coe_nonneg], by linarith [ε.coe_nonneg]⟩
      refine ⟨ReebQuotient.mk _ ((ofFiniteData D).ofStrip S01 0 (y, ⟨t, hK⟩),
        ⟨0, GeometricThickening.zero_mem_band ε⟩), ?_⟩
      show t + 0 = t
      rw [add_zero]

/-- **Support of the values, every `ε`.** For a graph object over `0 < 1` with an edge, the
smoothed value is nonempty on every interval meeting `[-ε, 1 + ε]`: it contains the class of a
point of the fiber. -/
theorem smoothed_nonempty_of_edge (y : D.E 0) (ε : ℝ≥0) {I : OpenInterval} {t : ℝ} (ht : t ∈ I)
    (ht₁ : -(ε : ℝ) ≤ t) (ht₂ : t ≤ 1 + ε) :
    Nonempty ((cosheafFunctor.obj ((geometricSmoothing ε).obj ((toRGraph S01).obj D))).obj.obj
      I) := by
  obtain ⟨q, hq⟩ := (smoothed_fiber_nonempty_iff D y ε t).2 ⟨ht₁, ht₂⟩
  have hq' : overBaseMap ((geometricSmoothing ε).obj ((toRGraph S01).obj D)).obj q = t := hq
  exact ⟨ZerothHomotopy.mk (⟨q, by rw [hq']; exact ht⟩ :
    {q : ((geometricSmoothing ε).obj ((toRGraph S01).obj D)).obj.left //
      overBaseMap ((geometricSmoothing ε).obj ((toRGraph S01).obj D)).obj q ∈ I})⟩

/-- On `(1/4, 3/4)`, inside the gap `(0, 1)`, the parallel-edge loop has two components: the value
maps bijectively to the gap value, labelled by the two edges. -/
theorem parallel_mid_not_subsingleton :
    ¬ Subsingleton ((parallelData.toCosheaf S01).obj (ioo (1 / 4) (3 / 4))) := by
  intro h
  have hle : ioo (1 / 4) (3 / 4) ≤ S01.K 0 := OpenInterval.le_iff_subset.2 fun x hx => by
    refine S01.mem_K.2 ?_
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
    obtain ⟨hx₁, hx₂⟩ := mem_ioo.1 hx
    exact ⟨by linarith, by linarith⟩
  have hbij := (parallelData.toCosheaf_isConstructibleAt S01).bijective hle
    ⟨1 / 2, mem_ioo.2 ⟨by norm_num, by norm_num⟩⟩ fun i =>
      iff_of_false (by fin_cases i <;> norm_num [mem_ioo]) (S01.value_notMem_K 0 i)
  have : Subsingleton ((parallelData.toCosheaf S01).obj (S01.K 0)) := hbij.surjective.subsingleton
  exact Bool.false_ne_true ((parallelData.edgeLabel S01 0).injective (Subsingleton.elim _ _))

end TwoLevels

/-! ### Height fibers of graph objects -/

section Fibers

/-- **Fibers of a finite realization.** The fiber over a level `a i` consists of vertex points of
level `i`, and the fiber over any other height consists of strip points of one gap. So if every
value of the component cosheaf has at most one element, then, through the vertex and edge labels,
every height fiber has at most one point. -/
theorem realization_fiber_subsingleton {m : ℕ} (T : CriticalValues m)
    (D : FiniteReebData.{0} m) (h : ∀ L, Subsingleton ((D.toCosheaf T).obj L)) (t : ℝ) :
    Subsingleton ((ofFiniteData D).height T ⁻¹' {t}) := by
  by_cases hlev : ∃ i, T.value i = t
  · obtain ⟨i, rfl⟩ := hlev
    have := h (T.J i)
    have hV : Subsingleton (D.V i) := (D.vertexLabel T i).subsingleton
    have key : ∀ q : (ofFiniteData D).height T ⁻¹' {T.value i},
        ∃ v : D.V i, q.1 = (ofFiniteData D).ofVertex T i v := by
      rintro ⟨q, hq⟩
      rcases (ofFiniteData D).exists_rep T q with ⟨j, v, rfl⟩ | ⟨e, p, rfl⟩
      · have hj : T.value j = T.value i := hq
        obtain rfl := T.strictMono.injective hj
        exact ⟨v, rfl⟩
      · have hp : (p.2 : ℝ) = T.value i := hq
        have hK := p.2.2
        rw [hp] at hK
        exact absurd hK (T.value_notMem_K e i)
    refine ⟨fun q q' => Subtype.ext ?_⟩
    obtain ⟨v, hv⟩ := key q
    obtain ⟨v', hv'⟩ := key q'
    rw [hv, hv', Subsingleton.elim v v']
  · simp only [not_exists] at hlev
    refine ⟨fun q q' => Subtype.ext ?_⟩
    obtain ⟨e, he, z, hz⟩ := exists_strip_rep (ofFiniteData D) q.1 q.2 hlev
    obtain ⟨e', he', z', hz'⟩ := exists_strip_rep (ofFiniteData D) q'.1 q'.2 hlev
    obtain rfl : e = e' := T.eq_of_K_inf_K_nonempty ⟨t, he, he'⟩
    have := h (T.K e)
    have hE : Subsingleton ((ofFiniteData D).E e) := (D.edgeLabel T e).subsingleton
    rw [hz, hz', Subsingleton.elim z z']

/-- **Fibers from cosheaf values.** For a graph object, if every value of its component cosheaf
has at most one element, then every height fiber has at most one point: an isomorphism with a
finite realization maps fibers injectively and values bijectively. -/
theorem fiber_subsingleton_of_cosheaf (B : RGraphCat)
    (h : ∀ L, Subsingleton ((cosheafFunctor.obj B).obj.obj L)) (t : ℝ) :
    Subsingleton (overBaseMap B.obj ⁻¹' {t}) := by
  obtain ⟨m, T, D, ⟨i⟩⟩ := B.property
  have hD : ∀ L, Subsingleton ((D.toCosheaf T).obj L) := fun L =>
    @Equiv.subsingleton _ _ ((intervalComponentsOver.mapIso i).app L).toEquiv.symm (h L)
  have hF := realization_fiber_subsingleton T D hD t
  have hinj : Function.Injective i.hom.left.hom := fun x y hxy => by
    have hx : i.inv.left.hom (i.hom.left.hom x) = x :=
      congrArg (fun φ : B.obj ⟶ B.obj => φ.left.hom x) i.hom_inv_id
    have hy : i.inv.left.hom (i.hom.left.hom y) = y :=
      congrArg (fun φ : B.obj ⟶ B.obj => φ.left.hom y) i.hom_inv_id
    rw [← hx, ← hy, hxy]
  refine ⟨fun x y => Subtype.ext (hinj ?_)⟩
  have hx : (ofFiniteData D).height T (i.hom.left.hom x.1) = t :=
    (overBaseMap_comm i.hom x.1).trans x.2
  have hy : (ofFiniteData D).height T (i.hom.left.hom y.1) = t :=
    (overBaseMap_comm i.hom y.1).trans y.2
  exact congrArg Subtype.val (hF.elim ⟨_, hx⟩ ⟨_, hy⟩)

end Fibers

/-! ### The parallel-edge loop: height span `1 ≤ 2ε` -/

/-- **Loop, span `1 ≤ 2ε`.** For the parallel-edge loop over `0 < 1` and every `ε ≥ 1/2`, every
smoothed value has at most one element: the loop is gone. -/
theorem parallel_smoothed_subsingleton {ε : ℝ≥0} (hε : 1 / 2 ≤ (ε : ℝ)) (I : OpenInterval) :
    Subsingleton ((cosheafFunctor.obj ((geometricSmoothing ε).obj parallelGraph)).obj.obj I) :=
  (geometricSmoothingValueEquiv ε parallelGraph I).subsingleton_congr.2
    (thicken_subsingleton_of_half_le parallelData (inferInstanceAs (Subsingleton Unit))
      (inferInstanceAs (Subsingleton Unit)) false hε I)

/-- The boundary case `ε = 1/2`, where the span equals `2ε`. -/
theorem parallel_half_subsingleton (I : OpenInterval) :
    Subsingleton
      ((cosheafFunctor.obj ((geometricSmoothing halfNN).obj parallelGraph)).obj.obj I) :=
  parallel_smoothed_subsingleton (by rw [coe_halfNN]) I

/-- **Loop, span `1 ≤ 2ε`.** On every interval meeting the support `[-ε, 1 + ε]` the smoothed value
is nonempty. -/
theorem parallel_smoothed_nonempty {ε : ℝ≥0} (hε : 1 / 2 ≤ (ε : ℝ)) {I : OpenInterval} {t : ℝ}
    (ht : t ∈ I) (ht₁ : -(ε : ℝ) ≤ t) (ht₂ : t ≤ 1 + ε) :
    Nonempty ((cosheafFunctor.obj ((geometricSmoothing ε).obj parallelGraph)).obj.obj I) :=
  smoothed_nonempty parallelData () () hε ht ht₁ ht₂

/-- **Loop.** On the rays below `-ε` and above `1 + ε` the smoothed values are empty, for every
`ε`. -/
theorem parallel_smoothed_isEmpty_rays (ε : ℝ≥0) :
    IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj parallelGraph)).obj.obj
        (iio (-(ε : ℝ)))) ∧
      IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj parallelGraph)).obj.obj
        (ioi (1 + ε))) :=
  smoothed_isEmpty_rays parallelData ε

/-- **Loop at `ε = 1/4 < 1/2`.** The loop survives: on `(1/4, 3/4)` the smoothed value has two
distinct elements, the two edges, because the thickening of `(1/4, 3/4)` is the gap `(0, 1)`. -/
theorem parallel_quarter_not_subsingleton :
    ¬ Subsingleton ((cosheafFunctor.obj ((geometricSmoothing quarter).obj parallelGraph)).obj.obj
      (ioo (1 / 4) (3 / 4))) := by
  intro h
  have h1 : Subsingleton ((parallelData.toCosheaf S01).obj
      (thicken quarter (ioo (1 / 4) (3 / 4)))) :=
    (geometricSmoothingValueEquiv quarter parallelGraph _).subsingleton_congr.1 h
  rw [quarter_thicken] at h1
  exact Bool.false_ne_true ((parallelData.edgeLabel S01 0).injective (h1.elim _ _))
/-- **Loop at `ε = 0`.** `U_0` keeps the loop: on `(1/4, 3/4)` the smoothed value still has two
distinct elements, since `(1/4, 3/4)` thickens by `0` to itself. -/
theorem parallel_zero_not_subsingleton :
    ¬ Subsingleton ((cosheafFunctor.obj ((geometricSmoothing 0).obj parallelGraph)).obj.obj
      (ioo (1 / 4) (3 / 4))) := by
  intro h
  have h1 : Subsingleton ((parallelData.toCosheaf S01).obj (thicken 0 (ioo (1 / 4) (3 / 4)))) :=
    (geometricSmoothingValueEquiv 0 parallelGraph _).subsingleton_congr.1 h
  rw [thicken_zero] at h1
  exact parallel_mid_not_subsingleton h1

/-! ### The parallel-edge loop: actual height fibers -/

/-- **Loop, actual fibers, span `1 ≤ 2ε`.** For every `ε ≥ 1/2`, every height fiber of `U_ε` of the
parallel-edge loop has at most one point. -/
theorem parallel_smoothed_fiber_subsingleton {ε : ℝ≥0} (hε : 1 / 2 ≤ (ε : ℝ)) (t : ℝ) :
    Subsingleton (overBaseMap ((geometricSmoothing ε).obj parallelGraph).obj ⁻¹' {t}) :=
  fiber_subsingleton_of_cosheaf _ (parallel_smoothed_subsingleton hε) t

/-- The equality case `ε = 1/2`, where the span equals `2ε`. -/
theorem parallel_half_fiber_subsingleton (t : ℝ) :
    Subsingleton (overBaseMap ((geometricSmoothing halfNN).obj parallelGraph).obj ⁻¹' {t}) :=
  parallel_smoothed_fiber_subsingleton (by rw [coe_halfNN]) t

/-- **Loop, support of the actual fibers, every `ε`.** The fiber over `t` is nonempty exactly when
`t ∈ [-ε, 1 + ε]`, endpoints included. -/
theorem parallel_smoothed_fiber_nonempty_iff (ε : ℝ≥0) (t : ℝ) :
    (overBaseMap ((geometricSmoothing ε).obj parallelGraph).obj ⁻¹' {t}).Nonempty ↔
      t ∈ Icc (-(ε : ℝ)) (1 + ε) :=
  smoothed_fiber_nonempty_iff parallelData false ε t

/-- **Loop.** Outside `[-ε, 1 + ε]` the fibers are empty, for every `ε`. -/
theorem parallel_smoothed_fiber_isEmpty (ε : ℝ≥0) {t : ℝ} (ht : t ∉ Icc (-(ε : ℝ)) (1 + ε)) :
    IsEmpty (overBaseMap ((geometricSmoothing ε).obj parallelGraph).obj ⁻¹' {t}) :=
  ⟨fun q => ht ((parallel_smoothed_fiber_nonempty_iff ε t).1 ⟨q.1, q.2⟩)⟩

/-- **Loop, span `1 ≤ 2ε`** (DMP Example 4.31 (3)): for `ε ≥ 1/2`, every nonempty fiber is a single
point, so over each `t ∈ [-ε, 1 + ε]` there is exactly one point of `U_ε` of the loop. -/
theorem parallel_smoothed_fiber_existsUnique {ε : ℝ≥0} (hε : 1 / 2 ≤ (ε : ℝ)) {t : ℝ}
    (ht : t ∈ Icc (-(ε : ℝ)) (1 + ε)) :
    ∃! q : ((geometricSmoothing ε).obj parallelGraph).obj.left,
      overBaseMap ((geometricSmoothing ε).obj parallelGraph).obj q = t := by
  obtain ⟨q, hq⟩ := (parallel_smoothed_fiber_nonempty_iff ε t).2 ht
  have := parallel_smoothed_fiber_subsingleton hε t
  exact ⟨q, hq, fun q' hq' => congrArg Subtype.val
    (Subsingleton.elim (⟨q', hq'⟩ : overBaseMap _ ⁻¹' {t}) ⟨q, hq⟩)⟩

/-- **Loop, equality and boundary cases.** At `ε = 1/2`, where the span equals `2ε`, the fibers at
both ends `-1/2` and `3/2` of the support are single points, and the fibers just outside the
support are empty. -/
theorem parallel_half_fiber_ends {δ : ℝ} (hδ : 0 < δ) :
    (∃! q : ((geometricSmoothing halfNN).obj parallelGraph).obj.left,
        overBaseMap ((geometricSmoothing halfNN).obj parallelGraph).obj q = -(1 / 2)) ∧
      (∃! q : ((geometricSmoothing halfNN).obj parallelGraph).obj.left,
        overBaseMap ((geometricSmoothing halfNN).obj parallelGraph).obj q = 3 / 2) ∧
      IsEmpty (overBaseMap ((geometricSmoothing halfNN).obj parallelGraph).obj ⁻¹'
        {-(1 / 2) - δ}) ∧
      IsEmpty (overBaseMap ((geometricSmoothing halfNN).obj parallelGraph).obj ⁻¹'
        {3 / 2 + δ}) := by
  have hε : 1 / 2 ≤ ((halfNN : ℝ≥0) : ℝ) := by rw [coe_halfNN]
  refine ⟨parallel_smoothed_fiber_existsUnique hε ?_, parallel_smoothed_fiber_existsUnique hε ?_,
    parallel_smoothed_fiber_isEmpty halfNN ?_, parallel_smoothed_fiber_isEmpty halfNN ?_⟩
  · rw [coe_halfNN]
    constructor <;> norm_num
  · rw [coe_halfNN]
    constructor <;> norm_num
  · rw [coe_halfNN]
    exact fun h => absurd h.1 (by linarith)
  · rw [coe_halfNN]
    exact fun h => absurd h.2 (by linarith)

/-- **Loop at `ε = 1/4 < 1/2`.** The fiber over `1/2` has two distinct points, the classes of the
two edge points at height `1/2`: over `(1/4, 3/4)` the comparison sends their classes to the
classes of the two edge points, which carry the two distinct edge labels of the gap `(0, 1)`. -/
theorem parallel_quarter_fiber_not_subsingleton :
    ¬ Subsingleton
      (overBaseMap ((geometricSmoothing quarter).obj parallelGraph).obj ⁻¹' {1 / 2}) := by
  intro h
  let x : Bool → (ofFiniteData parallelData).Realization S01 := fun b =>
    (ofFiniteData parallelData).ofStrip S01 0 (b, Examples.Cylinder.half)
  let z : Bool → {z : parallelGraph.obj.left × GeometricThickening.Band quarter //
      GeometricThickening.height (overBaseMap parallelGraph.obj) quarter z ∈
        ioo (1 / 4) (3 / 4)} := fun b =>
    ⟨(x b, ⟨0, GeometricThickening.zero_mem_band quarter⟩), by
      show (1 / 2 : ℝ) + 0 ∈ ioo (1 / 4) (3 / 4)
      rw [mem_ioo]
      constructor <;> norm_num⟩
  have hq : ReebQuotient.mk _ (z false).1 = ReebQuotient.mk _ (z true).1 :=
    congrArg Subtype.val (h.elim ⟨ReebQuotient.mk _ (z false).1, by
      show (1 / 2 : ℝ) + 0 = 1 / 2
      rw [add_zero]⟩ ⟨ReebQuotient.mk _ (z true).1, by
      show (1 / 2 : ℝ) + 0 = 1 / 2
      rw [add_zero]⟩)
  have hc := congrArg (((geometricSmoothingComparisonIso quarter).hom.app parallelGraph).hom.app
    (ioo (1 / 4) (3 / 4))) (congrArg ZerothHomotopy.mk (Subtype.ext hq :
      (⟨ReebQuotient.mk _ (z false).1, (z false).2⟩ :
        {q : ReebQuotient (GeometricThickening.height (overBaseMap parallelGraph.obj) quarter) //
          ReebQuotient.height _ q ∈ ioo (1 / 4) (3 / 4)}) =
        ⟨ReebQuotient.mk _ (z true).1, (z true).2⟩))
  rw [geometricSmoothingComparisonIso_hom_app_hom_app_mk,
    geometricSmoothingComparisonIso_hom_app_hom_app_mk] at hc
  have key : ∀ (L : OpenInterval), L = S01.K 0 →
      ∀ (h0 : (ofFiniteData parallelData).height S01 (x false) ∈ L)
        (h1 : (ofFiniteData parallelData).height S01 (x true) ∈ L),
      (ZerothHomotopy.mk ⟨x false, h0⟩ : (parallelData.toCosheaf S01).obj L) ≠
        ZerothHomotopy.mk ⟨x true, h1⟩ := by
    rintro L rfl h0 h1 hne
    exact Bool.false_ne_true ((parallelData.edgeLabel S01 0).injective
      (((parallelData.edgeLabel_apply S01 0 Examples.Cylinder.half false).trans hne).trans
        (parallelData.edgeLabel_apply S01 0 Examples.Cylinder.half true).symm))
  exact key _ quarter_thicken _ _ hc

/-! ### The single edge -/

/-- **Single edge, `ε ≥ 1/2`.** Every smoothed value of the single edge over `0 < 1` has at most one
element. -/
theorem single_smoothed_subsingleton {ε : ℝ≥0} (hε : 1 / 2 ≤ (ε : ℝ)) (I : OpenInterval) :
    Subsingleton ((cosheafFunctor.obj ((geometricSmoothing ε).obj singleGraph)).obj.obj I) :=
  (geometricSmoothingValueEquiv ε singleGraph I).subsingleton_congr.2
    (thicken_subsingleton_of_half_le singleEdge (inferInstanceAs (Subsingleton Unit))
      (inferInstanceAs (Subsingleton Unit)) () hε I)

/-- **Single edge, `ε ≥ 1/2`.** The line is stretched by `ε` at both ends: nonempty on every
interval meeting `[-ε, 1 + ε]`. -/
theorem single_smoothed_nonempty {ε : ℝ≥0} (hε : 1 / 2 ≤ (ε : ℝ)) {I : OpenInterval} {t : ℝ}
    (ht : t ∈ I) (ht₁ : -(ε : ℝ) ≤ t) (ht₂ : t ≤ 1 + ε) :
    Nonempty ((cosheafFunctor.obj ((geometricSmoothing ε).obj singleGraph)).obj.obj I) :=
  smoothed_nonempty singleEdge () () hε ht ht₁ ht₂

/-- **Single edge.** Empty on the rays below `-ε` and above `1 + ε`, for every `ε`. -/
theorem single_smoothed_isEmpty_rays (ε : ℝ≥0) :
    IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj singleGraph)).obj.obj
        (iio (-(ε : ℝ)))) ∧
      IsEmpty ((cosheafFunctor.obj ((geometricSmoothing ε).obj singleGraph)).obj.obj
        (ioi (1 + ε))) :=
  smoothed_isEmpty_rays singleEdge ε
/-- **Single edge, every `ε`.** Every smoothed value of the single edge has at most one element.
For `ε < 1/2` this includes the intervals whose thickening lies in the gap `(0, 1)`, where the
value is labelled by the single edge. -/
theorem single_stretched_subsingleton (ε : ℝ≥0) (I : OpenInterval) :
    Subsingleton ((cosheafFunctor.obj ((geometricSmoothing ε).obj singleGraph)).obj.obj I) :=
  (geometricSmoothingValueEquiv ε singleGraph I).subsingleton_congr.2
    (subsingleton_of_unique singleEdge (inferInstanceAs (Subsingleton Unit))
      (inferInstanceAs (Subsingleton Unit)) (inferInstanceAs (Subsingleton Unit)) () _)

/-- **Single edge, every `ε`** (DMP Example 4.31 (1)): the line is stretched by `ε` at both ends.
The smoothed value is nonempty on every interval meeting `[-ε, 1 + ε]`; for `ε < 1/2` a height in
`(ε, 1 - ε)` is reached by an interior edge point. -/
theorem single_stretched_nonempty (ε : ℝ≥0) {I : OpenInterval} {t : ℝ} (ht : t ∈ I)
    (ht₁ : -(ε : ℝ) ≤ t) (ht₂ : t ≤ 1 + ε) :
    Nonempty ((cosheafFunctor.obj ((geometricSmoothing ε).obj singleGraph)).obj.obj I) :=
  smoothed_nonempty_of_edge singleEdge () ε ht ht₁ ht₂

/-- **Single edge, the gap at `ε = 1/4`.** On `(1/4, 3/4)`, whose thickening is the gap `(0, 1)`,
the smoothed single edge has exactly one element, where the smoothed loop has two. -/
theorem single_quarter_gap :
    Nonempty ((cosheafFunctor.obj ((geometricSmoothing quarter).obj singleGraph)).obj.obj
        (ioo (1 / 4) (3 / 4))) ∧
      Subsingleton ((cosheafFunctor.obj ((geometricSmoothing quarter).obj singleGraph)).obj.obj
        (ioo (1 / 4) (3 / 4))) :=
  ⟨single_stretched_nonempty quarter (t := 1 / 2) (mem_ioo.2 ⟨by norm_num, by norm_num⟩)
      (by rw [coe_quarter]; norm_num) (by rw [coe_quarter]; norm_num),
    single_stretched_subsingleton quarter _⟩

/-- **Single edge, actual fibers, every `ε`.** Every height fiber of `U_ε` of the single edge has
at most one point. -/
theorem single_smoothed_fiber_subsingleton (ε : ℝ≥0) (t : ℝ) :
    Subsingleton (overBaseMap ((geometricSmoothing ε).obj singleGraph).obj ⁻¹' {t}) :=
  fiber_subsingleton_of_cosheaf _ (single_stretched_subsingleton ε) t

/-- **Single edge, support of the actual fibers, every `ε`.** The fiber over `t` is nonempty exactly
when `t ∈ [-ε, 1 + ε]`. -/
theorem single_smoothed_fiber_nonempty_iff (ε : ℝ≥0) (t : ℝ) :
    (overBaseMap ((geometricSmoothing ε).obj singleGraph).obj ⁻¹' {t}).Nonempty ↔
      t ∈ Icc (-(ε : ℝ)) (1 + ε) :=
  smoothed_fiber_nonempty_iff singleEdge () ε t

/-! ### Two disjoint segments stay apart -/

/-- Two disjoint segments over `0 < 1`, as a graph object. -/
abbrev twoSegGraph : RGraphCat := (toRGraph S01).obj twoSegData

/-- The class of `q (v_b, 0)` on `ℝ`, for the lower vertex `v_b` of segment `b`. -/
def twoSegClass (ε : ℝ≥0) (b : Bool) :
    (cosheafFunctor.obj ((geometricSmoothing ε).obj twoSegGraph)).obj.obj ⊤ :=
  ZerothHomotopy.mk (⟨ReebQuotient.mk _ ((ofFiniteData twoSegData).ofVertex S01 0 b,
      ⟨0, GeometricThickening.zero_mem_band ε⟩), trivial⟩ :
    {q : ReebQuotient (GeometricThickening.height (overBaseMap twoSegGraph.obj) ε) //
      ReebQuotient.height _ q ∈ (⊤ : OpenInterval)})

/-- **Disjoint edges, for every `ε`.** The two segments give distinct classes on `ℝ`: the
comparison sends them to the classes of the two lower vertices, which the continuous segment
label separates. -/
theorem twoSeg_smoothed_distinct (ε : ℝ≥0) : twoSegClass ε false ≠ twoSegClass ε true := by
  intro h
  have e : ∀ b : Bool, ((geometricSmoothingComparisonIso ε).hom.app twoSegGraph).hom.app ⊤
      (twoSegClass ε b) =
        ZerothHomotopy.mk (⟨(ofFiniteData twoSegData).ofVertex S01 0 b,
            OpenInterval.le_iff_subset.1 (le_thicken ε ⊤) trivial⟩ :
          {x : (ofFiniteData twoSegData).Realization S01 //
            (ofFiniteData twoSegData).height S01 x ∈ thicken ε ⊤}) := fun b =>
    geometricSmoothingComparisonIso_hom_app_hom_app_mk ε twoSegGraph ⊤
      ⟨((ofFiniteData twoSegData).ofVertex S01 0 b, ⟨0, GeometricThickening.zero_mem_band ε⟩),
        trivial⟩
  have h2 := (e false).symm.trans
    ((congrArg (((geometricSmoothingComparisonIso ε).hom.app twoSegGraph).hom.app ⊤) h).trans
      (e true))
  have hc : Continuous fun x : {x : (ofFiniteData twoSegData).Realization S01 //
      (ofFiniteData twoSegData).height S01 x ∈ thicken ε ⊤} => twoSegLabel x.1 :=
    twoSegLabel.continuous.comp continuous_subtype_val
  have hj := (Quotient.exact h2).map hc
  exact Bool.false_ne_true (joined_eq_of_discrete hj)

/-! ### A non-identity graph map and naturality across critical lists -/

/-- Naturality at the edge swap of the parallel-edge loop. -/
theorem swap_naturality (ε : ℝ≥0) :
    cosheafFunctor.map ((geometricSmoothing ε).map swapGraph) ≫
        (geometricSmoothingComparisonIso ε).hom.app parallelGraph =
      (geometricSmoothingComparisonIso ε).hom.app parallelGraph ≫
        (constructibleSmoothing ε).map (cosheafFunctor.map swapGraph) :=
  (geometricSmoothingComparisonIso ε).hom.naturality swapGraph

/-- **Non-identity graph map.** At `ε = 1/4`, `U_ε` of the edge swap is still not the identity:
its cosheaf image is conjugate to the merged smoothed swap, which is not the identity. -/
theorem swap_smoothed_quarter_ne_id :
    cosheafFunctor.map ((geometricSmoothing quarter).map swapGraph) ≠ 𝟙 _ := by
  intro h
  apply smoothedSwap_quarter_ne_id
  have hn := swap_naturality quarter
  rw [h, Category.id_comp] at hn
  rw [← cancel_epi ((geometricSmoothingComparisonIso quarter).hom.app parallelGraph)]
  exact hn.symm.trans (Category.comp_id _).symm

theorem swap_geometric_quarter_ne_id : (geometricSmoothing quarter).map swapGraph ≠ 𝟙 _ :=
  fun h => swap_smoothed_quarter_ne_id (by rw [h, CategoryTheory.Functor.map_id])

/-- **Naturality across critical lists.** The subdivision isomorphism from the single edge over
`0 < 1/2 < 1` to the single edge over `0 < 1`. -/
theorem subdivision_naturality (ε : ℝ≥0) :
    cosheafFunctor.map ((geometricSmoothing ε).map subdivisionIso.hom) ≫
        (geometricSmoothingComparisonIso ε).hom.app singleGraph =
      (geometricSmoothingComparisonIso ε).hom.app singleHalfGraph ≫
        (constructibleSmoothing ε).map (cosheafFunctor.map subdivisionIso.hom) :=
  (geometricSmoothingComparisonIso ε).hom.naturality subdivisionIso.hom

/-- The smoothed subdivision isomorphism, as an isomorphism of smoothed cosheaves. -/
def subdivisionSmoothedIso (ε : ℝ≥0) :
    cosheafFunctor.obj ((geometricSmoothing ε).obj singleHalfGraph) ≅
      cosheafFunctor.obj ((geometricSmoothing ε).obj singleGraph) :=
  cosheafFunctor.mapIso ((geometricSmoothing ε).mapIso subdivisionIso)

/-! ### The contraction corollary on fixtures -/

theorem parallel_single_contraction (ε : ℝ≥0) :
    interleavingDistance (cosheafFunctor.obj ((geometricSmoothing ε).obj parallelGraph)).obj
        (cosheafFunctor.obj ((geometricSmoothing ε).obj singleGraph)).obj ≤
      interleavingDistance (cosheafFunctor.obj parallelGraph).obj
        (cosheafFunctor.obj singleGraph).obj :=
  interleavingDistance_geometricSmoothing_le ε parallelGraph singleGraph

end Examples.RGraphSmoothing

end

end TDA.Reeb
