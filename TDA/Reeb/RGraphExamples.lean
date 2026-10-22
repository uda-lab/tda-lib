import TDA.Reeb.RGraphRefinement
import TDA.Reeb.ConstructibleSpaceExamples
import TDA.Reeb.ConstructibleCylinderExamples
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Examples: finite ℝ-graphs, their maps and refinements

All fixtures use realizations of finite data and slice morphisms. The level lists
`S01` (`0 < 1`), `S0` (the single level `0`) and `S012` (`0 < 1 < 2`) are the shared fixtures of
`ConstructibleSpaceExamples` and `ConstructibleCylinderExamples`; `Shalf` is `0 < 1/2 < 1`.

* Two parallel edges versus a single edge over `0 < 1`: no slice isomorphism exists, since its
  data isomorphism would make the edge map `Bool → Unit` injective (`parallel_not_iso_single`).
* Edge-label swap: exchanging the two parallel edges is an involutive non-identity automorphism of
  the data and of the graph object, and it moves the regular point `(true, 1/2)`.
* Isolated vertices: with two vertices per level and one edge attached to the vertices `false`,
  every height-preserving self-map fixes the attached bottom vertex, while the realized collapse
  sends the isolated vertex onto it.
* The 0–1–2 path and the 0–1–2–1 cycle are not isomorphic graph objects: their vertex sets at
  level `1` have different sizes (`cycle_not_iso_path`). By construction the cycle has a
  noninjective `left` at gap `0`, and it is its own Reeb quotient (`cycle_projHomeomorph`).
* Degree-two refinement: inserting the level `1/2` into a single edge gives a one-point vertex
  set with bijective incoming and outgoing endpoint maps, and the refined graph object is
  isomorphic to the original one (`singleEdge_refineIso`).
* Exterior refinement: refining `0 < 1` to `0 < 1 < 2` adds an empty vertex set at `2` and an
  empty edge set over `(1, 2)`.
* `n = 0`: finite maps are functions on the single vertex set (`homEquivZero`), so the slice
  endomorphisms of two points at one level are all functions `Bool → Bool`
  (`boolZero_overHomEquiv`).
* The empty graph: the realization of `emptyData n` is empty, and any graph object with an empty
  carrier, in particular `emptyRGraph n S` over any `S`, is initial in `RGraphCat`.
-/

open Set Topology CategoryTheory

universe u

namespace TDA.Reeb

noncomputable section

namespace RGraph

open CylinderPresentation

namespace Examples

open TDA.Reeb.Examples.Cylinder
open TDA.Reeb.Examples.ConstructibleCylinder (S0 S012)

/-- Levels `0 < 1/2 < 1`. -/
def Shalf : CriticalValues 2 where
  value i := ((i : ℕ) : ℝ) / 2
  strictMono _ _ h := div_lt_div_of_pos_right (Nat.cast_lt.2 h) two_pos

/-- `0 < 1/2 < 1` refines `0 < 1`. -/
theorem S01_sub_Shalf : Set.range S01.value ⊆ Set.range Shalf.value := by
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, by simp [Shalf]⟩
  · exact ⟨2, by simp [Shalf]⟩

/-- `0 < 1 < 2` refines `0 < 1`. -/
theorem S01_sub_S012 : Set.range S01.value ⊆ Set.range S012.value := by
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, by simp [S012]⟩
  · exact ⟨1, by simp [S012]⟩

/-- A single edge between single vertices. -/
def singleEdge : FiniteReebData.{0} 1 :=
  ⟨fun _ => Unit, fun _ => Unit, fun _ => inferInstance, fun _ => inferInstance,
    fun _ _ => (), fun _ _ => ()⟩

/-! ### Two parallel edges versus a single edge -/

/-- Two parallel edges and a single edge with the same endpoints are not isomorphic graph
objects. -/
theorem parallel_not_iso_single : IsEmpty (toOver S01 parallelData ≅ toOver S01 singleEdge) :=
  ⟨fun i => Bool.false_ne_true
    (e_injective_of_iso ((realizationFullyFaithful S01).preimageIso i) 0
      (a₁ := false) (a₂ := true) rfl)⟩

/-! ### The edge-label swap automorphism -/

/-- Swap the two parallel edges. -/
def swap : parallelData ⟶ parallelData :=
  (⟨fun _ => id, fun _ => Bool.not, fun _ _ => rfl, fun _ _ => rfl⟩ :
    FiniteReebData.Hom parallelData parallelData)

/-- The swap is an involution. -/
theorem swap_swap : swap ≫ swap = 𝟙 parallelData :=
  FiniteReebData.Hom.ext rfl (funext fun _ => funext fun b => Bool.not_not b)

/-- The swap is not the identity of the data. -/
theorem swap_ne_id : swap ≠ 𝟙 parallelData := fun h =>
  Bool.false_ne_true (congrArg (fun φ : parallelData ⟶ parallelData => φ.e 0 true) h)

/-- The realized swap is a nonidentity automorphism of the graph object. -/
theorem realize_swap_ne_id : (realizationFunctor S01).map swap ≠ 𝟙 _ := fun h =>
  swap_ne_id ((realizationFullyFaithful S01).map_injective
    (h.trans ((realizationFunctor S01).map_id parallelData).symm))

/-- It moves a regular point. -/
theorem realize_swap_apply :
    realizeHom S01 swap ((ofFiniteData parallelData).ofStrip S01 0 (true, half)) =
      (ofFiniteData parallelData).ofStrip S01 0 (false, half) := rfl

/-! ### Isolated vertices -/

/-- Two vertices per level, one edge attached to the vertices `false`; the vertices `true` are
isolated. -/
def isoData : FiniteReebData.{0} 1 :=
  ⟨fun _ => Bool, fun _ => Unit, fun _ => inferInstance, fun _ => inferInstance,
    fun _ _ => false, fun _ _ => false⟩

/-- Every height-preserving self-map fixes the attached bottom vertex. -/
theorem selfMap_fixes_attached
    (g : C((ofFiniteData isoData).Realization S01, (ofFiniteData isoData).Realization S01))
    (hg : ∀ q, (ofFiniteData isoData).height S01 (g q) = (ofFiniteData isoData).height S01 q) :
    g ((ofFiniteData isoData).ofVertex S01 0 false) =
      (ofFiniteData isoData).ofVertex S01 0 false := by
  refine (apply_ofVertex g hg 0 false).trans ?_
  exact congrArg ((ofFiniteData isoData).ofVertex S01 0) ((toHom g hg).left_comm 0 ()).symm

/-- Collapse the isolated vertices onto the attached ones. -/
def collapse : isoData ⟶ isoData :=
  (⟨fun _ _ => false, fun _ => id, fun _ _ => rfl, fun _ _ => rfl⟩ :
    FiniteReebData.Hom isoData isoData)

/-- The realized collapse sends the isolated bottom vertex to the attached one. -/
theorem realize_collapse_isolated :
    realizeHom S01 collapse ((ofFiniteData isoData).ofVertex S01 0 true) =
      (ofFiniteData isoData).ofVertex S01 0 false := rfl

/-- The isolated and the attached bottom vertices are different points. -/
theorem isolated_ne_attached :
    (ofFiniteData isoData).ofVertex S01 0 true ≠ (ofFiniteData isoData).ofVertex S01 0 false :=
  fun h => Bool.false_ne_true ((ofFiniteData isoData).ofVertex_injective S01 0 h).symm

/-! ### The 0–1–2 path and the 0–1–2–1 cycle -/

/-- The path with one vertex per level `0, 1, 2`. -/
def pathData : FiniteReebData.{0} 2 :=
  ⟨fun _ => Unit, fun _ => Unit, fun _ => inferInstance, fun _ => inferInstance,
    fun _ _ => (), fun _ _ => ()⟩

/-- The cycle: one vertex at `0`, two at `1`, one at `2`, and two edges per gap. -/
def cycleData : FiniteReebData.{0} 2 where
  V i := Fin (![1, 2, 1] i)
  E _ := Fin 2
  finiteV _ := inferInstance
  finiteE _ := inferInstance
  left e y := ⟨if e = 0 then 0 else y.val, by fin_cases e <;> fin_cases y <;> decide⟩
  right e y := ⟨if e = 0 then y.val else 0, by fin_cases e <;> fin_cases y <;> decide⟩

/-- The cycle and the path are not isomorphic graph objects. -/
theorem cycle_not_iso_path : IsEmpty (toOver S012 cycleData ≅ toOver S012 pathData) :=
  ⟨fun i => absurd (congrArg Fin.val (v_injective_of_iso
    ((realizationFullyFaithful S012).preimageIso i) 1
    (a₁ := (⟨0, by decide⟩ : cycleData.V 1)) (a₂ := ⟨1, by decide⟩) rfl))
    (show ¬ ((0 : ℕ) = 1) by decide)⟩

/-- The cycle's Reeb quotient is the cycle itself. -/
def cycle_projHomeomorph : (ofFiniteData cycleData).Realization S012 ≃ₜ
    ReebQuotient ((ofFiniteData cycleData).height S012) := projHomeomorph S012 cycleData

/-! ### Refinement producing degree-two vertices -/

/-- The inserted level `1/2` is not a level of `0 < 1`. -/
theorem half_notMem (i : Fin 2) : S01.value i ≠ Shalf.value (Fin.succ 0) := by
  fin_cases i <;> norm_num [Shalf]

/-- The inserted vertex at `1/2` receives exactly one edge from below... -/
theorem single_refine_right_bijective :
    Function.Bijective ((refineData S01_sub_Shalf singleEdge).right 0) :=
  right_bijective S01_sub_Shalf singleEdge 0 half_notMem

/-- ... and emits exactly one edge upwards. -/
theorem single_refine_left_bijective :
    Function.Bijective ((refineData S01_sub_Shalf singleEdge).left 1) :=
  left_bijective S01_sub_Shalf singleEdge 1 half_notMem

/-- The inserted vertex set has one element (the regular fiber of the single edge). -/
theorem single_refine_card_V1 : Nat.card ((refineData S01_sub_Shalf singleEdge).V 1) = 1 := by
  have h : Shalf.value 1 = (half : ℝ) := by norm_num [Shalf, half]
  show Nat.card ((ofFiniteData singleEdge).height S01 ⁻¹' {Shalf.value 1}) = 1
  rw [h, ← Nat.card_congr ((ofFiniteData singleEdge).regularFiberHomeomorph S01 0 half).toEquiv]
  exact Nat.card_eq_one_iff_unique.2
    ⟨inferInstanceAs (Subsingleton Unit), inferInstanceAs (Nonempty Unit)⟩

/-- The refined graph is homeomorphic to the single edge over `ℝ`. -/
def singleEdge_refineIso :
    toOver Shalf (refineData S01_sub_Shalf singleEdge) ≅ toOver S01 singleEdge :=
  refineIso S01_sub_Shalf singleEdge

/-! ### Exterior refinement adds empty pieces -/

/-- The exterior level `2` carries an empty vertex set. -/
theorem exterior_V_empty : IsEmpty ((refineData S01_sub_S012 singleEdge).V 2) :=
  isEmpty_refine_V S01_sub_S012 singleEdge 2 fun h => by
    have h2 := h.2
    have h3 : S012.value 2 = 2 := by simp [S012]
    rw [show Fin.last 1 = 1 from rfl, S01_value_one, h3] at h2
    norm_num at h2

/-- The exterior gap `(1, 2)` carries an empty edge set. -/
theorem exterior_E_empty : IsEmpty ((refineData S01_sub_S012 singleEdge).E 1) :=
  isEmpty_refine_E S01_sub_S012 singleEdge 1 fun h => by
    have h1 : S012.value (Fin.castSucc 1) < basePt S012 1 := (basePt S012 1).2.1
    have h2 := h.2
    have h3 : S012.value (Fin.castSucc 1) = 1 := by simp [S012]
    rw [h3] at h1
    rw [show Fin.last 1 = 1 from rfl, S01_value_one] at h2
    linarith

/-! ### `n = 0` -/

/-- For `n = 0` a finite map is a function on the single vertex set. -/
def homEquivZero {D D' : FiniteReebData.{u} 0} : D.Hom D' ≃ (D.V 0 → D'.V 0) where
  toFun φ := φ.v 0
  invFun f := ⟨fun i => Fin.cases (motive := fun i : Fin (0 + 1) => D.V i → D'.V i) f
      (fun j => j.elim0) i, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  left_inv φ := FiniteReebData.Hom.ext (funext fun i => by fin_cases i; rfl)
    (funext fun i => i.elim0)
  right_inv _ := rfl

/-- Two vertices at one level and no edges. -/
def boolZero : FiniteReebData.{0} 0 :=
  ⟨fun _ => Bool, fun i => i.elim0, fun _ => inferInstance, fun i => i.elim0,
    fun i => i.elim0, fun i => i.elim0⟩

/-- Height-preserving self-maps of two points at one level are all functions `Bool → Bool`. -/
def boolZero_overHomEquiv : (toOver S0 boolZero ⟶ toOver S0 boolZero) ≃ (Bool → Bool) :=
  (overHomEquiv S0 boolZero boolZero).trans ((homEquiv S0).symm.trans homEquivZero)

/-! ### The empty graph -/

/-- The empty data admit exactly one map to any finite data. -/
instance instUniqueEmptyHom (n : ℕ) (D : FiniteReebData.{0} n) : Unique (emptyData n ⟶ D) where
  default := (⟨fun _ x => x.elim, fun _ x => x.elim, fun _ x => x.elim, fun _ x => x.elim⟩ :
    FiniteReebData.Hom (emptyData n) D)
  uniq _ := FiniteReebData.Hom.ext (funext fun _ => funext fun x => x.elim)
    (funext fun _ => funext fun x => x.elim)

/-- The empty graph is initial among realizations over a common `S`. -/
instance instUniqueEmptyOverHom (n : ℕ) (S : CriticalValues n) (D : FiniteReebData.{0} n) :
    Unique (toOver S (emptyData n) ⟶ toOver S D) :=
  ((realizationFullyFaithful S).homEquiv (X := emptyData n) (Y := D)).symm.unique

/-- The realization of the empty data is empty; this restates `Examples.Cylinder.emptyData_isEmpty`
under the name used by the empty-graph fixtures. -/
theorem emptyData_realization_isEmpty (n : ℕ) (S : CriticalValues n) :
    IsEmpty ((ofFiniteData (emptyData n)).Realization S) :=
  emptyData_isEmpty n S

/-- Morphisms out of an object of the slice with empty carrier are unique. -/
@[reducible] def uniqueOverHomOfIsEmpty {A : Over (TopCat.of ℝ)} (h : IsEmpty A.left)
    (B : Over (TopCat.of ℝ)) : Unique (A ⟶ B) :=
  haveI := h
  { default := Over.homMk (TopCat.ofHom ⟨fun x => isEmptyElim x, continuous_of_discreteTopology⟩)
      (by ext x; exact isEmptyElim x)
    uniq := fun _ => by ext x; exact isEmptyElim x }

/-- **The empty graph is initial in `RGraphCat`**: any graph object with empty carrier, in
particular the realization of `emptyData n` over any `S`, is initial. -/
def isInitialOfIsEmpty (A : RGraphCat) (h : IsEmpty A.obj.left) : Limits.IsInitial A :=
  @Limits.IsInitial.ofUnique _ _ A fun B =>
    haveI : Unique (IsRGraph.ι.obj A ⟶ IsRGraph.ι.obj B) := uniqueOverHomOfIsEmpty h B.obj
    (IsRGraph.fullyFaithfulι.homEquiv (X := A) (Y := B)).unique

/-- The empty graph as a graph object, over any `S`. -/
def emptyRGraph (n : ℕ) (S : CriticalValues n) : RGraphCat :=
  ⟨toOver S (emptyData n), n, S, emptyData n, ⟨Iso.refl _⟩⟩

/-- The empty graph over any `S` is initial in `RGraphCat`. -/
def emptyRGraph_isInitial (n : ℕ) (S : CriticalValues n) : Limits.IsInitial (emptyRGraph n S) :=
  isInitialOfIsEmpty _ (emptyData_realization_isEmpty n S)

end Examples

end RGraph

end

end TDA.Reeb
