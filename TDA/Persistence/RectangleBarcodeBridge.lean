import TDA.Persistence.RectangleMatchingDistance
import TDA.Persistence.CoordinateRealBridge
import TDA.Persistence.MatchingInterleavingDistance
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# One-dimensional half-open rectangle and barcode realizations

For finite positive half-open interval families, the actual rectangle matching
distance equals the existing endpoint diagram bottleneck and real barcode
interleaving distance. Natural isomorphisms and witness transports connect the
existing realizations while retaining occurrence labels. Short pairs may need
to be deleted when passing to numerical endpoint costs. Other decorations and
empty half-open supports have separate contracts.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RectangleBarcodeBridge

open CategoryTheory CategoryTheory.Limits
open CoordinateShift RectangleHall RectangleStabilityGeometry
open scoped TDA.Persistence NNReal ENNReal Classical ZeroObject

variable {k : Type u} [Field k]

private instance : HasFiniteBiproducts (PModule.{u,0,u} k (Fin 1 → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable def fromRealZeroIso :
    CoordinateRealBridge.fromReal (0 : PModule.{u,0,u} k ℝ) ≅
      (0 : PModule.{u,0,u} k (Fin 1 → ℝ)) := by
  have h : IsZero (CoordinateRealBridge.fromReal (0 : PModule.{u,0,u} k ℝ)) := by
    apply Functor.isZero
    intro a
    exact Functor.zero_obj (C := ℝ) (D := ModuleCat.{u} k) (a 0)
  exact h.isoZero

/-- A positive finite pair as the nonempty half-open one-dimensional rectangle. -/
def halfOpenRectangle (p : ℝ × ℝ) (hp : p.1 < p.2) : Rectangle 1 :=
  fun _ => ⟨p.1, p.2, true, false, Or.inl hp⟩

/-- The coordinate support agrees with the existing half-open convention. -/
theorem halfOpen_support (p : ℝ × ℝ) (hp : p.1 < p.2) (a : Fin 1 → ℝ) :
    a ∈ (halfOpenRectangle p hp).support ↔ p.1 ≤ a 0 ∧ a 0 < p.2 := by
  simp [Rectangle.support, halfOpenRectangle, BoundedInterval.support,
    Fin.forall_fin_one, le_iff_lt_or_eq]

/-- A single rectangle has the existing real barcode module after reindexing. -/
theorem interval_module_eq (p : ℝ × ℝ) (hp : p.1 < p.2) :
    (halfOpenRectangle p hp).module (k := k) =
      CoordinateRealBridge.fromReal (RealBarcode.intervalModule (k := k)
        (p.1, (p.2 : WithTop ℝ))) := by
  have hS : (halfOpenRectangle p hp).support =
      {a : Fin 1 → ℝ | RealBarcode.alive (p.1, (p.2 : WithTop ℝ)) (a 0)} := by
    ext a
    simpa [RealBarcode.alive] using halfOpen_support p hp a
  unfold Rectangle.module
  simp only [hS]
  rfl

/-- The interval comparison is a natural isomorphism, including the zero fibers. -/
noncomputable def intervalIso (p : ℝ × ℝ) (hp : p.1 < p.2) :
    (halfOpenRectangle p hp).module (k := k) ≅
      CoordinateRealBridge.fromReal (RealBarcode.intervalModule (k := k)
        (p.1, (p.2 : WithTop ℝ))) :=
  eqToIso (interval_module_eq p hp)

/-- Half-open deletion uses the closed length threshold, including equality. -/
theorem halfOpen_interleaved_zero_iff (p : ℝ × ℝ) (hp : p.1 < p.2) (ε : ℝ≥0) :
    Nonempty (CoordinateInterleaving ε ((halfOpenRectangle p hp).module (k := k)) 0) ↔
      p.2 - p.1 ≤ 2 * (ε : ℝ) := by
  constructor
  · rintro ⟨I⟩
    apply (RealBarcode.interleaved_zero_iff (k := k) ε p.1 p.2).mp
    exact ⟨CoordinateRealBridge.toReal (I.congr (intervalIso p hp) fromRealZeroIso.symm)⟩
  · intro h
    obtain ⟨I⟩ := (RealBarcode.interleaved_zero_iff (k := k) ε p.1 p.2).mpr h
    exact ⟨(CoordinateRealBridge.toCoordinate I).congr (intervalIso p hp).symm fromRealZeroIso⟩

/-- A surviving summand forces both endpoint coordinates of its interleaved
partner to be within the parameter. No endpoint-decoration hypothesis is used. -/
theorem pairCost_le_of_significant (R S : Rectangle 1) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (R.module (k := k)) S.module)
    (h : Significant (ε + ε) R ∨ Significant (ε + ε) S) :
    finitePairCost ((R 0).lower, (R 0).upper) ((S 0).lower, (S 0).upper) ≤ ε := by
  have hn : I.φ ≠ 0 ∧ I.ψ ≠ 0 := by
    rcases h with h | h
    · have ht := (significant_iff_transition_ne_zero (k := k) R (ε + ε)).mp h
      constructor
      · intro hz
        apply ht
        rw [← I.φ_ψ, hz]
        simp
      · intro hz
        apply ht
        rw [← I.φ_ψ, hz]
        simp
    · have ht := (significant_iff_transition_ne_zero (k := k) S (ε + ε)).mp h
      constructor
      · intro hz
        apply ht
        rw [← I.ψ_φ, hz]
        simp
      · intro hz
        apply ht
        rw [← I.ψ_φ, hz]
        simp
  have hbl := decoratedLE_value (shifted_hom_endpoint_bounds R S ε I.φ hn.1 (0, false))
  have hbu := decoratedLE_value (shifted_hom_endpoint_bounds S R ε I.ψ hn.2 (0, false))
  have hdl := decoratedLE_value (shifted_hom_endpoint_bounds R S ε I.φ hn.1 (0, true))
  have hdu := decoratedLE_value (shifted_hom_endpoint_bounds S R ε I.ψ hn.2 (0, true))
  dsimp [endpoint] at hbl hbu hdl hdu
  apply ENNReal.ofReal_le_coe.mpr
  exact max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩)

private theorem decoratedLE_same {a b : ℝ} (h : a ≤ b) (p : Bool) :
    decoratedLE a b p p :=
  (lt_or_eq_of_le h).elim Or.inl (fun he => Or.inr ⟨he, le_rfl⟩)

/-- Numerical endpoint cost bounds produce actual half-open pair interleavings. -/
noncomputable def pairInterleavingOfCost (p q : ℝ × ℝ)
    (hp : p.1 < p.2) (hq : q.1 < q.2) (ε : ℝ≥0)
    (h : finitePairCost p q ≤ ε) :
    CoordinateInterleaving ε ((halfOpenRectangle p hp).module (k := k))
      (halfOpenRectangle q hq).module := by
  have hr : max |p.1 - q.1| |p.2 - q.2| ≤ (ε : ℝ) := ENNReal.ofReal_le_coe.mp h
  have hb := abs_le.mp ((le_max_left _ _).trans hr)
  have hd := abs_le.mp ((le_max_right _ _).trans hr)
  apply interleavingOfEndpointClose
  rintro ⟨i, b⟩
  fin_cases i
  cases b
  · exact ⟨decoratedLE_same (by dsimp [endpoint, halfOpenRectangle]; linarith [hb.2]) _,
      decoratedLE_same (by dsimp [endpoint, halfOpenRectangle]; linarith [hb.1]) _⟩
  · exact ⟨decoratedLE_same (by dsimp [endpoint, halfOpenRectangle]; linarith [hd.2]) _,
      decoratedLE_same (by dsimp [endpoint, halfOpenRectangle]; linarith [hd.1]) _⟩

private noncomputable def trim {ι κ : Type}
    (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ) (ε : ℝ≥0)
    (M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}) :
    OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1} where
  finite i := (M.finite i).filter (fun j => decide (finitePairCost (x i) (y j) ≤ ε))
  finite_injective i i' j hi hi' :=
    M.finite_injective i i' j (Option.eq_some_of_filter_eq_some hi)
      (Option.eq_some_of_filter_eq_some hi')
  essential := M.essential

private theorem trim_some_iff {ι κ : Type}
    (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ) (ε : ℝ≥0)
    (M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}) (i : ι) (j : κ) :
    (trim x y ε M).finite i = some j ↔
      M.finite i = some j ∧ finitePairCost (x i) (y j) ≤ ε := by
  simp [trim]

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- A numerical cost bound supplies all actual pair and deletion witnesses. -/
theorem isMatching_of_cost (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2)
    (ε : ℝ≥0) (M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1})
    (h : M.cost x y PEmpty.elim PEmpty.elim ≤ ε) :
    RectangleMatching.IsMatching (k := k) ε
      (fun i => halfOpenRectangle (x i) (hx i))
      (fun j => halfOpenRectangle (y j) (hy j)) M := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hc := (M.source_le_cost x y PEmpty.elim PEmpty.elim i).trans h
    rw [hij] at hc
    exact ⟨pairInterleavingOfCost (x i) (y j) (hx i) (hy j) ε hc⟩
  · intro i hi
    have hc := (M.source_le_cost x y PEmpty.elim PEmpty.elim i).trans h
    rw [hi] at hc
    have hl : |(x i).2 - (x i).1| / 2 ≤ (ε : ℝ) := ENNReal.ofReal_le_coe.mp hc
    rw [abs_of_pos (sub_pos.mpr (hx i))] at hl
    exact (halfOpen_interleaved_zero_iff (x i) (hx i) ε).mpr (by linarith)
  · intro j hj
    have hn : ¬ ∃ i, M.finite i = some j := by rintro ⟨i, hi⟩; exact hj i hi
    have hc := (M.target_le_cost x y PEmpty.elim PEmpty.elim j).trans h
    rw [if_neg hn] at hc
    have hl : |(y j).2 - (y j).1| / 2 ≤ (ε : ℝ) := ENNReal.ofReal_le_coe.mp hc
    rw [abs_of_pos (sub_pos.mpr (hy j))] at hl
    exact (halfOpen_interleaved_zero_iff (y j) (hy j) ε).mpr (by linarith)

/-- Removing excessive-cost pairs from an actual matching gives an endpoint
matching at the same radius. Both ends of each removed pair are short. -/
theorem exists_cost_matching (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2)
    (ε : ℝ≥0) (M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1})
    (hM : RectangleMatching.IsMatching (k := k) ε
      (fun i => halfOpenRectangle (x i) (hx i))
      (fun j => halfOpenRectangle (y j) (hy j)) M) :
    ∃ A : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1},
      A.cost x y PEmpty.elim PEmpty.elim ≤ ε := by
  let A := trim x y ε M
  have hdiag (p : ℝ × ℝ) (hp : p.1 < p.2)
      (hz : ¬ Significant (ε + ε) (halfOpenRectangle p hp)) : diagonalCost p ≤ ε := by
    have hi := (RectangleMatching.interleaved_zero_iff (k := k) _ ε).mpr hz
    have hl := (halfOpen_interleaved_zero_iff p hp ε).mp hi
    apply ENNReal.ofReal_le_coe.mpr
    rw [abs_of_pos (sub_pos.mpr hp)]
    linarith
  refine ⟨A, A.cost_le_of x y PEmpty.elim PEmpty.elim ε ?_ ?_ (fun i => nomatch i)⟩
  · intro i
    cases ha : A.finite i with
    | some j =>
      exact (trim_some_iff x y ε M i j).mp ha |>.2
    | none =>
      apply hdiag (x i) (hx i)
      intro hi
      obtain ⟨j, hj⟩ := hM.source_covered i hi
      obtain ⟨I⟩ := hM.paired i j hj
      have hc := pairCost_le_of_significant _ _ ε I (Or.inl hi)
      have he := (trim_some_iff x y ε M i j).mpr ⟨hj, hc⟩
      rw [ha] at he
      contradiction
  · intro j
    split_ifs with hj
    · exact zero_le
    · apply hdiag (y j) (hy j)
      intro hjlong
      obtain ⟨i, hi⟩ := hM.target_covered j hjlong
      obtain ⟨I⟩ := hM.paired i j hi
      have hc := pairCost_le_of_significant _ _ ε I (Or.inr hjlong)
      exact hj ⟨i, (trim_some_iff x y ε M i j).mpr ⟨hi, hc⟩⟩

/-- Equality of the actual-rectangle matching infimum and the existing
numerical finite-endpoint bottleneck. No minimizing matching is assumed. -/
theorem bottleneck_eq_presentation (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    RectangleMatching.bottleneckDistance (k := k)
      (fun i => halfOpenRectangle (x i) (hx i))
      (fun j => halfOpenRectangle (y j) (hy j)) =
        presentationBottleneck x y (PEmpty.elim : PEmpty.{1} → ℝ)
          (PEmpty.elim : PEmpty.{1} → ℝ) := by
  apply le_antisymm
  · apply le_iInf
    intro M
    let C := M.cost x y (PEmpty.elim : PEmpty.{1} → ℝ) PEmpty.elim
    have hC : C ≠ ⊤ := ne_of_lt (occurrenceMatching_cost_lt_top x y _ _ M)
    have hc : C ≤ (C.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hC).symm.le
    have hM := isMatching_of_cost (k := k) x y hx hy C.toNNReal M hc
    simpa only [ENNReal.coe_toNNReal hC] using
      RectangleMatching.bottleneckDistance_le_of_matching hM
  · apply (RectangleMatching.le_bottleneckDistance_iff _ _ _).mpr
    intro ε M hM
    obtain ⟨A, hA⟩ := exists_cost_matching x y hx hy ε M hM
    exact (presentationBottleneck_le_cost x y _ _ A).trans hA

private noncomputable def familyProjection (F : ι → PModule.{u,0,u} k ℝ) (i : ι) :
    RealBarcode.familyModule F ⟶ F i where
  app _ := ModuleCat.ofHom (LinearMap.proj i)
  naturality {s t} f := by ext x; rfl

private noncomputable def familyCone (F : ι → PModule.{u,0,u} k ℝ) :
    Fan (fun i => CoordinateRealBridge.fromReal (F i)) :=
  Fan.mk (CoordinateRealBridge.fromReal (RealBarcode.familyModule F))
    (fun i => reindexNatTrans CoordinateRealBridge.evaluate (familyProjection F i))

private noncomputable def familyIsLimit (F : ι → PModule.{u,0,u} k ℝ) :
    IsLimit (familyCone F) := by
  apply evaluationJointlyReflectsLimits
  intro a
  apply (IsLimit.postcomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) _).toFun
  exact (ModuleCat.productConeIsLimit (fun i => (F i).obj (a 0))).ofIsoLimit
    (Cone.ext (Iso.refl _) (fun j => by
      change ModuleCat.ofHom (LinearMap.proj j.as :
        (∀ i, (F i).obj (a 0)) →ₗ[k] (F j.as).obj (a 0)) =
        𝟙 _ ≫ ModuleCat.ofHom (LinearMap.proj j.as :
          (∀ i, (F i).obj (a 0)) →ₗ[k] (F j.as).obj (a 0)) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]))

/-- The existing rectangle biproduct is the reindexed existing barcode
coordinate product, with the original occurrence labels. -/
noncomputable def familyIso (x : ι → ℝ × ℝ) (hx : ∀ i, (x i).1 < (x i).2) :
    RectangleFamily.module (k := k) (fun i => halfOpenRectangle (x i) (hx i)) ≅
      CoordinateRealBridge.fromReal (RealBarcode.familyModule
        (fun i => RealBarcode.intervalModule (k := k) ((x i).1, ((x i).2 : WithTop ℝ)))) :=
  biproduct.mapIso (fun i => intervalIso (x i) (hx i)) ≪≫
    (biproduct.isLimit _).conePointUniqueUpToIso (familyIsLimit _)

/-- The family comparison retains the original projection at each occurrence. -/
theorem familyIso_hom_apply (x : ι → ℝ × ℝ) (hx : ∀ i, (x i).1 < (x i).2)
    (a : Fin 1 → ℝ)
    (v : (RectangleFamily.module (k := k) (fun i => halfOpenRectangle (x i) (hx i))).obj a)
    (i : ι) :
    ((familyIso x hx).hom.app a).hom v i =
      ((intervalIso (x i) (hx i)).hom.app a).hom
        (((RectangleFamily.projection (k := k)
          (fun j => halfOpenRectangle (x j) (hx j)) i).app a).hom v) := by
  let F := fun i => RealBarcode.intervalModule (k := k) ((x i).1, ((x i).2 : WithTop ℝ))
  have he := IsLimit.conePointUniqueUpToIso_hom_comp
    (biproduct.isLimit (fun i => CoordinateRealBridge.fromReal (F i))) (familyIsLimit F) ⟨i⟩
  have hπ : (familyIso x hx).hom ≫ (familyCone F).π.app ⟨i⟩ =
      RectangleFamily.projection (k := k) (fun j => halfOpenRectangle (x j) (hx j)) i ≫
        (intervalIso (x i) (hx i)).hom := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => biproduct.map (fun j => (intervalIso (x j) (hx j)).hom) ≫ f) he).trans
        (biproduct.map_π _ i))
  exact congrArg (fun f => (f.app a).hom v) hπ

/-- The positive finite endpoint diagram, retaining one copy per occurrence. -/
noncomputable def diagram (x : ι → ℝ × ℝ) (hx : ∀ i, (x i).1 < (x i).2) : Diagram ℝ where
  points := (Finset.univ : Finset ι).val.map (fun i => ((x i).1, ((x i).2 : WithTop ℝ)))
  offDiagonal := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hp
    exact ne_of_lt (WithTop.coe_lt_coe.mpr (hx i))

/-- Endpoint conversion remains positive, rather than merely off the diagonal. -/
theorem diagram_isPositive (x : ι → ℝ × ℝ) (hx : ∀ i, (x i).1 < (x i).2) :
    (diagram x hx).IsPositive := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hp
  exact WithTop.coe_lt_coe.mpr (hx i)

/-- Every finite pair occurrence survives, including repetitions. -/
theorem diagram_finitePart (x : ι → ℝ × ℝ) (hx : ∀ i, (x i).1 < (x i).2) :
    finitePart (diagram x hx).points = (Finset.univ : Finset ι).val.map x := by
  unfold diagram finitePart
  rw [Multiset.filterMap_map]
  exact congrFun (Multiset.filterMap_eq_map x) (Finset.univ : Finset ι).val

/-- Bounded rectangle endpoints create no essential occurrence. -/
theorem diagram_essentialPart (x : ι → ℝ × ℝ) (hx : ∀ i, (x i).1 < (x i).2) :
    essentialPart (diagram x hx).points = 0 := by
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro p
  simp [diagram, essentialPart, Multiset.filterMap_map, Function.comp_def,
    Multiset.mem_filterMap]

/-- The endpoint diagram bottleneck is exactly the existing occurrence
presentation value; its essential occurrence sets are empty. -/
theorem diagram_bottleneck_eq_presentation (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    bottleneck (diagram x hx) (diagram y hy) =
      presentationBottleneck x y (PEmpty.elim : PEmpty.{1} → ℝ)
        (PEmpty.elim : PEmpty.{1} → ℝ) := by
  apply TDA.Persistence.bottleneck_eq_presentation
  · exact (diagram_finitePart x hx).symm
  · exact (diagram_finitePart y hy).symm
  · simp [diagram_essentialPart]
  · simp [diagram_essentialPart]

/-- Re-enumerating the preserved occurrence labels gives the existing diagram
realization as an actual natural isomorphism. -/
noncomputable def diagramFamilyIso (x : ι → ℝ × ℝ) (hx : ∀ i, (x i).1 < (x i).2) :
    RealBarcode.familyModule
        (fun i => RealBarcode.intervalModule (k := k) ((x i).1, ((x i).2 : WithTop ℝ))) ≅
      RealBarcode.realize (k := k) (diagram x hx) := by
  let D := diagram x hx
  let xs := D.points.toList
  let f := fun i => ((x i).1, ((x i).2 : WithTop ℝ))
  have hxlist : (Finset.univ : Finset (Fin xs.length)).val.map (fun i => xs.get i) =
      (Finset.univ : Finset ι).val.map f := by
    rw [Fin.univ_val_map, List.ofFn_get]
    exact Multiset.coe_toList D.points
  let e := (presentationEquiv f (fun i : Fin xs.length => xs.get i) hxlist.symm).1
  change RealBarcode.familyModule (fun i => RealBarcode.intervalModule (k := k) (f i)) ≅
    RealBarcode.familyModule (fun j : Fin xs.length => RealBarcode.intervalModule (k := k) (xs.get j))
  apply RealBarcode.familyIso e
  intro j
  have h := (presentationEquiv f (fun i : Fin xs.length => xs.get i) hxlist.symm).2 (e.symm j)
  have hp : f (e.symm j) = xs.get j := by simpa [e] using h.symm
  exact eqToIso (congrArg (RealBarcode.intervalModule (k := k)) hp)

/-- Natural comparison to the original diagram realization, not just equality
of dimensions, ranks or endpoint multisets. -/
noncomputable def realizationIso (x : ι → ℝ × ℝ) (hx : ∀ i, (x i).1 < (x i).2) :
    RectangleFamily.module (k := k) (fun i => halfOpenRectangle (x i) (hx i)) ≅
      CoordinateRealBridge.fromReal (RealBarcode.realize (k := k) (diagram x hx)) :=
  familyIso x hx ≪≫ Functor.isoWhiskerLeft CoordinateRealBridge.evaluate.toFunctor
    (diagramFamilyIso x hx)

/-- On the common positive finite half-open class, rectangle matching and
the original endpoint diagram bottleneck have the same value. -/
theorem rectangle_bottleneck_eq_diagram (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    RectangleMatching.bottleneckDistance (k := k)
      (fun i => halfOpenRectangle (x i) (hx i))
      (fun j => halfOpenRectangle (y j) (hy j)) = bottleneck (diagram x hx) (diagram y hy) :=
  (bottleneck_eq_presentation x y hx hy).trans (diagram_bottleneck_eq_presentation x y hx hy).symm

/-- The proved n=1 rectangle equality agrees with the original real-indexed
interleaving distance, through the actual realization isomorphisms. -/
theorem rectangle_bottleneck_eq_real_distance (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    RectangleMatching.bottleneckDistance (k := k)
      (fun i => halfOpenRectangle (x i) (hx i))
      (fun j => halfOpenRectangle (y j) (hy j)) =
        realInterleavingDistance (RealBarcode.realize (k := k) (diagram x hx))
          (RealBarcode.realize (diagram y hy)) := by
  rw [RectangleMatching.bottleneckDistance_eq_interleavingDistance_one]
  rw [coordinateInterleavingDistance_congr (realizationIso x hx) (realizationIso y hy)]
  exact CoordinateRealBridge.distance_eq _ _

/-- The original numerical diagram bottleneck and original real barcode
realizations agree on this finite bounded half-open subclass. -/
theorem diagram_bottleneck_eq_real_distance (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    bottleneck (diagram x hx) (diagram y hy) =
      realInterleavingDistance (RealBarcode.realize (k := k) (diagram x hx))
        (RealBarcode.realize (diagram y hy)) :=
  (rectangle_bottleneck_eq_diagram (k := k) x y hx hy).symm.trans
    (rectangle_bottleneck_eq_real_distance x y hx hy)

/-- Zero distance detects endpoint diagrams on the common positive half-open
class. This does not discard endpoint decorations on other rectangle families. -/
theorem real_distance_zero_iff_diagram_eq (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    realInterleavingDistance (RealBarcode.realize (k := k) (diagram x hx))
      (RealBarcode.realize (diagram y hy)) = 0 ↔ diagram x hx = diagram y hy := by
  rw [← diagram_bottleneck_eq_real_distance]
  exact bottleneck_eq_zero_iff _ _

/-- Within this common subclass zero distance does give a natural isomorphism.
The closed-singleton counterexample belongs to the larger decorated domain. -/
theorem real_distance_zero_iff_iso (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    realInterleavingDistance (RealBarcode.realize (k := k) (diagram x hx))
      (RealBarcode.realize (diagram y hy)) = 0 ↔
        Nonempty (RealBarcode.realize (k := k) (diagram x hx) ≅
          RealBarcode.realize (diagram y hy)) := by
  constructor
  · intro h
    exact ⟨eqToIso (congrArg (RealBarcode.realize (k := k))
      ((real_distance_zero_iff_diagram_eq x y hx hy).mp h))⟩
  · rintro ⟨e⟩
    exact realInterleavingDistance_eq_zero_of_iso e

/-- Transport an actual family interleaving to the original real barcode modules. -/
noncomputable def toRealInterleaving (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) {ε : ℝ≥0}
    (I : CoordinateInterleaving ε
      (RectangleFamily.module (k := k) (fun i => halfOpenRectangle (x i) (hx i)))
      (RectangleFamily.module (fun j => halfOpenRectangle (y j) (hy j)))) :
    RealInterleaving ε (RealBarcode.realize (k := k) (diagram x hx))
      (RealBarcode.realize (diagram y hy)) :=
  CoordinateRealBridge.toReal (I.congr (realizationIso x hx) (realizationIso y hy))

/-- Transport in the other direction, preserving the exact parameter. -/
noncomputable def ofRealInterleaving (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) {ε : ℝ≥0}
    (I : RealInterleaving ε (RealBarcode.realize (k := k) (diagram x hx))
      (RealBarcode.realize (diagram y hy))) :
    CoordinateInterleaving ε
      (RectangleFamily.module (k := k) (fun i => halfOpenRectangle (x i) (hx i)))
      (RectangleFamily.module (fun j => halfOpenRectangle (y j) (hy j))) :=
  (CoordinateRealBridge.toCoordinate I).congr
    (realizationIso x hx).symm (realizationIso y hy).symm

/-- On the common subclass, actual real interleavings and cost-bounded
endpoint matchings exist at precisely the same radii, including zero. -/
theorem interleaving_iff_cost_matching (x : ι → ℝ × ℝ) (y : κ → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) (ε : ℝ≥0) :
    Nonempty (RealInterleaving ε (RealBarcode.realize (k := k) (diagram x hx))
      (RealBarcode.realize (diagram y hy))) ↔
      ∃ A : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1},
        A.cost x y PEmpty.elim PEmpty.elim ≤ ε := by
  constructor
  · rintro ⟨I⟩
    obtain ⟨M, hM⟩ := RectangleMatching.exists_matching (k := k) (by decide : 0 < 1)
      (fun i => halfOpenRectangle (x i) (hx i)) (fun j => halfOpenRectangle (y j) (hy j))
      ε (ofRealInterleaving x y hx hy I)
    have hM' : RectangleMatching.IsMatching (k := k) ε
        (fun i => halfOpenRectangle (x i) (hx i))
        (fun j => halfOpenRectangle (y j) (hy j)) M := by
      simpa [stabilityRadius] using hM
    exact exists_cost_matching x y hx hy ε M hM'
  · rintro ⟨M, hM⟩
    exact ⟨toRealInterleaving x y hx hy (isMatching_of_cost x y hx hy ε M hM).interleaving⟩

/-- The nonempty-rectangle contract forces positive length for half-open endpoints. -/
theorem upperOpen_lower_lt_upper (R : Rectangle 1) (hu : (R 0).upperClosed = false) :
    (R 0).lower < (R 0).upper := by
  rcases (R 0).nonempty with h | ⟨_, _, h⟩
  · exact h
  · simp [hu] at h

/-- Every rectangle with the common endpoint convention is produced by the bridge. -/
theorem rectangle_eq_halfOpen (R : Rectangle 1)
    (hl : (R 0).lowerClosed = true) (hu : (R 0).upperClosed = false) :
    R = halfOpenRectangle ((R 0).lower, (R 0).upper) (upperOpen_lower_lt_upper R hu) := by
  funext i
  fin_cases i
  change (⟨(R 0).lower, (R 0).upper, (R 0).lowerClosed,
      (R 0).upperClosed, (R 0).nonempty⟩ : BoundedInterval) = _
  simp only [halfOpenRectangle, BoundedInterval.mk.injEq]
  simpa only [true_and] using And.intro hl hu

/-- Empty, equal-endpoint and reversed half-open intervals in the legacy raw
constructor are zero modules; they are outside the nonempty rectangle domain. -/
theorem empty_interval_isZero (p : ℝ × ℝ) (h : p.2 ≤ p.1) :
    IsZero (RealBarcode.intervalModule (k := k) (p.1, (p.2 : WithTop ℝ))) := by
  apply Functor.isZero
  intro t
  change IsZero (ModuleCat.of k (RealBarcode.fiber (k := k) (p.1, (p.2 : WithTop ℝ)) t))
  have hn : ¬ RealBarcode.alive (p.1, (p.2 : WithTop ℝ)) t := by
    rintro ⟨hl, hu⟩
    exact not_lt_of_ge (h.trans hl) (WithTop.coe_lt_coe.mp hu)
  have : Subsingleton (RealBarcode.fiber (k := k) (p.1, (p.2 : WithTop ℝ)) t) := by
    simp only [RealBarcode.fiber, if_neg hn]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

end TDA.Persistence.RectangleBarcodeBridge
