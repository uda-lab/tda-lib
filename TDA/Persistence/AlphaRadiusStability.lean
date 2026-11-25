import TDA.Persistence.AlphaCech
import TDA.Persistence.CechStability
import TDA.Persistence.DiagramMap
import TDA.Persistence.RealBarcodeRankUniqueness
import TDA.Persistence.SublevelConstructible

set_option autoImplicit false

/-!
# Radius stability of Euclidean α persistence

At radius `r ≥ 0`, α persistence uses the squared grade `r ^ 2`. Whiskering the labelled
α–Čech inclusion by this parameter change identifies the entire radius module with ambient
Čech persistence. Hence the Čech critical radii suffice to recover the α barcode, even when
the α complexes themselves change between those radii.
-/

noncomputable section

universe u w

namespace TDA.Persistence

open CategoryTheory TDA.Filtration TDA.Simplicial FiniteConstructible

/-- Squared α grade at a real radius, extended by the identity on empty negative stages. -/
def alphaRadiusGrade : ℝ →o ℝ where
  toFun r := if r < 0 then r else r ^ 2
  monotone' := by
    intro a b hab
    change (if a < 0 then a else a ^ 2) ≤ (if b < 0 then b else b ^ 2)
    split_ifs with ha hb hb
    · exact hab
    · exact ha.le.trans (sq_nonneg _)
    · exact (ha (hab.trans_lt hb)).elim
    · exact pow_le_pow_left₀ (le_of_not_gt ha) hab 2

/-- At a nonnegative radius the grade is the squared radius. -/
theorem alphaRadiusGrade_of_nonneg {r : ℝ} (hr : 0 ≤ r) : alphaRadiusGrade r = r ^ 2 :=
  ite_eq_right (not_lt_of_ge hr)

/-- At a negative radius the grade is the radius itself. -/
theorem alphaRadiusGrade_of_neg {r : ℝ} (hr : r < 0) : alphaRadiusGrade r = r := ite_eq_left hr

private theorem cechRadius_radiusGrade (r : ℝ) : Alpha.squaredCechRadius (alphaRadiusGrade r) = r := by
  by_cases hr : r < 0
  · rw [alphaRadiusGrade_of_neg hr]
    exact ite_eq_left hr
  · rw [alphaRadiusGrade_of_nonneg (le_of_not_gt hr)]
    change (if r ^ 2 < 0 then r ^ 2 else Real.sqrt (r ^ 2)) = r
    simp [not_lt_of_ge (sq_nonneg r), Real.sqrt_sq (le_of_not_gt hr)]

/-- Change from squared grades to radii, fixing negative thresholds and taking the square
root of each nonnegative threshold. -/
def alphaSquaredGradeToRadius : ℝ ≃o ℝ :=
  OrderIso.ofHomInv Alpha.squaredCechRadius alphaRadiusGrade
    (DFunLike.ext _ _ cechRadius_radiusGrade) (by
      apply DFunLike.ext
      intro t
      by_cases ht : t < 0
      · change alphaRadiusGrade (if t < 0 then t else Real.sqrt t) = t
        simpa [ht] using alphaRadiusGrade_of_neg ht
      · change alphaRadiusGrade (if t < 0 then t else Real.sqrt t) = t
        simp [ht, alphaRadiusGrade_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt (le_of_not_gt ht)])

/-- At a nonnegative squared grade the radius is the square root. -/
theorem alphaSquaredGradeToRadius_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    alphaSquaredGradeToRadius t = Real.sqrt t := ite_eq_right (not_lt_of_ge ht)

variable {V : Type u} [LinearOrder V] [Fintype V]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (k : Type u) [Field k] (p q : V → E) (n : ℕ)

/-- Homology of the labelled α filtration indexed by radius. Its structure maps are the
original homology inclusions at the corresponding squared grades. -/
abbrev alphaRadiusModule := reindex alphaRadiusGrade
  (simplicialHomologyPModule k (Alpha.labelledComplexFiltration p) n)

omit [LinearOrder V] [Fintype V] in
private theorem reindex_squaredCechFiltration :
    TDA.Filtration.reindex alphaRadiusGrade (Alpha.squaredCechFiltration p) =
      (TDA.Filtration.Cech.filter p).sublevelFiltration := by
  rw [TDA.Filtration.Cech.sublevelFiltration_eq_complexFiltration]
  apply DFunLike.ext
  intro r
  change TDA.Filtration.Cech.complex p (Alpha.squaredCechRadius (alphaRadiusGrade r)) = _
  rw [cechRadius_radiusGrade]
  rfl

/-- The same-label inclusion identifies radius α persistence with ambient Čech persistence. -/
def alphaRadiusCechIso :
    alphaRadiusModule k p n ≅ sublevelModule k (TDA.Filtration.Cech.filter p) n :=
  Functor.isoWhiskerLeft alphaRadiusGrade.toFunctor (alphaCechIso p k n) ≪≫
    eqToIso (congrArg (fun F => simplicialHomologyPModule k F n) (reindex_squaredCechFiltration p))

private abbrev radiusGrid := (TDA.Filtration.Cech.filter p).criticalValue

private theorem finiteDimensionalAtRadius :
    ∀ i, FiniteDimensional k ((alphaRadiusModule k p n).obj (radiusGrid p i)) := by
  intro i
  let := sublevelModule_finiteDimensional k n (TDA.Filtration.Cech.filter p) i
  exact ((alphaRadiusCechIso k p n).app (radiusGrid p i)).toLinearEquiv.symm.finiteDimensional

/-- The rank diagram of actual α homology, sampled at the attained Čech radii. -/
def alphaRadiusDiagram : Diagram ℝ :=
  moduleDiagram (radiusGrid p) (alphaRadiusModule k p n) (finiteDimensionalAtRadius k p n)

/-- The labelled radius α and Čech diagrams agree, including essential bars and multiplicities. -/
theorem alphaRadiusDiagram_eq_cech : alphaRadiusDiagram k p n = dgm k (TDA.Filtration.Cech.filter p) n := by
  let c := (radiusGrid p).toOrderHom
  let : ∀ i, FiniteDimensional k ((reindex c (alphaRadiusModule k p n)).obj i) :=
    finiteDimensionalAtRadius k p n
  let : ∀ i, FiniteDimensional k ((reindex c (sublevelModule k (TDA.Filtration.Cech.filter p) n)).obj i) :=
    sublevelModule_finiteDimensional k n _
  exact congrArg (ofIndexBars (radiusGrid p) (radiusGrid p).strictMono)
    (rankBarcode_eq_of_iso (Functor.isoWhiskerLeft c.toFunctor (alphaRadiusCechIso k p n)))

/-- The intervals of the radius diagram realize the α module over the entire parameter line. -/
def alphaRadiusDiagramRealizationIso :
    alphaRadiusModule k p n ≅ RealBarcode.realize (k := k) (alphaRadiusDiagram k p n) :=
  alphaRadiusCechIso k p n ≪≫ sublevelModuleRealizationIso k n _ ≪≫
    eqToIso (congrArg (RealBarcode.realize (k := k)) (alphaRadiusDiagram_eq_cech k p n).symm)

/-- Moving matched labels in a common Euclidean space changes the radius α diagrams by
at most the largest site displacement, in every degree over any field in the universe of the
label type. -/
theorem bottleneck_alphaRadiusDiagram_le_displacement :
    bottleneck (alphaRadiusDiagram k p n) (alphaRadiusDiagram k q n) ≤
      ENNReal.ofReal (TDA.Filtration.Cech.displacement p q) := by
  rw [alphaRadiusDiagram_eq_cech, alphaRadiusDiagram_eq_cech]
  exact Cech.bottleneck_dgm_le_displacement k p q n

/-- For embedded sites the radius diagram is the squared α diagram with its finite
endpoints reparametrized. The essential death `⊤` stays infinite. -/
theorem alphaRadiusDiagram_eq_map (i : V ↪ E) [Fintype (TotalFace (Alpha.carrier i))] :
    alphaRadiusDiagram k i n = (dgm k (Alpha.filter i) n).map alphaSquaredGradeToRadius.toOrderEmbedding := by
  rw [← dgm_map]
  let f := (Alpha.filter i).map alphaSquaredGradeToRadius.toOrderEmbedding
  have hF : TDA.Filtration.reindex alphaRadiusGrade (Alpha.labelledComplexFiltration i) = f.sublevelFiltration := by
    apply DFunLike.ext
    intro r
    change Alpha.complex i (alphaRadiusGrade r) = f.sublevel r
    rw [show f.sublevel r = (Alpha.filter i).sublevel (alphaSquaredGradeToRadius.symm r) from
      FilterFunction.map_sublevel_orderIso _ _ _, Alpha.sublevel_eq_complex]
    rfl
  have eqM : alphaRadiusModule k i n = sublevelModule k f n :=
    congrArg (fun F => simplicialHomologyPModule k F n) hF
  apply RealBarcode.diagram_eq_of_rank_eq (k := k)
  · rw [alphaRadiusDiagram_eq_cech]
    exact dgm_isPositive k (TDA.Filtration.Cech.filter i) n
  · exact dgm_isPositive k f n
  · intro a b hab
    exact rankOfStructureMap_iso hab
      ((alphaRadiusDiagramRealizationIso k i n).symm ≪≫ eqToIso eqM ≪≫ sublevelModuleRealizationIso k n f)

/-- On a bounded radius interval, squaring finite endpoints multiplies their displacement
by at most twice the upper radius bound. -/
theorem abs_sq_sub_sq_le_of_radius_le {a b R ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haR : a ≤ R) (hbR : b ≤ R) (hab : |a - b| ≤ ε) : |a ^ 2 - b ^ 2| ≤ (2 * R) * ε := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  nlinarith [mul_le_mul_of_nonneg_left (show a + b ≤ 2 * R by linarith) (abs_nonneg (a - b)),
    mul_le_mul_of_nonneg_left hab (show 0 ≤ 2 * R by linarith)]

end TDA.Persistence
