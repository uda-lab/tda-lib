import TDA.Persistence.RankErosionCertificate
import TDA.Persistence.RankErosionAttainmentExamples
import TDA.Persistence.RankErosionWitness
import TDA.Persistence.FinitePresentationIndexLift

/-!
# Erosion certificates: executed tests, the fixed-radius comparison and nonseparation

* Executed tests of grid representations over the two-element field as consumers of the
  general statements about `F2GridRep.runErosion`: a failing test gives the chain from the
  tested radius through the erosion distance to the interleaving distance, and refutes
  strict-pair erosion at the tested radius when there is a coordinate.
* The interval module `[0, 1)` against zero: strict-pair erosion holds exactly at the radii
  from `1/2` on, and the executed test passes exactly at the rational radii from `1/2` on.
* With no coordinates two finitely presented modules satisfy strict-pair erosion and violate
  weak-pair erosion at every radius.
* The closed box `[0, 2c]ⁿ` and the zero module are not interleaved at radius `c`; with at
  least one coordinate they are interleaved at every larger radius, so their interleaving
  distance is `c` and is not attained.
* The hypotheses of `radius_lt_coordinateInterleavingDistance_of_rank_violation` give the
  certificate.
* Two two-parameter modules on the square with fibers of dimensions `0`, `1`, `1`, `2`: the
  two arm maps into the top fiber have the same image in the first module and independent
  images in the second. Their Kan extensions are finitely presented, have the same rank at
  every weak pair and erosion distance zero, pass the executed test at every radius, are not
  isomorphic and have nonzero interleaving distance.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankErosionCertificateExamples

open CategoryTheory
open TDA.Persistence.RatGrid TDA.Persistence.F2GridRep
open TDA.Persistence.F2GridRepExamples TDA.Persistence.F2GridErosionExamples
open TDA.Persistence.StrictRankErosionExamples TDA.Persistence.RankErosionAttainmentExamples
open scoped TDA.Persistence NNReal ENNReal ZeroObject

section Executed

/-- The failing executed test at radius `1/4` for the interval module `[0, 1)` and zero: the
radius is strictly below the erosion distance of the actual Kan extensions, which is at most
their interleaving distance. -/
theorem interval_zero_quarter_certificate :
    ((radius (1 / 4) quarter_nonneg : ℝ≥0) : ℝ≥0∞) <
        rankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
          (zero.grid.lan.obj (zero.toModule zero_valid)) ∧
      rankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
          (zero.grid.lan.obj (zero.toModule zero_valid)) ≤
        coordinateInterleavingDistance (interval.grid.lan.obj (interval.toModule interval_valid))
          (zero.grid.lan.obj (zero.toModule zero_valid)) := by
  obtain ⟨_, _, _, _, h⟩ := runErosion_eq_fail_certificate _ _ _ _ interval_zero_quarter
  exact h

/-- The same failing test refutes strict-pair erosion at the tested radius `1/4` itself, and
bounds the strict-pair distance strictly from below. -/
theorem interval_zero_quarter_strict_certificate :
    ¬ StrictRankErosion (radius (1 / 4) quarter_nonneg)
        (interval.grid.lan.obj (interval.toModule interval_valid))
        (zero.grid.lan.obj (zero.toModule zero_valid)) ∧
      ((radius (1 / 4) quarter_nonneg : ℝ≥0) : ℝ≥0∞) <
        strictRankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
          (zero.grid.lan.obj (zero.toModule zero_valid)) := by
  obtain ⟨_, _, _, h⟩ := runErosion_eq_fail_strict_certificate _ _ _ _ interval_zero_quarter
  exact h

/-- The passing executed test at radius `1/2`: both predicates hold and both erosion distances
are at most `1/2`. -/
theorem interval_zero_half_certificate :
    RankErosion (radius (1 / 2) half_nonneg)
        (interval.grid.lan.obj (interval.toModule interval_valid))
        (zero.grid.lan.obj (zero.toModule zero_valid)) ∧
      StrictRankErosion (radius (1 / 2) half_nonneg)
        (interval.grid.lan.obj (interval.toModule interval_valid))
        (zero.grid.lan.obj (zero.toModule zero_valid)) ∧
      rankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
          (zero.grid.lan.obj (zero.toModule zero_valid)) ≤
        ((radius (1 / 2) half_nonneg : ℝ≥0) : ℝ≥0∞) ∧
      strictRankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
          (zero.grid.lan.obj (zero.toModule zero_valid)) ≤
        ((radius (1 / 2) half_nonneg : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨_, _, _, h⟩ := runErosion_eq_pass_certificate _ _ _ interval_zero_half
  exact h

/-- The failing test of the rays born at `0` and at `1` at radius `1/2` bounds their
interleaving distance strictly from below, through their erosion distance. -/
theorem rays_half_lt_coordinateInterleavingDistance :
    ((radius (1 / 2) half_nonneg : ℝ≥0) : ℝ≥0∞) <
      coordinateInterleavingDistance ((ray 0).grid.lan.obj ((ray 0).toModule ray_zero_valid))
        ((ray 1).grid.lan.obj ((ray 1).toModule ray_one_valid)) := by
  obtain ⟨_, _, _, _, h₁, h₂⟩ := runErosion_eq_fail_certificate _ _ _ _ rays_half
  exact h₁.trans_le h₂

/-- Two parameters: the failing executed test at radius `0` shows that the two Kan extensions
are not isomorphic. -/
theorem plane_flat_not_iso :
    IsEmpty (plane.grid.lan.obj (plane.toModule plane_valid) ≅
      flat.grid.lan.obj (flat.toModule flat_valid)) := by
  obtain ⟨_, _, _, _, h₁, h₂⟩ := runErosion_eq_fail_certificate _ _ _ _ plane_flat_zero
  refine ⟨fun e => ?_⟩
  have h := h₁.trans_le h₂
  rw [coordinateInterleavingDistance_eq_zero_of_iso e] at h
  exact lt_irrefl _ (zero_le.trans_lt h)

end Executed

section IntervalRadii

/-- The fixed-radius comparison for the interval module `[0, 1)` and zero: strict-pair erosion
holds exactly at the radii from `1/2` on. -/
theorem interval_zero_strictRankErosion_iff (ε : ℝ≥0) :
    StrictRankErosion ε (interval.grid.lan.obj (interval.toModule interval_valid))
        (zero.grid.lan.obj (zero.toModule zero_valid)) ↔
      radius (1 / 2) half_nonneg ≤ ε := by
  rw [GradedFree.finitelyPresented_strictRankErosion_iff_rankErosion
      (interval.finitelyPresented_lan_toModule interval_valid)
      (zero.finitelyPresented_lan_toModule zero_valid),
    interval_zero_rankErosion_iff]

/-- The executed test of the interval module `[0, 1)` against zero passes exactly at the
rational radii from `1/2` on; at a negative radius the input is invalid. -/
theorem interval_zero_runErosion_eq_pass_iff (e : ℚ) :
    runErosion interval zero e = .pass ↔ 1 / 2 ≤ e := by
  by_cases he : 0 ≤ e
  · rw [runErosion_eq_pass_iff_rankErosionDistance_le interval zero interval_valid zero_valid he,
      interval_zero_rankErosionDistance, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_radius,
      coe_radius, Rat.cast_le]
  · rw [(runErosion_eq_invalid_iff interval zero e).mpr fun h => he h.2.2]
    exact iff_of_false (by simp) fun h => he (le_trans (by norm_num) h)

end IntervalRadii

section NoCoordinates

/-- With no coordinates the fixed-radius comparison fails for finitely presented modules: the
two Kan extensions with fibers of dimensions three and two are finitely presented, satisfy
strict-pair erosion at every radius and violate weak-pair erosion at every radius. -/
theorem noCoordinates_finitelyPresented_not_iff (ε : ℝ≥0) :
    GradedFree.FinitelyPresented.{0,0,0} (R := ZMod 2)
        (noCoordinates.grid.lan.obj (noCoordinates.toModule noCoordinates_valid)) ∧
      GradedFree.FinitelyPresented.{0,0,0} (R := ZMod 2)
        (noCoordinatesTwo.grid.lan.obj (noCoordinatesTwo.toModule noCoordinatesTwo_valid)) ∧
      ¬ (StrictRankErosion ε
          (noCoordinates.grid.lan.obj (noCoordinates.toModule noCoordinates_valid))
          (noCoordinatesTwo.grid.lan.obj (noCoordinatesTwo.toModule noCoordinatesTwo_valid)) ↔
        RankErosion ε
          (noCoordinates.grid.lan.obj (noCoordinates.toModule noCoordinates_valid))
          (noCoordinatesTwo.grid.lan.obj (noCoordinatesTwo.toModule noCoordinatesTwo_valid))) :=
  ⟨noCoordinates.finitelyPresented_lan_toModule noCoordinates_valid,
    noCoordinatesTwo.finitelyPresented_lan_toModule noCoordinatesTwo_valid,
    fun h => noCoordinates_not_rankErosion ε (h.mp (noCoordinates_strictRankErosion ε))⟩

/-- The failing executed test with no coordinates still gives the certificate for the weak-pair
distance and the interleaving distance, at the tested radius `3`. -/
theorem noCoordinates_lt_coordinateInterleavingDistance :
    ((radius 3 (by norm_num) : ℝ≥0) : ℝ≥0∞) <
      coordinateInterleavingDistance
        (noCoordinates.grid.lan.obj (noCoordinates.toModule noCoordinates_valid))
        (noCoordinatesTwo.grid.lan.obj (noCoordinatesTwo.toModule noCoordinatesTwo_valid)) := by
  obtain ⟨_, _, _, _, h₁, h₂⟩ := runErosion_eq_fail_certificate _ _ _ _ noCoordinates_differ
  exact h₁.trans_le h₂

end NoCoordinates

section ClosedBox

variable {n : ℕ}

/-- The closed box `[0, 2c]ⁿ` and the zero module are not interleaved at radius `c`, for any
number of coordinates: an interleaving would give weak-pair erosion at `c`. -/
theorem closedBox_not_interleaving (c : ℝ≥0) :
    ¬ Nonempty (CoordinateInterleaving c (closedBox (n := n) c) 0) := fun ⟨I⟩ =>
  have := zero_finiteDimensional (n := n)
  closedBox_not_rankErosion c I.rankErosion

/-- With at least one coordinate they are interleaved at every radius above `c`, by the zero
maps: the structure map of the closed box from a grade to its translate by twice the radius
leaves the box. -/
theorem closedBox_interleaving_of_lt [NeZero n] {c c' : ℝ≥0} (h : c < c') :
    Nonempty (CoordinateInterleaving c' (closedBox (n := n) c) 0) := by
  refine ⟨CoordinateInterleaving.ofStructureMapEquations 0 0 (fun a => ?_) (fun a => ?_)⟩
  · change (0 : (closedBox c).obj a ⟶
      (0 : PModule.{0,0,0} ℚ (Fin n → ℝ)).obj (CoordinateShift.translation c' a)) ≫ 0 = _
    rw [Limits.zero_comp]
    symm
    apply ModuleCat.hom_ext
    refine SupportInterval.structureMap_eq_zero_of_not_mem (box c) Set.ordConnected_Icc _
      fun hm => ?_
    have h0 : 0 ≤ a 0 := (mem_box.mp hm.1 0).1
    have h1 : a 0 + (c' : ℝ) + (c' : ℝ) ≤ 2 * (c : ℝ) := (mem_box.mp hm.2 0).2
    have hlt : (c : ℝ) < c' := NNReal.coe_lt_coe.mpr h
    linarith
  · exact (Functor.zero_obj a).eq_of_src _ _

/-- With at least one coordinate their interleaving distance is `c`, and it is not attained. -/
theorem closedBox_coordinateInterleavingDistance [NeZero n] (c : ℝ≥0) :
    coordinateInterleavingDistance (closedBox (n := n) c) 0 = c := by
  have := zero_finiteDimensional (n := n)
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_) ?_
  · have hle := coordinateInterleavingDistance_le_of_nonempty
      (closedBox_interleaving_of_lt (n := n) (lt_add_of_pos_right c hδ))
    rwa [ENNReal.coe_add] at hle
  · rw [← closedBox_rankErosionDistance (n := n) c]
    exact rankErosionDistance_le_coordinateInterleavingDistance _ _

end ClosedBox

section PairViolation

variable {k : Type u} [Field k] {n : ℕ} {M N : PModule.{u,0,u} k (Fin n → ℝ)}

/-- The hypotheses of `radius_lt_coordinateInterleavingDistance_of_rank_violation`, without its
finite-dimensionality instances, give the certificate: a violated inequality at one weak pair,
for presentations indexed in the universe of the coefficients. -/
theorem certificate_of_rank_violation {ε : ℝ≥0}
    (hM : GradedFree.FinitelyPresented.{u,0,u} (R := k) M)
    (hN : GradedFree.FinitelyPresented.{u,0,u} (R := k) N)
    {a b : Fin n → ℝ} (hab : a ≤ b)
    (h : rankOfStructureMap N hab < rankOfStructureMap M (erosionWide_le ε hab)) :
    (ε : ℝ≥0∞) < rankErosionDistance M N ∧
      rankErosionDistance M N ≤ coordinateInterleavingDistance M N :=
  GradedFree.finitelyPresented_rankErosion_failure_certificate
    (GradedFree.finitelyPresented_lowerIndexUniverse M hM)
    (GradedFree.finitelyPresented_lowerIndexUniverse N hN)
    fun H => absurd (H.1 a b hab) (not_le.mpr h)

end PairViolation

section Nonseparation

/-- The images of two structure maps into a common fiber have a nonzero vector in common. -/
def ImagesMeet {R : Type} [Ring R] {P : Type} [Preorder P] (M : PModule.{0,0,0} R P)
    {a b c : P} (hac : a ≤ c) (hbc : b ≤ c) : Prop :=
  ∃ (x : M.obj a) (y : M.obj b),
    structureMapLinear M hac x = structureMapLinear M hbc y ∧ structureMapLinear M hac x ≠ 0

/-- Isomorphic modules have the same meeting images. -/
private theorem ImagesMeet.of_iso {R : Type} [Ring R] {P : Type} [Preorder P]
    {M N : PModule.{0,0,0} R P} (e : M ≅ N) {a b c : P} {hac : a ≤ c} {hbc : b ≤ c}
    (h : ImagesMeet M hac hbc) : ImagesMeet N hac hbc := by
  obtain ⟨x, y, hxy, hne⟩ := h
  have hnat : ∀ {p q : P} (hpq : p ≤ q) (z : M.obj p),
      structureMapLinear N hpq ((e.hom.app p).hom z) =
        (e.hom.app q).hom (structureMapLinear M hpq z) := fun hpq z =>
    (congrArg (fun f => f.hom z) (e.hom.naturality (homOfLE hpq))).symm
  have hinj : Function.Injective (e.hom.app c).hom :=
    (ConcreteCategory.bijective_of_isIso (e.hom.app c)).injective
  refine ⟨(e.hom.app a).hom x, (e.hom.app b).hom y, ?_, ?_⟩
  · rw [hnat, hnat, hxy]
  · rw [hnat]
    exact fun h0 => hne (hinj (h0.trans (map_zero _).symm))

/-- For the Kan extension of a grid module, the images of two structure maps meet exactly when
the images of the structure maps between the floors meet. -/
private theorem imagesMeet_lan_iff {R : Type} [Ring R] {n : ℕ} (G : CoordinateGrid n)
    (M : PModule.{0,0,0} R G.Point) {a b c : Fin n → ℝ} (hac : a ≤ c) (hbc : b ≤ c)
    (ha : G.HasLowerPoint a) (hb : G.HasLowerPoint b) (hc : G.HasLowerPoint c) :
    ImagesMeet (G.lan.obj M) hac hbc ↔
      ImagesMeet M (G.floor_mono hac ha hc) (G.floor_mono hbc hb hc) := by
  have hinj : Function.Injective (G.appIso M c hc).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (G.appIso M c hc).hom).injective
  have hsa : Function.Surjective (G.appIso M a ha).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (G.appIso M a ha).hom).surjective
  have hsb : Function.Surjective (G.appIso M b hb).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (G.appIso M b hb).hom).surjective
  constructor
  · rintro ⟨x, y, hxy, hne⟩
    refine ⟨(G.appIso M a ha).hom.hom x, (G.appIso M b hb).hom.hom y, ?_, ?_⟩
    · rw [← G.appIso_structureMap_apply M hac ha hc, ← G.appIso_structureMap_apply M hbc hb hc,
        hxy]
    · rw [← G.appIso_structureMap_apply M hac ha hc]
      exact fun h0 => hne (hinj (h0.trans (map_zero _).symm))
  · rintro ⟨x', y', hxy, hne⟩
    obtain ⟨x, rfl⟩ := hsa x'
    obtain ⟨y, rfl⟩ := hsb y'
    rw [← G.appIso_structureMap_apply M hac ha hc] at hxy hne
    rw [← G.appIso_structureMap_apply M hbc hb hc] at hxy
    exact ⟨x, y, hinj hxy, fun h0 => hne (by rw [h0, map_zero])⟩

/-- The stored matrices from two rational grades into a third have a nonzero image vector in
common. -/
private def ColumnsMeet {n : ℕ} (R : F2GridRep n) (p q r : Fin n → ℚ) : Prop :=
  ∃ (x : Fin (R.dim p) → ZMod 2) (y : Fin (R.dim q) → ZMod 2),
    (R.map p r).mulVec x = (R.map q r).mulVec y ∧ (R.map p r).mulVec x ≠ 0

private instance columnsMeetDecidable {n : ℕ} (R : F2GridRep n) (p q r : Fin n → ℚ) :
    Decidable (ColumnsMeet R p q r) := by
  unfold ColumnsMeet
  infer_instance

/-- For the Kan extension of a valid representation, the images of the structure maps from two
rational grades with lower grid values into a third meet exactly when the stored matrices
between the executable floors have a nonzero image vector in common. -/
private theorem imagesMeet_lan_toModule_iff {n : ℕ} (R : F2GridRep n) (hR : R.Valid)
    {p q r : Fin n → ℚ} (hpr : p ≤ r) (hqr : q ≤ r) (hp : R.values.hasLower p = true)
    (hq : R.values.hasLower q = true) :
    ImagesMeet (R.grid.lan.obj (R.toModule hR)) (realGrade_le_iff.mpr hpr)
        (realGrade_le_iff.mpr hqr) ↔
      ColumnsMeet R (R.values.floor p) (R.values.floor q) (R.values.floor r) := by
  have ha := (R.values.hasLowerPoint_realGrade_iff p).mpr hp
  have hb := (R.values.hasLowerPoint_realGrade_iff q).mpr hq
  have hc := R.grid.hasLowerPoint_mono (realGrade_le_iff.mpr hpr) ha
  rw [imagesMeet_lan_iff R.grid (R.toModule hR) _ _ ha hb hc, ← R.values.ratPoint_floor p ha,
    ← R.values.ratPoint_floor q hb, ← R.values.ratPoint_floor r hc]
  exact Iff.rfl

/-- Fiber dimensions on the square with coordinates `0, 1`: zero at the origin, one at `(1, 0)`
and at `(0, 1)`, two at `(1, 1)`. -/
def squareDim (a : Fin 2 → ℚ) : ℕ :=
  if a 0 = 1 then (if a 1 = 1 then 2 else 1) else (if a 1 = 1 then 1 else 0)

/-- Both arm maps into the two-dimensional top fiber send the generator to the first basis
vector. -/
def armsCoincident : F2GridRep 2 where
  values := fun _ => [0, 1]
  dim := squareDim
  map := fun a b => Matrix.of fun i j =>
    if squareDim a = squareDim b then (if (i : ℕ) = (j : ℕ) then 1 else 0)
    else if (i : ℕ) = 0 then 1 else 0

/-- The arm map from `(1, 0)` sends the generator to the first basis vector of the top fiber,
the arm map from `(0, 1)` to the second. -/
def armsIndependent : F2GridRep 2 where
  values := fun _ => [0, 1]
  dim := squareDim
  map := fun a b => Matrix.of fun i j =>
    if squareDim a = squareDim b then (if (i : ℕ) = (j : ℕ) then 1 else 0)
    else if (i : ℕ) = (if a 0 = 1 then 0 else 1) then 1 else 0

/-- The first representation is valid. -/
theorem armsCoincident_valid : armsCoincident.Valid := by decide +kernel

/-- The second representation is valid. -/
theorem armsIndependent_valid : armsIndependent.Valid := by decide +kernel

/-- The executed test at radius `0` finds no rank difference between the two modules. -/
theorem arms_zero : runErosion armsCoincident armsIndependent 0 = .pass := by decide +kernel

/-- The Kan extensions of the two modules have the same rank at every weak pair. -/
theorem arms_rank_eq (a b : Fin 2 → ℝ) (hab : a ≤ b) :
    rankOfStructureMap (armsCoincident.grid.lan.obj (armsCoincident.toModule armsCoincident_valid))
        hab =
      rankOfStructureMap
        (armsIndependent.grid.lan.obj (armsIndependent.toModule armsIndependent_valid)) hab := by
  obtain ⟨_, _, _, h, _⟩ := runErosion_eq_pass_certificate _ _ _ arms_zero
  have h0 : radius 0 le_rfl = 0 := by
    rw [← NNReal.coe_inj, coe_radius]
    simp
  rw [h0] at h
  exact rankErosion_zero_iff.mp h a b hab

/-- Their erosion distance is zero. -/
theorem arms_rankErosionDistance :
    rankErosionDistance
        (armsCoincident.grid.lan.obj (armsCoincident.toModule armsCoincident_valid))
        (armsIndependent.grid.lan.obj (armsIndependent.toModule armsIndependent_valid)) = 0 :=
  (GradedFree.finitelyPresented_rankErosionDistance_eq_zero_iff
    (armsCoincident.finitelyPresented_lan_toModule armsCoincident_valid)
    (armsIndependent.finitelyPresented_lan_toModule armsIndependent_valid)).mpr arms_rank_eq

/-- The executed test passes at every nonnegative rational radius: no rank test separates the
two modules. -/
theorem arms_runErosion_eq_pass_iff (e : ℚ) :
    runErosion armsCoincident armsIndependent e = .pass ↔ 0 ≤ e := by
  by_cases he : 0 ≤ e
  · rw [runErosion_eq_pass_iff_rankErosionDistance_le _ _ armsCoincident_valid
      armsIndependent_valid he, arms_rankErosionDistance]
    exact iff_of_true zero_le he
  · rw [(runErosion_eq_invalid_iff armsCoincident armsIndependent e).mpr fun h => he h.2.2]
    exact iff_of_false (by simp) he

/-- The grade `(1, 0)` lies below `(1, 1)`. -/
theorem arm_right_le : (![1, 0] : Fin 2 → ℚ) ≤ ![1, 1] := by decide +kernel

/-- The grade `(0, 1)` lies below `(1, 1)`. -/
theorem arm_up_le : (![0, 1] : Fin 2 → ℚ) ≤ ![1, 1] := by decide +kernel

/-- In the first module the images of the two arm maps into the fiber at `(1, 1)` meet. -/
theorem armsCoincident_imagesMeet :
    ImagesMeet (armsCoincident.grid.lan.obj (armsCoincident.toModule armsCoincident_valid))
      (realGrade_le_iff.mpr arm_right_le) (realGrade_le_iff.mpr arm_up_le) :=
  (imagesMeet_lan_toModule_iff armsCoincident armsCoincident_valid arm_right_le arm_up_le
    (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)

/-- In the second module they do not. -/
theorem armsIndependent_not_imagesMeet :
    ¬ ImagesMeet
      (armsIndependent.grid.lan.obj (armsIndependent.toModule armsIndependent_valid))
      (realGrade_le_iff.mpr arm_right_le) (realGrade_le_iff.mpr arm_up_le) := fun h =>
  absurd ((imagesMeet_lan_toModule_iff armsIndependent armsIndependent_valid arm_right_le
    arm_up_le (by decide +kernel) (by decide +kernel)).mp h) (by decide +kernel)

/-- The two Kan extensions are not isomorphic. -/
theorem arms_not_iso :
    IsEmpty (armsCoincident.grid.lan.obj (armsCoincident.toModule armsCoincident_valid) ≅
      armsIndependent.grid.lan.obj (armsIndependent.toModule armsIndependent_valid)) :=
  ⟨fun e => armsIndependent_not_imagesMeet (armsCoincident_imagesMeet.of_iso e)⟩

/-- **Nonseparation.** Two finitely presented two-parameter modules with erosion distance zero
and nonzero interleaving distance: the rank invariant does not determine the module. -/
theorem arms_nonseparation :
    GradedFree.FinitelyPresented.{0,0,0} (R := ZMod 2)
        (armsCoincident.grid.lan.obj (armsCoincident.toModule armsCoincident_valid)) ∧
      GradedFree.FinitelyPresented.{0,0,0} (R := ZMod 2)
        (armsIndependent.grid.lan.obj (armsIndependent.toModule armsIndependent_valid)) ∧
      rankErosionDistance
        (armsCoincident.grid.lan.obj (armsCoincident.toModule armsCoincident_valid))
        (armsIndependent.grid.lan.obj (armsIndependent.toModule armsIndependent_valid)) = 0 ∧
      coordinateInterleavingDistance
        (armsCoincident.grid.lan.obj (armsCoincident.toModule armsCoincident_valid))
        (armsIndependent.grid.lan.obj (armsIndependent.toModule armsIndependent_valid)) ≠ 0 :=
  ⟨armsCoincident.finitelyPresented_lan_toModule armsCoincident_valid,
    armsIndependent.finitelyPresented_lan_toModule armsIndependent_valid,
    arms_rankErosionDistance,
    fun h => arms_not_iso.false ((GradedFree.finitelyPresented_distance_eq_zero_iff_iso
      (armsCoincident.finitelyPresented_lan_toModule armsCoincident_valid)
      (armsIndependent.finitelyPresented_lan_toModule armsIndependent_valid)).mp h).some⟩

end Nonseparation

end TDA.Persistence.RankErosionCertificateExamples
