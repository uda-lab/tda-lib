import TDA.Sheaf.BandMatchingLowerBound

/-!
# Attainment of the band distance

A minimizing graded matching of finite cost assembles a witness at its cost.
The finite isometry identifies that radius with the band distance of the sums.
The same criterion applies to bounded objects through their graded barcodes.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open TDA.Sheaf.RealConstructible TDA.Sheaf.RealStratification
open scoped ENNReal

namespace TDA.Sheaf.BandConvolution

variable {k : Type} [Field k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

local notation "Sh" => realLine.Sheaf (ModuleCat k)

section Biproduct

variable {I J : Type} [Fintype I] [Fintype J]
  {mi : I → ℕ} {nj : J → ℕ} {pi : (i : I) → Fin (mi i) → ℝ} {qj : (j : J) → Fin (nj j) → ℝ}
  (hpi : ∀ i, StrictMono (pi i)) (hqj : ∀ j, StrictMono (qj j))
  {X : (i : I) → GradedInterval (mi i)} {Y : (j : J) → GradedInterval (nj j)}

local notation "XX" => (fun i => GradedInterval.obj k (hpi i) (X i))
local notation "YY" => (fun j => GradedInterval.obj k (hqj j) (Y j))

/-- A real radius admits a witness of finite graded interval sums exactly when it bounds
their band distance. -/
theorem nonempty_witness_biproduct_iff_distance_le {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (Witness k hr (⨁ XX) (⨁ YY)) ↔ distance (⨁ XX) (⨁ YY) ≤ ENNReal.ofReal r := by
  refine ⟨fun ⟨w⟩ => w.distance_le, ?_⟩
  intro h
  obtain ⟨M, hM⟩ := exists_matching_cost_eq XX YY
  rw [distance_biproduct_eq_matchingDistance hpi hqj, ← hM] at h
  let E i := IntervalEndpoints.ofInterval (hpi i) (X i).interval
  let F j := IntervalEndpoints.ofInterval (hqj j) (Y j).interval
  have hE i := IntervalEndpoints.support_ofInterval (hpi i) (X i).interval
  have hF j := IntervalEndpoints.support_ofInterval (hqj j) (Y j).interval
  obtain ⟨hp, hl, hr'⟩ := M.cost_le_iff.mp h
  refine M.nonempty_witness_biproduct hr ?_ ?_ ?_
  · intro i j hij
    apply ((E i).nonempty_witness_iff_totalPairCost_le k (hpi i) (hqj j) (X i) (Y j)
      (F j) (hE i) (hF j) hr).mpr
    rw [← (E i).distance_eq_totalPairCost k (hpi i) (hqj j) (X i) (Y j) (F j) (hE i) (hF j)]
    exact hp i j hij
  · intro i hi
    apply ((E i).nonempty_witness_zero_iff_deletionCost_le k (hpi i) (X i) (hE i) hr).mpr
    rw [← (E i).distance_zero_eq k (hpi i) (X i) (hE i)]
    exact hl i hi
  · intro j hj
    apply ((F j).nonempty_witness_zero_iff_deletionCost_le k (hqj j) (Y j) (hF j) hr).mpr
    rw [← (F j).distance_zero_eq k (hqj j) (Y j) (hF j)]
    exact hr' j hj

/-- Finite graded interval sums at finite distance admit a witness at that distance. -/
theorem nonempty_witness_biproduct_at_distance (h : distance (⨁ XX) (⨁ YY) < ⊤) :
    Nonempty (Witness k (ENNReal.toReal_nonneg (a := distance (⨁ XX) (⨁ YY))) (⨁ XX) (⨁ YY)) :=
  (nonempty_witness_biproduct_iff_distance_le hpi hqj ENNReal.toReal_nonneg).mpr
    (ENNReal.ofReal_toReal h.ne).ge

/-- The fixed-radius witness criterion for objects presented as finite graded interval sums. -/
theorem nonempty_witness_of_iso_biproduct_iff_distance_le {K L : Plus Sh}
    (e : K ≅ ⨁ XX) (f : L ≅ ⨁ YY) {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (Witness k hr K L) ↔ distance K L ≤ ENNReal.ofReal r := by
  rw [distance_congr e f, ← nonempty_witness_biproduct_iff_distance_le hpi hqj hr]
  exact ⟨fun ⟨w⟩ => ⟨w.congr e f⟩, fun ⟨w⟩ => ⟨w.congr e.symm f.symm⟩⟩

/-- Objects presented as finite graded interval sums attain their finite band distance. -/
theorem nonempty_witness_of_iso_biproduct_at_distance {K L : Plus Sh}
    (e : K ≅ ⨁ XX) (f : L ≅ ⨁ YY) (h : distance K L < ⊤) :
    Nonempty (Witness k (ENNReal.toReal_nonneg (a := distance K L)) K L) :=
  (nonempty_witness_of_iso_biproduct_iff_distance_le hpi hqj e f ENNReal.toReal_nonneg).mpr
    (ENNReal.ofReal_toReal h.ne).ge

end Biproduct

variable {m n : ℕ} {p : Fin m → ℝ} {q : Fin n → ℝ}

/-- A real radius admits a bounded witness of objects with constructible cohomology exactly
when it bounds their band distance. -/
theorem nonempty_witnessB_iff_distanceB_le (hp : StrictMono p) (hq : StrictMono q)
    (K L : Bounded Sh) (a b c d : ℤ) [K.obj.IsGE a] [K.obj.IsLE b] [L.obj.IsGE c] [L.obj.IsLE d]
    (hK : HasConstructibleCohomology k p K.obj) (hL : HasConstructibleCohomology k q L.obj)
    {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (WitnessB k hr K L) ↔ distanceB K L ≤ ENNReal.ofReal r := by
  obtain ⟨e⟩ := nonempty_iso_biproduct_gradedBarcode k hp K a b hK
  obtain ⟨f⟩ := nonempty_iso_biproduct_gradedBarcode k hq L c d hL
  rw [nonempty_witnessB_iff]
  exact nonempty_witness_of_iso_biproduct_iff_distance_le (fun _ => hp) (fun _ => hq)
    ((boundedToPlus Sh).mapIso e ≪≫ (boundedToPlus Sh).mapBiproduct _)
    ((boundedToPlus Sh).mapIso f ≪≫ (boundedToPlus Sh).mapBiproduct _) hr

/-- Bounded objects with constructible cohomology at finite distance admit a bounded witness
at that distance. -/
theorem nonempty_witnessB_at_distanceB (hp : StrictMono p) (hq : StrictMono q)
    (K L : Bounded Sh) (a b c d : ℤ) [K.obj.IsGE a] [K.obj.IsLE b] [L.obj.IsGE c] [L.obj.IsLE d]
    (hK : HasConstructibleCohomology k p K.obj) (hL : HasConstructibleCohomology k q L.obj)
    (h : distanceB K L < ⊤) :
    Nonempty (WitnessB k (ENNReal.toReal_nonneg (a := distanceB K L)) K L) :=
  (nonempty_witnessB_iff_distanceB_le hp hq K L a b c d hK hL ENNReal.toReal_nonneg).mpr
    (ENNReal.ofReal_toReal h.ne).ge

end TDA.Sheaf.BandConvolution
