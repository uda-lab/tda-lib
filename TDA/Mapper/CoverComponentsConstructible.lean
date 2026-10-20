import TDA.Mapper.CoverComponentsCosheaf
import TDA.Mapper.GraphPLCosheaf

/-!
# Finite constructibility of interval-cover assembly

The endpoints of a finite family of bounded intervals form a critical-value witness for
the assembled component precosheaf. The proof compares the actual saturated open sets:
a nested nonempty interval enlargement that sees no new endpoint changes no active member.
No vertex-height genericity or absence of horizontal graph edges is needed.
-/

open Set CategoryTheory

universe u v

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.OpenInterval

/-- A real interval containing the left endpoint meets every nonempty interval to its right. -/
theorem ioo_inter_nonempty_of_left_mem (I : OpenInterval) {a b : ℝ}
    (ha : a ∈ I) (hab : a < b) : ((ioo a b : Set ℝ) ∩ I).Nonempty := by
  obtain ⟨l, r, ⟨hla, har⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (I.isOpen.mem_nhds ha)
  obtain ⟨x, hax, hxr⟩ := exists_between (lt_min har hab)
  exact ⟨x, ⟨hax, hxr.trans_le (min_le_right _ _)⟩,
    hsub ⟨hla.trans hax, hxr.trans_le (min_le_left _ _)⟩⟩

/-- The symmetric endpoint form. -/
theorem ioo_inter_nonempty_of_right_mem (I : OpenInterval) {a b : ℝ}
    (hb : b ∈ I) (hab : a < b) : ((ioo a b : Set ℝ) ∩ I).Nonempty := by
  obtain ⟨l, r, ⟨hlb, hbr⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (I.isOpen.mem_nhds hb)
  obtain ⟨x, hlx, hxb⟩ := exists_between (max_lt hlb hab)
  exact ⟨x, ⟨(le_max_right _ _).trans_lt hlx, hxb⟩,
    hsub ⟨(le_max_left _ _).trans_lt hlx, hxb.trans hbr⟩⟩

/-- Same-endpoint interval enlargements activate exactly the same bounded cover member. -/
theorem ioo_inter_nonempty_of_same_endpoints {I J : OpenInterval} (hIJ : I ≤ J)
    (hI : (I : Set ℝ).Nonempty) {a b : ℝ}
    (ha : a ∈ I ↔ a ∈ J) (hb : b ∈ I ↔ b ∈ J) :
    ((ioo a b : Set ℝ) ∩ I).Nonempty ↔ ((ioo a b : Set ℝ) ∩ J).Nonempty := by
  constructor
  · rintro ⟨x, hx, hxI⟩
    exact ⟨x, hx, hIJ hxI⟩
  · rintro ⟨y, ⟨hay, hyb⟩, hyJ⟩
    obtain ⟨x, hxI⟩ := hI
    by_cases hx : a < x ∧ x < b
    · exact ⟨x, hx, hxI⟩
    · by_cases hxa : x ≤ a
      · have haJ : a ∈ J := J.ordConnected.out (hIJ hxI) hyJ ⟨hxa, hay.le⟩
        exact ioo_inter_nonempty_of_left_mem I (ha.mpr haJ) (hay.trans hyb)
      · have hbx : b ≤ x := le_of_not_gt (fun hxb => hx ⟨lt_of_not_ge hxa, hxb⟩)
        have hbJ : b ∈ J := J.ordConnected.out hyJ (hIJ hxI) ⟨hyb.le, hbx⟩
        exact ioo_inter_nonempty_of_right_mem I (hb.mpr hbJ) (hay.trans hyb)

variable {ι : Type v} (a b : ι → ℝ)

/-- The endpoint family whose sorted distinct values are used as critical levels. -/
def coverEndpointHeight : ι × Bool → ℝ := fun p => if p.2 then b p.1 else a p.1

/-- A critical-value witness contains both endpoints of every cover member. -/
def CoversIntervalEndpoints {n : ℕ} (S : CriticalValues n) : Prop :=
  (∀ i, a i ∈ Set.range S.value) ∧ ∀ i, b i ∈ Set.range S.value

/-- The existing finite real-value sorting API supplies the cover's endpoint witness. -/
theorem exists_coversIntervalEndpoints [Finite ι] :
    ∃ n, ∃ S : CriticalValues n, CoversIntervalEndpoints a b S := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let : Subsingleton (Fin (0 + 1)) := ⟨fun i j =>
      (Fin.eq_zero i).trans (Fin.eq_zero j).symm⟩
    exact ⟨0, ⟨fun _ => 0, Subsingleton.strictMono _⟩,
      (fun i => isEmptyElim i), fun i => isEmptyElim i⟩
  · let : Nonempty ι := hι
    let : Fintype (ι × Bool) := Fintype.ofFinite _
    refine ⟨_, GraphPL.vertexHeightLevels (coverEndpointHeight a b), ?_, ?_⟩
    · intro i
      simpa [coverEndpointHeight] using
        GraphPL.coversVertexHeights_vertexHeightLevels (coverEndpointHeight a b) (i, false)
    · intro i
      simpa [coverEndpointHeight] using
        GraphPL.coversVertexHeights_vertexHeightLevels (coverEndpointHeight a b) (i, true)

/-- Saturated opens agree when a nested nonempty enlargement sees no new cover endpoint. -/
theorem coverSaturation_eq_of_same_endpoints {n : ℕ} (S : CriticalValues n)
    (hS : CoversIntervalEndpoints a b S) {I J : OpenInterval} (hIJ : I ≤ J)
    (hI : (I : Set ℝ).Nonempty) (hlev : ∀ j, S.value j ∈ I ↔ S.value j ∈ J) :
    coverSaturation (fun i => ioo (a i) (b i)) I =
      coverSaturation (fun i => ioo (a i) (b i)) J := by
  apply le_antisymm (coverSaturation_mono _ hIJ)
  intro x hx
  obtain ⟨i, hxi, y, hyU, hyJ⟩ := mem_coverSaturation.mp hx
  obtain ⟨j, hj⟩ := hS.1 i
  obtain ⟨k, hk⟩ := hS.2 i
  have ha : a i ∈ I ↔ a i ∈ J := by simpa [hj] using hlev j
  have hb : b i ∈ I ↔ b i ∈ J := by simpa [hk] using hlev k
  obtain ⟨z, hzU, hzI⟩ := (ioo_inter_nonempty_of_same_endpoints hIJ hI ha hb).mpr
    ⟨y, hyU, hyJ⟩
  exact mem_coverSaturation.mpr ⟨i, hxi, z, hzU, hzI⟩

variable {X : Type u} [TopologicalSpace X]

/-- Finite component values and endpoint bounds prove constructibility of the actual assembly. -/
theorem isConstructibleAt_coverComponents [Finite ι] (f : C(X, ℝ))
    (hfinite : ∀ i, Finite ((intervalComponents f).obj (ioo (a i) (b i))))
    {n : ℕ} (S : CriticalValues n) (hS : CoversIntervalEndpoints a b S) :
    S.IsConstructibleAt (coverComponents f (fun i => ioo (a i) (b i))) where
  finite := finite_coverComponents f _ hfinite
  bijective := by
    intro I J hIJ hI hlev
    have hsat := coverSaturation_eq_of_same_endpoints a b S hS hIJ hI hlev
    let m := homOfLE (coverSaturation_mono (fun i => ioo (a i) (b i)) hIJ)
    let : IsIso m := ⟨⟨homOfLE hsat.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    exact (isIso_iff_bijective ((componentFunctor f).map m)).mp inferInstance
  isEmpty_lowerTail := ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x =>
      obtain ⟨i, _, y, hyU, hyI⟩ := mem_coverSaturation.mp x.property
      obtain ⟨j, hj⟩ := hS.1 i
      have hj0 := S.strictMono.monotone (Fin.zero_le j)
      rw [hj] at hj0
      exact (not_lt_of_ge hj0) (hyU.1.trans (S.mem_lowerTail.mp hyI))⟩
  isEmpty_upperTail := ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x =>
      obtain ⟨i, _, y, hyU, hyI⟩ := mem_coverSaturation.mp x.property
      obtain ⟨j, hj⟩ := hS.2 i
      have hjn := S.strictMono.monotone (Fin.le_last j)
      rw [hj] at hjn
      exact (not_lt_of_ge hjn) ((S.mem_upperTail.mp hyI).trans hyU.2)⟩

/-- The assembled bounded-cover precosheaf is a constructible interval cosheaf. -/
theorem isConstructibleCosheaf_coverComponents [Finite ι] (f : C(X, ℝ))
    (hfinite : ∀ i, Finite ((intervalComponents f).obj (ioo (a i) (b i)))) :
    IsConstructibleCosheaf (coverComponents f (fun i => ioo (a i) (b i))) := by
  obtain ⟨n, S, hS⟩ := exists_coversIntervalEndpoints a b
  exact IsConstructibleCosheaf.of_isConstructibleAt
    (isConstructibleAt_coverComponents a b f hfinite S hS)
    (coverComponents_isIntervalCosheaf f (fun i => ioo (a i) (b i)))

end TDA.Mapper
