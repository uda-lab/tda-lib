import TDA.Filtration.RationalAlpha.Geometry
import TDA.Filtration.FilterFunctionMap
import TDA.Simplicial.FiniteComplex
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

/-!
# An exact finite planar alpha filtration

For distinct rational sites, the finite carrier stores each feasible nonempty face
once. A successful lookup supplies its squared entry grade and a rational center
whose full nearest-site tie contains the face.
-/

namespace TDA.Filtration.RationalAlpha

open TDA.Simplicial

variable {n : ℕ} (p : Fin n ↪ Point) {s : Finset (Fin n)} {r : Record n}

private theorem dist_sq_cast_site (c : Point) (v : Fin n) :
    dist (castPoint c) (realSites p v)^2 = (sqDist c (p v) : ℝ) :=
  distSq_cast c (p v)

/-- The returned center lies in every closed cell of the face. Its squared
distance to each of those sites is the reported grade. -/
theorem entry_witness (h : entry? p s = some r) :
    castPoint r.center ∈ Alpha.commonCells (realSites p) s ∧
      ∀ v ∈ s, dist (castPoint r.center) (realSites p v)^2 = (r.grade : ℝ) := by
  obtain ⟨_, hr, ht, _⟩ := lookup_spec h
  obtain ⟨hlow, htie⟩ := record_spec hr
  have he (v) (hv : v ∈ s) := (htie v).1 (ht hv)
  constructor
  · intro v hv j
    apply (sq_le_sq₀ dist_nonneg dist_nonneg).1
    rw [dist_sq_cast_site, dist_sq_cast_site, he v hv]
    exact_mod_cast hlow.2 (Set.mem_range_self j)
  · intro v hv
    rw [dist_sq_cast_site, he v hv]

private theorem least_record (hs : s ∈ Alpha.carrier (realSites p)) {v : Fin n} (hv : v ∈ s) :
    ∃ a ∈ records p, s ⊆ a.ties ∧
      (a.grade : ℝ) = (Alpha.filter (realSites p)).value ⟨s, hs⟩ := by
  have least := Alpha.isLeast_sq_dist (realSites p) ⟨s, hs⟩ hv
  obtain ⟨x, hx, hgrade⟩ := least.1
  obtain ⟨c, hc, rfl⟩ := minimizer_mem_centers p hv x hx (fun y hy =>
    hgrade.trans_le (least.2 ⟨y, hy, rfl⟩))
  obtain ⟨a, ha, hcenter, hq⟩ := exists_record hc v (by
    intro j
    have h := (sq_le_sq₀ dist_nonneg dist_nonneg).2 (hx v hv j)
    simp only [dist_sq_cast_site] at h
    exact_mod_cast h)
  refine ⟨a, ha, fun j hj => (record_spec ha).2 j |>.2 ?_, ?_⟩
  · rw [hcenter, hq]
    have h := congrArg (fun z : ℝ => z^2)
      (Alpha.dist_eq_of_mem_commonCells (realSites p) hj hv hx)
    simpa only [dist_sq_cast_site, Rat.cast_inj] using h
  · simpa only [hq, dist_sq_cast_site] using hgrade

/-- A successful record exists exactly on the feasible nonempty faces. -/
theorem exists_entry_iff : (∃ r, entry? p s = some r) ↔ s ∈ Alpha.carrier (realSites p) := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨(lookup_spec hr).1, castPoint r.center, (entry_witness p hr).1⟩
  · intro hs
    obtain ⟨v, hv⟩ := (Alpha.carrier (realSites p)).isRelLowerSet_faces hs |>.1
    obtain ⟨a, ha, ht, _⟩ := least_record p hs hv
    exact exists_lookup ⟨v, hv⟩ ha ht

theorem entry_none_iff : entry? p s = none ↔ s ∉ Alpha.carrier (realSites p) := by
  rw [← exists_entry_iff p]
  cases entry? p s <;> simp

/-- The minimum over the rational records equals the attained real Alpha value. -/
theorem cast_grade (hs : s ∈ Alpha.carrier (realSites p)) (hr : entry? p s = some r) :
    (r.grade : ℝ) = (Alpha.filter (realSites p)).value ⟨s, hs⟩ := by
  obtain ⟨⟨v, hv⟩, _, _, hle⟩ := lookup_spec hr
  obtain ⟨a, ha, ht, hgrade⟩ := least_record p hs hv
  obtain ⟨hx, he⟩ := entry_witness p hr
  apply le_antisymm
  · rw [← hgrade]
    exact_mod_cast hle a ha ht
  · exact (Alpha.isLeast_sq_dist (realSites p) ⟨s, hs⟩ hv).2 ⟨_, hx, he v hv⟩

/-- A lookup decides membership at any real squared-radius threshold. -/
theorem mem_complex_iff (t : ℝ) : s ∈ Alpha.complex (realSites p) t ↔
    ∃ r, entry? p s = some r ∧ (r.grade : ℝ) ≤ t := by
  constructor
  · intro h
    have hs := (Alpha.exists_mem_complex_iff (realSites p) s).1 ⟨t, h⟩
    obtain ⟨r, hr⟩ := (exists_entry_iff p).2 hs
    exact ⟨r, hr, (cast_grade p hs hr).trans_le ((Alpha.isLeast_grade _ _).2 h)⟩
  · rintro ⟨r, hr, ht⟩
    obtain ⟨v, hv⟩ := (lookup_spec hr).1
    obtain ⟨hx, he⟩ := entry_witness p hr
    exact (Alpha.mem_complex_iff _ hv t).2 ⟨_, hx, (he v hv).trans_le ht⟩

/-- Enumerate the full finite carrier, using the same records for every face. -/
def faces (p : Fin n → Point) : Finset (Finset (Fin n)) :=
  let rows := records p
  Finset.univ.powerset.filter fun s => (lookup rows s).isSome

theorem mem_faces_iff (p : Fin n → Point) :
    s ∈ faces p ↔ ∃ r, entry? p s = some r := by
  simp [faces, entry?, Option.isSome_iff_exists]

@[simp] theorem entry_empty (p : Fin n → Point) : entry? p ∅ = none := by
  simp [entry?, lookup]

theorem faces_zero (p : Fin 0 → Point) : faces p = ∅ := by
  ext s
  have he : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun v => v.elim0)
  simp [he, mem_faces_iff]

/-- The finite nonempty closed-cell nerve on the given labels. -/
def finiteComplex : FiniteComplex n where
  faces := faces p
  nonempty s hs := (lookup_spec ((mem_faces_iff _).1 hs).choose_spec).1
  downClosed := by
    intro s t hs ht hts
    obtain ⟨r, hr⟩ := (mem_faces_iff _).1 hs
    obtain ⟨_, hmem, htie, _⟩ := lookup_spec hr
    exact (mem_faces_iff _).2 (exists_lookup ht hmem (hts.trans htie))

theorem carrier_eq : (finiteComplex p).toPre = Alpha.carrier (realSites p) := by
  ext s
  exact (mem_faces_iff p).trans (exists_entry_iff p)

private theorem entry_isSome (s : TotalFace (finiteComplex p).toPre) : (entry? p s.val).isSome :=
  Option.isSome_iff_exists.mpr ((mem_faces_iff p).mp s.property)

/-- The rational squared grade of each emitted face. -/
def filter : FilterFunction (finiteComplex p).toPre ℚ where
  value s := ((entry? p s.val).get (entry_isSome p s)).grade
  mono := by
    intro a b hab
    have ha := lookup_spec (Option.some_get (entry_isSome p a)).symm
    have hb := lookup_spec (Option.some_get (entry_isSome p b)).symm
    exact ha.2.2.2 _ hb.2.1 (hab.trans hb.2.2.1)

theorem filter_value (s : TotalFace (finiteComplex p).toPre) {r : Record n}
    (h : entry? p s.val = some r) : (filter p).value s = r.grade := by
  change ((entry? p s.val).get _).grade = r.grade
  simp [h]

/-- The full face/grade table, with one row per emitted face. -/
def gradedFaces : Finset (Finset (Fin n) × ℚ) :=
  let rows := records p
  Finset.univ.powerset.biUnion fun s =>
    ((lookup rows s).map fun r => (s, r.grade)).toFinset

theorem mem_gradedFaces_iff (q : ℚ) : (s, q) ∈ gradedFaces p ↔
    ∃ r, entry? p s = some r ∧ r.grade = q := by
  simp [gradedFaces, Option.mem_def, Option.map_eq_some_iff, entry?]

theorem sublevel_eq_complex (t : ℝ) :
    ((filter p).map Rat.castOrderEmbedding).sublevel t = Alpha.complex (realSites p) t := by
  ext s
  change s ∈ ((filter p).map Rat.castOrderEmbedding).sublevel t ↔ s ∈ Alpha.complex _ t
  rw [FilterFunction.mem_sublevel_iff, mem_complex_iff]
  constructor
  · rintro ⟨hs, h⟩
    obtain ⟨r, hr⟩ := (mem_faces_iff p).1 hs
    refine ⟨r, hr, ?_⟩
    change ((filter p).value ⟨s, hs⟩ : ℝ) ≤ t at h
    rwa [filter_value p _ hr] at h
  · rintro ⟨r, hr, h⟩
    refine ⟨(mem_faces_iff p).2 ⟨r, hr⟩, ?_⟩
    change ((filter p).value _ : ℝ) ≤ t
    rwa [filter_value p _ hr]

end TDA.Filtration.RationalAlpha
