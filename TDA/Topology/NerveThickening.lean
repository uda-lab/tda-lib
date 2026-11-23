import TDA.Topology.Nerve
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Small open thickenings of compact nerves

A finite family of compact sets retains its ordinary labelled nerve under small positive
open thickenings. For nested compact convex families with the same union a single radius
bound works for both families, and their offsets cover the thickening of that union.
-/

namespace TDA.Topology

open Set Metric

section Metric

variable {X I : Type*} [MetricSpace X]

/-- A nonempty set of labels without a common point still has no common point after
a sufficiently small open thickening. -/
private theorem exists_radius_for_nonface (C : CoverFamily X I) (s : Finset I)
    (hs : s.Nonempty) (hcompact : ∀ i, IsCompact (C i))
    (hn : ¬ ∃ x, ∀ i ∈ s, x ∈ C i) :
    ∃ δ : ℝ, 0 < δ ∧ ¬ ∃ x, ∀ i ∈ s, x ∈ thickening δ (C i) := by
  obtain ⟨j, hj⟩ := hs
  -- The closed thickenings shrink to the original closed sets.
  let R := {r : ℝ // 0 < r}
  let : Nonempty R := ⟨⟨1, zero_lt_one⟩⟩
  let K (r : R) : Set X := ⋂ i ∈ s, cthickening (r : ℝ) (C i)
  have hK_closed (r : R) : IsClosed (K r) :=
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_cthickening
  have hK_mono {r t : R} (hrt : (r : ℝ) ≤ t) : K r ⊆ K t := by
    exact iInter₂_mono fun i _ => cthickening_mono hrt (C i)
  have hK_dir : Directed (· ⊇ ·) K := by
    intro r t
    let a : R := ⟨min (r : ℝ) t, lt_min r.property t.property⟩
    exact ⟨a, hK_mono (min_le_left _ _), hK_mono (min_le_right _ _)⟩
  have hK_disj : Disjoint (C j) (⋂ r, K r) := by
    refine Set.disjoint_left.2 ?_
    intro x _ hx
    apply hn
    refine ⟨x, fun i hi => ?_⟩
    rw [← (hcompact i).isClosed.closure_eq, closure_eq_iInter_cthickening]
    exact mem_iInter.2 fun r => mem_iInter.2 fun hr =>
      mem_iInter₂.1 (mem_iInter.1 hx ⟨r, hr⟩) i hi
  obtain ⟨r, hr⟩ :=
    (hcompact j).elim_directed_family_closed K hK_closed hK_disj hK_dir
  -- A common point of the open thickenings would give a point of the compact anchor
  -- within distance r of every member.
  refine ⟨(r : ℝ) / 2, half_pos r.property, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 (hx j hj)
  refine Set.disjoint_left.1 hr hy (mem_iInter₂.2 fun i hi => ?_)
  obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 (hx i hi)
  apply mem_cthickening_of_dist_le y z _ _ hz
  calc
    dist y z ≤ dist x y + dist x z := dist_triangle_left _ _ _
    _ ≤ (r : ℝ) := by simpa only [add_halves] using (add_lt_add hxy hxz).le

/-- A finite compact family has a positive radius bound up to which its open
thickenings have exactly the same labelled nerve. -/
theorem exists_pos_nerve_thickening_eq [Finite I] (C : CoverFamily X I)
    (hC : ∀ i, IsCompact (C i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      nerve (fun i => thickening ε (C i)) = nerve C := by
  classical
  let := Fintype.ofFinite I
  have bound (s : Finset I) : ∃ r : ℝ, 0 < r ∧
      (s.Nonempty → (¬ ∃ x, ∀ i ∈ s, x ∈ C i) →
        ¬ ∃ x, ∀ i ∈ s, x ∈ thickening r (C i)) := by
    by_cases h : s.Nonempty ∧ ¬ ∃ x, ∀ i ∈ s, x ∈ C i
    · obtain ⟨r, hr, hn⟩ := exists_radius_for_nonface C s h.1 hC h.2
      exact ⟨r, hr, fun _ _ => hn⟩
    · exact ⟨1, zero_lt_one, fun hsn hn => (h ⟨hsn, hn⟩).elim⟩
  choose r hr hn using bound
  -- Including the empty candidate makes the minimum available even for an empty index type.
  let F : Finset (Finset I) := Finset.univ
  have hF : F.Nonempty := ⟨∅, Finset.mem_univ _⟩
  let δ := F.inf' hF r
  refine ⟨δ, (Finset.lt_inf'_iff _).2 fun s _ => hr s, ?_⟩
  intro ε hε hεδ
  refine le_antisymm ?_ (nerve_mono fun _ => self_subset_thickening hε _)
  intro s hs
  obtain ⟨hsn, x, hx⟩ := (mem_nerve_iff _ _).1 hs
  apply (mem_nerve_iff _ _).2
  refine ⟨hsn, ?_⟩
  by_contra hn'
  apply hn s hsn hn'
  have hδs : δ ≤ r s := Finset.inf'_le _ (Finset.mem_univ s)
  exact ⟨x, fun i hi => thickening_mono (hεδ.trans hδs) _ (hx i hi)⟩

end Metric

section Normed

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]

/-- For nested finite labelled compact convex families with the same union, one positive
radius bound preserves both labelled nerves. At every positive radius up to that bound
the open convex offsets are still nested and cover the same thickening of the union. -/
theorem exists_pos_common_convex_thickening (C D : CoverFamily E I)
    (hC : ∀ i, IsCompact (C i)) (hD : ∀ i, IsCompact (D i))
    (hcC : ∀ i, Convex ℝ (C i)) (hcD : ∀ i, Convex ℝ (D i))
    (hCD : ∀ i, C i ⊆ D i) (hU : (⋃ i, C i) = ⋃ i, D i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      nerve (fun i => thickening ε (C i)) = nerve C ∧
      nerve (fun i => thickening ε (D i)) = nerve D ∧
      (⋃ i, thickening ε (C i)) = thickening ε (⋃ i, C i) ∧
      (⋃ i, thickening ε (D i)) = thickening ε (⋃ i, C i) ∧
      (∀ i, thickening ε (C i) ⊆ thickening ε (D i)) ∧
      (∀ i, IsOpen (thickening ε (C i)) ∧ Convex ℝ (thickening ε (C i))) ∧
      (∀ i, IsOpen (thickening ε (D i)) ∧ Convex ℝ (thickening ε (D i))) := by
  obtain ⟨r, hr, h₁⟩ := exists_pos_nerve_thickening_eq C hC
  obtain ⟨s, hs, h₂⟩ := exists_pos_nerve_thickening_eq D hD
  refine ⟨min r s, lt_min hr hs, fun ε hε hεrs => ?_⟩
  refine ⟨h₁ ε hε (hεrs.trans (min_le_left _ _)), h₂ ε hε (hεrs.trans (min_le_right _ _)),
    (thickening_iUnion ε C).symm, ?_, fun i => thickening_subset_of_subset ε (hCD i),
    fun i => ⟨isOpen_thickening, (hcC i).thickening ε⟩,
    fun i => ⟨isOpen_thickening, (hcD i).thickening ε⟩⟩
  rw [hU, thickening_iUnion]

end Normed

end TDA.Topology
