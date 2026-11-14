import TDA.Topology.QuotientProduct

/-!
# Quotient-map product fixtures

Fixtures for `TDA.Topology.QuotientProduct`.

* A non-Hausdorff quotient. The sign map `ℝ → Prop`, `x ↦ 0 < x`, onto the Sierpiński space is a
  quotient map (`isQuotientMap_posMap`) from a noncompact space onto a non-Hausdorff space
  (`not_t2Space_Prop`). Its product with `[0, 1]` is again a quotient map
  (`isQuotientMap_posMap_prodMap_Icc`), although the target `Prop × [0, 1]` is not Hausdorff
  (`not_t2Space_Prop_prod_Icc`), so no compact-to-Hausdorff argument applies.
* A collapsing scalar map. `triangleMap (s, u) = (s u, u)` maps the square `[0, 1]²` onto the
  triangle `0 ≤ x ≤ u ≤ 1`, collapsing the edge `u = 0` to a corner (`triangleMap_collapse`).
  After product with the identity of an arbitrary space it remains a quotient map
  (`isQuotientMap_prodMap_triangleMap`), for instance with the non-Hausdorff factor `Prop`.
-/

open Set Topology Filter

namespace TDA.Topology.Examples

noncomputable section

/-! ### A non-Hausdorff quotient times an interval -/

/-- The Sierpiński space is not Hausdorff: every neighbourhood of `False` contains `True`. -/
theorem not_t2Space_Prop : ¬ T2Space Prop := fun _ => by
  have h := disjoint_nhds_nhds.2 (show False ≠ True from fun h => of_eq_true h)
  rw [nhds_false, top_disjoint] at h
  exact (nhds_neBot (x := True)).ne h

/-- The sign map `x ↦ 0 < x` onto the Sierpiński space. -/
def posMap (x : ℝ) : Prop := 0 < x

theorem continuous_posMap : Continuous posMap := continuous_Prop.2 isOpen_Ioi

/-- The sign map is a quotient map onto the Sierpiński space. -/
theorem isQuotientMap_posMap : IsQuotientMap posMap := by
  have hsurj : Function.Surjective posMap := fun p => by
    by_cases hp : p
    · exact ⟨1, propext ⟨fun _ => hp, fun _ => one_pos⟩⟩
    · exact ⟨0, propext ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h hp⟩⟩
  refine (isQuotientMap_iff _).2 ⟨.of_isOpen_preimage_iff_isOpen fun s => ⟨fun hs => ?_,
    fun hs => hs.preimage continuous_posMap⟩, hsurj⟩
  rw [isOpen_iff_mem_nhds]
  intro p hp
  by_cases hpt : p
  · rw [eq_true hpt] at hp ⊢
    rw [nhds_true]
    exact mem_pure.2 hp
  · -- `p = False`, whose only neighbourhood is the whole space.
    have hp0 : posMap 0 ∈ s := by
      rw [show posMap 0 = p from propext ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h hpt⟩]
      exact hp
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hs 0 hp0
    have hδ2 : posMap (δ / 2) ∈ s := hball (show δ / 2 ∈ Metric.ball (0 : ℝ) δ by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ)
    have hT : True ∈ s := by
      rw [← eq_true (show posMap (δ / 2) from half_pos hδ)]
      exact hδ2
    have huniv : s = univ := eq_univ_of_forall fun r => by
      by_cases hr : r
      · rw [eq_true hr]
        exact hT
      · rw [show r = p from propext ⟨fun h => absurd h hr, fun h => absurd h hpt⟩]
        exact hp
    rw [huniv]
    exact univ_mem

/-- The product of the sign quotient with `[0, 1]` is a quotient map onto a non-Hausdorff
space. -/
theorem isQuotientMap_posMap_prodMap_Icc :
    IsQuotientMap (Prod.map posMap (id : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)) :=
  isQuotientMap_prodMap_id_Icc isQuotientMap_posMap 0 1

/-- The target of `isQuotientMap_posMap_prodMap_Icc` is not Hausdorff. -/
theorem not_t2Space_Prop_prod_Icc : ¬ T2Space (Prop × Icc (0 : ℝ) 1) := fun _ =>
  not_t2Space_Prop (isEmbedding_prodMkLeft (⟨0, left_mem_Icc.2 zero_le_one⟩ : Icc (0 : ℝ) 1)
    |>.t2Space)

/-! ### A collapsing scalar map times an arbitrary space -/

/-- The triangle `{(x, u) | 0 ≤ x ≤ u ≤ 1}`. -/
def triangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}

/-- The square `[0, 1]²` onto the triangle, `(s, u) ↦ (s u, u)`; it collapses the edge `u = 0`. -/
def triangleMap (p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) : triangle :=
  ⟨((p.1 : ℝ) * p.2, p.2), mul_nonneg p.1.2.1 p.2.2.1,
    mul_le_of_le_one_left p.2.2.1 p.1.2.2, p.2.2.2⟩

theorem continuous_triangleMap : Continuous triangleMap :=
  (((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem triangleMap_surjective : Function.Surjective triangleMap := by
  rintro ⟨⟨x, u⟩, hx, hxu, hu⟩
  have hu0 : 0 ≤ u := hx.trans hxu
  refine ⟨(⟨x / u, div_nonneg hx hu0, div_le_one_of_le₀ hxu hu0⟩, ⟨u, hu0, hu⟩), ?_⟩
  apply Subtype.ext
  simp only [triangleMap, Prod.mk.injEq, and_true]
  rcases eq_or_lt_of_le hu0 with h | h
  · subst h
    simpa using (le_antisymm hxu hx).symm
  · exact div_mul_cancel₀ x h.ne'

/-- The bottom edge collapses to the corner `(0, 0)`: the map is not injective. -/
theorem triangleMap_collapse :
    triangleMap (⟨0, left_mem_Icc.2 zero_le_one⟩, ⟨0, left_mem_Icc.2 zero_le_one⟩) =
      triangleMap (⟨1, right_mem_Icc.2 zero_le_one⟩, ⟨0, left_mem_Icc.2 zero_le_one⟩) :=
  Subtype.ext (by simp [triangleMap])

/-- After product with the identity of any space, the collapsing map is still a quotient map. -/
theorem isQuotientMap_prodMap_triangleMap (E : Type*) [TopologicalSpace E] :
    IsQuotientMap (Prod.map (id : E → E) triangleMap) :=
  isQuotientMap_prodMap_id_of_compactSpace continuous_triangleMap triangleMap_surjective

/-- In particular with the non-Hausdorff factor `Prop`. -/
example : IsQuotientMap (Prod.map (id : Prop → Prop) triangleMap) :=
  isQuotientMap_prodMap_triangleMap Prop

end

end TDA.Topology.Examples
