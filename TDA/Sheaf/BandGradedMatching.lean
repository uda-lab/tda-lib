import TDA.Sheaf.BandDistanceBiproduct
import TDA.Persistence.BoundaryAugmentedMatching

/-!
# Finite graded matching for real-band convolution

A partial injection acts on occurrence indices. The cost of a pair is the band distance
of its two objects, and each unmatched object contributes its band distance to zero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence
open scoped NNReal ENNReal ZeroObject

namespace TDA.Sheaf.BandConvolution

/-- A partial matching of finite occurrence labels, encoded by an option-valued injection. -/
abbrev GradedMatching (I J : Type) := OccurrenceMatching I J PEmpty.{1} PEmpty.{1}

variable {k : Type} [Ring k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

local notation "D⁺[" k "]" => DerivedCategory.Plus (realLine.Sheaf (ModuleCat k))
local notation "Dᵇ[" k "]" => DerivedCategory.Bounded (realLine.Sheaf (ModuleCat k))
local notation "ι[" k "]" => boundedToPlus (realLine.Sheaf (ModuleCat k))

variable {I J : Type} {X : I → D⁺[k]} {Y : J → D⁺[k]}

namespace GradedMatching

/-- The matching that deletes every occurrence on each side. -/
def empty : GradedMatching I J where
  finite _ := none
  finite_injective _ _ _ h _ := by cases h
  essential := Equiv.refl _

/-- Match all occurrences along a bijection of labels. -/
def ofEquiv (e : I ≃ J) : GradedMatching I J where
  finite i := some (e i)
  finite_injective _ _ _ h h' := e.injective (Option.some.inj (h.trans h'.symm))
  essential := Equiv.refl _

/-- The supremum of paired distances and the distances to zero of unmatched occurrences. -/
def cost (M : GradedMatching I J) (X : I → D⁺[k]) (Y : J → D⁺[k]) : ℝ≥0∞ :=
  (⨆ (i : I) (j : J) (_ : M.finite i = some j), distance (X i) (Y j)) ⊔
  (⨆ (i : I) (_ : M.finite i = none), distance (X i) 0) ⊔
  (⨆ (j : J) (_ : ¬ ∃ i, M.finite i = some j), distance (Y j) 0)

/-- A cost bound consists of one bound for each pair and each unmatched occurrence. -/
theorem cost_le_iff (M : GradedMatching I J) {r : ℝ≥0∞} :
    M.cost X Y ≤ r ↔
      (∀ i j, M.finite i = some j → distance (X i) (Y j) ≤ r) ∧
      (∀ i, M.finite i = none → distance (X i) 0 ≤ r) ∧
      (∀ j, (¬ ∃ i, M.finite i = some j) → distance (Y j) 0 ≤ r) := by
  simp only [cost, sup_le_iff, iSup_le_iff, and_assoc]

/-- A source occurrence whose deletion cost is infinite must be paired at finite cost. -/
theorem exists_partner_of_cost_lt_top (M : GradedMatching I J) (i : I)
    (hi : distance (X i) 0 = ⊤) (h : M.cost X Y < ⊤) :
    ∃ j, M.finite i = some j := by
  cases hf : M.finite i with
  | some j => exact ⟨j, rfl⟩
  | none =>
    exact (h.not_ge (hi ▸ ((M.cost_le_iff.mp le_rfl).2.1 i hf))).elim

/-- A target occurrence whose deletion cost is infinite must be paired at finite cost. -/
theorem exists_source_of_cost_lt_top (M : GradedMatching I J) (j : J)
    (hj : distance (Y j) 0 = ⊤) (h : M.cost X Y < ⊤) :
    ∃ i, M.finite i = some j := by
  by_contra hn
  exact h.not_ge (hj ▸ ((M.cost_le_iff.mp le_rfl).2.2 j hn))

variable [Fintype I] [Fintype J]

private def padded (X : I → D⁺[k]) : I ⊕ J → D⁺[k] :=
  Sum.elim X (fun _ => 0)

private def paddedIso (X : I → D⁺[k]) : (⨁ padded (J := J) X) ≅ ⨁ X where
  hom := biproduct.desc fun z => match z with
    | .inl i => biproduct.ι X i
    | .inr _ => 0
  inv := biproduct.desc fun i => biproduct.ι (padded X) (.inl i)
  hom_inv_id := by
    apply biproduct.hom_ext'
    rintro (i | j)
    · simp only [Category.comp_id, biproduct.ι_desc_assoc]
      exact biproduct.ι_desc _ _
    · exact (isZero_zero _).eq_of_src _ _
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro i
    simp only [Category.comp_id]
    erw [biproduct.ι_desc_assoc, biproduct.ι_desc]

omit [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem padded_rel (M : GradedMatching I J) (R : D⁺[k] → D⁺[k] → Prop)
    (h₀ : R 0 0) (hp : ∀ i j, M.finite i = some j → R (X i) (Y j))
    (hl : ∀ i, M.finite i = none → R (X i) 0)
    (hr : ∀ j, (¬ ∃ i, M.finite i = some j) → R 0 (Y j)) (z : I ⊕ J) :
    R (padded X z) (padded Y (M.toBoundaryAssignment z)) := by
  cases z with
  | inl i =>
    change R (X i) (padded Y (match M.finite i with | some j => .inl j | none => .inr i))
    cases h : M.finite i with
    | some j => exact hp i j h
    | none => exact hl i h
  | inr j =>
    change R 0 (padded Y (match M.reverse.finite j with | some i => .inr i | none => .inl j))
    cases h : M.reverse.finite j with
    | some i => exact h₀
    | none =>
      exact hr j (fun ⟨i, hi⟩ => by
        have e := (M.reverse_finite_some_iff j i).mpr hi
        rw [h] at e
        cases e)

private def paddedTargetIso (M : GradedMatching I J) (Y : J → D⁺[k]) :
    (⨁ fun z => padded Y (M.toBoundaryAssignment z)) ≅ ⨁ Y :=
  biproduct.whiskerEquiv M.toBoundaryAssignment (fun _ => Iso.refl _) ≪≫ paddedIso Y

/-- Pair and deletion witnesses at a common radius give a witness of the sums. -/
theorem nonempty_witness_biproduct (M : GradedMatching I J) {ε : ℝ} (hε : 0 ≤ ε)
    (hp : ∀ i j, M.finite i = some j → Nonempty (Witness k hε (X i) (Y j)))
    (hl : ∀ i, M.finite i = none → Nonempty (Witness k hε (X i) 0))
    (hr : ∀ j, (¬ ∃ i, M.finite i = some j) → Nonempty (Witness k hε (Y j) 0)) :
    Nonempty (Witness k hε (⨁ X) (⨁ Y)) := by
  have w := M.padded_rel (fun A B => Nonempty (Witness k hε A B))
    ⟨(Witness.ofIso (Iso.refl (0 : D⁺[k]))).mono hε⟩ hp hl (fun j hj => ⟨(hr j hj).some.symm⟩)
  exact ⟨(Witness.biproduct fun z => (w z).some).congr (paddedIso X) (M.paddedTargetIso Y)⟩

/-- Every matching of two indexed families bounds the distance between their biproducts. -/
theorem distance_biproduct_le_cost (M : GradedMatching I J) :
    distance (⨁ X) (⨁ Y) ≤ M.cost X Y := by
  let A : I ⊕ J → D⁺[k] := padded X
  let B : I ⊕ J → D⁺[k] := fun z => padded Y (M.toBoundaryAssignment z)
  rw [← distance_congr (paddedIso (J := J) X) (M.paddedTargetIso Y)]
  refine (distance_biproduct_le A B).trans (iSup_le fun z => ?_)
  obtain ⟨hp, hl, hr⟩ := M.cost_le_iff.mp (le_refl (M.cost X Y))
  exact M.padded_rel (fun A B => distance A B ≤ M.cost X Y)
    (by simp) hp hl (fun j hj => (distance_comm 0 (Y j)).le.trans (hr j hj)) z

end GradedMatching

/-- The infimum of partial matching costs for the two families of occurrence objects. -/
def matchingDistance (X : I → D⁺[k]) (Y : J → D⁺[k]) : ℝ≥0∞ :=
  ⨅ M : GradedMatching I J, M.cost X Y

/-- The least matching cost is bounded by the cost of any specified matching. -/
theorem matchingDistance_le_cost (M : GradedMatching I J) :
    matchingDistance X Y ≤ M.cost X Y :=
  iInf_le _ M

variable [Fintype I] [Fintype J]

/-- A finite family of occurrence matchings has a cost minimizer, even at infinite cost. -/
theorem exists_matching_cost_eq (X : I → D⁺[k]) (Y : J → D⁺[k]) :
    ∃ M : GradedMatching I J, M.cost X Y = matchingDistance X Y := by
  classical
  let : Nonempty (GradedMatching I J) := ⟨GradedMatching.empty⟩
  obtain ⟨M, _, hM⟩ := Finset.exists_min_image Finset.univ
    (fun M : GradedMatching I J => M.cost X Y) Finset.univ_nonempty
  exact ⟨M, le_antisymm (le_iInf fun N => hM N (Finset.mem_univ _)) (iInf_le _ M)⟩

/-- The matching distance bounds the band distance of objects presented by their occurrences. -/
theorem distance_le_matchingDistance {F G : D⁺[k]} (e : F ≅ ⨁ X) (f : G ≅ ⨁ Y) :
    distance F G ≤ matchingDistance X Y := by
  rw [distance_congr e f]
  exact le_iInf fun M => M.distance_biproduct_le_cost

/-- The bounded band distance is bounded by matching the included occurrence objects. -/
theorem distanceB_le_matchingDistance {F G : Dᵇ[k]} {A : I → Dᵇ[k]} {B : J → Dᵇ[k]}
    (e : F ≅ ⨁ A) (f : G ≅ ⨁ B) :
    distanceB F G ≤ matchingDistance (ι[k].obj ∘ A) (ι[k].obj ∘ B) :=
  distance_le_matchingDistance (ι[k].mapIso e ≪≫ ι[k].mapBiproduct A)
    (ι[k].mapIso f ≪≫ ι[k].mapBiproduct B)

end TDA.Sheaf.BandConvolution
