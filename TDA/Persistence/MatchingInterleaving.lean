import TDA.Persistence.RealIntervalInterleaving
import TDA.Persistence.DiagramBottleneckLaws

/-!
# Interleavings constructed from finite occurrence matchings

Matched coordinates use normalized interval comparisons. Unmatched finite
coordinates have zero double-shift maps. Essential coordinates use the matching's
total equivalence. Coordinate permutations identify this construction with `realize`.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RealBarcode

open CategoryTheory RealShift
open scoped NNReal ZeroObject Classical ENNReal

variable {k : Type u} [Field k]

/-- One label for every finite or essential occurrence, including repeated values. -/
abbrev Occurrences (D : Diagram ℝ) := D.finiteOccurrences ⊕ D.essentialOccurrences

/-- Endpoints belonging to a finite or essential occurrence. -/
def occurrencePoint (D : Diagram ℝ) : Occurrences D → ℝ × WithTop ℝ
  | .inl p => (p.1.1, (p.1.2 : WithTop ℝ))
  | .inr b => (b.1, ⊤)

private theorem occurrencePoint_multiset (D : Diagram ℝ) :
    (Finset.univ : Finset (Occurrences D)).val.map (occurrencePoint D) = D.points := by
  rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum, Multiset.map_add,
    Multiset.map_map, Multiset.map_map]
  change ((Finset.univ : Finset D.finiteOccurrences).val.map
    (fun p => (p.1.1, (p.1.2 : WithTop ℝ)))) +
      ((Finset.univ : Finset D.essentialOccurrences).val.map (fun b => (b.1, ⊤))) = _
  erw [← Multiset.map_map (fun p : ℝ × ℝ => (p.1, (p.2 : WithTop ℝ))),
    ← Multiset.map_map (fun b : ℝ => (b, (⊤ : WithTop ℝ))),
    Multiset.map_univ_coe, Multiset.map_univ_coe]
  exact parts_reconstruct D.points

/-- The occurrence-indexed coordinate presentation of the existing realization. -/
noncomputable def occurrenceModule (D : Diagram ℝ) : PModule.{u,0,u} k ℝ :=
  familyModule (fun i : Occurrences D => intervalModule (k := k) (occurrencePoint D i))

/-- Every occurrence, including repetitions, is transported to the actual `realize` list. -/
noncomputable def occurrenceIso (D : Diagram ℝ) :
    occurrenceModule (k := k) D ≅ realize D := by
  let xs := D.points.toList
  have hx : (Finset.univ : Finset (Fin xs.length)).val.map (fun i => xs.get i) = D.points := by
    rw [Fin.univ_val_map, List.ofFn_get]
    exact Multiset.coe_toList D.points
  let e := (presentationEquiv (occurrencePoint D) (fun i : Fin xs.length => xs.get i)
    ((occurrencePoint_multiset D).trans hx.symm)).1
  change familyModule (fun i : Occurrences D => intervalModule (k := k) (occurrencePoint D i)) ≅
    familyModule (fun j : Fin xs.length => intervalModule (k := k) (xs.get j))
  apply familyIso e
  intro j
  have h := (presentationEquiv (occurrencePoint D) (fun i : Fin xs.length => xs.get i)
    ((occurrencePoint_multiset D).trans hx.symm)).2 (e.symm j)
  have hp : occurrencePoint D (e.symm j) = xs.get j := by simpa [e] using h.symm
  exact eqToIso (congrArg (intervalModule (k := k)) hp)

private noncomputable def familyLinear {ι κ : Type} (ε : ℝ≥0)
    (F : ι → PModule.{u,0,u} k ℝ) (G : κ → PModule.{u,0,u} k ℝ)
    (τ : κ → Option ι)
    (f : ∀ j i, τ j = some i → (F i ⟶ (shift ε).obj (G j)))
    (t : ℝ) (j : κ) : (∀ i, (F i).obj t) →ₗ[k] (G j).obj (t + (ε : ℝ)) :=
  if h : ∃ i, τ j = some i then
    (((f j h.choose h.choose_spec).app t).hom).comp (LinearMap.proj h.choose) else 0

private theorem familyLinear_some {ι κ : Type} (ε : ℝ≥0)
    (F : ι → PModule.{u,0,u} k ℝ) (G : κ → PModule.{u,0,u} k ℝ)
    (τ : κ → Option ι)
    (f : ∀ j i, τ j = some i → (F i ⟶ (shift ε).obj (G j)))
    (t : ℝ) (j : κ) (i : ι) (hi : τ j = some i) :
    familyLinear ε F G τ f t j = (((f j i hi).app t).hom).comp (LinearMap.proj i) := by
  have h : ∃ i, τ j = some i := ⟨i, hi⟩
  unfold familyLinear
  erw [dif_pos h]
  have heq : h.choose = i := Option.some.inj (h.choose_spec.symm.trans hi)
  subst i
  rfl

private theorem familyLinear_none {ι κ : Type} (ε : ℝ≥0)
    (F : ι → PModule.{u,0,u} k ℝ) (G : κ → PModule.{u,0,u} k ℝ)
    (τ : κ → Option ι)
    (f : ∀ j i, τ j = some i → (F i ⟶ (shift ε).obj (G j)))
    (t : ℝ) (j : κ) (hj : τ j = none) : familyLinear ε F G τ f t j = 0 := by
  have h : ¬ ∃ i, τ j = some i := by simp [hj]
  exact dif_neg h

private noncomputable def familyMap {ι κ : Type} (ε : ℝ≥0)
    (F : ι → PModule.{u,0,u} k ℝ) (G : κ → PModule.{u,0,u} k ℝ)
    (τ : κ → Option ι)
    (f : ∀ j i, τ j = some i → (F i ⟶ (shift ε).obj (G j))) :
    familyModule F ⟶ (shift ε).obj (familyModule G) where
  app t := ModuleCat.ofHom (LinearMap.pi (familyLinear ε F G τ f t))
  naturality {s t} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    change familyLinear ε F G τ f t j (fun i => ((F i).map a).hom (x i)) =
      ((G j).map (homOfLE (add_le_add (leOfHom a) le_rfl))).hom
        (familyLinear ε F G τ f s j x)
    cases hj : τ j with
    | none =>
      erw [familyLinear_none ε F G τ f t j hj, familyLinear_none ε F G τ f s j hj]
      change (0 : (G j).obj (t + (ε : ℝ))) =
        ((G j).map (homOfLE (add_le_add (leOfHom a) le_rfl))).hom 0
      exact (map_zero _).symm
    | some i =>
      erw [familyLinear_some ε F G τ f t j i hj, familyLinear_some ε F G τ f s j i hj]
      exact congrArg (fun m => m.hom (x i)) ((f j i hj).naturality a)

private theorem familyMap_app_some {ι κ : Type} (ε : ℝ≥0)
    (F : ι → PModule.{u,0,u} k ℝ) (G : κ → PModule.{u,0,u} k ℝ)
    (τ : κ → Option ι)
    (f : ∀ j i, τ j = some i → (F i ⟶ (shift ε).obj (G j)))
    (t : ℝ) (x : (familyModule F).obj t) (j : κ) (i : ι) (hi : τ j = some i) :
    ((familyMap ε F G τ f).app t).hom x j = ((f j i hi).app t).hom (x i) := by
  change familyLinear ε F G τ f t j x = _
  erw [familyLinear_some ε F G τ f t j i hi]
  rfl

private theorem familyMap_app_none {ι κ : Type} (ε : ℝ≥0)
    (F : ι → PModule.{u,0,u} k ℝ) (G : κ → PModule.{u,0,u} k ℝ)
    (τ : κ → Option ι)
    (f : ∀ j i, τ j = some i → (F i ⟶ (shift ε).obj (G j)))
    (t : ℝ) (x : (familyModule F).obj t) (j : κ) (hj : τ j = none) :
    ((familyMap ε F G τ f).app t).hom x j = 0 := by
  change familyLinear ε F G τ f t j x = 0
  erw [familyLinear_none ε F G τ f t j hj]
  rfl

-- A partial injection permits at most one coordinate path through either composite.
-- Paired paths use their two interval equations; every unpaired path is zero.
private noncomputable def familyInterleaving {ι κ : Type} (ε : ℝ≥0)
    (F : ι → PModule.{u,0,u} k ℝ) (G : κ → PModule.{u,0,u} k ℝ)
    (σ : ι → Option κ) (τ : κ → Option ι)
    (hinv : ∀ i j, σ i = some j ↔ τ j = some i)
    (pair : ∀ i j, σ i = some j → RealInterleaving ε (F i) (G j))
    (hF : ∀ i, σ i = none → transition (ε + ε) (F i) = 0)
    (hG : ∀ j, τ j = none → transition (ε + ε) (G j) = 0) :
    RealInterleaving ε (familyModule F) (familyModule G) := by
  let f := familyMap ε F G τ (fun j i h => (pair i j ((hinv i j).mpr h)).φ)
  let g := familyMap ε G F σ (fun i j h => (pair i j h).ψ)
  apply RealInterleaving.ofApp f g
  · intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change ((F i).map (eqToHom (show (t + (ε : ℝ)) + (ε : ℝ) =
      t + ((ε + ε : ℝ≥0) : ℝ) by simp [NNReal.coe_add, add_assoc]))).hom
        ((g.app (t + (ε : ℝ))).hom ((f.app t).hom x) i) =
      ((transition (ε + ε) (F i)).app t).hom (x i)
    dsimp only [g]
    cases h : σ i with
    | none =>
      erw [familyMap_app_none ε G F σ _ _ _ i h, map_zero, hF i h]
      rfl
    | some j =>
      erw [familyMap_app_some ε G F σ _ _ _ i j h]
      dsimp only [f]
      erw [familyMap_app_some ε F G τ _ _ _ j i ((hinv i j).mp h)]
      exact congrArg (fun m => m.hom (x i)) ((pair i j h).φ_ψ_app t)
  · intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    change ((G j).map (eqToHom (show (t + (ε : ℝ)) + (ε : ℝ) =
      t + ((ε + ε : ℝ≥0) : ℝ) by simp [NNReal.coe_add, add_assoc]))).hom
        ((f.app (t + (ε : ℝ))).hom ((g.app t).hom x) j) =
      ((transition (ε + ε) (G j)).app t).hom (x j)
    dsimp only [f]
    cases h : τ j with
    | none =>
      erw [familyMap_app_none ε F G τ _ _ _ j h, map_zero, hG j h]
      rfl
    | some i =>
      erw [familyMap_app_some ε F G τ _ _ _ j i h]
      dsimp only [g]
      erw [familyMap_app_some ε G F σ _ _ _ i j ((hinv i j).mpr h)]
      exact congrArg (fun m => m.hom (x j))
        ((pair i j ((hinv i j).mpr h)).ψ_φ_app t)

private def selection {D E : Diagram ℝ}
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) : Occurrences D → Option (Occurrences E)
  | .inl i => (M.finite i).map Sum.inl
  | .inr i => some (.inr (M.essential i))

private theorem selection_reverse {D E : Diagram ℝ}
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) (i : Occurrences D) (j : Occurrences E) :
    selection M i = some j ↔ selection M.reverse j = some i := by
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [selection, OccurrenceMatching.reverse_finite_some_iff]
    | inr j => simp [selection]
  | inr i =>
    cases j with
    | inl j => simp [selection]
    | inr j =>
      change some (Sum.inr (M.essential i) : Occurrences E) = some (.inr j) ↔
        some (Sum.inr (M.essential.symm j) : Occurrences D) = some (.inr i)
      simp only [Option.some.injEq, Sum.inr.injEq]
      exact M.essential.eq_symm_apply.symm.trans eq_comm

private theorem finite_positive {D : Diagram ℝ} (hD : D.IsPositive)
    (i : D.finiteOccurrences) : i.1.1 < i.1.2 := by
  obtain ⟨⟨b, d⟩, hmem, heq⟩ :=
    (Multiset.mem_filterMap _ _).mp (Multiset.coe_mem (x := i))
  cases d with
  | top => simp [finitePart] at heq
  | coe d =>
    simp only [finitePart, Option.some.injEq] at heq
    have h := hD (b, (d : WithTop ℝ)) hmem
    have hi : i.1 = (b, d) := heq.symm
    simpa only [hi, WithTop.coe_lt_coe] using h

private noncomputable def transportInterleaving (ε : ℝ≥0)
    {M N M' N' : PModule.{u,0,u} k ℝ} (i : RealInterleaving ε M N)
    (e : M ≅ M') (d : N ≅ N') : RealInterleaving ε M' N' := by
  have comp {A B A' B' : PModule.{u,0,u} k ℝ}
      (f : A ⟶ (shift ε).obj B) (g : B ⟶ (shift ε).obj A)
      (h : f ≫ (shift ε).map g ≫ (compIso ε ε A).hom = transition (ε + ε) A)
      (a : A ≅ A') (b : B ≅ B') :
      (a.inv ≫ f ≫ (shift ε).map b.hom) ≫
        (shift ε).map (b.inv ≫ g ≫ (shift ε).map a.hom) ≫
          (compIso ε ε A').hom = transition (ε + ε) A' := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, b.hom_inv_id, (shift ε).map_id, Category.id_comp]
    rw [compIso_naturality]
    have hh := congrArg (fun m => a.inv ≫ m ≫ (shift (ε + ε)).map a.hom) h
    simp only [Category.assoc] at hh
    rw [hh]
    rw [← transition_naturality, Iso.inv_hom_id_assoc]
  exact ⟨e.inv ≫ i.φ ≫ (shift ε).map d.hom,
    d.inv ≫ i.ψ ≫ (shift ε).map e.hom,
    comp i.φ i.ψ i.φ_ψ e d, comp i.ψ i.φ i.ψ_φ d e⟩

/-- A finite occurrence matching with cost at most `ε` constructs the actual
interleaving of its two positive diagram realizations. -/
noncomputable def matchingInterleaving (D E : Diagram ℝ) (hD : D.IsPositive)
    (hE : E.IsPositive) (ε : ℝ≥0)
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences)
    (hc : M.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤
      (ε : ℝ≥0∞)) :
    RealInterleaving ε (realize (k := k) D) (realize E) := by
  let F := fun i : Occurrences D => intervalModule (k := k) (occurrencePoint D i)
  let G := fun j : Occurrences E => intervalModule (k := k) (occurrencePoint E j)
  -- Numeric matching costs supply every comparison bound; no coordinate witness is input.
  have pair : ∀ i j, selection M i = some j → RealInterleaving ε (F i) (G j) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hm : M.finite i = some j := by simpa [selection] using hij
        have hr : max |i.1.1 - j.1.1| |i.1.2 - j.1.2| ≤ (ε : ℝ) := by
          apply ENNReal.ofReal_le_coe.mp
          simpa only [hm, finitePairCost] using
            (M.source_le_cost (fun p => p.1) (fun p => p.1)
              (fun b => b.1) (fun b => b.1) i).trans hc
        have hb := abs_le.mp ((le_max_left _ _).trans hr)
        have hd := abs_le.mp ((le_max_right _ _).trans hr)
        exact interleavingOfBounds ε _ _ (by dsimp [occurrencePoint]; linarith [hb.1])
          (by dsimp [occurrencePoint]; linarith [hb.2])
          (by simpa only [occurrencePoint, ← WithTop.coe_add, WithTop.coe_le_coe] using
            (show j.1.2 ≤ i.1.2 + (ε : ℝ) by linarith [hd.1]))
          (by simpa only [occurrencePoint, ← WithTop.coe_add, WithTop.coe_le_coe] using
            (show i.1.2 ≤ j.1.2 + (ε : ℝ) by linarith [hd.2]))
      | inr j =>
        simp [selection] at hij
    | inr i =>
      cases j with
      | inl j => simp [selection] at hij
      | inr j =>
        have hm : M.essential i = j := by simpa [selection] using hij
        have hr : |i.1 - j.1| ≤ (ε : ℝ) := by
          apply ENNReal.ofReal_le_coe.mp
          simpa only [hm, essentialPairCost] using
            (M.essential_le_cost (fun p => p.1) (fun p => p.1)
              (fun b => b.1) (fun b => b.1) i).trans hc
        have hb := abs_le.mp hr
        exact interleavingOfBounds ε _ _ (by dsimp [occurrencePoint]; linarith [hb.1])
          (by dsimp [occurrencePoint]; linarith [hb.2]) (by simp [occurrencePoint])
          (by simp [occurrencePoint])
  -- Apply the same argument to the reverse matching for unmatched target coordinates.
  have unmatched (A B : Diagram ℝ) (hA : A.IsPositive)
      (N : OccurrenceMatching A.finiteOccurrences B.finiteOccurrences
        A.essentialOccurrences B.essentialOccurrences)
      (hN : N.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤
        (ε : ℝ≥0∞)) (i : Occurrences A) (hi : selection N i = none) :
      transition (ε + ε) (intervalModule (k := k) (occurrencePoint A i)) = 0 := by
    cases i with
    | inl i =>
      have hm : N.finite i = none := by simpa [selection] using hi
      have hr : |i.1.2 - i.1.1| / 2 ≤ (ε : ℝ) := by
        apply ENNReal.ofReal_le_coe.mp
        simpa only [hm, diagonalCost] using
          (N.source_le_cost (fun p => p.1) (fun p => p.1)
            (fun b => b.1) (fun b => b.1) i).trans hN
      rw [abs_of_pos (sub_pos.mpr (finite_positive hA i))] at hr
      exact (transition_eq_zero_iff ε i.1.1 i.1.2).mpr (by linarith)
    | inr i => simp [selection] at hi
  let w := familyInterleaving ε F G (selection M) (selection M.reverse)
    (selection_reverse M) pair (unmatched D E hD M hc)
    (unmatched E D hE M.reverse (by
      simpa only [OccurrenceMatching.cost_reverse] using hc))
  exact transportInterleaving ε w (occurrenceIso D) (occurrenceIso E)

end TDA.Persistence.RealBarcode
