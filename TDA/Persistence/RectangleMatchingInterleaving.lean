import TDA.Persistence.RectangleMatching
import TDA.Persistence.DiagramBottleneckLaws

/-!
# Finite rectangle interleavings assembled from occurrence matchings

Finite biproduct maps are reconstructed from their component matrices.
For a partial occurrence matching, each row and column has at most one paired
path. Its two interleaving equations supply the paired diagonal entries;
the zero interleavings of the unmatched modules supply the remaining entries.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits CoordinateShift
open scoped TDA.Persistence NNReal Classical ZeroObject

variable {k : Type u} [Field k] {n : ℕ}

private instance (ε : ℝ≥0) :
    (shift (R := k) (n := n) ε).Additive where
  map_add := by intros; rfl

namespace RectangleFamily

/-- The map with the prescribed finite matrix of shifted occurrence maps. -/
noncomputable def mapOfComponents {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (f : ∀ i j, (R i).module (k := k) ⟶ (shift ε).obj (S j).module) :
    module (k := k) R ⟶ (shift ε).obj (module S) :=
  ∑ i, ∑ j, projection R i ≫ f i j ≫ (shift ε).map (inclusion S j)

/-- Reading a component of the assembled matrix returns the supplied map. -/
theorem component_mapOfComponents {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (f : ∀ i j, (R i).module (k := k) ⟶ (shift ε).obj (S j).module)
    (i : ι) (j : κ) :
    component R S ε (mapOfComponents R S ε f) i j = f i j := by
  classical
  simp only [component, mapOfComponents, Preadditive.comp_sum, Preadditive.sum_comp]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp only [← Category.assoc, inclusion_projection_self, Category.id_comp]
      simp only [Category.assoc, ← Functor.map_comp, inclusion_projection_self]
      simp
    · intro b _ hbj
      simp only [← Category.assoc, inclusion_projection_self, Category.id_comp]
      simp only [Category.assoc, ← Functor.map_comp, inclusion_projection_ne S hbj,
        Functor.map_zero, comp_zero]
    · simp
  · intro a _ hai
    simp only [← Category.assoc, inclusion_projection_ne R hai.symm,
      zero_comp, Finset.sum_const_zero]
  · simp

/-- The occurrence matrix determines the original family map. -/
theorem mapOfComponents_component {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (f : module (k := k) R ⟶ (shift ε).obj (module S)) :
    mapOfComponents R S ε (component R S ε f) = f := by
  classical
  calc
    _ = ∑ i, (projection R i ≫ inclusion R i ≫ f) ≫
        (shift ε).map (∑ j, projection S j ≫ inclusion S j) := by
      simp only [mapOfComponents, component, Functor.map_sum, Functor.map_comp,
        Preadditive.comp_sum, Category.assoc]
    _ = f := by
      simp only [sum_projection_inclusion, ← Category.assoc,
        ← Preadditive.sum_comp, Category.id_comp]
      simp

/-- Equality of every shifted occurrence component implies equality of maps. -/
theorem component_ext {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    {f g : module (k := k) R ⟶ (shift ε).obj (module S)}
    (h : ∀ i j, component R S ε f i j = component R S ε g i j) : f = g := by
  rw [← mapOfComponents_component R S ε f, ← mapOfComponents_component R S ε g]
  congr 1
  funext i j
  exact h i j

/-- A family composite expands into the finite sum of its shifted component paths. -/
theorem component_composite_shift {ι κ ν : Type}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (T : ν → Rectangle n) (ε : ℝ≥0)
    (f : module (k := k) R ⟶ (shift ε).obj (module S))
    (g : module (k := k) S ⟶ (shift ε).obj (module T)) (i : ι) (l : ν) :
    (∑ j, component R S ε f i j ≫ (shift ε).map (component S T ε g j l)) ≫
        (compIso ε ε ((T l).module (k := k))).hom =
      component R T (ε + ε) (f ≫ (shift ε).map g ≫ (compIso ε ε (module T)).hom) i l := by
  rw [component_composite]
  simp only [component, Category.assoc]
  rw [compIso_naturality ε ε (projection (k := k) T l)]

/-- The diagonal transition component is the original rectangle transition. -/
theorem component_transition_self {ι : Type} [Fintype ι]
    (R : ι → Rectangle n) (ε : ℝ≥0) (i : ι) :
    component R R ε (transition ε (module (k := k) R)) i i =
      transition ε ((R i).module (k := k)) := by
  simp only [component, ← Category.assoc]
  rw [transition_naturality ε (inclusion (k := k) R i)]
  simp only [Category.assoc, ← Functor.map_comp, inclusion_projection_self]
  simp

/-- Different occurrence indices have zero transition components. -/
theorem component_transition_ne {ι : Type} [Fintype ι]
    (R : ι → Rectangle n) (ε : ℝ≥0) {i l : ι} (h : i ≠ l) :
    component R R ε (transition ε (module (k := k) R)) i l = 0 := by
  simp only [component, ← Category.assoc]
  rw [transition_naturality ε (inclusion (k := k) R i)]
  simp only [Category.assoc, ← Functor.map_comp, inclusion_projection_ne R h,
    Functor.map_zero, comp_zero]

end RectangleFamily

namespace RectangleMatching

open RectangleFamily

private noncomputable def entry {ι κ : Type} (R : ι → Rectangle n)
    (S : κ → Rectangle n) (ε : ℝ≥0) (σ : ι → Option κ)
    (f : ∀ i j, σ i = some j → ((R i).module (k := k) ⟶ (shift ε).obj (S j).module))
    (i : ι) (j : κ) : (R i).module (k := k) ⟶ (shift ε).obj (S j).module :=
  if h : σ i = some j then f i j h else 0

private theorem entry_some {ι κ : Type} (R : ι → Rectangle n)
    (S : κ → Rectangle n) (ε : ℝ≥0) (σ : ι → Option κ)
    (f : ∀ i j, σ i = some j → ((R i).module (k := k) ⟶ (shift ε).obj (S j).module))
    (i : ι) (j : κ) (h : σ i = some j) : entry R S ε σ f i j = f i j h := by
  simp [entry, h]

-- Each composite path is forced by the two inverse partial selections.
-- The hypotheses concern individual summands, never the desired family equation.
private theorem selection_composite {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (σ : ι → Option κ) (τ : κ → Option ι)
    (hinv : ∀ i j, σ i = some j ↔ τ j = some i)
    (f : ∀ i j, σ i = some j → ((R i).module (k := k) ⟶ (shift ε).obj (S j).module))
    (g : ∀ j i, τ j = some i → ((S j).module (k := k) ⟶ (shift ε).obj (R i).module))
    (hpair : ∀ i j (h : σ i = some j), f i j h ≫ (shift ε).map (g j i ((hinv i j).mp h)) ≫
      (compIso ε ε ((R i).module (k := k))).hom = transition (ε + ε) ((R i).module (k := k)))
    (hzero : ∀ i, σ i = none → transition (ε + ε) ((R i).module (k := k)) = 0)
    (i l : ι) :
    (∑ j, entry R S ε σ f i j ≫ (shift ε).map (entry S R ε τ g j l)) ≫
        (compIso ε ε ((R l).module (k := k))).hom =
      component R R (ε + ε) (transition (ε + ε) (module (k := k) R)) i l := by
  classical
  cases hi : σ i with
  | none =>
    have he (j : κ) : entry R S ε σ f i j = 0 := by simp [entry, hi]
    simp only [he, zero_comp, Finset.sum_const_zero]
    by_cases hil : i = l
    · subst l
      rw [component_transition_self, hzero i hi]
    · exact (component_transition_ne R (ε + ε) hil).symm
  | some j =>
    rw [Finset.sum_eq_single j]
    · rw [entry_some R S ε σ f i j hi]
      have hj : τ j = some i := (hinv i j).mp hi
      by_cases hil : i = l
      · subst l
        rw [entry_some S R ε τ g j i hj, component_transition_self]
        exact hpair i j hi
      · have hne : ¬ τ j = some l := by simp [hj, hil]
        rw [show entry S R ε τ g j l = 0 from dif_neg hne,
          Functor.map_zero, comp_zero, zero_comp, component_transition_ne R (ε + ε) hil]
    · intro b _ hbj
      have hne : ¬ σ i = some b := by simp [hi, hbj.symm]
      simp only [entry, dif_neg hne, zero_comp]
    · simp

private noncomputable def selectedInterleaving {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (σ : ι → Option κ) (τ : κ → Option ι)
    (hinv : ∀ i j, σ i = some j ↔ τ j = some i)
    (pair : ∀ i j, σ i = some j →
      CoordinateInterleaving ε ((R i).module (k := k)) (S j).module)
    (hR : ∀ i, σ i = none → transition (ε + ε) ((R i).module (k := k)) = 0)
    (hS : ∀ j, τ j = none → transition (ε + ε) ((S j).module (k := k)) = 0) :
    CoordinateInterleaving ε (module (k := k) R) (module S) := by
  let f := fun i j h => (pair i j h).φ
  let g := fun j i h => (pair i j ((hinv i j).mpr h)).ψ
  let F := mapOfComponents R S ε (entry R S ε σ f)
  let G := mapOfComponents S R ε (entry S R ε τ g)
  refine ⟨F, G, ?_, ?_⟩
  · apply component_ext R R (ε + ε)
    intro i l
    rw [← component_composite_shift R S R ε F G i l]
    simp only [F, G, component_mapOfComponents]
    exact selection_composite R S ε σ τ hinv f g (fun i j h => (pair i j h).φ_ψ) hR i l
  · apply component_ext S S (ε + ε)
    intro j b
    rw [← component_composite_shift S R S ε G F j b]
    simp only [F, G, component_mapOfComponents]
    exact selection_composite S R ε τ σ (fun j i => (hinv i j).symm) g f
      (fun j i h => (pair i j ((hinv i j).mpr h)).ψ_φ) hS j b

/-- Assemble the actual pair and deletion interleavings of a matching into
an actual interleaving of the existing finite biproduct families. -/
noncomputable def IsMatching.interleaving {ι κ : Type} [Fintype ι] [Fintype κ]
    {R : ι → Rectangle n} {S : κ → Rectangle n} {ε : ℝ≥0}
    {M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}}
    (hM : IsMatching (k := k) ε R S M) :
    CoordinateInterleaving ε (module (k := k) R) (module S) := by
  classical
  have hinv (i : ι) (j : κ) : M.finite i = some j ↔ M.reverse.finite j = some i :=
    (M.reverse_finite_some_iff j i).symm
  apply selectedInterleaving R S ε M.finite M.reverse.finite hinv
    (fun i j h => (hM.paired i j h).some)
  · intro i hi
    have h := (interleaved_zero_iff (k := k) (R i) ε).mp (hM.source_zero i hi)
    simpa only [RectangleHall.significant_iff_transition_ne_zero (k := k), not_not] using h
  · intro j hj
    have hnot : ∀ i, M.finite i ≠ some j := by
      intro i hi
      have h := (hinv i j).mp hi
      simp [hj] at h
    have h := (interleaved_zero_iff (k := k) (S j) ε).mp (hM.target_zero j hnot)
    simpa only [RectangleHall.significant_iff_transition_ne_zero (k := k), not_not] using h

/-- Each matched edge of the assembled maps comes from the same actual
interleaving of its two rectangle summands. -/
theorem IsMatching.interleaving_components {ι κ : Type} [Fintype ι] [Fintype κ]
    {R : ι → Rectangle n} {S : κ → Rectangle n} {ε : ℝ≥0}
    {M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}}
    (hM : IsMatching (k := k) ε R S M) (i : ι) (j : κ) (h : M.finite i = some j) :
    ∃ I : CoordinateInterleaving ε ((R i).module (k := k)) (S j).module,
      component R S ε hM.interleaving.φ i j = I.φ ∧
      component S R ε hM.interleaving.ψ j i = I.ψ := by
  refine ⟨(hM.paired i j h).some, ?_, ?_⟩
  · simp [IsMatching.interleaving, selectedInterleaving, component_mapOfComponents, entry, h]
  · have hr := (M.reverse_finite_some_iff j i).mpr h
    simp [IsMatching.interleaving, selectedInterleaving, component_mapOfComponents, entry, hr]

/-- A forward component outside the matching graph is zero. -/
theorem IsMatching.interleaving_component_zero {ι κ : Type} [Fintype ι] [Fintype κ]
    {R : ι → Rectangle n} {S : κ → Rectangle n} {ε : ℝ≥0}
    {M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}}
    (hM : IsMatching (k := k) ε R S M) (i : ι) (j : κ) (h : M.finite i ≠ some j) :
    component R S ε hM.interleaving.φ i j = 0 := by
  simp [IsMatching.interleaving, selectedInterleaving, component_mapOfComponents, entry, h]

/-- A reverse component outside the same matching graph is zero. -/
theorem IsMatching.interleaving_reverse_component_zero {ι κ : Type} [Fintype ι] [Fintype κ]
    {R : ι → Rectangle n} {S : κ → Rectangle n} {ε : ℝ≥0}
    {M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}}
    (hM : IsMatching (k := k) ε R S M) (i : ι) (j : κ) (h : M.finite i ≠ some j) :
    component S R ε hM.interleaving.ψ j i = 0 := by
  have hr : M.reverse.finite j ≠ some i := by simpa [M.reverse_finite_some_iff] using h
  simp [IsMatching.interleaving, selectedInterleaving, component_mapOfComponents, entry, hr]

/-- Reversing an occurrence matching reverses its pair interleavings and
exchanges its two sets of actual zero interleavings. -/
theorem IsMatching.reverse {ι κ : Type} [Fintype ι] [Fintype κ]
    {R : ι → Rectangle n} {S : κ → Rectangle n} {ε : ℝ≥0}
    {M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}}
    (hM : IsMatching (k := k) ε R S M) : IsMatching (k := k) ε S R M.reverse := by
  refine ⟨?_, ?_, ?_⟩
  · intro j i h
    exact (hM.paired i j ((M.reverse_finite_some_iff j i).mp h)).elim (fun I => ⟨I.symm⟩)
  · intro j hj
    apply hM.target_zero j
    intro i hi
    have h := (M.reverse_finite_some_iff j i).mpr hi
    simp [hj] at h
  · intro i hi
    apply hM.source_zero i
    cases h : M.finite i with
    | none => rfl
    | some j => exact False.elim (hi j ((M.reverse_finite_some_iff j i).mpr h))

end RectangleMatching
end TDA.Persistence
