import TDA.Sheaf.BandIntervalCostTable

/-!
# Common convolution for graded interval occurrences

A common convolution sends all bounded open occurrences into the bounded closed
block in the next degree. The other types retain their degrees. The radius of
the witness and the occurrence labels are preserved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open TDA.Sheaf.RealStratification

namespace TDA.Sheaf.BandConvolution

variable {k : Type} [Field k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

/-- One positive radius exceeds the bounded-open half-lengths in both finite families. -/
theorem exists_normalizing_radius {I L : Type} [Finite I] [Finite L]
    (E : I → IntervalEndpoints) (F : L → IntervalEndpoints) :
    ∃ s : ℝ, 0 < s ∧ (∀ i, (E i).normalizationThreshold < 2 * s) ∧
      (∀ j, (F j).normalizationThreshold < 2 * s) := by
  let f : I ⊕ L → ℝ := Sum.elim (fun i => (E i).normalizationThreshold)
    (fun j => (F j).normalizationThreshold)
  obtain ⟨b, hb⟩ := (Set.finite_range f).bddAbove
  let s := max b 0 + 1
  have hs : 0 < s := by dsimp [s]; linarith [le_max_right b (0 : ℝ)]
  have h (a : I ⊕ L) : f a < 2 * s := by
    have hba := (hb (Set.mem_range_self a)).trans (le_max_left b 0)
    dsimp [s] at hs ⊢
    linarith
  exact ⟨s, hs, fun i => h (.inl i), fun j => h (.inr j)⟩

/-- Common convolution identifies each summand with the interval of normalized support
in the effective degree, and gives a witness at the original radius on their biproducts. -/
theorem Witness.exists_normalized_biproduct {I L : Type} [Finite I] [Finite L]
    {m : I → ℕ} {n : L → ℕ} {p : (i : I) → Fin (m i) → ℝ} {q : (j : L) → Fin (n j) → ℝ}
    (hp : ∀ i, StrictMono (p i)) (hq : ∀ j, StrictMono (q j))
    {X : (i : I) → GradedInterval (m i)} {Y : (j : L) → GradedInterval (n j)}
    {ε : ℝ} {hε : 0 ≤ ε}
    (w : Witness k hε (⨁ fun i => (X i).obj k (hp i)) (⨁ fun j => (Y j).obj k (hq j)))
    (E : I → IntervalEndpoints) (F : L → IntervalEndpoints)
    (hX : ∀ i, intervalSet (p i) (X i).interval = (E i).support)
    (hY : ∀ j, intervalSet (q j) (Y j).interval = (F j).support)
    {s : ℝ} (hs : 0 ≤ s) (hE : ∀ i, (E i).normalizationThreshold < 2 * s)
    (hF : ∀ j, (F j).normalizationThreshold < 2 * s) :
    ∃ (X' : (i : I) → GradedInterval (bandBreakpoints (p i) s).card)
      (Y' : (j : L) → GradedInterval (bandBreakpoints (q j) s).card),
      (∀ i, intervalSet (sortedBreakpoints (bandBreakpoints (p i) s)) (X' i).interval =
          ((E i).normalized hs (hE i)).support ∧
        (X' i).degree = (E i).effectiveDegree (X i).degree ∧
        Nonempty ((T k s).obj ((X i).obj k (hp i)) ≅
          (X' i).obj k (strictMono_sortedBreakpoints (bandBreakpoints (p i) s)))) ∧
      (∀ j, intervalSet (sortedBreakpoints (bandBreakpoints (q j) s)) (Y' j).interval =
          ((F j).normalized hs (hF j)).support ∧
        (Y' j).degree = (F j).effectiveDegree (Y j).degree ∧
        Nonempty ((T k s).obj ((Y j).obj k (hq j)) ≅
          (Y' j).obj k (strictMono_sortedBreakpoints (bandBreakpoints (q j) s)))) ∧
      Nonempty (Witness k hε
        (⨁ fun i => (X' i).obj k (strictMono_sortedBreakpoints (bandBreakpoints (p i) s)))
        (⨁ fun j => (Y' j).obj k (strictMono_sortedBreakpoints (bandBreakpoints (q j) s)))) := by
  classical
  have hx := fun i => (E i).exists_iso_normalized k (hp i) (X i) (hX i) hs (hE i)
  have hy := fun j => (F j).exists_iso_normalized k (hq j) (Y j) (hY j) hs (hF j)
  choose J hJ e using hx
  choose K hK f using hy
  let X' (i : I) : GradedInterval (bandBreakpoints (p i) s).card :=
    ⟨J i, (E i).effectiveDegree (X i).degree⟩
  let Y' (j : L) : GradedInterval (bandBreakpoints (q j) s).card :=
    ⟨K j, (F j).effectiveDegree (Y j).degree⟩
  refine ⟨X', Y', fun i => ⟨hJ i, rfl, e i⟩, fun j => ⟨hK j, rfl, f j⟩, ⟨?_⟩⟩
  exact (w.convolve hs).congr
    ((T k s).mapBiproduct _ ≪≫ biproduct.mapIso fun i => (e i).some)
    ((T k s).mapBiproduct _ ≪≫ biproduct.mapIso fun j => (f j).some)

end TDA.Sheaf.BandConvolution
