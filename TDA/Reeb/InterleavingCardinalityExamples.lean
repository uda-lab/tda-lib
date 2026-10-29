import TDA.Reeb.InterleavingCardinality
import TDA.Reeb.InterleavingDistanceExamples
import TDA.Reeb.IntervalTranslation

/-!
# Cardinality obstructions: fixtures

C1. The point precosheaves `I ↦ {0 ∈ I}` and `I ↦ {1 ∈ I}` are at distance `1`. The lower bound
comes from `le_interleavingDistance_of_forall_exists_card_lt`: for `ε < 1` and
`r = (1 - ε) / 2`, the value at `(-r, r)` has one element and the value of the second precosheaf
at its `ε`-thickening has none.

C2. A nonempty finite value `F(I)` and an empty value `G(T_ε I)` exclude every `ε`-interleaving,
through the range form `Interleaving.isEmpty_of_card_lt_card_range`; this is
`Interleaving.isEmpty_of_nonempty_of_isEmpty` for finite `F(I)`.

C3. Graph objects with empty and nonempty total space and finitely many top components are at
geometric distance `⊤` by `RGraph.geometricInterleavingDistance_eq_top_of_card_ne`; this is
`RGraph.geometricInterleavingDistance_eq_top_of_isEmpty_of_nonempty` when the second graph has
finitely many components.
-/

open Set CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb.Examples.InterleavingCardinality

open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.Examples

/-! ## C1. Point precosheaves -/

/-- The distance `1` of the point precosheaves at `0` and `1`, with the lower bound from the
cardinality obstruction. -/
theorem point_distance_eq_one_of_card :
    interleavingDistance (pointPrecosheaf 0) (pointPrecosheaf 1) = 1 := by
  refine le_antisymm (by simpa using pointInterleaving.interleavingDistance_le)
    (le_interleavingDistance_of_forall_exists_card_lt fun ε hε => ?_)
  have hε' : (ε : ℝ) < 1 := by exact_mod_cast hε
  set r : ℝ := (1 - ε) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hx : (0 : ℝ) ∈ ioo (-r) r := ⟨by linarith, hr0⟩
  have hy : (1 : ℝ) ∉ thicken ε (ioo (-r) r) := by
    rw [thicken_ioo (by linarith)]
    rintro ⟨-, h⟩
    rw [hr] at h
    linarith
  have : IsEmpty ((pointPrecosheaf 1).obj (thicken ε (ioo (-r) r))) := ⟨fun x => hy x.down⟩
  have : Unique ((pointPrecosheaf 0).obj (ioo (-r) r)) :=
    ⟨⟨PLift.up hx⟩, fun _ => rfl⟩
  refine ⟨ioo (-r) r, Function.injective_of_subsingleton _, inferInstance, ?_⟩
  rw [Nat.card_of_isEmpty, Nat.card_unique]
  exact Nat.one_pos

/-! ## C2. Nonempty against empty values -/

/-- A nonempty finite value `F(I)` and an empty value `G(T_ε I)` exclude every `ε`-interleaving,
through the image cardinality bound. -/
theorem isEmpty_of_nonempty_of_isEmpty_of_finite {F G : OpenInterval ⥤ Type} {ε : ℝ≥0}
    {I : OpenInterval} [Finite (F.obj I)] (hF : Nonempty (F.obj I))
    (hG : IsEmpty (G.obj (thicken ε I))) : IsEmpty (Interleaving ε F G) := by
  refine Interleaving.isEmpty_of_card_lt_card_range (I := I) ?_
  rw [Nat.card_of_isEmpty]
  have : Finite (range (F.map (homOfLE ((le_thicken ε I).trans
      (le_thicken ε (thicken ε I)))))) := finite_range _
  have : Nonempty (range (F.map (homOfLE ((le_thicken ε I).trans
      (le_thicken ε (thicken ε I)))))) := (range_nonempty _).to_subtype
  exact Nat.card_pos

/-! ## C3. Empty against nonempty graph objects -/

/-- An empty and a nonempty graph object with finitely many top components are at geometric
distance `⊤`, by cardinality of the top components. -/
theorem geometricInterleavingDistance_eq_top_of_isEmpty_of_nonempty_of_card
    {A B : RGraph.RGraphCat} (hA : IsEmpty A.obj.left) (hB : Nonempty B.obj.left)
    [Finite ((RGraph.cosheafFunctor.obj B).obj.obj ⊤)] :
    RGraph.geometricInterleavingDistance A B = ⊤ := by
  apply RGraph.geometricInterleavingDistance_eq_top_of_card_ne
  have : IsEmpty ((RGraph.cosheafFunctor.obj A).obj.obj ⊤) := ⟨fun c => by
    change ZerothHomotopy _ at c
    induction c using ZerothHomotopy.rec with
    | mk x => exact hA.false x.1⟩
  have : Nonempty ((RGraph.cosheafFunctor.obj B).obj.obj ⊤) :=
    ⟨(ZerothHomotopy.mk ⟨hB.some, trivial⟩ :
      (intervalComponents (overBaseMap B.obj)).obj ⊤)⟩
  rw [Nat.card_of_isEmpty]
  exact (Nat.card_pos).ne

end TDA.Reeb.Examples.InterleavingCardinality
