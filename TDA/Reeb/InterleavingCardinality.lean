import TDA.Reeb.GeometricComponentObstruction

/-!
# Cardinality obstructions for interleavings of interval precosheaves

Let `F G : OpenInterval ⥤ Type v` and let `i` be an `ε`-interleaving of `F` and `G`. At an
interval `I`, the restriction `F(I) → F(T_ε T_ε I)` is `ψ_(T_ε I) ∘ φ_I` (`Interleaving.φ_ψ_app`),
so its range lies in the range of `ψ_(T_ε I)` (`Interleaving.range_map_subset_range_ψ`). For finite
`G(T_ε I)` the range therefore has at most `Nat.card (G (T_ε I))` elements
(`Interleaving.card_range_map_le`); `Interleaving.card_range_map_add_le` is the same bound for the
restriction to `T_(ε+ε) I`. When the restriction is injective, `φ_I` is injective
(`Interleaving.φ_app_injective`), so `F(I)` is finite and
`Nat.card (F I) ≤ Nat.card (G (T_ε I))` (`Interleaving.finite_of_injective`,
`Interleaving.card_le_of_injective`).

A strict reverse inequality excludes every `ε`-interleaving:
`Interleaving.isEmpty_of_card_lt_card_range` in the range form, and
`Interleaving.isEmpty_of_injective_of_card_lt` in the injective form. An
obstructing interval for every `ε` below `r` gives `r ≤ interleavingDistance F G`
(`le_interleavingDistance_of_forall_exists_card_lt`, and
`le_interleavingDistance_of_forall_exists_card_lt_symm` with the roles of `F` and `G` exchanged).

At the full line `thicken ε ⊤ = ⊤`, and every interleaving gives an equivalence `F(⊤) ≃ G(⊤)`
(`Interleaving.topEquiv`). Values at `⊤` of different cardinality therefore give distance `⊤`
(`interleavingDistance_eq_top_of_card_ne`; `RGraph.geometricInterleavingDistance_eq_top_of_card_ne`
for graph objects).

`Nat.card` of an infinite type is `0`. The bounds assume finiteness of the target value where they
use it, and the top form says nothing when both top values are infinite.

These are library statements about the distance of de Silva–Munch–Patel, Definition 4.4; no
numbered result of theirs states them. See `docs/math/reeb-interleaving-distance.md`.
-/

open Set CategoryTheory
open scoped NNReal ENNReal

universe v

namespace TDA.Reeb

open OpenInterval

variable {ε : ℝ≥0} {F G : OpenInterval ⥤ Type v}

namespace Interleaving

/-- The image of `F(I) → F(T_ε T_ε I)` lies in the image of `ψ_(T_ε I)`. -/
theorem range_map_subset_range_ψ (i : Interleaving ε F G) (I : OpenInterval) :
    range (F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))) ⊆
      range (i.ψ.app (thicken ε I)) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨i.φ.app I x, ?_⟩
  simpa only [types_comp_apply] using congrArg (fun f => f x) (i.φ_ψ_app I)

/-- A finite value `G(T_ε I)` bounds the number of elements of the image of
`F(I) → F(T_ε T_ε I)`. -/
theorem card_range_map_le (i : Interleaving ε F G) (I : OpenInterval)
    [Finite (G.obj (thicken ε I))] :
    Nat.card (range (F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I)))))) ≤
      Nat.card (G.obj (thicken ε I)) :=
  (Nat.card_mono (finite_range _) (i.range_map_subset_range_ψ I)).trans
    (Nat.card_le_card_of_surjective _ rangeFactorization_surjective)

/-- The bound of `card_range_map_le` for the restriction `F(I) → F(T_(ε+ε) I)`. -/
theorem card_range_map_add_le (i : Interleaving ε F G) (I : OpenInterval)
    [Finite (G.obj (thicken ε I))] :
    Nat.card (range (F.map (homOfLE (le_thicken (ε + ε) I)))) ≤ Nat.card (G.obj (thicken ε I)) := by
  let k : thicken ε (thicken ε I) ⟶ thicken (ε + ε) I := homOfLE (thicken_thicken' ε ε I).le
  have hsub : range (F.map (homOfLE (le_thicken (ε + ε) I))) ⊆
      range (fun y => F.map k (i.ψ.app (thicken ε I) y)) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨i.φ.app I x, ?_⟩
    have h := congrArg (fun f => f x)
      ((i.φ_ψ_app_assoc I (F.map k)).trans
        (map_comp_map_of_interval F _ k (homOfLE (le_thicken (ε + ε) I))))
    simpa only [types_comp_apply] using h
  exact (Nat.card_mono (finite_range _) hsub).trans
    (Nat.card_le_card_of_surjective _ rangeFactorization_surjective)

/-- An injective restriction `F(I) → F(T_ε T_ε I)` and a finite value `G(T_ε I)` make `F(I)`
finite. -/
theorem finite_of_injective (i : Interleaving ε F G) {I : OpenInterval}
    (h : Function.Injective
      (F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))))
    [Finite (G.obj (thicken ε I))] : Finite (F.obj I) :=
  Finite.of_injective _ (i.φ_app_injective h)

/-- An injective restriction `F(I) → F(T_ε T_ε I)` gives `Nat.card (F I) ≤ Nat.card (G (T_ε I))`
for a finite value `G(T_ε I)`. -/
theorem card_le_of_injective (i : Interleaving ε F G) {I : OpenInterval}
    (h : Function.Injective
      (F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))))
    [Finite (G.obj (thicken ε I))] : Nat.card (F.obj I) ≤ Nat.card (G.obj (thicken ε I)) :=
  Nat.card_le_card_of_injective _ (i.φ_app_injective h)

/-- If the image of `F(I) → F(T_ε T_ε I)` has more elements than the finite value `G(T_ε I)`,
there is no `ε`-interleaving of `F` and `G`. -/
theorem isEmpty_of_card_lt_card_range {I : OpenInterval} [Finite (G.obj (thicken ε I))]
    (hc : Nat.card (G.obj (thicken ε I)) <
      Nat.card (range (F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))))) :
    IsEmpty (Interleaving ε F G) :=
  ⟨fun i => (i.card_range_map_le I).not_gt hc⟩

end Interleaving

/-- If for every `ε` below `r` some interval `I` has an injective restriction
`F(I) → F(T_ε T_ε I)` and a finite value `G(T_ε I)` with fewer elements than `F(I)`, then
`r ≤ interleavingDistance F G`. -/
theorem le_interleavingDistance_of_forall_exists_card_lt {r : ℝ≥0∞}
    (h : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → ∃ I : OpenInterval,
      Function.Injective
        (F.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))) ∧
      Finite (G.obj (thicken ε I)) ∧ Nat.card (G.obj (thicken ε I)) < Nat.card (F.obj I)) :
    r ≤ interleavingDistance F G := by
  refine le_interleavingDistance_iff.2 fun ε ⟨i⟩ => le_of_not_gt fun hε => ?_
  obtain ⟨I, hinj, hfin, hc⟩ := h ε hε
  exact (Interleaving.isEmpty_of_injective_of_card_lt hinj hc).false i

/-- `le_interleavingDistance_of_forall_exists_card_lt` with the obstruction on the second
precosheaf. -/
theorem le_interleavingDistance_of_forall_exists_card_lt_symm {r : ℝ≥0∞}
    (h : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → ∃ I : OpenInterval,
      Function.Injective
        (G.map (homOfLE ((le_thicken ε I).trans (le_thicken ε (thicken ε I))))) ∧
      Finite (F.obj (thicken ε I)) ∧ Nat.card (F.obj (thicken ε I)) < Nat.card (G.obj I)) :
    r ≤ interleavingDistance F G := by
  rw [interleavingDistance_comm]
  exact le_interleavingDistance_of_forall_exists_card_lt h

/-- Values at `⊤` of different cardinality give interleaving distance `⊤`. -/
theorem interleavingDistance_eq_top_of_card_ne (h : Nat.card (F.obj ⊤) ≠ Nat.card (G.obj ⊤)) :
    interleavingDistance F G = ⊤ :=
  interleavingDistance_eq_top_iff.2 fun _ => ⟨fun i => h (Nat.card_congr i.topEquiv)⟩

/-- Graph objects whose component types at `⊤` have different cardinality are at geometric
interleaving distance `⊤`. -/
theorem RGraph.geometricInterleavingDistance_eq_top_of_card_ne {A B : RGraph.RGraphCat}
    (h : Nat.card ((RGraph.cosheafFunctor.obj A).obj.obj ⊤) ≠
      Nat.card ((RGraph.cosheafFunctor.obj B).obj.obj ⊤)) :
    RGraph.geometricInterleavingDistance A B = ⊤ :=
  RGraph.geometricInterleavingDistance_eq_top_of_isEmpty_equiv ⟨fun e => h (Nat.card_congr e)⟩

end TDA.Reeb
