import TDA.Reeb.Smoothing

/-!
# The extended interleaving distance

For precosheaves `F G : OpenInterval ⥤ C` valued in an arbitrary category `C`,
`interleavingDistance F G : ℝ≥0∞` is the infimum of the parameters `ε : ℝ≥0` admitting an
`ε`-interleaving (de Silva–Munch–Patel, Definition 4.4). It is `⊤` exactly when no
interleaving exists (`interleavingDistance_eq_top_iff`). The infimum is not assumed to be
attained: zero distance means an `ε`-interleaving for every `ε > 0`
(`interleavingDistance_eq_zero_iff`), which in general does not give a `0`-interleaving, so
zero distance does not imply isomorphism.

The extended pseudometric laws of DMP Proposition 4.5 hold: distance zero to itself, symmetry
and the triangle inequality. Isomorphic precosheaves are at distance zero, and the distance is
invariant under natural isomorphism in both arguments. An explicit `ε`-interleaving bounds the
distance by `ε`, and smoothing is nonexpansive. The distance is a plain function: no `EDist`,
`PseudoEMetricSpace` or `MetricSpace` instance is installed on `OpenInterval ⥤ C`.
See `docs/math/reeb-interleaving-distance.md`.
-/

open Set CategoryTheory
open scoped NNReal ENNReal

universe v u

namespace TDA.Reeb

open OpenInterval

section Distance

variable {C : Type u} [Category.{v} C]

/-- The extended interleaving distance (DMP Definition 4.4 / Proposition 4.5 form):
`⨅ ε ≥ 0 with an ε-interleaving, ε` in `[0, ∞]`. -/
noncomputable def interleavingDistance (F G : OpenInterval ⥤ C) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (Interleaving ε F G)), (ε : ℝ≥0∞)

variable {F G H F' G' : OpenInterval ⥤ C}

/-- A witness bounds the distance. -/
theorem interleavingDistance_le_of_nonempty {ε : ℝ≥0} (h : Nonempty (Interleaving ε F G)) :
    interleavingDistance F G ≤ ε :=
  iInf₂_le ε h

/-- An explicit `ε`-interleaving gives `d F G ≤ ε`. -/
theorem Interleaving.interleavingDistance_le {ε : ℝ≥0} (i : Interleaving ε F G) :
    interleavingDistance F G ≤ ε :=
  interleavingDistance_le_of_nonempty ⟨i⟩

/-- Lower-envelope property of the infimum. -/
theorem le_interleavingDistance_iff {r : ℝ≥0∞} :
    r ≤ interleavingDistance F G ↔ ∀ ε : ℝ≥0, Nonempty (Interleaving ε F G) → r ≤ ε :=
  le_iInf₂_iff

/-- Approximation from above, without assuming the infimum is attained. -/
theorem interleavingDistance_lt_iff {r : ℝ≥0∞} :
    interleavingDistance F G < r ↔
      ∃ ε : ℝ≥0, (ε : ℝ≥0∞) < r ∧ Nonempty (Interleaving ε F G) := by
  simp only [interleavingDistance, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

/-- Empty witness set gives `⊤`, and conversely. -/
theorem interleavingDistance_eq_top_iff :
    interleavingDistance F G = ⊤ ↔ ∀ ε : ℝ≥0, IsEmpty (Interleaving ε F G) := by
  simp only [interleavingDistance, iInf_eq_top, ENNReal.coe_ne_top, imp_false,
    not_nonempty_iff]

/-- A `0`-interleaving gives distance `0` (the converse fails; see the fixtures). -/
theorem Interleaving.interleavingDistance_eq_zero (i : Interleaving 0 F G) :
    interleavingDistance F G = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using i.interleavingDistance_le)

theorem interleavingDistance_self (F : OpenInterval ⥤ C) : interleavingDistance F F = 0 :=
  (Interleaving.refl 0 F).interleavingDistance_eq_zero

theorem interleavingDistance_eq_zero_of_iso (e : F ≅ G) : interleavingDistance F G = 0 :=
  (Interleaving.ofIso e).interleavingDistance_eq_zero

theorem interleavingDistance_comm (F G : OpenInterval ⥤ C) :
    interleavingDistance F G = interleavingDistance G F :=
  le_antisymm (le_iInf₂ fun _ ⟨i⟩ => i.symm.interleavingDistance_le)
    (le_iInf₂ fun _ ⟨i⟩ => i.symm.interleavingDistance_le)

/-- Triangle inequality. `ENNReal.iInf_add`/`ENNReal.add_iInf` hold for arbitrary (also
empty) index types, so the `⊤` summands need no separate case. -/
theorem interleavingDistance_triangle (F G H : OpenInterval ⥤ C) :
    interleavingDistance F H ≤ interleavingDistance F G + interleavingDistance G H := by
  calc interleavingDistance F H
      ≤ ⨅ (ε : ℝ≥0) (_ : Nonempty (Interleaving ε F G)) (δ : ℝ≥0)
          (_ : Nonempty (Interleaving δ G H)), ((ε : ℝ≥0∞) + δ) :=
        le_iInf₂ fun ε ⟨i⟩ => le_iInf₂ fun δ ⟨j⟩ => by
          simpa only [ENNReal.coe_add] using (i.trans j).interleavingDistance_le
    _ = interleavingDistance F G + interleavingDistance G H := by
        rw [interleavingDistance, interleavingDistance, ENNReal.iInf_add]
        refine iInf_congr fun ε => ?_
        rw [ENNReal.iInf_add]
        refine iInf_congr fun _ => ?_
        rw [ENNReal.add_iInf]
        refine iInf_congr fun δ => ?_
        rw [ENNReal.add_iInf]

/-- Invariance under natural isomorphism, on both arguments. -/
theorem interleavingDistance_congr (e : F ≅ F') (e' : G ≅ G') :
    interleavingDistance F G = interleavingDistance F' G' := by
  have key : ∀ {A B A' B' : OpenInterval ⥤ C}, (A ≅ A') → (B ≅ B') →
      interleavingDistance A' B' ≤ interleavingDistance A B := fun e e' =>
    le_iInf₂ fun _ ⟨i⟩ =>
      (((Interleaving.ofIso e.symm).trans (i.trans (Interleaving.ofIso e'))).mono
        (by simp)).interleavingDistance_le
  exact le_antisymm (key e.symm e'.symm) (key e e')

/-- Zero distance means witnesses at every positive parameter; not a `0`-witness. -/
theorem interleavingDistance_eq_zero_iff :
    interleavingDistance F G = 0 ↔ ∀ ε : ℝ≥0, 0 < ε → Nonempty (Interleaving ε F G) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, ⟨i⟩⟩ :=
      interleavingDistance_lt_iff.1 (h.trans_lt (ENNReal.coe_pos.2 hε))
    exact ⟨i.mono (ENNReal.coe_lt_coe.1 hδ).le⟩
  · intro h
    refine nonpos_iff_eq_zero.1 (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
    simpa using interleavingDistance_le_of_nonempty (h ε hε)

/-- Smoothing is nonexpansive for the distance (from `Interleaving.smooth`). -/
theorem interleavingDistance_smoothing_le (ε : ℝ≥0) (F G : OpenInterval ⥤ C) :
    interleavingDistance ((smoothing ε).obj F) ((smoothing ε).obj G) ≤
      interleavingDistance F G :=
  le_iInf₂ fun _ ⟨i⟩ => (i.smooth ε).interleavingDistance_le

/-- A precosheaf is within `ε` of its smoothing (from `Interleaving.selfSmoothing`). -/
theorem interleavingDistance_smoothing_self_le (ε : ℝ≥0) (F : OpenInterval ⥤ C) :
    interleavingDistance F ((smoothing ε).obj F) ≤ ε :=
  (Interleaving.selfSmoothing ε F).interleavingDistance_le

end Distance

end TDA.Reeb
