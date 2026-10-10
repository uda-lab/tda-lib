import TDA.Reeb.Smoothing
import Mathlib.CategoryTheory.Types.Basic

/-!
# Smoothing and interleaving fixtures

Regression fixtures for `TDA.Reeb.smoothing` and `TDA.Reeb.Interleaving`, all at
`C := Type`:

* the zero parameter: `S_0 F ≅ F`, and the `0`-interleaving of an isomorphism round-trips;
* the empty interval: `S_ε F (∅) ≅ F (∅)`;
* the composition order: `S_ε (S_δ F)` is definitionally `(T_ε ⋙ T_δ) ⋙ F`;
* identity witnesses followed by enlargement;
* the point precosheaves at `0` and `1` are `1`-interleaved but not `0`-interleaved;
* the precosheaves `I ↦ {0 ∈ I}` and `I ↦ {0 ∈ closure I}` are `ε`-interleaved for every
  `ε > 0` but not `0`-interleaved: witnesses at every positive parameter do not give an
  isomorphism;
* self-smoothing, nonexpansiveness, composition and symmetry.
-/

open Set CategoryTheory
open scoped NNReal

namespace TDA.Reeb.Examples

open OpenInterval Interleaving

/-- Zero parameter: `S_0 F ≅ F`, and the `0`-interleaving from an isomorphism round-trips. -/
example (F : OpenInterval ⥤ Type) : (smoothing 0).obj F ≅ F := smoothingZeroIso.app F

example (F G : OpenInterval ⥤ Type) (e : F ≅ G) : (Interleaving.ofIso e).toIso = e :=
  Interleaving.zeroEquivIso.right_inv e

/-- Empty interval: `S_ε F (∅) ≅ F (∅)`. -/
example (ε : ℝ≥0) (F : OpenInterval ⥤ Type) : ((smoothing ε).obj F).obj ⊥ ≅ F.obj ⊥ :=
  smoothingObjBotIso ε F

/-- The composition order is definitional: `S_ε (S_δ F) = (T_ε ⋙ T_δ) ⋙ F`. -/
example (ε δ : ℝ≥0) (F : OpenInterval ⥤ Type) :
    (smoothing ε).obj ((smoothing δ).obj F) = (thickenFunctor ε ⋙ thickenFunctor δ) ⋙ F :=
  rfl

/-- Identity witnesses and enlargement. -/
example (F : OpenInterval ⥤ Type) : Interleaving 1 F F :=
  (Interleaving.refl 0 F).mono zero_le_one

/-- The point precosheaf `I ↦ {a ∈ I}` (a singleton or empty). -/
def pointPrecosheaf (a : ℝ) : OpenInterval ⥤ Type where
  obj I := PLift (a ∈ I)
  map f := TypeCat.ofHom fun h => PLift.up (f.le h.down)

/-- `I ↦ {a ∈ closure I}`. -/
def closurePrecosheaf (a : ℝ) : OpenInterval ⥤ Type where
  obj I := PLift (a ∈ closure (I : Set ℝ))
  map f := TypeCat.ofHom fun h => PLift.up (closure_mono (OpenInterval.le_iff_subset.1 f.le) h.down)

instance (a : ℝ) (I : OpenInterval) : Subsingleton ((pointPrecosheaf a).obj I) :=
  inferInstanceAs (Subsingleton (PLift (a ∈ I)))

instance (a : ℝ) (I : OpenInterval) : Subsingleton ((closurePrecosheaf a).obj I) :=
  inferInstanceAs (Subsingleton (PLift (a ∈ closure (I : Set ℝ))))

/-- Witnesses between subsingleton-valued precosheaves satisfy every triangle. -/
def interleavingOfSubsingleton {ε : ℝ≥0} {F G : OpenInterval ⥤ Type}
    [∀ I, Subsingleton (F.obj I)] [∀ I, Subsingleton (G.obj I)]
    (φ : F ⟶ (smoothing ε).obj G) (ψ : G ⟶ (smoothing ε).obj F) : Interleaving ε F G where
  φ := φ
  ψ := ψ
  φ_ψ := by ext I x; exact Subsingleton.elim (α := F.obj _) _ _
  ψ_φ := by ext I x; exact Subsingleton.elim (α := G.obj _) _ _

/-- `F_a ⟶ S_ε F_b` when `|b - a| ≤ ε`. -/
def pointShift {a b : ℝ} {ε : ℝ≥0} (h : |b - a| ≤ ε) :
    pointPrecosheaf a ⟶ (smoothing ε).obj (pointPrecosheaf b) where
  app I := TypeCat.ofHom fun (x : PLift (a ∈ I)) =>
    (PLift.up (mem_thicken.2 ⟨a, x.down, h⟩) : PLift (b ∈ thicken ε I))
  naturality _ _ _ := rfl

/-- The point precosheaves at `0` and `1` are `1`-interleaved ... -/
def pointInterleaving : Interleaving 1 (pointPrecosheaf 0) (pointPrecosheaf 1) :=
  interleavingOfSubsingleton (pointShift (by norm_num)) (pointShift (by norm_num))

/-- ... but not `0`-interleaved: on `(-1/2, 1/2)` one value is inhabited, the other empty. -/
theorem not_pointInterleaving_zero :
    IsEmpty (Interleaving 0 (pointPrecosheaf 0) (pointPrecosheaf 1)) := by
  refine ⟨fun i => ?_⟩
  have x : (pointPrecosheaf 0).obj (ioo (-1/2) (1/2)) :=
    PLift.up (by change (0 : ℝ) ∈ Set.Ioo (-1/2) (1/2); constructor <;> norm_num)
  have h : (1 : ℝ) ∈ ioo (-1/2) (1/2) := PLift.down ((i.toIso).hom.app _ x)
  change (1 : ℝ) ∈ Set.Ioo (-1/2) (1/2) at h
  norm_num at h

/-- Zero interleaving is distinguished from zero distance: `I ↦ {0 ∈ I}` and
`I ↦ {0 ∈ closure I}` are `ε`-interleaved for every `ε > 0` but not `0`-interleaved (they
differ on `(0, 1)`). -/
theorem point_closure_interleaving :
    (∀ ε : ℝ≥0, 0 < ε → Nonempty (Interleaving ε (pointPrecosheaf 0) (closurePrecosheaf 0))) ∧
      IsEmpty (Interleaving 0 (pointPrecosheaf 0) (closurePrecosheaf 0)) := by
  refine ⟨fun ε hε => ⟨interleavingOfSubsingleton
    { app := fun I => TypeCat.ofHom fun (x : PLift ((0 : ℝ) ∈ I)) =>
        (PLift.up (subset_closure (le_thicken ε I x.down)) :
          PLift ((0 : ℝ) ∈ closure (thicken ε I : Set ℝ)))
      naturality := fun _ _ _ => rfl }
    { app := fun I => TypeCat.ofHom fun (x : PLift ((0 : ℝ) ∈ closure (I : Set ℝ))) =>
        (PLift.up (by
          obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.1 x.down ε hε
          exact mem_thicken.2 ⟨b, hb, by rw [← Real.dist_eq]; exact hd.le⟩) :
          PLift ((0 : ℝ) ∈ thicken ε I))
      naturality := fun _ _ _ => rfl }⟩, ⟨fun i => ?_⟩⟩
  have x : (closurePrecosheaf 0).obj (ioo 0 1) := PLift.up (by
    change (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1)
    rw [closure_Ioo (by norm_num)]; constructor <;> norm_num)
  have h : (0 : ℝ) ∈ ioo 0 1 := PLift.down ((i.toIso).inv.app _ x)
  change (0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 at h
  exact lt_irrefl _ h.1

/-- Interleaving of a precosheaf with its own smoothing, and nonexpansiveness. -/
example (ε δ : ℝ≥0) (F G : OpenInterval ⥤ Type) (i : Interleaving δ F G) :
    Interleaving ε F ((smoothing ε).obj F) × Interleaving δ ((smoothing ε).obj F)
      ((smoothing ε).obj G) :=
  (Interleaving.selfSmoothing ε F, i.smooth ε)

/-- Composition and symmetry. -/
example : Interleaving (1 + 1) (pointPrecosheaf 0) (pointPrecosheaf 0) :=
  pointInterleaving.trans pointInterleaving.symm

end TDA.Reeb.Examples
