import TDA.Sheaf.OrthantLocalization
import TDA.Sheaf.RayLocalizationExamples

/-!
# Orthant localization: fixtures

These fixtures consume `TDA.Sheaf.OrthantSheaf` and `TDA.Sheaf.OrthantLocalization` over a field
`k`, with value category `ModuleCat.{0} k`, on the plane `Fin 2 → ℝ`.

* `lineModule` is `k` on the horizontal line `{x | x 1 = 0}` with identity maps along the line
  and zero maps elsewhere: the singleton module of `TDA.Sheaf.RaySheafExamples` read through the
  second coordinate `secondCoord`. Its maps along the line are nonzero
  (`lineModule_map_ne_zero`, so `not_isZero_lineModule`), and its all-strict maps vanish
  (`lineModule_map_strict`), so it is ephemeral (`ephemeral_lineModule`) and `Q` kills it
  (`isZero_orthantQ_lineModule`).
* `halfPlaneModule` is `k` on the closed upper half-plane `{x | 0 ≤ x 1}`, the module
  `setModule (Ici 0)` of `TDA.Sheaf.RayLocalizationExamples` read through the second
  coordinate; its all-strict map from `0` to `1` is the identity of `k`, so `Q` does not kill it
  (`not_isZero_orthantQ_halfPlaneModule`).
* Consumers of the comparisons: the singleton module on `ℝ` is orthant-ephemeral on `Fin 1 → ℝ`
  through `orthantOne_ephemeral_iff`, and `Q` is an equivalence for `n = 0`.
-/

set_option autoImplicit false

namespace TDA.Sheaf.OrthantLocalizationExamples

open CategoryTheory Limits TDA.Persistence TDA.Sheaf.OrthantSheaf TDA.Sheaf.RaySheaf
  TDA.Sheaf.RaySheafExamples TDA.Sheaf.RayLocalizationExamples

variable {k : Type} [Field k]

/-! ## A line that `Q` kills -/

/-- The second coordinate of the plane. -/
def secondCoord : (Fin 2 → ℝ) →o ℝ :=
  ⟨fun x => x 1, fun _ _ h => h 1⟩

/-- `k` on the horizontal line `{x | x 1 = 0}`: the singleton module read through the second
coordinate. -/
noncomputable def lineModule : PModule.{0,0,0} k (Fin 2 → ℝ) :=
  reindex secondCoord pointModule

/-- The map of the singleton module from `0` to `0` is nonzero. -/
theorem pointModule_map_ne_zero {s t : ℝ} (hst : s ≤ t) (hs : s = 0) (ht : t = 0) :
    (pointModule (k := k)).map (homOfLE hst) ≠ 0 := by
  classical
  subst hs
  subst ht
  intro h
  have h1 : (1 : k) ∈ pointFiber (k := k) 0 := by simp [pointFiber]
  have key : (((pointModule (k := k)).map (homOfLE hst)).hom ⟨1, h1⟩ : pointFiber (k := k) 0).1
      = 1 := by
    change ((pointMap (k := k) hst ⟨1, h1⟩ : pointFiber (k := k) 0) : k) = 1
    simp [pointMap]
  rw [h] at key
  exact one_ne_zero key.symm

/-- Along the line, the maps of `lineModule` are nonzero. -/
theorem lineModule_map_ne_zero {x y : Fin 2 → ℝ} (hxy : x ≤ y) (hx : x 1 = 0) (hy : y 1 = 0) :
    (lineModule (k := k)).map (homOfLE hxy) ≠ 0 :=
  pointModule_map_ne_zero (hxy 1) hx hy

/-- The all-strict maps of `lineModule` vanish. -/
theorem lineModule_map_strict {x y : Fin 2 → ℝ} (h : ∀ i, x i < y i) :
    (lineModule (k := k)).map (homOfLE fun i => (h i).le) = 0 :=
  pointModule_map_lt (h 1)

/-- `lineModule` is nonzero: its map from `0` to `(1, 0)` is nonzero. -/
theorem not_isZero_lineModule : ¬ IsZero (lineModule (k := k)) := by
  intro hz
  have hxy : (fun _ : Fin 2 => (0 : ℝ)) ≤ fun i => if i = 0 then 1 else 0 := by
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  refine lineModule_map_ne_zero (k := k) hxy rfl (by simp) ?_
  have h0 : 𝟙 ((lineModule (k := k)).obj fun i => if i = 0 then 1 else 0) = 0 :=
    congrArg (fun f => NatTrans.app f _) ((IsZero.iff_id_eq_zero _).1 hz)
  rw [← Category.comp_id ((lineModule (k := k)).map _), h0, comp_zero]

/-- `lineModule` is ephemeral. -/
theorem ephemeral_lineModule : (orthantBasis 2).ephemeral _ (lineModule (k := k)) :=
  (ephemeral_orthantBasis_iff _).2 fun _ _ h => lineModule_map_strict h

/-- `Q` kills `lineModule`. -/
theorem isZero_orthantQ_lineModule :
    IsZero (((orthantBasis 2).Q (ModuleCat.{0} k)).obj (lineModule (k := k))) :=
  (isZero_orthantQ_iff _).2 fun _ _ h => lineModule_map_strict h

/-- `lineModule` is at distance zero from `BQ` of it, which is zero. -/
example : coordinateInterleavingDistance (lineModule (k := k))
    (((orthantBasis 2).B _).obj (((orthantBasis 2).Q (ModuleCat.{0} k)).obj lineModule)) = 0 :=
  coordinateInterleavingDistance_orthantB_orthantQ _

/-! ## A half-plane that `Q` does not kill -/

/-- `k` on the closed upper half-plane `{x | 0 ≤ x 1}`. -/
noncomputable def halfPlaneModule : PModule.{0,0,0} k (Fin 2 → ℝ) :=
  reindex secondCoord (setModule (Set.Ici 0))

/-- `Q` of the half-plane module is nonzero: its all-strict map from `0` to `1` is the identity
of `k`. -/
theorem not_isZero_orthantQ_halfPlaneModule :
    ¬ IsZero (((orthantBasis 2).Q (ModuleCat.{0} k)).obj (halfPlaneModule (k := k))) := by
  classical
  rw [isZero_orthantQ_iff]
  intro h
  have hlt : ∀ i : Fin 2, (fun _ => (0 : ℝ)) i < (fun _ => (1 : ℝ)) i := fun _ => one_pos
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
  have h1 : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 zero_le_one
  have hk : (1 : k) ∈ setFiber (k := k) (Set.Ici 0) 0 := by simp [setFiber]
  have := congrArg (fun φ : (halfPlaneModule (k := k)).obj (fun _ => 0) ⟶ _ =>
    (show setFiber (k := k) (Set.Ici 0) 1 from φ.hom ⟨1, hk⟩).1) (h _ _ hlt)
  have e := setModule_map_apply (k := k) (Set.Ici 0) (homOfLE (zero_le_one : (0 : ℝ) ≤ 1)) h0 h1
    ⟨1, hk⟩
  have h2 := e.symm.trans this
  simp only at h2
  exact one_ne_zero (h2.trans rfl)

/-! ## Consumers of the comparisons -/

/-- The singleton module on `ℝ`, read on `Fin 1 → ℝ`, is orthant-ephemeral. -/
example : (orthantBasis 1).ephemeral _
    ((OrderIso.funUnique (Fin 1) ℝ).monotone.functor ⋙ pointModule (k := k)) :=
  (orthantOne_ephemeral_iff _).2 rayEphemeral_pointModule

/-- For `n = 0`, `Q` is an equivalence. -/
example : ((orthantBasis 0).Q (ModuleCat.{0} k)).IsEquivalence :=
  orthantQ_zero_isEquivalence _

end TDA.Sheaf.OrthantLocalizationExamples
