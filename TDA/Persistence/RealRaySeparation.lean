import TDA.Persistence.SupportInterval
import TDA.Persistence.RealInterleavingDistance

/-!
# Zero distance between distinct real ray modules

The closed ray `[0,∞)` and the open ray `(0,∞)` support nonisomorphic persistence
modules over every field. They admit an interleaving at each positive parameter,
so their interleaving distance is zero. This example shows why separation and
attainment require additional hypotheses.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RealRay

open CategoryTheory
open scoped Classical NNReal ENNReal

variable {k : Type u} [Field k]

/-- The support of the ray, with an optional included birth endpoint. -/
def support (closed : Bool) : Set ℝ := {t | if closed then 0 ≤ t else 0 < t}

private theorem support_mono (closed : Bool) {s t : ℝ} (h : s ≤ t)
    (hs : s ∈ support closed) : t ∈ support closed := by
  cases closed <;> simp only [support, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq] at *
  · exact hs.trans_le h
  · exact hs.trans h

private theorem support_ordConnected (closed : Bool) : (support closed).OrdConnected := by
  constructor
  intro a ha b _ c hc
  exact support_mono closed hc.1 ha

/-- The coefficient field on one real ray, with zero fibers before its birth. -/
@[reducible]
noncomputable def module (closed : Bool) : PModule.{u,0,u} k ℝ :=
  SupportInterval.module (support closed) (support_ordConnected closed)

private theorem structureMap_val (closed : Bool) {s t : ℝ} (h : s ≤ t)
    (x : (module (k := k) closed).obj s) :
    ((structureMapLinear (module closed) h x) : k) = (x : k) := by
  classical
  rw [SupportInterval.structureMap_val]
  split_ifs with ht
  · rfl
  · exact (SupportInterval.val_eq_zero (support closed)
      (fun hs => ht (support_mono closed h hs)) x).symm

private theorem shifted_support (c d : Bool) {ε : ℝ≥0} (hε : 0 < ε)
    {t : ℝ} (ht : t ∈ support c) : t + (ε : ℝ) ∈ support d := by
  have ht' : 0 ≤ t := by
    cases c
    · exact le_of_lt (by simpa [support] using ht)
    · simpa [support] using ht
  have he : (0 : ℝ) < ε := hε
  cases d <;> simp [support] <;> linarith

private theorem fiber_le_shift (c d : Bool) (ε : ℝ≥0) (hε : 0 < ε) (t : ℝ) :
    SupportInterval.fiber (k := k) (support c) t ≤
      SupportInterval.fiber (k := k) (support d) (t + (ε : ℝ)) := by
    classical
    intro x hx
    by_cases ht : t ∈ support c
    · simp [SupportInterval.fiber, shifted_support c d hε ht]
    · have hx0 : x = 0 := by simpa [SupportInterval.fiber, ht] using hx
      simp [hx0]

private noncomputable def forward (c d : Bool) (ε : ℝ≥0) (hε : 0 < ε) :
    module (k := k) c ⟶ (RealShift.shift ε).obj (module d) where
  app t := ModuleCat.ofHom (Submodule.inclusion (fiber_le_shift c d ε hε t))
  naturality s t f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (structureMapLinear (module (k := k) c) (leOfHom f) x).val =
      (structureMapLinear (module (k := k) d)
        (show s + (ε : ℝ) ≤ t + (ε : ℝ) from add_le_add (leOfHom f) le_rfl) _).val
    exact (structureMap_val c (leOfHom f) x).trans
      (structureMap_val d (add_le_add (leOfHom f) le_rfl)
        (Submodule.inclusion (fiber_le_shift c d ε hε s) x)).symm

private theorem forward_val (c d : Bool) (ε : ℝ≥0) (hε : 0 < ε) (t : ℝ)
    (x : (module (k := k) c).obj t) :
    (((forward c d ε hε).app t).hom x).val = (x : k) := rfl

/-- Any pair of these rays admits a positive-parameter interleaving. -/
noncomputable def interleaving (c d : Bool) (ε : ℝ≥0) (hε : 0 < ε) :
    RealInterleaving ε (module (k := k) c) (module d) := by
  refine RealInterleaving.ofApp (forward c d ε hε) (forward d c ε hε) ?_ ?_
  · intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have heq : (t + (ε : ℝ)) + (ε : ℝ) = t + ((ε + ε : ℝ≥0) : ℝ) := by
      simp [NNReal.coe_add, add_assoc]
    change (structureMapLinear (module (k := k) c) heq.le _).val =
      (structureMapLinear (module (k := k) c)
        (le_add_of_nonneg_right (ε + ε).coe_nonneg) x).val
    exact (structureMap_val c heq.le _).trans
      (structureMap_val c (le_add_of_nonneg_right (ε + ε).coe_nonneg) x).symm
  · intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have heq : (t + (ε : ℝ)) + (ε : ℝ) = t + ((ε + ε : ℝ≥0) : ℝ) := by
      simp [NNReal.coe_add, add_assoc]
    change (structureMapLinear (module (k := k) d) heq.le _).val =
      (structureMapLinear (module (k := k) d)
        (le_add_of_nonneg_right (ε + ε).coe_nonneg) x).val
    exact (structureMap_val d heq.le _).trans
      (structureMap_val d (le_add_of_nonneg_right (ε + ε).coe_nonneg) x).symm

/-- Closing or opening the birth endpoint does not change interleaving distance. -/
theorem distance_eq_zero (c d : Bool) :
    realInterleavingDistance (module (k := k) c) (module d) = 0 := by
  apply realInterleavingDistance_eq_zero_iff.mpr
  intro ε hε
  exact ⟨interleaving c d ε hε⟩

/-- The closed and open rays are distinguished by the fiber at their birth. -/
theorem not_nonempty_iso : ¬ Nonempty (module (k := k) true ≅ module false) := by
  rintro ⟨e⟩
  let x : (module (k := k) true).obj 0 :=
    SupportInterval.one (support true) (by simp [support])
  have hz : ((e.hom.app 0).hom x : k) = 0 :=
    SupportInterval.val_eq_zero (support false) (by simp [support]) _
  have hy : (e.hom.app 0).hom x = 0 := Subtype.ext hz
  have hx0 : x = 0 := by
    have hh := congrArg (fun y => (e.inv.app 0).hom y) hy
    change ((e.hom.app 0 ≫ e.inv.app 0).hom x) = _ at hh
    rw [e.hom_inv_id_app] at hh
    simpa only [ModuleCat.hom_id, LinearMap.id_apply, map_zero] using hh
  have h := congrArg (fun y : (module (k := k) true).obj 0 => (y : k)) hx0
  exact one_ne_zero h

/-- The zero distance of the two rays is not attained by a zero-interleaving. -/
theorem not_nonempty_zero_interleaving :
    ¬ Nonempty (RealInterleaving 0 (module (k := k) true) (module false)) := by
  rintro ⟨i⟩
  exact not_nonempty_iso ⟨i.toIso⟩

end TDA.Persistence.RealRay
