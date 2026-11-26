import TDA.Sheaf.AlexandrovTranslation
import TDA.Persistence.RealIntervalInterleaving

/-!
# Real Alexandrov translations: fixtures

These fixtures consume `TDA.Sheaf.AlexandrovTranslation` through actual Mathlib types.

* Evaluation of the sheaf shift at the non-principal opens of the upper Alexandrov line: the
  empty open, the whole line and the open ray `(t, ∞)` (`openRay`, `openRay_ne_principalOpen`)
  pull back to themselves, to themselves and to `(t + ε, ∞)`, computed from the geometric
  preimage formula `coe_map_translate`.
* The upper-ray modules `[0, ∞)` and `[r, ∞)` over a field, for `0 ≤ r` (in particular for
  `r > 0`): a real witness exists if and only if `r ≤ ε` (`rays_nonempty_iff`), and likewise a
  sheaf witness for the attached sheaves (`raySheaves_nonempty_iff`). For `ε < r` the first
  arrow at `t = 0` lands in the zero fibre, while the double-shift map of `[0, ∞)` at `0` is
  nonzero. For `r ≤ ε` the witness `rayInterleaving` consists of the interval comparisons, which
  send `1` to `1` at `t = 0`; the corresponding sheaf witness is nonzero over the principal
  open `↑0`. The sheaf distance of the two ray sheaves is `r` (`raySheaves_distance`).
* At `ε = 0` the transitions of a sheaf form the witness of its identity isomorphism.
-/

set_option autoImplicit false

namespace TDA.Sheaf.AlexandrovTranslationExamples

open CategoryTheory Limits Opposite TopologicalSpace Topology TDA.Persistence
open TDA.Persistence.RealBarcode TDA.Sheaf.Alexandrov TDA.Sheaf.AlexandrovTranslation
open scoped NNReal ENNReal

/-! ## The shift on non-principal opens -/

/-- The open ray `(t, ∞)` of the upper Alexandrov line. -/
def openRay (t : ℝ) : Opens (upperSpace ℝ) :=
  ⟨{x | t < WithUpperSet.ofUpperSet (α := ℝ) x},
    Topology.IsUpperSet.isOpen_iff_isUpperSet.mpr fun _ _ hab ha =>
      lt_of_lt_of_le ha (WithUpperSet.ofUpperSet_le_iff.mpr hab)⟩

/-- The open ray `(t, ∞)` is not a principal open. -/
theorem openRay_ne_principalOpen (t : ℝ) (p : upperSpace ℝ) :
    openRay t ≠ _root_.Alexandrov.principalOpen p := by
  intro h
  have hp : t < WithUpperSet.ofUpperSet (α := ℝ) p := by
    have : p ∈ openRay t := h ▸ _root_.Alexandrov.self_mem_principalOpen p
    exact this
  have hm : WithUpperSet.toUpperSet ((t + WithUpperSet.ofUpperSet (α := ℝ) p) / 2) ∈
      openRay t := by
    change t < (t + WithUpperSet.ofUpperSet (α := ℝ) p) / 2
    linarith
  rw [h] at hm
  change WithUpperSet.ofUpperSet (α := ℝ) p ≤ (t + WithUpperSet.ofUpperSet (α := ℝ) p) / 2 at hm
  linarith

/-- The open ray `(t, ∞)` pulls back to `(t + ε, ∞)`, by the geometric preimage formula. -/
theorem map_translate_openRay (ε : ℝ≥0) (t : ℝ) :
    (Opens.map (translate ε)).obj (openRay t) = openRay (t + ε) := by
  apply Opens.ext
  rw [coe_map_translate]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change t + (ε : ℝ) < WithUpperSet.ofUpperSet (α := ℝ) y + (ε : ℝ)
    exact add_lt_add_left hy _
  · intro hx
    refine ⟨WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ)), ?_, ?_⟩
    · change t < WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ)
      exact lt_sub_iff_add_lt.mpr hx
    · change WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ) + (ε : ℝ)) = x
      rw [sub_add_cancel]
      rfl

/-- The empty open pulls back to the empty open, by the geometric preimage formula. -/
theorem map_translate_bot (ε : ℝ≥0) : (Opens.map (translate ε)).obj ⊥ = ⊥ := by
  apply Opens.ext
  rw [coe_map_translate, Opens.coe_bot, Set.image_empty]

/-- The whole line pulls back to the whole line: translation by `ε` is onto. -/
theorem map_translate_top (ε : ℝ≥0) : (Opens.map (translate ε)).obj ⊤ = ⊤ := by
  apply Opens.ext
  rw [coe_map_translate, Opens.coe_top, Set.image_univ_of_surjective]
  intro x
  refine ⟨WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ)), ?_⟩
  change WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ) + (ε : ℝ)) = x
  rw [sub_add_cancel]
  rfl

variable {C : Type*} [Category C]

/-- Sections of the shifted sheaf over the open ray `(t, ∞)` are sections over `(t + ε, ∞)`. -/
theorem sheafShift_openRay (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) (t : ℝ) :
    ((sheafShift C ε).obj F).presheaf.obj (op (openRay t)) =
      F.presheaf.obj (op (openRay (t + ε))) := by
  rw [sheafShift_obj_presheaf_obj, map_translate_openRay]

/-- Sections of the shifted sheaf over the empty open are those of `F`. -/
theorem sheafShift_bot (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) :
    ((sheafShift C ε).obj F).presheaf.obj (op ⊥) = F.presheaf.obj (op ⊥) := by
  rw [sheafShift_obj_presheaf_obj, map_translate_bot]

/-- Global sections of the shifted sheaf are global sections of `F`. -/
theorem sheafShift_top (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) :
    ((sheafShift C ε).obj F).presheaf.obj (op ⊤) = F.presheaf.obj (op ⊤) := by
  rw [sheafShift_obj_presheaf_obj, map_translate_top]

/-- On a principal open the shift is the translate principal open. -/
example (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) (t : ℝ) :
    ((sheafShift C ε).obj F).presheaf.obj
        (op (_root_.Alexandrov.principalOpen (X := upperSpace ℝ) (WithUpperSet.toUpperSet t))) =
      F.presheaf.obj (op (_root_.Alexandrov.principalOpen (X := upperSpace ℝ)
        (WithUpperSet.toUpperSet (t + (ε : ℝ))))) :=
  sheafShift_obj_presheaf_obj_principalOpen ε F t

/-! ## Upper rays -/

section Rays

variable {k : Type*} [Field k]

/-- For `ε < r`, the upper rays `[0, ∞)` and `[r, ∞)` admit no real `ε`-witness: the first
arrow at `0` lands in the zero fibre at `ε`, so the first double-shift composite at `0` is zero,
while the double-shift map of `[0, ∞)` at `0` sends `1` to `1`. -/
theorem rays_isEmpty {ε : ℝ≥0} {r : ℝ} (h : (ε : ℝ) < r) :
    IsEmpty (RealInterleaving ε (intervalModule (k := k) (0, ⊤))
      (intervalModule (k := k) (r, ⊤))) := by
  refine ⟨fun i => ?_⟩
  have hdead : ¬ alive (r, ⊤) (0 + (ε : ℝ)) := fun ha => by
    have := ha.1
    linarith
  have hsub : Subsingleton (fiber (k := k) (r, ⊤) (0 + (ε : ℝ))) := ⟨fun a b => Subtype.ext (by
    have ha := a.property
    have hb := b.property
    simp only [fiber, ite_eq_right hdead, Submodule.mem_bot] at ha hb
    rw [ha, hb])⟩
  have hz : IsZero ((intervalModule (k := k) (r, ⊤)).obj (0 + (ε : ℝ))) :=
    @ModuleCat.isZero_of_subsingleton _ _ ((intervalModule (k := k) (r, ⊤)).obj (0 + (ε : ℝ))) hsub
  have hφ : i.φ.app 0 = 0 := hz.eq_of_tgt _ _
  have key := i.φ_ψ_app 0
  rw [hφ, zero_comp] at key
  have hb : alive (0, ⊤) 0 := ⟨le_rfl, WithTop.coe_lt_top 0⟩
  have ht : alive (0, ⊤) (0 + ((ε + ε : ℝ≥0) : ℝ)) :=
    ⟨le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε)), WithTop.coe_lt_top _⟩
  let x : fiber (k := k) (0, ⊤) 0 := ⟨1, by simp [fiber, hb]⟩
  have hx := congrArg (fun f => f.hom x) key
  have hv := congrArg (fun y : fiber (k := k) (0, ⊤) (0 + ((ε + ε : ℝ≥0) : ℝ)) => (y : k)) hx
  change (0 : k) = ((show fiber (k := k) (0, ⊤) (0 + ((ε + ε : ℝ≥0) : ℝ)) from
    ((intervalModule (0, ⊤)).map
      (homOfLE (le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε))))).hom x) : k) at hv
  erw [map_val] at hv
  rw [ite_eq_left ht] at hv
  exact one_ne_zero (show (1 : k) = 0 from hv.symm)

/-- For `0 ≤ r ≤ ε`, the interval comparisons interleave `[0, ∞)` and `[r, ∞)`: the supports
`[-ε, ∞)` and `[r - ε, ∞)` of the shifted modules contain `[r, ∞)` and `[0, ∞)` respectively, by
`r - ε ≤ 0 ≤ r`. -/
noncomputable def rayInterleaving (ε : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) (h : r ≤ ε) :
    RealInterleaving ε (intervalModule (k := k) (0, ⊤)) (intervalModule (k := k) (r, ⊤)) :=
  interleavingOfBounds ε (0, ⊤) (r, ⊤) (by simpa using h)
    (by simpa using add_nonneg hr ε.coe_nonneg) le_top le_top

/-- The first arrow of `rayInterleaving` is the interval comparison. -/
theorem rayInterleaving_φ (ε : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) (h : r ≤ ε) :
    (rayInterleaving (k := k) ε hr h).φ =
      comparison ε (0, ⊤) (r, ⊤) (by simpa using h) le_top :=
  rfl

/-- At `t = 0`, the first arrow of `rayInterleaving` sends the coefficient `1` to `1`. -/
theorem rayInterleaving_φ_app_zero (ε : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) (h : r ≤ ε)
    (x : fiber (k := k) (0, ⊤) 0) :
    ((show fiber (k := k) (r, ⊤) (0 + (ε : ℝ)) from
      ((rayInterleaving (k := k) ε hr h).φ.app 0).hom x) : k) = x := by
  exact (comparison_app_val ε (0, ⊤) (r, ⊤) (by simpa using h) le_top 0 x).trans
    (ite_eq_left ⟨by simpa using h, WithTop.coe_lt_top _⟩)

/-- Both arrows of `rayInterleaving` are nonzero. -/
theorem rayInterleaving_ne_zero (ε : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) (h : r ≤ ε) :
    (rayInterleaving (k := k) ε hr h).φ ≠ 0 ∧ (rayInterleaving (k := k) ε hr h).ψ ≠ 0 :=
  ⟨(comparison_ne_zero_iff (k := k) ε (0, ⊤) (r, ⊤) (WithTop.coe_lt_top _)
      (by simpa using h) le_top).mpr (WithTop.coe_lt_top _),
    (comparison_ne_zero_iff (k := k) ε (r, ⊤) (0, ⊤) (WithTop.coe_lt_top _)
      (by simpa using add_nonneg hr ε.coe_nonneg) le_top).mpr (WithTop.coe_lt_top _)⟩

/-- For `0 ≤ r`, the upper rays `[0, ∞)` and `[r, ∞)` admit a real `ε`-witness if and only if
`r ≤ ε`. -/
theorem rays_nonempty_iff (ε : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (RealInterleaving ε (intervalModule (k := k) (0, ⊤))
      (intervalModule (k := k) (r, ⊤))) ↔ r ≤ ε := by
  constructor
  · intro hi
    by_contra h
    exact (rays_isEmpty (lt_of_not_ge h)).false hi.some
  · intro h
    exact ⟨rayInterleaving ε hr h⟩

end Rays

section RaySheaves

variable {k : Type} [Field k]

/-- The sheaf on the upper Alexandrov line attached to the upper ray `[r, ∞)`. -/
noncomputable abbrev raySheaf (k : Type) [Field k] (r : ℝ) :
    (upperSpace ℝ).Sheaf (ModuleCat.{0} k) :=
  (upperSetEquivalence ℝ (ModuleCat.{0} k)).functor.obj (intervalModule (k := k) (r, ⊤))

/-- For `0 ≤ r`, the sheaves of `[0, ∞)` and `[r, ∞)` admit a sheaf `ε`-witness if and only if
`r ≤ ε`. -/
theorem raySheaves_nonempty_iff (ε : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (SheafInterleaving ε (raySheaf k 0) (raySheaf k r)) ↔ r ≤ ε :=
  (nonempty_sheafInterleaving_upperSet_iff _ _).trans (rays_nonempty_iff ε hr)

/-- If the sheaf witness attached to a module witness vanishes over `↑t`, then so does the first
module arrow at `t`. -/
private theorem app_eq_zero_of_sheaf {ε : ℝ≥0} {F G : (upperSpace ℝ).Sheaf (ModuleCat.{0} k)}
    (j : RealInterleaving ε ((realSections _).obj F) ((realSections _).obj G)) (t : ℝ)
    (hz : (SheafInterleaving.equivRealInterleaving.symm j).φ.hom.app
      (op (_root_.Alexandrov.principalOpen (X := upperSpace ℝ) (WithUpperSet.toUpperSet t))) = 0) :
    j.φ.app t = 0 := by
  have h1 := congrArg (fun f => f.app t) (SheafInterleaving.map_equivRealInterleaving_symm_φ j)
  simp only [NatTrans.comp_app, realSections_map_app] at h1
  rw [hz] at h1
  rw [← h1]
  exact zero_comp

/-- A transported arrow vanishing at `t` forces the original arrow to vanish at `t`. -/
private theorem app_eq_zero_of_congr {ε : ℝ≥0} {A A' B B' : PModule.{0,0,0} k ℝ} (e : A ≅ A')
    (d : B ≅ B') (f : A ⟶ (RealShift.shift ε).obj B) (t : ℝ)
    (h : (e.inv ≫ f ≫ (RealShift.shift ε).map d.hom).app t = 0) : f.app t = 0 := by
  have hf : f = e.hom ≫ (e.inv ≫ f ≫ (RealShift.shift ε).map d.hom) ≫
      (RealShift.shift ε).map d.inv := by
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Iso.hom_inv_id_assoc]
    rw [(RealShift.shift ε).map_id, Category.comp_id]
  rw [hf, NatTrans.comp_app, NatTrans.comp_app, h, zero_comp, comp_zero]

/-- For `0 ≤ r ≤ ε`, the sheaf witness attached to `rayInterleaving` has a nonzero first arrow
over the principal open `↑0`. -/
theorem raySheafInterleaving_φ_ne_zero (ε : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) (h : r ≤ ε) :
    (SheafInterleaving.equivRealInterleaving.symm
        ((rayInterleaving (k := k) ε hr h).congr
          ((upperSetEquivalence ℝ (ModuleCat.{0} k)).unitIso.app
            (intervalModule (k := k) (0, ⊤)))
          ((upperSetEquivalence ℝ (ModuleCat.{0} k)).unitIso.app
            (intervalModule (k := k) (r, ⊤))))).φ.hom.app
        (op (_root_.Alexandrov.principalOpen (X := upperSpace ℝ)
          (WithUpperSet.toUpperSet (0 : ℝ)))) ≠ 0 := by
  intro hz
  have h1 := app_eq_zero_of_sheaf (F := raySheaf k 0) (G := raySheaf k r) _ 0 hz
  have h2 := app_eq_zero_of_congr
    ((upperSetEquivalence ℝ (ModuleCat.{0} k)).unitIso.app (intervalModule (k := k) (0, ⊤)))
    ((upperSetEquivalence ℝ (ModuleCat.{0} k)).unitIso.app (intervalModule (k := k) (r, ⊤)))
    (rayInterleaving (k := k) ε hr h).φ 0 h1
  let x : fiber (k := k) (0, ⊤) 0 := ⟨1, by simp [fiber, alive]⟩
  have hv := rayInterleaving_φ_app_zero (k := k) ε hr h x
  erw [h2] at hv
  exact one_ne_zero hv.symm

/-- The sheaf interleaving distance of the sheaves of `[0, ∞)` and `[r, ∞)` is `r`. -/
theorem raySheaves_distance {r : ℝ≥0} :
    sheafInterleavingDistance (raySheaf k 0) (raySheaf k r) = r := by
  rw [sheafInterleavingDistance_upperSet]
  apply le_antisymm
  · exact realInterleavingDistance_le_of_nonempty ⟨rayInterleaving r r.coe_nonneg le_rfl⟩
  · rw [le_realInterleavingDistance_iff]
    intro ε hε
    exact ENNReal.coe_le_coe.mpr ((rays_nonempty_iff ε r.coe_nonneg).mp hε)

end RaySheaves

/-! ## The zero witness of the identity -/

/-- The transitions of a sheaf form a zero witness whose isomorphism is the identity. -/
example {R : Type} [Ring R] (F : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)) :
    SheafInterleaving.zeroEquivIso (SheafInterleaving.refl 0 F) = Iso.refl F := by
  apply Iso.ext
  rw [SheafInterleaving.zeroEquivIso_apply_hom]
  exact sheafTransition_zero F

end TDA.Sheaf.AlexandrovTranslationExamples
