import TDA.Sheaf.RealStratification

/-!
# Fixtures for stratifications of the real line

* No breakpoints: the only star is the whole line, which is basic, and every basic open has
  stratum `0`.
* One breakpoint at `0`, with strata `0 ← 1 → 2`: the stars are `(-∞, 0)`, `ℝ` and `(0, ∞)`;
  the strata of `(-2, -1)`, `(-1, 1)` and `(1, 2)` are `0`, `1` and `2`, and the inclusion
  `(1, 2) ⊆ (-1, 3)` of a piece of the right cell into a neighbourhood of the point follows
  the arrow `1 → 2`.
* The constant presheaf satisfies the hypothesis of the basis sheaf condition; its sheaf on
  the basis extends to the real line with the given sections on basic opens.
* The point diagram (the field at the breakpoint, zero on both cells) composed with the
  stratum functor is a sheaf on the basis. Its extension to the real line has
  one-dimensional sections over `(-1, 1)` and zero sections over `(1, 2)`.
-/

namespace TDA.Sheaf.RealStratificationExamples

open CategoryTheory TopologicalSpace Opposite TDA.Persistence TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.RealStratification

/-! ### No breakpoints -/

/-- With no breakpoints, the only star is the whole line. -/
theorem star_fin_zero (p : Fin 0 → ℝ) : star p 0 = ⊤ :=
  top_unique fun _ _ i => i.elim0

/-- With no breakpoints, the whole line is basic. -/
theorem isBasicOpen_top_fin_zero (p : Fin 0 → ℝ) : IsBasicOpen (breakpoints p) ⊤ :=
  star_fin_zero p ▸ isBasicOpen_star (Subsingleton.strictMono p) 0

/-- With no breakpoints, every basic open has stratum `0`. -/
theorem tau_fin_zero (p : Fin 0 → ℝ) (U : Basic (breakpoints p)) : tau p U = 0 :=
  Fin.ext (by have := (tau p U).isLt; omega)

/-! ### One breakpoint -/

/-- The single breakpoint `0`. -/
def p₁ : Fin 1 → ℝ := fun _ => 0

theorem p₁_strictMono : StrictMono p₁ := Subsingleton.strictMono p₁

theorem breakpoints_p₁ : breakpoints p₁ = {0} := by
  ext x
  simp [mem_breakpoints, p₁, eq_comm]

theorem coe_star_p₁_zero : (star p₁ 0 : Set ℝ) = Set.Iio 0 := by
  ext x
  rw [SetLike.mem_coe, mem_star]
  simp [p₁]

theorem coe_star_p₁_one : (star p₁ 1 : Set ℝ) = Set.univ := by
  ext x
  rw [SetLike.mem_coe, mem_star]
  simp

theorem coe_star_p₁_two : (star p₁ 2 : Set ℝ) = Set.Ioi 0 := by
  ext x
  rw [SetLike.mem_coe, mem_star]
  simp [p₁]

/-- The open interval `(a, b)`. -/
def ioo (a b : ℝ) : Opens realLine := ⟨Set.Ioo a b, isOpen_Ioo⟩

theorem isBasicOpen_ioo {a b : ℝ} (h : a < b) : IsBasicOpen (breakpoints p₁) (ioo a b) :=
  ⟨Set.nonempty_Ioo.2 h, Set.ordConnected_Ioo, by
    rw [breakpoints_p₁, Finset.coe_singleton]
    exact Set.subsingleton_singleton.anti Set.inter_subset_right⟩

/-- The stratum of `(a, b)` is `v` when the star of `v` contains `(a, b)` and contains the
breakpoint `0` exactly when `(a, b)` does. -/
theorem tau_ioo_eq {a b : ℝ} (h : a < b) {v : Fin 3} (hle : Set.Ioo a b ⊆ star p₁ v)
    (h0 : (0 : ℝ) ∈ (star p₁ v : Set ℝ) ↔ (0 : ℝ) ∈ Set.Ioo a b) :
    tau p₁ ⟨ioo a b, isBasicOpen_ioo h⟩ = v := by
  refine (tau_eq_iff p₁_strictMono _ v).2 ⟨hle, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Finset.mem_coe, breakpoints_p₁, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨h0.1 hx, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨h0.2 hx, rfl⟩

/-- `(-2, -1)` lies in the left cell. -/
theorem tau_left : tau p₁ ⟨ioo (-2) (-1), isBasicOpen_ioo (by norm_num)⟩ = 0 :=
  tau_ioo_eq (by norm_num) (by rw [coe_star_p₁_zero]; exact fun x hx => hx.2.trans (by norm_num))
    (by rw [coe_star_p₁_zero]; norm_num)

/-- `(-1, 1)` contains the breakpoint. -/
theorem tau_center : tau p₁ ⟨ioo (-1) 1, isBasicOpen_ioo (by norm_num)⟩ = 1 :=
  tau_ioo_eq (by norm_num) (by rw [coe_star_p₁_one]; exact Set.subset_univ _)
    (by rw [coe_star_p₁_one]; norm_num)

/-- `(-1, 3)` contains the breakpoint. -/
theorem tau_wide : tau p₁ ⟨ioo (-1) 3, isBasicOpen_ioo (by norm_num)⟩ = 1 :=
  tau_ioo_eq (by norm_num) (by rw [coe_star_p₁_one]; exact Set.subset_univ _)
    (by rw [coe_star_p₁_one]; norm_num)

/-- `(1, 2)` lies in the right cell. -/
theorem tau_right : tau p₁ ⟨ioo 1 2, isBasicOpen_ioo (by norm_num)⟩ = 2 :=
  tau_ioo_eq (by norm_num)
    (by rw [coe_star_p₁_two]; exact fun x hx => (by norm_num : (0 : ℝ) < 1).trans hx.1)
    (by rw [coe_star_p₁_two]; norm_num)

/-- The inclusion of `(1, 2)` into the neighbourhood `(-1, 3)` of the breakpoint follows the
arrow `1 → 2` from the point to the right cell. -/
example : Arrow (orient 1) (tau p₁ ⟨ioo (-1) 3, isBasicOpen_ioo (by norm_num)⟩)
    (tau p₁ ⟨ioo 1 2, isBasicOpen_ioo (by norm_num)⟩) := by
  refine (tau_eq_or_arrow p₁_strictMono ⟨ioo 1 2, isBasicOpen_ioo (by norm_num)⟩
    ⟨ioo (-1) 3, isBasicOpen_ioo (by norm_num)⟩
    (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).resolve_left fun h => ?_
  rw [tau_wide, tau_right] at h
  exact absurd h (by decide)

/-- The same arrow, read off directly. -/
example : Arrow (orient 1) 1 2 := arrow_orient_iff.2 ⟨rfl, Or.inr rfl⟩

/-! ### Sheaves on the basis -/

variable (k : Type) [Field k]

/-- The constant presheaf inverts every inclusion, so it is a sheaf on the basis. -/
theorem isSheaf_const (S : Finset ℝ) :
    Presheaf.IsSheaf (basicTopology S)
      ((Functor.const (BasicCat S)ᵒᵖ).obj (ModuleCat.of k k)) :=
  isSheaf_basic_of_isIso_sameStratum _ fun _ _ _ _ => by
    simp only [Functor.const_obj_map]
    infer_instance

/-- The constant sheaf on the basis, extended to the real line. -/
noncomputable def constLineSheaf (S : Finset ℝ) :
    Sheaf (Opens.grothendieckTopology realLine) (ModuleCat.{0} k) :=
  (basisEquiv S k).functor.obj ⟨_, isSheaf_const k S⟩

/-- Sections of the extended constant sheaf over a basic open are the field. -/
noncomputable def constLineSheafSectionsIso (S : Finset ℝ) (U : BasicCat S) :
    (constLineSheaf k S).obj.obj (op U.1) ≅ ModuleCat.of k k :=
  (((sheafToPresheaf _ _).mapIso ((basisEquiv S k).unitIso.app ⟨_, isSheaf_const k S⟩)).app
    (op U)).symm

/-- The point segment `{1}` of `0 ← 1 → 2`. -/
def pointSegment : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩

/-- The point diagram: the field at the breakpoint and zero on both cells. Both arrows are
noninvertible. -/
noncomputable abbrev pointDiagram : Diagram k (orient 1) := interval (orient 1) pointSegment

/-- The point diagram, read on basic opens through their strata, is a sheaf on the basis. -/
theorem isSheaf_point :
    Presheaf.IsSheaf (basicTopology (breakpoints p₁)) (tauFunctor p₁_strictMono ⋙ pointDiagram k) :=
  isSheaf_tauFunctor_comp p₁_strictMono _

/-- The point sheaf extended to the real line. -/
noncomputable def pointLineSheaf :
    Sheaf (Opens.grothendieckTopology realLine) (ModuleCat.{0} k) :=
  (basisEquiv _ k).functor.obj ⟨_, isSheaf_point k⟩

/-- Sections of the extended point sheaf over a basic open are the diagram at its stratum. -/
noncomputable def pointLineSheafSectionsIso (U : BasicCat (breakpoints p₁)) :
    (pointLineSheaf k).obj.obj (op U.1) ≅
      (pointDiagram k).obj (vtx (orient 1) (tau p₁ U)) :=
  (((sheafToPresheaf _ _).mapIso ((basisEquiv _ k).unitIso.app ⟨_, isSheaf_point k⟩)).app
    (op U)).symm

/-- Over `(-1, 1)` the point sheaf has one-dimensional sections. -/
theorem finrank_pointLineSheaf_center :
    Module.finrank k ((pointLineSheaf k).obj.obj (op (ioo (-1) 1))) = 1 := by
  rw [(pointLineSheafSectionsIso k ⟨ioo (-1) 1, isBasicOpen_ioo (by norm_num)⟩).toLinearEquiv
    |>.finrank_eq, tau_center, finrank_interval_obj]
  decide

/-- Over `(1, 2)` the point sheaf has zero sections. -/
theorem finrank_pointLineSheaf_right :
    Module.finrank k ((pointLineSheaf k).obj.obj (op (ioo 1 2))) = 0 := by
  rw [(pointLineSheafSectionsIso k ⟨ioo 1 2, isBasicOpen_ioo (by norm_num)⟩).toLinearEquiv
    |>.finrank_eq, tau_right, finrank_interval_obj]
  decide

end TDA.Sheaf.RealStratificationExamples
