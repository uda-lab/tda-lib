import TDA.Sheaf.LocalSystem
import TDA.Sheaf.RealStratificationExamples

/-!
# Fixtures for interval-local constancy

* The constant sheaf with no breakpoints is locally constant on the whole line. The
  trivialisation identifies its global sections with its sections over `(0, 1)`, and its stalks
  are one-dimensional.
* The point sheaf (the field at the breakpoint `0`, zero on both cells) is locally constant on
  the right cell `(0, ∞)`, where its stalks vanish. It is not locally constant on the whole line:
  the trivialisation would identify its one-dimensional sections over `(-1, 3)` with its zero
  sections over `(1, 2)`.
-/

namespace TDA.Sheaf.LocalSystemExamples

open CategoryTheory TopologicalSpace Opposite TDA.Persistence TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.RealStratification
  TDA.Sheaf.RealStratificationExamples TDA.Sheaf.LocalSystem

variable (k : Type) [Field k]

/-! ### The constant sheaf -/

/-- The constant sheaf with no breakpoints is locally constant on the whole line. -/
theorem isLocallyConstantOn_constLineSheaf :
    IsLocallyConstantOn (constLineSheaf k ∅) Set.univ := by
  intro x _
  refine ⟨⊤, Set.mem_univ x, Set.subset_univ _, fun V W hVW hVne hVc hWc _ => ?_⟩
  exact isIso_map_basisEquiv k ⟨_, isSheaf_const k ∅⟩
    (U := ⟨V, isBasicOpen_empty hVne hVc⟩) (V := ⟨W, isBasicOpen_empty (hVne.mono hVW) hWc⟩)
    (InducedCategory.homMk (homOfLE hVW)) (by
      simp only [Functor.const_obj_map]
      infer_instance)

/-- The trivialisation for the constant sheaf: its global sections restrict isomorphically to
`(0, 1)`. -/
theorem isIso_constLineSheaf_map_ioo :
    IsIso ((constLineSheaf k ∅).obj.map (homOfLE (le_top : ioo 0 1 ≤ ⊤)).op) :=
  restrict_isIso_of_isLocallyConstantOn _ _ (Set.nonempty_Ioo.2 zero_lt_one) Set.ordConnected_Ioo
    (by rw [Opens.coe_top]; exact Set.ordConnected_univ)
    (by rw [Opens.coe_top]; exact isLocallyConstantOn_constLineSheaf k)

/-- Every stalk of the constant sheaf is one-dimensional. -/
theorem finrank_stalk_constLineSheaf (x : ℝ) :
    Module.finrank k ((TopCat.Sheaf.presheaf (constLineSheaf k ∅)).stalk x) = 1 := by
  have hc : ((⊤ : Opens realLine) : Set ℝ).OrdConnected := by
    rw [Opens.coe_top]
    exact Set.ordConnected_univ
  have hF : IsLocallyConstantOn (constLineSheaf k ∅) (⊤ : Opens realLine) := by
    rw [Opens.coe_top]
    exact isLocallyConstantOn_constLineSheaf k
  have := isIso_germ_of_isLocallyConstantOn _ hc hF (Set.mem_univ x)
  rw [← (asIso ((TopCat.Sheaf.presheaf (constLineSheaf k ∅)).germ ⊤ x (Set.mem_univ x)))
    |>.toLinearEquiv.finrank_eq, (constLineSheafSectionsIso k ∅
      ⟨⊤, isBasicOpen_empty ⟨0, Set.mem_univ 0⟩ hc⟩).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-! ### The point sheaf -/

/-- The point sheaf is locally constant on the right cell `(0, ∞)`. -/
theorem isLocallyConstantOn_pointLineSheaf_Ioi :
    IsLocallyConstantOn (pointLineSheaf k) (Set.Ioi 0) := by
  intro x hx
  refine ⟨⟨Set.Ioi 0, isOpen_Ioi⟩, hx, subset_rfl, fun V W hVW hVne hVc hWc hWN => ?_⟩
  have hW0 : (0 : ℝ) ∉ (W : Set ℝ) := fun h => lt_irrefl (0 : ℝ) (hWN h)
  have hV0 : (0 : ℝ) ∉ (V : Set ℝ) := fun h => hW0 (hVW h)
  have inter : ∀ U : Opens realLine, (0 : ℝ) ∉ (U : Set ℝ) →
      (U : Set ℝ) ∩ breakpoints p₁ = ∅ := fun U h => by
    rw [breakpoints_p₁, Finset.coe_singleton]
    exact Set.inter_singleton_eq_empty.2 h
  have basic : ∀ U : Opens realLine, (U : Set ℝ).Nonempty → (U : Set ℝ).OrdConnected →
      (0 : ℝ) ∉ (U : Set ℝ) → IsBasicOpen (breakpoints p₁) U := fun U hne hc h0 =>
    ⟨hne, hc, by rw [inter U h0]; exact Set.subsingleton_empty⟩
  let U₁ : BasicCat (breakpoints p₁) := ⟨V, basic V hVne hVc hV0⟩
  let U₂ : BasicCat (breakpoints p₁) := ⟨W, basic W (hVne.mono hVW) hWc hW0⟩
  let f : U₁ ⟶ U₂ := InducedCategory.homMk (homOfLE hVW)
  have := isIso_tauFunctor_map p₁_strictMono f (by rw [inter V hV0, inter W hW0])
  exact isIso_map_basisEquiv k ⟨_, isSheaf_point k⟩ f
    (inferInstance : IsIso ((pointDiagram k).map ((tauFunctor p₁_strictMono).map f.op)))

/-- The stalk of the point sheaf at `3/2`, inside the right cell, vanishes. -/
theorem finrank_stalk_pointLineSheaf_right :
    Module.finrank k ((TopCat.Sheaf.presheaf (pointLineSheaf k)).stalk (3 / 2 : ℝ)) = 0 := by
  have hx : (3 / 2 : ℝ) ∈ ioo 1 2 := ⟨by norm_num, by norm_num⟩
  have hF : IsLocallyConstantOn (pointLineSheaf k) (ioo 1 2 : Opens realLine) :=
    (isLocallyConstantOn_pointLineSheaf_Ioi k).mono (ioo 1 2).isOpen
      fun y hy => (zero_lt_one' ℝ).trans hy.1
  have := isIso_germ_of_isLocallyConstantOn _ Set.ordConnected_Ioo hF hx
  rw [← (asIso ((TopCat.Sheaf.presheaf (pointLineSheaf k)).germ (ioo 1 2) _ hx))
    |>.toLinearEquiv.finrank_eq]
  exact finrank_pointLineSheaf_right k

/-- Over `(-1, 3)` the point sheaf has one-dimensional sections. -/
theorem finrank_pointLineSheaf_wide :
    Module.finrank k ((pointLineSheaf k).obj.obj (op (ioo (-1) 3))) = 1 := by
  rw [(pointLineSheafSectionsIso k ⟨ioo (-1) 3, isBasicOpen_ioo (by norm_num)⟩).toLinearEquiv
    |>.finrank_eq, tau_wide, finrank_interval_obj]
  decide

/-- The point sheaf is not locally constant on the whole line. -/
theorem not_isLocallyConstantOn_pointLineSheaf_univ :
    ¬IsLocallyConstantOn (pointLineSheaf k) Set.univ := by
  intro hF
  have hle : ioo 1 2 ≤ ioo (-1) 3 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have := restrict_isIso_of_isLocallyConstantOn (pointLineSheaf k) hle
    (Set.nonempty_Ioo.2 (by norm_num)) Set.ordConnected_Ioo Set.ordConnected_Ioo
    (hF.mono (ioo (-1) 3).isOpen (Set.subset_univ _))
  have h := (asIso ((pointLineSheaf k).obj.map (homOfLE hle).op)).toLinearEquiv.finrank_eq
  rw [finrank_pointLineSheaf_wide, finrank_pointLineSheaf_right] at h
  exact one_ne_zero h

end TDA.Sheaf.LocalSystemExamples
