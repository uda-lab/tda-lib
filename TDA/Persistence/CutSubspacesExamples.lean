import TDA.Persistence.CutSubspaces

set_option autoImplicit false

namespace TDA.Persistence.CutSubspacesExamples

open TDA.Persistence
open TDA.Persistence.Cut
open CategoryTheory

/-- The cut whose lower side is strictly before `a`. -/
def cutBefore (a : ℝ) : Cut ℝ where
  lower := Set.Iio a
  upper := Set.Ici a
  mem_lower_or_upper x := lt_or_ge x a
  lower_lt_upper := by
    intro x y hx hy
    exact lt_of_lt_of_le hx hy

/-- The cut whose lower side includes `a`. -/
def cutAfter (a : ℝ) : Cut ℝ where
  lower := Set.Iic a
  upper := Set.Ioi a
  mem_lower_or_upper x := le_or_gt x a
  lower_lt_upper := by
    intro x y hx hy
    exact lt_of_le_of_lt hx hy

theorem support_before_after (a b : ℝ) :
    support (cutBefore a) (cutAfter b) = Set.Icc a b := by
  ext x
  simp [support, cutBefore, cutAfter]

theorem support_after_before (a b : ℝ) :
    support (cutAfter a) (cutBefore b) = Set.Ioo a b := by
  ext x
  simp [support, cutBefore, cutAfter]

theorem support_before_after_singleton (a : ℝ) :
    support (cutBefore a) (cutAfter a) = {a} := by
  simp [support_before_after]

theorem support_before_after_empty_of_reversed {a b : ℝ} (hba : b < a) :
    support (cutBefore a) (cutAfter b) = ∅ := by
  rw [support_before_after]
  ext x
  simp only [Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact (not_lt_of_ge (hx.1.trans hx.2)) hba

/-- The persistence module with a rational line in every fiber and zero maps across
strict inequalities. Its singleton fibers model the ephemeral summands that an interval
decomposition must retain. -/
noncomputable def ephemeralModule : PModule.{0,0,0} ℚ ℝ where
  obj _ := ModuleCat.of ℚ ℚ
  map {s t} _ := if s = t then 𝟙 (ModuleCat.of ℚ ℚ) else 0
  map_id t := by simp
  map_comp {s t r} f g := by
    have hstOrd : s ≤ t := leOfHom f
    have htrOrd : t ≤ r := leOfHom g
    by_cases hst : s = t
    · subst t
      by_cases htr : s = r
      · subst r
        simp
      · simp [htr]
    · by_cases htr : t = r
      · subst r
        simp [hst]
      · have hsr : s ≠ r := by
          intro hsr
          have hrs : r ≤ s := hsr ▸ le_rfl
          have hts : t ≤ s := htrOrd.trans hrs
          exact hst (le_antisymm hstOrd hts)
        simp [hst, htr, hsr]

theorem ephemeralModule_pfd (t : ℝ) :
    FiniteDimensional ℚ (ephemeralModule.obj t) := by
  change FiniteDimensional ℚ ℚ
  infer_instance

theorem ephemeralModule_strict_map_zero {s t : ℝ} (h : s < t) :
    structureMapLinear ephemeralModule h.le = 0 := by
  simp [structureMapLinear, structureMap, ephemeralModule, ne_of_lt h]
  rfl

theorem ephemeralModule_self_map (t : ℝ) :
    structureMapLinear ephemeralModule (le_rfl : t ≤ t) = LinearMap.id := by
  simp [structureMapLinear, structureMap, ephemeralModule]
  rfl

theorem ephemeral_imagePlus_singleton_eq_top (t : ℝ) :
    imagePlus ephemeralModule (cutBefore t) t = ⊤ := by
  apply top_unique
  intro x _
  simp only [imagePlus, Submodule.mem_iInf]
  intro s
  have hst : s.val = t := le_antisymm s.property.2 (by
    simpa [cutBefore] using s.property.1)
  have hmap : structureMapLinear ephemeralModule s.property.2 = LinearMap.id := by
    simp [structureMapLinear, structureMap, ephemeralModule, ← hst]
    rfl
  rw [hmap]
  exact ⟨x, rfl⟩

theorem ephemeral_imageMinus_singleton_eq_bot (t : ℝ) :
    imageMinus ephemeralModule (cutBefore t) t = ⊥ := by
  apply le_antisymm
  · rw [imageMinus]
    apply iSup_le
    intro s
    have hst : s.val < t := s.property.1
    rw [ephemeralModule_strict_map_zero hst]
    simp
  · exact bot_le

theorem ephemeral_kernelPlus_singleton_eq_top (t : ℝ) :
    kernelPlus ephemeralModule (cutAfter t) t = ⊤ := by
  apply top_unique
  intro x _
  simp only [kernelPlus, Submodule.mem_iInf]
  intro s
  have hts : t < s.val := by simpa [cutAfter] using s.property.1
  rw [ephemeralModule_strict_map_zero hts, LinearMap.mem_ker]
  simp

theorem ephemeral_kernelMinus_singleton_eq_bot (t : ℝ) :
    kernelMinus ephemeralModule (cutAfter t) t = ⊥ := by
  apply le_antisymm
  · rw [kernelMinus]
    apply iSup_le
    intro s
    have hst : s.val = t := le_antisymm (by
      simpa [cutAfter] using s.property.1) s.property.2
    have hmap : structureMapLinear ephemeralModule s.property.2 = LinearMap.id := by
      simp [structureMapLinear, structureMap, ephemeralModule, ← hst]
      rfl
    rw [hmap]
    intro x hx
    have hx0 : LinearMap.id x = 0 := LinearMap.mem_ker.mp hx
    change x = 0
    simpa only [LinearMap.id_apply] using hx0
  · exact bot_le

theorem ephemeral_singleton_interval_spaces (t : ℝ) :
    intervalPlus ephemeralModule (cutBefore t) (cutAfter t) t = ⊤ ∧
      intervalMinus ephemeralModule (cutBefore t) (cutAfter t) t = ⊥ := by
  constructor
  · simp [intervalPlus, ephemeral_imagePlus_singleton_eq_top,
      ephemeral_kernelPlus_singleton_eq_top]
  · simp [intervalMinus, ephemeral_imagePlus_singleton_eq_top,
      ephemeral_imageMinus_singleton_eq_bot, ephemeral_kernelPlus_singleton_eq_top,
      ephemeral_kernelMinus_singleton_eq_bot]

end TDA.Persistence.CutSubspacesExamples
