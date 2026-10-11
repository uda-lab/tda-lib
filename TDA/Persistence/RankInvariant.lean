import TDA.Persistence.Interval
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

universe u
namespace TDA.Persistence
open CategoryTheory
variable {N : ℕ} {k : Type u} [Field k]
variable (M : PModule.{u,0,u} k (Fin N))
variable [∀ i : Fin N, FiniteDimensional k (M.obj i)]

noncomputable def moduleRankInteger (i j : ℤ) : ℤ := by
  classical
  exact if h : 0 ≤ i ∧ i ≤ j ∧ j < (N : ℤ) then
    let hi : (i.toNat : ℤ) = i := Int.toNat_of_nonneg h.1
    let hj : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (h.1.trans h.2.1)
    let fi : Fin N := ⟨i.toNat, by
      have hlt : i < (N : ℤ) := h.2.1.trans_lt h.2.2
      have hlt' : (i.toNat : ℤ) < (N : ℤ) := by rw [hi]; exact hlt
      exact_mod_cast hlt'⟩
    let fj : Fin N := ⟨j.toNat, by
      have hlt' : (j.toNat : ℤ) < (N : ℤ) := by rw [hj]; exact h.2.2
      exact_mod_cast hlt'⟩
    let hFin : fi ≤ fj := Fin.le_iff_val_le_val.mpr (by
      have hle : (i.toNat : ℤ) ≤ (j.toNat : ℤ) := by rw [hi, hj]; exact h.2.1
      exact_mod_cast hle)
    (structureMapRank M fi fj hFin : ℤ)
  else 0

noncomputable def moduleMultiplicityInteger (b d : ℕ) : ℤ :=
  moduleRankInteger M (b : ℤ) ((d : ℤ) - 1) -
  moduleRankInteger M ((b : ℤ) - 1) ((d : ℤ) - 1) -
  moduleRankInteger M (b : ℤ) (d : ℤ) +
  moduleRankInteger M ((b : ℤ) - 1) (d : ℤ)

theorem moduleRankInteger_fin (i j : Fin N) (hij : i ≤ j) :
    moduleRankInteger M (i.val : ℤ) (j.val : ℤ) =
      (structureMapRank M i j hij : ℤ) := by
  have hvalid : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ (j.val : ℤ) ∧
      (j.val : ℤ) < (N : ℤ) := by
    exact ⟨by positivity, by exact_mod_cast Fin.le_iff_val_le_val.mp hij,
      by exact_mod_cast j.isLt⟩
  unfold moduleRankInteger
  rw [dif_pos hvalid]
  dsimp

theorem moduleRankInteger_neg_one (j : ℤ) :
    moduleRankInteger M (-1) j = 0 := by
  simp [moduleRankInteger]

theorem moduleRankInteger_at_size (i : ℤ) :
    moduleRankInteger M i (N : ℤ) = 0 := by
  simp [moduleRankInteger]

omit [∀ i : Fin N, FiniteDimensional k (M.obj i)] in
private theorem image_le {a b c : Fin N} (hab : a ≤ b) (hbc : b ≤ c) :
    LinearMap.range (structureMapLinear M (hab.trans hbc)) ≤
      LinearMap.range (structureMapLinear M hbc) := by
  rw [structureMapLinear_comp M hab hbc]
  exact LinearMap.range_comp_le_range _ _

theorem structureMapRank_mono_source (a b c : Fin N)
    (hab : a ≤ b) (hbc : b ≤ c) :
    structureMapRank M a c (hab.trans hbc) ≤ structureMapRank M b c hbc := by
  unfold structureMapRank
  exact Submodule.finrank_mono (image_le M hab hbc)

omit [∀ i : Fin N, FiniteDimensional k (M.obj i)] in
private theorem range_restricted {a c d : Fin N} (hac : a ≤ c) (hcd : c ≤ d) :
    LinearMap.range ((structureMapLinear M hcd).comp
      (LinearMap.range (structureMapLinear M hac)).subtype) =
    LinearMap.range (structureMapLinear M (hac.trans hcd)) := by
  rw [structureMapLinear_comp M hac hcd]
  rw [LinearMap.range_comp, Submodule.range_subtype]
  exact (LinearMap.range_comp (structureMapLinear M hac) (structureMapLinear M hcd)).symm

theorem structureMapRank_drop (a c d : Fin N)
    (hac : a ≤ c) (hcd : c ≤ d) :
    structureMapRank M a c hac =
      structureMapRank M a d (hac.trans hcd) +
        Module.finrank k (LinearMap.ker
          ((structureMapLinear M hcd).comp
            (LinearMap.range (structureMapLinear M hac)).subtype)) := by
  let U := LinearMap.range (structureMapLinear M hac)
  let g := structureMapLinear M hcd
  let f := g.comp U.subtype
  have hr := LinearMap.finrank_range_add_finrank_ker f
  have he : LinearMap.range f = LinearMap.range (structureMapLinear M (hac.trans hcd)) :=
    range_restricted M hac hcd
  unfold structureMapRank
  rw [← he]
  exact hr.symm

omit [∀ i : Fin N, FiniteDimensional k (M.obj i)] in
private theorem ker_restricted_finrank {c d : Fin N} (hcd : c ≤ d)
    (U : Submodule k (M.obj c)) :
    Module.finrank k (LinearMap.ker ((structureMapLinear M hcd).comp U.subtype)) =
      Module.finrank k (U ⊓ LinearMap.ker (structureMapLinear M hcd) :
        Submodule k (M.obj c)) := by
  rw [← Submodule.finrank_map_subtype_eq U
    (LinearMap.ker ((structureMapLinear M hcd).comp U.subtype))]
  change Module.finrank k (Submodule.map U.subtype
    (LinearMap.ker ((structureMapLinear M hcd).domRestrict U))) = _
  rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]

theorem structureMapRank_four_le (a b c d : Fin N)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    structureMapRank M a c (hab.trans hbc) + structureMapRank M b d (hbc.trans hcd) ≤
      structureMapRank M b c hbc + structureMapRank M a d ((hab.trans hbc).trans hcd) := by
  let U := LinearMap.range (structureMapLinear M (hab.trans hbc))
  let W := LinearMap.range (structureMapLinear M hbc)
  let g := structureMapLinear M hcd
  have hUW : U ≤ W := image_le M hab hbc
  have hker : Module.finrank k (LinearMap.ker (g.comp U.subtype)) ≤
      Module.finrank k (LinearMap.ker (g.comp W.subtype)) := by
    rw [ker_restricted_finrank M hcd U, ker_restricted_finrank M hcd W]
    exact Submodule.finrank_mono (inf_le_inf_right _ hUW)
  have hU := structureMapRank_drop M a c d (hab.trans hbc) hcd
  have hW := structureMapRank_drop M b c d hbc hcd
  change structureMapRank M a c (hab.trans hbc) =
    structureMapRank M a d ((hab.trans hbc).trans hcd) +
    Module.finrank k (LinearMap.ker (g.comp U.subtype)) at hU
  change structureMapRank M b c hbc = structureMapRank M b d (hbc.trans hcd) +
    Module.finrank k (LinearMap.ker (g.comp W.subtype)) at hW
  omega

private theorem rank_nat (i j : ℕ) (hij : i ≤ j) (hj : j < N) :
    moduleRankInteger M (i : ℤ) (j : ℤ) =
      structureMapRank M ⟨i, by omega⟩ ⟨j, hj⟩
        (Fin.le_iff_val_le_val.mpr hij) := by
  exact moduleRankInteger_fin M ⟨i, by omega⟩ ⟨j, hj⟩
    (Fin.le_iff_val_le_val.mpr hij)

theorem moduleMultiplicityInteger_nonneg (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    0 ≤ moduleMultiplicityInteger M b d := by
  have hdpos : 0 < d := by omega
  have hcN : d - 1 < N := by omega
  have hc : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  by_cases hb : b = 0
  · subst b
    have hzero₁ := moduleRankInteger_neg_one M ((d : ℤ) - 1)
    have hzero₂ := moduleRankInteger_neg_one M (d : ℤ)
    by_cases hterminal : d = N
    · subst d
      have hr := rank_nat M 0 (N - 1) (by omega) hcN
      simp only [Nat.cast_zero] at hr
      have ht₁ := moduleRankInteger_at_size M (0 : ℤ)
      simp only [moduleMultiplicityInteger, Nat.cast_zero, zero_sub]
      rw [hzero₁, hzero₂, ht₁, ← hc, hr]
      omega
    · have hdn : d < N := by omega
      have hrc := rank_nat M 0 (d - 1) (by omega) hcN
      have hrd := rank_nat M 0 d (by omega) hdn
      simp only [Nat.cast_zero] at hrc hrd
      let a : Fin N := ⟨0, by omega⟩
      let c : Fin N := ⟨d - 1, hcN⟩
      let e : Fin N := ⟨d, hdn⟩
      have hac : a ≤ c := by
        apply Fin.le_iff_val_le_val.mpr
        change 0 ≤ d - 1
        omega
      have hce : c ≤ e := by
        apply Fin.le_iff_val_le_val.mpr
        change d - 1 ≤ d
        omega
      have hdrop := structureMapRank_drop M a c e hac hce
      simp only [moduleMultiplicityInteger, Nat.cast_zero, zero_sub]
      rw [hzero₁, hzero₂, ← hc, hrc, hrd]
      change 0 ≤ (structureMapRank M a c _ : ℤ) - 0 -
        (structureMapRank M a e _ : ℤ) + 0
      omega
  · have hbpos : 0 < b := by omega
    have ha : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
    have hab : b - 1 ≤ b := by omega
    have hbc : b ≤ d - 1 := by omega
    by_cases hterminal : d = N
    · subst d
      have hrb := rank_nat M b (N - 1) hbc hcN
      have hra := rank_nat M (b - 1) (N - 1) (by omega) hcN
      have ht₁ := moduleRankInteger_at_size M (b : ℤ)
      have ht₂ := moduleRankInteger_at_size M ((b : ℤ) - 1)
      let a : Fin N := ⟨b - 1, by omega⟩
      let bb : Fin N := ⟨b, by omega⟩
      let c : Fin N := ⟨N - 1, hcN⟩
      have hmono := structureMapRank_mono_source M a bb c
        (Fin.le_iff_val_le_val.mpr hab) (Fin.le_iff_val_le_val.mpr hbc)
      unfold moduleMultiplicityInteger
      rw [ht₁, ht₂, ← hc, ← ha, hrb, hra]
      change 0 ≤ (structureMapRank M bb c _ : ℤ) -
        (structureMapRank M a c _ : ℤ) - 0 + 0
      omega
    · have hdn : d < N := by omega
      let a : Fin N := ⟨b - 1, by omega⟩
      let bb : Fin N := ⟨b, by omega⟩
      let c : Fin N := ⟨d - 1, hcN⟩
      let e : Fin N := ⟨d, hdn⟩
      have h₁ := rank_nat M b (d - 1) hbc hcN
      have h₂ := rank_nat M (b - 1) (d - 1) (by omega) hcN
      have h₃ := rank_nat M b d (by omega) hdn
      have h₄ := rank_nat M (b - 1) d (by omega) hdn
      have hce : c ≤ e := by
        apply Fin.le_iff_val_le_val.mpr
        change d - 1 ≤ d
        omega
      have hfour := structureMapRank_four_le M a bb c e
        (Fin.le_iff_val_le_val.mpr hab)
        (Fin.le_iff_val_le_val.mpr hbc) hce
      unfold moduleMultiplicityInteger
      rw [← hc, ← ha, h₁, h₂, h₃, h₄]
      change 0 ≤ (structureMapRank M bb c _ : ℤ) -
        (structureMapRank M a c _ : ℤ) -
        (structureMapRank M bb e _ : ℤ) +
        (structureMapRank M a e _ : ℤ)
      omega
