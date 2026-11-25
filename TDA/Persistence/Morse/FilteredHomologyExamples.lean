import TDA.Persistence.Morse.FilteredHomology
import TDA.Persistence.Morse.FilteredContractionExamples

/-!
# Fixtures for grade-sublevel homology

Evaluations of `TDA.Persistence.Morse.Cancellation.sublevelHomology` over `ZMod 2`, on the
filled triangle of `TDA.Persistence.Morse.UnitCancellationExamples` with the grade `cGrade` of
`TDA.Persistence.Morse.FilteredContractionExamples` (A, B, C, AB, BC at 0, CA at 1, ABC at 2),
and on its critical complex `Crit` (A, CA, ABC, with the single differential entry
`d ABC = CA`).

* H1. The critical complex, computed directly: `H₀` has dimension 1 at every grade `t ≥ 0`
  and 0 below; `H₁` has dimension 1 at grade 1 and 0 at every other grade; `H₂` and every
  `H_p` with `p ≥ 3` vanish.
* H2. The same dimensions for the triangle, through `critFlat.finrank_sublevelHomology_eq`.
* H3. The lift `incl (CA) = AB + BC + CA` is a cycle at grade 1 whose class is not zero, and
  the degree-1 structure map from grade 1 to grade 2 of the triangle's persistence module is
  zero: the cycle is born at grade 1 and filled at grade 2.

The critical-complex computations are short `simp` and case arguments; the matrix value
`critFlat_incl_mulVec_cCA` is a kernel `decide`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.FilteredHomologyExamples

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation
open TDA.Persistence.Morse.UnitCancellationExamples
open TDA.Persistence.Morse.FilteredContractionExamples

/-- The degree of the critical cells, inherited from the triangle. -/
abbrev critDegree : Crit → ℕ := tDegree ∘ Subtype.val

/-- The grade of the critical cells, inherited from `cGrade`. -/
abbrev critGrade : Crit → ℤ := cGrade ∘ Subtype.val

/-- The critical cells are exactly A, CA and ABC. -/
private theorem crit_cases (r : Crit) : r = cA ∨ r = cCA ∨ r = cABC := by
  revert r; decide +kernel

private theorem critDegree_cA : critDegree cA = 0 := by decide +kernel
private theorem critDegree_cCA : critDegree cCA = 1 := by decide +kernel
private theorem critDegree_cABC : critDegree cABC = 2 := by decide +kernel
private theorem critGrade_cA : critGrade cA = 0 := by decide +kernel
private theorem critGrade_cCA : critGrade cCA = 1 := by decide +kernel
private theorem critGrade_cABC : critGrade cABC = 2 := by decide +kernel

private theorem cA_ne_cCA : cA ≠ cCA := by decide
private theorem cA_ne_cABC : cA ≠ cABC := by decide
private theorem cCA_ne_cABC : cCA ≠ cABC := by decide

private theorem critD_mulVec (y : Crit → ZMod 2) :
    critD.mulVec y = Pi.single cCA (y cABC) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, critD, ite_mul, one_mul, zero_mul, Pi.single_apply]
  by_cases hr : r = cCA
  · subst hr; simp
  · simp [hr]

/-- A vector supported in a single degree `p` that only `g` has, is a multiple of `single g`. -/
private theorem eq_smul_single {g : Crit} {p : ℕ} (hg : critDegree g = p)
    (hother : ∀ r, r ≠ g → critDegree r ≠ p) {x : Crit → ZMod 2}
    (hx : DegreeSupported critDegree p x) : x = x g • Pi.single g 1 := by
  funext r
  by_cases hr : r = g
  · subst hr; simp
  · simp [hr, hx r (hother r hr)]

private theorem only_cA (r : Crit) (h : r ≠ cA) : critDegree r ≠ 0 := by
  rcases crit_cases r with rfl | rfl | rfl
  · exact absurd rfl h
  · decide +kernel
  · decide +kernel

private theorem only_cCA (r : Crit) (h : r ≠ cCA) : critDegree r ≠ 1 := by
  rcases crit_cases r with rfl | rfl | rfl
  · decide +kernel
  · exact absurd rfl h
  · decide +kernel

private theorem only_cABC (r : Crit) (h : r ≠ cABC) : critDegree r ≠ 2 := by
  rcases crit_cases r with rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · exact absurd rfl h

private theorem single_mem_sublevelChains {g : Crit} {p : ℕ} {t : ℤ} (hg : critDegree g = p)
    (ht : critGrade g ≤ t) :
    Pi.single g (1 : ZMod 2) ∈ sublevelChains critDegree critGrade p t := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have : r ≠ g := fun e => hr (e ▸ hg)
    simp [this]
  · have : r ≠ g := fun e => by subst e; omega
    simp [this]

/-- A class whose cycles are the multiples of one cycle `single g` that is not a boundary has
dimension one. -/
private theorem finrank_eq_one_of {g : Crit} {p : ℕ} {t : ℤ} (hg : critDegree g = p)
    (hother : ∀ r, r ≠ g → critDegree r ≠ p) (ht : critGrade g ≤ t)
    (hcyc : critD.mulVec (Pi.single g 1) = 0)
    (hnb : Pi.single g (1 : ZMod 2) ∉ sublevelBoundaries critDegree critGrade critD p t) :
    Module.finrank (ZMod 2) (sublevelHomology critDegree critGrade critD p t) = 1 := by
  have hmem : Pi.single g (1 : ZMod 2) ∈ sublevelCycles critDegree critGrade critD p t :=
    mem_sublevelCycles.mpr ⟨(single_mem_sublevelChains hg ht).1,
      (single_mem_sublevelChains hg ht).2, hcyc⟩
  refine (finrank_eq_one_iff_of_nonzero' (Submodule.Quotient.mk ⟨_, hmem⟩) ?_).mpr ?_
  · rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hnb
  · intro w
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨(x : Crit → ZMod 2) g, ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (eq_smul_single hg hother (mem_sublevelCycles.mp x.2).1).symm

/-- Every cycle is a boundary, so the homology is trivial. -/
private theorem subsingleton_of {p : ℕ} {t : ℤ}
    (h : ∀ x ∈ sublevelCycles critDegree critGrade critD p t,
      x ∈ sublevelBoundaries critDegree critGrade critD p t) :
    Subsingleton (sublevelHomology critDegree critGrade critD p t) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ b
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact h _ (sub_mem x.2 y.2)

/-- With no nonzero chain of degree `p` in grades `≤ t`, the homology is trivial. -/
private theorem finrank_eq_zero_of_chains {p : ℕ} {t : ℤ}
    (h : ∀ x ∈ sublevelChains critDegree critGrade p t, x = (0 : Crit → ZMod 2)) :
    Module.finrank (ZMod 2) (sublevelHomology critDegree critGrade critD p t) = 0 := by
  have := subsingleton_of (p := p) (t := t) fun x hx => by
    obtain ⟨h₁, h₂, -⟩ := mem_sublevelCycles.mp hx
    rw [h x ⟨h₁, h₂⟩]
    exact Submodule.zero_mem _
  exact Module.finrank_zero_of_subsingleton

/-- Below the grade of the only generator `g` of degree `p`, every chain vanishes. -/
private theorem chains_eq_zero_of_lt {g : Crit} {p : ℕ} {t : ℤ} (hg : critDegree g = p)
    (hother : ∀ r, r ≠ g → critDegree r ≠ p) (ht : t < critGrade g) :
    ∀ x ∈ sublevelChains critDegree critGrade p t, x = (0 : Crit → ZMod 2) := by
  intro x hx
  rw [eq_smul_single hg hother hx.1, hx.2 g ht, zero_smul]

/-! ## The critical complex -/

/-- `H₀` of the critical complex has dimension one at every grade `t ≥ 0`. -/
theorem crit_finrank_zero (t : ℤ) (ht : 0 ≤ t) :
    Module.finrank (ZMod 2) (sublevelHomology critDegree critGrade critD 0 t) = 1 := by
  refine finrank_eq_one_of critDegree_cA only_cA (critGrade_cA ▸ ht) ?_ ?_
  · rw [critD_mulVec]; simp [cA_ne_cABC.symm]
  · intro hb
    obtain ⟨y, -, -, hy⟩ := mem_sublevelBoundaries.mp hb
    have := congrFun hy cA
    rw [critD_mulVec] at this
    simp [cA_ne_cCA] at this

/-- `H₁` of the critical complex has dimension one at grade 1. -/
theorem crit_finrank_one_one :
    Module.finrank (ZMod 2) (sublevelHomology critDegree critGrade critD 1 1) = 1 := by
  refine finrank_eq_one_of critDegree_cCA only_cCA critGrade_cCA.le ?_ ?_
  · rw [critD_mulVec]; simp [cCA_ne_cABC.symm]
  · intro hb
    obtain ⟨y, -, hy', hy⟩ := mem_sublevelBoundaries.mp hb
    have h0 : y cABC = 0 := hy' cABC (by rw [critGrade_cABC]; decide)
    have := congrFun hy cCA
    rw [critD_mulVec, h0] at this
    revert this; simp

/-- `H₁` of the critical complex vanishes at every grade `t ≥ 2`. -/
theorem crit_subsingleton_one (t : ℤ) (ht : 2 ≤ t) :
    Subsingleton (sublevelHomology critDegree critGrade critD 1 t) := by
  refine subsingleton_of fun x hx => ?_
  obtain ⟨h₁, -, -⟩ := mem_sublevelCycles.mp hx
  refine mem_sublevelBoundaries.mpr ⟨x cCA • Pi.single cABC 1,
    (Submodule.smul_mem _ _ (single_mem_sublevelChains critDegree_cABC
      (critGrade_cABC ▸ ht))).1,
    (Submodule.smul_mem _ _ (single_mem_sublevelChains critDegree_cABC
      (critGrade_cABC ▸ ht))).2, ?_⟩
  rw [critD_mulVec, eq_smul_single critDegree_cCA only_cCA h₁]
  funext r
  by_cases hr : r = cCA
  · subst hr; simp
  · simp [hr]

/-- `H₁` of the critical complex vanishes at every grade `t ≥ 2`. -/
theorem crit_finrank_one (t : ℤ) (ht : 2 ≤ t) :
    Module.finrank (ZMod 2) (sublevelHomology critDegree critGrade critD 1 t) = 0 :=
  have := crit_subsingleton_one t ht
  Module.finrank_zero_of_subsingleton

/-- `H₂` of the critical complex vanishes at every grade. -/
theorem crit_finrank_two (t : ℤ) :
    Module.finrank (ZMod 2) (sublevelHomology critDegree critGrade critD 2 t) = 0 := by
  have := subsingleton_of (p := 2) (t := t) fun x hx => ?_
  · exact Module.finrank_zero_of_subsingleton
  obtain ⟨h₁, -, h₃⟩ := mem_sublevelCycles.mp hx
  have hx0 : x = 0 := by
    rw [eq_smul_single critDegree_cABC only_cABC h₁] at h₃ ⊢
    have := congrFun h₃ cCA
    rw [critD_mulVec] at this
    have hc : x cABC = 0 := by simpa using this
    simp [hc]
  rw [hx0]
  exact Submodule.zero_mem _

/-- `H₀` of the critical complex vanishes below grade 0. -/
theorem crit_finrank_zero_of_lt (t : ℤ) (ht : t < 0) :
    Module.finrank (ZMod 2) (sublevelHomology critDegree critGrade critD 0 t) = 0 :=
  finrank_eq_zero_of_chains (chains_eq_zero_of_lt critDegree_cA only_cA (critGrade_cA ▸ ht))

/-- `H₁` of the critical complex vanishes below grade 1. -/
theorem crit_finrank_one_of_lt (t : ℤ) (ht : t < 1) :
    Module.finrank (ZMod 2) (sublevelHomology critDegree critGrade critD 1 t) = 0 :=
  finrank_eq_zero_of_chains (chains_eq_zero_of_lt critDegree_cCA only_cCA (critGrade_cCA ▸ ht))

/-- The critical complex has no generator of degree `p ≥ 3`. -/
theorem crit_finrank_of_three_le (p : ℕ) (hp : 3 ≤ p) (t : ℤ) :
    Module.finrank (ZMod 2) (sublevelHomology critDegree critGrade critD p t) = 0 := by
  refine finrank_eq_zero_of_chains fun x hx => funext fun r => hx.1 r ?_
  rcases crit_cases r with rfl | rfl | rfl
  · rw [critDegree_cA]; omega
  · rw [critDegree_cCA]; omega
  · rw [critDegree_cABC]; omega

/-- The single generator CA of degree 1 and grade 1 is a cycle. -/
theorem crit_single_cCA_mem :
    Pi.single cCA (1 : ZMod 2) ∈ sublevelCycles critDegree critGrade critD 1 1 :=
  mem_sublevelCycles.mpr ⟨(single_mem_sublevelChains critDegree_cCA critGrade_cCA.le).1,
    (single_mem_sublevelChains critDegree_cCA critGrade_cCA.le).2,
    by rw [critD_mulVec]; simp [cCA_ne_cABC.symm]⟩

/-- At grade 1, the class of CA is not zero. -/
theorem crit_class_cCA_ne_zero :
    (Submodule.Quotient.mk ⟨_, crit_single_cCA_mem⟩ :
      sublevelHomology critDegree critGrade critD 1 1) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  intro hb
  obtain ⟨y, -, hy', hy⟩ := mem_sublevelBoundaries.mp hb
  have h0 : y cABC = 0 := hy' cABC (by rw [critGrade_cABC]; decide)
  have := congrFun hy cCA
  rw [critD_mulVec, h0] at this
  revert this; simp

/-! ## The triangle, through the contraction -/

/-- `H₀` of the regraded filled triangle has dimension one at every grade `t ≥ 0`. -/
theorem triangle_finrank_zero (t : ℤ) (ht : 0 ≤ t) :
    Module.finrank (ZMod 2) (sublevelHomology tDegree cGrade tD 0 t) = 1 :=
  (critFlat.finrank_sublevelHomology_eq 0 t).trans (crit_finrank_zero t ht)

/-- `H₁` of the regraded filled triangle has dimension one at grade 1: the cycle
AB + BC + CA. -/
theorem triangle_finrank_one_one :
    Module.finrank (ZMod 2) (sublevelHomology tDegree cGrade tD 1 1) = 1 :=
  (critFlat.finrank_sublevelHomology_eq 1 1).trans crit_finrank_one_one

/-- `H₁` of the regraded filled triangle vanishes at every grade `t ≥ 2`. -/
theorem triangle_finrank_one (t : ℤ) (ht : 2 ≤ t) :
    Module.finrank (ZMod 2) (sublevelHomology tDegree cGrade tD 1 t) = 0 :=
  (critFlat.finrank_sublevelHomology_eq 1 t).trans (crit_finrank_one t ht)

/-- `H₂` of the regraded filled triangle vanishes at every grade. -/
theorem triangle_finrank_two (t : ℤ) :
    Module.finrank (ZMod 2) (sublevelHomology tDegree cGrade tD 2 t) = 0 :=
  (critFlat.finrank_sublevelHomology_eq 2 t).trans (crit_finrank_two t)

/-- `H₀` of the regraded filled triangle vanishes below grade 0. -/
theorem triangle_finrank_zero_of_lt (t : ℤ) (ht : t < 0) :
    Module.finrank (ZMod 2) (sublevelHomology tDegree cGrade tD 0 t) = 0 :=
  (critFlat.finrank_sublevelHomology_eq 0 t).trans (crit_finrank_zero_of_lt t ht)

/-- `H₁` of the regraded filled triangle vanishes below grade 1. -/
theorem triangle_finrank_one_of_lt (t : ℤ) (ht : t < 1) :
    Module.finrank (ZMod 2) (sublevelHomology tDegree cGrade tD 1 t) = 0 :=
  (critFlat.finrank_sublevelHomology_eq 1 t).trans (crit_finrank_one_of_lt t ht)

/-- `H_p` of the regraded filled triangle vanishes for `p ≥ 3`. -/
theorem triangle_finrank_of_three_le (p : ℕ) (hp : 3 ≤ p) (t : ℤ) :
    Module.finrank (ZMod 2) (sublevelHomology tDegree cGrade tD p t) = 0 :=
  (critFlat.finrank_sublevelHomology_eq p t).trans (crit_finrank_of_three_le p hp t)

/-- The cycle AB + BC + CA of the triangle. -/
def triangleCycle : T → ZMod 2 := fun x => if x = tAB ∨ x = tBC ∨ x = tCA then 1 else 0

/-- The inclusion lifts the critical edge CA to the cycle AB + BC + CA. -/
theorem critFlat_incl_mulVec_cCA : critFlat.incl.mulVec (Pi.single cCA 1) = triangleCycle := by
  rw [critFlat_incl]; decide +kernel

/-- `AB + BC + CA` is a degree-1 cycle in grades `≤ 1`. -/
theorem triangleCycle_mem : triangleCycle ∈ sublevelCycles tDegree cGrade tD 1 1 :=
  critFlat_incl_mulVec_cCA ▸ critFlat.incl_mem_sublevelCycles crit_single_cCA_mem

/-- At grade 1, the class of AB + BC + CA is not zero. -/
theorem triangle_class_ne_zero :
    (Submodule.Quotient.mk ⟨triangleCycle, triangleCycle_mem⟩ :
      sublevelHomology tDegree cGrade tD 1 1) ≠ 0 := by
  have h : (critFlat.sublevelHomologyEquiv 1 1).symm
      (Submodule.Quotient.mk ⟨_, crit_single_cCA_mem⟩) =
      Submodule.Quotient.mk ⟨triangleCycle, triangleCycle_mem⟩ := by
    rw [FilteredContraction.sublevelHomologyEquiv_symm_apply,
      FilteredContraction.homologyIncl_mk]
    congr 1
    exact Subtype.ext critFlat_incl_mulVec_cCA
  rw [← h]
  exact (LinearEquiv.map_ne_zero_iff _).mpr crit_class_cCA_ne_zero

/-- The degree-1 structure map of the triangle from grade 1 to grade 2 is zero: the class of
AB + BC + CA, nonzero at grade 1, is filled at grade 2. -/
theorem triangle_structureMap_one_two :
    structureMapLinear (sublevelHomologyPModule tDegree cGrade tD 1)
      (show (1 : ℤ) ≤ 2 by norm_num) = 0 := by
  have := crit_subsingleton_one 2 le_rfl
  have h : Subsingleton (sublevelHomology tDegree cGrade tD 1 2) :=
    (critFlat.sublevelHomologyEquiv 1 2).toEquiv.subsingleton
  exact LinearMap.ext fun _ => @Subsingleton.elim (sublevelHomology tDegree cGrade tD 1 2) h _ _

end TDA.Persistence.Morse.FilteredHomologyExamples
