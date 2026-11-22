import TDA.Persistence.Morse.SimplicialBridge
import TDA.Persistence.Morse.MatchingScheduleExamples

/-!
# Fixtures for the simplicial bridge and the Morse persistence theorem

On the multi-grade square `square` of `TDA.Persistence.Morse.FiniteInputMatchingExamples`, with
the certificate `sqCert` of `TDA.Persistence.Morse.MatchingScheduleExamples`, over `ZMod 2`:

* M1. The Morse complex of `sqCert` on A, AD, ACD has the single entry `d ACD = AD`.
* M2. Its sublevel homology: `H₀` is 1 for `t ≥ 0`; `H₁` is 1 at `t = 1`; all else vanishes.
* M3. The same table for the simplicial homology of the square's grade sublevels, through
  `CertifiedMatching.finrank_simplicialHomology_eq`.
* M4. The rank invariants of the simplicial sublevel persistence module: those of the
  intervals `[1,2)` in degree 1 and `[0,∞)` in degree 0 of `ℤ`.
* M5. The loop AB + BC + CD + AD: its class is not zero at grade 1 and is filled at grade 2.
* M6. The greedy certificate `genCert`, read off the simplicial side through the main theorem.
* M7. The degree-1 diagram `dgm` of the square is `{(1, 2)}`, and the degree-0 one is
  `{(0, ⊤)}`.

Closed computations are kernel `decide`s, after `boundary_eq_coverIncidence`; the homology
values are proved, not evaluated.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.SimplicialBridgeExamples

open CategoryTheory TDA.Simplicial TDA.Persistence.Reduction
open TDA.Persistence.Morse.Cancellation TDA.Persistence.Morse.MatchingInput
open TDA.Persistence.Morse.SimplicialBridge
open TDA.Persistence.Morse.FiniteInputMatchingExamples (square square_valid)
open TDA.Persistence.Morse.IteratedCancellationExamples
open TDA.Persistence.Morse.MatchingScheduleExamples (sqCert sqMorseD sqCert_morseDifferential
  genCert)

/-! ## The Morse complex of `sqCert` -/

/-- The critical generators of the schedule of `sqCert`. -/
abbrev MC := Critical sqCert.schedule

/-- The degrees of the critical generators, inherited from `square`. -/
abbrev mDegree : MC → ℕ := FiniteInput.degree square ∘ Subtype.val

/-- The grades of the critical generators, inherited from `square`. -/
abbrev mGrade : MC → ℤ := (fun i => (square.get i).2) ∘ Subtype.val

/-- The critical vertex A. -/
def mA : MC := ⟨qA, by decide +kernel⟩
/-- The critical edge AD. -/
def mAD : MC := ⟨qAD, by decide +kernel⟩
/-- The critical triangle ACD. -/
def mACD : MC := ⟨qACD, by decide +kernel⟩

/-- The critical generators are exactly A, AD and ACD. -/
theorem mc_cases (r : MC) : r = mA ∨ r = mAD ∨ r = mACD := by
  revert r; decide +kernel

private theorem mDegree_mA : mDegree mA = 0 := by decide +kernel
private theorem mDegree_mAD : mDegree mAD = 1 := by decide +kernel
private theorem mDegree_mACD : mDegree mACD = 2 := by decide +kernel
private theorem mGrade_mA : mGrade mA = 0 := by decide +kernel
private theorem mGrade_mAD : mGrade mAD = 1 := by decide +kernel
private theorem mGrade_mACD : mGrade mACD = 2 := by decide +kernel

private theorem mA_ne_mAD : mA ≠ mAD := by decide +kernel
private theorem mA_ne_mACD : mA ≠ mACD := by decide +kernel
private theorem mAD_ne_mACD : mAD ≠ mACD := by decide +kernel

/-- The Morse differential of `sqCert` on the named generators: only `d ACD = AD`. -/
def mDiff : Matrix MC MC (ZMod 2) := fun r s => if r = mAD ∧ s = mACD then 1 else 0

/-- The Morse differential of `sqCert` is `mDiff`. -/
theorem morseDifferential_eq : sqCert.morseDifferential = mDiff := by
  rw [sqCert_morseDifferential]; decide +kernel

private theorem mD_mulVec (y : MC → ZMod 2) :
    sqCert.morseDifferential.mulVec y = Pi.single mAD (y mACD) := by
  funext r
  simp only [morseDifferential_eq, mDiff, Matrix.mulVec, dotProduct, ite_and, ite_mul, one_mul,
    zero_mul, Pi.single_apply]
  by_cases hr : r = mAD
  · subst hr; simp
  · simp [hr]

private theorem eq_smul_single {g : MC} {p : ℕ} (hg : mDegree g = p)
    (hother : ∀ r, r ≠ g → mDegree r ≠ p) {x : MC → ZMod 2}
    (hx : DegreeSupported mDegree p x) : x = x g • Pi.single g 1 := by
  funext r
  by_cases hr : r = g
  · subst hr; simp
  · simp [hr, hx r (hother r hr)]

private theorem only_mA (r : MC) (h : r ≠ mA) : mDegree r ≠ 0 := by
  rcases mc_cases r with rfl | rfl | rfl
  · exact absurd rfl h
  · decide +kernel
  · decide +kernel

private theorem only_mAD (r : MC) (h : r ≠ mAD) : mDegree r ≠ 1 := by
  rcases mc_cases r with rfl | rfl | rfl
  · decide +kernel
  · exact absurd rfl h
  · decide +kernel

private theorem only_mACD (r : MC) (h : r ≠ mACD) : mDegree r ≠ 2 := by
  rcases mc_cases r with rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · exact absurd rfl h

private theorem single_mem_sublevelChains {g : MC} {p : ℕ} {t : ℤ} (hg : mDegree g = p)
    (ht : mGrade g ≤ t) :
    Pi.single g (1 : ZMod 2) ∈ sublevelChains mDegree mGrade p t := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have : r ≠ g := fun e => hr (e ▸ hg)
    simp [this]
  · have : r ≠ g := fun e => by subst e; omega
    simp [this]

private theorem finrank_eq_one_of {g : MC} {p : ℕ} {t : ℤ} (hg : mDegree g = p)
    (hother : ∀ r, r ≠ g → mDegree r ≠ p) (ht : mGrade g ≤ t)
    (hcyc : sqCert.morseDifferential.mulVec (Pi.single g 1) = 0)
    (hnb : Pi.single g (1 : ZMod 2) ∉
      sublevelBoundaries mDegree mGrade sqCert.morseDifferential p t) :
    Module.finrank (ZMod 2) (sublevelHomology mDegree mGrade sqCert.morseDifferential p t) =
      1 := by
  have hmem : Pi.single g (1 : ZMod 2) ∈
      sublevelCycles mDegree mGrade sqCert.morseDifferential p t :=
    mem_sublevelCycles.mpr ⟨(single_mem_sublevelChains hg ht).1,
      (single_mem_sublevelChains hg ht).2, hcyc⟩
  refine (finrank_eq_one_iff_of_nonzero' (Submodule.Quotient.mk ⟨_, hmem⟩) ?_).mpr ?_
  · rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hnb
  · intro w
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨(x : MC → ZMod 2) g, ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (eq_smul_single hg hother (mem_sublevelCycles.mp x.2).1).symm

private theorem subsingleton_of {p : ℕ} {t : ℤ}
    (h : ∀ x ∈ sublevelCycles mDegree mGrade sqCert.morseDifferential p t,
      x ∈ sublevelBoundaries mDegree mGrade sqCert.morseDifferential p t) :
    Subsingleton (sublevelHomology mDegree mGrade sqCert.morseDifferential p t) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ b
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact h _ (sub_mem x.2 y.2)

private theorem subsingleton_of_chains {p : ℕ} {t : ℤ}
    (h : ∀ x ∈ sublevelChains mDegree mGrade p t, x = (0 : MC → ZMod 2)) :
    Subsingleton (sublevelHomology mDegree mGrade sqCert.morseDifferential p t) :=
  subsingleton_of fun x hx => by
    obtain ⟨h₁, h₂, -⟩ := mem_sublevelCycles.mp hx
    rw [h x ⟨h₁, h₂⟩]
    exact Submodule.zero_mem _

private theorem chains_eq_zero_of_lt {g : MC} {p : ℕ} {t : ℤ} (hg : mDegree g = p)
    (hother : ∀ r, r ≠ g → mDegree r ≠ p) (ht : t < mGrade g) :
    ∀ x ∈ sublevelChains mDegree mGrade p t, x = (0 : MC → ZMod 2) := by
  intro x hx
  rw [eq_smul_single hg hother hx.1, hx.2 g ht, zero_smul]

/-! ## Homology of the Morse complex -/

private theorem mA_cycle : sqCert.morseDifferential.mulVec (Pi.single mA 1) = 0 := by
  rw [mD_mulVec]; simp [mA_ne_mACD.symm]

private theorem mA_not_mem_sublevelBoundaries (t : ℤ) :
    Pi.single mA (1 : ZMod 2) ∉ sublevelBoundaries mDegree mGrade sqCert.morseDifferential 0 t := by
  intro hb
  obtain ⟨y, -, -, hy⟩ := mem_sublevelBoundaries.mp hb
  have := congrFun hy mA
  rw [mD_mulVec] at this
  simp [mA_ne_mAD] at this

private theorem mA_mem_sublevelCycles (t : ℤ) (ht : 0 ≤ t) :
    Pi.single mA (1 : ZMod 2) ∈ sublevelCycles mDegree mGrade sqCert.morseDifferential 0 t :=
  mem_sublevelCycles.mpr ⟨(single_mem_sublevelChains mDegree_mA (mGrade_mA ▸ ht)).1,
    (single_mem_sublevelChains mDegree_mA (mGrade_mA ▸ ht)).2, mA_cycle⟩

/-- `H₀` of the Morse complex has dimension one at every grade `t ≥ 0`. -/
theorem morse_finrank_zero (t : ℤ) (ht : 0 ≤ t) :
    Module.finrank (ZMod 2) (sublevelHomology mDegree mGrade sqCert.morseDifferential 0 t) =
      1 :=
  finrank_eq_one_of mDegree_mA only_mA (mGrade_mA ▸ ht) mA_cycle
    (mA_not_mem_sublevelBoundaries t)

/-- `H₀` of the Morse complex vanishes below grade 0. -/
theorem morse_subsingleton_zero_of_lt (t : ℤ) (ht : t < 0) :
    Subsingleton (sublevelHomology mDegree mGrade sqCert.morseDifferential 0 t) :=
  subsingleton_of_chains (chains_eq_zero_of_lt mDegree_mA only_mA (mGrade_mA ▸ ht))

/-- `H₁` of the Morse complex vanishes below grade 1. -/
theorem morse_subsingleton_one_of_lt (t : ℤ) (ht : t < 1) :
    Subsingleton (sublevelHomology mDegree mGrade sqCert.morseDifferential 1 t) :=
  subsingleton_of_chains (chains_eq_zero_of_lt mDegree_mAD only_mAD (mGrade_mAD ▸ ht))

/-- `H₁` of the Morse complex has dimension one at grade 1. -/
theorem morse_finrank_one_one :
    Module.finrank (ZMod 2) (sublevelHomology mDegree mGrade sqCert.morseDifferential 1 1) =
      1 := by
  refine finrank_eq_one_of mDegree_mAD only_mAD mGrade_mAD.le ?_ ?_
  · rw [mD_mulVec]; simp [mAD_ne_mACD.symm]
  · intro hb
    obtain ⟨y, -, hy', hy⟩ := mem_sublevelBoundaries.mp hb
    have h0 : y mACD = 0 := hy' mACD (by rw [mGrade_mACD]; decide)
    have := congrFun hy mAD
    rw [mD_mulVec, h0] at this
    revert this; simp

/-- `H₁` of the Morse complex vanishes at every grade `t ≥ 2`. -/
theorem morse_subsingleton_one (t : ℤ) (ht : 2 ≤ t) :
    Subsingleton (sublevelHomology mDegree mGrade sqCert.morseDifferential 1 t) := by
  refine subsingleton_of fun x hx => ?_
  obtain ⟨h₁, -, -⟩ := mem_sublevelCycles.mp hx
  refine mem_sublevelBoundaries.mpr ⟨x mAD • Pi.single mACD 1,
    (Submodule.smul_mem _ _ (single_mem_sublevelChains mDegree_mACD
      (mGrade_mACD ▸ ht))).1,
    (Submodule.smul_mem _ _ (single_mem_sublevelChains mDegree_mACD
      (mGrade_mACD ▸ ht))).2, ?_⟩
  rw [mD_mulVec, eq_smul_single mDegree_mAD only_mAD h₁]
  funext r
  by_cases hr : r = mAD
  · subst hr; simp
  · simp [hr]

/-- `H₂` of the Morse complex vanishes at every grade. -/
theorem morse_subsingleton_two (t : ℤ) :
    Subsingleton (sublevelHomology mDegree mGrade sqCert.morseDifferential 2 t) := by
  refine subsingleton_of fun x hx => ?_
  obtain ⟨h₁, -, h₃⟩ := mem_sublevelCycles.mp hx
  have hx0 : x = 0 := by
    rw [eq_smul_single mDegree_mACD only_mACD h₁] at h₃ ⊢
    have := congrFun h₃ mAD
    rw [mD_mulVec] at this
    have hc : x mACD = 0 := by simpa using this
    simp [hc]
  rw [hx0]
  exact Submodule.zero_mem _

/-- The Morse complex has no generator of degree `p ≥ 3`. -/
theorem morse_subsingleton_of_three_le (p : ℕ) (hp : 3 ≤ p) (t : ℤ) :
    Subsingleton (sublevelHomology mDegree mGrade sqCert.morseDifferential p t) := by
  refine subsingleton_of_chains fun x hx => funext fun r => hx.1 r ?_
  rcases mc_cases r with rfl | rfl | rfl
  · rw [mDegree_mA]; omega
  · rw [mDegree_mAD]; omega
  · rw [mDegree_mACD]; omega

/-! ## Simplicial homology of the square, through the main theorem -/

/-- The grade-`t` sublevel complex of the square. -/
abbrev sqSublevel (t : ℤ) := (FiniteInput.gradeFilter square square_valid).sublevel t

private theorem finrank_eq (p : ℕ) (t : ℤ) :
    Module.finrank (ZMod 2) (simplicialHomology (sqSublevel t) (ZMod 2) p) =
      Module.finrank (ZMod 2)
        (sublevelHomology mDegree mGrade sqCert.morseDifferential p t) :=
  sqCert.finrank_simplicialHomology_eq square_valid p t

/-- `H₀` of the square's sublevel complex has dimension one at every grade `t ≥ 0`. -/
theorem square_finrank_zero (t : ℤ) (ht : 0 ≤ t) :
    Module.finrank (ZMod 2) (simplicialHomology (sqSublevel t) (ZMod 2) 0) = 1 :=
  (finrank_eq 0 t).trans (morse_finrank_zero t ht)

/-- `H₀` of the square's sublevel complex vanishes below grade 0. -/
theorem square_finrank_zero_of_lt (t : ℤ) (ht : t < 0) :
    Module.finrank (ZMod 2) (simplicialHomology (sqSublevel t) (ZMod 2) 0) = 0 :=
  have := morse_subsingleton_zero_of_lt t ht
  (finrank_eq 0 t).trans Module.finrank_zero_of_subsingleton

/-- `H₁` of the square's sublevel complex vanishes below grade 1. -/
theorem square_finrank_one_of_lt (t : ℤ) (ht : t < 1) :
    Module.finrank (ZMod 2) (simplicialHomology (sqSublevel t) (ZMod 2) 1) = 0 :=
  have := morse_subsingleton_one_of_lt t ht
  (finrank_eq 1 t).trans Module.finrank_zero_of_subsingleton

/-- `H₁` of the square's sublevel complex has dimension one at grade 1. -/
theorem square_finrank_one_one :
    Module.finrank (ZMod 2) (simplicialHomology (sqSublevel 1) (ZMod 2) 1) = 1 :=
  (finrank_eq 1 1).trans morse_finrank_one_one

/-- `H₁` of the square's sublevel complex vanishes at every grade `t ≥ 2`. -/
theorem square_finrank_one (t : ℤ) (ht : 2 ≤ t) :
    Module.finrank (ZMod 2) (simplicialHomology (sqSublevel t) (ZMod 2) 1) = 0 :=
  have := morse_subsingleton_one t ht
  (finrank_eq 1 t).trans Module.finrank_zero_of_subsingleton

/-- `H₂` of the square's sublevel complex vanishes at every grade. -/
theorem square_finrank_two (t : ℤ) :
    Module.finrank (ZMod 2) (simplicialHomology (sqSublevel t) (ZMod 2) 2) = 0 :=
  have := morse_subsingleton_two t
  (finrank_eq 2 t).trans Module.finrank_zero_of_subsingleton

/-- `H_p` of the square's sublevel complex vanishes for `p ≥ 3`. -/
theorem square_finrank_of_three_le (p : ℕ) (hp : 3 ≤ p) (t : ℤ) :
    Module.finrank (ZMod 2) (simplicialHomology (sqSublevel t) (ZMod 2) p) = 0 :=
  have := morse_subsingleton_of_three_le p hp t
  (finrank_eq p t).trans Module.finrank_zero_of_subsingleton

/-! ## The rank invariant of `H₁`: the bar `[1,2)` -/

/-- **The H₁ bar `[1,2)`, as a rank invariant.** For grades `a ≤ b`, the rank of the degree-1
structure map `a → b` of the square's simplicial sublevel persistence module is `1` exactly
when `a = b = 1`, and `0` otherwise: the rank invariant of the interval `[1,2)` of `ℤ`. -/
theorem square_rankOfStructureMap_one {a b : ℤ} (hab : a ≤ b) :
    rankOfStructureMap (sublevelModule (ZMod 2) (FiniteInput.gradeFilter square square_valid) 1)
      hab = if a = 1 ∧ b = 1 then 1 else 0 := by
  rw [sqCert.rankOfStructureMap_sublevelModule_eq square_valid 1 hab, rankOfStructureMap]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
    exact morse_finrank_one_one
  · by_cases ha : a < 1
    · have : Subsingleton
          ((sublevelHomologyPModule mDegree mGrade sqCert.morseDifferential 1).obj a) :=
        morse_subsingleton_one_of_lt a ha
      rw [LinearMap.range_eq_bot.mpr (LinearMap.ext fun x => by
        rw [Subsingleton.elim x 0, map_zero]; rfl), finrank_bot]
    · have : Subsingleton
          ((sublevelHomologyPModule mDegree mGrade sqCert.morseDifferential 1).obj b) :=
        morse_subsingleton_one b (by omega)
      have : Subsingleton (LinearMap.range (structureMapLinear
          (sublevelHomologyPModule mDegree mGrade sqCert.morseDifferential 1) hab)) :=
        ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
      exact Module.finrank_zero_of_subsingleton

/-- **The H₀ bar `[0,∞)`, as a rank invariant.** For grades `a ≤ b`, the rank of the
degree-0 structure map `a → b` of the square's simplicial sublevel persistence module is `1`
when `0 ≤ a` and `0` otherwise. -/
theorem square_rankOfStructureMap_zero {a b : ℤ} (hab : a ≤ b) :
    rankOfStructureMap (sublevelModule (ZMod 2) (FiniteInput.gradeFilter square square_valid) 0)
      hab = if 0 ≤ a then 1 else 0 := by
  rw [sqCert.rankOfStructureMap_sublevelModule_eq square_valid 0 hab, rankOfStructureMap]
  split_ifs with ha
  · have hfa := morse_finrank_zero a ha
    have : Module.Finite (ZMod 2)
        ((sublevelHomologyPModule mDegree mGrade sqCert.morseDifferential 0).obj a) :=
      Module.finite_of_finrank_eq_succ hfa
    have hle := (LinearMap.finrank_range_le (structureMapLinear
      (sublevelHomologyPModule mDegree mGrade sqCert.morseDifferential 0) hab)).trans hfa.le
    have hne : LinearMap.range (structureMapLinear
        (sublevelHomologyPModule mDegree mGrade sqCert.morseDifferential 0) hab) ≠ ⊥ := by
      intro hbot
      have hx := LinearMap.mem_range_self (structureMapLinear
        (sublevelHomologyPModule mDegree mGrade sqCert.morseDifferential 0) hab)
        (Submodule.Quotient.mk ⟨_, mA_mem_sublevelCycles a ha⟩)
      rw [hbot, Submodule.mem_bot] at hx
      have hx' : (Submodule.Quotient.mk (⟨Pi.single mA 1, mA_mem_sublevelCycles b (ha.trans hab)⟩ :
          sublevelCycles mDegree mGrade sqCert.morseDifferential 0 b) :
          sublevelHomology mDegree mGrade sqCert.morseDifferential 0 b) = 0 := hx
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx'
      exact mA_not_mem_sublevelBoundaries b hx'
    have hpos : Module.finrank (ZMod 2) (LinearMap.range (structureMapLinear
        (sublevelHomologyPModule mDegree mGrade sqCert.morseDifferential 0) hab)) ≠ 0 :=
      fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
    exact le_antisymm hle (Nat.one_le_iff_ne_zero.mpr hpos)
  · have : Subsingleton
        ((sublevelHomologyPModule mDegree mGrade sqCert.morseDifferential 0).obj a) :=
      morse_subsingleton_zero_of_lt a (by omega)
    rw [LinearMap.range_eq_bot.mpr (LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero]; rfl), finrank_bot]

/-! ## The loop AB + BC + CD + AD: born at grade 1, filled at grade 2 -/

/-- The loop AB + BC + CD + AD, on the positions of `square`. -/
def sqLoop : Sq → ZMod 2 := fun i => if i = qAB ∨ i = qBC ∨ i = qCD ∨ i = qAD then 1 else 0

/-- The filling ABC + ACD, on the positions of `square`. -/
def sqFill : Sq → ZMod 2 := fun i => if i = qABC ∨ i = qACD then 1 else 0

/-- The loop is a degree-1 cycle in grades `≤ 1`. -/
theorem sqLoop_cycleInput : FiniteInput.CycleInput square 1 1 sqLoop := by
  rw [FiniteInput.CycleInput, boundary_eq_coverIncidence]; decide +kernel

/-- The boundary of the filling is the loop. -/
theorem boundary_mulVec_sqFill : (FiniteInput.boundary square).mulVec sqFill = sqLoop := by
  rw [boundary_eq_coverIncidence]; decide +kernel

/-- At grade 1, the actual simplicial homology class of the loop is not zero. -/
theorem sqLoop_class_ne_zero :
    FiniteInput.vectorSublevelClass square square_valid 1 1 sqLoop sqLoop_cycleInput ≠ 0 := by
  have hz := (cycleInput_iff_mem_sublevelCycles square 1 1 sqLoop).mp sqLoop_cycleInput
  have he := boundaryHomologyEquiv_mk square_valid 1 1 ⟨sqLoop, hz⟩
  change _ = FiniteInput.vectorSublevelClass square square_valid 1 1 sqLoop _ at he
  rw [← he, Ne, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.subtype_apply]
  intro hb
  obtain ⟨y, hyd, hys, hy⟩ := mem_sublevelBoundaries.mp hb
  have hy0 : y = 0 := by
    have hpos : ∀ i : Sq, FiniteInput.degree square i ≠ 2 ∨ 1 < (square.get i).2 := by
      decide +kernel
    funext i
    rcases hpos i with hi | hi
    · exact hyd i hi
    · exact hys i hi
  rw [hy0, Matrix.mulVec_zero] at hy
  have := congrFun hy qAB
  change (0 : ZMod 2) = sqLoop qAB at this
  revert this; decide +kernel

/-- From grade 1 to grade 2, the inclusion of sublevel complexes sends the class of the loop
to zero: the loop is filled at grade 2. -/
theorem sqLoop_class_filled :
    (simplicialHomologyIncl (ZMod 2)
        ((FiniteInput.gradeFilter square square_valid).sublevel_mono
          (show (1 : ℤ) ≤ 2 by norm_num)) 1).hom
      (FiniteInput.vectorSublevelClass square square_valid 1 1 sqLoop sqLoop_cycleInput) =
      0 := by
  have h2 : FiniteInput.CycleInput square 1 2 sqLoop :=
    FiniteInput.cycleInput_mono square 1 1 2 (by norm_num) sqLoop sqLoop_cycleInput
  rw [FiniteInput.vectorSublevelClass_naturality square square_valid 1 1 2 (by norm_num) sqLoop
    sqLoop_cycleInput h2]
  have hz := (cycleInput_iff_mem_sublevelCycles square 1 2 sqLoop).mp h2
  have he := boundaryHomologyEquiv_mk square_valid 1 2 ⟨sqLoop, hz⟩
  change _ = FiniteInput.vectorSublevelClass square square_valid 1 2 sqLoop _ at he
  rw [← he, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.subtype_apply]
  refine mem_sublevelBoundaries.mpr ⟨sqFill, ?_, ?_, boundary_mulVec_sqFill⟩
  · intro i hi
    revert i; decide +kernel
  · intro i hi
    revert i; decide +kernel

/-! ## The greedy certificate, through the main theorem -/

/-- `H₁` of the Morse complex of the greedy certificate `genCert` has dimension one at grade 1,
read off the square's simplicial homology through the main theorem. -/
theorem genCert_morse_finrank_one_one :
    Module.finrank (ZMod 2) (sublevelHomology (FiniteInput.degree square ∘ Subtype.val)
      ((fun i => (square.get i).2) ∘ Subtype.val) genCert.morseDifferential 1 1) = 1 :=
  (genCert.finrank_simplicialHomology_eq square_valid 1 1).symm.trans square_finrank_one_one

/-- The degree-1 persistence module of the Morse complex of `genCert` has the rank invariant of
the interval `[1,2)`, read off the square's simplicial persistence through the main theorem. -/
theorem genCert_rankOfStructureMap_one {a b : ℤ} (hab : a ≤ b) :
    rankOfStructureMap (sublevelHomologyPModule (FiniteInput.degree square ∘ Subtype.val)
      ((fun i => (square.get i).2) ∘ Subtype.val) genCert.morseDifferential 1) hab =
      if a = 1 ∧ b = 1 then 1 else 0 :=
  (genCert.rankOfStructureMap_sublevelModule_eq square_valid 1 hab).symm.trans
    (square_rankOfStructureMap_one hab)

/-! ## The diagrams of the square: the bars `[1,2)` and `[0,∞)` -/

private theorem two_le_countP {β : Type*} {P : β → Prop} [DecidablePred P]
    {s : Multiset β} {x y : β} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (hPx : P x)
    (hPy : P y) : 2 ≤ s.countP P := by
  rw [Multiset.countP_eq_card_filter]
  have hle : ({x, y} : Multiset β) ≤ s.filter P :=
    (Multiset.le_iff_subset (by simp [hxy])).mpr fun z hz => by
      rcases (by simpa using hz : z = x ∨ z = y) with rfl | rfl
      · exact Multiset.mem_filter.mpr ⟨hx, hPx⟩
      · exact Multiset.mem_filter.mpr ⟨hy, hPy⟩
  simpa using Multiset.card_le_card hle

/-- **The H₁ bar `[1,2)`.** The degree-1 sublevel diagram `dgm` of the square, the library's
barcode of its simplicial sublevel persistence module over `ℤ`, is the single point `(1, 2)`;
read off M4 through `rank_sublevelHomologyMap`, not from the reducer. -/
theorem square_dgm_one :
    letI := FiniteInput.faceFintype square square_valid
    (dgm (ZMod 2) (FiniteInput.gradeFilter square square_valid) 1).points =
      {((1 : ℤ), ((2 : ℤ) : WithTop ℤ))} := by
  let := FiniteInput.faceFintype square square_valid
  have hc : ∀ {a b : ℤ} (hab : a ≤ b),
      (dgm (ZMod 2) (FiniteInput.gradeFilter square square_valid) 1).points.countP
        (fun q => q.1 ≤ a ∧ (b : WithTop ℤ) < q.2) = if a = 1 ∧ b = 1 then 1 else 0 :=
    fun hab => (rank_sublevelHomologyMap (ZMod 2) _ 1 _ _ hab).symm.trans
      (square_rankOfStructureMap_one hab)
  have hpos := dgm_isPositive (ZMod 2) (FiniteInput.gradeFilter square square_valid) 1
  have hall : ∀ q ∈ (dgm (ZMod 2) (FiniteInput.gradeFilter square square_valid) 1).points,
      q = ((1 : ℤ), ((2 : ℤ) : WithTop ℤ)) := by
    rintro ⟨x, y⟩ hq
    have hxy : (x : WithTop ℤ) < y := hpos _ hq
    have hx : x = 1 := by
      by_contra hne
      have h0 := hc (le_refl x)
      simp only [hne, false_and, ite_false] at h0
      exact Multiset.countP_eq_zero.mp h0 _ hq ⟨le_rfl, hxy⟩
    subst hx
    cases y with
    | top =>
      have h0 : _ = 0 := hc (show (1 : ℤ) ≤ 2 by norm_num)
      exact absurd (Multiset.countP_eq_zero.mp h0 _ hq) (by simp)
    | coe d =>
      have h1 : (1 : ℤ) < d := WithTop.coe_lt_coe.mp hxy
      by_contra hne
      have h0 : _ = 0 := hc (show (1 : ℤ) ≤ 2 by norm_num)
      refine Multiset.countP_eq_zero.mp h0 _ hq ⟨le_rfl, WithTop.coe_lt_coe.mpr ?_⟩
      have : d ≠ 2 := fun h => hne (by rw [h])
      omega
  have hcard : _ = 1 := hc (le_refl (1 : ℤ))
  rw [Multiset.countP_eq_card.mpr fun q hq => by
    rw [hall q hq]; exact ⟨le_rfl, by decide⟩] at hcard
  rw [Multiset.eq_replicate.mpr ⟨hcard, hall⟩]
  rfl

/-- **The H₀ bar `[0,∞)`.** The degree-0 sublevel diagram `dgm` of the square is the single
essential point `(0, ⊤)`; read off M4 through `rank_sublevelHomologyMap`. -/
theorem square_dgm_zero :
    letI := FiniteInput.faceFintype square square_valid
    (dgm (ZMod 2) (FiniteInput.gradeFilter square square_valid) 0).points =
      {((0 : ℤ), (⊤ : WithTop ℤ))} := by
  let := FiniteInput.faceFintype square square_valid
  have hc : ∀ {a b : ℤ} (hab : a ≤ b),
      (dgm (ZMod 2) (FiniteInput.gradeFilter square square_valid) 0).points.countP
        (fun q => q.1 ≤ a ∧ (b : WithTop ℤ) < q.2) = if 0 ≤ a then 1 else 0 :=
    fun hab => (rank_sublevelHomologyMap (ZMod 2) _ 0 _ _ hab).symm.trans
      (square_rankOfStructureMap_zero hab)
  have hpos := dgm_isPositive (ZMod 2) (FiniteInput.gradeFilter square square_valid) 0
  have hall : ∀ q ∈ (dgm (ZMod 2) (FiniteInput.gradeFilter square square_valid) 0).points,
      q = ((0 : ℤ), (⊤ : WithTop ℤ)) := by
    rintro ⟨x, y⟩ hq
    have hxy : (x : WithTop ℤ) < y := hpos _ hq
    have hx0 : 0 ≤ x := by
      by_contra hn
      have h0 := hc (le_refl x)
      simp only [hn, ite_false] at h0
      exact Multiset.countP_eq_zero.mp h0 _ hq ⟨le_rfl, hxy⟩
    have hx : x = 0 := by
      by_contra hne
      have h1 := hc (show x - 1 ≤ x by omega)
      simp only [show 0 ≤ x - 1 by omega, ite_true] at h1
      obtain ⟨q', hq', hq'1, hq'2⟩ := Multiset.countP_pos.mp (lt_of_lt_of_eq Nat.one_pos h1.symm)
      have h2 := two_le_countP (P := fun q : ℤ × WithTop ℤ => q.1 ≤ x ∧ (x : WithTop ℤ) < q.2)
        hq hq' (fun he => by have := congrArg Prod.fst he; simp at this; omega) ⟨le_rfl, hxy⟩
        ⟨by omega, hq'2⟩
      rw [hc (le_refl x)] at h2
      simp only [hx0, ↓reduceIte] at h2
      omega
    subst hx
    cases y with
    | top => rfl
    | coe d =>
      have hd : (0 : ℤ) < d := WithTop.coe_lt_coe.mp hxy
      have h1 := hc (show (0 : ℤ) ≤ d by omega)
      simp only [le_refl, ite_true] at h1
      obtain ⟨q', hq', hq'1, hq'2⟩ := Multiset.countP_pos.mp (lt_of_lt_of_eq Nat.one_pos h1.symm)
      have h2 := two_le_countP (P := fun q : ℤ × WithTop ℤ => q.1 ≤ 0 ∧ ((0 : ℤ) : WithTop ℤ) < q.2)
        hq hq' (fun he => by
          have := congrArg Prod.snd he; simp only at this; rw [← this] at hq'2
          exact lt_irrefl _ hq'2)
        ⟨le_rfl, hxy⟩ ⟨hq'1, lt_trans (WithTop.coe_lt_coe.mpr hd) hq'2⟩
      rw [hc (le_refl (0 : ℤ))] at h2
      simp only [le_refl, ↓reduceIte] at h2
      omega
  have hcard : _ = 1 := hc (le_refl (0 : ℤ))
  rw [Multiset.countP_eq_card.mpr fun q hq => by
    rw [hall q hq]; exact ⟨le_rfl, by decide⟩] at hcard
  rw [Multiset.eq_replicate.mpr ⟨hcard, hall⟩]
  rfl

end TDA.Persistence.Morse.SimplicialBridgeExamples
