import TDA.Simplicial.FiniteDimensionalHomology
import Mathlib.LinearAlgebra.Transvection.Generation

/-!
# Adding one actual simplex

The face-set equation supplies the extra chain coordinate. All homology maps below
are induced by the existing inclusion of actual oriented face chains.
-/

universe u v
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000

namespace TDA.Simplicial

open CategoryTheory Module

variable {V : Type u} [LinearOrder V]

/-- An attachment specified by the difference of the *actual* face sets. -/
structure SimplexAttachment (K L : PreAbstractSimplicialComplex V) (q : ℕ) where
  simplex : Finset V
  card_simplex : simplex.card = q + 1
  not_mem : simplex ∉ K
  face_iff : ∀ s : Finset V, s ∈ L ↔ s ∈ K ∨ s = simplex

namespace SimplexAttachment

variable {K L : PreAbstractSimplicialComplex V} {q : ℕ}
variable (A : SimplexAttachment K L q)
include A

theorem inclusion : K ≤ L := by
  intro s hs
  exact (A.face_iff s).2 (Or.inl hs)

theorem simplex_mem : A.simplex ∈ L :=
  (A.face_iff A.simplex).2 (Or.inr rfl)

/-- The actual new basis face. -/
def newFace : Face L q := ⟨A.simplex, A.simplex_mem, A.card_simplex⟩

theorem faceIncl_injective (n : ℕ) :
    Function.Injective (faceIncl A.inclusion n) := by
  intro s t h
  exact Subtype.ext (congrArg (fun x : Face L n => x.1) h)

theorem newFace_not_range : A.newFace ∉ Set.range (faceIncl A.inclusion q) := by
  rintro ⟨s, hs⟩
  have : s.1 = A.simplex := congrArg Subtype.val hs
  exact A.not_mem (this ▸ s.2.1)

theorem old_of_ne {n : ℕ} (s : Face L n) (hs : s.1 ≠ A.simplex) : s.1 ∈ K := by
  rcases (A.face_iff s.1).1 s.2.1 with hk | he
  · exact hk
  · exact (hs he).elim

theorem old_of_degree_ne {n : ℕ} (hn : n ≠ q) (s : Face L n) : s.1 ∈ K := by
  apply A.old_of_ne s
  intro he
  have hc : n + 1 = q + 1 := by rw [← s.2.2, he, A.card_simplex]
  exact hn (Nat.add_right_cancel hc)

theorem old_face_of_degree_ne {n : ℕ} (hn : n ≠ q) (s : Face L n) :
    ∃ t : Face K n, faceIncl A.inclusion n t = s := by
  exact ⟨⟨s.1, A.old_of_degree_ne hn s, s.2.2⟩, Subtype.ext rfl⟩

variable (k : Type v) [Field k]

theorem chainIncl_injective (n : ℕ) :
    Function.Injective (chainIncl k A.inclusion n) := by
  change Function.Injective (Finsupp.mapDomain (faceIncl A.inclusion n))
  exact Finsupp.mapDomain_injective (A.faceIncl_injective n)

theorem chainIncl_surjective_of_ne {n : ℕ} (hn : n ≠ q) :
    Function.Surjective (chainIncl k A.inclusion n) := by
  intro c
  change ∃ a, Finsupp.mapDomain (faceIncl A.inclusion n) a = c
  exact (Finsupp.mem_range_mapDomain_iff (faceIncl A.inclusion n)
    (A.faceIncl_injective n) c).2
    (fun s hs => (hs (A.old_face_of_degree_ne hn s)).elim)

/-- In all other degrees the actual face inclusion is a chain isomorphism. -/
noncomputable def chainEquivOfNe {n : ℕ} (hn : n ≠ q) :
    Chain K k n ≃ₗ[k] Chain L k n :=
  LinearEquiv.ofBijective (chainIncl k A.inclusion n)
    ⟨A.chainIncl_injective k n, A.chainIncl_surjective_of_ne k hn⟩

theorem chainIncl_new_coeff (a : Chain K k q) :
    (chainIncl k A.inclusion q a) A.newFace = 0 := by
  change (Finsupp.mapDomain (faceIncl A.inclusion q) a) A.newFace = 0
  exact Finsupp.mapDomain_of_notMem_range a A.newFace (by
    intro h
    rcases h with ⟨s, hs⟩
    have he : s.1 = A.simplex := congrArg (fun x : Face L q => x.1) hs
    exact A.not_mem (he ▸ s.2.1))

/-- Every new chain has precisely one extra coefficient, derived from `faces`. -/
theorem chain_decomposition (c : Chain L k q) :
    ∃ a : Chain K k q, c = chainIncl k A.inclusion q a + Finsupp.single A.newFace (c A.newFace) := by
  classical
  have hrange : c - Finsupp.single A.newFace (c A.newFace) ∈
      Set.range (Finsupp.mapDomain (faceIncl A.inclusion q)) := by
    apply (Finsupp.mem_range_mapDomain_iff (faceIncl A.inclusion q)
      (A.faceIncl_injective q) _).2
    intro s hs
    by_cases he : s = A.newFace
    · subst s
      simp
    · have hold : s.1 ∈ K := A.old_of_ne s (by
        intro hval
        exact he (Subtype.ext hval))
      exact (hs ⟨⟨s.1, hold, s.2.2⟩, Subtype.ext rfl⟩).elim
  obtain ⟨a, ha⟩ := hrange
  change chainIncl k A.inclusion q a = _ at ha
  exact ⟨a, by rw [ha]; abel⟩

theorem chainIncl_range_iff_coeff_zero (c : Chain L k q) :
    c ∈ LinearMap.range (chainIncl k A.inclusion q) ↔ c A.newFace = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact A.chainIncl_new_coeff k a
  · intro hc
    obtain ⟨a, ha⟩ := A.chain_decomposition k c
    refine ⟨a, ?_⟩
    simpa [hc] using ha.symm


end SimplexAttachment


namespace SimplexAttachment

variable {K L : PreAbstractSimplicialComplex V} {q : ℕ}
variable (A : SimplexAttachment K L q) (k : Type v) [Field k]
include A

private noncomputable instance quotientForAttachment (J : PreAbstractSimplicialComplex V)
    (n : ℕ) : HasQuotient (simplicialCycles J k n)
      (Submodule k (simplicialCycles J k n)) :=
  Submodule.hasQuotient (R := k) (M := simplicialCycles J k n)

/-- A cycle on unchanged chains lifts to an old cycle. -/
theorem cycleIncl_surjective_of_ne {n : ℕ} (hn : n ≠ q) :
    Function.Surjective (simplicialCycleIncl k A.inclusion n) := by
  intro z
  obtain ⟨a, ha⟩ := A.chainIncl_surjective_of_ne k hn (z : Chain L k n)
  have hcycle : a ∈ simplicialCycles K k n := by
    cases n with
    | zero => rw [simplicialCycles_zero]; trivial
    | succ m =>
      rw [simplicialCycles_succ]
      apply A.chainIncl_injective k m
      have hnat := congrArg (fun f : Chain K k (m + 1) →ₗ[k] Chain L k m => f a)
        (boundary_chainIncl k A.inclusion m)
      simp only [LinearMap.comp_apply] at hnat
      rw [ha] at hnat
      have hz : boundary L k m (z : Chain L k (m + 1)) = 0 := by
        have hm : (z : Chain L k (m + 1)) ∈ LinearMap.ker (boundary L k m) := by
          simpa only [simplicialCycles_succ] using z.2
        exact hm
      simpa [hz] using hnat.symm
  refine ⟨⟨a, hcycle⟩, ?_⟩
  apply Subtype.ext
  simpa only [simplicialCycleIncl_coe] using ha

theorem old_cycle_of_included_chain (n : ℕ) (a : Chain K k n)
    (z : simplicialCycles L k n)
    (ha : chainIncl k A.inclusion n a = (z : Chain L k n)) :
    a ∈ simplicialCycles K k n := by
  cases n with
  | zero => rw [simplicialCycles_zero]; trivial
  | succ m =>
    rw [simplicialCycles_succ]
    apply A.chainIncl_injective k m
    have hnat := congrArg (fun f : Chain K k (m + 1) →ₗ[k] Chain L k m => f a)
      (boundary_chainIncl k A.inclusion m)
    simp only [LinearMap.comp_apply] at hnat
    rw [ha] at hnat
    have hz : boundary L k m (z : Chain L k (m + 1)) = 0 := by
      have hm : (z : Chain L k (m + 1)) ∈ LinearMap.ker (boundary L k m) := by
        simpa only [simplicialCycles_succ] using z.2
      exact hm
    simpa [hz] using hnat.symm

private noncomputable instance attachmentRawQuotient
    (J : PreAbstractSimplicialComplex V) (n : ℕ) :
    HasQuotient (LinearMap.ker ((simplicialChainComplex J k).sc n).g.hom)
      (Submodule k (LinearMap.ker ((simplicialChainComplex J k).sc n).g.hom)) :=
  Submodule.hasQuotient (R := k)
    (M := LinearMap.ker ((simplicialChainComplex J k).sc n).g.hom)

/-- The coefficient of the genuinely new basis face on cycles. -/
noncomputable def newCoeffCycles : simplicialCycles L k q →ₗ[k] k :=
  (Finsupp.lapply A.newFace).comp (simplicialCycles L k q).subtype

theorem boundary_new_coeff_zero (d : Chain L k (q + 1)) :
    (boundary L k q d) A.newFace = 0 := by
  obtain ⟨a, ha⟩ := A.chainIncl_surjective_of_ne k (by omega : q + 1 ≠ q) d
  have hn := congrArg (fun f : Chain K k (q + 1) →ₗ[k] Chain L k q => f a)
    (boundary_chainIncl k A.inclusion q)
  simp only [LinearMap.comp_apply] at hn
  calc
    (boundary L k q d) A.newFace =
        (chainIncl k A.inclusion q (boundary K k q a)) A.newFace := by
      rw [← ha, hn]
    _ = 0 := A.chainIncl_new_coeff k _

theorem boundaries_new_coeff_zero :
    simplicialBoundaries L k q ≤ LinearMap.ker (A.newCoeffCycles k) := by
  intro z hz
  obtain ⟨d, hd⟩ := (mem_simplicialBoundaries_iff k L q z).mp hz
  change (show Chain L k q from z.1) A.newFace = 0
  rw [← hd]
  exact A.boundary_new_coeff_zero k d

theorem cycleIncl_surjective_of_coeff_zero
    (hz : ∀ z : simplicialCycles L k q, (z : Chain L k q) A.newFace = 0) :
    Function.Surjective (simplicialCycleIncl k A.inclusion q) := by
  intro z
  obtain ⟨a, ha⟩ := (A.chainIncl_range_iff_coeff_zero k _).2 (hz z)
  have hca := A.old_cycle_of_included_chain k q a z ha
  refine ⟨⟨a, hca⟩, ?_⟩
  apply Subtype.ext
  simpa only [simplicialCycleIncl_coe] using ha

theorem quotientIncl_surjective_of_coeff_zero
    (hz : ∀ z : simplicialCycles L k q, (z : Chain L k q) A.newFace = 0) :
    Function.Surjective (simplicialQuotientIncl k A.inclusion q) := by
  intro x
  induction x using Quotient.inductionOn' with
  | _ z =>
    obtain ⟨a, ha⟩ := A.cycleIncl_surjective_of_coeff_zero k hz z
    refine ⟨Submodule.mkQ (R := k) (M := simplicialCycles K k q)
      (simplicialBoundaries K k q) a, ?_⟩
    change simplicialQuotientIncl k A.inclusion q
      (Submodule.mkQ (R := k) (M := simplicialCycles K k q)
        (simplicialBoundaries K k q) a) =
      Submodule.mkQ (R := k) (M := simplicialCycles L k q)
        (simplicialBoundaries L k q) z
    rw [simplicialQuotientIncl_mkQ, ha]

theorem new_cycle_class_not_range (w : simplicialCycles L k q)
    (hw : (w : Chain L k q) A.newFace = 1) :
    (simplicialBoundaries L k q).mkQ w ∉
      LinearMap.range (simplicialQuotientIncl k A.inclusion q) := by
  rintro ⟨x, hx⟩
  induction x using Quotient.inductionOn' with
  | _ a =>
    change simplicialQuotientIncl k A.inclusion q
      (Submodule.mkQ (R := k) (M := simplicialCycles K k q)
        (simplicialBoundaries K k q) a) =
        Submodule.mkQ (R := k) (M := simplicialCycles L k q)
          (simplicialBoundaries L k q) w at hx
    rw [simplicialQuotientIncl_mkQ] at hx
    have hb : simplicialCycleIncl k A.inclusion q a - w ∈
        simplicialBoundaries L k q := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.eq] using hx
    have hc := (LinearMap.mem_ker).mp (A.boundaries_new_coeff_zero k hb)
    change (chainIncl k A.inclusion q (a : Chain K k q) -
      (w : Chain L k q)) A.newFace = 0 at hc
    simp only [Finsupp.sub_apply] at hc
    simp only [A.chainIncl_new_coeff, hw, zero_sub] at hc
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0)) hc

theorem quotient_range_sup_birth_span_eq_top (w : simplicialCycles L k q)
    (hw : (w : Chain L k q) A.newFace = 1) :
    LinearMap.range (simplicialQuotientIncl k A.inclusion q) ⊔
      k ∙ (simplicialBoundaries L k q).mkQ w = ⊤ := by
  apply (Submodule.eq_top_iff').2
  intro x
  induction x using Quotient.inductionOn' with
  | _ z =>
    let c := (z : Chain L k q) A.newFace
    have hc : ((z - c • w : simplicialCycles L k q) : Chain L k q)
        A.newFace = 0 := by
      change ((z : Chain L k q) - c • (w : Chain L k q)) A.newFace = 0
      simp [Finsupp.sub_apply, c, hw]
    obtain ⟨a, ha⟩ := (A.chainIncl_range_iff_coeff_zero k _).2 hc
    let old : simplicialCycles K k q :=
      ⟨a, A.old_cycle_of_included_chain k q a (z - c • w) ha⟩
    have he : simplicialCycleIncl k A.inclusion q old + c • w = z := by
      apply Subtype.ext
      change chainIncl k A.inclusion q a + c • (w : Chain L k q) =
        (z : Chain L k q)
      rw [ha]
      change ((z : Chain L k q) - c • (w : Chain L k q)) +
        c • (w : Chain L k q) = (z : Chain L k q)
      abel
    have hq : simplicialQuotientIncl k A.inclusion q
        (Submodule.mkQ (R := k) (M := simplicialCycles K k q)
          (simplicialBoundaries K k q) old) +
        c • Submodule.mkQ (R := k) (M := simplicialCycles L k q)
          (simplicialBoundaries L k q) w =
          Submodule.mkQ (R := k) (M := simplicialCycles L k q)
            (simplicialBoundaries L k q) z := by
      rw [simplicialQuotientIncl_mkQ]
      change (simplicialBoundaries L k q).mkQ
          (simplicialCycleIncl k A.inclusion q old) +
          c • (simplicialBoundaries L k q).mkQ w =
          (simplicialBoundaries L k q).mkQ z
      rw [← map_smul, ← map_add, he]
    apply Submodule.mem_sup.mpr
    refine ⟨simplicialQuotientIncl k A.inclusion q
      (Submodule.mkQ (R := k) (M := simplicialCycles K k q)
        (simplicialBoundaries K k q) old), ⟨_, rfl⟩,
      c • Submodule.mkQ (R := k) (M := simplicialCycles L k q)
        (simplicialBoundaries L k q) w, ?_, hq⟩
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- An attached cycle with new coefficient one generates a one-dimensional cokernel. -/
theorem quotientIncl_birth_cokernel_finrank [Finite (TotalFace L)]
    (w : simplicialCycles L k q)
    (hw : (w : Chain L k q) A.newFace = 1) :
    Module.finrank k
      ((simplicialCycles L k q ⧸ simplicialBoundaries L k q) ⧸
        LinearMap.range (simplicialQuotientIncl k A.inclusion q)) = 1 := by
  letI : Finite (Face L q) := faceFiniteOfTotalFinite L q
  letI : FiniteDimensional k (Chain L k q) := finiteDimensional_finsupp
  letI : FiniteDimensional k (simplicialCycles L k q) := inferInstance
  letI : FiniteDimensional k
      (simplicialCycles L k q ⧸ simplicialBoundaries L k q) := inferInstance
  have htop := A.quotient_range_sup_birth_span_eq_top k w hw
  have hnot := A.new_cycle_class_not_range k w hw
  have hd := LinearEquiv.finrank_quotient_sup_span_singleton hnot
  rw [htop] at hd
  have hzero : Module.finrank k
      ((simplicialCycles L k q ⧸ simplicialBoundaries L k q) ⧸
        (⊤ : Submodule k (simplicialCycles L k q ⧸ simplicialBoundaries L k q))) =
        0 := (Module.finrank_zero_iff).2 inferInstance
  rw [hzero, zero_add] at hd
  exact hd.symm

/-- Boundaries reflect through inclusion when the source of the differential is unchanged. -/
theorem boundary_reflect_of_ne {n : ℕ} (hn : n + 1 ≠ q)
    (z : simplicialCycles K k n)
    (hz : simplicialCycleIncl k A.inclusion n z ∈ simplicialBoundaries L k n) :
    z ∈ simplicialBoundaries K k n := by
  obtain ⟨d, hd⟩ := (mem_simplicialBoundaries_iff k L n _).mp hz
  obtain ⟨a, ha⟩ := A.chainIncl_surjective_of_ne k hn d
  apply (mem_simplicialBoundaries_iff k K n z).2
  refine ⟨a, A.chainIncl_injective k n ?_⟩
  have hnat := congrArg (fun f : Chain K k (n + 1) →ₗ[k] Chain L k n => f a)
    (boundary_chainIncl k A.inclusion n)
  simp only [LinearMap.comp_apply] at hnat
  rw [ha] at hnat
  rw [hd] at hnat
  simpa only [simplicialCycleIncl_coe] using hnat.symm

set_option backward.isDefEq.respectTransparency false in
theorem quotientIncl_injective_of_ne {n : ℕ} (hn : n + 1 ≠ q) :
    Function.Injective (simplicialQuotientIncl k A.inclusion n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  induction x using Quotient.inductionOn' with
  | _ z =>
    change (simplicialBoundaries K k n).mkQ z = 0
    have hx' := (LinearMap.mem_ker).mp hx
    change simplicialQuotientIncl k A.inclusion n
      (Submodule.mkQ (R := k) (M := simplicialCycles K k n)
        (simplicialBoundaries K k n) z) = 0 at hx'
    rw [simplicialQuotientIncl_mkQ] at hx'
    rw [Submodule.mkQ_apply] at hx'
    simp only [Submodule.Quotient.mk_eq_zero] at hx'
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact A.boundary_reflect_of_ne k hn z hx'

set_option backward.isDefEq.respectTransparency false in
theorem quotientIncl_surjective_of_ne {n : ℕ} (hn : n ≠ q) :
    Function.Surjective (simplicialQuotientIncl k A.inclusion n) := by
  intro x
  induction x using Quotient.inductionOn' with
  | _ z =>
    obtain ⟨a, ha⟩ := A.cycleIncl_surjective_of_ne k hn z
    refine ⟨Submodule.mkQ (R := k) (M := simplicialCycles K k n)
      (simplicialBoundaries K k n) a, ?_⟩
    change simplicialQuotientIncl k A.inclusion n
      (Submodule.mkQ (R := k) (M := simplicialCycles K k n)
        (simplicialBoundaries K k n) a) =
      Submodule.mkQ (R := k) (M := simplicialCycles L k n)
        (simplicialBoundaries L k n) z
    rw [simplicialQuotientIncl_mkQ, ha]

/-- Actual homology inclusion is bijective away from the two adjacent degrees. -/
theorem homologyIncl_bijective_of_ne {n : ℕ}
    (hn : n ≠ q) (hn' : n + 1 ≠ q) :
    Function.Bijective (simplicialHomologyIncl k A.inclusion n).hom := by
  let eK := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex K k) n).toLinearEquiv
  let eL := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex L k) n).toLinearEquiv
  have hnat := simplicialHomologyIncl_quotient_naturality k A.inclusion n
  constructor
  · intro x y hxy
    apply eK.injective
    apply A.quotientIncl_injective_of_ne k hn'
    have hx := congrArg (fun f => f.hom x) hnat
    have hy := congrArg (fun f => f.hom y) hnat
    change eL ((simplicialHomologyIncl k A.inclusion n).hom x) =
      (simplicialQuotientIncl k A.inclusion n) (eK x) at hx
    change eL ((simplicialHomologyIncl k A.inclusion n).hom y) =
      (simplicialQuotientIncl k A.inclusion n) (eK y) at hy
    rw [hxy] at hx
    exact hx.symm.trans hy
  · intro y
    obtain ⟨z, hz⟩ := A.quotientIncl_surjective_of_ne k hn (eL y)
    refine ⟨eK.symm z, ?_⟩
    have hx := congrArg (fun f => f.hom (eK.symm z)) hnat
    change eL ((simplicialHomologyIncl k A.inclusion n).hom (eK.symm z)) =
      (simplicialQuotientIncl k A.inclusion n) (eK (eK.symm z)) at hx
    apply eL.injective
    exact hx.trans ((congrArg (simplicialQuotientIncl k A.inclusion n)
      (eK.apply_symm_apply z)).trans hz)

theorem homologyIncl_injective_of_succ_ne {n : ℕ} (hn : n + 1 ≠ q) :
    Function.Injective (simplicialHomologyIncl k A.inclusion n).hom := by
  let eK := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex K k) n).toLinearEquiv
  let eL := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex L k) n).toLinearEquiv
  have hnat := simplicialHomologyIncl_quotient_naturality k A.inclusion n
  intro x y hxy
  apply eK.injective
  apply A.quotientIncl_injective_of_ne k hn
  have hx := congrArg (fun f => f.hom x) hnat
  have hy := congrArg (fun f => f.hom y) hnat
  change eL ((simplicialHomologyIncl k A.inclusion n).hom x) =
    (simplicialQuotientIncl k A.inclusion n) (eK x) at hx
  change eL ((simplicialHomologyIncl k A.inclusion n).hom y) =
    (simplicialQuotientIncl k A.inclusion n) (eK y) at hy
  rw [hxy] at hx
  exact hx.symm.trans hy

theorem homologyIncl_surjective_of_quotient {n : ℕ}
    (hq : Function.Surjective (simplicialQuotientIncl k A.inclusion n)) :
    Function.Surjective (simplicialHomologyIncl k A.inclusion n).hom := by
  let eK := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex K k) n).toLinearEquiv
  let eL := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex L k) n).toLinearEquiv
  have hnat := simplicialHomologyIncl_quotient_naturality k A.inclusion n
  intro y
  obtain ⟨z, hz⟩ := hq (eL y)
  refine ⟨eK.symm z, ?_⟩
  have hx := congrArg (fun f => f.hom (eK.symm z)) hnat
  change eL ((simplicialHomologyIncl k A.inclusion n).hom (eK.symm z)) =
    (simplicialQuotientIncl k A.inclusion n) (eK (eK.symm z)) at hx
  apply eL.injective
  exact hx.trans ((congrArg (simplicialQuotientIncl k A.inclusion n)
    (eK.apply_symm_apply z)).trans hz)

/-- The quotient comparison transports the cokernel of the actual homology map. -/
noncomputable def homologyCokernelEquiv (n : ℕ) :
    (simplicialHomology L k n ⧸
      LinearMap.range (simplicialHomologyIncl k A.inclusion n).hom) ≃ₗ[k]
    ((simplicialCycles L k n ⧸ simplicialBoundaries L k n) ⧸
      LinearMap.range (simplicialQuotientIncl k A.inclusion n)) := by
  let eK := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex K k) n).toLinearEquiv
  let eL := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex L k) n).toLinearEquiv
  have hnat := simplicialHomologyIncl_quotient_naturality k A.inclusion n
  have hcomm (x : simplicialHomology K k n) :
      eL ((simplicialHomologyIncl k A.inclusion n).hom x) =
        simplicialQuotientIncl k A.inclusion n (eK x) := by
    have hx := congrArg (fun f => f.hom x) hnat
    exact hx
  apply Submodule.Quotient.equiv (R := k) (R₂ := k)
    (σ₁₂ := RingHom.id k) (σ₂₁ := RingHom.id k)
    (LinearMap.range (simplicialHomologyIncl k A.inclusion n).hom)
    (LinearMap.range (simplicialQuotientIncl k A.inclusion n)) eL
  ext y
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨eK a, (hcomm a).symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨z, rfl⟩ := hb
    refine ⟨(simplicialHomologyIncl k A.inclusion n).hom (eK.symm b),
      ⟨eK.symm b, rfl⟩, ?_⟩
    have hk : eK (eK.symm b) = b := eK.apply_symm_apply b
    exact (hcomm (eK.symm b)).trans
      (congrArg (simplicialQuotientIncl k A.inclusion n) hk)

theorem homologyIncl_birth_cokernel_finrank [Finite (TotalFace L)]
    (w : simplicialCycles L k q)
    (hw : (w : Chain L k q) A.newFace = 1) :
    Module.finrank k (simplicialHomology L k q ⧸
      LinearMap.range (simplicialHomologyIncl k A.inclusion q).hom) = 1 := by
  calc
    _ = Module.finrank k
        ((simplicialCycles L k q ⧸ simplicialBoundaries L k q) ⧸
          LinearMap.range (simplicialQuotientIncl k A.inclusion q)) :=
      (A.homologyCokernelEquiv k q).finrank_eq
    _ = 1 := A.quotientIncl_birth_cokernel_finrank k w hw

set_option backward.isDefEq.respectTransparency false in
/-- The homology class represented by a cycle with a new coordinate. -/
noncomputable def birthQuotientClass (w : simplicialCycles L k q) :
    simplicialCycles L k q ⧸ simplicialBoundaries L k q :=
  Submodule.mkQ (R := k) (M := simplicialCycles L k q)
    (simplicialBoundaries L k q) w

set_option backward.isDefEq.respectTransparency false in
/-- The actual homology class represented by a cycle with a new coordinate. -/
noncomputable def birthHomologyClass (w : simplicialCycles L k q) :
    simplicialHomology L k q :=
  (homologyKernelQuotient.{v,u,v} k
    (simplicialChainComplex L k) q).toLinearEquiv.symm
      (birthQuotientClass (L := L) k w)

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel class represented by a cycle with a new coordinate. -/
noncomputable def birthCokernelClass (w : simplicialCycles L k q) :
    simplicialHomology L k q ⧸
      LinearMap.range (simplicialHomologyIncl k A.inclusion q).hom :=
  (LinearMap.range (simplicialHomologyIncl k A.inclusion q).hom).mkQ
    (birthHomologyClass (L := L) k w)

/-- The cycle with new coefficient one gives an actual homology cokernel generator. -/
theorem homologyIncl_birth_generator [Finite (TotalFace L)]
    (w : simplicialCycles L k q)
    (hw : (w : Chain L k q) A.newFace = 1) :
    k ∙ A.birthCokernelClass k w = ⊤ := by
  let eK := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex K k) q).toLinearEquiv
  let eL := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex L k) q).toLinearEquiv
  let u := birthHomologyClass (L := L) k w
  have hnot := A.new_cycle_class_not_range k w hw
  have hne : (LinearMap.range (simplicialHomologyIncl k A.inclusion q).hom).mkQ u ≠ 0 := by
    intro hz
    have hu : u ∈ LinearMap.range (simplicialHomologyIncl k A.inclusion q).hom := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hz
    obtain ⟨x, hx⟩ := hu
    apply hnot
    refine ⟨eK x, ?_⟩
    have hnat := simplicialHomologyIncl_quotient_naturality k A.inclusion q
    have hc := congrArg (fun f => f.hom x) hnat
    change eL ((simplicialHomologyIncl k A.inclusion q).hom x) =
      simplicialQuotientIncl k A.inclusion q (eK x) at hc
    have hu' : eL u = (simplicialBoundaries L k q).mkQ w := by
      change eL (eL.symm (birthQuotientClass (L := L) k w)) = _
      exact eL.apply_symm_apply _
    exact hc.symm.trans ((congrArg eL hx).trans hu')
  exact (finrank_eq_one_iff_of_nonzero _ hne).mp
    (A.homologyIncl_birth_cokernel_finrank k w hw)


end SimplexAttachment

namespace SimplexAttachment

variable {K L : PreAbstractSimplicialComplex V} {p : ℕ}
variable (A : SimplexAttachment K L (p + 1))
include A
variable (k : Type v) [Field k]

private noncomputable instance cyclesQuotient (J : PreAbstractSimplicialComplex V) (n : ℕ) :
    HasQuotient (simplicialCycles J k n) (Submodule k (simplicialCycles J k n)) :=
  Submodule.hasQuotient (R := k) (M := simplicialCycles J k n)

private noncomputable instance cyclesRawQuotient
    (J : PreAbstractSimplicialComplex V) (n : ℕ) :
    HasQuotient (LinearMap.ker ((simplicialChainComplex J k).sc n).g.hom)
      (Submodule k (LinearMap.ker ((simplicialChainComplex J k).sc n).g.hom)) :=
  Submodule.hasQuotient (R := k)
    (M := LinearMap.ker ((simplicialChainComplex J k).sc n).g.hom)

/-- The ordered deletion face belongs to the old complex. -/
def oldDeletedFace (i : Fin (p + 2)) : Face K p := by
  let s := deletedFace L p A.newFace i
  have hne : s.1 ≠ A.simplex := by
    intro he
    have hc : p + 1 = p + 2 := by
      rw [← s.2.2, he, A.card_simplex]
    omega
  exact ⟨s.1, A.old_of_ne s hne, s.2.2⟩

theorem oldDeletedFace_incl (i : Fin (p + 2)) :
    faceIncl A.inclusion p (A.oldDeletedFace i) = deletedFace L p A.newFace i :=
  Subtype.ext rfl

/-- The oriented boundary of the attached simplex, in the old chain module. -/
noncomputable def attachingBoundary : Chain K k p :=
  ∑ i : Fin (p + 2), Finsupp.single (A.oldDeletedFace i) ((-1 : k) ^ (i : ℕ))

theorem attachingBoundary_incl :
    chainIncl k A.inclusion p (A.attachingBoundary k) =
      boundary L k p (Finsupp.single A.newFace 1) := by
  simp only [attachingBoundary, map_sum, chainIncl_single, boundary_single, one_smul]
  exact Finset.sum_congr rfl (fun i _ => by rw [A.oldDeletedFace_incl])

theorem attachingBoundary_ne_zero : A.attachingBoundary k ≠ 0 := by
  have hinj : Function.Injective (deletedFace L p A.newFace) := by
    intro i j hij
    by_contra hne
    let vi := A.newFace.1.orderEmbOfFin A.newFace.2.2 i
    let vj := A.newFace.1.orderEmbOfFin A.newFace.2.2 j
    have hvne : vi ≠ vj := fun h => hne
      ((A.newFace.1.orderEmbOfFin A.newFace.2.2).injective h)
    have hmem : vi ∈ (deletedFace L p A.newFace j).1 := by
      change vi ∈ A.newFace.1.erase vj
      exact Finset.mem_erase.mpr
        ⟨hvne, Finset.orderEmbOfFin_mem A.newFace.1 A.newFace.2.2 i⟩
    rw [← hij] at hmem
    have : vi ∈ A.newFace.1.erase vi := hmem
    simpa using this
  have hcoeff :
      (boundary L k p (Finsupp.single A.newFace 1))
        (deletedFace L p A.newFace 0) = 1 := by
    rw [boundary_single]
    change (Finsupp.lapply (deletedFace L p A.newFace 0) : Chain L k p →ₗ[k] k)
      ((1 : k) • ∑ i : Fin (p + 2),
        Finsupp.single (deletedFace L p A.newFace i) ((-1 : k) ^ (i : ℕ))) = 1
    rw [one_smul, map_sum]
    simp only [Finsupp.lapply_apply, Finsupp.single_apply, hinj.eq_iff]
    simp
  intro hz
  rw [← A.attachingBoundary_incl, hz, map_zero, Finsupp.zero_apply] at hcoeff
  exact one_ne_zero hcoeff.symm

/-- The attaching boundary is a cycle, including the case of an edge attaching to vertices. -/
noncomputable def attachingCycle : simplicialCycles K k p := by
  refine ⟨A.attachingBoundary k, ?_⟩
  cases p with
  | zero => rw [simplicialCycles_zero]; trivial
  | succ m =>
    rw [simplicialCycles_succ]
    apply A.chainIncl_injective k m
    have hc := congrArg (fun f : Chain L k (m + 2) →ₗ[k] Chain L k m =>
      f (Finsupp.single A.newFace 1))
      (boundary_comp_boundary L k m)
    have hn := congrArg (fun f : Chain K k (m + 1) →ₗ[k] Chain L k m =>
      f (A.attachingBoundary k)) (boundary_chainIncl k A.inclusion m)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hc hn
    rw [A.attachingBoundary_incl] at hn
    simpa [hn] using hc

theorem boundary_of_decomposition (c : Chain L k (p + 1))
    (a : Chain K k (p + 1))
    (hc : c = chainIncl k A.inclusion (p + 1) a +
      Finsupp.single A.newFace (c A.newFace)) :
    boundary L k p c = chainIncl k A.inclusion p
      (boundary K k p a + (c A.newFace) • A.attachingBoundary k) := by
  have hs : Finsupp.single A.newFace (c A.newFace) =
      (c A.newFace) • (Finsupp.single A.newFace (1 : k)) := by simp
  have hn := congrArg (fun f : Chain K k (p + 1) →ₗ[k] Chain L k p => f a)
    (boundary_chainIncl k A.inclusion p)
  simp only [LinearMap.comp_apply] at hn
  conv_lhs => rw [hc]
  rw [map_add, hs, map_smul, ← A.attachingBoundary_incl, hn]
  simp only [map_add, map_smul]

theorem boundary_of_chain (c : Chain L k (p + 1)) :
    ∃ a : Chain K k (p + 1), boundary L k p c =
      chainIncl k A.inclusion p (boundary K k p a +
        (c A.newFace) • A.attachingBoundary k) := by
  obtain ⟨a, ha⟩ := A.chain_decomposition k c
  exact ⟨a, A.boundary_of_decomposition k c a ha⟩

noncomputable def attachingQuotientClass :
    simplicialCycles K k p ⧸ simplicialBoundaries K k p :=
  Submodule.mkQ (R := k) (M := simplicialCycles K k p)
    (simplicialBoundaries K k p) (A.attachingCycle k)

theorem attachingQuotientClass_maps_zero :
    simplicialQuotientIncl k A.inclusion p (A.attachingQuotientClass k) = 0 := by
  change simplicialQuotientIncl k A.inclusion p
    (Submodule.mkQ (R := k) (M := simplicialCycles K k p)
      (simplicialBoundaries K k p) (A.attachingCycle k)) = 0
  rw [simplicialQuotientIncl_mkQ]
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  apply (mem_simplicialBoundaries_iff k L p _).2
  refine ⟨Finsupp.single A.newFace 1, ?_⟩
  simpa only [simplicialCycleIncl_coe, attachingCycle] using
    (A.attachingBoundary_incl k).symm

theorem quotientIncl_ker_eq_span_attachingClass :
    LinearMap.ker (simplicialQuotientIncl k A.inclusion p) =
      k ∙ A.attachingQuotientClass k := by
  apply le_antisymm
  · intro x hx
    induction x using Quotient.inductionOn' with
    | _ z =>
      have hx' := (LinearMap.mem_ker).mp hx
      change simplicialQuotientIncl k A.inclusion p
        (Submodule.mkQ (R := k) (M := simplicialCycles K k p)
          (simplicialBoundaries K k p) z) = 0 at hx'
      rw [simplicialQuotientIncl_mkQ, Submodule.mkQ_apply] at hx'
      simp only [Submodule.Quotient.mk_eq_zero] at hx'
      obtain ⟨d, hd⟩ := (mem_simplicialBoundaries_iff k L p _).mp hx'
      obtain ⟨a, ha⟩ := A.boundary_of_chain k d
      have he : (z : Chain K k p) = boundary K k p a +
          (d A.newFace) • A.attachingBoundary k := by
        apply A.chainIncl_injective k p
        calc
          chainIncl k A.inclusion p (z : Chain K k p) =
              boundary L k p d := by simpa only [simplicialCycleIncl_coe] using hd.symm
          _ = _ := ha
      have hb : z - (d A.newFace) • A.attachingCycle k ∈
          simplicialBoundaries K k p := by
        apply (mem_simplicialBoundaries_iff k K p _).2
        refine ⟨a, ?_⟩
        change boundary K k p a = (z : Chain K k p) -
          (d A.newFace) • A.attachingBoundary k
        rw [he]
        abel
      have hq' : (Quotient.mk'' z : simplicialCycles K k p ⧸
          simplicialBoundaries K k p) =
          (d A.newFace) • A.attachingQuotientClass k := by
        calc
          _ = Quotient.mk'' ((d A.newFace) • A.attachingCycle k) :=
            (Submodule.Quotient.eq (simplicialBoundaries K k p)).2 hb
          _ = _ := by
            change (simplicialBoundaries K k p).mkQ
              ((d A.newFace) • A.attachingCycle k) =
                (d A.newFace) • (simplicialBoundaries K k p).mkQ
                  (A.attachingCycle k)
            rfl
      rw [hq']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (A.attachingQuotientClass_maps_zero k))

set_option backward.isDefEq.respectTransparency false in
/-- The actual homology class of the attaching boundary. -/
noncomputable def attachingHomologyClass : simplicialHomology K k p :=
  (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex K k) p).toLinearEquiv.symm
    (A.attachingQuotientClass k)

theorem attachingHomologyClass_equiv :
    (homologyKernelQuotient.{v,u,v} k
      (simplicialChainComplex K k) p).toLinearEquiv (A.attachingHomologyClass k) =
      A.attachingQuotientClass k := by
  exact LinearEquiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the actual inclusion map is exactly the attaching class's span. -/
theorem homologyIncl_ker_eq_span_attachingClass :
    LinearMap.ker (simplicialHomologyIncl k A.inclusion p).hom =
      k ∙ A.attachingHomologyClass k := by
  let eK := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex K k) p).toLinearEquiv
  let eL := (homologyKernelQuotient.{v,u,v} k (simplicialChainComplex L k) p).toLinearEquiv
  have hnat := simplicialHomologyIncl_quotient_naturality k A.inclusion p
  have hcomm (x : simplicialHomology K k p) :
      eL ((simplicialHomologyIncl k A.inclusion p).hom x) =
        simplicialQuotientIncl k A.inclusion p (eK x) := by
    exact congrArg (fun f => f.hom x) hnat
  ext x
  constructor
  · intro hx
    have hq : eK x ∈ LinearMap.ker (simplicialQuotientIncl k A.inclusion p) := by
      change simplicialQuotientIncl k A.inclusion p (eK x) = 0
      calc
        _ = eL ((simplicialHomologyIncl k A.inclusion p).hom x) := (hcomm x).symm
        _ = eL 0 := congrArg eL ((LinearMap.mem_ker).mp hx)
        _ = 0 := eL.map_zero
    rw [A.quotientIncl_ker_eq_span_attachingClass k] at hq
    change (eK x : simplicialCycles K k p ⧸ simplicialBoundaries K k p) ∈
      k ∙ A.attachingQuotientClass k at hq
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hq
    apply (Submodule.mem_span_singleton).2
    refine ⟨c, ?_⟩
    apply eK.injective
    calc
      eK (c • A.attachingHomologyClass k) =
          c • eK (A.attachingHomologyClass k) := eK.map_smul c _
      _ = c • A.attachingQuotientClass k :=
        congrArg (c • ·) (A.attachingHomologyClass_equiv k)
      _ = eK x := hc
  · intro hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hx
    have hq : eK x ∈ k ∙ A.attachingQuotientClass k := by
      apply (Submodule.mem_span_singleton).2
      refine ⟨c, ?_⟩
      calc
        c • A.attachingQuotientClass k =
            c • eK (A.attachingHomologyClass k) :=
          congrArg (c • ·) (A.attachingHomologyClass_equiv k).symm
        _ = eK (c • A.attachingHomologyClass k) := (eK.map_smul c _).symm
        _ = eK x := congrArg eK hc
    rw [← A.quotientIncl_ker_eq_span_attachingClass k] at hq
    change (simplicialHomologyIncl k A.inclusion p).hom x = 0
    apply eL.injective
    calc
      eL ((simplicialHomologyIncl k A.inclusion p).hom x) =
          simplicialQuotientIncl k A.inclusion p (eK x) := hcomm x
      _ = 0 := (LinearMap.mem_ker).mp hq
      _ = eL 0 := eL.map_zero.symm

theorem homologyIncl_death_kernel_finrank
    (hne : A.attachingQuotientClass k ≠ 0) :
    Module.finrank k (LinearMap.ker
      (simplicialHomologyIncl k A.inclusion p).hom) = 1 := by
  rw [A.homologyIncl_ker_eq_span_attachingClass k]
  apply finrank_span_singleton
  intro hz
  apply hne
  have heq := A.attachingHomologyClass_equiv k
  rw [hz] at heq
  exact heq.symm.trans
    ((homologyKernelQuotient.{v,u,v} k
      (simplicialChainComplex K k) p).toLinearEquiv.map_zero)

theorem new_coeff_zero_of_attachingClass_ne_zero
    (hne : A.attachingQuotientClass k ≠ 0)
    (z : simplicialCycles L k (p + 1)) :
    (z : Chain L k (p + 1)) A.newFace = 0 := by
  let c := (z : Chain L k (p + 1)) A.newFace
  by_contra hc
  have hc' : c ≠ 0 := hc
  have hnot : A.attachingCycle k ∉ simplicialBoundaries K k p := by
    intro hb
    apply hne
    change (simplicialBoundaries K k p).mkQ (A.attachingCycle k) = 0
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hb
  obtain ⟨a, ha⟩ := A.chain_decomposition k (z : Chain L k (p + 1))
  have hz : boundary L k p (z : Chain L k (p + 1)) = 0 := by
    have hm : (z : Chain L k (p + 1)) ∈ LinearMap.ker (boundary L k p) := by
      simpa only [simplicialCycles_succ] using z.2
    exact hm
  have he : boundary K k p a + c • A.attachingBoundary k = 0 := by
    apply A.chainIncl_injective k p
    have hd := A.boundary_of_decomposition k (z : Chain L k (p + 1)) a ha
    simpa only [map_zero] using hd.symm.trans hz
  have he' : boundary K k p a = (-c) • A.attachingBoundary k := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left he
  apply hnot
  apply (mem_simplicialBoundaries_iff k K p (A.attachingCycle k)).2
  refine ⟨(-c)⁻¹ • a, ?_⟩
  change boundary K k p ((-c)⁻¹ • a) = A.attachingBoundary k
  rw [map_smul, he', smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hc'), one_smul]

theorem homologyIncl_bijective_of_attachingClass_ne_zero
    (hne : A.attachingQuotientClass k ≠ 0) :
    Function.Bijective (simplicialHomologyIncl k A.inclusion (p + 1)).hom := by
  refine ⟨A.homologyIncl_injective_of_succ_ne k (by omega), ?_⟩
  apply A.homologyIncl_surjective_of_quotient k
  exact A.quotientIncl_surjective_of_coeff_zero k
    (A.new_coeff_zero_of_attachingClass_ne_zero k hne)

theorem attachingClass_zero_iff_boundary :
    A.attachingQuotientClass k = 0 ↔
      A.attachingCycle k ∈ simplicialBoundaries K k p := by
  change (simplicialBoundaries K k p).mkQ (A.attachingCycle k) = 0 ↔ _
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem attachingClass_ne_zero_of_no_old_coface
    [IsEmpty (Face K (p + 1))] : A.attachingHomologyClass k ≠ 0 := by
  intro hz
  have heq := A.attachingHomologyClass_equiv k
  rw [hz] at heq
  have hqzero : A.attachingQuotientClass k = 0 := by
    exact heq.symm.trans
      ((homologyKernelQuotient.{v,u,v} k
        (simplicialChainComplex K k) p).toLinearEquiv.map_zero)
  obtain ⟨a, ha⟩ := (mem_simplicialBoundaries_iff k K p _).mp
    ((A.attachingClass_zero_iff_boundary k).mp hqzero)
  have ha0 : a = 0 := by
    ext s
    exact isEmptyElim s
  rw [ha0, map_zero] at ha
  exact A.attachingBoundary_ne_zero k ha.symm

theorem birth_cycle_of_attachingClass_zero
    (hzero : A.attachingQuotientClass k = 0) :
    ∃ a : Chain K k (p + 1), boundary K k p a = A.attachingBoundary k ∧
      ∃ z : simplicialCycles L k (p + 1),
        (z : Chain L k (p + 1)) =
          Finsupp.single A.newFace 1 - chainIncl k A.inclusion (p + 1) a ∧
        (z : Chain L k (p + 1)) A.newFace = 1 := by
  obtain ⟨a, ha⟩ := (mem_simplicialBoundaries_iff k K p _).mp
    ((A.attachingClass_zero_iff_boundary k).mp hzero)
  let c : Chain L k (p + 1) :=
    Finsupp.single A.newFace 1 - chainIncl k A.inclusion (p + 1) a
  have hc : c ∈ simplicialCycles L k (p + 1) := by
    rw [simplicialCycles_succ]
    have hnat := congrArg (fun f : Chain K k (p + 1) →ₗ[k] Chain L k p => f a)
      (boundary_chainIncl k A.inclusion p)
    simp only [LinearMap.comp_apply] at hnat
    change boundary L k p c = 0
    dsimp [c]
    rw [map_sub, ← A.attachingBoundary_incl, hnat, ha]
    change chainIncl k A.inclusion p (A.attachingBoundary k) -
      chainIncl k A.inclusion p (A.attachingBoundary k) = 0
    exact sub_self _
  refine ⟨a, ha, ⟨c, hc⟩, rfl, ?_⟩
  change c A.newFace = 1
  simp only [c, Finsupp.sub_apply, Finsupp.single_eq_same, A.chainIncl_new_coeff,
    sub_zero]

end SimplexAttachment

namespace SimplexAttachment

variable {K L : PreAbstractSimplicialComplex V}
variable (A : SimplexAttachment K L 0) (k : Type v) [Field k]

/-- A new isolated vertex is a cycle under the unaugmented convention. -/
noncomputable def isolatedVertexCycle : simplicialCycles L k 0 :=
  ⟨Finsupp.single A.newFace 1, by rw [simplicialCycles_zero]; trivial⟩

theorem isolatedVertexCycle_coeff :
    ((A.isolatedVertexCycle k : simplicialCycles L k 0) : Chain L k 0) A.newFace = 1 := by
  simp [isolatedVertexCycle]

/-- The actual degree-zero inclusion has one birth; every positive degree is unchanged. -/
theorem isolatedVertex_birth [Finite (TotalFace L)] :
    Function.Injective (simplicialHomologyIncl k A.inclusion 0).hom ∧
    Module.finrank k (simplicialHomology L k 0 ⧸
      LinearMap.range (simplicialHomologyIncl k A.inclusion 0).hom) = 1 ∧
    ∀ r : ℕ, 0 < r →
      Function.Bijective (simplicialHomologyIncl k A.inclusion r).hom := by
  refine ⟨A.homologyIncl_injective_of_succ_ne k (by omega),
    A.homologyIncl_birth_cokernel_finrank k (A.isolatedVertexCycle k)
      (A.isolatedVertexCycle_coeff k), ?_⟩
  intro r hr
  exact A.homologyIncl_bijective_of_ne k (by omega) (by omega)

theorem isolatedVertex_generates [Finite (TotalFace L)] :
    k ∙ A.birthCokernelClass k (A.isolatedVertexCycle k) = ⊤ :=
  A.homologyIncl_birth_generator k (A.isolatedVertexCycle k)
    (A.isolatedVertexCycle_coeff k)

end SimplexAttachment

namespace SimplexAttachment

variable {K L : PreAbstractSimplicialComplex V} {p : ℕ}
variable (A : SimplexAttachment K L (p + 1)) (k : Type v) [Field k]

/-- If the attaching class vanishes, the new simplex creates a homology class. -/
theorem positive_birth [Finite (TotalFace L)]
    (hzero : A.attachingHomologyClass k = 0) :
    Function.Injective (simplicialHomologyIncl k A.inclusion (p + 1)).hom ∧
    Module.finrank k (simplicialHomology L k (p + 1) ⧸
      LinearMap.range (simplicialHomologyIncl k A.inclusion (p + 1)).hom) = 1 ∧
    (∀ r : ℕ, r ≠ p + 1 →
      Function.Bijective (simplicialHomologyIncl k A.inclusion r).hom) ∧
    (∃ a : Chain K k (p + 1), boundary K k p a = A.attachingBoundary k ∧
      ∃ z : simplicialCycles L k (p + 1),
        (z : Chain L k (p + 1)) =
          Finsupp.single A.newFace 1 - chainIncl k A.inclusion (p + 1) a ∧
        (z : Chain L k (p + 1)) A.newFace = 1) := by
  have heq := A.attachingHomologyClass_equiv k
  rw [hzero] at heq
  have hqzero : A.attachingQuotientClass k = 0 := by
    exact heq.symm.trans
      ((homologyKernelQuotient.{v,u,v} k
        (simplicialChainComplex K k) p).toLinearEquiv.map_zero)
  obtain ⟨a, ha, z, hz, hc⟩ := A.birth_cycle_of_attachingClass_zero k hqzero
  refine ⟨A.homologyIncl_injective_of_succ_ne k (by omega),
    A.homologyIncl_birth_cokernel_finrank k z hc, ?_, ⟨a, ha, z, hz, hc⟩⟩
  intro r hr
  by_cases hp : r = p
  · subst r
    have hsurj : Function.Surjective (simplicialHomologyIncl k A.inclusion p).hom :=
      A.homologyIncl_surjective_of_quotient k
        (A.quotientIncl_surjective_of_ne k (by omega))
    have hinj : Function.Injective (simplicialHomologyIncl k A.inclusion p).hom := by
      apply LinearMap.ker_eq_bot.mp
      rw [A.homologyIncl_ker_eq_span_attachingClass k, hzero]
      simp
    exact ⟨hinj, hsurj⟩
  · exact A.homologyIncl_bijective_of_ne k hr (by omega)

/-- The explicit cycle `σ - a` spans the actual birth cokernel. -/
theorem positive_birth_generator [Finite (TotalFace L)]
    (hzero : A.attachingHomologyClass k = 0) :
    ∃ a : Chain K k (p + 1), boundary K k p a = A.attachingBoundary k ∧
      ∃ z : simplicialCycles L k (p + 1),
        (z : Chain L k (p + 1)) =
          Finsupp.single A.newFace 1 - chainIncl k A.inclusion (p + 1) a ∧
        k ∙ A.birthCokernelClass k z = ⊤ := by
  obtain ⟨_, _, _, h⟩ := A.positive_birth k hzero
  obtain ⟨a, ha, z, hz, hc⟩ := h
  exact ⟨a, ha, z, hz, A.homologyIncl_birth_generator k z hc⟩

/-- A nonzero attaching class dies; all other actual inclusion maps are bijective. -/
theorem positive_death
    (hne : A.attachingHomologyClass k ≠ 0) :
    Function.Surjective (simplicialHomologyIncl k A.inclusion p).hom ∧
    LinearMap.ker (simplicialHomologyIncl k A.inclusion p).hom =
      k ∙ A.attachingHomologyClass k ∧
    Module.finrank k (LinearMap.ker
      (simplicialHomologyIncl k A.inclusion p).hom) = 1 ∧
    ∀ r : ℕ, r ≠ p →
      Function.Bijective (simplicialHomologyIncl k A.inclusion r).hom := by
  have hqne : A.attachingQuotientClass k ≠ 0 := by
    intro hq
    apply hne
    apply (homologyKernelQuotient.{v,u,v} k
      (simplicialChainComplex K k) p).toLinearEquiv.injective
    rw [A.attachingHomologyClass_equiv k, hq]
    exact ((homologyKernelQuotient.{v,u,v} k
      (simplicialChainComplex K k) p).toLinearEquiv.map_zero).symm
  refine ⟨A.homologyIncl_surjective_of_quotient k
      (A.quotientIncl_surjective_of_ne k (by omega)),
    A.homologyIncl_ker_eq_span_attachingClass k,
    A.homologyIncl_death_kernel_finrank k hqne, ?_⟩
  intro r hr
  by_cases hq : r = p + 1
  · subst r
    exact A.homologyIncl_bijective_of_attachingClass_ne_zero k hqne
  · exact A.homologyIncl_bijective_of_ne k hq (by omega)

end SimplexAttachment

end TDA.Simplicial
