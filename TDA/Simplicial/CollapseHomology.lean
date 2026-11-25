import TDA.Simplicial.Collapse
import TDA.Simplicial.Homology
import Mathlib.Algebra.Homology.Homotopy

set_option autoImplicit false

/-!
# Elementary collapses induce homology isomorphisms

Let `(σ, τ)` be a free pair of `K` and `L = deletion K σ`. In the chain complex of `K`, the
coefficient `ε` of `σ` in the boundary of `τ` is a sign, so `ε * ε = 1`. Sending `σ` to `ε τ`
and every other face to zero is a degree-raising map `h`. Then `g = 1 - ∂ h - h ∂` is a chain
map of the chain complex of `K` whose values are chains of `L`: it fixes every face of `L`,
kills `τ`, and sends `σ` to `σ - ε ∂τ`, whose `σ`-coefficient is `1 - ε * ε = 0`. Its
corestriction `r` is a chain map to the chain complex of `L` with `r ∘ i = 1` for the inclusion
`i`, and `1 - i ∘ r = ∂ h + h ∂`. So the inclusion is a chain homotopy equivalence
(`IsFreePair.collapseHomotopyEquiv`), over every ring and in every degree.

The inclusion of the end of an elementary collapse, or of a finite collapse sequence, therefore
induces an isomorphism of ordinary simplicial homology in every degree
(`ElementaryCollapsesTo.isIso_simplicialHomologyIncl`, `CollapsesTo.isIso_simplicialHomologyIncl`).
The forward map is always the homology map of the actual inclusion; the retraction
(`IsFreePair.collapseRetraction`) and the homotopy enter only the proof that it is invertible.
Homology is the ordinary unaugmented homology of `simplicialChainComplex`. These are library
derivations; no source theorem is attributed to them.
-/

universe u v

namespace TDA.Simplicial

open CategoryTheory

variable {V : Type u} [LinearOrder V]
variable {K : PreAbstractSimplicialComplex V} {σ τ : Finset V}

namespace IsFreePair

/-- The coface of a free pair has exactly one more vertex than the free face. -/
theorem card_upper (hp : IsFreePair K σ τ) : τ.card = σ.card + 1 := by
  obtain ⟨a, ha, rfl⟩ := Finset.covBy_iff_exists_insert.mp hp.covBy
  exact Finset.card_insert_of_notMem ha

/-- The coface, as a face one degree above a face whose vertex set is `σ`. -/
private def upperFace (hp : IsFreePair K σ τ) {n : ℕ} (s : Face K n) (hs : s.1 = σ) :
    Face K (n + 1) :=
  ⟨τ, hp.upper_mem, by rw [hp.card_upper, ← hs, s.2.2]⟩

/-- A face whose deletion is the free face is the coface. -/
private theorem eq_upper_of_deletedFace (hp : IsFreePair K σ τ) {n : ℕ} (ρ : Face K (n + 1))
    (i : Fin (n + 2)) (h : (deletedFace K n ρ i).1 = σ) : ρ.1 = τ := by
  apply hp.eq_upper ρ.2.1
  rw [← h]
  exact Finset.erase_ssubset (Finset.orderEmbOfFin_mem _ _ _)

/-- Exactly one deletion of the coface is the free face. -/
private theorem existsUnique_deletedFace (hp : IsFreePair K σ τ) {n : ℕ} (u : Face K (n + 1))
    (hu : u.1 = τ) : ∃! i : Fin (n + 2), (deletedFace K n u i).1 = σ := by
  obtain ⟨a, ha, hτ⟩ := Finset.covBy_iff_exists_insert.mp hp.covBy
  have haτ : a ∈ u.1 := by rw [hu, ← hτ]; exact Finset.mem_insert_self a σ
  have haτ' : a ∈ Set.range (u.1.orderEmbOfFin u.2.2) := by
    rw [Finset.range_orderEmbOfFin]
    exact haτ
  obtain ⟨i, hi⟩ := haτ'
  refine ⟨i, ?_, fun j hj => ?_⟩
  · change u.1.erase (u.1.orderEmbOfFin u.2.2 i) = σ
    rw [hi, hu, ← hτ, Finset.erase_insert ha]
  · have hj' : u.1.erase (u.1.orderEmbOfFin u.2.2 j) = u.1.erase (u.1.orderEmbOfFin u.2.2 i) := by
      change (deletedFace K n u j).1 = u.1.erase (u.1.orderEmbOfFin u.2.2 i)
      rw [hj, hi, hu, ← hτ, Finset.erase_insert ha]
    apply (u.1.orderEmbOfFin u.2.2).injective
    by_contra hne
    have hmem : u.1.orderEmbOfFin u.2.2 j ∈ u.1.erase (u.1.orderEmbOfFin u.2.2 i) :=
      Finset.mem_erase.mpr ⟨hne, Finset.orderEmbOfFin_mem _ _ _⟩
    rw [← hj'] at hmem
    exact (Finset.notMem_erase _ _) hmem

variable (R : Type v) [Ring R]

/-- The coefficient of the free face in the boundary of the coface. -/
private noncomputable def coeff (hp : IsFreePair K σ τ) {n : ℕ} (s : Face K n) (hs : s.1 = σ) :
    R :=
  boundary K R n (Finsupp.single (hp.upperFace s hs) 1) s

/-- The boundary coefficient of a face at a face with vertex set `σ`. -/
private theorem boundary_single_apply (hp : IsFreePair K σ τ) {n : ℕ} (ρ : Face K (n + 1))
    (s : Face K n) (hs : s.1 = σ) (a : R) :
    boundary K R n (Finsupp.single ρ a) s =
      if ρ.1 = τ then a * coeff R hp s hs else 0 := by
  have hsingle : Finsupp.single ρ a = a • Finsupp.single ρ (1 : R) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  split_ifs with hρ
  · have hρu : ρ = hp.upperFace s hs := Subtype.ext hρ
    subst hρu
    rw [coeff, hsingle, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · rw [boundary_single, Finsupp.smul_apply, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_zero, smul_zero]
    intro i _
    rw [Finsupp.single_apply, ite_eq_right]
    intro he
    exact hρ (hp.eq_upper_of_deletedFace ρ i (by rw [he]; exact hs))

/-- The coefficient of the free face in the boundary of the coface is a sign. -/
private theorem coeff_mul_self (hp : IsFreePair K σ τ) {n : ℕ} (s : Face K n) (hs : s.1 = σ) :
    coeff R hp s hs * coeff R hp s hs = 1 := by
  obtain ⟨i, hi, huniq⟩ := hp.existsUnique_deletedFace (hp.upperFace s hs) rfl
  have hc : coeff R hp s hs = (-1 : R) ^ (i : ℕ) := by
    rw [coeff, boundary_single, one_smul, Finsupp.finsetSum_apply,
      Finset.sum_eq_single i]
    · rw [Finsupp.single_apply, ite_eq_left (Subtype.ext (hi.trans hs.symm))]
    · intro j _ hj
      rw [Finsupp.single_apply, ite_eq_right]
      intro he
      exact hj (huniq j ((congrArg Subtype.val he).trans hs))
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- Send the free face to the coface, scaled by the coefficient, and every other face to zero. -/
private noncomputable def push (hp : IsFreePair K σ τ) (n : ℕ) :
    Chain K R n →ₗ[R] Chain K R (n + 1) :=
  Finsupp.linearCombination R (fun s : Face K n =>
    if hs : s.1 = σ then Finsupp.single (hp.upperFace s hs) (coeff R hp s hs) else 0)

private theorem push_single (hp : IsFreePair K σ τ) {n : ℕ} (s : Face K n) (a : R) :
    push R hp n (Finsupp.single s a) =
      if hs : s.1 = σ then Finsupp.single (hp.upperFace s hs) (a * coeff R hp s hs) else 0 := by
  rw [push, Finsupp.linearCombination_single]
  split_ifs with hs
  · rw [Finsupp.smul_single, smul_eq_mul]
  · exact smul_zero a

/-- With `s₀` the face of degree `n` on `σ`, the map `push` reads off the `s₀` coordinate. -/
private theorem push_apply (hp : IsFreePair K σ τ) {n : ℕ} (s₀ : Face K n) (hs₀ : s₀.1 = σ)
    (x : Chain K R n) :
    push R hp n x = Finsupp.single (hp.upperFace s₀ hs₀) (x s₀ * coeff R hp s₀ hs₀) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, Finsupp.add_apply, add_mul, Finsupp.single_add]
  | single s a =>
    rw [push_single]
    split_ifs with hs
    · have e : s = s₀ := Subtype.ext (hs.trans hs₀.symm)
      subst e
      rw [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (fun e => hs (by rw [← e]; exact hs₀)), zero_mul,
        Finsupp.single_zero]

/-- Without a face of degree `n` on `σ`, the map `push` vanishes. -/
private theorem push_eq_zero (hp : IsFreePair K σ τ) {n : ℕ} (hn : σ.card ≠ n + 1)
    (x : Chain K R n) : push R hp n x = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, add_zero]
  | single s a =>
    rw [push_single, dite_eq_right]
    intro hs
    exact hn (hs ▸ s.2.2)

/-- The values of `push` are supported at the coface. -/
private theorem push_apply_of_ne (hp : IsFreePair K σ τ) {n : ℕ} (x : Chain K R n)
    (s : Face K (n + 1)) (hs : s.1 ≠ τ) : push R hp n x s = 0 := by
  by_cases hn : σ.card = n + 1
  · obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Face K n, s₀.1 = σ := ⟨⟨σ, hp.lower_mem, hn⟩, rfl⟩
    rw [push_apply R hp s₀ hs₀, Finsupp.single_eq_of_ne]
    intro e
    exact hs (by rw [e]; rfl)
  · rw [push_eq_zero R hp hn, Finsupp.zero_apply]

/-- `push` vanishes on the boundary of every face other than the coface. -/
private theorem push_boundary_single (hp : IsFreePair K σ τ) {n : ℕ} (ρ : Face K (n + 1))
    (hρ : ρ.1 ≠ τ) (a : R) : push R hp n (boundary K R n (Finsupp.single ρ a)) = 0 := by
  by_cases hn : σ.card = n + 1
  · obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Face K n, s₀.1 = σ := ⟨⟨σ, hp.lower_mem, hn⟩, rfl⟩
    rw [push_apply R hp s₀ hs₀, boundary_single_apply R hp ρ s₀ hs₀, ite_eq_right hρ, zero_mul,
      Finsupp.single_zero]
  · exact push_eq_zero R hp hn _

/-- The chain map `1 - ∂ h - h ∂` on the chain complex of `K`. -/
private noncomputable def proj (hp : IsFreePair K σ τ) : (n : ℕ) → Chain K R n →ₗ[R] Chain K R n
  | 0 => LinearMap.id - (boundary K R 0).comp (push R hp 0)
  | n + 1 => LinearMap.id - (boundary K R (n + 1)).comp (push R hp (n + 1)) -
      (push R hp n).comp (boundary K R n)

/-- `proj` commutes with the boundary. -/
private theorem boundary_comp_proj (hp : IsFreePair K σ τ) (n : ℕ) :
    (boundary K R n).comp (proj R hp (n + 1)) = (proj R hp n).comp (boundary K R n) := by
  have bb : ∀ (m : ℕ) (y : Chain K R (m + 2)),
      boundary K R m (boundary K R (m + 1) y) = 0 :=
    fun m y => LinearMap.congr_fun (boundary_comp_boundary K R m) y
  apply LinearMap.ext
  intro x
  cases n with
  | zero =>
    simp only [proj, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      bb, sub_zero]
  | succ n =>
    simp only [proj, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      bb, map_zero, sub_zero]

/-- `proj` fixes every face of the deletion. -/
private theorem proj_single_of_mem (hp : IsFreePair K σ τ) {n : ℕ} (ρ : Face K n)
    (hρ : ρ.1 ∈ deletion K σ) (a : R) :
    proj R hp n (Finsupp.single ρ a) = Finsupp.single ρ a := by
  have hρ' := (hp.mem_deletion_iff).1 hρ
  have hpush : push R hp n (Finsupp.single ρ a) = 0 := by
    rw [push_single, dite_eq_right hρ'.2.1]
  cases n with
  | zero =>
    simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hpush,
      map_zero, sub_zero]
  | succ n =>
    simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hpush,
      map_zero, sub_zero, push_boundary_single R hp ρ hρ'.2.2]

/-- The values of `proj` vanish at the two faces outside the deletion. -/
private theorem proj_apply_of_notMem (hp : IsFreePair K σ τ) {n : ℕ} (x : Chain K R n)
    (s : Face K n) (hs : s.1 ∉ deletion K σ) : proj R hp n x s = 0 := by
  have hst : s.1 = σ ∨ s.1 = τ := by
    by_contra h
    push Not at h
    exact hs ((hp.mem_deletion_iff).2 ⟨s.2.1, h.1, h.2⟩)
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | single ρ a =>
    rcases hst with hsσ | hsτ
    · -- `s` is the free face; then `σ` lives in degree `n`, and `τ` does not.
      have hpush : push R hp n (Finsupp.single ρ a) =
          Finsupp.single (hp.upperFace s hsσ) ((Finsupp.single ρ a) s * coeff R hp s hsσ) :=
        push_apply R hp s hsσ _
      have hbd : boundary K R n (push R hp n (Finsupp.single ρ a)) s =
          (Finsupp.single ρ a) s * coeff R hp s hsσ * coeff R hp s hsσ := by
        rw [hpush, boundary_single_apply R hp _ s hsσ,
          ite_eq_left (show (hp.upperFace s hsσ).1 = τ from rfl)]
      have hmain : (Finsupp.single ρ a) s -
          boundary K R n (push R hp n (Finsupp.single ρ a)) s = 0 := by
        rw [hbd, mul_assoc, coeff_mul_self, mul_one, sub_self]
      cases n with
      | zero =>
        simpa only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          Finsupp.sub_apply] using hmain
      | succ n =>
        simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          Finsupp.sub_apply]
        rw [push_apply_of_ne R hp _ s (fun h => ?_), sub_zero]
        · exact hmain
        · have := hp.card_upper
          rw [← h, ← hsσ, s.2.2] at this
          omega
    · -- `s` is the coface; then `n = m + 1` and `σ` lives in degree `m`.
      cases n with
      | zero =>
        exfalso
        have h1 := hp.card_upper
        have h2 : σ.Nonempty := (K.isRelLowerSet_faces hp.lower_mem).1
        rw [← hsτ, s.2.2] at h1
        have := h2.card_pos
        omega
      | succ m =>
        have hcard : σ.card = m + 1 := by
          have h1 := hp.card_upper
          rw [← hsτ, s.2.2] at h1
          omega
        let s₀ : Face K m := ⟨σ, hp.lower_mem, hcard⟩
        have hs₀ : s₀.1 = σ := rfl
        have hsu : hp.upperFace s₀ hs₀ = s := Subtype.ext hsτ.symm
        have hpush0 : push R hp (m + 1) (Finsupp.single ρ a) = 0 :=
          push_eq_zero R hp (by omega) _
        have hpush1 : push R hp m (boundary K R m (Finsupp.single ρ a)) s =
            (Finsupp.single ρ a) s := by
          rw [push_apply R hp s₀ hs₀, hsu, Finsupp.single_eq_same,
            boundary_single_apply R hp ρ s₀ hs₀]
          split_ifs with hρ
          · have e : ρ = s := Subtype.ext (hρ.trans hsτ.symm)
            subst e
            rw [Finsupp.single_eq_same, mul_assoc, coeff_mul_self, mul_one]
          · rw [zero_mul, Finsupp.single_eq_of_ne]
            intro e
            exact hρ (by rw [← e]; exact hsτ)
        simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          Finsupp.sub_apply, hpush0, map_zero, sub_zero, hpush1, sub_self]

omit [LinearOrder V] in
private theorem faceIncl_injective (n : ℕ) :
    Function.Injective (faceIncl (deletion_le K σ) n) :=
  fun _ _ h => Subtype.ext (congrArg (fun x : Face K n => x.1) h)

/-- Corestriction of a chain of `K` to the faces of the deletion. -/
private noncomputable def restrict (n : ℕ) :
    Chain K R n →ₗ[R] Chain (deletion K σ) R n :=
  Finsupp.lcomapDomain (faceIncl (deletion_le K σ) n) (faceIncl_injective n)

omit [LinearOrder V] in
private theorem chainIncl_injective (n : ℕ) :
    Function.Injective (chainIncl R (deletion_le K σ) n) :=
  Finsupp.mapDomain_injective (faceIncl_injective n)

/-- The retraction of chains: `proj` followed by corestriction. -/
private noncomputable def retract (hp : IsFreePair K σ τ) (n : ℕ) :
    Chain K R n →ₗ[R] Chain (deletion K σ) R n :=
  (restrict R n).comp (proj R hp n)

private theorem chainIncl_comp_retract (hp : IsFreePair K σ τ) (n : ℕ) :
    (chainIncl R (deletion_le K σ) n).comp (retract R hp n) = proj R hp n := by
  apply LinearMap.ext
  intro x
  change Finsupp.mapDomain _ (Finsupp.comapDomain _ _ _) = _
  apply Finsupp.mapDomain_comapDomain _ (faceIncl_injective n)
  intro s hs
  by_cases h : s.1 ∈ deletion K σ
  · exact ⟨⟨s.1, h, s.2.2⟩, rfl⟩
  · exact absurd (proj_apply_of_notMem R hp x s h) (Finsupp.mem_support_iff.mp hs)

private theorem retract_comp_chainIncl (hp : IsFreePair K σ τ) (n : ℕ) :
    (retract R hp n).comp (chainIncl R (deletion_le K σ) n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro t a
  apply chainIncl_injective R n
  change (chainIncl R (deletion_le K σ) n).comp (retract R hp n)
      (chainIncl R (deletion_le K σ) n (Finsupp.single t a)) = _
  rw [chainIncl_comp_retract, LinearMap.id_apply, chainIncl_single]
  exact proj_single_of_mem R hp _ t.2.1 a

private theorem boundary_comp_retract (hp : IsFreePair K σ τ) (n : ℕ) :
    (boundary (deletion K σ) R n).comp (retract R hp (n + 1)) =
      (retract R hp n).comp (boundary K R n) := by
  apply LinearMap.ext
  intro x
  apply chainIncl_injective R n
  have h1 := congrArg (fun f => f (retract R hp (n + 1) x))
    (boundary_chainIncl R (deletion_le K σ) n)
  simp only [LinearMap.comp_apply] at h1
  have h2 := congrArg (fun f => f x) (chainIncl_comp_retract R hp (n + 1))
  have h3 := congrArg (fun f => f (boundary K R n x)) (chainIncl_comp_retract R hp n)
  have h4 := congrArg (fun f => f x) (boundary_comp_proj R hp n)
  simp only [LinearMap.comp_apply] at h2 h3 h4
  simp only [LinearMap.comp_apply]
  rw [← h1, h2, h3, h4]

/-- The retraction chain map onto the deletion of a free face. -/
noncomputable def collapseRetraction (hp : IsFreePair K σ τ) :
    simplicialChainComplex K R ⟶ simplicialChainComplex (deletion K σ) R :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (retract R hp n)) (by
    intro n
    apply ModuleCat.hom_ext
    simp only [simplicialChainComplex_d]
    exact boundary_comp_retract R hp n)

/-- The degree-`n` component of the retraction. -/
private theorem collapseRetraction_f (hp : IsFreePair K σ τ) (n : ℕ) :
    (collapseRetraction R hp).f n = ModuleCat.ofHom (retract R hp n) := rfl

/-- The retraction is a left inverse of the inclusion chain map. -/
theorem simplicialChainIncl_comp_collapseRetraction (hp : IsFreePair K σ τ) :
    simplicialChainIncl R (deletion_le K σ) ≫ collapseRetraction R hp = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, simplicialChainIncl_f,
    collapseRetraction_f]
  apply ModuleCat.hom_ext
  exact retract_comp_chainIncl R hp n

private noncomputable def homotopyComponent (hp : IsFreePair K σ τ) (i j : ℕ) :
    (simplicialChainComplex K R).X i ⟶ (simplicialChainComplex K R).X j :=
  if hij : i + 1 = j then
    ModuleCat.ofHom (push R hp i) ≫
      eqToHom (congrArg (fun k => (simplicialChainComplex K R).X k) hij)
  else 0

private theorem homotopyComponent_succ (hp : IsFreePair K σ τ) (i : ℕ) :
    homotopyComponent R hp i (i + 1) = ModuleCat.ofHom (push R hp i) := by
  simp [homotopyComponent]

/-- The identity of the chain complex of `K` is homotopic to the retraction followed by the
inclusion, with homotopy `push`. -/
private noncomputable def collapseHomotopy (hp : IsFreePair K σ τ) :
    Homotopy (𝟙 (simplicialChainComplex K R))
      (collapseRetraction R hp ≫ simplicialChainIncl R (deletion_le K σ)) where
  hom := homotopyComponent R hp
  zero i j hij := dite_eq_right hij
  comm i := by
    have hg : ∀ n, (collapseRetraction R hp ≫ simplicialChainIncl R (deletion_le K σ)).f n =
        ModuleCat.ofHom (proj R hp n) := by
      intro n
      simp only [HomologicalComplex.comp_f, simplicialChainIncl_f, collapseRetraction_f]
      apply ModuleCat.hom_ext
      exact chainIncl_comp_retract R hp n
    cases i with
    | zero =>
      rw [prevD_eq (j' := 1) (w := by simp), dNext_eq_zero _ _ (by simp), zero_add, hg]
      simp only [homotopyComponent_succ, simplicialChainComplex_d, HomologicalComplex.id_f]
      apply ModuleCat.hom_ext
      change LinearMap.id = (boundary K R 0).comp (push R hp 0) + proj R hp 0
      simp only [proj]
      abel
    | succ n =>
      rw [dNext_eq (i' := n) (w := by simp), prevD_eq (j' := n + 2) (w := by simp), hg]
      simp only [homotopyComponent_succ, simplicialChainComplex_d, HomologicalComplex.id_f]
      apply ModuleCat.hom_ext
      change LinearMap.id = (push R hp n).comp (boundary K R n) +
        (boundary K R (n + 1)).comp (push R hp (n + 1)) + proj R hp (n + 1)
      simp only [proj]
      abel

/-- The inclusion of the deletion of a free face is a chain homotopy equivalence, with the
inclusion chain map as its forward map. -/
noncomputable def collapseHomotopyEquiv (hp : IsFreePair K σ τ) :
    HomotopyEquiv (simplicialChainComplex (deletion K σ) R) (simplicialChainComplex K R) where
  hom := simplicialChainIncl R (deletion_le K σ)
  inv := collapseRetraction R hp
  homotopyHomInvId := Homotopy.ofEq (simplicialChainIncl_comp_collapseRetraction R hp)
  homotopyInvHomId := (collapseHomotopy R hp).symm

/-- The forward map of `collapseHomotopyEquiv` is the inclusion chain map. -/
@[simp] theorem collapseHomotopyEquiv_hom (hp : IsFreePair K σ τ) :
    (collapseHomotopyEquiv R hp).hom = simplicialChainIncl R (deletion_le K σ) := rfl

/-- The inverse of `collapseHomotopyEquiv` is the retraction. -/
@[simp] theorem collapseHomotopyEquiv_inv (hp : IsFreePair K σ τ) :
    (collapseHomotopyEquiv R hp).inv = collapseRetraction R hp := rfl

/-- Deleting a free face does not change ordinary homology: the inclusion of the deletion
induces an isomorphism in every degree, over every ring. -/
theorem isIso_simplicialHomologyIncl (hp : IsFreePair K σ τ) (n : ℕ) :
    IsIso (simplicialHomologyIncl R (deletion_le K σ) n) :=
  (HomotopyEquiv.toHomologyIso (collapseHomotopyEquiv R hp) n).isIso_hom

end IsFreePair

variable (R : Type v) [Ring R] {L : PreAbstractSimplicialComplex V}

/-- The inclusion of the end of an elementary collapse induces an isomorphism of ordinary
homology in every degree, over every ring. -/
theorem ElementaryCollapsesTo.isIso_simplicialHomologyIncl (h : ElementaryCollapsesTo K L)
    (hle : L ≤ K) (n : ℕ) : IsIso (simplicialHomologyIncl R hle n) := by
  obtain ⟨σ, τ, hp, rfl⟩ := h
  exact hp.isIso_simplicialHomologyIncl R n

/-- The inclusion of the end of a finite collapse sequence induces an isomorphism of ordinary
homology in every degree, over every ring. -/
theorem CollapsesTo.isIso_simplicialHomologyIncl (h : CollapsesTo K L) (hle : L ≤ K)
    (n : ℕ) : IsIso (simplicialHomologyIncl R hle n) := by
  induction h with
  | refl => exact simplicialHomologyIncl_isIso_of_eq R hle rfl n
  | @tail M N hKM hMN ih =>
    have hNM : N ≤ M := hMN.lt.le
    have hMK : M ≤ K := CollapsesTo.le hKM
    have := ih hMK
    have := hMN.isIso_simplicialHomologyIncl R hNM n
    have e : simplicialHomologyIncl R hle n =
        simplicialHomologyIncl R hNM n ≫ simplicialHomologyIncl R hMK n :=
      simplicialHomologyIncl_comp R hNM hMK n
    rw [e]
    infer_instance

/-- The homology isomorphism of a collapse; its forward map is the inclusion. -/
noncomputable def CollapsesTo.simplicialHomologyIso (h : CollapsesTo K L) (n : ℕ) :
    simplicialHomology L R n ≅ simplicialHomology K R n :=
  haveI := h.isIso_simplicialHomologyIncl R h.le n
  asIso (simplicialHomologyIncl R h.le n)

/-- The forward map of `CollapsesTo.simplicialHomologyIso` is the homology inclusion. -/
@[simp] theorem CollapsesTo.simplicialHomologyIso_hom (h : CollapsesTo K L) (n : ℕ) :
    (h.simplicialHomologyIso R n).hom = simplicialHomologyIncl R h.le n := rfl

end TDA.Simplicial
