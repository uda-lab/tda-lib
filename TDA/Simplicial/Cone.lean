import TDA.Simplicial.H0Augmentation
import TDA.Simplicial.FiniteDimensionalHomology
import Mathlib.Order.Fin.Tuple

/-!
# Apex cones are acyclic

An apex cone has a least vertex which belongs to every cone face.  The least-vertex
convention puts the apex at position zero in the ordered enumeration, so the
cone operator is an unsigned contracting operator in the displayed formulas.
Its degree-zero endpoint is the coefficient-sum projection onto the apex.
-/

universe u v

namespace TDA.Simplicial

open CategoryTheory Module
open CategoryTheory.Limits
open scoped BigOperators

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

variable {V : Type u} [LinearOrder V]

/-- A simplicial complex with a least vertex which cones every face to a face. -/
structure IsApexCone (K : PreAbstractSimplicialComplex V) (v : V) : Prop where
  apex_mem : {v} ∈ K
  insert_mem : ∀ s ∈ K, insert v s ∈ K
  apex_le : ∀ s ∈ K, ∀ w ∈ s, v ≤ w

/-- The top complex is an apex cone whenever `v` is below every vertex. -/
theorem isApexCone_top (v : V) (hv : ∀ w, v ≤ w) :
    IsApexCone (⊤ : PreAbstractSimplicialComplex V) v := by
  refine ⟨?_, ?_, ?_⟩
  · change ({v} : Finset V).Nonempty
    simp
  · intro s hs
    change (insert v s).Nonempty
    simp
  · intro s hs w hw
    exact hv w

/-- A finite nonempty linearly ordered vertex type has a top-complex apex. -/
theorem exists_isApexCone_top [Finite V] [Nonempty V] :
    ∃ v, IsApexCone (⊤ : PreAbstractSimplicialComplex V) v := by
  obtain ⟨v, hv⟩ := Finite.exists_min (fun w : V => w)
  exact ⟨v, isApexCone_top v hv⟩

namespace IsApexCone

variable {K : PreAbstractSimplicialComplex V} {v : V}

/-- The apex as a zero-dimensional face. -/
def apexFace (hK : IsApexCone K v) : Face K 0 :=
  ⟨{v}, hK.apex_mem, by simp⟩

/-- The cone on a face which does not already contain the apex. -/
def coneFace (hK : IsApexCone K v) {n : ℕ} (s : Face K n) (hs : v ∉ s.1) :
    Face K (n + 1) :=
  ⟨insert v s.1, hK.insert_mem s.1 s.2.1, by
    rw [Finset.card_insert_of_notMem hs, s.2.2]⟩

private theorem coneFace_orderEmb (hK : IsApexCone K v) {n : ℕ}
    (s : Face K n) (hs : v ∉ s.1) :
    ∀ i, (hK.coneFace s hs).1.orderEmbOfFin (hK.coneFace s hs).2.2 i =
      ((Fin.cons (n := n + 1) v (fun j => s.1.orderEmbOfFin s.2.2 j) :
        Fin (n + 1 + 1) → V) i) := by
  intro i
  have horder :
      (Fin.cons (n := n + 1) v (fun j => s.1.orderEmbOfFin s.2.2 j) :
          Fin (n + 1 + 1) → V) =
        (hK.coneFace s hs).1.orderEmbOfFin (hK.coneFace s hs).2.2 := by
    apply Finset.orderEmbOfFin_unique (hK.coneFace s hs).2.2
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Finset.mem_insert_self v s.1
      · exact Finset.mem_insert_of_mem (Finset.orderEmbOfFin_mem s.1 s.2.2 j)
    · apply Fin.strictMono_cons.mpr
      refine ⟨?_, (s.1.orderEmbOfFin s.2.2).strictMono⟩
      intro j
      have hle := hK.apex_le (insert v s.1) (hK.insert_mem s.1 s.2.1)
        (s.1.orderEmbOfFin s.2.2 j)
        (Finset.mem_insert_of_mem (Finset.orderEmbOfFin_mem s.1 s.2.2 j))
      have hne : v ≠ s.1.orderEmbOfFin s.2.2 j := by
        intro h
        exact hs (h.symm ▸ Finset.orderEmbOfFin_mem s.1 s.2.2 j)
      exact lt_of_le_of_ne hle hne
  exact congrFun horder.symm i

private theorem deletedFace_coneFace_zero (hK : IsApexCone K v) {n : ℕ}
    (s : Face K n) (hs : v ∉ s.1) :
    deletedFace K n (hK.coneFace s hs) 0 = s := by
  apply Subtype.ext
  change (hK.coneFace s hs).1.erase
      ((hK.coneFace s hs).1.orderEmbOfFin (hK.coneFace s hs).2.2 0) = s.1
  rw [coneFace_orderEmb hK s hs 0]
  change (insert v s.1).erase v = s.1
  simp [hs]

private theorem deletedFace_coneFace_succ (hK : IsApexCone K v) {n : ℕ}
    (s : Face K (n + 1)) (hs : v ∉ s.1) (j : Fin (n + 2)) :
    deletedFace K (n + 1) (hK.coneFace s hs) j.succ =
      hK.coneFace (deletedFace K n s j) (by
        intro hvj
        exact hs (Finset.erase_subset _ _ hvj)) := by
  apply Subtype.ext
  change (hK.coneFace s hs).1.erase
      ((hK.coneFace s hs).1.orderEmbOfFin (hK.coneFace s hs).2.2 j.succ) =
    insert v (s.1.erase (s.1.orderEmbOfFin s.2.2 j))
  rw [coneFace_orderEmb hK s hs j.succ]
  have hne : v ≠ s.1.orderEmbOfFin s.2.2 j := by
    intro h
    exact hs (h.symm ▸ Finset.orderEmbOfFin_mem s.1 s.2.2 j)
  change (insert v s.1).erase
      ((Fin.cons v (fun j => s.1.orderEmbOfFin s.2.2 j) : Fin (n + 3) → V) j.succ) =
    insert v (s.1.erase (s.1.orderEmbOfFin s.2.2 j))
  simp only [Fin.cons_succ]
  exact Finset.erase_insert_of_ne hne

private theorem orderEmbOfFin_zero_of_mem (hK : IsApexCone K v) {n : ℕ}
    (s : Face K (n + 1)) (hs : v ∈ s.1) :
    s.1.orderEmbOfFin s.2.2 0 = v := by
  change s.1.orderEmbOfFin s.2.2 (⟨0, by omega⟩ : Fin (n + 2)) = v
  rw [Finset.orderEmbOfFin_zero s.2.2 (by omega)]
  apply le_antisymm
  · exact Finset.min'_le _ _ hs
  · exact Finset.le_min' _ _ _ (fun w hw => hK.apex_le s s.2.1 w hw)

private theorem deletedFace_zero_of_mem (hK : IsApexCone K v) {n : ℕ}
    (s : Face K (n + 1)) (hs : v ∈ s.1) :
    (deletedFace K n s 0).1 = s.1.erase v := by
  change s.1.erase (s.1.orderEmbOfFin s.2.2 0) = s.1.erase v
  rw [orderEmbOfFin_zero_of_mem hK s hs]

private theorem coneFace_deletedFace_zero_of_mem (hK : IsApexCone K v) {n : ℕ}
    (s : Face K (n + 1)) (hs : v ∈ s.1) :
    hK.coneFace (deletedFace K n s 0) (by
      rw [deletedFace_zero_of_mem hK s hs]
      exact Finset.notMem_erase _ _) = s := by
  apply Subtype.ext
  change insert v (deletedFace K n s 0).1 = s.1
  rw [deletedFace_zero_of_mem hK s hs]
  exact Finset.insert_erase hs

private theorem deletedFace_succ_mem_of_mem (hK : IsApexCone K v) {n : ℕ}
    (s : Face K (n + 1)) (hs : v ∈ s.1) (j : Fin (n + 1)) :
    v ∈ (deletedFace K n s j.succ).1 := by
  change v ∈ s.1.erase (s.1.orderEmbOfFin s.2.2 j.succ)
  refine Finset.mem_erase.mpr ⟨?_, hs⟩
  intro h
  have he : s.1.orderEmbOfFin s.2.2 0 =
      s.1.orderEmbOfFin s.2.2 j.succ := by
    exact (orderEmbOfFin_zero_of_mem hK s hs).trans h
  have hi := (s.1.orderEmbOfFin s.2.2).injective he
  have hi' := congrArg (fun i : Fin (n + 2) => i.1) hi
  have hjpos : 0 < (j.succ : ℕ) := by simp
  exact (Nat.ne_of_gt hjpos) hi'.symm

private theorem deletedFace_coneFace_succ_zero (hK : IsApexCone K v)
    (s : Face K 0) (hs : v ∉ s.1) :
    deletedFace K 0 (hK.coneFace s hs) (Fin.succ 0) = hK.apexFace := by
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp s.2.2
  apply Subtype.ext
  change (hK.coneFace s hs).1.erase
      ((hK.coneFace s hs).1.orderEmbOfFin (hK.coneFace s hs).2.2 (Fin.succ 0)) =
    (hK.apexFace).1
  rw [coneFace_orderEmb hK s hs (Fin.succ 0)]
  change (insert v s.1).erase
      ((Fin.cons v (fun j => s.1.orderEmbOfFin s.2.2 j) : Fin 2 → V) (Fin.succ 0)) = {v}
  have hvw : v ≠ w := by
    intro hvw
    apply hs
    rw [hw, hvw]
    exact Finset.mem_singleton_self _
  simpa [hw] using
    (Finset.erase_insert_of_ne hvw :
      (insert v ({w} : Finset V)).erase w =
        insert v (({w} : Finset V).erase w))

/-- The linear cone operator on chains. -/
noncomputable def coneOperator (hK : IsApexCone K v) (R : Type v) [Ring R] (n : ℕ) :
    Chain K R n →ₗ[R] Chain K R (n + 1) :=
  Finsupp.linearCombination R
    (fun s : Face K n => if h : v ∈ s.1 then 0 else Finsupp.single (hK.coneFace s h) 1)

/-- The cone operator sends a basis face not containing the apex to its cone. -/
@[simp]
theorem coneOperator_single_of_notMem (hK : IsApexCone K v) (R : Type v) [Ring R]
    {n : ℕ} (s : Face K n) (a : R) (hs : v ∉ s.1) :
    hK.coneOperator R n (Finsupp.single s a) = Finsupp.single (hK.coneFace s hs) a := by
  simp [coneOperator, hs]

/-- The cone operator vanishes on a basis face already containing the apex. -/
@[simp]
theorem coneOperator_single_of_mem (hK : IsApexCone K v) (R : Type v) [Ring R]
    {n : ℕ} (s : Face K n) (a : R) (hs : v ∈ s.1) :
    hK.coneOperator R n (Finsupp.single s a) = 0 := by
  simp [coneOperator, hs]

/-- In positive degree, the cone operator is a contracting homotopy. -/
theorem boundary_coneOperator_add (hK : IsApexCone K v) (R : Type v) [Ring R] (n : ℕ)
    (c : Chain K R (n + 1)) :
    boundary K R (n + 1) (hK.coneOperator R (n + 1) c) +
        hK.coneOperator R n (boundary K R n c) = c := by
  classical
  let f : Chain K R (n + 1) →ₗ[R] Chain K R (n + 1) :=
    (boundary K R (n + 1)).comp (hK.coneOperator R (n + 1)) +
      (hK.coneOperator R n).comp (boundary K R n)
  have hf : f = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s a
    change boundary K R (n + 1) (hK.coneOperator R (n + 1) (Finsupp.single s a)) +
      hK.coneOperator R n (boundary K R n (Finsupp.single s a)) = Finsupp.single s a
    by_cases hs : v ∈ s.1
    · rw [show hK.coneOperator R (n + 1) (Finsupp.single s a) = 0 from
          hK.coneOperator_single_of_mem R s a hs]
      simp only [map_zero, zero_add]
      rw [boundary_single, Fin.sum_univ_succ]
      simp only [map_smul, map_add, map_sum]
      have hzero : v ∉ (deletedFace K n s 0).1 := by
        rw [deletedFace_zero_of_mem hK s hs]
        exact Finset.notMem_erase _ _
      rw [hK.coneOperator_single_of_notMem R _ _ hzero]
      rw [coneFace_deletedFace_zero_of_mem hK s hs]
      have htail (j : Fin (n + 1)) :
          hK.coneOperator R n
              (Finsupp.single (deletedFace K n s j.succ)
                ((-1 : R) ^ (j.succ : ℕ))) = 0 := by
        exact hK.coneOperator_single_of_mem R _ _
          (deletedFace_succ_mem_of_mem hK s hs j)
      simp_rw [htail]
      simp
    · let hdel : ∀ j : Fin (n + 2), v ∉ (deletedFace K n s j).1 := fun j => by
        intro hvj
        exact hs (Finset.erase_subset _ _ hvj)
      have hface (j : Fin (n + 2)) :
          deletedFace K (n + 1) (hK.coneFace s hs) j.succ =
            hK.coneFace (deletedFace K n s j) (hdel j) := by
        apply Subtype.ext
        change (hK.coneFace s hs).1.erase
            ((hK.coneFace s hs).1.orderEmbOfFin (hK.coneFace s hs).2.2 j.succ) =
          insert v (s.1.erase (s.1.orderEmbOfFin s.2.2 j))
        rw [coneFace_orderEmb hK s hs j.succ]
        have hne : v ≠ s.1.orderEmbOfFin s.2.2 j := by
          intro h
          exact hs (h.symm ▸ Finset.orderEmbOfFin_mem s.1 s.2.2 j)
        change (insert v s.1).erase
            ((Fin.cons v (fun j => s.1.orderEmbOfFin s.2.2 j) : Fin (n + 3) → V) j.succ) =
          insert v (s.1.erase (s.1.orderEmbOfFin s.2.2 j))
        simp only [Fin.cons_succ]
        exact Finset.erase_insert_of_ne hne
      have hzero : deletedFace K (n + 1) (hK.coneFace s hs) 0 = s :=
        deletedFace_coneFace_zero hK s hs
      have hsign (j : Fin (n + 2)) :
          (-1 : R) ^ (j.succ : ℕ) = -((-1 : R) ^ (j : ℕ)) := by
        simp [pow_succ]
      have hboundary :
          boundary K R (n + 1)
              (hK.coneOperator R (n + 1) (Finsupp.single s a)) =
            a • (Finsupp.single s 1 +
              ∑ j : Fin (n + 2),
                Finsupp.single (hK.coneFace (deletedFace K n s j) (hdel j))
                  ((-1 : R) ^ (j.succ : ℕ))) := by
        rw [hK.coneOperator_single_of_notMem R s a hs, boundary_single,
          Fin.sum_univ_succ, hzero]
        simp_rw [hface]
        simp
      have hcone :
          hK.coneOperator R n (boundary K R n (Finsupp.single s a)) =
            a • ∑ j : Fin (n + 2),
              Finsupp.single (hK.coneFace (deletedFace K n s j) (hdel j))
                ((-1 : R) ^ (j : ℕ)) := by
        rw [boundary_single]
        simp only [map_smul, map_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [hK.coneOperator_single_of_notMem R _ _ (hdel j)]
      have hcancel :
          (∑ j : Fin (n + 2),
              Finsupp.single (hK.coneFace (deletedFace K n s j) (hdel j))
                ((-1 : R) ^ (j.succ : ℕ))) +
            ∑ j : Fin (n + 2),
              Finsupp.single (hK.coneFace (deletedFace K n s j) (hdel j))
                ((-1 : R) ^ (j : ℕ)) = 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro j hj
        rw [hsign j]
        apply Finsupp.ext
        intro x
        by_cases hx : x = hK.coneFace (deletedFace K n s j) (hdel j)
        · subst x
          simp
        · simp
      rw [hboundary, hcone, ← smul_add, add_assoc, hcancel]
      simp
  exact LinearMap.congr_fun hf c

/-- In degree zero, the cone homotopy ends at the augmentation projection. -/
theorem boundary_coneOperator_zero (hK : IsApexCone K v) (k : Type v) [Field k]
    (c : Chain K k 0) :
    boundary K k 0 (hK.coneOperator k 0 c) =
      c - Finsupp.single hK.apexFace (zeroChainSum K k c) := by
  classical
  let f : Chain K k 0 →ₗ[k] Chain K k 0 :=
    (boundary K k 0).comp (hK.coneOperator k 0)
  have hf : f = LinearMap.id -
      (zeroChainSum K k).smulRight (Finsupp.single hK.apexFace 1) := by
    apply Finsupp.lhom_ext
    intro s a
    change boundary K k 0 (hK.coneOperator k 0 (Finsupp.single s a)) =
      Finsupp.single s a -
        (zeroChainSum K k (Finsupp.single s a)) • Finsupp.single hK.apexFace 1
    by_cases hs : v ∈ s.1
    · have hseq : s = hK.apexFace := by
        apply Subtype.ext
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp s.2.2
        have hwv : w = v := by
          have : v ∈ ({w} : Finset V) := by simpa [← hw] using hs
          have hvw : v = w := by simpa using this
          exact hvw.symm
        change s.1 = ({v} : Finset V)
        rw [hw, hwv]
      rw [hK.coneOperator_single_of_mem k s a hs, hseq]
      simp [zeroChainSum_single]
    · have hzero : deletedFace K 0 (hK.coneFace s hs) 0 = s :=
        deletedFace_coneFace_zero hK s hs
      have hsucc : deletedFace K 0 (hK.coneFace s hs) (Fin.succ 0) = hK.apexFace :=
        deletedFace_coneFace_succ_zero hK s hs
      rw [hK.coneOperator_single_of_notMem k s a hs, boundary_single,
        Fin.sum_univ_succ, hzero, Fin.sum_univ_succ, hsucc]
      simp [f, zeroChainSum_single, sub_eq_add_neg]
  have h := LinearMap.congr_fun hf c
  simpa [f, LinearMap.sub_apply, LinearMap.smulRight_apply] using h

/-- An apex cone has zero ordinary simplicial homology in every positive degree. -/
theorem isZero_simplicialHomology_succ (hK : IsApexCone K v) (R : Type v) [Ring R]
    (n : ℕ) : IsZero (simplicialHomology K R (n + 1)) := by
  classical
  have htop : simplicialBoundaries K R (n + 1) = ⊤ := by
    apply top_unique
    intro z hz
    apply (mem_simplicialBoundaries_iff R K (n + 1) z).2
    have hz' : boundary K R n (z : Chain K R (n + 1)) = 0 := by
      have h : (z : Chain K R (n + 1)) ∈ LinearMap.ker (boundary K R n) := by
        rw [← simplicialCycles_succ R K n]
        exact z.2
      exact h
    refine ⟨hK.coneOperator R (n + 1) (z : Chain K R (n + 1)), ?_⟩
    simpa [hz'] using hK.boundary_coneOperator_add R n (z : Chain K R (n + 1))
  letI : HasQuotient (simplicialCycles K R (n + 1))
      (Submodule R (simplicialCycles K R (n + 1))) :=
    Submodule.hasQuotient (R := R) (M := simplicialCycles K R (n + 1))
  letI : Subsingleton
      (simplicialCycles K R (n + 1) ⧸ simplicialBoundaries K R (n + 1)) := by
    exact (Submodule.Quotient.subsingleton_iff).mpr htop
  letI : Subsingleton
      (↑(ModuleCat.of R (LinearMap.ker
        ((simplicialChainComplex K R).sc (n + 1)).g.hom ⧸
        LinearMap.range ((simplicialChainComplex K R).sc (n + 1)).moduleCatToCycles))) := by
    change Subsingleton (simplicialCycles K R (n + 1) ⧸ simplicialBoundaries K R (n + 1))
    infer_instance
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (homologyKernelQuotient.{v,u,v} R (simplicialChainComplex K R) (n + 1))

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero homology of an apex cone has rank one over a field. -/
theorem finrank_simplicialHomology_zero (hK : IsApexCone K v) (k : Type v) [Field k] :
    Module.finrank k (simplicialHomology K k 0) = 1 := by
  classical
  letI : HasQuotient (simplicialCycles K k 0)
      (Submodule k (simplicialCycles K k 0)) :=
    Submodule.hasQuotient (R := k) (M := simplicialCycles K k 0)
  let f : simplicialCycles K k 0 →ₗ[k] k :=
    (zeroChainSum K k).comp (simplicialCycles K k 0).subtype
  have hf : Function.Surjective f := by
    intro a
    refine ⟨⟨Finsupp.single hK.apexFace a, ?_⟩, ?_⟩
    · rw [simplicialCycles_zero]
      trivial
    · simp [f, zeroChainSum_single]
  have hle : simplicialBoundaries K k 0 ≤ LinearMap.ker f := by
    intro z hz
    change zeroChainSum K k (z : Chain K k 0) = 0
    obtain ⟨c, hc⟩ := (mem_simplicialBoundaries_iff k K 0 z).mp hz
    rw [← hc]
    have h := congrArg (fun g : Chain K k 1 →ₗ[k] k => g c)
      (zeroChainSum_boundary K k)
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have hge : LinearMap.ker f ≤ simplicialBoundaries K k 0 := by
    intro z hz
    apply (mem_simplicialBoundaries_iff k K 0 z).2
    have hsum : zeroChainSum K k (z : Chain K k 0) = 0 := by
      simpa [f] using hz
    refine ⟨hK.coneOperator k 0 (z : Chain K k 0), ?_⟩
    simpa [hsum] using hK.boundary_coneOperator_zero k (z : Chain K k 0)
  have hker : LinearMap.ker f = simplicialBoundaries K k 0 :=
    le_antisymm hge hle
  have he := (LinearMap.quotKerEquivOfSurjective (R := k) (M := simplicialCycles K k 0)
    (M₂ := k) f hf).finrank_eq
  rw [hker] at he
  have hhom := (homologyKernelQuotient.{v,u,v} k
    (simplicialChainComplex K k) 0).toLinearEquiv.finrank_eq
  change Module.finrank k (simplicialHomology K k 0) =
    Module.finrank k (simplicialCycles K k 0 ⧸ simplicialBoundaries K k 0) at hhom
  calc
    Module.finrank k (simplicialHomology K k 0) =
        Module.finrank k (simplicialCycles K k 0 ⧸ simplicialBoundaries K k 0) := hhom
    _ = Module.finrank k k := he
    _ = 1 := Module.finrank_self k

end IsApexCone

/-- The full complex has zero positive-degree simplicial homology. -/
theorem isZero_simplicialHomology_top_succ [Finite V] (R : Type v) [Ring R] (n : ℕ) :
    IsZero (simplicialHomology (⊤ : PreAbstractSimplicialComplex V) R (n + 1)) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · letI := hV
    letI : IsEmpty (Face (⊤ : PreAbstractSimplicialComplex V) (n + 1)) := by
      constructor
      intro s
      have hs : s.1.Nonempty := s.2.1
      rcases hs with ⟨w, hw⟩
      exact isEmptyElim w
    have hX : IsZero ((simplicialChainComplex (⊤ : PreAbstractSimplicialComplex V) R).X
        (n + 1)) := by
      rw [simplicialChainComplex_X]
      exact ModuleCat.isZero_of_subsingleton _
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ hX
  · letI := hV
    obtain ⟨v, hv⟩ := exists_isApexCone_top (V := V)
    exact hv.isZero_simplicialHomology_succ R n

/-- The full finite nonempty complex has degree-zero homology of rank one. -/
theorem finrank_simplicialHomology_top_zero [Finite V] [Nonempty V] (k : Type v) [Field k] :
    Module.finrank k
        (simplicialHomology (⊤ : PreAbstractSimplicialComplex V) k 0) = 1 := by
  obtain ⟨v, hv⟩ := exists_isApexCone_top (V := V)
  exact hv.finrank_simplicialHomology_zero k

end TDA.Simplicial
