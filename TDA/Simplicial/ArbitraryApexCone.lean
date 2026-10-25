import TDA.Simplicial.Cone
import TDA.Simplicial.VertexChainMap

/-!
# Signed cone operators with an arbitrary apex

The cone is formed by inserting the chosen apex into each oriented vertex
 tuple.  `orientedTuple` transports the insertion sign to the ambient ordering.
-/

universe u v

namespace TDA.Simplicial

open Module
open scoped BigOperators

variable {V : Type u} [LinearOrder V]
variable {K : PreAbstractSimplicialComplex V}

/-- The chosen apex is a face and can be inserted into every face of the
complex. Bundling the closure data keeps applications atomic. -/
structure ApexInsertionClosed (K : PreAbstractSimplicialComplex V) (apex : V) : Prop where
  apex_mem : ({apex} : Finset V) ∈ K
  insert_mem : ∀ s ∈ K, insert apex s ∈ K

/-- A coefficient ring does not need a field structure for the vertex sum. -/
noncomputable def zeroChainCoefficientSum (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] : Chain K R 0 →ₗ[R] R :=
  Finsupp.linearCombination R (fun _ : Face K 0 => (1 : R))

@[simp]
theorem zeroChainCoefficientSum_single (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] (s : Face K 0) (a : R) :
    zeroChainCoefficientSum K R (Finsupp.single s a) = a := by
  simp [zeroChainCoefficientSum]

/-- The sum of the vertex coefficients is unchanged by a simplicial vertex map. -/
theorem zeroChainCoefficientSum_vertexChainMap
    {W : Type u} [LinearOrder W] {L : PreAbstractSimplicialComplex W}
    (R : Type v) [Ring R] (f : VertexMap K L) :
    (zeroChainCoefficientSum L R).comp (vertexChainMap R f 0) =
      zeroChainCoefficientSum K R := by
  apply Finsupp.lhom_ext
  intro s a
  change zeroChainCoefficientSum L R
      (vertexChainMap R f 0 (Finsupp.single s a)) =
    zeroChainCoefficientSum K R (Finsupp.single s a)
  rw [vertexChainMap_vertex]
  simp

private theorem fin_cons_image_eq {n : ℕ} (apex : V) (x : Fin (n + 1) → V) :
    Finset.univ.image (Fin.cons apex x) =
      insert apex (Finset.univ.image x) := by
  classical
  ext w
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · exact Or.inr ⟨j, rfl⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨Fin.succ j, by simp⟩

private theorem succ_cons_succAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (Fin.succ i).succAbove (Fin.succ j) = Fin.succ (i.succAbove j) := by
  by_cases hji : j.succ ≤ i
  · rw [Fin.succAbove_succ_of_le i (j.succ) hji,
      Fin.succAbove_of_succ_le i j hji]
    apply Fin.ext
    rfl
  · have hij : i ≤ j.castSucc := by
      rcases Fin.succ_le_or_le_castSucc i j with h | h
      · exact False.elim (hji h)
      · exact h
    have hlt : i < j.succ := lt_of_le_of_lt hij Fin.castSucc_lt_succ
    rw [Fin.succAbove_succ_of_lt i (j.succ) hlt,
      Fin.succAbove_of_le_castSucc i j hij]

private theorem fin_cons_comp_succ_succAbove {n : ℕ} (apex : V)
    (x : Fin (n + 1) → V) (i : Fin (n + 1)) :
    Fin.cons apex x ∘ (Fin.succ i).succAbove =
      Fin.cons apex (x ∘ i.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp only [Fin.cons_succ, Function.comp_apply, succ_cons_succAbove]

private theorem tupleBoundarySum_cons {n : ℕ} (R : Type v) [Ring R]
    (apex : V) (x : Fin (n + 1) → V) :
    tupleBoundarySum K R (Fin.cons apex x) =
      orientedTuple K R x -
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
          orientedTuple K R (Fin.cons apex (x ∘ i.succAbove)) := by
  classical
  unfold tupleBoundarySum
  rw [Fin.sum_univ_succ]
  simp_rw [Fin.succAbove_zero]
  have hhead : Fin.cons apex x ∘ Fin.succ = x := by
    funext i
    rfl
  rw [hhead]
  simp_rw [fin_cons_comp_succ_succAbove]
  have hsign (i : Fin (n + 1)) :
      (-1 : ℤ) ^ (i.succ : ℕ) = -((-1 : ℤ) ^ (i : ℕ)) := by
    simp [pow_succ]
  simp_rw [hsign]
  simp only [Fin.val_zero, pow_zero, one_smul, neg_smul]
  rw [Finset.sum_neg_distrib]
  abel

private def apexConsTuple (apex : V) {n : ℕ} (s : Face K n) : Fin (n + 2) → V :=
  Fin.cons apex (s.1.orderEmbOfFin s.2.2)

private theorem apexConsTuple_mem (apex : V)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K) {n : ℕ} (s : Face K n) :
    Finset.univ.image (apexConsTuple apex s) ∈ K := by
  rw [apexConsTuple, fin_cons_image_eq]
  simpa only [Finset.image_orderEmbOfFin_univ] using hinsert s.1 s.2.1

/-- Insert the chosen apex into the oriented tuple of each face.  The tuple
orientation automatically accounts for its position in the ambient order. -/
noncomputable def arbitraryApexConeOperator (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] (apex : V)
    (_hapex : ({apex} : Finset V) ∈ K)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K) (n : ℕ) :
    Chain K R n →ₗ[R] Chain K R (n + 1) :=
  Finsupp.linearCombination R
    (fun s : Face K n => orientedTuple K R (apexConsTuple apex s))

@[simp]
theorem arbitraryApexConeOperator_single (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] (apex : V) (hapex : ({apex} : Finset V) ∈ K)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K) (n : ℕ)
    (s : Face K n) (a : R) :
    arbitraryApexConeOperator K R apex hapex hinsert n (Finsupp.single s a) =
      a • orientedTuple K R (apexConsTuple apex s) := by
  simp [arbitraryApexConeOperator]

/-- The chain-valued arbitrary-apex filler. `orientedTuple` is allowed to
vanish when a tuple does not lie in the carrier, so constructing the chain
does not require a carrier-closure proof. -/
noncomputable def arbitraryApexConeFill (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] (apex : V) (n : ℕ) (c : Chain K R n) :
    Chain K R (n + 1) :=
  c.sum (fun s a => a • orientedTuple K R (apexConsTuple apex s))

/-- If the apex insertion stays in the complex, the chain-valued filler is the
linear arbitrary-apex cone operator. -/
theorem arbitraryApexConeFill_eq_operator (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] (apex : V)
    (hapex : ({apex} : Finset V) ∈ K)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K) (n : ℕ) (c : Chain K R n) :
    arbitraryApexConeFill K R apex n c =
      arbitraryApexConeOperator K R apex hapex hinsert n c := by
  classical
  simp [arbitraryApexConeFill, arbitraryApexConeOperator, apexConsTuple,
    Finsupp.linearCombination_apply]

@[simp]
theorem arbitraryApexConeFill_zero (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] (apex : V) (n : ℕ) :
    arbitraryApexConeFill K R apex n (0 : Chain K R n) = 0 := by
  simp [arbitraryApexConeFill]

private theorem intSign_smul (R : Type v) [Ring R] {n : ℕ}
    (c : Chain K R n) (i : ℕ) :
    (-1 : ℤ) ^ i • c = (-1 : R) ^ i • c := by
  rw [← Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ i) c]
  simp

private theorem arbitraryApexCone_basis_add
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R]
    (apex : V) (hapex : ({apex} : Finset V) ∈ K)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K) (n : ℕ)
    (s : Face K (n + 1)) :
    boundary K R (n + 1)
        (arbitraryApexConeOperator K R apex hapex hinsert (n + 1)
          (Finsupp.single s (1 : R))) +
      arbitraryApexConeOperator K R apex hapex hinsert n
        (boundary K R n (Finsupp.single s (1 : R))) =
      Finsupp.single s (1 : R) := by
  classical
  let x := s.1.orderEmbOfFin s.2.2
  have himage : Finset.univ.image (apexConsTuple apex s) ∈ K :=
    apexConsTuple_mem apex hinsert s
  have hfirst : orientedTuple K R x = Finsupp.single s (1 : R) :=
    orientedTuple_face K R s
  have hdelEnum (i : Fin (n + 2)) :
      (deletedFace K n s i).1.orderEmbOfFin (deletedFace K n s i).2.2 =
        x ∘ i.succAbove := by
    funext j
    exact enumerationAfterDeletion K n s i (deletedFace K n s i).2.2 j
  have hdelTuple (i : Fin (n + 2)) :
      apexConsTuple apex (deletedFace K n s i) =
        (Fin.cons (n := n + 1) (α := fun _ : Fin (n + 2) => V)
          apex (x ∘ i.succAbove) : Fin (n + 2) → V) := by
    unfold apexConsTuple
    change Fin.cons (n := n + 1) apex
        (fun j : Fin (n + 1) =>
          (deletedFace K n s i).1.orderEmbOfFin (deletedFace K n s i).2.2 j) =
      (Fin.cons (n := n + 1) (α := fun _ : Fin (n + 2) => V)
        apex (x ∘ i.succAbove) : Fin (n + 2) → V)
    exact congrArg
      (fun y : Fin (n + 1) → V =>
        (Fin.cons (n := n + 1) (α := fun _ : Fin (n + 2) => V)
          apex y : Fin (n + 2) → V)) (hdelEnum i)
  have hmap :
      arbitraryApexConeOperator K R apex hapex hinsert n
        (boundary K R n (Finsupp.single s (1 : R))) =
      ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) •
        orientedTuple K R (Fin.cons apex (x ∘ i.succAbove)) := by
    rw [boundary_single, one_smul, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [arbitraryApexConeOperator_single, hdelTuple]
  have hsigns :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        orientedTuple K R (Fin.cons apex (x ∘ i.succAbove))) =
      ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) •
        orientedTuple K R (Fin.cons apex (x ∘ i.succAbove)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact intSign_smul R _ i
  have hboundary :
      boundary K R (n + 1)
        (orientedTuple K R (apexConsTuple apex s)) =
      Finsupp.single s (1 : R) -
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          orientedTuple K R (Fin.cons apex (x ∘ i.succAbove)) := by
    change boundary K R (n + 1)
      (orientedTuple K R (Fin.cons apex x)) = _
    rw [boundary_orientedTuple K R (Fin.cons apex x) himage,
      tupleBoundarySum_cons, hfirst]
  simp only [arbitraryApexConeOperator_single, one_smul]
  rw [hboundary, hmap, hsigns]
  abel

/-- The signed arbitrary-apex cone is a chain contraction in positive degree. -/
theorem boundary_arbitraryApexConeOperator_add
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (apex : V)
    (hapex : ({apex} : Finset V) ∈ K)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K) (n : ℕ)
    (c : Chain K R (n + 1)) :
    boundary K R (n + 1)
        (arbitraryApexConeOperator K R apex hapex hinsert (n + 1) c) +
      arbitraryApexConeOperator K R apex hapex hinsert n
        (boundary K R n c) = c := by
  classical
  let f : Chain K R (n + 1) →ₗ[R] Chain K R (n + 1) :=
    (boundary K R (n + 1)).comp
        (arbitraryApexConeOperator K R apex hapex hinsert (n + 1)) +
      (arbitraryApexConeOperator K R apex hapex hinsert n).comp
        (boundary K R n)
  have hf : f = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s a
    change boundary K R (n + 1)
        (arbitraryApexConeOperator K R apex hapex hinsert (n + 1)
          (Finsupp.single s a)) +
      arbitraryApexConeOperator K R apex hapex hinsert n
        (boundary K R n (Finsupp.single s a)) = Finsupp.single s a
    have hboundary_single : boundary K R n (Finsupp.single s a) =
        a • boundary K R n (Finsupp.single s (1 : R)) := by
      rw [boundary_single, boundary_single]
      simp
    rw [arbitraryApexConeOperator_single, map_smul, hboundary_single,
      map_smul, ← smul_add]
    have hunit :
        boundary K R (n + 1)
            (arbitraryApexConeOperator K R apex hapex hinsert (n + 1)
              (Finsupp.single s (1 : R))) +
          arbitraryApexConeOperator K R apex hapex hinsert n
            (boundary K R n (Finsupp.single s (1 : R))) =
          Finsupp.single s (1 : R) :=
      arbitraryApexCone_basis_add K R apex hapex hinsert n s
    have hunit' :
        boundary K R (n + 1)
            (orientedTuple K R (apexConsTuple apex s)) +
          arbitraryApexConeOperator K R apex hapex hinsert n
            (boundary K R n (Finsupp.single s (1 : R))) =
          Finsupp.single s (1 : R) := by
      simpa only [arbitraryApexConeOperator_single, one_smul] using hunit
    rw [hunit']
    simp
  exact LinearMap.congr_fun hf c

/-- The chain-valued arbitrary-apex filler is a contraction in positive
degree whenever the apex can be inserted into every face. -/
theorem boundary_arbitraryApexConeFill_add
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (apex : V)
    (hapex : ({apex} : Finset V) ∈ K)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K) (n : ℕ)
    (c : Chain K R (n + 1)) :
    boundary K R (n + 1) (arbitraryApexConeFill K R apex (n + 1) c) +
      arbitraryApexConeFill K R apex n (boundary K R n c) = c := by
  rw [arbitraryApexConeFill_eq_operator K R apex hapex hinsert (n + 1) c,
    arbitraryApexConeFill_eq_operator K R apex hapex hinsert n
      (boundary K R n c)]
  exact boundary_arbitraryApexConeOperator_add K R apex hapex hinsert n c

/-- Contraction theorem using bundled apex-closure data. -/
theorem boundary_arbitraryApexConeFill_add_of_closed
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (apex : V)
    (hclosed : ApexInsertionClosed K apex) (n : ℕ)
    (c : Chain K R (n + 1)) :
    boundary K R (n + 1) (arbitraryApexConeFill K R apex (n + 1) c) +
      arbitraryApexConeFill K R apex n (boundary K R n c) = c := by
  exact boundary_arbitraryApexConeFill_add K R apex hclosed.apex_mem
    hclosed.insert_mem n c

private noncomputable def apexFace (apex : V)
    (hapex : ({apex} : Finset V) ∈ K) : Face K 0 :=
  ⟨{apex}, hapex, by simp⟩

private theorem orientedTuple_apexFace (R : Type v) [Ring R] (apex : V)
    (hapex : ({apex} : Finset V) ∈ K) :
    orientedTuple K R (fun _ : Fin 1 => apex) =
      Finsupp.single (apexFace apex hapex) (1 : R) := by
  have hEnum : (apexFace apex hapex).1.orderEmbOfFin
      (apexFace apex hapex).2.2 = (fun _ : Fin 1 => apex) := by
    funext i
    have hi := Finset.orderEmbOfFin_mem (apexFace apex hapex).1
      (apexFace apex hapex).2.2 i
    exact Finset.mem_singleton.mp hi
  rw [← hEnum]
  exact orientedTuple_face K R (apexFace apex hapex)

private theorem tupleBoundarySum_cons_zero (R : Type v) [Ring R] (apex : V)
    (hapex : ({apex} : Finset V) ∈ K) (x : Fin 1 → V) :
    tupleBoundarySum K R (Fin.cons apex x) =
      orientedTuple K R x -
        Finsupp.single (apexFace apex hapex) (1 : R) := by
  rw [tupleBoundarySum_cons]
  have hsum :
      (∑ i : Fin 1, (-1 : ℤ) ^ (i : ℕ) •
        orientedTuple K R (Fin.cons apex (x ∘ i.succAbove))) =
      Finsupp.single (apexFace apex hapex) (1 : R) := by
    rw [Fin.sum_univ_succ]
    have htuple : Fin.cons apex (x ∘ (0 : Fin 1).succAbove) =
        (fun _ : Fin 1 => apex) := by
      funext i
      fin_cases i
      simp
    rw [htuple]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.sum_univ_zero, add_zero]
    exact orientedTuple_apexFace R apex hapex
  rw [hsum]

private theorem boundary_apexCone_basis_zero
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R]
    (apex : V) (hapex : ({apex} : Finset V) ∈ K)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K)
    (s : Face K 0) (a : R) :
    boundary K R 0
        (arbitraryApexConeOperator K R apex hapex hinsert 0
          (Finsupp.single s a)) =
      Finsupp.single s a - Finsupp.single (apexFace apex hapex) a := by
  classical
  let x := s.1.orderEmbOfFin s.2.2
  have himage : Finset.univ.image (apexConsTuple apex s) ∈ K :=
    apexConsTuple_mem apex hinsert s
  have hformula :
      boundary K R 0 (orientedTuple K R (apexConsTuple apex s)) =
        Finsupp.single s (1 : R) -
          Finsupp.single (apexFace apex hapex) (1 : R) := by
    change boundary K R 0 (orientedTuple K R (Fin.cons apex x)) = _
    rw [boundary_orientedTuple K R (Fin.cons apex x) himage,
      tupleBoundarySum_cons_zero R, orientedTuple_face K R s]
  rw [arbitraryApexConeOperator_single, map_smul, hformula]
  simp [smul_sub]

/-- In degree zero, the signed arbitrary-apex cone subtracts the total vertex
coefficient at the apex. -/
theorem boundary_arbitraryApexConeOperator_zero
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (apex : V)
    (hapex : ({apex} : Finset V) ∈ K)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K) (c : Chain K R 0) :
    boundary K R 0 (arbitraryApexConeOperator K R apex hapex hinsert 0 c) =
      c - Finsupp.single
        (⟨{apex}, hapex, by simp⟩ : Face K 0)
        (zeroChainCoefficientSum K R c) := by
  classical
  let f : Chain K R 0 →ₗ[R] Chain K R 0 :=
    (boundary K R 0).comp
      (arbitraryApexConeOperator K R apex hapex hinsert 0)
  have hf : f = LinearMap.id -
      (zeroChainCoefficientSum K R).smulRight
        (Finsupp.single (apexFace apex hapex) (1 : R)) := by
    apply Finsupp.lhom_ext
    intro s a
    change boundary K R 0
        (arbitraryApexConeOperator K R apex hapex hinsert 0
          (Finsupp.single s a)) =
      Finsupp.single s a -
        zeroChainCoefficientSum K R (Finsupp.single s a) •
          Finsupp.single (apexFace apex hapex) 1
    rw [boundary_apexCone_basis_zero, zeroChainCoefficientSum_single]
    simp [Finsupp.smul_single]
  have h := LinearMap.congr_fun hf c
  simpa [f, LinearMap.sub_apply, LinearMap.smulRight_apply, apexFace] using h

/-- The degree-zero filler subtracts the total coefficient at the apex. -/
theorem boundary_arbitraryApexConeFill_zero
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (apex : V)
    (hapex : ({apex} : Finset V) ∈ K)
    (hinsert : ∀ s ∈ K, insert apex s ∈ K) (c : Chain K R 0) :
    boundary K R 0 (arbitraryApexConeFill K R apex 0 c) =
      c - Finsupp.single
        (⟨{apex}, hapex, by simp⟩ : Face K 0)
        (zeroChainCoefficientSum K R c) := by
  rw [arbitraryApexConeFill_eq_operator K R apex hapex hinsert 0 c]
  exact boundary_arbitraryApexConeOperator_zero K R apex hapex hinsert c

/-- Degree-zero contraction theorem using bundled apex-closure data. -/
theorem boundary_arbitraryApexConeFill_zero_of_closed
    (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R] (apex : V)
    (hclosed : ApexInsertionClosed K apex) (c : Chain K R 0) :
    boundary K R 0 (arbitraryApexConeFill K R apex 0 c) =
      c - Finsupp.single
        (⟨{apex}, hclosed.apex_mem, by simp⟩ : Face K 0)
        (zeroChainCoefficientSum K R c) := by
  exact boundary_arbitraryApexConeFill_zero K R apex hclosed.apex_mem
    hclosed.insert_mem c

end TDA.Simplicial
