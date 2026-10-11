import TDA.Persistence.GradeHomologyBarcode
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxHeartbeats 200000
universe u w
namespace TDA.Persistence.Examples
open TDA.Simplicial TDA.Filtration TDA.Persistence CategoryTheory

private def emptyFilter (V : Type u) (α : Type w) [LinearOrder α] :
    FilterFunction (⊥ : PreAbstractSimplicialComplex V) α where
  value := fun s => ((mem_bot_iff s.val).mp s.property).elim
  mono := by
    intro τ σ _
    exact ((mem_bot_iff τ.val).mp τ.property).elim

private instance emptyFaces (V : Type u) :
    Fintype (TotalFace (⊥ : PreAbstractSimplicialComplex V)) := by
  letI : IsEmpty (TotalFace (⊥ : PreAbstractSimplicialComplex V)) :=
    ⟨fun s => ((mem_bot_iff s.val).mp s.property).elim⟩
  exact Fintype.ofIsEmpty

private theorem empty_actual (V : Type u) [LinearOrder V] (α : Type w)
    [LinearOrder α] (k : Type u) [Field k] (n : ℕ) :
    (emptyFilter V α).criticalValues.card = 0 ∧
    gradeHomologyBarcode k (emptyFilter V α) n = 0 := by
  have hc : (emptyFilter V α).criticalValues.card = 0 := by
    rw [((emptyFilter V α).criticalValues_eq_empty_iff).2 rfl]
    rfl
  constructor
  · exact hc
  · have hi : IsEmpty (Fin (emptyFilter V α).criticalValues.card) := by
      rw [hc]
      infer_instance
    letI := hi
    simp [gradeHomologyBarcode, rankBarcode]

private instance singletonMem (s : Finset (Fin 2)) :
    Decidable (s ∈ singletonFace (0 : Fin 2)) :=
  decidable_of_iff (s = {0}) (mem_singletonFace_iff 0 s).symm

private instance singletonFaces : Fintype (TotalFace (singletonFace (0 : Fin 2))) :=
  inferInstance

private def singletonFilter : FilterFunction (singletonFace (0 : Fin 2)) ℤ where
  value := fun _ => 0
  mono := by intros; omega

private theorem singleton_values : singletonFilter.criticalValues.card = 1 := by decide

private def s0 : Fin singletonFilter.criticalValues.card :=
  ⟨0, by rw [singleton_values]; decide⟩

private theorem singleton_stage :
    singletonFilter.gradeFiltration s0 = singletonFace (0 : Fin 2) := by
  have hv : singletonFilter.criticalValue s0 = 0 := by
    have h := singletonFilter.criticalValue_mem s0
    have hs : singletonFilter.criticalValues = {0} := by decide
    simpa [hs] using h
  rw [singletonFilter.gradeFiltration_apply, hv]
  apply singletonFilter.sublevel_eq_self_of_forall_le
  intro s
  simp [singletonFilter]

private theorem singleton_H0 (k : Type) [Field k] :
    Module.finrank k ((simplicialHomologyPModule k singletonFilter.gradeFiltration 0).obj s0) = 1 := by
  rw [simplicialHomologyPModule_obj, singleton_stage]
  exact (simplicialSingletonH0Equiv k (0 : Fin 2)).finrank_eq.trans (Module.finrank_self k)

private theorem singleton_H1 (k : Type) [Field k] :
    Module.finrank k ((simplicialHomologyPModule k singletonFilter.gradeFiltration 1).obj s0) = 0 := by
  rw [simplicialHomologyPModule_obj, singleton_stage]
  have hc : Subsingleton (Chain (singletonFace (0 : Fin 2)) k 1) :=
    ⟨fun a b => (singletonHigherChain_eq_zero (0 : Fin 2) k 0 a).trans
      (singletonHigherChain_eq_zero (0 : Fin 2) k 0 b).symm⟩
  letI : Subsingleton (Chain (singletonFace (0 : Fin 2)) k 1) := hc
  letI : Subsingleton (simplicialCycles (singletonFace (0 : Fin 2)) k 1) :=
    inferInstance
  letI : HasQuotient (simplicialCycles (singletonFace (0 : Fin 2)) k 1)
      (Submodule k (simplicialCycles (singletonFace (0 : Fin 2)) k 1)) :=
    Submodule.hasQuotient (R := k)
      (M := simplicialCycles (singletonFace (0 : Fin 2)) k 1)
  letI : Subsingleton (simplicialCycles (singletonFace (0 : Fin 2)) k 1 ⧸
      simplicialBoundaries (singletonFace (0 : Fin 2)) k 1) := inferInstance
  letI : Subsingleton
      (↑(ModuleCat.of k (LinearMap.ker
        ((simplicialChainComplex (singletonFace (0 : Fin 2)) k).sc 1).g.hom ⧸
        LinearMap.range ((simplicialChainComplex
          (singletonFace (0 : Fin 2)) k).sc 1).moduleCatToCycles))) := by
    change Subsingleton (simplicialCycles (singletonFace (0 : Fin 2)) k 1 ⧸
      simplicialBoundaries (singletonFace (0 : Fin 2)) k 1)
    infer_instance
  have hz : Subsingleton (simplicialHomology (singletonFace (0 : Fin 2)) k 1) := by
    let e := (homologyKernelQuotient k
      (simplicialChainComplex (singletonFace (0 : Fin 2)) k) 1).toLinearEquiv
    exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
  letI := hz
  exact Module.finrank_zero_of_subsingleton (R := k)

private def singletonBar : FiniteInterval singletonFilter.criticalValues.card :=
  ⟨0, 1, by omega, by rw [singleton_values]⟩

private theorem singleton_barcode (k : Type) [Field k] :
    gradeHomologyBarcode k singletonFilter 0 =
      ({singletonBar} : Multiset (FiniteInterval singletonFilter.criticalValues.card)) := by
  calc
    gradeHomologyBarcode k singletonFilter 0 =
        rankBarcode (barcodeModule (k := k) ({singletonBar} :
          Multiset (FiniteInterval singletonFilter.criticalValues.card))) := by
      apply (rankBarcode_eq_iff
        (simplicialHomologyPModule k singletonFilter.gradeFiltration 0)
        (barcodeModule (k := k) ({singletonBar} :
          Multiset (FiniteInterval singletonFilter.criticalValues.card)))).mpr
      intro i j hij
      have hi : i = s0 := by
        apply Fin.ext
        have h := i.isLt
        change i.val = 0
        have hc := singleton_values
        omega
      have hj : j = s0 := by
        apply Fin.ext
        have h := j.isLt
        change j.val = 0
        have hc := singleton_values
        omega
      subst i
      subst j
      rw [rank_barcodeMap]
      have hr : structureMapRank
          (simplicialHomologyPModule k singletonFilter.gradeFiltration 0) s0 s0 hij = 1 := by
        unfold structureMapRank
        rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
        exact singleton_H0 k
      rw [hr]
      decide
    _ = _ := rankBarcode_barcodeModule _

private theorem singleton_barcode_H1 (k : Type) [Field k] :
    gradeHomologyBarcode k singletonFilter 1 = 0 := by
  calc
    gradeHomologyBarcode k singletonFilter 1 =
        rankBarcode (barcodeModule (k := k)
          (0 : Multiset (FiniteInterval singletonFilter.criticalValues.card))) := by
      apply (rankBarcode_eq_iff
        (simplicialHomologyPModule k singletonFilter.gradeFiltration 1)
        (barcodeModule (k := k)
          (0 : Multiset (FiniteInterval singletonFilter.criticalValues.card)))).mpr
      intro i j hij
      have hi : i = s0 := by
        apply Fin.ext
        have h := i.isLt
        change i.val = 0
        have hc := singleton_values
        omega
      have hj : j = s0 := by
        apply Fin.ext
        have h := j.isLt
        change j.val = 0
        have hc := singleton_values
        omega
      subst i
      subst j
      rw [rank_barcodeMap]
      have hr : structureMapRank
          (simplicialHomologyPModule k singletonFilter.gradeFiltration 1) s0 s0 hij = 0 := by
        unfold structureMapRank
        rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
        exact singleton_H1 k
      simpa using hr
    _ = _ := rankBarcode_barcodeModule _

private theorem singleton_Q :
    Module.finrank ℚ ((simplicialHomologyPModule ℚ singletonFilter.gradeFiltration 0).obj s0) = 1 ∧
    gradeHomologyBarcode ℚ singletonFilter 0 =
      ({singletonBar} : Multiset (FiniteInterval singletonFilter.criticalValues.card)) ∧
    Module.finrank ℚ ((simplicialHomologyPModule ℚ singletonFilter.gradeFiltration 1).obj s0) = 0 ∧
    gradeHomologyBarcode ℚ singletonFilter 1 = 0 :=
  ⟨singleton_H0 ℚ, singleton_barcode ℚ, singleton_H1 ℚ, singleton_barcode_H1 ℚ⟩

private theorem singleton_ZMod2 :
    Module.finrank (ZMod 2) ((simplicialHomologyPModule (ZMod 2)
      singletonFilter.gradeFiltration 0).obj s0) = 1 ∧
    gradeHomologyBarcode (ZMod 2) singletonFilter 0 =
      ({singletonBar} : Multiset (FiniteInterval singletonFilter.criticalValues.card)) ∧
    Module.finrank (ZMod 2) ((simplicialHomologyPModule (ZMod 2)
      singletonFilter.gradeFiltration 1).obj s0) = 0 ∧
    gradeHomologyBarcode (ZMod 2) singletonFilter 1 = 0 :=
  ⟨singleton_H0 (ZMod 2), singleton_barcode (ZMod 2), singleton_H1 (ZMod 2),
    singleton_barcode_H1 (ZMod 2)⟩

private abbrev twoVertices : PreAbstractSimplicialComplex (Fin 2) :=
  singletonFace (0 : Fin 2) ⊔ singletonFace (1 : Fin 2)

private instance twoMem (s : Finset (Fin 2)) : Decidable (s ∈ twoVertices) := by
  change Decidable (s = {0} ∨ s = {1})
  infer_instance

private instance twoFaces : Fintype (TotalFace twoVertices) := inferInstance

private def twoFilter : FilterFunction twoVertices ℤ where
  value := fun s => if s.1 = ({0} : Finset (Fin 2)) then 0 else 1
  mono := by
    intro τ σ hsub
    have he : τ.1 = σ.1 := by
      rcases (show τ.1 = ({0} : Finset (Fin 2)) ∨ τ.1 = {1}
        from τ.property) with hτ | hτ <;>
      rcases (show σ.1 = ({0} : Finset (Fin 2)) ∨ σ.1 = {1}
        from σ.property) with hσ | hσ <;>
      simp_all
    simp [he]

private theorem two_values : twoFilter.criticalValues = {0, 1} ∧
    twoFilter.criticalValues.card = 2 := by decide

private def t0 : Fin twoFilter.criticalValues.card :=
  ⟨0, by rw [two_values.2]; decide⟩
private def t1 : Fin twoFilter.criticalValues.card :=
  ⟨1, by rw [two_values.2]; decide⟩

private theorem two_critical :
    twoFilter.criticalValue t0 = 0 ∧ twoFilter.criticalValue t1 = 1 := by
  have h0 := twoFilter.criticalValue_mem t0
  have h1 := twoFilter.criticalValue_mem t1
  have hlt : twoFilter.criticalValue t0 < twoFilter.criticalValue t1 :=
    twoFilter.criticalValue.strictMono (by
      apply Fin.lt_def.mpr
      decide)
  simp only [two_values.1, Finset.mem_insert, Finset.mem_singleton] at h0 h1
  omega

private theorem two_critical0 : twoFilter.criticalValue t0 = 0 := two_critical.1
private theorem two_critical1 : twoFilter.criticalValue t1 = 1 := two_critical.2

private theorem two_stage0 :
    twoFilter.gradeFiltration t0 = singletonFace (0 : Fin 2) := by
  rw [twoFilter.gradeFiltration_apply, two_critical0]
  ext s
  constructor
  · intro hs
    obtain ⟨hsK, hv⟩ := (twoFilter.mem_sublevel_iff 0 s).mp hs
    have hmem : s = ({0} : Finset (Fin 2)) ∨ s = {1} := hsK
    rcases hmem with h | h
    · exact h
    · subst s
      simp [twoFilter] at hv
  · intro hs
    have h : s = ({0} : Finset (Fin 2)) := hs
    subst s
    exact (twoFilter.mem_sublevel_iff 0 _).mpr ⟨Or.inl rfl, by simp [twoFilter]⟩

private theorem two_stage1 : twoFilter.gradeFiltration t1 = twoVertices := by
  rw [twoFilter.gradeFiltration_apply, two_critical1]
  apply twoFilter.sublevel_eq_self_of_forall_le
  intro s
  by_cases h : s.val = ({0} : Finset (Fin 2)) <;> simp [twoFilter, h]

private instance noEdges : IsEmpty (Face twoVertices 1) :=
  ⟨fun s => by
    have hs : s.1 = ({0} : Finset (Fin 2)) ∨ s.1 = {1} := s.2.1
    have hc := s.2.2
    rcases hs with h | h <;> simp [h] at hc⟩

private instance twoFace0Fintype : Fintype (Face twoVertices 0) := inferInstance

private theorem two_face0_card : Fintype.card (Face twoVertices 0) = 2 := by decide

private theorem two_short_f_zero (k : Type) [Field k] :
    ((simplicialChainComplex twoVertices k).sc 0).f = 0 := by
  have hf : (simplicialChainComplex twoVertices k).d 1 0 = 0 := by
    apply ModuleCat.hom_ext
    ext c
    change (boundary twoVertices k 0) c = 0
    have hc : c = 0 := by
      change Chain twoVertices k 1 at c
      exact Subsingleton.elim c 0
    rw [hc]
    exact map_zero _
  change (simplicialChainComplex twoVertices k).d
    ((ComplexShape.down ℕ).prev 0) 0 = 0
  rw [ChainComplex.prev]
  exact hf

private theorem two_short_g_zero (k : Type) [Field k] :
    ((simplicialChainComplex twoVertices k).sc 0).g = 0 := by
  change (simplicialChainComplex twoVertices k).d
    0 ((ComplexShape.down ℕ).next 0) = 0
  rw [ChainComplex.next_nat_zero]
  exact simplicialChainComplex_d_zero twoVertices k 0

private noncomputable def twoH0Equiv (k : Type) [Field k] :
    simplicialHomology twoVertices k 0 ≃ₗ[k] Chain twoVertices k 0 :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((simplicialChainComplex twoVertices k).sc 0)
    (two_short_f_zero k) (two_short_g_zero k)).homologyIso.toLinearEquiv

private theorem two_H0_stage0 (k : Type) [Field k] :
    Module.finrank k ((simplicialHomologyPModule k twoFilter.gradeFiltration 0).obj t0) = 1 := by
  rw [simplicialHomologyPModule_obj, two_stage0]
  exact (simplicialSingletonH0Equiv k (0 : Fin 2)).finrank_eq.trans (Module.finrank_self k)

private theorem two_H0_stage1 (k : Type) [Field k] :
    Module.finrank k ((simplicialHomologyPModule k twoFilter.gradeFiltration 0).obj t1) = 2 := by
  rw [simplicialHomologyPModule_obj, two_stage1]
  rw [(twoH0Equiv k).finrank_eq]
  change Module.finrank k (Chain twoVertices k 0) = 2
  rw [Module.finrank_finsupp_self]
  exact two_face0_card

private theorem two_boundaries_zero (k : Type) [Field k] :
    simplicialBoundaries twoVertices k 0 = ⊥ := by
  let S := (simplicialChainComplex twoVertices k).sc 0
  have hm : S.moduleCatToCycles = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change S.f.hom x = 0
    rw [two_short_f_zero k]
    rfl
  change LinearMap.range S.moduleCatToCycles = ⊥
  rw [hm]
  exact LinearMap.range_zero

private theorem two_map_rank (k : Type) [Field k] :
    Module.finrank k (LinearMap.range
      (simplicialHomologyIncl k (show singletonFace (0 : Fin 2) ≤ twoVertices
        from le_sup_left) 0).hom) = 1 := by
  let h : singletonFace (0 : Fin 2) ≤ twoVertices := le_sup_left
  let z : simplicialCycles (singletonFace (0 : Fin 2)) k 0 :=
    ⟨Finsupp.single (singletonVertex (0 : Fin 2)) 1, by
      rw [simplicialCycles_zero]
      trivial⟩
  letI : HasQuotient (simplicialCycles (singletonFace (0 : Fin 2)) k 0)
      (Submodule k (simplicialCycles (singletonFace (0 : Fin 2)) k 0)) :=
    Submodule.hasQuotient (R := k)
      (M := simplicialCycles (singletonFace (0 : Fin 2)) k 0)
  letI : HasQuotient (simplicialCycles twoVertices k 0)
      (Submodule k (simplicialCycles twoVertices k 0)) :=
    Submodule.hasQuotient (R := k) (M := simplicialCycles twoVertices k 0)
  let q := (simplicialBoundaries (singletonFace (0 : Fin 2)) k 0).mkQ z
  have htarget : (simplicialBoundaries twoVertices k 0).mkQ
      (simplicialCycleIncl k h 0 z) ≠ 0 := by
    intro hz
    let P : Submodule k (simplicialCycles twoVertices k 0) :=
      simplicialBoundaries twoVertices k 0
    have hP : P = ⊥ := two_boundaries_zero k
    have hc : simplicialCycleIncl k h 0 z = 0 := by
      have hm : simplicialCycleIncl k h 0 z ∈ P := by
        simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hz
      rw [hP] at hm
      simpa using hm
    have hchain := congrArg (fun x : simplicialCycles twoVertices k 0 =>
      (x : Chain twoVertices k 0)) hc
    rw [simplicialCycleIncl_coe, chainIncl_single] at hchain
    simp [z] at hchain
  have hquot : simplicialQuotientIncl k h 0 q ≠ 0 := by
    rw [show simplicialQuotientIncl k h 0 q =
      (simplicialBoundaries twoVertices k 0).mkQ
        (simplicialCycleIncl k h 0 z) from simplicialQuotientIncl_mkQ k h 0 z]
    exact htarget
  let e0 := (homologyKernelQuotient.{0,0,0} k
    (simplicialChainComplex (singletonFace (0 : Fin 2)) k) 0).toLinearEquiv
  let e1 := (homologyKernelQuotient.{0,0,0} k
    (simplicialChainComplex twoVertices k) 0).toLinearEquiv
  let x := e0.symm q
  have hnat : e1 ((simplicialHomologyIncl k h 0).hom x) =
      simplicialQuotientIncl k h 0 q := by
    have hh := simplicialHomologyIncl_quotient_naturality k h 0
    have hx := congrArg (fun f : simplicialHomology (singletonFace (0 : Fin 2)) k 0 ⟶
      ModuleCat.of k (simplicialCycles twoVertices k 0 ⧸ simplicialBoundaries twoVertices k 0) =>
      f.hom x) hh
    change e1 ((simplicialHomologyIncl k h 0).hom x) =
      simplicialQuotientIncl k h 0 (e0 x) at hx
    exact hx.trans (by rw [show e0 x = q from e0.apply_symm_apply q])
  have himage : (simplicialHomologyIncl k h 0).hom x ≠ 0 := by
    intro hx
    apply hquot
    have hz := congrArg e1 hx
    exact hnat.symm.trans (hz.trans e1.map_zero)
  have hrpos : 0 < Module.finrank k
      (LinearMap.range (simplicialHomologyIncl k h 0).hom) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨(simplicialHomologyIncl k h 0).hom x, ⟨x, rfl⟩⟩, ?_⟩
    exact fun hy => himage (congrArg Subtype.val hy)
  have hrle := LinearMap.finrank_range_le (simplicialHomologyIncl k h 0).hom
  have hd : Module.finrank k (simplicialHomology (singletonFace (0 : Fin 2)) k 0) = 1 :=
    (simplicialSingletonH0Equiv k (0 : Fin 2)).finrank_eq.trans (Module.finrank_self k)
  rw [hd] at hrle
  omega

private def twoBar02 : FiniteInterval twoFilter.criticalValues.card :=
  ⟨0, 2, by omega, by rw [two_values.2]⟩

private def twoBar12 : FiniteInterval twoFilter.criticalValues.card :=
  ⟨1, 2, by omega, by rw [two_values.2]⟩

private theorem incl_rank_congr (k : Type) [Field k]
    {A B A' B' : PreAbstractSimplicialComplex (Fin 2)}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') :
    Module.finrank k (LinearMap.range (simplicialHomologyIncl k h 0).hom) =
      Module.finrank k (LinearMap.range (simplicialHomologyIncl k h' 0).hom) := by
  cases hA
  cases hB
  rfl

private theorem two_barcode (k : Type) [Field k] :
    gradeHomologyBarcode k twoFilter 0 =
      ({twoBar02, twoBar12} : Multiset (FiniteInterval twoFilter.criticalValues.card)) := by
  calc
    gradeHomologyBarcode k twoFilter 0 =
        rankBarcode (barcodeModule (k := k) ({twoBar02, twoBar12} :
          Multiset (FiniteInterval twoFilter.criticalValues.card))) := by
      apply (rankBarcode_eq_iff
        (simplicialHomologyPModule k twoFilter.gradeFiltration 0)
        (barcodeModule (k := k) ({twoBar02, twoBar12} :
          Multiset (FiniteInterval twoFilter.criticalValues.card)))).mpr
      intro i j hij
      have hi : i = t0 ∨ i = t1 := by
        have hb := i.isLt
        have hcard := two_values.2
        rcases (show i.val = 0 ∨ i.val = 1 by omega) with h | h
        · left; apply Fin.ext; exact h
        · right; apply Fin.ext; exact h
      have hj : j = t0 ∨ j = t1 := by
        have hb := j.isLt
        have hcard := two_values.2
        rcases (show j.val = 0 ∨ j.val = 1 by omega) with h | h
        · left; apply Fin.ext; exact h
        · right; apply Fin.ext; exact h
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · rw [rank_barcodeMap]
        have hr : structureMapRank
            (simplicialHomologyPModule k twoFilter.gradeFiltration 0) t0 t0 hij = 1 := by
          unfold structureMapRank
          rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
          exact two_H0_stage0 k
        rw [hr]
        decide
      · rw [rank_barcodeMap]
        have hr : structureMapRank
            (simplicialHomologyPModule k twoFilter.gradeFiltration 0) t0 t1 hij = 1 := by
          change Module.finrank k (LinearMap.range
            (simplicialHomologyIncl k (twoFilter.gradeFiltration.monotone hij) 0).hom) = 1
          exact (incl_rank_congr k two_stage0 two_stage1 _ _).trans (two_map_rank k)
        rw [hr]
        decide
      · have h : ¬ t1 ≤ t0 := by
          intro hh
          have := Fin.le_def.mp hh
          change (1 : ℕ) ≤ 0 at this
          omega
        exact (h hij).elim
      · rw [rank_barcodeMap]
        have hr : structureMapRank
            (simplicialHomologyPModule k twoFilter.gradeFiltration 0) t1 t1 hij = 2 := by
          unfold structureMapRank
          rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
          exact two_H0_stage1 k
        rw [hr]
        decide
    _ = _ := rankBarcode_barcodeModule _

private theorem two_Q :
    Module.finrank ℚ ((simplicialHomologyPModule ℚ twoFilter.gradeFiltration 0).obj t0) = 1 ∧
    Module.finrank ℚ ((simplicialHomologyPModule ℚ twoFilter.gradeFiltration 0).obj t1) = 2 ∧
    Module.finrank ℚ (LinearMap.range
      (simplicialHomologyIncl ℚ (show singletonFace (0 : Fin 2) ≤ twoVertices
        from le_sup_left) 0).hom) = 1 ∧
    gradeHomologyBarcode ℚ twoFilter 0 =
      ({twoBar02, twoBar12} : Multiset (FiniteInterval twoFilter.criticalValues.card)) :=
  ⟨two_H0_stage0 ℚ, two_H0_stage1 ℚ, two_map_rank ℚ, two_barcode ℚ⟩

private theorem two_ZMod2 :
    Module.finrank (ZMod 2) ((simplicialHomologyPModule (ZMod 2)
      twoFilter.gradeFiltration 0).obj t0) = 1 ∧
    Module.finrank (ZMod 2) ((simplicialHomologyPModule (ZMod 2)
      twoFilter.gradeFiltration 0).obj t1) = 2 ∧
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) (show singletonFace (0 : Fin 2) ≤ twoVertices
        from le_sup_left) 0).hom) = 1 ∧
    gradeHomologyBarcode (ZMod 2) twoFilter 0 =
      ({twoBar02, twoBar12} : Multiset (FiniteInterval twoFilter.criticalValues.card)) :=
  ⟨two_H0_stage0 (ZMod 2), two_H0_stage1 (ZMod 2), two_map_rank (ZMod 2),
    two_barcode (ZMod 2)⟩

end TDA.Persistence.Examples
