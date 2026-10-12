import TDA.Simplicial.Attachment

set_option autoImplicit false

/-! The coefficient sum on actual degree-zero chains is preserved by every
simplex inclusion and annihilates every actual edge boundary. -/

namespace TDA.Simplicial

open CategoryTheory Module

universe u v

variable {V : Type u} [LinearOrder V]
variable (K : PreAbstractSimplicialComplex V) (k : Type v) [Field k]

/-- Sum of the coefficients of actual vertices. -/
noncomputable def zeroChainSum : Chain K k 0 →ₗ[k] k :=
  Finsupp.lsum k (fun _ => LinearMap.id)

omit [LinearOrder V] in theorem zeroChainSum_single (σ : Face K 0) (a : k) :
    zeroChainSum K k (Finsupp.single σ a) = a := by
  exact Finsupp.lsum_single k (fun _ : Face K 0 => LinearMap.id) σ a

theorem zeroChainSum_boundary :
    (zeroChainSum K k).comp (boundary K k 0) = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  change zeroChainSum K k (boundary K k 0 (Finsupp.single σ a)) = 0
  rw [boundary_single]
  simp only [map_sum, map_smul, zeroChainSum_single]
  simp [Fin.sum_univ_succ]

omit [LinearOrder V] in theorem zeroChainSum_chainIncl {L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) :
    (zeroChainSum L k).comp (chainIncl k h 0) = zeroChainSum K k := by
  apply Finsupp.lhom_ext
  intro σ a
  change zeroChainSum L k (chainIncl k h 0 (Finsupp.single σ a)) =
    zeroChainSum K k (Finsupp.single σ a)
  rw [chainIncl_single, zeroChainSum_single, zeroChainSum_single]

/-- Sum only the coefficients of vertices selected by a predicate. -/
noncomputable def selectedZeroChainSum (P : Face K 0 → Prop) [DecidablePred P] :
    Chain K k 0 →ₗ[k] k :=
  Finsupp.lsum k (fun σ => if P σ then LinearMap.id else 0)

omit [LinearOrder V] in theorem selectedZeroChainSum_single
    (P : Face K 0 → Prop) [DecidablePred P] (σ : Face K 0) (a : k) :
    selectedZeroChainSum K k P (Finsupp.single σ a) =
      if P σ then a else 0 := by
  simp only [selectedZeroChainSum, Finsupp.lsum_single]
  by_cases h : P σ <;> simp [h]

theorem selectedZeroChainSum_boundary (P : Face K 0 → Prop) [DecidablePred P]
    (hP : ∀ σ : Face K 1,
      P (deletedFace K 0 σ 0) ↔ P (deletedFace K 0 σ 1)) :
    (selectedZeroChainSum K k P).comp (boundary K k 0) = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro σ a
  change selectedZeroChainSum K k P (boundary K k 0 (Finsupp.single σ a)) = 0
  rw [boundary_single]
  simp only [map_sum, map_smul, selectedZeroChainSum_single]
  by_cases hp : P (deletedFace K 0 σ 0)
  · have hp' := (hP σ).mp hp
    simp [Fin.sum_univ_succ, hp, hp']
  · have hp' := mt (hP σ).mpr hp
    simp [Fin.sum_univ_succ, hp, hp']

/-- The actual zero-cycle carried by one vertex. -/
noncomputable def zeroVertexCycle (σ : Face K 0) : simplicialCycles K k 0 :=
  ⟨Finsupp.single σ 1, by rw [simplicialCycles_zero]; trivial⟩

theorem zeroVertexCycle_not_boundary (σ : Face K 0) :
    zeroVertexCycle K k σ ∉ simplicialBoundaries K k 0 := by
  intro hz
  obtain ⟨d, hd⟩ := (mem_simplicialBoundaries_iff k K 0 _).mp hz
  have hb : zeroChainSum K k (boundary K k 0 d) = 0 := by
    have h := congrArg (fun f : Chain K k 1 →ₗ[k] k => f d)
      (zeroChainSum_boundary K k)
    simpa using h
  have hv : zeroChainSum K k (zeroVertexCycle K k σ : Chain K k 0) = 1 := by
    exact zeroChainSum_single K k σ 1
  rw [hd] at hb
  exact one_ne_zero (hv.symm.trans hb)

theorem vertexCombination_not_boundary_of_selected
    (P : Face K 0 → Prop) [DecidablePred P]
    (hP : ∀ σ : Face K 1,
      P (deletedFace K 0 σ 0) ↔ P (deletedFace K 0 σ 1))
    (u v : Face K 0) (hu : P u) (hv : ¬ P v) (a b : k)
    (hmem : a • zeroVertexCycle K k u + b • zeroVertexCycle K k v ∈
      simplicialBoundaries K k 0) : a = 0 ∧ b = 0 := by
  obtain ⟨d, hd⟩ := (mem_simplicialBoundaries_iff k K 0 _).mp hmem
  have hsel : selectedZeroChainSum K k P (boundary K k 0 d) = 0 := by
    have h := congrArg (fun f : Chain K k 1 →ₗ[k] k => f d)
      (selectedZeroChainSum_boundary K k P hP)
    simpa using h
  have hsum : zeroChainSum K k (boundary K k 0 d) = 0 := by
    have h := congrArg (fun f : Chain K k 1 →ₗ[k] k => f d)
      (zeroChainSum_boundary K k)
    simpa using h
  have hsel' : a = 0 := by
    rw [hd] at hsel
    simpa [map_add, map_smul, zeroVertexCycle,
      selectedZeroChainSum_single, hu, hv] using hsel
  have hsum' : a + b = 0 := by
    rw [hd] at hsum
    simpa [map_add, map_smul, zeroVertexCycle,
      zeroChainSum_single] using hsum
  exact ⟨hsel', by simpa [hsel'] using hsum'⟩

theorem zeroShortF_of_no_edges [IsEmpty (Face K 1)] :
    ((simplicialChainComplex K k).sc 0).f = 0 := by
  have hf : (simplicialChainComplex K k).d 1 0 = 0 := by
    apply ModuleCat.hom_ext
    ext c
    change (boundary K k 0) c = 0
    have hc : c = 0 := by
      apply Finsupp.ext
      intro σ
      exact isEmptyElim σ
    rw [hc]
    exact map_zero _
  change (simplicialChainComplex K k).d
    ((ComplexShape.down ℕ).prev 0) 0 = 0
  rw [ChainComplex.prev]
  exact hf

theorem zeroShortG : ((simplicialChainComplex K k).sc 0).g = 0 := by
  change (simplicialChainComplex K k).d
    0 ((ComplexShape.down ℕ).next 0) = 0
  rw [ChainComplex.next_nat_zero]
  exact simplicialChainComplex_d_zero K k 0

/-- In an actual complex without edges, H₀ is the free module on its vertices. -/
noncomputable def zeroHomologyEquivOfNoEdges [IsEmpty (Face K 1)] :
    simplicialHomology K k 0 ≃ₗ[k] Chain K k 0 :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((simplicialChainComplex K k).sc 0)
    (zeroShortF_of_no_edges K k) (zeroShortG K k)).homologyIso.toLinearEquiv

theorem finrank_zeroHomology_of_no_edges [IsEmpty (Face K 1)]
    [Fintype (Face K 0)] :
    Module.finrank k (simplicialHomology K k 0) = Fintype.card (Face K 0) := by
  rw [(zeroHomologyEquivOfNoEdges K k).finrank_eq]
  exact Module.finrank_finsupp_self k

set_option backward.isDefEq.respectTransparency false in
/-- The quotient presentation and actual homology inclusion have the same
range dimension. This uses their natural isomorphisms, not a rank model. -/
theorem finrank_homologyIncl_range_eq_quotientIncl_range
    {L : PreAbstractSimplicialComplex V} (h : K ≤ L) :
    Module.finrank k (LinearMap.range (simplicialHomologyIncl k h 0).hom) =
      Module.finrank k (LinearMap.range (simplicialQuotientIncl k h 0)) := by
  let eK := (homologyKernelQuotient.{v,u,v} k
    (simplicialChainComplex K k) 0).toLinearEquiv
  let eL := (homologyKernelQuotient.{v,u,v} k
    (simplicialChainComplex L k) 0).toLinearEquiv
  let f := (simplicialHomologyIncl k h 0).hom
  let q := simplicialQuotientIncl k h 0
  have hn (x : simplicialHomology K k 0) : eL (f x) = q (eK x) := by
    have hh := congrArg (fun z => z.hom x)
      (simplicialHomologyIncl_quotient_naturality k h 0)
    exact hh
  let g : LinearMap.range f →ₗ[k] LinearMap.range q := {
    toFun x := ⟨eL x.1, by
      obtain ⟨a, ha⟩ := x.2
      refine ⟨eK a, ?_⟩
      rw [← ha]
      exact (hn a).symm⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      change eL (x.1 + y.1) = eL x.1 + eL y.1
      exact eL.map_add x.1 y.1
    map_smul' := by
      intro c x
      apply Subtype.ext
      change eL (c • x.1) = c • eL x.1
      exact eL.map_smul c x.1
  }
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply eL.injective
      have hh := congrArg Subtype.val hxy
      change eL x.1 = eL y.1 at hh
      exact hh
    · intro y
      obtain ⟨b, hb⟩ := y.2
      obtain ⟨a, ha⟩ := eK.surjective b
      refine ⟨⟨f a, ⟨a, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      have he : eL (f a) = y.1 :=
        (hn a).trans ((congrArg q ha).trans hb)
      exact he
  exact (LinearEquiv.ofBijective g hg).finrank_eq

/-- A vertex cycle stays a vertex cycle under actual simplicial inclusion. -/
theorem zeroVertexCycle_incl {L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (σ : Face K 0) :
    simplicialCycleIncl k h 0 (zeroVertexCycle K k σ) =
      zeroVertexCycle L k (faceIncl h 0 σ) := by
  apply Subtype.ext
  change chainIncl k h 0 (Finsupp.single σ 1) =
    Finsupp.single (faceIncl h 0 σ) 1
  exact chainIncl_single k h 0 σ 1

theorem zeroVertexCycle_incl_not_boundary
    {L : PreAbstractSimplicialComplex V} (h : K ≤ L) (σ : Face K 0) :
    simplicialCycleIncl k h 0 (zeroVertexCycle K k σ) ∉
      simplicialBoundaries L k 0 := by
  rw [zeroVertexCycle_incl]
  exact zeroVertexCycle_not_boundary L k (faceIncl h 0 σ)

set_option backward.isDefEq.respectTransparency false in
/-- Every included actual vertex gives a nonzero element of the H₀ map range. -/
theorem finrank_homologyIncl_range_pos_of_vertex
    {L : PreAbstractSimplicialComplex V} [Finite (TotalFace L)]
    (h : K ≤ L) (σ : Face K 0) :
    0 < Module.finrank k
      (LinearMap.range (simplicialHomologyIncl k h 0).hom) := by
  let z := zeroVertexCycle K k σ
  let qz := Submodule.mkQ (R := k) (M := simplicialCycles K k 0)
    (simplicialBoundaries K k 0) z
  have hq : simplicialQuotientIncl k h 0 qz ≠ 0 := by
    rw [show simplicialQuotientIncl k h 0 qz =
      Submodule.mkQ (R := k) (M := simplicialCycles L k 0)
        (simplicialBoundaries L k 0) (simplicialCycleIncl k h 0 z) from
      simplicialQuotientIncl_mkQ k h 0 z]
    intro hz
    apply zeroVertexCycle_incl_not_boundary K k h σ
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hz
  let eK := (homologyKernelQuotient.{v,u,v} k
    (simplicialChainComplex K k) 0).toLinearEquiv
  let eL := (homologyKernelQuotient.{v,u,v} k
    (simplicialChainComplex L k) 0).toLinearEquiv
  let x := eK.symm qz
  have hn : eL ((simplicialHomologyIncl k h 0).hom x) =
      simplicialQuotientIncl k h 0 (eK x) := by
    exact congrArg (fun z => z.hom x)
      (simplicialHomologyIncl_quotient_naturality k h 0)
  have hne : (simplicialHomologyIncl k h 0).hom x ≠ 0 := by
    intro hz
    rw [hz, map_zero, show eK x = qz from eK.apply_symm_apply qz] at hn
    exact hq hn.symm
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨(simplicialHomologyIncl k h 0).hom x, ⟨x, rfl⟩⟩, ?_⟩
  intro hz
  exact hne (congrArg Subtype.val hz)

set_option backward.isDefEq.respectTransparency false in
/-- Two source vertices in distinct target edge components remain independent
under the actual degree-zero quotient inclusion. -/
theorem quotientIncl_injective_of_two_vertices_separated
    {L : PreAbstractSimplicialComplex V} (h : K ≤ L)
    (u v : Face K 0)
    (hdecomp : ∀ c : Chain K k 0,
      c = Finsupp.single u (c u) + Finsupp.single v (c v))
    (P : Face L 0 → Prop) [DecidablePred P]
    (hP : ∀ σ : Face L 1,
      P (deletedFace L 0 σ 0) ↔ P (deletedFace L 0 σ 1))
    (hu : P (faceIncl h 0 u)) (hv : ¬ P (faceIncl h 0 v)) :
    Function.Injective (simplicialQuotientIncl k h 0) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  induction x using Quotient.inductionOn' with
  | _ z =>
    let a : k := (z : Chain K k 0) u
    let b : k := (z : Chain K k 0) v
    have hz : z = a • zeroVertexCycle K k u + b • zeroVertexCycle K k v := by
      apply Subtype.ext
      change (z : Chain K k 0) =
        a • Finsupp.single u 1 + b • Finsupp.single v 1
      rw [hdecomp (z : Chain K k 0)]
      simp [a, b, Finsupp.smul_single]
    have htarget : simplicialCycleIncl k h 0 z ∈ simplicialBoundaries L k 0 := by
      have hx' := (LinearMap.mem_ker).mp hx
      change simplicialQuotientIncl k h 0
        (Submodule.mkQ (R := k) (M := simplicialCycles K k 0)
          (simplicialBoundaries K k 0) z) = 0 at hx'
      rw [simplicialQuotientIncl_mkQ, Submodule.mkQ_apply] at hx'
      simpa only [Submodule.Quotient.mk_eq_zero] using hx'
    rw [hz, map_add, map_smul, map_smul,
      zeroVertexCycle_incl, zeroVertexCycle_incl] at htarget
    obtain ⟨ha, hb⟩ := vertexCombination_not_boundary_of_selected L k P hP
      (faceIncl h 0 u) (faceIncl h 0 v) hu hv a b htarget
    change (simplicialBoundaries K k 0).mkQ z = 0
    rw [hz, ha, hb, zero_smul, zero_smul, add_zero]
    exact map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- An edge joining distinct old components kills a nonzero actual H₀ class. -/
theorem SimplexAttachment.attachingHomologyClass_ne_zero_of_separated_vertices
    {L : PreAbstractSimplicialComplex V}
    (A : SimplexAttachment K L 1)
    (P : Face K 0 → Prop) [DecidablePred P]
    (hP : ∀ σ : Face K 1,
      P (deletedFace K 0 σ 0) ↔ P (deletedFace K 0 σ 1))
    (h0 : P (A.oldDeletedFace 0)) (h1 : ¬ P (A.oldDeletedFace 1)) :
    A.attachingHomologyClass k ≠ 0 := by
  intro hz
  have hq : A.attachingQuotientClass k = 0 := by
    rw [← A.attachingHomologyClass_equiv k, hz, map_zero]
  obtain ⟨d, hd⟩ := (mem_simplicialBoundaries_iff k K 0 _).mp
    ((A.attachingClass_zero_iff_boundary k).mp hq)
  have hsum : selectedZeroChainSum K k P (boundary K k 0 d) = 0 := by
    have h := congrArg (fun f : Chain K k 1 →ₗ[k] k => f d)
      (selectedZeroChainSum_boundary K k P hP)
    simpa using h
  rw [hd] at hsum
  have hv : selectedZeroChainSum K k P (A.attachingBoundary k) = 1 := by
    simp [SimplexAttachment.attachingBoundary, Fin.sum_univ_succ,
      selectedZeroChainSum_single, h0, h1]
  exact one_ne_zero (hv.symm.trans hsum)

end TDA.Simplicial
