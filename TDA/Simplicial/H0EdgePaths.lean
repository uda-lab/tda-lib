import TDA.Simplicial.Homology

set_option autoImplicit false

/-!
# Degree-zero homology and replacement paths

In ordinary degree zero every chain is a cycle. When two complexes on the same labels
have the same vertex basis, replacing each edge of the larger complex by an edge path
in the smaller one preserves the boundary subspace. The resulting isomorphism on
homology is induced by the inclusion.
-/

namespace TDA.Simplicial

open CategoryTheory

universe u w

noncomputable section

variable {V : Type u} [LinearOrder V] (R : Type w) [Ring R]
variable {K L : PreAbstractSimplicialComplex V}

local instance h0CyclesHasQuotient (K : PreAbstractSimplicialComplex V) :
    HasQuotient (simplicialCycles K R 0) (Submodule R (simplicialCycles K R 0)) :=
  Submodule.hasQuotient (R := R) (M := simplicialCycles K R 0)

private def vFace (hK : ∀ v : V, ({v} : Finset V) ∈ K) (v : V) : Face K 0 :=
  ⟨{v}, hK v, Finset.card_singleton v⟩

private def vBasis (hK : ∀ v : V, ({v} : Finset V) ∈ K) (v : V) : Chain K R 0 :=
  Finsupp.single (vFace hK v) 1

private def edgeEnds (s : Face K 1) : Fin 2 → V := s.val.orderEmbOfFin s.property.2

private theorem face_eq_endpoints (s : Face K 1) :
    ({edgeEnds s 0, edgeEnds s 1} : Finset V) = s.val := by
  rw [← Finset.image_orderEmbOfFin_univ s.val s.property.2]
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem signed_boundary_edge (hK : ∀ v : V, ({v} : Finset V) ∈ K) (s : Face K 1) :
    boundary K R 0 (Finsupp.single s 1) =
      vBasis R hK (edgeEnds s 1) - vBasis R hK (edgeEnds s 0) := by
  have hne : edgeEnds s 0 ≠ edgeEnds s 1 :=
    (s.val.orderEmbOfFin s.property.2).injective.ne (by decide)
  have hd (i : Fin 2) : deletedFace K 0 s i = vFace hK (edgeEnds s (1 - i)) := by
    apply Subtype.ext
    change s.val.erase (edgeEnds s i) = {edgeEnds s (1 - i)}
    rw [← face_eq_endpoints s]
    fin_cases i
    · simp [hne]
    · simp [Finset.erase_insert_of_ne, hne]
  have d0 : deletedFace K 0 s 0 = vFace hK (edgeEnds s 1) := by
    simpa using hd 0
  have d1 : deletedFace K 0 s 1 = vFace hK (edgeEnds s 0) := by
    simpa using hd 1
  rw [boundary_single, Fin.sum_univ_two, d0, d1, sub_eq_add_neg]
  simp only [one_smul, Fin.val_zero, pow_zero, Fin.val_one, pow_one, vBasis, Finsupp.single_neg]

private theorem signed_boundary_ordered_pair (hK : ∀ v : V, ({v} : Finset V) ∈ K)
    {a b : V} (hab : a < b) (hm : ({a,b} : Finset V) ∈ K) :
    vBasis R hK b - vBasis R hK a ∈ LinearMap.range (boundary K R 0) := by
  let s : Face K 1 := ⟨{a,b}, hm, Finset.card_pair hab.ne⟩
  have e : edgeEnds s = ![a,b] := by
    symm
    apply Finset.orderEmbOfFin_unique
    · intro i
      fin_cases i <;> simp [s]
    · exact Fin.strictMono_iff_lt_succ.2 (fun i => by fin_cases i; simpa using hab)
  exact ⟨Finsupp.single s 1, by rw [signed_boundary_edge R hK s, e]; rfl⟩

private theorem signed_path_boundary (hK : ∀ v : V, ({v} : Finset V) ∈ K)
    {u v : V} (h : Relation.EqvGen (fun a b => ({a,b} : Finset V) ∈ K) u v) :
    vBasis R hK v - vBasis R hK u ∈ LinearMap.range (boundary K R 0) := by
  let B := LinearMap.range (boundary K R 0)
  change _ ∈ B
  induction h with
  | rel a b hab =>
    rcases lt_trichotomy a b with ab | rfl | ba
    · exact signed_boundary_ordered_pair R hK ab hab
    · rw [sub_self]
      exact B.zero_mem
    · have hba := signed_boundary_ordered_pair R hK ba (by rwa [Finset.pair_comm])
      simpa only [neg_sub] using B.neg_mem hba
  | refl a =>
    rw [sub_self]
    exact B.zero_mem
  | symm a b hab h =>
    simpa only [neg_sub] using B.neg_mem h
  | trans a b c hab hbc ha hb =>
    simpa only [sub_add_sub_cancel] using B.add_mem hb ha

omit [LinearOrder V] in
private theorem chainIncl_vertex (h : K ≤ L) (hK : ∀ v : V, ({v} : Finset V) ∈ K) (v : V) :
    chainIncl R h 0 (vBasis R hK v) = vBasis R (fun v => h (hK v)) v := by
  rw [vBasis, chainIncl_single]
  rfl

omit [LinearOrder V] in
private theorem chainIncl_zero_bijective (h : K ≤ L) (hK : ∀ v : V, ({v} : Finset V) ∈ K) :
    Function.Bijective (chainIncl R h 0) := by
  have hi : Function.Injective (faceIncl h 0) := by
    intro a b he
    exact Subtype.ext (congrArg (fun t : Face L 0 => t.val) he)
  have hs : Function.Surjective (faceIncl h 0) := by
    intro s
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp s.property.2
    exact ⟨vFace hK v, Subtype.ext hv.symm⟩
  exact ⟨Finsupp.mapDomain_injective hi, Finsupp.mapDomain_surjective hs⟩

private theorem transported_boundary_eq (h : K ≤ L) (hK : ∀ v : V, ({v} : Finset V) ∈ K)
    (paths : ∀ u v, ({u,v} : Finset V) ∈ L →
      Relation.EqvGen (fun a b => ({a,b} : Finset V) ∈ K) u v) :
    (LinearMap.range (boundary K R 0)).map (chainIncl R h 0) =
      LinearMap.range (boundary L R 0) := by
  let U := (LinearMap.range (boundary K R 0)).map (chainIncl R h 0)
  apply le_antisymm
  · rintro _ ⟨x, ⟨c, rfl⟩, rfl⟩
    exact ⟨chainIncl R h 1 c, DFunLike.congr_fun (boundary_chainIncl R h 0) c⟩
  · rintro _ ⟨c, rfl⟩
    have hp : U.mkQ.comp (boundary L R 0) = 0 := by
      apply Finsupp.lhom_ext
      intro e a
      change U.mkQ (boundary L R 0 (Finsupp.single e a)) = 0
      apply (Submodule.Quotient.mk_eq_zero U).2
      have he : ({edgeEnds e 0, edgeEnds e 1} : Finset V) ∈ L := by
        rw [face_eq_endpoints]
        exact e.property.1
      have hd := signed_path_boundary R hK (paths _ _ he)
      have hU : boundary L R 0 (Finsupp.single e 1) ∈ U := by
        refine ⟨_, hd, ?_⟩
        rw [map_sub, chainIncl_vertex, chainIncl_vertex, signed_boundary_edge R (fun v => h (hK v))]
      have hsingle : Finsupp.single e a = a • (Finsupp.single e (1 : R)) := by simp
      rw [hsingle, map_smul]
      exact U.smul_mem a hU
    exact (Submodule.Quotient.mk_eq_zero U).1 (DFunLike.congr_fun hp c)

private theorem cycleIncl_zero_bijective (h : K ≤ L) (hK : ∀ v : V, ({v} : Finset V) ∈ K) :
    Function.Bijective (simplicialCycleIncl R h 0) := by
  have chainBij := chainIncl_zero_bijective R h hK
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply chainBij.injective
    simpa only [simplicialCycleIncl_coe] using
      congrArg (fun z : simplicialCycles L R 0 => z.val) hxy
  · intro z
    obtain ⟨w, hw⟩ := chainBij.surjective z.val
    let w' : simplicialCycles K R 0 := ⟨w, by rw [simplicialCycles_zero]; trivial⟩
    exact ⟨w', Subtype.ext ((simplicialCycleIncl_coe R h 0 w').trans hw)⟩

private theorem transported_cycles_boundary_eq
    (h : K ≤ L) (hK : ∀ v : V, ({v} : Finset V) ∈ K)
    (paths : ∀ u v, ({u,v} : Finset V) ∈ L →
      Relation.EqvGen (fun a b => ({a,b} : Finset V) ∈ K) u v) :
    (simplicialBoundaries K R 0).map (simplicialCycleIncl R h 0) =
      simplicialBoundaries L R 0 := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact simplicialBoundaries_le_comap R h 0 hz
  · intro z hz
    obtain ⟨c, hc⟩ := (mem_simplicialBoundaries_iff R L 0 z).1 hz
    have hm : z.val ∈ LinearMap.range (boundary L R 0) := ⟨c, hc⟩
    rw [← transported_boundary_eq R h hK paths] at hm
    obtain ⟨_, ⟨d, rfl⟩, hd⟩ := hm
    let z' : simplicialCycles K R 0 :=
      ⟨boundary K R 0 d, by rw [simplicialCycles_zero]; trivial⟩
    exact ⟨z', (mem_simplicialBoundaries_iff R K 0 z').2 ⟨d, rfl⟩,
      Subtype.ext ((simplicialCycleIncl_coe R h 0 z').trans hd)⟩

private theorem simplicialQuotientIncl_zero_bijective
    (h : K ≤ L) (hK : ∀ v : V, ({v} : Finset V) ∈ K)
    (paths : ∀ u v, ({u,v} : Finset V) ∈ L →
      Relation.EqvGen (fun a b => ({a,b} : Finset V) ∈ K) u v) :
    Function.Bijective (simplicialQuotientIncl R h 0) := by
  let e : simplicialCycles K R 0 ≃ₗ[R] simplicialCycles L R 0 :=
    LinearEquiv.ofBijective (simplicialCycleIncl R h 0) (cycleIncl_zero_bijective R h hK)
  have hmap : (simplicialBoundaries K R 0).map e.toLinearMap = simplicialBoundaries L R 0 :=
    transported_cycles_boundary_eq R h hK paths
  let q : (simplicialCycles K R 0 ⧸ simplicialBoundaries K R 0) ≃ₗ[R]
      (simplicialCycles L R 0 ⧸ simplicialBoundaries L R 0) :=
    Submodule.Quotient.equiv (σ₁₂ := RingHom.id R) _ _ e hmap
  have hq : q.toLinearMap = simplicialQuotientIncl R h 0 := by
    apply Submodule.quot_hom_ext
    intro z
    exact (simplicialQuotientIncl_mkQ R h 0 z).symm
  rw [← hq]
  exact q.bijective

set_option backward.isDefEq.respectTransparency false in
/-- An inclusion with all singleton faces induces an isomorphism in ordinary degree zero
over every ring if the endpoints of every target edge can be joined by source edges. -/
theorem simplicialHomologyIncl_zero_isIso_of_edge_reachable_of_ring (h : K ≤ L)
    (hK : ∀ v : V, ({v} : Finset V) ∈ K)
    (paths : ∀ u v, ({u,v} : Finset V) ∈ L →
      Relation.EqvGen (fun a b => ({a,b} : Finset V) ∈ K) u v) :
    IsIso (simplicialHomologyIncl R h 0) := by
  have : IsIso (ModuleCat.ofHom (simplicialQuotientIncl R h 0)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (simplicialQuotientIncl_zero_bijective R h hK paths)
  have : IsIso (simplicialHomologyIncl R h 0 ≫
      (homologyKernelQuotient.{w,u,w} R (simplicialChainComplex L R) 0).hom) := by
    rw [simplicialHomologyIncl_quotient_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (homologyKernelQuotient.{w,u,w} R (simplicialChainComplex L R) 0).hom

end

variable {V : Type u} [LinearOrder V] (R : Type w) [Field R]
variable {K L : PreAbstractSimplicialComplex V}

/-- An inclusion with all singleton faces induces an isomorphism in ordinary degree zero
if the endpoints of every target edge can be joined by source edges. Over an arbitrary ring
this is `simplicialHomologyIncl_zero_isIso_of_edge_reachable_of_ring`. -/
theorem simplicialHomologyIncl_zero_isIso_of_edge_reachable (h : K ≤ L)
    (hK : ∀ v : V, ({v} : Finset V) ∈ K)
    (paths : ∀ u v, ({u,v} : Finset V) ∈ L →
      Relation.EqvGen (fun a b => ({a,b} : Finset V) ∈ K) u v) :
    IsIso (simplicialHomologyIncl R h 0) :=
  simplicialHomologyIncl_zero_isIso_of_edge_reachable_of_ring R h hK paths

end TDA.Simplicial
