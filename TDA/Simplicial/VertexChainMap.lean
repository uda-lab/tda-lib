import TDA.Simplicial.OrientedTuple
import TDA.Simplicial.VertexMap
import TDA.Simplicial.Homology

/-!
# Signed chains and homology induced by arbitrary vertex maps

The image of a face is zero in its original degree when vertices merge.
Otherwise its orientation is transported by the sorting permutation.
-/

namespace TDA.Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Module
open scoped BigOperators

universe u v

noncomputable section

variable {V W U : Type u} [LinearOrder V] [LinearOrder W] [LinearOrder U]
variable {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}
variable {M : PreAbstractSimplicialComplex U}
variable (R : Type v) [Ring R]

/-- The signed linear chain map of an arbitrary simplicial vertex map in one degree. -/
def vertexChainMap (f : VertexMap K L) (n : ℕ) : Chain K R n →ₗ[R] Chain L R n :=
  Finsupp.linearCombination R (fun s : Face K n =>
    orientedTuple L R (f ∘ s.1.orderEmbOfFin s.2.2))

/-- The image of a basis chain, retaining its left coefficient. -/
theorem vertexChainMap_single (f : VertexMap K L) (n : ℕ) (s : Face K n) (a : R) :
    vertexChainMap R f n (Finsupp.single s a) =
      a • orientedTuple L R (f ∘ s.1.orderEmbOfFin s.2.2) := by
  simp [vertexChainMap]

private theorem vertexTuple_mem (f : VertexMap K L) {n : ℕ}
    (x : Fin (n + 1) → V) (hk : Finset.univ.image x ∈ K) :
    Finset.univ.image (f ∘ x) ∈ L := by
  have h := f.map_face (Finset.univ.image x) hk
  have he : @Finset.image V W (Classical.decEq W) f (Finset.univ.image x) =
      Finset.univ.image (f ∘ x) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, hv⟩
      exact ⟨i, hv⟩
    · rintro ⟨i, hi⟩
      exact ⟨x i, ⟨i, rfl⟩, hi⟩
  rw [he] at h
  exact h

/-- Vertex-induced maps act on every oriented tuple by applying the vertex function. -/
theorem vertexChainMap_orientedTuple (f : VertexMap K L) {n : ℕ}
    (x : Fin (n + 1) → V) (hk : Finset.univ.image x ∈ K) :
    vertexChainMap R f n (orientedTuple K R x) = orientedTuple L R (f ∘ x) := by
  by_cases hx : Function.Injective x
  · rw [orientedTuple_of_injective K R x hx hk, map_zsmul, vertexChainMap_single,
      one_smul, tupleFace_sorted_enumeration K x hx hk]
    have he : f ∘ (x ∘ Tuple.sort x) = (f ∘ x) ∘ Tuple.sort x := rfl
    rw [he, orientedTuple_comp_perm, smul_smul]
    have hs : (Equiv.Perm.sign (Tuple.sort x) : ℤ) *
        (Equiv.Perm.sign (Tuple.sort x) : ℤ) = 1 := by
      simp
    rw [hs, one_smul]
  · have hfx : ¬Function.Injective (f ∘ x) := by
      intro h
      exact hx (fun _ _ hxy => h (congrArg f hxy))
    rw [orientedTuple_of_not_injective K R x hx, map_zero,
      orientedTuple_of_not_injective L R _ hfx]

/-- The signed boundary commutes with every simplicial vertex map. -/
theorem boundary_vertexChainMap (f : VertexMap K L) (n : ℕ) :
    (boundary L R n).comp (vertexChainMap R f (n + 1)) =
      (vertexChainMap R f n).comp (boundary K R n) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  have hk : Finset.univ.image (s.1.orderEmbOfFin s.2.2) ∈ K := by
    simpa only [Finset.image_orderEmbOfFin_univ] using s.2.1
  change boundary L R n (vertexChainMap R f (n + 1) (Finsupp.single s 1)) =
    vertexChainMap R f n (boundary K R n (Finsupp.single s 1))
  rw [← orientedTuple_face K R s, vertexChainMap_orientedTuple R f _ hk,
    boundary_orientedTuple L R _ (vertexTuple_mem f _ hk), boundary_orientedTuple K R _ hk]
  unfold tupleBoundarySum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, vertexChainMap_orientedTuple R f _ (tupleImage_delete_mem K _ hk i)]
  rfl

/-- The chain-complex morphism of an arbitrary simplicial vertex map. -/
def simplicialChainMap (f : VertexMap K L) :
    simplicialChainComplex K R ⟶ simplicialChainComplex L R :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (vertexChainMap R f n)) (by
    intro n
    apply ModuleCat.hom_ext
    simp only [simplicialChainComplex_d]
    exact boundary_vertexChainMap R f n)

@[simp] theorem simplicialChainMap_f (f : VertexMap K L) (n : ℕ) :
    (simplicialChainMap R f).f n = ModuleCat.ofHom (vertexChainMap R f n) := rfl

/-- The identity vertex function induces the identity linear map. -/
theorem vertexChainMap_id (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    vertexChainMap R (VertexMap.id K) n = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s a
  rw [vertexChainMap_single]
  change a • orientedTuple K R (s.1.orderEmbOfFin s.2.2) = Finsupp.single s a
  rw [orientedTuple_face]
  simp

/-- Signed linear vertex maps compose strictly, including degenerate images. -/
theorem vertexChainMap_comp (f : VertexMap K L) (g : VertexMap L M) (n : ℕ) :
    vertexChainMap R (VertexMap.comp f g) n =
      (vertexChainMap R g n).comp (vertexChainMap R f n) := by
  apply Finsupp.lhom_ext
  intro s a
  have hk : Finset.univ.image (s.1.orderEmbOfFin s.2.2) ∈ K := by
    simpa only [Finset.image_orderEmbOfFin_univ] using s.2.1
  change vertexChainMap R (VertexMap.comp f g) n (Finsupp.single s a) =
    vertexChainMap R g n (vertexChainMap R f n (Finsupp.single s a))
  rw [vertexChainMap_single, vertexChainMap_single, map_smul,
    vertexChainMap_orientedTuple R g _ (vertexTuple_mem f _ hk)]
  rfl

/-- The identity simplicial vertex map induces the identity chain map. -/
theorem simplicialChainMap_id (K : PreAbstractSimplicialComplex V) :
    simplicialChainMap R (VertexMap.id K) = 𝟙 (simplicialChainComplex K R) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [vertexChainMap_id]

/-- Arbitrary vertex maps induce strictly composable chain maps. -/
theorem simplicialChainMap_comp (f : VertexMap K L) (g : VertexMap L M) :
    simplicialChainMap R (VertexMap.comp f g) =
      simplicialChainMap R f ≫ simplicialChainMap R g := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [simplicialChainMap_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  exact vertexChainMap_comp R f g n

/-- An inclusion as a vertex map on its unchanged ambient vertex type. -/
def inclusionVertexMap {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) :
    VertexMap K L where
  toFun := id
  map_face s hs := by
    have he : @Finset.image V V (Classical.decEq V) id s = s := by
      ext v
      simp only [Finset.mem_image, id_eq, exists_eq_right]
    rw [he]
    exact h hs

/-- The new signed map specializes to the existing linear inclusion. -/
theorem vertexChainMap_inclusion {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (n : ℕ) : vertexChainMap R (inclusionVertexMap h) n = chainIncl R h n := by
  apply Finsupp.lhom_ext
  intro s a
  rw [vertexChainMap_single, chainIncl_single]
  have ht : inclusionVertexMap h ∘ s.1.orderEmbOfFin s.2.2 =
      (faceIncl h n s).1.orderEmbOfFin (faceIncl h n s).2.2 := rfl
  rw [ht, orientedTuple_face]
  simp

/-- The new chain map agrees with the existing chain inclusion. -/
theorem simplicialChainMap_inclusion {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) : simplicialChainMap R (inclusionVertexMap h) = simplicialChainIncl R h := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [vertexChainMap_inclusion]

/-- The map on the existing simplicial homology induced by a vertex map. -/
def simplicialHomologyMap (f : VertexMap K L) (n : ℕ) :
    simplicialHomology K R n ⟶ simplicialHomology L R n :=
  HomologicalComplex.homologyMap (simplicialChainMap R f) n

/-- Homology takes identity vertex maps to identity maps. -/
theorem simplicialHomologyMap_id (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    simplicialHomologyMap R (VertexMap.id K) n = 𝟙 (simplicialHomology K R n) := by
  unfold simplicialHomologyMap
  rw [simplicialChainMap_id]
  exact HomologicalComplex.homologyMap_id _ n

/-- Homology takes vertex-map composition to composition. -/
theorem simplicialHomologyMap_comp (f : VertexMap K L) (g : VertexMap L M) (n : ℕ) :
    simplicialHomologyMap R (VertexMap.comp f g) n =
      simplicialHomologyMap R f n ≫ simplicialHomologyMap R g n := by
  unfold simplicialHomologyMap
  rw [simplicialChainMap_comp]
  exact HomologicalComplex.homologyMap_comp _ _ n

/-- The induced homology map specializes to the existing inclusion. -/
theorem simplicialHomologyMap_inclusion {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (n : ℕ) :
    simplicialHomologyMap R (inclusionVertexMap h) n = simplicialHomologyIncl R h n := by
  unfold simplicialHomologyMap simplicialHomologyIncl
  rw [simplicialChainMap_inclusion]

/-- A collapsed face contributes zero in its original degree, with any coefficient. -/
theorem vertexChainMap_single_of_not_injective (f : VertexMap K L) (n : ℕ)
    (s : Face K n) (a : R) (hx : ¬Function.Injective (f ∘ s.1.orderEmbOfFin s.2.2)) :
    vertexChainMap R f n (Finsupp.single s a) = 0 := by
  rw [vertexChainMap_single, orientedTuple_of_not_injective L R _ hx, smul_zero]

/-- The image face when a vertex map is injective on the enumerated face. -/
def vertexImageFace (f : VertexMap K L) {n : ℕ} (s : Face K n)
    (hx : Function.Injective (f ∘ s.1.orderEmbOfFin s.2.2)) : Face L n :=
  tupleFace L _ hx (vertexTuple_mem f _ (by
    simpa only [Finset.image_orderEmbOfFin_univ] using s.2.1))

/-- A noncollapsed basis face acquires exactly the sign of its image sorting permutation. -/
theorem vertexChainMap_single_of_injective (f : VertexMap K L) (n : ℕ)
    (s : Face K n) (a : R) (hx : Function.Injective (f ∘ s.1.orderEmbOfFin s.2.2)) :
    vertexChainMap R f n (Finsupp.single s a) =
      a • ((Equiv.Perm.sign (Tuple.sort (f ∘ s.1.orderEmbOfFin s.2.2)) : ℤ) •
        Finsupp.single (vertexImageFace f s hx) (1 : R)) := by
  rw [vertexChainMap_single, orientedTuple_of_injective L R _ hx
    (vertexTuple_mem f _ (by simpa only [Finset.image_orderEmbOfFin_univ] using s.2.1))]
  rfl

/-- A vertex generator maps to its image vertex generator with unchanged coefficient. -/
theorem vertexChainMap_vertex (f : VertexMap K L) (s : Face K 0) (a : R) :
    vertexChainMap R f 0 (Finsupp.single s a) =
      Finsupp.single (vertexImageFace f s (fun i j _ => Fin.ext (by omega))) a := by
  rw [vertexChainMap_single]
  have hm : Monotone (f ∘ s.1.orderEmbOfFin s.2.2) :=
    fun i j _ => le_of_eq (congrArg (f ∘ s.1.orderEmbOfFin s.2.2) (show i = j from Fin.ext (by omega)))
  rw [orientedTuple_of_monotone L R _ (fun i j _ => Fin.ext (by omega))
    (vertexTuple_mem f _ (by simpa only [Finset.image_orderEmbOfFin_univ] using s.2.1)) hm]
  simp [vertexImageFace]

private def shortHomologyClass (S : ShortComplex (ModuleCat.{max u v} R))
    (z : LinearMap.ker S.g.hom) : S.homology :=
  (S.moduleCatCyclesIso.inv ≫ S.homologyπ).hom z

private theorem shortHomologyClass_map
    (S T : ShortComplex (ModuleCat.{max u v} R)) (φ : S ⟶ T)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker T.g.hom)
    (h : φ.τ₂.hom (z : S.X₂) = (w : T.X₂)) :
    (ShortComplex.homologyMap φ).hom (shortHomologyClass R S z) =
      shortHomologyClass R T w := by
  have hc : (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ).hom z =
      T.moduleCatCyclesIso.inv.hom w := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    change (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫ T.iCycles).hom z =
      (T.moduleCatCyclesIso.inv ≫ T.iCycles).hom w
    rw [ShortComplex.cyclesMap_i, ← Category.assoc,
      ShortComplex.moduleCatCyclesIso_inv_iCycles,
      ShortComplex.moduleCatCyclesIso_inv_iCycles]
    exact h
  have hn := congrArg
    (fun q => q.hom (S.moduleCatCyclesIso.inv.hom z))
    (ShortComplex.homologyπ_naturality φ)
  change (ShortComplex.homologyMap φ).hom (shortHomologyClass R S z) =
    T.homologyπ.hom ((S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ).hom z) at hn
  rw [hc] at hn
  exact hn

/-- The homology class of a cycle, through mathlib's homology projection. -/
def simplicialHomologyClass (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (z : simplicialCycles K R n) : simplicialHomology K R n :=
  shortHomologyClass R ((simplicialChainComplex K R).sc n) z

/-- The homology class has its usual representative in the existing kernel/image quotient. -/
theorem simplicialHomologyClass_quotient (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (z : simplicialCycles K R n) :
    (homologyKernelQuotient.{v,u,v} R (simplicialChainComplex K R) n).hom.hom
      (simplicialHomologyClass R K n z) = (simplicialBoundaries K R n).mkQ z := by
  let S := (simplicialChainComplex K R).sc n
  change (S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ S.moduleCatHomologyIso.hom).hom z = _
  rw [← Category.assoc, ShortComplex.moduleCatCyclesIso_inv_π]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The induced homology map takes a cycle class to its chain image class. -/
theorem simplicialHomologyMap_class (f : VertexMap K L) (n : ℕ)
    (z : simplicialCycles K R n) (w : simplicialCycles L R n)
    (h : vertexChainMap R f n (z : Chain K R n) = (w : Chain L R n)) :
    (simplicialHomologyMap R f n).hom (simplicialHomologyClass R K n z) =
      simplicialHomologyClass R L n w := by
  exact shortHomologyClass_map R _ _
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (simplicialChainMap R f)) z w h

/-- The singleton vertex class has its original coefficient under the existing H0 equivalence. -/
theorem simplicialSingletonH0Equiv_class (v : V) (a : R) :
    simplicialSingletonH0Equiv R v
      (simplicialHomologyClass R (Filtration.singletonFace v) 0
        ⟨Finsupp.single (singletonVertex v) a, by rw [simplicialCycles_zero]; trivial⟩) = a := by
  let S := (simplicialChainComplex (Filtration.singletonFace v) R).sc 0
  have hf : S.f = 0 := by
    change (simplicialChainComplex (Filtration.singletonFace v) R).d
      ((ComplexShape.down ℕ).prev 0) 0 = 0
    rw [ChainComplex.prev]
    apply ModuleCat.hom_ext
    ext c
    change boundary (Filtration.singletonFace v) R 0 c = 0
    rw [singletonHigherChain_eq_zero v R 0 c]
    simp
  have hg : S.g = 0 := by
    change (simplicialChainComplex (Filtration.singletonFace v) R).d
      0 ((ComplexShape.down ℕ).next 0) = 0
    rw [ChainComplex.next_nat_zero]
    exact simplicialChainComplex_d_zero _ R 0
  have hi : (ShortComplex.LeftHomologyData.ofZeros S hf hg).cyclesIso.hom =
      S.iCycles := by
    simpa [ShortComplex.LeftHomologyData.ofZeros] using
      (ShortComplex.LeftHomologyData.ofZeros S hf hg).cyclesIso_hom_comp_i
  have hn : S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫
      (ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyIso.hom =
      S.moduleCatLeftHomologyData.i := by
    rw [(ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyπ_comp_homologyIso_hom]
    simp only [ShortComplex.LeftHomologyData.ofZeros_π]
    rw [hi]
    exact S.moduleCatCyclesIso_inv_iCycles
  change (Finsupp.uniqueLinearEquiv R R (singletonVertex v))
    ((S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫
      (ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyIso.hom).hom
      ⟨Finsupp.single (singletonVertex v) a, _⟩) = a
  rw [hn]
  change (Finsupp.single (singletonVertex v) a) (singletonVertex v) = a
  simp

end
end TDA.Simplicial
