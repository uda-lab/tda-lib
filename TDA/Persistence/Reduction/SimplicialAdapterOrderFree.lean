import TDA.Persistence.Reduction.SimplicialAdapterBarcode
import TDA.Simplicial.HomologyOrderFree

set_option autoImplicit false

/-!
# The pivot barcode of the simplicial adapter with the vertex order chosen internally

The face boundary matrix of `facePivotBarcode` carries the signs of the ordered chain complex,
so its definition takes a linear order on the vertex type.  A `CompatibleOrder` is an
enumeration of the faces and does not refer to a vertex order.  For two linear orders `o₁`,
`o₂` on the vertex type, the prefix homology modules are related by the comparison
isomorphisms of `simplicialHomologyIso_of_linearOrder`, which commute with the inclusions of
the prefix complexes; hence the structure maps have equal ranks and the prefix barcodes agree
(`facePrefixBarcode_congr_linearOrder`).  The pivot barcode is the prefix barcode
(`facePivotBarcode_eq_facePrefixBarcode`), so the pivot barcodes agree as well
(`facePivotBarcode_congr_linearOrder`).

`facePrefixModuleOrderFree` and `facePivotBarcodeOrderFree` use the vertex order chosen
classically (the well-ordering `WellOrderingRel`), for an arbitrary vertex type.  The fibres of
`facePrefixModuleOrderFree` are `simplicialHomologyOrderFree` of the prefix complexes
(`facePrefixModuleOrderFree_obj`).  `facePivotBarcodeOrderFree_eq_facePivotBarcode` identifies
the order-free barcode with `facePivotBarcode` for every supplied order, and the isomorphism of
`nonempty_facePrefixHomologyIsoPivotBarcode` holds for the order-free module and barcode
(`nonempty_facePrefixModuleOrderFreeIsoPivotBarcodeOrderFree`) and for the order-free module and
the pivot barcode of every supplied order
(`nonempty_facePrefixModuleOrderFreeIsoPivotBarcode`).  The coefficient field lives in the
universe of the vertex type.
-/

universe u w

namespace TDA.Persistence.Reduction

open TDA.Persistence TDA.Simplicial TDA.Filtration CategoryTheory

section ExplicitOrders

variable {V : Type u} {α : Type w} [LinearOrder α] {K : PreAbstractSimplicialComplex V}
  [Fintype (TotalFace K)] {f : FilterFunction K α} (k : Type u) [Field k]
  (o₁ o₂ : LinearOrder V)

omit [LinearOrder α] in
private theorem finrank_range_eq_of_square {A B C D : Type u}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    (S : A ≃ₗ[k] B) (T : C ≃ₗ[k] D) (F : A →ₗ[k] C) (G : B →ₗ[k] D)
    (h : T.toLinearMap.comp F = G.comp S.toLinearMap) :
    Module.finrank k (LinearMap.range F) = Module.finrank k (LinearMap.range G) := by
  have h1 : LinearMap.range (T.toLinearMap.comp F) = (LinearMap.range F).map T.toLinearMap :=
    LinearMap.range_comp _ _
  have h2 : LinearMap.range (G.comp S.toLinearMap) = LinearMap.range G :=
    LinearMap.range_comp_of_range_eq_top _ S.range
  rw [← h2, ← h, h1]
  exact (T.finrank_map_eq (LinearMap.range F)).symm

/-- The canonical barcode of prefix homology is the same for two linear orders on the vertex
type: the comparison isomorphisms of the homology of the prefix complexes commute with the
inclusions, so the structure maps have equal ranks. -/
theorem facePrefixBarcode_congr_linearOrder (e : CompatibleOrder f) (n : ℕ) :
    @facePrefixBarcode V o₁ k _ α _ K _ f e n =
      @facePrefixBarcode V o₂ k _ α _ K _ f e n := by
  unfold facePrefixBarcode
  refine (@rankBarcode_eq_iff _ k _ (@facePrefixModule V o₁ k _ α _ K _ f e n)
    (@facePrefix_finiteDimensional V o₁ k _ α _ K _ f e n)
    (@facePrefixModule V o₂ k _ α _ K _ f e n)
    (@facePrefix_finiteDimensional V o₂ k _ α _ K _ f e n)).2 ?_
  intro s t hst
  unfold structureMapRank
  have hsub := e.prefixComplex_mono (show s.val ≤ t.val from hst)
  have hnat := @simplicialHomologyMap_comp_iso_of_linearOrder V o₁ o₂
    (e.prefixComplex s.val) k _ n V o₁ o₂ (e.prefixComplex t.val) (inclusionVertexMap hsub)
  refine finrank_range_eq_of_square k
    (simplicialHomologyIso_of_linearOrder o₁ o₂ (e.prefixComplex s.val) k n).toLinearEquiv
    (simplicialHomologyIso_of_linearOrder o₁ o₂ (e.prefixComplex t.val) k n).toLinearEquiv _ _ ?_
  rw [@simplicialHomologyMap_inclusion V o₁, @simplicialHomologyMap_inclusion V o₂] at hnat
  exact LinearMap.ext fun x => congrArg (fun g => g.hom x) hnat

/-- The pivot barcode of the simplicial adapter is the same for two linear orders on the vertex
type, for one compatible order `e` of the faces. -/
theorem facePivotBarcode_congr_linearOrder [DecidableEq k] (e : CompatibleOrder f) (p : ℕ) :
    @facePivotBarcode V o₁ α _ K _ f k _ _ e p =
      @facePivotBarcode V o₂ α _ K _ f k _ _ e p := by
  rw [@facePivotBarcode_eq_facePrefixBarcode V o₁ α _ K _ f k _ _ e p,
    @facePivotBarcode_eq_facePrefixBarcode V o₂ α _ K _ f k _ _ e p]
  exact facePrefixBarcode_congr_linearOrder k o₁ o₂ e p

end ExplicitOrders

section OrderFree

variable {V : Type u} {α : Type w} [LinearOrder α] {K : PreAbstractSimplicialComplex V}
  [Fintype (TotalFace K)] {f : FilterFunction K α} (k : Type u) [Field k]

/-- The prefix homology module with the vertex order chosen classically (the well-ordering
`WellOrderingRel`), for an arbitrary vertex type. -/
noncomputable def facePrefixModuleOrderFree (e : CompatibleOrder f) (n : ℕ) :
    PModule.{u,0,u} k (Fin (faceCount K + 1)) :=
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  facePrefixModule k e n

/-- The fibres of the order-free prefix homology module are the order-free homology modules of
the prefix complexes. -/
theorem facePrefixModuleOrderFree_obj (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K + 1)) :
    (facePrefixModuleOrderFree k e n).obj i =
      simplicialHomologyOrderFree (e.prefixComplex i.val) k n := rfl

/-- The pivot barcode with the vertex order chosen classically (the well-ordering
`WellOrderingRel`), for an arbitrary vertex type. -/
noncomputable def facePivotBarcodeOrderFree [DecidableEq k] (e : CompatibleOrder f) (p : ℕ) :
    Multiset (FiniteInterval (faceCount K + 1)) :=
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  facePivotBarcode k e p

/-- The order-free pivot barcode equals the pivot barcode of every supplied linear order. -/
theorem facePivotBarcodeOrderFree_eq_facePivotBarcode [o : LinearOrder V] [DecidableEq k]
    (e : CompatibleOrder f) (p : ℕ) :
    facePivotBarcodeOrderFree k e p = facePivotBarcode k e p :=
  facePivotBarcode_congr_linearOrder k (IsWellOrder.linearOrder WellOrderingRel) o e p

/-- The order-free prefix homology module is naturally isomorphic to the interval module of the
order-free pivot barcode. -/
theorem nonempty_facePrefixModuleOrderFreeIsoPivotBarcodeOrderFree [DecidableEq k]
    (e : CompatibleOrder f) (p : ℕ) :
    Nonempty (facePrefixModuleOrderFree k e p ≅
      barcodeModule (k := k) (facePivotBarcodeOrderFree k e p)) :=
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  nonempty_facePrefixHomologyIsoPivotBarcode k e p

/-- The order-free prefix homology module is naturally isomorphic to the interval module of the
pivot barcode of every supplied linear order. -/
theorem nonempty_facePrefixModuleOrderFreeIsoPivotBarcode [o : LinearOrder V] [DecidableEq k]
    (e : CompatibleOrder f) (p : ℕ) :
    Nonempty (facePrefixModuleOrderFree k e p ≅
      barcodeModule (k := k) (facePivotBarcode k e p)) := by
  rw [← facePivotBarcodeOrderFree_eq_facePivotBarcode k e p]
  exact nonempty_facePrefixModuleOrderFreeIsoPivotBarcodeOrderFree k e p

end OrderFree

end TDA.Persistence.Reduction
