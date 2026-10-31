import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Quotient maps after products

Two point-set facts about products of quotient maps, with no separation hypothesis on the
quotient map itself. They are the tools used for the geometric thickening of constructible
ℝ-spaces whose pieces need not be Hausdorff (see `docs/math/reeb-thickening-constructible.md`).

* Locally compact factor. If `q : X → Y` is a quotient map and `I` is locally compact, then
  `q × id_I` and `id_I × q` are quotient maps (`isQuotientMap_prodMap_id_left`,
  `isQuotientMap_prodMap_id_right`). Neither `X` nor `Y` is assumed Hausdorff; the proof reads
  "open" as "continuous into the Sierpiński space" and applies the exponential law behind
  `Topology.IsQuotientMap.continuous_lift_prod_left`. Compact real intervals are the case used
  (`isQuotientMap_prodMap_id_Icc`).
* Proper factor. A proper surjection `f` stays a quotient map after product with the identity of
  an arbitrary space `E` (`isQuotientMap_prodMap_id_of_isProperMap`), since `id_E × f` is proper,
  hence closed. In particular this holds for every continuous surjection from a compact space onto
  a Hausdorff space (`isQuotientMap_prodMap_id_of_compactSpace`); only the source and target of
  `f` carry these hypotheses, and `E` is arbitrary. This is the form used for the scalar
  polygon and gluing maps of a thickened cylinder; product stability is not claimed for
  arbitrary quotient maps, where it fails in general.
-/

open Set Topology

namespace TDA.Topology

universe u v w

section LocallyCompact

variable {X : Type u} {Y : Type v} {I : Type w} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace I] [LocallyCompactSpace I] {q : X → Y}

/-- The product of a quotient map with the identity of a locally compact space is a quotient
map. No separation hypothesis is placed on the source or target of `q`. -/
theorem isQuotientMap_prodMap_id_left (hq : IsQuotientMap q) :
    IsQuotientMap (Prod.map q (id : I → I)) := by
  refine (isQuotientMap_iff _).2 ⟨.of_isOpen_preimage_iff_isOpen fun s => ⟨fun hs => ?_,
    fun hs => hs.preimage (hq.continuous.prodMap continuous_id)⟩,
    hq.surjective.prodMap Function.surjective_id⟩
  rw [isOpen_iff_continuous_mem] at hs ⊢
  exact hq.continuous_lift_prod_left (g := fun p : Y × I => p ∈ s) hs

/-- The mirror form of `isQuotientMap_prodMap_id_left`, with the locally compact factor on the
left. -/
theorem isQuotientMap_prodMap_id_right (hq : IsQuotientMap q) :
    IsQuotientMap (Prod.map (id : I → I) q) := by
  refine (isQuotientMap_iff _).2 ⟨.of_isOpen_preimage_iff_isOpen fun s => ⟨fun hs => ?_,
    fun hs => hs.preimage (continuous_id.prodMap hq.continuous)⟩,
    Function.surjective_id.prodMap hq.surjective⟩
  rw [isOpen_iff_continuous_mem] at hs ⊢
  exact hq.continuous_lift_prod_right (g := fun p : I × Y => p ∈ s) hs

end LocallyCompact

/-- A quotient map stays a quotient map after product with a compact real interval, which may be
empty or a single point. -/
theorem isQuotientMap_prodMap_id_Icc {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {q : X → Y} (hq : IsQuotientMap q) (a b : ℝ) :
    IsQuotientMap (Prod.map q (id : Icc a b → Icc a b)) :=
  isQuotientMap_prodMap_id_left hq

section Proper

variable {X : Type u} {Y : Type v} {E : Type w} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E] {f : X → Y}

/-- A proper surjection stays a quotient map after product with the identity of an arbitrary
space. -/
theorem isQuotientMap_prodMap_id_of_isProperMap (hf : IsProperMap f)
    (hs : Function.Surjective f) : IsQuotientMap (Prod.map (id : E → E) f) :=
  (isProperMap_id.prodMap hf).isClosedMap.isQuotientMap (continuous_id.prodMap hf.continuous)
    (Function.surjective_id.prodMap hs)

/-- A continuous surjection from a compact space onto a Hausdorff space stays a quotient map
after product with the identity of an arbitrary space `E`. Only the source and target of `f`
are compact and Hausdorff; `E` carries no hypothesis. -/
theorem isQuotientMap_prodMap_id_of_compactSpace [CompactSpace X] [T2Space Y]
    (hf : Continuous f) (hs : Function.Surjective f) :
    IsQuotientMap (Prod.map (id : E → E) f) :=
  isQuotientMap_prodMap_id_of_isProperMap hf.isProperMap hs

end Proper

end TDA.Topology
