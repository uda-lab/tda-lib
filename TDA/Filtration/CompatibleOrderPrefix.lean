import TDA.Filtration.CompatibleOrder
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

/-!
# Prefix complexes from compatible face orders

A `CompatibleOrder` enumerates the actual faces of a preabstract simplicial complex. Its
first `k` faces form a subcomplex because every proper face precedes its cofaces. Counting
the enumerated faces whose filtration value is at most a threshold recovers that sublevel
as one of these prefixes. Equal grades enter together in the recovered sublevel, even though
an intermediate face prefix may split a tied block.
-/

universe u w

namespace TDA.Filtration.CompatibleOrder

variable {V : Type u} {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TDA.Simplicial.TotalFace K)]
variable {f : TDA.Filtration.FilterFunction K α}

/-- The subcomplex consisting of actual faces whose compatible-order index is below `k`. -/
def prefixComplex (e : CompatibleOrder f) (k : ℕ) :
    PreAbstractSimplicialComplex V where
  faces := {s | ∃ hs : s ∈ K, (e.enum.symm ⟨s, hs⟩).val < k}
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨hsK, hsidx⟩ := hs
    constructor
    · exact (K.isRelLowerSet_faces hsK).1
    · intro t hts ht
      have htK : t ∈ K := (K.isRelLowerSet_faces hsK).2 hts ht
      refine ⟨htK, ?_⟩
      by_cases h : t = s
      · subst t
        simpa only [Subtype.mk.injEq] using hsidx
      · have hproper : t ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hts, h⟩
        have hindex := e.face_lt (e.enum.symm ⟨t, htK⟩)
          (e.enum.symm ⟨s, hsK⟩) (by simpa using hproper)
        exact lt_trans hindex hsidx

/-- Membership in a prefix is actual membership in `K` plus an index bound. -/
theorem mem_prefixComplex (e : CompatibleOrder f) (k : ℕ) (s : Finset V) :
    s ∈ e.prefixComplex k ↔
      ∃ hs : s ∈ K, (e.enum.symm ⟨s, hs⟩).val < k := Iff.rfl

/-- The zero prefix is empty. -/
theorem prefixComplex_zero (e : CompatibleOrder f) :
    e.prefixComplex 0 = ⊥ := by
  apply le_antisymm
  · intro s hs
    obtain ⟨_, hidx⟩ := (e.mem_prefixComplex 0 s).mp hs
    omega
  · exact bot_le

/-- Once the stage reaches the number of actual faces, the prefix is all of `K`. -/
theorem prefixComplex_eq_self_of_card_le (e : CompatibleOrder f) (k : ℕ)
    (hk : Fintype.card (TDA.Simplicial.TotalFace K) ≤ k) :
    e.prefixComplex k = K := by
  ext s
  constructor
  · intro hs
    exact ((e.mem_prefixComplex k s).mp hs).1
  · intro hs
    exact (e.mem_prefixComplex k s).mpr ⟨hs, (e.enum.symm ⟨s, hs⟩).isLt.trans_le hk⟩

/-- Prefixes are nested as their face-count stage increases. -/
theorem prefixComplex_mono (e : CompatibleOrder f) :
    Monotone e.prefixComplex := by
  intro k l hkl s hs
  obtain ⟨hsK, hsidx⟩ := (e.mem_prefixComplex k s).mp hs
  exact (e.mem_prefixComplex l s).mpr ⟨hsK, lt_of_lt_of_le hsidx hkl⟩

/-- The natural-number filtration of all compatible-order face prefixes. -/
def prefixFiltration (e : CompatibleOrder f) :
    TDA.Filtration.SimplicialFiltration ℕ V where
  toFun := e.prefixComplex
  monotone' := e.prefixComplex_mono

/-- The number of enumerated faces whose filtration value is at most `r`. -/
def sublevelCount (e : CompatibleOrder f) (r : α) : ℕ :=
  (Finset.univ.filter (fun i : Fin (Fintype.card (TDA.Simplicial.TotalFace K)) =>
    f.value (e.enum i) ≤ r)).card

/-- A sublevel count never exceeds the total number of actual faces. -/
theorem sublevelCount_le_card (e : CompatibleOrder f) (r : α) :
    e.sublevelCount r ≤ Fintype.card (TDA.Simplicial.TotalFace K) := by
  unfold sublevelCount
  exact (Finset.card_filter_le _ _).trans (Finset.card_fin _).le

/-- Sublevel counts are monotone in the threshold. -/
theorem sublevelCount_mono (e : CompatibleOrder f) :
    Monotone e.sublevelCount := by
  intro r q hrq
  unfold sublevelCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans hrq

/-- An enumerated face is below `r` exactly when its index is below the sublevel count. -/
theorem value_le_iff_index_lt_sublevelCount (e : CompatibleOrder f) (r : α)
    (i : Fin (Fintype.card (TDA.Simplicial.TotalFace K))) :
    f.value (e.enum i) ≤ r ↔ i.val < e.sublevelCount r := by
  let S : Finset (Fin (Fintype.card (TDA.Simplicial.TotalFace K))) :=
    Finset.univ.filter (fun j => f.value (e.enum j) ≤ r)
  have hcount : e.sublevelCount r = S.card := rfl
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ S := by
      intro j hj
      have hji : j ≤ i := Finset.mem_Iic.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e.monotone hji).trans hi⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hi
    by_contra hnot
    have hsub : S ⊆ Finset.Iio i := by
      intro j hj
      have hjr : f.value (e.enum j) ≤ r := (Finset.mem_filter.mp hj).2
      apply Finset.mem_Iio.mpr
      by_contra hji
      have hij : i ≤ j := le_of_not_gt hji
      exact hnot ((e.monotone hij).trans hjr)
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

/-- Each graded sublevel is the prefix ending at its count of accepted faces. -/
theorem sublevel_eq_prefixComplex (e : CompatibleOrder f) (r : α) :
    f.sublevel r = e.prefixComplex (e.sublevelCount r) := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsK, hgrade⟩ := (f.mem_sublevel_iff r s).mp hs
    apply (e.mem_prefixComplex _ s).mpr
    refine ⟨hsK, ?_⟩
    have h := (e.value_le_iff_index_lt_sublevelCount r
      (e.enum.symm ⟨s, hsK⟩)).mp
    apply h
    simpa only [Equiv.apply_symm_apply] using hgrade
  · intro hs
    obtain ⟨hsK, hidx⟩ := (e.mem_prefixComplex _ s).mp hs
    apply (f.mem_sublevel_iff r s).mpr
    refine ⟨hsK, ?_⟩
    have h := (e.value_le_iff_index_lt_sublevelCount r
      (e.enum.symm ⟨s, hsK⟩)).mpr hidx
    simpa only [Equiv.apply_symm_apply] using h

/-- The monotone map sending each grade to its sublevel face count. -/
def thresholdMap (e : CompatibleOrder f) : α →o ℕ where
  toFun := e.sublevelCount
  monotone' := e.sublevelCount_mono

/-- Reindexing the prefix filtration by the threshold map recovers `f`'s sublevels. -/
theorem reindex_prefixFiltration (e : CompatibleOrder f) :
    TDA.Filtration.reindex e.thresholdMap e.prefixFiltration =
      f.sublevelFiltration := by
  apply OrderHom.ext
  funext r
  exact (e.sublevel_eq_prefixComplex r).symm

end TDA.Filtration.CompatibleOrder
