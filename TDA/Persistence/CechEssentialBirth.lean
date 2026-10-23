import TDA.Persistence.EssentialVanishing

/-!
# The essential Čech H₀ bar starts at zero

Every singleton has infimal enclosing radius zero. Its vertex class
survives inclusion into a full stage, so the diagram has an essential point
already alive at zero. Nonnegative critical values and the existing essential
count identify the entire essential multiset, including its multiplicity.

This is ordinary unreduced homology of the library's real radius filter, whose
negative stages are empty. It does not identify the whole real H₀ module with
CDSO's nonpositive-scale vertex-retaining convention.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.Cech

open TDA.Simplicial TDA.Filtration

variable {V : Type u} [LinearOrder V] [Fintype V]
variable {X : Type w} [PseudoMetricSpace X]

private theorem singleton_value_eq_zero (a : V → X) (v : V) :
    (Cech.filter a).value
      (⟨{v}, by simp⟩ : TotalFace (Rips.fullComplex V)) = 0 := by
  apply le_antisymm _ (Cech.filter_value_nonneg a _)
  apply (Cech.filter_value_le_radiusAt a _ (a v)).trans
  exact (Cech.radiusAt_le_iff a (a v) {v} 0).mpr ⟨le_rfl, by simp⟩

/-- The surviving point is obtained from the rank of an inclusion,
rather than inferred from the eventual essential count. -/
private theorem zero_mem_essentialPart_dgm (k : Type u) [Field k]
    (a : V → X) [Nonempty V] :
    0 ∈ essentialPart (dgm k (Cech.filter a) 0).points := by
  classical
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  let f := Cech.filter a
  let t := Cech.radiusAt a (a v) Finset.univ
  have ht : 0 ≤ t := Cech.radiusAt_nonneg a (a v) Finset.univ
  have hstage : f.sublevel t = Rips.fullComplex V :=
    sublevel_eq_fullComplex a (a v) le_rfl
  have hfull (s : TotalFace (Rips.fullComplex V)) : f.value s ≤ t := by
    apply (f.mem_sublevel_iff_of_mem t s).mp
    rw [hstage]
    exact s.property
  let σ : Face (f.sublevel 0) 0 :=
    ⟨{v}, (f.mem_sublevel_iff 0 {v}).mpr
      ⟨by simp, (singleton_value_eq_zero a v).le⟩, by simp⟩
  have hrank := finrank_homologyIncl_range_pos_of_vertex
    (f.sublevel 0) k (f.sublevel_mono ht) σ
  rw [rank_sublevelHomologyMap k f 0 0 t ht] at hrank
  obtain ⟨p, hp, hb, hd⟩ := Multiset.countP_pos.mp hrank
  have htop : p.2 = ⊤ := by
    by_contra hne
    have hparts : p ∈
        (finitePart (dgm k f 0).points).map (fun q => (q.1, (q.2 : WithTop ℝ))) +
          (essentialPart (dgm k f 0).points).map (fun b => (b, (⊤ : WithTop ℝ))) := by
      rw [parts_reconstruct]
      exact hp
    rcases Multiset.mem_add.mp hparts with hfinite | hessential
    · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hfinite
      obtain ⟨s, hs⟩ := (FilterFunction.mem_criticalValues f q.2).mp
        (mem_criticalValues_of_mem_finitePart_dgm k f hq).2
      have hdeath : q.2 ≤ t := by
        rw [← hs]
        exact hfull s
      exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hdeath)) hd
    · obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hessential
      exact hne rfl
  have hessential : p.1 ∈ essentialPart (dgm k f 0).points := by
    apply (Multiset.mem_filterMap _ _).mpr
    exact ⟨p, hp, by simp [htop]⟩
  obtain ⟨s, hs⟩ := (FilterFunction.mem_criticalValues f p.1).mp
    (mem_criticalValues_of_mem_essentialPart_dgm k f hessential)
  have hnonneg : 0 ≤ p.1 := by
    rw [← hs]
    exact Cech.filter_value_nonneg a s
  have hbirth : p.1 = 0 := le_antisymm hb hnonneg
  simpa only [hbirth] using hessential

/-- The ordinary degree-zero Čech diagram has exactly one essential
occurrence, born at zero, on every nonempty finite label type. Repeated labels
and arbitrary pseudometric ambient spaces are included. -/
theorem essentialPart_dgm_zero_eq_singleton (k : Type u) [Field k]
    (a : V → X) [Nonempty V] :
    essentialPart (dgm k (Cech.filter a) 0).points = ({0} : Multiset ℝ) := by
  classical
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp (card_essentialPart_dgm_zero k a)
  have hz : (0 : ℝ) = b := by
    simpa only [hb, Multiset.mem_singleton] using zero_mem_essentialPart_dgm k a
  simpa only [← hz] using hb

end TDA.Persistence.Cech
