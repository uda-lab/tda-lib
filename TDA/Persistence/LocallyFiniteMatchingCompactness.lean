import TDA.Persistence.QTameFiniteSaturation
import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Global matching compactness for locally finite diagrams

Finite saturation on every finite set of long finite and essential occurrences
extends to one global matching.  Local finiteness makes each finite stage have
only finitely many candidate edges, so the inverse system of finite matching
sets has a coherent section.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence

open CategoryTheory Opposite RectangleMeasure
open scoped ENNReal NNReal Classical

noncomputable section

private theorem cut_mem_cell_of_endpoint_inside {c : Cut ℝ} {a b : ℝ}
    (hc : ∃ x y, c ∈ cutCell x y) (ha : a < cutEndpoint c) (hb : cutEndpoint c < b) :
    c ∈ cutCell a b := by
  obtain ⟨x, y, hcell⟩ := hc
  rcases cut_eq_minus_or_plus_of_mem_cutCell hcell with hminus | hplus
  · rw [hminus]
    change a ∈ (minusCut (cutEndpoint c)).lower ∧ b ∈ (minusCut (cutEndpoint c)).upper
    exact ⟨by simpa [minusCut] using ha, by simpa [minusCut] using hb.le⟩
  · rw [hplus]
    change a ∈ (plusCut (cutEndpoint c)).lower ∧ b ∈ (plusCut (cutEndpoint c)).upper
    exact ⟨by simpa [plusCut] using ha.le, by simpa [plusCut] using hb⟩

private theorem finiteOccurrence_neighbors_finite
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (x : D.finiteOccurrences)
    (hlong : 2 * (ε : ℝ) < (D.finitePoint x).2 - (D.finitePoint x).1) :
    Finite {y : E.finiteOccurrences //
      finitePairCost (D.finitePoint x) (E.finitePoint y) ≤ ENNReal.ofReal (ε : ℝ)} := by
  classical
  let birth := (D.finitePoint x).1
  let death := (D.finitePoint x).2
  let δ := ((ε : ℝ) + (death - birth) / 2) / 2
  have hgap : birth < death := by
    exact D.finiteEndpointOrder x.1.1 x.1.2.1 x.1.2.2
  have hεδ : (ε : ℝ) < δ := by dsimp [δ]; linarith
  have hδgap : δ < (death - birth) / 2 := by dsimp [δ]; linarith
  have hδ : 0 < δ := by linarith
  let a := birth - δ
  let b := birth + δ
  let c := death - δ
  let d := death + δ
  have hab : a < b := by dsimp [a, b]; linarith
  have hbc : b < c := by dsimp [b, c]; linarith
  have hcd : c < d := by dsimp [c, d]; linarith
  let S : Set (Cut ℝ × Cut ℝ) :=
    {p | p ∈ rectangleCell a b c d ∧ 0 < E.multiplicity p}
  have hS : S.Finite := by
    exact E.locallyFiniteRectangle a b c d hab hbc hcd
  let Tokens := {p : Cut ℝ × Cut ℝ // p ∈ S}
  letI : Finite Tokens := hS
  let emb : {y : E.finiteOccurrences //
      finitePairCost (D.finitePoint x) (E.finitePoint y) ≤ ENNReal.ofReal (ε : ℝ)} →
      Σ p : Tokens, Fin (E.multiplicity p.1) := fun y => by
    have hcost := y.2
    have hmax : max |birth - (E.finitePoint y.1).1|
        |death - (E.finitePoint y.1).2| ≤ (ε : ℝ) := by
      have h := (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg ε)).1 hcost
      simpa [finitePairCost, birth, death] using h
    have hb : |(E.finitePoint y.1).1 - birth| ≤ (ε : ℝ) := by
      have := le_trans (le_max_left _ _) hmax
      simpa [abs_sub_comm] using this
    have hd : |(E.finitePoint y.1).2 - death| ≤ (ε : ℝ) := by
      have := le_trans (le_max_right _ _) hmax
      simpa [abs_sub_comm] using this
    have hborn : a < cutEndpoint y.1.1.1.1 ∧ cutEndpoint y.1.1.1.1 < b := by
      have hb' : |cutEndpoint y.1.1.1.1 - birth| ≤ (ε : ℝ) := by
        simpa [LocallyFiniteDecoratedDiagram.finitePoint, birth] using hb
      constructor <;> dsimp [a, b] <;> rw [abs_le] at hb' <;> dsimp [δ] at * <;> linarith
    have hdead : c < cutEndpoint y.1.1.1.2 ∧ cutEndpoint y.1.1.1.2 < d := by
      have hd' : |cutEndpoint y.1.1.1.2 - death| ≤ (ε : ℝ) := by
        simpa [LocallyFiniteDecoratedDiagram.finitePoint, death] using hd
      constructor <;> dsimp [c, d] <;> rw [abs_le] at hd' <;> dsimp [δ] at * <;> linarith
    have hend := E.finiteEndpoints y.1.1.1 y.1.1.2.1 y.1.1.2.2
    have hcell1 := cut_mem_cell_of_endpoint_inside hend.1 hborn.1 hborn.2
    have hcell2 := cut_mem_cell_of_endpoint_inside hend.2 hdead.1 hdead.2
    exact ⟨⟨y.1.1.1, ⟨⟨hcell1, hcell2⟩, y.1.1.2.1⟩⟩, y.1.2⟩
  have hemb : Function.Injective emb := by
    intro y z h
    rcases y with ⟨⟨⟨p, hp⟩, iy⟩, hy⟩
    rcases z with ⟨⟨⟨q, hq⟩, iz⟩, hz⟩
    dsimp [emb] at h
    have hpq : p = q := congrArg
      (fun t : Σ p : Tokens, Fin (E.multiplicity p.1) => t.1.1) h
    have hij : (iy : ℕ) = iz := congrArg
      (fun t : Σ p : Tokens, Fin (E.multiplicity p.1) => (t.2 : ℕ)) h
    subst q
    have hidx : iy = iz := Fin.ext hij
    subst iz
    rfl
  exact Finite.of_injective emb hemb

private theorem essentialOccurrence_neighbors_finite
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (x : D.essentialOccurrences) :
    Finite {y : E.essentialOccurrences //
      essentialPairCost (D.essentialBirth x) (E.essentialBirth y) ≤
        ENNReal.ofReal (ε : ℝ)} := by
  classical
  let birth := D.essentialBirth x
  let δ := (ε : ℝ) + 1
  let a := birth - δ
  let b := birth + δ
  let c := b + 1
  have hab : a < b := by dsimp [a, b, δ]; linarith
  have hbc : b < c := by dsimp [c]; linarith
  let S : Set (Cut ℝ × Cut ℝ) :=
    {p | p ∈ tailRectangleCell a b c ∧ 0 < E.multiplicity p}
  have hS : S.Finite := E.locallyFiniteTail a b c hab hbc
  let Tokens := {p : Cut ℝ × Cut ℝ // p ∈ S}
  letI : Finite Tokens := hS
  let emb : {y : E.essentialOccurrences //
      essentialPairCost (D.essentialBirth x) (E.essentialBirth y) ≤
        ENNReal.ofReal (ε : ℝ)} → Σ p : Tokens, Fin (E.multiplicity p.1) := fun y => by
    have hcost : |birth - E.essentialBirth y.1| ≤ (ε : ℝ) := by
      apply (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg ε)).1
      simpa [essentialPairCost] using y.2
    have hb : |E.essentialBirth y.1 - birth| ≤ (ε : ℝ) := by
      simpa [abs_sub_comm] using hcost
    have hbirth : a < cutEndpoint y.1.1.1 ∧ cutEndpoint y.1.1.1 < b := by
      have hb' : |cutEndpoint y.1.1.1 - birth| ≤ (ε : ℝ) := by
        simpa [LocallyFiniteDecoratedDiagram.essentialBirth, birth] using hb
      constructor <;> dsimp [a, b, δ] <;> rw [abs_le] at hb' <;> linarith
    have hend := E.essentialBirthEndpoint y.1.1.1 y.1.1.2
    have hcell := cut_mem_cell_of_endpoint_inside hend hbirth.1 hbirth.2
    have hc : c ∈ infinityCut.lower := by
      simp [infinityCut, cutOfLowerSet]
    exact ⟨⟨(y.1.1.1, infinityCut), ⟨hcell, hc⟩, y.1.1.2⟩, y.1.2⟩
  have hemb : Function.Injective emb := by
    intro y z h
    rcases y with ⟨⟨⟨birth, hb⟩, iy⟩, hy⟩
    rcases z with ⟨⟨⟨birth', hb'⟩, iz⟩, hz⟩
    dsimp [emb] at h
    have hpoint : (birth, infinityCut) = (birth', infinityCut) := congrArg
      (fun t : Σ p : Tokens, Fin (E.multiplicity p.1) => t.1.1) h
    have hbirth : birth = birth' := congrArg Prod.fst hpoint
    have hij : (iy : ℕ) = iz := congrArg
      (fun t : Σ p : Tokens, Fin (E.multiplicity p.1) => (t.2 : ℕ)) h
    subst birth'
    have hidx : iy = iz := Fin.ext hij
    subst iz
    rfl
  exact Finite.of_injective emb hemb

private abbrev LongFiniteOccurrence (D : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0) :=
  {x : D.finiteOccurrences // 2 * (ε : ℝ) <
    (D.finitePoint x).2 - (D.finitePoint x).1}

private abbrev MatchingIndex (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0) :=
  (Finset (LongFiniteOccurrence D ε) × Finset (LongFiniteOccurrence E ε)) ×
    (Finset D.essentialOccurrences × Finset E.essentialOccurrences)

private instance matchingIndexCategory (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0) :
    Category (MatchingIndex D E ε) := Preorder.smallCategory _

private def finiteSourceCandidates (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (s : Finset (LongFiniteOccurrence D ε)) : Set (D.finiteOccurrences × E.finiteOccurrences) :=
  {e | ∃ x ∈ s, e.1 = x.1 ∧
    finitePairCost (D.finitePoint e.1) (E.finitePoint e.2) ≤ ENNReal.ofReal (ε : ℝ)}

private def finiteTargetCandidates (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (s : Finset (LongFiniteOccurrence E ε)) : Set (D.finiteOccurrences × E.finiteOccurrences) :=
  {e | ∃ y ∈ s, e.2 = y.1 ∧
    finitePairCost (D.finitePoint e.1) (E.finitePoint e.2) ≤ ENNReal.ofReal (ε : ℝ)}

private def finiteCandidates (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (I : MatchingIndex D E ε) : Set (D.finiteOccurrences × E.finiteOccurrences) :=
  finiteSourceCandidates D E ε I.1.1 ∪ finiteTargetCandidates D E ε I.1.2

private def essentialSourceCandidates (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (s : Finset D.essentialOccurrences) : Set (D.essentialOccurrences × E.essentialOccurrences) :=
  {e | ∃ x ∈ s, e.1 = x ∧
    essentialPairCost (D.essentialBirth e.1) (E.essentialBirth e.2) ≤ ENNReal.ofReal (ε : ℝ)}

private def essentialTargetCandidates (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (s : Finset E.essentialOccurrences) : Set (D.essentialOccurrences × E.essentialOccurrences) :=
  {e | ∃ y ∈ s, e.2 = y ∧
    essentialPairCost (D.essentialBirth e.1) (E.essentialBirth e.2) ≤ ENNReal.ofReal (ε : ℝ)}

private def essentialCandidates (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (I : MatchingIndex D E ε) : Set (D.essentialOccurrences × E.essentialOccurrences) :=
  essentialSourceCandidates D E ε I.2.1 ∪ essentialTargetCandidates D E ε I.2.2

private theorem finite_sourceCandidates_finite
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (s : Finset (LongFiniteOccurrence D ε)) :
    (finiteSourceCandidates D E ε s).Finite := by
  classical
  let L := {x : LongFiniteOccurrence D ε // x ∈ s}
  let N : L → Type := fun x =>
    {y : E.finiteOccurrences //
      finitePairCost (D.finitePoint x.1.1) (E.finitePoint y) ≤ ENNReal.ofReal (ε : ℝ)}
  letI : Fintype L := Finset.Subtype.fintype s
  have hN : ∀ x : L, Finite (N x) := by
    intro x
    exact finiteOccurrence_neighbors_finite D E ε x.1.1 x.1.2
  letI : ∀ x : L, Finite (N x) := hN
  letI : ∀ x : L, Fintype (N x) := fun x => Fintype.ofFinite (N x)
  let SigmaN := Σ x : L, N x
  letI : Fintype SigmaN := inferInstance
  let f : SigmaN → D.finiteOccurrences × E.finiteOccurrences :=
    fun q => (q.1.1.1, q.2.1)
  have hImage : (Set.image f (Set.univ : Set SigmaN)).Finite := Set.finite_univ.image f
  have heq : finiteSourceCandidates D E ε s = Set.image f Set.univ := by
    ext e
    constructor
    · rintro ⟨x, hx, hfirst, hcost⟩
      rcases e with ⟨a, b⟩
      simp only [Prod.mk.injEq] at hfirst
      subst a
      refine ⟨⟨⟨x, hx⟩, ⟨b, ?_⟩⟩, Set.mem_univ _, ?_⟩
      · exact hcost
      · rfl
    · rintro ⟨q, -, hEq⟩
      rcases q with ⟨x, y⟩
      have hfirst := congrArg Prod.fst hEq
      have hsecond := congrArg Prod.snd hEq
      rcases e with ⟨a, b⟩
      simp only [Prod.mk.injEq] at hfirst hsecond
      subst a
      subst b
      exact ⟨x.1, x.2, rfl, y.2⟩
  rw [heq]
  exact hImage

private theorem finite_targetCandidates_finite
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (s : Finset (LongFiniteOccurrence E ε)) :
    (finiteTargetCandidates D E ε s).Finite := by
  classical
  let L := {y : LongFiniteOccurrence E ε // y ∈ s}
  let N : L → Type := fun y =>
    {x : D.finiteOccurrences //
      finitePairCost (D.finitePoint x) (E.finitePoint y.1.1) ≤ ENNReal.ofReal (ε : ℝ)}
  letI : Fintype L := Finset.Subtype.fintype s
  have hN : ∀ y : L, Finite (N y) := by
    intro y
    let Rev := {x : D.finiteOccurrences //
      finitePairCost (E.finitePoint y.1.1) (D.finitePoint x) ≤ ENNReal.ofReal (ε : ℝ)}
    let f : Rev → N y := fun x => ⟨x.1, by
      simpa only [finitePairCost_comm] using x.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x z h
        apply Subtype.ext
        simpa [f] using congrArg Subtype.val h
      · intro x
        exact ⟨⟨x.1, by simpa only [finitePairCost_comm] using x.2⟩, rfl⟩
    letI : Finite Rev := finiteOccurrence_neighbors_finite E D ε y.1.1 y.1.2
    exact Finite.of_equiv Rev (Equiv.ofBijective f hf)
  letI : ∀ y : L, Finite (N y) := hN
  letI : ∀ y : L, Fintype (N y) := fun y => Fintype.ofFinite (N y)
  let SigmaN := Σ y : L, N y
  letI : Fintype SigmaN := inferInstance
  let f : SigmaN → D.finiteOccurrences × E.finiteOccurrences :=
    fun q => (q.2.1, q.1.1.1)
  have hImage : (Set.image f (Set.univ : Set SigmaN)).Finite := Set.finite_univ.image f
  have heq : finiteTargetCandidates D E ε s = Set.image f Set.univ := by
    ext e
    constructor
    · rintro ⟨y, hy, hsecond, hcost⟩
      rcases e with ⟨a, b⟩
      simp only [Prod.mk.injEq] at hsecond
      subst b
      refine ⟨⟨⟨y, hy⟩, ⟨a, ?_⟩⟩, Set.mem_univ _, ?_⟩
      · exact hcost
      · rfl
    · rintro ⟨q, -, hEq⟩
      rcases q with ⟨y, x⟩
      have hfirst := congrArg Prod.fst hEq
      have hsecond := congrArg Prod.snd hEq
      rcases e with ⟨a, b⟩
      simp only [Prod.mk.injEq] at hfirst hsecond
      subst a
      subst b
      exact ⟨y.1, y.2, rfl, x.2⟩
  rw [heq]
  exact hImage

private theorem finite_essentialSourceCandidates_finite
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (s : Finset D.essentialOccurrences) :
    (essentialSourceCandidates D E ε s).Finite := by
  classical
  let L := {x : D.essentialOccurrences // x ∈ s}
  let N : L → Type := fun x =>
    {y : E.essentialOccurrences //
      essentialPairCost (D.essentialBirth x.1) (E.essentialBirth y) ≤ ENNReal.ofReal (ε : ℝ)}
  letI : Fintype L := Finset.Subtype.fintype s
  have hN : ∀ x : L, Finite (N x) := by
    intro x
    exact essentialOccurrence_neighbors_finite D E ε x.1
  letI : ∀ x : L, Finite (N x) := hN
  letI : ∀ x : L, Fintype (N x) := fun x => Fintype.ofFinite (N x)
  let SigmaN := Σ x : L, N x
  letI : Fintype SigmaN := inferInstance
  let f : SigmaN → D.essentialOccurrences × E.essentialOccurrences :=
    fun q => (q.1.1, q.2.1)
  have hImage : (Set.image f (Set.univ : Set SigmaN)).Finite := Set.finite_univ.image f
  have heq : essentialSourceCandidates D E ε s = Set.image f Set.univ := by
    ext e
    constructor
    · rintro ⟨x, hx, hfirst, hcost⟩
      rcases e with ⟨a, b⟩
      simp only [Prod.mk.injEq] at hfirst
      subst a
      refine ⟨⟨⟨x, hx⟩, ⟨b, ?_⟩⟩, Set.mem_univ _, ?_⟩
      · exact hcost
      · rfl
    · rintro ⟨q, -, hEq⟩
      rcases q with ⟨x, y⟩
      have hfirst := congrArg Prod.fst hEq
      have hsecond := congrArg Prod.snd hEq
      rcases e with ⟨a, b⟩
      simp only [Prod.mk.injEq] at hfirst hsecond
      subst a
      subst b
      exact ⟨x.1, x.2, rfl, y.2⟩
  rw [heq]
  exact hImage

private theorem finite_essentialTargetCandidates_finite
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (s : Finset E.essentialOccurrences) :
    (essentialTargetCandidates D E ε s).Finite := by
  classical
  let L := {y : E.essentialOccurrences // y ∈ s}
  let N : L → Type := fun y =>
    {x : D.essentialOccurrences //
      essentialPairCost (D.essentialBirth x) (E.essentialBirth y.1) ≤ ENNReal.ofReal (ε : ℝ)}
  letI : Fintype L := Finset.Subtype.fintype s
  have hN : ∀ y : L, Finite (N y) := by
    intro y
    let Rev := {x : D.essentialOccurrences //
      essentialPairCost (E.essentialBirth y.1) (D.essentialBirth x) ≤ ENNReal.ofReal (ε : ℝ)}
    let f : Rev → N y := fun x => ⟨x.1, by
      simpa only [essentialPairCost_comm] using x.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x z h
        apply Subtype.ext
        simpa [f] using congrArg Subtype.val h
      · intro x
        exact ⟨⟨x.1, by simpa only [essentialPairCost_comm] using x.2⟩, rfl⟩
    letI : Finite Rev := essentialOccurrence_neighbors_finite E D ε y.1
    exact Finite.of_equiv Rev (Equiv.ofBijective f hf)
  letI : ∀ y : L, Finite (N y) := hN
  letI : ∀ y : L, Fintype (N y) := fun y => Fintype.ofFinite (N y)
  let SigmaN := Σ y : L, N y
  letI : Fintype SigmaN := inferInstance
  let f : SigmaN → D.essentialOccurrences × E.essentialOccurrences :=
    fun q => (q.2.1, q.1.1)
  have hImage : (Set.image f (Set.univ : Set SigmaN)).Finite := Set.finite_univ.image f
  have heq : essentialTargetCandidates D E ε s = Set.image f Set.univ := by
    ext e
    constructor
    · rintro ⟨y, hy, hsecond, hcost⟩
      rcases e with ⟨a, b⟩
      simp only [Prod.mk.injEq] at hsecond
      subst b
      refine ⟨⟨⟨y, hy⟩, ⟨a, ?_⟩⟩, Set.mem_univ _, ?_⟩
      · exact hcost
      · rfl
    · rintro ⟨q, -, hEq⟩
      rcases q with ⟨y, x⟩
      have hfirst := congrArg Prod.fst hEq
      have hsecond := congrArg Prod.snd hEq
      rcases e with ⟨a, b⟩
      simp only [Prod.mk.injEq] at hfirst hsecond
      subst a
      subst b
      exact ⟨y.1, y.2, rfl, x.2⟩
  rw [heq]
  exact hImage

private theorem finiteCandidates_finite
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (I : MatchingIndex D E ε) : (finiteCandidates D E ε I).Finite := by
  exact (finite_sourceCandidates_finite D E ε I.1.1).union
    (finite_targetCandidates_finite D E ε I.1.2)

private theorem essentialCandidates_finite
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (I : MatchingIndex D E ε) : (essentialCandidates D E ε I).Finite := by
  exact (finite_essentialSourceCandidates_finite D E ε I.2.1).union
    (finite_essentialTargetCandidates_finite D E ε I.2.2)

private theorem finiteCandidates_mono
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    {I J : MatchingIndex D E ε} (hIJ : I ≤ J) :
    finiteCandidates D E ε I ⊆ finiteCandidates D E ε J := by
  intro e he
  rcases Set.mem_or_mem_of_mem_union he with hs | ht
  · left
    rcases hs with ⟨x, hx, hEq, hcost⟩
    rcases e with ⟨a, b⟩
    simp only [Prod.mk.injEq] at hEq
    subst a
    exact ⟨x, hIJ.1.1 hx, rfl, hcost⟩
  · right
    rcases ht with ⟨y, hy, hEq, hcost⟩
    rcases e with ⟨a, b⟩
    simp only [Prod.mk.injEq] at hEq
    subst b
    exact ⟨y, hIJ.1.2 hy, rfl, hcost⟩

private theorem essentialCandidates_mono
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    {I J : MatchingIndex D E ε} (hIJ : I ≤ J) :
    essentialCandidates D E ε I ⊆ essentialCandidates D E ε J := by
  intro e he
  rcases Set.mem_or_mem_of_mem_union he with hs | ht
  · left
    rcases hs with ⟨x, hx, hEq, hcost⟩
    rcases e with ⟨a, b⟩
    simp only [Prod.mk.injEq] at hEq
    subst a
    exact ⟨x, hIJ.2.1 hx, rfl, hcost⟩
  · right
    rcases ht with ⟨y, hy, hEq, hcost⟩
    rcases e with ⟨a, b⟩
    simp only [Prod.mk.injEq] at hEq
    subst b
    exact ⟨y, hIJ.2.2 hy, rfl, hcost⟩

private theorem finiteCandidates_cost
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    {I : MatchingIndex D E ε} {e : D.finiteOccurrences × E.finiteOccurrences}
    (he : e ∈ finiteCandidates D E ε I) :
    finitePairCost (D.finitePoint e.1) (E.finitePoint e.2) ≤ ENNReal.ofReal (ε : ℝ) := by
  rcases Set.mem_or_mem_of_mem_union he with hs | ht
  · rcases hs with ⟨x, hx, hEq, hcost⟩
    exact hcost
  · rcases ht with ⟨y, hy, hEq, hcost⟩
    exact hcost

private theorem essentialCandidates_cost
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    {I : MatchingIndex D E ε} {e : D.essentialOccurrences × E.essentialOccurrences}
    (he : e ∈ essentialCandidates D E ε I) :
    essentialPairCost (D.essentialBirth e.1) (E.essentialBirth e.2) ≤
      ENNReal.ofReal (ε : ℝ) := by
  rcases Set.mem_or_mem_of_mem_union he with hs | ht
  · rcases hs with ⟨x, hx, hEq, hcost⟩
    exact hcost
  · rcases ht with ⟨y, hy, hEq, hcost⟩
    exact hcost

private structure LocalMatchingStateProperty
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (I : MatchingIndex D E ε)
    (F : Finset (D.finiteOccurrences × E.finiteOccurrences))
    (G : Finset (D.essentialOccurrences × E.essentialOccurrences)) : Prop where
  finiteCandidates : ∀ e ∈ F, e ∈ finiteCandidates D E ε I
  finiteRightInjective : ∀ a b c, (a, b) ∈ F → (a, c) ∈ F → b = c
  finiteLeftInjective : ∀ a b c, (a, b) ∈ F → (c, b) ∈ F → a = c
  finiteLeftCovered : ∀ x ∈ I.1.1, ∃ y, (x.1, y) ∈ F
  finiteRightCovered : ∀ y ∈ I.1.2, ∃ x, (x, y.1) ∈ F
  essentialCandidates : ∀ e ∈ G, e ∈ essentialCandidates D E ε I
  essentialRightInjective : ∀ a b c, (a, b) ∈ G → (a, c) ∈ G → b = c
  essentialLeftInjective : ∀ a b c, (a, b) ∈ G → (c, b) ∈ G → a = c
  essentialLeftCovered : ∀ x ∈ I.2.1, ∃ y, (x, y) ∈ G
  essentialRightCovered : ∀ y ∈ I.2.2, ∃ x, (x, y) ∈ G

private def LocalMatchingState
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (I : MatchingIndex D E ε) :=
  {p : Finset (D.finiteOccurrences × E.finiteOccurrences) ×
      Finset (D.essentialOccurrences × E.essentialOccurrences) //
    LocalMatchingStateProperty D E ε I p.1 p.2}

private def restrictLocalMatchingState
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    {I J : MatchingIndex D E ε} (hIJ : I ≤ J)
    (s : LocalMatchingState D E ε J) : LocalMatchingState D E ε I := by
  classical
  let F := s.1.1.filter (fun e => decide (e ∈ finiteCandidates D E ε I))
  let G := s.1.2.filter (fun e => decide (e ∈ essentialCandidates D E ε I))
  refine ⟨(F, G), ?_⟩
  constructor
  · intro e he
    simpa only [decide_eq_true_eq] using (Finset.mem_filter.mp he).2
  · intro a b c hab hac
    exact s.2.finiteRightInjective a b c
      (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hac).1
  · intro a b c hab hac
    exact s.2.finiteLeftInjective a b c
      (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hac).1
  · intro x hx
    obtain ⟨y, hxy⟩ := s.2.finiteLeftCovered x (hIJ.1.1 hx)
    refine ⟨y, Finset.mem_filter.mpr ⟨hxy, ?_⟩⟩
    have hcost := finiteCandidates_cost (s.2.finiteCandidates (x.1, y) hxy)
    have hcand : (x.1, y) ∈ finiteCandidates D E ε I := by
      apply Set.mem_union_left
      exact ⟨x, hx, rfl, hcost⟩
    simpa only [decide_eq_true_eq] using hcand
  · intro y hy
    obtain ⟨x, hxy⟩ := s.2.finiteRightCovered y (hIJ.1.2 hy)
    refine ⟨x, Finset.mem_filter.mpr ⟨hxy, ?_⟩⟩
    have hcost := finiteCandidates_cost (s.2.finiteCandidates (x, y.1) hxy)
    have hcand : (x, y.1) ∈ finiteCandidates D E ε I := by
      apply Set.mem_union_right
      exact ⟨y, hy, rfl, hcost⟩
    simpa only [decide_eq_true_eq] using hcand
  · intro e he
    simpa only [decide_eq_true_eq] using (Finset.mem_filter.mp he).2
  · intro a b c hab hac
    exact s.2.essentialRightInjective a b c
      (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hac).1
  · intro a b c hab hac
    exact s.2.essentialLeftInjective a b c
      (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hac).1
  · intro x hx
    obtain ⟨y, hxy⟩ := s.2.essentialLeftCovered x (hIJ.2.1 hx)
    refine ⟨y, Finset.mem_filter.mpr ⟨hxy, ?_⟩⟩
    have hcost := essentialCandidates_cost (s.2.essentialCandidates (x, y) hxy)
    have hcand : (x, y) ∈ essentialCandidates D E ε I := by
      apply Set.mem_union_left
      exact ⟨x, hx, rfl, hcost⟩
    simpa only [decide_eq_true_eq] using hcand
  · intro y hy
    obtain ⟨x, hxy⟩ := s.2.essentialRightCovered y (hIJ.2.2 hy)
    refine ⟨x, Finset.mem_filter.mpr ⟨hxy, ?_⟩⟩
    have hcost := essentialCandidates_cost (s.2.essentialCandidates (x, y) hxy)
    have hcand : (x, y) ∈ essentialCandidates D E ε I := by
      apply Set.mem_union_right
      exact ⟨y, hy, rfl, hcost⟩
    simpa only [decide_eq_true_eq] using hcand

private theorem restrictLocalMatchingState_id
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    {I : MatchingIndex D E ε} (s : LocalMatchingState D E ε I) :
    restrictLocalMatchingState (le_rfl : I ≤ I) s = s := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · apply Finset.ext
    intro e
    simp only [restrictLocalMatchingState, Finset.mem_filter, decide_eq_true_eq]
    constructor
    · exact And.left
    · intro he
      exact ⟨he, s.2.finiteCandidates e he⟩
  · apply Finset.ext
    intro e
    simp only [restrictLocalMatchingState, Finset.mem_filter, decide_eq_true_eq]
    constructor
    · exact And.left
    · intro he
      exact ⟨he, s.2.essentialCandidates e he⟩

private theorem restrictLocalMatchingState_comp
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    {I J K : MatchingIndex D E ε} (hIJ : I ≤ J) (hJK : J ≤ K)
    (s : LocalMatchingState D E ε K) :
    restrictLocalMatchingState hIJ (restrictLocalMatchingState hJK s) =
      restrictLocalMatchingState (le_trans hIJ hJK) s := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · apply Finset.ext
    intro e
    simp only [restrictLocalMatchingState, Finset.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨he, hJ⟩, hI⟩
      exact ⟨he, hI⟩
    · rintro ⟨he, hI⟩
      exact ⟨⟨he, finiteCandidates_mono hIJ hI⟩, hI⟩
  · apply Finset.ext
    intro e
    simp only [restrictLocalMatchingState, Finset.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨he, hJ⟩, hI⟩
      exact ⟨he, hI⟩
    · rintro ⟨he, hI⟩
      exact ⟨⟨he, essentialCandidates_mono hIJ hI⟩, hI⟩

private def encodeFinset {α : Type*} [DecidableEq α] (C : Set α) [DecidablePred C]
    (s : Finset α)
    (h : ∀ a ∈ s, a ∈ C) : Finset {a // a ∈ C} :=
  s.subtype C

private theorem map_encodeFinset {α : Type*} [DecidableEq α] (C : Set α)
    [DecidablePred C]
    (s : Finset α) (h : ∀ a ∈ s, a ∈ C) :
    (encodeFinset C s h).map (Function.Embedding.subtype C) = s := by
  rw [encodeFinset]
  exact Finset.subtype_map_of_mem h

private theorem finite_localMatchingState
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (I : MatchingIndex D E ε) : Finite (LocalMatchingState D E ε I) := by
  classical
  let CF := {e : D.finiteOccurrences × E.finiteOccurrences //
    e ∈ finiteCandidates D E ε I}
  let CG := {e : D.essentialOccurrences × E.essentialOccurrences //
    e ∈ essentialCandidates D E ε I}
  letI : Fintype CF := (finiteCandidates_finite D E ε I).fintype
  letI : Fintype CG := (essentialCandidates_finite D E ε I).fintype
  letI : DecidablePred (finiteCandidates D E ε I) :=
    Classical.decPred (finiteCandidates D E ε I)
  letI : DecidablePred (essentialCandidates D E ε I) :=
    Classical.decPred (essentialCandidates D E ε I)
  let encode : LocalMatchingState D E ε I → Finset CF × Finset CG := fun s =>
    (encodeFinset _ s.1.1 s.2.finiteCandidates,
      encodeFinset _ s.1.2 s.2.essentialCandidates)
  have hencode : Function.Injective encode := by
    intro s t h
    apply Subtype.ext
    apply Prod.ext
    · have h' := congrArg (fun p : Finset CF × Finset CG =>
          p.1.map (Function.Embedding.subtype _)) h
      have hs := map_encodeFinset (finiteCandidates D E ε I) s.1.1
        s.2.finiteCandidates
      have ht := map_encodeFinset (finiteCandidates D E ε I) t.1.1
        t.2.finiteCandidates
      exact hs.symm.trans (h'.trans ht)
    · have h' := congrArg (fun p : Finset CF × Finset CG =>
          p.2.map (Function.Embedding.subtype _)) h
      have hs := map_encodeFinset (essentialCandidates D E ε I) s.1.2
        s.2.essentialCandidates
      have ht := map_encodeFinset (essentialCandidates D E ε I) t.1.2
        t.2.essentialCandidates
      exact hs.symm.trans (h'.trans ht)
  exact Finite.of_injective encode hencode

private theorem localMatchingState_nonempty
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (i : RealInterleaving ε M N) (hM : M.QTame) (hN : N.QTame)
    (I : MatchingIndex (LocallyFiniteDecoratedDiagram.ofQModule hM)
      (LocallyFiniteDecoratedDiagram.ofQModule hN) ε) :
    Nonempty (LocalMatchingState (LocallyFiniteDecoratedDiagram.ofQModule hM)
      (LocallyFiniteDecoratedDiagram.ofQModule hN) ε I) := by
  classical
  let D : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hM
  let E : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hN
  let F_M := I.1.1.image Subtype.val
  let F_N := I.1.2.image Subtype.val
  have hLongM : ∀ x ∈ F_M, 2 * (ε : ℝ) < (D.finitePoint x).2 - (D.finitePoint x).1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    exact z.2
  have hLongN : ∀ x ∈ F_N, 2 * (ε : ℝ) < (E.finitePoint x).2 - (E.finitePoint x).1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    exact z.2
  obtain ⟨FEdges, hFR, hFL, hFC, hFCoverL, hFCoverR,
      EEdges, hER, hEL, hEC, hECoverL, hECoverR⟩ :=
    i.exists_finite_saturating_matching hM hN F_M F_N hLongM hLongN I.2.1 I.2.2
  let F := FEdges.filter (fun e => decide (e ∈ finiteCandidates D E ε I))
  let G := EEdges.filter (fun e => decide (e ∈ essentialCandidates D E ε I))
  refine ⟨⟨(F, G), ?_⟩⟩
  constructor
  · intro e he
    simpa only [decide_eq_true_eq, D, E] using (Finset.mem_filter.mp he).2
  · intro a b c hab hac
    exact hFR a b c (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hac).1
  · intro a b c hab hac
    exact hFL a b c (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hac).1
  · intro x hx
    have hxFM : x.1 ∈ F_M := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hxy⟩ := hFCoverL x.1 hxFM
    refine ⟨y, Finset.mem_filter.mpr ⟨hxy, ?_⟩⟩
    have hCandidate : (x.1, y) ∈ finiteCandidates D E ε I := by
      apply Set.mem_union_left
      exact ⟨x, hx, rfl, hFC x.1 y hxy⟩
    simpa only [decide_eq_true_eq] using hCandidate
  · intro y hy
    have hyFN : y.1 ∈ F_N := Finset.mem_image.mpr ⟨y, hy, rfl⟩
    obtain ⟨x, hxy⟩ := hFCoverR y.1 hyFN
    refine ⟨x, Finset.mem_filter.mpr ⟨hxy, ?_⟩⟩
    have hCandidate : (x, y.1) ∈ finiteCandidates D E ε I := by
      apply Set.mem_union_right
      exact ⟨y, hy, rfl, hFC x y.1 hxy⟩
    simpa only [decide_eq_true_eq] using hCandidate
  · intro e he
    simpa only [decide_eq_true_eq, D, E] using (Finset.mem_filter.mp he).2
  · intro a b c hab hac
    exact hER a b c (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hac).1
  · intro a b c hab hac
    exact hEL a b c (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hac).1
  · intro x hx
    obtain ⟨y, hxy⟩ := hECoverL x hx
    refine ⟨y, Finset.mem_filter.mpr ⟨hxy, ?_⟩⟩
    have hCandidate : (x, y) ∈ essentialCandidates D E ε I := by
      apply Set.mem_union_left
      exact ⟨x, hx, rfl, hEC x y hxy⟩
    simpa only [decide_eq_true_eq] using hCandidate
  · intro y hy
    obtain ⟨x, hxy⟩ := hECoverR y hy
    refine ⟨x, Finset.mem_filter.mpr ⟨hxy, ?_⟩⟩
    have hCandidate : (x, y) ∈ essentialCandidates D E ε I := by
      apply Set.mem_union_right
      exact ⟨y, hy, rfl, hEC x y hxy⟩
    simpa only [decide_eq_true_eq] using hCandidate

private def matchingStateFunctor (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0) :
    (MatchingIndex D E ε)ᵒᵖ ⥤ Type _ where
  obj I := LocalMatchingState D E ε I.unop
  map {I J} (f : I ⟶ J) := ↾(fun (s : LocalMatchingState D E ε I.unop) =>
    restrictLocalMatchingState (leOfHom f.unop : J.unop ≤ I.unop) s
  )
  map_id := by
    intro I
    ext s
    exact restrictLocalMatchingState_id s
  map_comp := by
    intro I J K f g
    ext s
    exact (restrictLocalMatchingState_comp
      (leOfHom g.unop) (leOfHom f.unop) s).symm

private structure CoherentMatchingStates (D E : LocallyFiniteDecoratedDiagram)
    (ε : ℝ≥0) where
  state : ∀ I : MatchingIndex D E ε, LocalMatchingState D E ε I
  coherent : ∀ {I J : MatchingIndex D E ε} (hIJ : I ≤ J),
    restrictLocalMatchingState hIJ (state J) = state I

private theorem exists_qModule_coherent_matchingStates
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (i : RealInterleaving ε M N) (hM : M.QTame) (hN : N.QTame) :
    Nonempty (CoherentMatchingStates (LocallyFiniteDecoratedDiagram.ofQModule hM)
      (LocallyFiniteDecoratedDiagram.ofQModule hN) ε) := by
  classical
  let D : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hM
  let E : LocallyFiniteDecoratedDiagram := LocallyFiniteDecoratedDiagram.ofQModule hN
  let F := matchingStateFunctor D E ε
  letI : ∀ j : (MatchingIndex D E ε)ᵒᵖ, Finite (F.obj j) := by
    intro j
    simpa [F, matchingStateFunctor] using finite_localMatchingState D E ε j.unop
  letI : ∀ j : (MatchingIndex D E ε)ᵒᵖ, Nonempty (F.obj j) := by
    intro j
    simpa [F, D, E, matchingStateFunctor] using localMatchingState_nonempty i hM hN j.unop
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨{ state := fun I => u (op I), coherent := ?_ }⟩
  intro I J hIJ
  have hsec := hu (homOfLE hIJ).op
  change restrictLocalMatchingState hIJ (u (op J)) = u (op I) at hsec
  exact hsec

private def sectionFiniteEdge (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (u : CoherentMatchingStates D E ε)
    (x : D.finiteOccurrences) (y : E.finiteOccurrences) : Prop :=
  ∃ I : MatchingIndex D E ε,
    (x, y) ∈ (u.state I).1.1 ∧
      finitePairCost (D.finitePoint x) (E.finitePoint y) ≤ ENNReal.ofReal (ε : ℝ)

private def sectionEssentialEdge (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (u : CoherentMatchingStates D E ε)
    (x : D.essentialOccurrences) (y : E.essentialOccurrences) : Prop :=
  ∃ I : MatchingIndex D E ε,
    (x, y) ∈ (u.state I).1.2 ∧
      essentialPairCost (D.essentialBirth x) (E.essentialBirth y) ≤ ENNReal.ofReal (ε : ℝ)

private theorem section_finiteEdge_mono
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    {I J : MatchingIndex D E ε} (hIJ : I ≤ J)
    {x : D.finiteOccurrences} {y : E.finiteOccurrences}
    (he : (x, y) ∈ (u.state I).1.1) :
    (x, y) ∈ (u.state J).1.1 := by
  have hsec := u.coherent hIJ
  have hm : (x, y) ∈ (restrictLocalMatchingState hIJ (u.state J)).1.1 := by
    rw [hsec]
    exact he
  exact (Finset.mem_filter.mp hm).1

private theorem section_essentialEdge_mono
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    {I J : MatchingIndex D E ε} (hIJ : I ≤ J)
    {x : D.essentialOccurrences} {y : E.essentialOccurrences}
    (he : (x, y) ∈ (u.state I).1.2) :
    (x, y) ∈ (u.state J).1.2 := by
  have hsec := u.coherent hIJ
  have hm : (x, y) ∈ (restrictLocalMatchingState hIJ (u.state J)).1.2 := by
    rw [hsec]
    exact he
  exact (Finset.mem_filter.mp hm).1

private theorem sectionFiniteEdge_right_injective
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    {x : D.finiteOccurrences} {y z : E.finiteOccurrences}
    (hy : sectionFiniteEdge D E ε u x y)
    (hz : sectionFiniteEdge D E ε u x z) : y = z := by
  rcases hy with ⟨I, hy, _⟩
  rcases hz with ⟨J, hz, _⟩
  let K := I ⊔ J
  have hyK := section_finiteEdge_mono u (le_sup_left : I ≤ K) hy
  have hzK := section_finiteEdge_mono u (le_sup_right : J ≤ K) hz
  exact (u.state K).property.finiteRightInjective x y z hyK hzK

private theorem sectionFiniteEdge_left_injective
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    {x z : D.finiteOccurrences} {y : E.finiteOccurrences}
    (hx : sectionFiniteEdge D E ε u x y)
    (hz : sectionFiniteEdge D E ε u z y) : x = z := by
  rcases hx with ⟨I, hx, _⟩
  rcases hz with ⟨J, hz, _⟩
  let K := I ⊔ J
  have hxK := section_finiteEdge_mono u (le_sup_left : I ≤ K) hx
  have hzK := section_finiteEdge_mono u (le_sup_right : J ≤ K) hz
  exact (u.state K).property.finiteLeftInjective x y z hxK hzK

private theorem sectionEssentialEdge_right_injective
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    {x : D.essentialOccurrences} {y z : E.essentialOccurrences}
    (hy : sectionEssentialEdge D E ε u x y)
    (hz : sectionEssentialEdge D E ε u x z) : y = z := by
  rcases hy with ⟨I, hy, _⟩
  rcases hz with ⟨J, hz, _⟩
  let K := I ⊔ J
  have hyK := section_essentialEdge_mono u (le_sup_left : I ≤ K) hy
  have hzK := section_essentialEdge_mono u (le_sup_right : J ≤ K) hz
  exact (u.state K).property.essentialRightInjective x y z hyK hzK

private theorem sectionEssentialEdge_left_injective
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    {x z : D.essentialOccurrences} {y : E.essentialOccurrences}
    (hx : sectionEssentialEdge D E ε u x y)
    (hz : sectionEssentialEdge D E ε u z y) : x = z := by
  rcases hx with ⟨I, hx, _⟩
  rcases hz with ⟨J, hz, _⟩
  let K := I ⊔ J
  have hxK := section_essentialEdge_mono u (le_sup_left : I ≤ K) hx
  have hzK := section_essentialEdge_mono u (le_sup_right : J ≤ K) hz
  exact (u.state K).property.essentialLeftInjective x y z hxK hzK

private theorem sectionFiniteEdge_cost
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    {x : D.finiteOccurrences} {y : E.finiteOccurrences}
    (hxy : sectionFiniteEdge D E ε u x y) :
    finitePairCost (D.finitePoint x) (E.finitePoint y) ≤ ENNReal.ofReal (ε : ℝ) := by
  exact hxy.choose_spec.2

set_option maxHeartbeats 500000 in
private theorem sectionEssentialEdge_cost
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    {x : D.essentialOccurrences} {y : E.essentialOccurrences}
    (hxy : sectionEssentialEdge D E ε u x y) :
    essentialPairCost (D.essentialBirth x) (E.essentialBirth y) ≤
      ENNReal.ofReal (ε : ℝ) := by
  exact hxy.choose_spec.2

set_option maxHeartbeats 1500000 in
private theorem sectionFiniteEdge_left_covered
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε) (x : LongFiniteOccurrence D ε) :
    ∃ y : E.finiteOccurrences, sectionFiniteEdge D E ε u x.1 y := by
  classical
  let I : MatchingIndex D E ε := (({x}, ∅), (∅, ∅))
  have hx : x ∈ I.1.1 := by simp [I]
  obtain ⟨y, hxy⟩ := (u.state I).property.finiteLeftCovered x hx
  refine ⟨y, I, hxy, ?_⟩
  exact finiteCandidates_cost ((u.state I).property.finiteCandidates (x.1, y) hxy)

set_option maxHeartbeats 1500000 in
private theorem sectionFiniteEdge_right_covered
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε) (y : LongFiniteOccurrence E ε) :
    ∃ x : D.finiteOccurrences, sectionFiniteEdge D E ε u x y.1 := by
  classical
  let I : MatchingIndex D E ε := ((∅, {y}), (∅, ∅))
  have hy : y ∈ I.1.2 := by simp [I]
  obtain ⟨x, hxy⟩ := (u.state I).property.finiteRightCovered y hy
  refine ⟨x, I, hxy, ?_⟩
  exact finiteCandidates_cost ((u.state I).property.finiteCandidates (x, y.1) hxy)

set_option maxHeartbeats 500000 in
private theorem sectionEssentialEdge_left_covered
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε) (x : D.essentialOccurrences) :
    ∃ y, sectionEssentialEdge D E ε u x y := by
  classical
  let I : MatchingIndex D E ε := ((∅, ∅), ({x}, ∅))
  have hx : x ∈ I.2.1 := by simp [I]
  obtain ⟨y, hxy⟩ := (u.state I).property.essentialLeftCovered x hx
  refine ⟨y, I, hxy, ?_⟩
  exact essentialCandidates_cost ((u.state I).property.essentialCandidates (x, y) hxy)

set_option maxHeartbeats 500000 in
private theorem sectionEssentialEdge_right_covered
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε) (y : E.essentialOccurrences) :
    ∃ x, sectionEssentialEdge D E ε u x y := by
  classical
  let I : MatchingIndex D E ε := ((∅, ∅), (∅, {y}))
  have hy : y ∈ I.2.2 := by simp [I]
  obtain ⟨x, hxy⟩ := (u.state I).property.essentialRightCovered y hy
  refine ⟨x, I, hxy, ?_⟩
  exact essentialCandidates_cost ((u.state I).property.essentialCandidates (x, y) hxy)

private noncomputable def sectionFiniteMap
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    (x : D.finiteOccurrences) : Option E.finiteOccurrences :=
  if h : ∃ y, sectionFiniteEdge D E ε u x y then some (Classical.choose h) else none

private theorem sectionFiniteMap_some_iff
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε)
    {x : D.finiteOccurrences} {y : E.finiteOccurrences} :
    sectionFiniteMap u x = some y ↔ sectionFiniteEdge D E ε u x y := by
  classical
  unfold sectionFiniteMap
  split_ifs with h
  · constructor
    · intro heq
      have hchoose : Classical.choose h = y := Option.some.inj heq
      subst y
      exact Classical.choose_spec h
    · intro hxy
      have hEq := sectionFiniteEdge_right_injective u (Classical.choose_spec h) hxy
      subst y
      rfl
  · constructor
    · intro heq
      simp at heq
    · intro hxy
      exact (h ⟨y, hxy⟩).elim

set_option maxHeartbeats 500000 in
private noncomputable def sectionEssentialEquiv
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε) : D.essentialOccurrences ≃ E.essentialOccurrences := by
  classical
  let f : D.essentialOccurrences → E.essentialOccurrences := fun x =>
    Classical.choose (sectionEssentialEdge_left_covered u x)
  have hf : Function.Bijective f := by
    constructor
    · intro x z hxz
      have hx := Classical.choose_spec (sectionEssentialEdge_left_covered u x)
      have hz := Classical.choose_spec (sectionEssentialEdge_left_covered u z)
      have hfEq : Classical.choose (sectionEssentialEdge_left_covered u x) =
          Classical.choose (sectionEssentialEdge_left_covered u z) := by
        simpa [f] using hxz
      have hz' : sectionEssentialEdge D E ε u z
          (Classical.choose (sectionEssentialEdge_left_covered u x)) := by
        simpa only [hfEq] using hz
      exact sectionEssentialEdge_left_injective u hx hz'
    · intro y
      obtain ⟨x, hxy⟩ := sectionEssentialEdge_right_covered u y
      refine ⟨x, ?_⟩
      have hx := Classical.choose_spec (sectionEssentialEdge_left_covered u x)
      exact sectionEssentialEdge_right_injective u hx hxy
  exact Equiv.ofBijective f hf

private noncomputable def occurrenceMatchingOfSection
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (u : CoherentMatchingStates D E ε) :
    OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences where
  finite := sectionFiniteMap u
  finite_injective := by
    intro x z y hx hz
    have hx' := (sectionFiniteMap_some_iff u).1 hx
    have hz' := (sectionFiniteMap_some_iff u).1 hz
    exact sectionFiniteEdge_left_injective u hx' hz'
  essential := sectionEssentialEquiv u

private theorem sectionEssentialEquiv_edge
    {D E : LocallyFiniteDecoratedDiagram} {ε : ℝ≥0}
    (u : CoherentMatchingStates D E ε) (x : D.essentialOccurrences) :
    sectionEssentialEdge D E ε u x (sectionEssentialEquiv u x) := by
  classical
  change sectionEssentialEdge D E ε u x
    (Classical.choose (sectionEssentialEdge_left_covered u x))
  exact Classical.choose_spec (sectionEssentialEdge_left_covered u x)

private theorem diagonalCost_le_of_length_le
    (D : LocallyFiniteDecoratedDiagram) (x : D.finiteOccurrences) {ε : ℝ≥0}
    (hLen : (D.finitePoint x).2 - (D.finitePoint x).1 ≤ 2 * (ε : ℝ)) :
    diagonalCost (D.finitePoint x) ≤ ENNReal.ofReal (ε : ℝ) := by
  unfold diagonalCost
  apply ENNReal.ofReal_le_ofReal
  have horder : (D.finitePoint x).1 < (D.finitePoint x).2 := by
    simpa [LocallyFiniteDecoratedDiagram.finitePoint] using
      D.finiteEndpointOrder x.1.1 x.1.2.1 x.1.2.2
  have hgap : 0 ≤ (D.finitePoint x).2 - (D.finitePoint x).1 := sub_nonneg.mpr horder.le
  rw [abs_of_nonneg hgap]
  linarith

set_option maxHeartbeats 500000 in
private theorem occurrenceMatchingOfSection_cost_le
    (D E : LocallyFiniteDecoratedDiagram) (ε : ℝ≥0)
    (u : CoherentMatchingStates D E ε) :
    LocallyFiniteDecoratedDiagram.matchingCost (occurrenceMatchingOfSection D E ε u) ≤
      ENNReal.ofReal (ε : ℝ) := by
  classical
  change max
    (⨆ x, match sectionFiniteMap u x with
      | some y => finitePairCost (D.finitePoint x) (E.finitePoint y)
      | none => diagonalCost (D.finitePoint x))
    (max
      (⨆ y, if ∃ x, sectionFiniteMap u x = some y then 0 else diagonalCost (E.finitePoint y))
      (⨆ x, essentialPairCost (D.essentialBirth x)
        (E.essentialBirth (sectionEssentialEquiv u x)))) ≤ ENNReal.ofReal (ε : ℝ)
  have hSource : (⨆ x, match sectionFiniteMap u x with
      | some y => finitePairCost (D.finitePoint x) (E.finitePoint y)
      | none => diagonalCost (D.finitePoint x)) ≤ ENNReal.ofReal (ε : ℝ) := by
    apply iSup_le
    intro x
    cases hm : sectionFiniteMap u x with
    | some y =>
        have hxy := (sectionFiniteMap_some_iff u).1 hm
        simpa [hm] using sectionFiniteEdge_cost u hxy
    | none =>
        have hLong : ¬ 2 * (ε : ℝ) <
            (D.finitePoint x).2 - (D.finitePoint x).1 := by
          intro h
          let xLong : LongFiniteOccurrence D ε := ⟨x, h⟩
          obtain ⟨y, hxy⟩ := sectionFiniteEdge_left_covered u xLong
          have hsome := (sectionFiniteMap_some_iff u).2 hxy
          rw [hm] at hsome
          cases hsome
        have hLen : (D.finitePoint x).2 - (D.finitePoint x).1 ≤ 2 * (ε : ℝ) :=
          le_of_not_gt hLong
        simpa [hm] using diagonalCost_le_of_length_le D x hLen
  have hTarget : (⨆ y, if ∃ x, sectionFiniteMap u x = some y then 0
      else diagonalCost (E.finitePoint y)) ≤ ENNReal.ofReal (ε : ℝ) := by
    apply iSup_le
    intro y
    by_cases hmatched : ∃ x, sectionFiniteMap u x = some y
    · simp [hmatched]
    · have hLong : ¬ 2 * (ε : ℝ) <
          (E.finitePoint y).2 - (E.finitePoint y).1 := by
        intro h
        let yLong : LongFiniteOccurrence E ε := ⟨y, h⟩
        obtain ⟨x, hxy⟩ := sectionFiniteEdge_right_covered u yLong
        exact hmatched ⟨x, (sectionFiniteMap_some_iff u).2 hxy⟩
      have hLen : (E.finitePoint y).2 - (E.finitePoint y).1 ≤ 2 * (ε : ℝ) :=
        le_of_not_gt hLong
      simpa [hmatched] using diagonalCost_le_of_length_le E y hLen
  have hEssential : (⨆ x, essentialPairCost (D.essentialBirth x)
      (E.essentialBirth (sectionEssentialEquiv u x))) ≤ ENNReal.ofReal (ε : ℝ) := by
    apply iSup_le
    intro x
    exact sectionEssentialEdge_cost u (sectionEssentialEquiv_edge u x)
  exact max_le hSource (max_le hTarget hEssential)

/-- The bottleneck distance between finite-birth decorated diagrams extracted from actual
q-tame modules is bounded by every actual real interleaving parameter. The proof obtains
one occurrence matching from finite saturation on all finite index sets; no decomposition
or global-matching hypothesis is assumed. -/
theorem qTame_bottleneck_le_of_realInterleaving
    {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}
    (i : RealInterleaving ε M N) (hM : M.QTame) (hN : N.QTame) :
    LocallyFiniteDecoratedDiagram.bottleneck
      (LocallyFiniteDecoratedDiagram.ofQModule hM)
      (LocallyFiniteDecoratedDiagram.ofQModule hN) ≤ ENNReal.ofReal (ε : ℝ) := by
  classical
  obtain ⟨u⟩ := exists_qModule_coherent_matchingStates i hM hN
  exact (iInf_le _ (occurrenceMatchingOfSection _ _ ε u)).trans
    (occurrenceMatchingOfSection_cost_le _ _ ε u)

end
end TDA.Persistence
