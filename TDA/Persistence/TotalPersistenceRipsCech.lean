import TDA.Persistence.TotalPersistence
import TDA.Persistence.FaceEndpointUniqueness
import TDA.Persistence.CechRipsAdditive
import TDA.Persistence.RipsWeightedKernel

set_option autoImplicit false

/-!
# Total-persistence bounds for finite Rips and Čech diagrams

Finite coordinates of a sublevel diagram are attained face values.  Consequently,
finite and essential coordinates of Rips diagrams lie below the carrier diameter,
and Čech coordinates lie below either an enclosing radius or the label diameter.
The face-endpoint argument gives the size-uniform bar counts needed for total
persistence, which feeds KFH18 equations (8)--(9).  KFH18 Lemma 4, its
card-independent bound, (W1), Proposition 8 and Theorem 9 are not proved here;
essential-bar vanishing in degree at least one is not claimed.
-/

universe u w

namespace TDA.Persistence

open TDA.Simplicial TDA.Filtration

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TotalFace K)]
variable {α : Type w} [LinearOrder α]
variable {f : FilterFunction K α}

private theorem finitePart_mem_points {α : Type w} [LinearOrder α]
    {D : Diagram α} {x : α × α} (hx : x ∈ finitePart D.points) :
    (x.1, (x.2 : WithTop α)) ∈ D.points := by
  rw [← parts_reconstruct D.points]
  exact Multiset.mem_add.mpr <|
    Or.inl (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)

private theorem essentialPart_mem_points {α : Type w} [LinearOrder α]
    {D : Diagram α} {b : α} (hb : b ∈ essentialPart D.points) :
    (b, (⊤ : WithTop α)) ∈ D.points := by
  rw [← parts_reconstruct D.points]
  exact Multiset.mem_add.mpr <|
    Or.inr (Multiset.mem_map.mpr ⟨b, hb, rfl⟩)

/-- Every finite birth and death coordinate is nonnegative, strictly ordered, and at most `M`
when all filter values are in `[0,M]`. -/
theorem dgm_finitePart_mem_Icc {f : FilterFunction K ℝ} {M : ℝ} (n : ℕ)
    (h0 : ∀ s, 0 ≤ f.value s) (hM : ∀ s, f.value s ≤ M) :
    ∀ x ∈ finitePart (dgm k f n).points,
      0 ≤ x.1 ∧ x.1 < x.2 ∧ x.2 ≤ M := by
  intro x hx
  obtain ⟨s, hs⟩ :=
    (TDA.Filtration.FilterFunction.mem_criticalValues f x.1).1
      (mem_criticalValues_of_mem_finitePart_dgm k f hx).1
  obtain ⟨t, ht⟩ :=
    (TDA.Filtration.FilterFunction.mem_criticalValues f x.2).1
      (mem_criticalValues_of_mem_finitePart_dgm k f hx).2
  have hpos := dgm_isPositive k f n _ (finitePart_mem_points hx)
  have hlt : x.1 < x.2 := WithTop.coe_lt_coe.mp hpos
  refine ⟨?_, hlt, ?_⟩
  · rw [← hs]
    exact h0 s
  · rw [← ht]
    exact hM t

/-- Every essential birth coordinate is in `[0,M]` when all filter values are in `[0,M]`. -/
theorem dgm_essentialPart_mem_Icc {f : FilterFunction K ℝ} {M : ℝ} (n : ℕ)
    (h0 : ∀ s, 0 ≤ f.value s) (hM : ∀ s, f.value s ≤ M) :
    ∀ b ∈ essentialPart (dgm k f n).points, 0 ≤ b ∧ b ≤ M := by
  intro b hb
  obtain ⟨s, hs⟩ :=
    (TDA.Filtration.FilterFunction.mem_criticalValues f b).1
      (mem_criticalValues_of_mem_essentialPart_dgm k f hb)
  refine ⟨?_, ?_⟩
  · rw [← hs]
    exact h0 s
  · rw [← hs]
    exact hM s

namespace Rips

open Real

variable [Fintype V]

/-- Finite and essential coordinates of a Rips diagram lie in the interval bounded by its
full-carrier diameter. -/
theorem dgm_coordinates_le_diameter (d : MetricSpace V) (n : ℕ) :
    (∀ x ∈ finitePart (dgm k (Rips.filter d) n).points,
      0 ≤ x.1 ∧ x.1 < x.2 ∧ x.2 ≤ Rips.diameter d Finset.univ) ∧
    (∀ b ∈ essentialPart (dgm k (Rips.filter d) n).points,
      0 ≤ b ∧ b ≤ Rips.diameter d Finset.univ) := by
  constructor
  · apply dgm_finitePart_mem_Icc k n
    · intro s
      simpa [Rips.filter_value] using Rips.diameter_nonneg d s.val
    · intro s
      exact Rips.filter_value_le_diameter_univ d s
  · apply dgm_essentialPart_mem_Icc k n
    · intro s
      simpa [Rips.filter_value] using Rips.diameter_nonneg d s.val
    · intro s
      exact Rips.filter_value_le_diameter_univ d s

end Rips

namespace Cech

variable {X : Type*} [PseudoMetricSpace X] [Fintype V]

/-- Finite and essential coordinates of a Čech diagram lie below the enclosing radius at `x`.
This form needs no metric on the labels. -/
theorem dgm_coordinates_le_radiusAt (p : V → X) (x : X) (n : ℕ) :
    (∀ y ∈ finitePart (dgm k (Cech.filter p) n).points,
      0 ≤ y.1 ∧ y.1 < y.2 ∧ y.2 ≤ Cech.radiusAt p x Finset.univ) ∧
    (∀ b ∈ essentialPart (dgm k (Cech.filter p) n).points,
      0 ≤ b ∧ b ≤ Cech.radiusAt p x Finset.univ) := by
  have hM (s : TotalFace (Rips.fullComplex V)) :
      (Cech.filter p).value s ≤ Cech.radiusAt p x Finset.univ := by
    exact (Cech.filter_value_le_radiusAt p s x).trans
      (Cech.radiusAt_mono p x (Finset.subset_univ _))
  constructor
  · apply dgm_finitePart_mem_Icc k n
    · intro s
      exact Cech.filter_value_nonneg p s
    · exact hM
  · apply dgm_essentialPart_mem_Icc k n
    · intro s
      exact Cech.filter_value_nonneg p s
    · exact hM

/-- The Čech coordinate bound below the label diameter, assuming the label metric realizes the
given metric on vertices. -/
theorem dgm_coordinates_le_diameter (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ) :
    (∀ y ∈ finitePart (dgm k (Cech.filter p) n).points,
      0 ≤ y.1 ∧ y.1 < y.2 ∧ y.2 ≤ Rips.diameter d Finset.univ) ∧
    (∀ b ∈ essentialPart (dgm k (Cech.filter p) n).points,
      0 ≤ b ∧ b ≤ Rips.diameter d Finset.univ) := by
  have hM (s : TotalFace (Rips.fullComplex V)) :
      (Cech.filter p).value s ≤ Rips.diameter d Finset.univ :=
    (Cech.filter_value_le_rips d p hd s).trans
      (Rips.filter_value_le_diameter_univ d s)
  constructor
  · apply dgm_finitePart_mem_Icc k n
    · intro s
      exact Cech.filter_value_nonneg p s
    · exact hM
  · apply dgm_essentialPart_mem_Icc k n
    · intro s
      exact Cech.filter_value_nonneg p s
    · exact hM

end Cech

private def faceIndexEquiv (e : CompatibleOrder f) (m : ℕ) :
    {i : Fin (faceCount K) // (e.enum i).val.card = m + 1} ≃ Face K m := by
  classical
  let toFace : {i : Fin (faceCount K) // (e.enum i).val.card = m + 1} → Face K m :=
    fun i => ⟨(e.enum i.1).val, (e.enum i.1).property, i.2⟩
  let fromFace : Face K m → {i : Fin (faceCount K) // (e.enum i).val.card = m + 1} :=
    fun s => ⟨e.enum.symm ⟨s.1, s.2.1⟩, by
      have he := e.enum.apply_symm_apply (⟨s.1, s.2.1⟩ : TotalFace K)
      simpa [he] using s.2.2⟩
  exact { toFun := toFace
          invFun := fromFace
          left_inv := by
            intro i
            apply Subtype.ext
            simp [toFace, fromFace]
          right_inv := by
            intro s
            apply Subtype.ext
            simp [toFace, fromFace] }

private theorem templatePairs_card_le_face (e : CompatibleOrder f) (n : ℕ) :
    (faceTemplatePairs k e n).card ≤ Nat.card (Face K (n + 1)) := by
  classical
  let s := faceTemplatePairs k e n
  let m := s.map Prod.snd
  let good : Fin (faceCount K) → Prop :=
    fun i => (e.enum i).val.card = n + 2
  have hm_mem : ∀ i ∈ m, i ∈ (Finset.univ : Finset (Fin (faceCount K))) := by
    simp
  have hsum := Multiset.sum_count_eq_card hm_mem
  have hcount (i : Fin (faceCount K)) : m.count i ≤ if good i then 1 else 0 := by
    have hcm : m.count i = faceDeathCount k e n i := by
      simpa [m, Multiset.count_map, Multiset.countP_eq_card_filter, eq_comm] using
        (faceTemplate_death_count k e n i)
    rw [hcm]
    by_cases hi : good i
    · simp only [if_pos hi]
      have hone := faceTemplate_endpoint_count_le_one k e i n
      have hd := faceTemplate_death_count k e n i
      omega
    · simp only [if_neg hi]
      exact (faceDeathCount_eq_zero_of_card_ne k e n i (by simpa [good] using hi)).le
  calc
    s.card = m.card := by simp [m]
    _ = ∑ i ∈ (Finset.univ : Finset (Fin (faceCount K))), m.count i := hsum.symm
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (faceCount K))), if good i then 1 else 0 := by
      exact Finset.sum_le_sum fun i hi => hcount i
    _ = (Finset.univ.filter good).card := by
      exact (Finset.card_filter _ _).symm
    _ = Nat.card {i : Fin (faceCount K) // good i} := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card (Face K (n + 1)) := by
      exact Nat.card_congr (faceIndexEquiv e (n + 1))

private theorem templateEssential_card_le_face (e : CompatibleOrder f) (n : ℕ) :
    (faceTemplateEssential k e n).card ≤ Nat.card (Face K n) := by
  classical
  let good : Fin (faceCount K) → Prop :=
    fun i => (e.enum i).val.card = n + 1
  have hs_mem : ∀ i ∈ faceTemplateEssential k e n,
      i ∈ (Finset.univ : Finset (Fin (faceCount K))) := by
    simp
  have hsum := Multiset.sum_count_eq_card hs_mem
  have hcount (i : Fin (faceCount K)) :
      (faceTemplateEssential k e n).count i ≤ if good i then 1 else 0 := by
    by_cases hi : good i
    · simp only [if_pos hi]
      exact faceTemplateEssential_count_le_one k e n i
    · simp only [if_neg hi]
      have hbirth := faceTemplate_birth_count k e n i
      have hzero := faceBirthCount_eq_zero_of_card_ne k e n i (by simpa [good] using hi)
      have hnonneg := Nat.zero_le ((faceTemplateEssential k e n).count i)
      omega
  calc
    (faceTemplateEssential k e n).card =
        ∑ i ∈ (Finset.univ : Finset (Fin (faceCount K))),
          (faceTemplateEssential k e n).count i := hsum.symm
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (faceCount K))), if good i then 1 else 0 := by
      exact Finset.sum_le_sum fun i hi => hcount i
    _ = (Finset.univ.filter good).card := by
      exact (Finset.card_filter _ _).symm
    _ = Nat.card {i : Fin (faceCount K) // good i} := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card (Face K n) := by
      exact Nat.card_congr (faceIndexEquiv e n)

private theorem finitePart_add' {β : Type*} [LinearOrder β]
    (s t : Multiset (β × WithTop β)) :
    finitePart (s + t) = finitePart s + finitePart t := by
  unfold finitePart
  exact Multiset.filterMap_add _ _ _

private theorem finitePart_finiteEmbed' {β : Type*} [LinearOrder β]
    (s : Multiset (β × β)) :
    finitePart (s.map (fun p => (p.1, (p.2 : WithTop β)))) = s := by
  unfold finitePart
  rw [Multiset.filterMap_map]
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons p s ih => simp [ih]

private theorem finitePart_essentialEmbed' {β : Type*} [LinearOrder β]
    (s : Multiset β) :
    finitePart (s.map (fun b => (b, (⊤ : WithTop β)))) = 0 := by
  unfold finitePart
  rw [Multiset.filterMap_map]
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons b s ih => simp [ih]

private theorem finitePart_dgm_card_le_templatePairs (e : CompatibleOrder f)
    (n : ℕ) :
    (finitePart (dgm k f n).points).card ≤ (faceTemplatePairs k e n).card := by
  rw [← evaluateFaceTemplate_eq_dgm k e f e.monotone n]

  change
    (finitePart
      ( (((faceTemplatePairs k e n).map (pairValues f e)).filter
          (fun p => p.1 ≠ p.2)).map
        (fun p => (p.1, (p.2 : WithTop α))) +
        ((faceTemplateEssential k e n).map (birthValue f e)).map
          (fun b => (b, (⊤ : WithTop α))))).card ≤
      (faceTemplatePairs k e n).card
  rw [finitePart_add', finitePart_finiteEmbed', finitePart_essentialEmbed']
  simp only [add_zero]
  exact
    (Multiset.card_le_card
      (Multiset.filter_le
        (p := fun p : α × α => p.1 ≠ p.2)
        ((faceTemplatePairs k e n).map (pairValues f e)))).trans
      (Multiset.card_map _ _).le

private theorem essentialPart_add' {β : Type*} [LinearOrder β]
    (s t : Multiset (β × WithTop β)) :
    essentialPart (s + t) = essentialPart s + essentialPart t := by
  unfold essentialPart
  exact Multiset.filterMap_add _ _ _

private theorem essentialPart_finiteEmbed' {β : Type*} [LinearOrder β]
    (s : Multiset (β × β)) :
    essentialPart (s.map (fun p => (p.1, (p.2 : WithTop β)))) = 0 := by
  unfold essentialPart
  rw [Multiset.filterMap_map]
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons p s ih => simp [ih]

private theorem essentialPart_essentialEmbed' {β : Type*} [LinearOrder β]
    (s : Multiset β) :
    essentialPart (s.map (fun b => (b, (⊤ : WithTop β)))) = s := by
  unfold essentialPart
  rw [Multiset.filterMap_map]
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons b s ih => simp [ih]

private theorem essentialPart_dgm_card_le_templateEssential (e : CompatibleOrder f)
    (n : ℕ) :
    (essentialPart (dgm k f n).points).card ≤ (faceTemplateEssential k e n).card := by
  rw [← evaluateFaceTemplate_eq_dgm k e f e.monotone n]
  change
    (essentialPart
      ( (((faceTemplatePairs k e n).map (pairValues f e)).filter
          (fun p => p.1 ≠ p.2)).map
        (fun p => (p.1, (p.2 : WithTop α))) +
        ((faceTemplateEssential k e n).map (birthValue f e)).map
          (fun b => (b, (⊤ : WithTop α))))).card ≤
      (faceTemplateEssential k e n).card
  rw [essentialPart_add', essentialPart_finiteEmbed', essentialPart_essentialEmbed']
  simp

/-- The finite bar count is bounded by the number of `(n+1)`-vertex faces. -/
theorem card_finitePart_dgm_le (f : FilterFunction K α) (n : ℕ) :
    (finitePart (dgm k f n).points).card ≤ Nat.card (Face K (n + 1)) := by
  obtain ⟨e⟩ := exists_compatibleOrder f
  exact (finitePart_dgm_card_le_templatePairs k e n).trans
    (templatePairs_card_le_face k e n)

/-- The essential bar count is bounded by the number of `n`-faces. -/
theorem card_essentialPart_dgm_le (f : FilterFunction K α) (n : ℕ) :
    (essentialPart (dgm k f n).points).card ≤ Nat.card (Face K n) := by
  obtain ⟨e⟩ := exists_compatibleOrder f
  exact (essentialPart_dgm_card_le_templateEssential k e n).trans
    (templateEssential_card_le_face k e n)

section FiniteVertexBounds

variable [Fintype V]

omit [LinearOrder V] in
/-- The full Rips simplex has exactly `choose N (n+1)` faces of degree `n`. -/
theorem card_face_fullComplex (n : ℕ) :
    Nat.card (Face (Rips.fullComplex V) n) =
      Nat.choose (Fintype.card V) (n + 1) := by
  classical
  let e : Face (Rips.fullComplex V) n ≃
      {s // s ∈ Finset.powersetCard (n + 1) (Finset.univ : Finset V)} :=
    { toFun := fun s => ⟨s.1, by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, s.2.2⟩⟩
      invFun := fun s => ⟨s.1, by
        have hs := Finset.mem_powersetCard.mp s.2
        have hpos : 0 < s.1.card := by omega
        exact ⟨Finset.card_pos.mp hpos, by simpa using hs.2⟩⟩
      left_inv := by intro s; apply Subtype.ext; simp
      right_inv := by intro s; apply Subtype.ext; simp }
  calc
    Nat.card (Face (Rips.fullComplex V) n) =
        Nat.card {s // s ∈ Finset.powersetCard (n + 1) (Finset.univ : Finset V)} :=
      Nat.card_congr e
    _ = (Finset.powersetCard (n + 1) (Finset.univ : Finset V)).card :=
      Nat.card_eq_finsetCard _
    _ = Nat.choose (Fintype.card V) (n + 1) := by
      simp [Finset.card_powersetCard]

/-- The Rips total-persistence bound obtained from the degree-sharp face count. -/
theorem Rips.totalPersistence_dgm_le (d : MetricSpace V) (n p : ℕ) :
    (dgm k (Rips.filter d) n).totalPersistence p ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) *
        Rips.diameter d Finset.univ ^ p := by
  let M := Rips.diameter d Finset.univ
  have hcoord : ∀ x ∈ finitePart (dgm k (Rips.filter d) n).points,
      x.1 ∈ Set.Icc 0 M ∧ x.2 ∈ Set.Icc 0 M := by
    intro x hx
    have h := (Rips.dgm_coordinates_le_diameter k d n).1 x hx
    exact ⟨⟨h.1, h.2.1.le.trans h.2.2⟩,
      ⟨h.1.trans h.2.1.le, h.2.2⟩⟩
  have htotal := totalPersistence_le_of_coordinates_mem_Icc
    (dgm k (Rips.filter d) n) p M hcoord
  have hcardNat : Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences ≤
      Nat.choose (Fintype.card V) (n + 2) := by
    rw [Multiset.card_coe]
    calc
      (finitePart (dgm k (Rips.filter d) n).points).card ≤
          Nat.card (Face (Rips.fullComplex V) (n + 1)) :=
        card_finitePart_dgm_le k (Rips.filter d) n
      _ = Nat.choose (Fintype.card V) (n + 2) := by
        simpa [Nat.add_assoc] using card_face_fullComplex (V := V) (n + 1)
  have hcard : (Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    exact_mod_cast hcardNat
  dsimp [M] at htotal ⊢
  exact htotal.trans (mul_le_mul_of_nonneg_right hcard
    (pow_nonneg (Rips.diameter_nonneg d Finset.univ) p))

/-- The Čech total-persistence bound using an ambient enclosing radius. -/
theorem Cech.totalPersistence_dgm_le_radiusAt {X : Type*} [PseudoMetricSpace X]
    (p : V → X) (x : X) (n q : ℕ) :
    (dgm k (Cech.filter p) n).totalPersistence q ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) *
        Cech.radiusAt p x Finset.univ ^ q := by
  let M := Cech.radiusAt p x Finset.univ
  have hcoord : ∀ y ∈ finitePart (dgm k (Cech.filter p) n).points,
      y.1 ∈ Set.Icc 0 M ∧ y.2 ∈ Set.Icc 0 M := by
    intro y hy
    have h := (Cech.dgm_coordinates_le_radiusAt k p x n).1 y hy
    exact ⟨⟨h.1, h.2.1.le.trans h.2.2⟩,
      ⟨h.1.trans h.2.1.le, h.2.2⟩⟩
  have htotal := totalPersistence_le_of_coordinates_mem_Icc
    (dgm k (Cech.filter p) n) q M hcoord
  have hcardNat : Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences ≤
      Nat.choose (Fintype.card V) (n + 2) := by
    rw [Multiset.card_coe]
    calc
      (finitePart (dgm k (Cech.filter p) n).points).card ≤
          Nat.card (Face (Rips.fullComplex V) (n + 1)) :=
        card_finitePart_dgm_le k (Cech.filter p) n
      _ = Nat.choose (Fintype.card V) (n + 2) := by
        simpa [Nat.add_assoc] using card_face_fullComplex (V := V) (n + 1)
  have hcard : (Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    exact_mod_cast hcardNat
  dsimp [M] at htotal ⊢
  exact htotal.trans (mul_le_mul_of_nonneg_right hcard
    (pow_nonneg (Cech.radiusAt_nonneg p x Finset.univ) q))

/-- The Čech total-persistence bound using the label diameter. -/
theorem Cech.totalPersistence_dgm_le_diameter {X : Type*} [PseudoMetricSpace X]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n q : ℕ) :
    (dgm k (Cech.filter p) n).totalPersistence q ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) *
        Rips.diameter d Finset.univ ^ q := by
  let M := Rips.diameter d Finset.univ
  have hcoord : ∀ y ∈ finitePart (dgm k (Cech.filter p) n).points,
      y.1 ∈ Set.Icc 0 M ∧ y.2 ∈ Set.Icc 0 M := by
    intro y hy
    have h := (Cech.dgm_coordinates_le_diameter k d p hd n).1 y hy
    exact ⟨⟨h.1, h.2.1.le.trans h.2.2⟩,
      ⟨h.1.trans h.2.1.le, h.2.2⟩⟩
  have htotal := totalPersistence_le_of_coordinates_mem_Icc
    (dgm k (Cech.filter p) n) q M hcoord
  have hcardNat : Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences ≤
      Nat.choose (Fintype.card V) (n + 2) := by
    rw [Multiset.card_coe]
    calc
      (finitePart (dgm k (Cech.filter p) n).points).card ≤
          Nat.card (Face (Rips.fullComplex V) (n + 1)) :=
        card_finitePart_dgm_le k (Cech.filter p) n
      _ = Nat.choose (Fintype.card V) (n + 2) := by
        simpa [Nat.add_assoc] using card_face_fullComplex (V := V) (n + 1)
  have hcard : (Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    exact_mod_cast hcardNat
  dsimp [M] at htotal ⊢
  exact htotal.trans (mul_le_mul_of_nonneg_right hcard
    (pow_nonneg (Rips.diameter_nonneg d Finset.univ) q))

end FiniteVertexBounds

namespace Rips

open Real

variable [Fintype V] {A B : ℝ}

/-- The merged Rips weighted-kernel estimate with both bar counts replaced by the full-simplex
face count. -/
theorem norm_diagramEmbedding_sub_le_choose_mul_pairwiseDiscrepancy
    (d e : MetricSpace V) (n : ℕ) (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w (dgm k (Rips.filter d) n) -
        WeightedKernel.diagramEmbedding σ w (dgm k (Rips.filter e) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        (2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ)) *
          Rips.pairwiseDiscrepancy d e := by
  have hbase := norm_diagramEmbedding_sub_le_pairwiseDiscrepancy
    k d e n σ hA hB w
  have hdNat : Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences ≤
      Nat.choose (Fintype.card V) (n + 2) := by
    rw [Multiset.card_coe]
    calc
      (finitePart (dgm k (Rips.filter d) n).points).card ≤
          Nat.card (Face (Rips.fullComplex V) (n + 1)) :=
        card_finitePart_dgm_le k (Rips.filter d) n
      _ = Nat.choose (Fintype.card V) (n + 2) := by
        simpa [Nat.add_assoc] using card_face_fullComplex (V := V) (n + 1)
  have heNat : Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences ≤
      Nat.choose (Fintype.card V) (n + 2) := by
    rw [Multiset.card_coe]
    calc
      (finitePart (dgm k (Rips.filter e) n).points).card ≤
          Nat.card (Face (Rips.fullComplex V) (n + 1)) :=
        card_finitePart_dgm_le k (Rips.filter e) n
      _ = Nat.choose (Fintype.card V) (n + 2) := by
        simpa [Nat.add_assoc] using card_face_fullComplex (V := V) (n + 1)
  have hd : (Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by exact_mod_cast hdNat
  have he : (Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by exact_mod_cast heNat
  have hcount :
      ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
        Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) ≤
        2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    calc
      ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
        Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) =
          (Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences : ℝ) +
            (Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℝ) := by
              norm_num
      _ ≤ (Nat.choose (Fintype.card V) (n + 2) : ℝ) +
            (Nat.choose (Fintype.card V) (n + 2) : ℝ) := add_le_add hd he
      _ = 2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by ring
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcount
      (WeightedKernel.stabilityConstant_nonneg σ hA hB))
    (Rips.pairwiseDiscrepancy_nonneg d e))

end Rips

end TDA.Persistence
