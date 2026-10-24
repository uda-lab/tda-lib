import TDA.Persistence.PersistenceMeasureExtendedDiagram
import TDA.Persistence.PersistenceMeasureDiagramCountability
import TDA.Persistence.DiagramBottleneck
import TDA.Persistence.DiagramBottleneckLaws
import TDA.Persistence.DecoratedCutEndpoints

/-!
# Locally finite decorated persistence diagrams and bottleneck cost

A decorated diagram records a natural multiplicity at each pair of persistence cuts.
Its positive support is countable and finite in every separated finite rectangle and
every finite-birth tail rectangle.  Finite endpoint decorations remain in the support;
the bottleneck cost uses only their real endpoints.  The essential boundary is the
actual `infinityCut` coordinate.

The module construction below uses rectangle and essential multiplicities extracted from
the persistence measure.  It assumes neither an interval decomposition nor a stability
theorem.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open Set RectangleMeasure
open scoped ENNReal

noncomputable section

local instance : DecidableEq (Cut ℝ) := Classical.decEq _
local instance : DecidableEq (Cut ℝ × Cut ℝ) := Classical.decEq _

/-- Natural-valued occurrences on decorated endpoint cuts, with the local finiteness
needed for finite rectangles and neighborhoods of the essential boundary. -/
structure LocallyFiniteDecoratedDiagram where
  multiplicity : Cut ℝ × Cut ℝ → ℕ
  countableSupport : Set.Countable {p | 0 < multiplicity p}
  finiteEndpoints : ∀ p, 0 < multiplicity p → p.2 ≠ infinityCut →
    (∃ a b, p.1 ∈ cutCell a b) ∧ (∃ c d, p.2 ∈ cutCell c d)
  finiteEndpointOrder : ∀ p, 0 < multiplicity p → p.2 ≠ infinityCut →
    cutEndpoint p.1 < cutEndpoint p.2
  essentialBirthEndpoint : ∀ birth, 0 < multiplicity (birth, infinityCut) →
    ∃ a b, birth ∈ cutCell a b
  locallyFiniteRectangle : ∀ (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d),
    Set.Finite {p | p ∈ rectangleCell a b c d ∧ 0 < multiplicity p}
  locallyFiniteTail : ∀ (a b c : ℝ) (hab : a < b) (hbc : b < c),
    Set.Finite {p | p ∈ tailRectangleCell a b c ∧ 0 < multiplicity p}

@[ext] theorem LocallyFiniteDecoratedDiagram.ext
    {D E : LocallyFiniteDecoratedDiagram}
    (h : D.multiplicity = E.multiplicity) : D = E := by
  cases D
  cases E
  simp_all

namespace LocallyFiniteDecoratedDiagram

/-- One token for each unit of multiplicity at a positive decorated point. -/
def finiteOccurrences (D : LocallyFiniteDecoratedDiagram) :=
  Σ p : {p : Cut ℝ × Cut ℝ // 0 < D.multiplicity p ∧ p.2 ≠ infinityCut},
    Fin (D.multiplicity p.1)

/-- Essential tokens live on the actual infinity boundary. -/
def essentialOccurrences (D : LocallyFiniteDecoratedDiagram) :=
  Σ birth : {b : Cut ℝ // 0 < D.multiplicity (b, infinityCut)},
    Fin (D.multiplicity (birth.1, infinityCut))

/-- Real endpoints of a finite decorated occurrence.  The two cut decorations are
retained by the occurrence, but omitted from its metric cost. -/
noncomputable def finitePoint (D : LocallyFiniteDecoratedDiagram) (o : D.finiteOccurrences) : ℝ × ℝ :=
  (cutEndpoint o.1.1.1, cutEndpoint o.1.1.2)

/-- Real birth endpoint of an essential occurrence. -/
noncomputable def essentialBirth (D : LocallyFiniteDecoratedDiagram) (o : D.essentialOccurrences) : ℝ :=
  cutEndpoint o.1.1

/-- The global cost of a possibly infinite occurrence matching.  Unlike the finite
`OccurrenceMatching.cost`, the suprema range over all occurrence tokens. -/
noncomputable def matchingCost {D E : LocallyFiniteDecoratedDiagram}
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) : ℝ≥0∞ := by
  classical
  exact max
    (⨆ i, match M.finite i with
      | some j => finitePairCost (D.finitePoint i) (E.finitePoint j)
      | none => diagonalCost (D.finitePoint i))
    (max
      (⨆ j, if ∃ i, M.finite i = some j then 0 else diagonalCost (E.finitePoint j))
      (⨆ b, essentialPairCost (D.essentialBirth b)
        (E.essentialBirth (M.essential b))))

/-- Bottleneck distance on the locally finite decorated occurrence space.  If the
essential occurrence sets admit no bijection, the empty infimum is `∞`. -/
noncomputable def bottleneck (D E : LocallyFiniteDecoratedDiagram) : ℝ≥0∞ :=
  ⨅ M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
    D.essentialOccurrences E.essentialOccurrences,
      LocallyFiniteDecoratedDiagram.matchingCost M

/-- The canonical decorated diagram of an actual q-tame real persistence module. -/
noncomputable def ofQModule {k : Type u} [Field k] {M : PModule.{u,0,w} k ℝ}
    (hM : M.QTame) : LocallyFiniteDecoratedDiagram where
  multiplicity := moduleExtendedDiagramMultiplicity M hM
  countableSupport := moduleExtendedDiagramMultiplicity_countable_support M hM
  finiteEndpoints := by
    intro p hp hInf
    have hfinite : 0 < moduleDiagramMultiplicity M hM p := by
      simpa [moduleExtendedDiagramMultiplicity, hInf] using hp
    obtain ⟨U, hU, hpU⟩ := moduleDiagramMultiplicity_visible_of_pos M hM hfinite
    rcases hU with rfl | ⟨a, b, c, d, hab, hbc, hcd, rfl⟩
    · exact hpU.elim
    · exact ⟨⟨a, b, hpU.1⟩, ⟨c, d, hpU.2⟩⟩
  essentialBirthEndpoint := by
    intro birth hb
    have hb' : 0 < moduleEssentialMultiplicity M hM birth := by
      simpa [moduleExtendedDiagramMultiplicity] using hb
    obtain ⟨U, hU, hbU⟩ := moduleEssentialMultiplicity_visible_of_pos M hM hb'
    obtain ⟨a, b, hab, rfl⟩ := hU
    exact ⟨a, b, hbU⟩
  finiteEndpointOrder := by
    intro p hp hInf
    have hfinite : 0 < moduleDiagramMultiplicity M hM p := by
      simpa [moduleExtendedDiagramMultiplicity, hInf] using hp
    obtain ⟨U, hU, hpU⟩ := moduleDiagramMultiplicity_visible_of_pos M hM hfinite
    rcases hU with rfl | ⟨a, b, c, d, hab, hbc, hcd, rfl⟩
    · exact hpU.elim
    · exact cutEndpoint_lt_of_mem_rectangleCell hbc hpU
  locallyFiniteRectangle := by
    intro a b c d hab hbc hcd
    have hf := moduleDiagramMultiplicity_locally_finite M hM
      (rectangleCell_mem_separatedRectangleCells a b c d hbc)
    apply hf.subset
    intro p hp
    refine ⟨hp.1, ?_⟩
    have hInf : p.2 ≠ infinityCut := by
      intro h
      exact infinityCut_not_mem_cutCell c d (h ▸ hp.1.2)
    simpa [moduleExtendedDiagramMultiplicity, hInf] using hp.2
  locallyFiniteTail := by
    intro a b c hab hbc
    exact moduleExtendedDiagramMultiplicity_tail_locally_finite M hM a b c hab hbc

end LocallyFiniteDecoratedDiagram

/-- The decorated endpoint of one occurrence in a finite diagram, including the
distinguished essential boundary. -/
noncomputable def diagramDecoratedPoint (p : ℝ × WithTop ℝ) : Cut ℝ × Cut ℝ :=
  (minusCut p.1, match p.2 with
  | (d : ℝ) => minusCut d
  | ⊤ => infinityCut)

/-- Embed a finite full diagram into the locally finite occurrence interface by its
actual finite-multiset occurrence counts. -/
noncomputable def Diagram.toLocallyFinite (D : Diagram ℝ) (hD : D.IsPositive) :
    LocallyFiniteDecoratedDiagram where
  multiplicity := by
    classical
    exact fun p => (D.points.map diagramDecoratedPoint).count p
  countableSupport := by
    classical
    have hfin : Set.Finite {p | 0 < (D.points.map diagramDecoratedPoint).count p} := by
      apply (D.points.map diagramDecoratedPoint).toFinset.finite_toSet.subset
      intro p hp
      exact Multiset.mem_toFinset.mpr ((Multiset.count_pos.mp hp))
    exact hfin.countable
  finiteEndpoints := by
    classical
    intro p hp hInf
    have hmem : p ∈ D.points.map diagramDecoratedPoint := Multiset.count_pos.mp hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hmem
    rcases q with ⟨birth, death⟩
    cases death with
    | top => exact (hInf rfl).elim
    | coe death => exact ⟨⟨birth - 1, birth, by simp [diagramDecoratedPoint, cutCell, minusCut]⟩,
        ⟨death - 1, death, by simp [diagramDecoratedPoint, cutCell, minusCut]⟩⟩
  essentialBirthEndpoint := by
    classical
    intro birth hp
    have hmem : (birth, infinityCut) ∈ D.points.map diagramDecoratedPoint :=
      Multiset.count_pos.mp hp
    obtain ⟨q, hq, hq'⟩ := Multiset.mem_map.mp hmem
    rcases q with ⟨b, death⟩
    cases death with
    | top =>
        have hb : birth = minusCut b := by
          simpa [diagramDecoratedPoint] using (congrArg Prod.fst hq').symm
        refine ⟨b - 1, b, ?_⟩
        rw [hb]
        simp [cutCell, minusCut]
    | coe d =>
        have hd : minusCut d = infinityCut := by
          simpa [diagramDecoratedPoint] using congrArg Prod.snd hq'
        have hmem : minusCut d ∈ cutCell (d - 1) d := by
          simp [cutCell, minusCut]
        have : infinityCut ∈ cutCell (d - 1) d := hd ▸ hmem
        exact (infinityCut_not_mem_cutCell (d - 1) d this).elim
  finiteEndpointOrder := by
    classical
    intro p hp hInf
    have hmem : p ∈ D.points.map diagramDecoratedPoint := Multiset.count_pos.mp hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hmem
    rcases q with ⟨birth, death⟩
    cases death with
    | top => exact (hInf rfl).elim
    | coe death =>
        simpa [diagramDecoratedPoint] using hD (birth, death) hq
  locallyFiniteRectangle := by
    classical
    intro a b c d hab hbc hcd
    have hfin : Set.Finite {p | 0 < (D.points.map diagramDecoratedPoint).count p} := by
      apply (D.points.map diagramDecoratedPoint).toFinset.finite_toSet.subset
      intro p hp
      exact Multiset.mem_toFinset.mpr ((Multiset.count_pos.mp hp))
    exact hfin.subset (by intro p hp; exact hp.2)
  locallyFiniteTail := by
    classical
    intro a b c hab hbc
    have hfin : Set.Finite {p | 0 < (D.points.map diagramDecoratedPoint).count p} := by
      apply (D.points.map diagramDecoratedPoint).toFinset.finite_toSet.subset
      intro p hp
      exact Multiset.mem_toFinset.mpr ((Multiset.count_pos.mp hp))
    exact hfin.subset (by intro p hp; exact hp.2)

private noncomputable def finiteDecoratedMultisetOf
    (s : Multiset (ℝ × WithTop ℝ)) :
    Multiset (Cut ℝ × Cut ℝ) := by
  classical
  exact (s.map diagramDecoratedPoint).filter (fun p => p.2 ≠ infinityCut)

private noncomputable def finiteDecoratedMultiset (D : Diagram ℝ) :
    Multiset (Cut ℝ × Cut ℝ) := finiteDecoratedMultisetOf D.points

private theorem finiteDecoratedMultiset_count (D : Diagram ℝ)
    (p : Cut ℝ × Cut ℝ) (hp : p.2 ≠ infinityCut) :
    (finiteDecoratedMultiset D).count p =
      (D.points.map diagramDecoratedPoint).count p := by
  classical
  simp only [finiteDecoratedMultiset, finiteDecoratedMultisetOf]
  exact Multiset.count_filter_of_pos hp

/-- Occurrence labels of a positive finite diagram are the same finite multiset of
decorated finite endpoints, expanded to one label per copy. -/
noncomputable def Diagram.toLocallyFiniteFiniteOccurrenceEquiv (D : Diagram ℝ)
    (hD : D.IsPositive) :
    (D.toLocallyFinite hD).finiteOccurrences ≃ finiteDecoratedMultiset D := by
  classical
  change (Σ p : {p : Cut ℝ × Cut ℝ //
      0 < (D.points.map diagramDecoratedPoint).count p ∧ p.2 ≠ infinityCut},
      Fin ((D.points.map diagramDecoratedPoint).count p.1)) ≃ finiteDecoratedMultiset D
  refine
    { toFun := fun o => ⟨o.1.1, ⟨o.2.1, ?_⟩⟩
      invFun := fun q => by
        have hInf : q.1.2 ≠ infinityCut := by
          have hpos : 0 < (finiteDecoratedMultiset D).count q.1 :=
            Nat.zero_lt_of_lt q.2.2
          exact (Multiset.mem_filter.mp (Multiset.count_pos.mp hpos)).2
        have hcount := finiteDecoratedMultiset_count D q.1 hInf
        have hpos : 0 < (D.points.map diagramDecoratedPoint).count q.1 := by
          rw [← hcount]
          exact Nat.zero_lt_of_lt q.2.2
        have hlt : q.2.1 < (D.points.map diagramDecoratedPoint).count q.1 := by
          rw [← hcount]
          exact q.2.2
        exact ⟨⟨q.1, hpos, hInf⟩, ⟨q.2.1, hlt⟩⟩
      left_inv := by
        intro o
        cases o with
        | mk q n => cases q with
          | mk p hp => cases n; rfl
      right_inv := by
        intro q
        cases q
        rfl }
  · have hcount := finiteDecoratedMultiset_count D o.1.1 o.1.2.2
    rw [hcount]
    exact o.2.2

noncomputable instance Diagram.toLocallyFinite_finiteOccurrences_fintype
    (D : Diagram ℝ) (hD : D.IsPositive) :
    Fintype (D.toLocallyFinite hD).finiteOccurrences :=
  Fintype.ofEquiv _ (Diagram.toLocallyFiniteFiniteOccurrenceEquiv D hD).symm

private noncomputable def essentialDecoratedMultiset (D : Diagram ℝ) : Multiset (Cut ℝ) :=
  (D.points.map diagramDecoratedPoint).filterMap fun p =>
    if p.2 = infinityCut then some p.1 else none

private noncomputable def essentialDecoratedMultisetOf
    (s : Multiset (ℝ × WithTop ℝ)) : Multiset (Cut ℝ) :=
  (s.map diagramDecoratedPoint).filterMap fun p =>
    if p.2 = infinityCut then some p.1 else none

private theorem essentialDecoratedMultisetOf_count
    (s : Multiset (ℝ × WithTop ℝ)) (birth : Cut ℝ) :
    (essentialDecoratedMultisetOf s).count birth =
      (s.map diagramDecoratedPoint).count (birth, infinityCut) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [essentialDecoratedMultisetOf]
  | @cons q s ih =>
      rcases q with ⟨b, d⟩
      cases d with
      | top =>
          have hL : essentialDecoratedMultisetOf ((b, (⊤ : WithTop ℝ)) ::ₘ s) =
              minusCut b ::ₘ essentialDecoratedMultisetOf s := by
            simp [essentialDecoratedMultisetOf, diagramDecoratedPoint]
          have hR : (((b, (⊤ : WithTop ℝ)) ::ₘ s).map diagramDecoratedPoint) =
              (minusCut b, infinityCut) ::ₘ (s.map diagramDecoratedPoint) := by
            simp [diagramDecoratedPoint]
          rw [hL, hR]
          simp [Multiset.count_cons, ih]
      | coe d =>
          have hne : minusCut d ≠ infinityCut := by
            intro heq
            have hm : minusCut d ∈ cutCell (d - 1) d := by
              simp [cutCell, minusCut]
            exact infinityCut_not_mem_cutCell (d - 1) d (heq ▸ hm)
          have hne' : infinityCut ≠ minusCut d := Ne.symm hne
          have hL : essentialDecoratedMultisetOf ((b, (d : WithTop ℝ)) ::ₘ s) =
              essentialDecoratedMultisetOf s := by
            unfold essentialDecoratedMultisetOf
            rw [Multiset.map_cons]
            have hnone : (fun p : Cut ℝ × Cut ℝ =>
                if p.2 = infinityCut then some p.1 else none)
                (minusCut b, minusCut d) = none := by
              simp [hne]
            exact Multiset.filterMap_cons_none _ _ hnone
          have hR : (((b, (d : WithTop ℝ)) ::ₘ s).map diagramDecoratedPoint) =
              (minusCut b, minusCut d) ::ₘ (s.map diagramDecoratedPoint) := by
            simp [diagramDecoratedPoint]
          rw [hL, hR]
          simp [Multiset.count_cons, ih, hne']

private theorem essentialDecoratedMultiset_count (D : Diagram ℝ) (birth : Cut ℝ) :
    (essentialDecoratedMultiset D).count birth =
      (D.points.map diagramDecoratedPoint).count (birth, infinityCut) := by
  classical
  simpa [essentialDecoratedMultiset, essentialDecoratedMultisetOf] using
    essentialDecoratedMultisetOf_count D.points birth

/-- Essential occurrence labels of the positive finite diagram are retained on its
actual infinity boundary. -/
noncomputable def Diagram.toLocallyFiniteEssentialOccurrenceEquiv (D : Diagram ℝ)
    (hD : D.IsPositive) :
    (D.toLocallyFinite hD).essentialOccurrences ≃ essentialDecoratedMultiset D := by
  classical
  change (Σ birth : {b : Cut ℝ //
      0 < (D.points.map diagramDecoratedPoint).count (b, infinityCut)},
      Fin ((D.points.map diagramDecoratedPoint).count (birth.1, infinityCut))) ≃
        essentialDecoratedMultiset D
  refine
    { toFun := fun o => ⟨o.1.1, ⟨o.2.1, ?_⟩⟩
      invFun := fun q => by
        have hcount := essentialDecoratedMultiset_count D q.1
        have hpos : 0 < (D.points.map diagramDecoratedPoint).count (q.1, infinityCut) := by
          rw [← hcount]
          exact Nat.zero_lt_of_lt q.2.2
        have hlt : q.2.1 < (D.points.map diagramDecoratedPoint).count
            (q.1, infinityCut) := by
          rw [← hcount]
          exact q.2.2
        exact ⟨⟨q.1, hpos⟩, ⟨q.2.1, hlt⟩⟩
      left_inv := by
        intro o
        cases o with
        | mk q n => cases q with
          | mk p hp => cases n; rfl
      right_inv := by
        intro q
        cases q
        rfl }
  · have hcount := essentialDecoratedMultiset_count D o.1.1
    rw [hcount]
    exact o.2.2

noncomputable instance Diagram.toLocallyFinite_essentialOccurrences_fintype
    (D : Diagram ℝ) (hD : D.IsPositive) :
    Fintype (D.toLocallyFinite hD).essentialOccurrences :=
  Fintype.ofEquiv _ (Diagram.toLocallyFiniteEssentialOccurrenceEquiv D hD).symm

private theorem finiteDecoratedMultisetOf_endpoints (s : Multiset (ℝ × WithTop ℝ)) :
    (finiteDecoratedMultisetOf s).map
      (fun p => (cutEndpoint p.1, cutEndpoint p.2)) = finitePart s := by
  classical
  simp only [finiteDecoratedMultisetOf, finitePart, Multiset.filter_map,
    Multiset.map_map, Multiset.map_filter_eq_filterMap, Multiset.map_filterMap]
  apply congrArg (fun f : (ℝ × WithTop ℝ) → Option (ℝ × ℝ) => s.filterMap f)
  funext p
  rcases p with ⟨b, d⟩
  cases d with
  | top => simp [diagramDecoratedPoint]
  | coe d =>
      have hne : minusCut d ≠ infinityCut := by
        intro heq
        have hm : minusCut d ∈ cutCell (d - 1) d := by
          simp [cutCell, minusCut]
        exact infinityCut_not_mem_cutCell (d - 1) d (heq ▸ hm)
      simp [diagramDecoratedPoint, cutEndpoint_minusCut, hne]

private theorem finiteDecoratedMultiset_endpoints (D : Diagram ℝ) :
    (finiteDecoratedMultiset D).map
      (fun p => (cutEndpoint p.1, cutEndpoint p.2)) = finitePart D.points := by
  exact finiteDecoratedMultisetOf_endpoints D.points

private theorem essentialDecoratedMultisetOf_endpoints
    (s : Multiset (ℝ × WithTop ℝ)) :
    (essentialDecoratedMultisetOf s).map cutEndpoint = essentialPart s := by
  classical
  simp only [essentialDecoratedMultisetOf, essentialPart, Multiset.map_filterMap,
    Multiset.filterMap_map]
  apply congrArg (fun f : (ℝ × WithTop ℝ) → Option ℝ => s.filterMap f)
  funext p
  rcases p with ⟨b, d⟩
  cases d with
  | top => simp [diagramDecoratedPoint, cutEndpoint_minusCut]
  | coe d =>
      have hne : minusCut d ≠ infinityCut := by
        intro heq
        have hm : minusCut d ∈ cutCell (d - 1) d := by
          simp [cutCell, minusCut]
        exact infinityCut_not_mem_cutCell (d - 1) d (heq ▸ hm)
      simp [diagramDecoratedPoint, hne]

private theorem essentialDecoratedMultiset_endpoints (D : Diagram ℝ) :
    (essentialDecoratedMultiset D).map cutEndpoint = essentialPart D.points := by
  simpa [essentialDecoratedMultiset, essentialDecoratedMultisetOf] using
    essentialDecoratedMultisetOf_endpoints D.points

private theorem map_univ_eq_of_equiv_local {A B C : Type*}
    [Fintype A] [Fintype B] (x : A → C) (y : B → C)
    (e : A ≃ B) (h : ∀ a, y (e a) = x a) :
    (Finset.univ : Finset A).val.map x =
      (Finset.univ : Finset B).val.map y := by
  classical
  calc
    (Finset.univ : Finset A).val.map x =
        (Finset.univ : Finset A).val.map (y ∘ e) := by
          congr 1
          funext a
          exact (h a).symm
    _ = ((Finset.univ : Finset A).map e.toEmbedding).val.map y := by
          rw [Finset.map_val, Multiset.map_map]
          rfl
    _ = (Finset.univ : Finset B).val.map y := by rw [Finset.map_univ_equiv]

private theorem finiteOccurrence_endpoints (D : Diagram ℝ) (hD : D.IsPositive) :
    (Finset.univ : Finset (D.toLocallyFinite hD).finiteOccurrences).val.map
        (D.toLocallyFinite hD).finitePoint = finitePart D.points := by
  classical
  let e := Diagram.toLocallyFiniteFiniteOccurrenceEquiv D hD
  let x := (D.toLocallyFinite hD).finitePoint
  let y : finiteDecoratedMultiset D → ℝ × ℝ :=
    fun p => (cutEndpoint p.1.1, cutEndpoint p.1.2)
  have hv : ∀ o, y (e o) = x o := by
    intro o
    rfl
  calc
    _ = (Finset.univ : Finset (finiteDecoratedMultiset D)).val.map y :=
      map_univ_eq_of_equiv_local x y e hv
    _ = (finiteDecoratedMultiset D).map (fun p =>
        (cutEndpoint p.1, cutEndpoint p.2)) := by
          calc
            _ = ((Finset.univ : Finset (finiteDecoratedMultiset D)).val.map
                (fun p => p.1)).map (fun p => (cutEndpoint p.1, cutEndpoint p.2)) := by
                  simp only [y, Multiset.map_map]
                  rfl
            _ = _ := by rw [Multiset.map_univ_coe]
    _ = finitePart D.points := finiteDecoratedMultiset_endpoints D

private theorem essentialOccurrence_endpoints (D : Diagram ℝ) (hD : D.IsPositive) :
    (Finset.univ : Finset (D.toLocallyFinite hD).essentialOccurrences).val.map
        (D.toLocallyFinite hD).essentialBirth = essentialPart D.points := by
  classical
  let e := Diagram.toLocallyFiniteEssentialOccurrenceEquiv D hD
  let x := (D.toLocallyFinite hD).essentialBirth
  let y : essentialDecoratedMultiset D → ℝ := fun p => cutEndpoint p.1
  have hv : ∀ o, y (e o) = x o := by
    intro o
    rfl
  calc
    _ = (Finset.univ : Finset (essentialDecoratedMultiset D)).val.map y :=
      map_univ_eq_of_equiv_local x y e hv
    _ = (essentialDecoratedMultiset D).map cutEndpoint := by
          calc
            _ = ((Finset.univ : Finset (essentialDecoratedMultiset D)).val.map
                (fun p => p.1)).map cutEndpoint := by
                  simp only [y, Multiset.map_map]
                  rfl
            _ = _ := by rw [Multiset.map_univ_coe]
    _ = essentialPart D.points := essentialDecoratedMultiset_endpoints D

private theorem iSup_eq_finset_sup {α : Type*} [Fintype α]
    (f : α → ℝ≥0∞) : (⨆ a, f a) = (Finset.univ : Finset α).sup f := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro a
    exact Finset.le_sup (Finset.mem_univ a)
  · apply Finset.sup_le
    intro a _
    exact le_iSup f a

private theorem matchingCost_eq_cost
    {D E : LocallyFiniteDecoratedDiagram}
    [Fintype D.finiteOccurrences] [Fintype E.finiteOccurrences]
    [Fintype D.essentialOccurrences] [Fintype E.essentialOccurrences]
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) :
    LocallyFiniteDecoratedDiagram.matchingCost M =
      M.cost D.finitePoint E.finitePoint D.essentialBirth E.essentialBirth := by
  classical
  unfold LocallyFiniteDecoratedDiagram.matchingCost OccurrenceMatching.cost
  simp only [iSup_eq_finset_sup]
  apply congrArg₂ max
  · apply Finset.sup_congr
    · ext i
      simp
    · intro i hi
      cases h : M.finite i <;> rfl
  · apply congrArg₂ max
    · apply Finset.sup_congr
      · ext j
        simp
      · intro j hj
        by_cases h : ∃ i, M.finite i = some j
        · simp [h]
        · simp [h]
    · apply Finset.sup_congr
      · ext b
        simp
      · intro b hb
        simp

/-- The locally finite bottleneck restricts to the existing finite bottleneck on
positive finite diagrams. Positivity is necessary because the source `Diagram`
type also permits reverse bars, while q-tame finite deaths are supported only
on the positive half of the decorated endpoint plane. -/
theorem bottleneck_toLocallyFinite (D E : Diagram ℝ)
    (hD : D.IsPositive) (hE : E.IsPositive) :
    (D.toLocallyFinite hD).bottleneck (E.toLocallyFinite hE) = bottleneck D E := by
  classical
  let D' := D.toLocallyFinite hD
  let E' := E.toLocallyFinite hE
  have hfinite :
      (Finset.univ : Finset D'.finiteOccurrences).val.map D'.finitePoint =
        finitePart D.points := finiteOccurrence_endpoints D hD
  have hfinite' :
      (Finset.univ : Finset E'.finiteOccurrences).val.map E'.finitePoint =
        finitePart E.points := finiteOccurrence_endpoints E hE
  have hess :
      (Finset.univ : Finset D'.essentialOccurrences).val.map D'.essentialBirth =
        essentialPart D.points := essentialOccurrence_endpoints D hD
  have hess' :
      (Finset.univ : Finset E'.essentialOccurrences).val.map E'.essentialBirth =
        essentialPart E.points := essentialOccurrence_endpoints E hE
  calc
    D'.bottleneck E' = presentationBottleneck D'.finitePoint E'.finitePoint
        D'.essentialBirth E'.essentialBirth := by
          unfold LocallyFiniteDecoratedDiagram.bottleneck presentationBottleneck
          apply iInf_congr
          intro M
          exact matchingCost_eq_cost M
    _ = bottleneck D E := by
      symm
      exact bottleneck_eq_presentation D E D'.finitePoint E'.finitePoint
        D'.essentialBirth E'.essentialBirth hfinite hfinite' hess hess'

end
end TDA.Persistence
