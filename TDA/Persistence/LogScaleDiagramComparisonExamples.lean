import TDA.Persistence.SublevelDiagramMonotone
import TDA.Persistence.LogScaleDiagramComparison
import TDA.Persistence.SublevelDiagramExamples
import TDA.Persistence.CechSupNormDiagramExamples
import TDA.Persistence.LogScaleDiagramExamples
import TDA.Simplicial.Attachment
import TDA.Persistence.DiagramBottleneckLaws

set_option autoImplicit false

/-!
# Explicit fixtures for the log-scale/radius comparison

These fixtures test the monotone reparametrisation law, the two-point Čech and Rips
diagrams, the positive-degree log identity, and the necessity of its positivity and
degree hypotheses.  The degree-zero fixtures are radius-level statements only.
-/

namespace TDA.Persistence.LogScaleDiagramComparisonExamples

open CategoryTheory CategoryTheory.Limits TDA.Simplicial TDA.Filtration TDA.Persistence
open TDA.Persistence.Examples
open TDA.Persistence.FiniteConstructible
open TDA.Persistence.SublevelConstructibleExamples
open TDA.Persistence.LogScaleDiagramExamples
open TDA.Persistence.Reduction.Examples
open TDA.Filtration.Cech.Examples
open scoped NNReal ENNReal

/-! ### The two-point Rips filter on the edge fixture -/

private noncomputable def ripsEdge : FilterFunction edgeK ℝ where
  value s := (Rips.filter TwoPoints.metric).value s
  mono := by
    intro τ σ hτ
    exact (Rips.filter TwoPoints.metric).mono hτ

private theorem ripsEdge_values :
    ripsEdge.value edge_v0 = 0 ∧
      ripsEdge.value edge_v1 = 0 ∧
      ripsEdge.value edge_e01 = 2 := by
  have h0 : (Rips.filter TwoPoints.metric).value edge_v0 = 0 := by
    change Rips.diameter TwoPoints.metric ({0} : Finset (Fin 2)) = 0
    simp
  have h1 : (Rips.filter TwoPoints.metric).value edge_v1 = 0 := by
    change Rips.diameter TwoPoints.metric ({1} : Finset (Fin 2)) = 0
    simp
  have he : (Rips.filter TwoPoints.metric).value edge_e01 = 2 := by
    change Rips.diameter TwoPoints.metric ({0, 1} : Finset (Fin 2)) = 2
    rw [Rips.diameter_pair, TwoPoints.metric_dist, TwoPoints.dist_pts]
  exact ⟨h0, h1, he⟩

private theorem ripsEdge_dgm (n : ℕ) :
    dgm (ZMod 2) ripsEdge n = dgm (ZMod 2) (Rips.filter TwoPoints.metric) n := by
  have hI : (edgeFaces : Fintype (TotalFace edgeK)) =
      (Rips.fullComplexFintype : Fintype (TotalFace edgeK)) :=
    Subsingleton.elim _ _
  exact congrArg (fun I => @dgm (Fin 2) _ (ZMod 2) _ ℝ _ edgeK I ripsEdge n) hI

private theorem ripsEdge_map_value (s : TotalFace edgeK) :
    (Rips.filter TwoPoints.metric).value s =
      (if s.val = ({0} : Finset (Fin 2)) then 0
        else if s.val = ({1} : Finset (Fin 2)) then 0 else 2) := by
  rcases edge_face_cases s with h0 | h1 | he
  · change Rips.diameter TwoPoints.metric s.val = _
    rw [h0]
    simp
  · change Rips.diameter TwoPoints.metric s.val = _
    rw [h1]
    simp
  · change Rips.diameter TwoPoints.metric s.val = _
    rw [he]
    change Rips.diameter TwoPoints.metric ({0, 1} : Finset (Fin 2)) = 2
    rw [Rips.diameter_pair, TwoPoints.metric_dist, TwoPoints.dist_pts]

/-- The degree-zero two-point Rips diagram has one essential and one finite bar. -/
theorem twoPoints_rips_dgm_zero :
    (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), ((0 : ℝ), ((2 : ℝ) : WithTop ℝ))} := by
  rw [← ripsEdge_dgm 0]
  let φ : ℝ → ℝ := fun x => if x ≤ 5 then 0 else 2
  have hφ : MonotoneOn φ (Set.range edgeFilter.value) := by
    intro a ha b hb hab
    by_cases ha5 : a ≤ 5
    · by_cases hb5 : b ≤ 5 <;> simp [φ, ha5, hb5]
    · have hb5 : ¬ b ≤ 5 := fun hb' => ha5 (hab.trans hb')
      simp [φ, ha5, hb5]
  have hvalue : ∀ s, ripsEdge.value s = φ (edgeFilter.value s) := by
    intro s
    change (Rips.filter TwoPoints.metric).value s = φ (edgeFilter.value s)
    rw [ripsEdge_map_value]
    rcases edge_face_cases s with h0 | h1 | he
    · simp [edgeFilter, φ, h0] ; norm_num
    · simp [edgeFilter, φ, h1]
    · simp [edgeFilter, φ, he, Finset.ext_iff] ; norm_num
  rw [dgm_points_map_of_monotoneOn (ZMod 2) edgeFilter ripsEdge φ hφ hvalue 0]
  rw [edge_points]
  norm_num [φ, Multiset.filter_singleton]

/-! ### The diagonal-control fixture -/

/-- The constant edge filter used to exhibit deletion of a collapsed finite bar. -/
def constEdge : FilterFunction edgeK ℝ where
  value _ := 0
  mono _ := le_rfl

/-- A monotone map may collapse a finite bar onto the diagonal, which is filtered out. -/
theorem constEdge_dgm_zero :
    (dgm (ZMod 2) constEdge 0).points = {((0 : ℝ), (⊤ : WithTop ℝ))} := by
  let φ : ℝ → ℝ := fun _ => 0
  have hφ : MonotoneOn φ (Set.range edgeFilter.value) :=
    monotone_const.monotoneOn _
  have hvalue : ∀ s, constEdge.value s = φ (edgeFilter.value s) := by
    intro s
    rfl
  rw [dgm_points_map_of_monotoneOn (ZMod 2) edgeFilter constEdge φ hφ hvalue 0]
  rw [edge_points]
  norm_num [φ, Multiset.filter_singleton]

/-! ### Vanishing in positive degrees on two vertices -/

private theorem twoPoint_sublevel_card_le_one
    (f : FilterFunction (Rips.fullComplex (Fin 2)) ℝ) {t : ℝ}
    (hedge : ({0, 1} : Finset (Fin 2)) ∉ f.sublevel t) :
    ∀ s ∈ f.sublevel t, s.card ≤ 1 := by
  intro s hs
  have hsK := (f.sublevel_le t) hs
  change s.Nonempty at hsK
  by_contra hcard
  have hle : s.card ≤ Fintype.card (Fin 2) := Finset.card_le_univ s
  have hscard : s.card = 2 := by
    simp only [Fintype.card_fin] at hle
    omega
  have hfull : s = ({0, 1} : Finset (Fin 2)) := by
    simpa only [Finset.univ_fin2] using (Finset.eq_univ_of_card s hscard)
  apply hedge
  rw [← hfull]
  exact hs

private theorem twoPoint_sublevel_eq_full
    (f : FilterFunction (Rips.fullComplex (Fin 2)) ℝ) {t : ℝ}
    (hedge : ({0, 1} : Finset (Fin 2)) ∈ f.sublevel t) :
    f.sublevel t = Rips.fullComplex (Fin 2) := by
  apply le_antisymm (f.sublevel_le t)
  intro s hs
  change s.Nonempty at hs
  have hsub : s ⊆ ({0, 1} : Finset (Fin 2)) := by
    rw [← Finset.univ_fin2]
    exact Finset.subset_univ s
  exact ((f.sublevel t).isRelLowerSet_faces hedge).2 hsub hs

private def twoPointVertices : PreAbstractSimplicialComplex (Fin 2) where
  faces := {s | s.card = 1}
  isRelLowerSet_faces := by
    intro s hs
    change s.card = 1 at hs
    have hspos : 0 < s.card := by omega
    refine ⟨Finset.card_pos.mp hspos, ?_⟩
    intro t hts ht
    change t.card = 1
    have hle := Finset.card_le_card hts
    have hpos : 1 ≤ t.card := Finset.card_pos.mpr ht
    omega

private instance twoPointVertices_no_edge : IsEmpty (Face twoPointVertices 1) :=
  ⟨fun σ => by
    have hs := σ.2.1
    change σ.1.card = 1 at hs
    have hdeg := σ.2.2
    omega⟩

private def twoPointEdgeAttachment :
    SimplexAttachment twoPointVertices (Rips.fullComplex (Fin 2)) 1 where
  simplex := {0, 1}
  card_simplex := by decide
  not_mem := by
    change ¬ (({0, 1} : Finset (Fin 2)).card = 1)
    decide
  face_iff := by
    change ∀ s : Finset (Fin 2),
      s.Nonempty ↔ s.card = 1 ∨ s = ({0, 1} : Finset (Fin 2))
    decide

private theorem twoPoint_full_isZero (k : Type) [Field k] {n : ℕ}
    (hn : 1 ≤ n) :
    IsZero (simplicialHomology (Rips.fullComplex (Fin 2)) k n) := by
  by_cases hn1 : n = 1
  · subst n
    let A := twoPointEdgeAttachment
    have hq : A.attachingQuotientClass k ≠ 0 := by
      intro hq
      apply A.attachingClass_ne_zero_of_no_old_coface k
      apply (homologyKernelQuotient k
        (simplicialChainComplex twoPointVertices k) 0).toLinearEquiv.injective
      rw [A.attachingHomologyClass_equiv k, hq]
      exact ((homologyKernelQuotient k
        (simplicialChainComplex twoPointVertices k) 0).toLinearEquiv.map_zero).symm
    have hbij := A.homologyIncl_bijective_of_attachingClass_ne_zero k hq
    have hsource : IsZero (simplicialHomology twoPointVertices k 1) :=
      isZero_simplicialHomology_of_card_le_one k
        (by
          intro s hs
          change s.card = 1 at hs
          exact hs.le) le_rfl
    letI : Subsingleton (simplicialHomology twoPointVertices k 1) :=
      ModuleCat.isZero_iff_subsingleton.mp hsource
    letI : Subsingleton (simplicialHomology (Rips.fullComplex (Fin 2)) k 1) :=
      ⟨fun x y => by
        obtain ⟨x', hx'⟩ := hbij.2 x
        obtain ⟨y', hy'⟩ := hbij.2 y
        exact hx'.symm.trans
          ((congrArg (fun z => (simplicialHomologyIncl k A.inclusion 1).hom z)
            (Subsingleton.elim x' y')).trans hy')⟩
    exact ModuleCat.isZero_of_subsingleton _
  · have hn2 : 2 ≤ n := by omega
    letI : IsEmpty (Face (Rips.fullComplex (Fin 2)) n) :=
      ⟨fun σ => by
        have hcard := Finset.card_le_univ σ.1
        simp only [Fintype.card_fin] at hcard
        have hdeg := σ.2.2
        omega⟩
    exact isZero_simplicialHomology_of_isEmpty_face k n

private theorem twoPoint_sublevel_isZero (k : Type) [Field k]
    (f : FilterFunction (Rips.fullComplex (Fin 2)) ℝ) {n : ℕ}
    (hn : 1 ≤ n) (t : ℝ) :
    IsZero (simplicialHomology (f.sublevel t) k n) := by
  by_cases hedge : ({0, 1} : Finset (Fin 2)) ∈ f.sublevel t
  · rw [twoPoint_sublevel_eq_full f hedge]
    exact twoPoint_full_isZero k hn
  · exact isZero_simplicialHomology_of_card_le_one k
      (twoPoint_sublevel_card_le_one f hedge) hn

/-- In every positive degree, the two-point Rips diagram is empty over every field. -/
theorem twoPoints_rips_dgm_pos (k : Type) [Field k] {n : ℕ} (hn : 1 ≤ n) :
    (dgm k (Rips.filter TwoPoints.metric) n).points = 0 := by
  exact dgm_points_eq_zero_of_isZero k (Rips.filter TwoPoints.metric)
    (fun t => twoPoint_sublevel_isZero k (Rips.filter TwoPoints.metric) hn t)

/-- In every positive degree, the two-point Čech diagram is empty over every field. -/
theorem twoPoints_cech_dgm_pos (k : Type) [Field k] {n : ℕ} (hn : 1 ≤ n) :
    (dgm k (Cech.filter TwoPoints.pts) n).points = 0 := by
  exact dgm_points_eq_zero_of_isZero k (Cech.filter TwoPoints.pts)
    (fun t => twoPoint_sublevel_isZero k (Cech.filter TwoPoints.pts) hn t)

/-! ### Čech and log-scale diagrams -/

/-- The degree-zero two-point Čech diagram has death one, the ambient radius convention. -/
theorem twoPoints_cech_dgm_zero :
    (dgm (ZMod 2) (Cech.filter TwoPoints.pts) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), ((0 : ℝ), ((1 : ℝ) : WithTop ℝ))} := by
  rw [Cech.SupNormDiagramExamples.TwoPoints.dgm_eq, Diagram.scale,
    Diagram.map_points, twoPoints_rips_dgm_zero]
  norm_num

/-- In every positive degree, the two-point Rips log-scale diagram is empty. -/
theorem twoPoints_rips_logDgm_pos {n : ℕ} (hn : 1 ≤ n) :
    (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n).points = 0 := by
  rw [logDgm_points_eq_map_log (ZMod 2) hn twoPoints_rips_positive,
    twoPoints_rips_dgm_pos (ZMod 2) hn, Multiset.map_zero]

/-- In every positive degree, the two-point Čech log-scale diagram is empty. -/
theorem twoPoints_cech_logDgm_pos {n : ℕ} (hn : 1 ≤ n) :
    (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n).points = 0 := by
  rw [logDgm_points_eq_map_log (ZMod 2) hn twoPoints_cech_positive,
    twoPoints_cech_dgm_pos (ZMod 2) hn, Multiset.map_zero]

/-! ### Exact two-point bottleneck values -/

/-- The degree-zero two-point Čech and Rips bottleneck distance is one. -/
theorem twoPoints_bottleneck_zero :
    bottleneck (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0)
        (dgm (ZMod 2) (Cech.filter TwoPoints.pts) 0) = 1 := by
  classical
  let x : Fin 1 → ℝ × ℝ := fun _ => (0, 2)
  let y : Fin 1 → ℝ × ℝ := fun _ => (0, 1)
  let b : Fin 1 → ℝ := fun _ => 0
  let c : Fin 1 → ℝ := fun _ => 0
  have hx : (Finset.univ : Finset (Fin 1)).val.map x =
      finitePart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points := by
    simp [finitePart, x, twoPoints_rips_dgm_zero] ; rfl
  have hy : (Finset.univ : Finset (Fin 1)).val.map y =
      finitePart (dgm (ZMod 2) (Cech.filter TwoPoints.pts) 0).points := by
    simp [finitePart, y, twoPoints_cech_dgm_zero] ; rfl
  have hb : (Finset.univ : Finset (Fin 1)).val.map b =
      essentialPart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points := by
    simp [essentialPart, b, twoPoints_rips_dgm_zero] ; rfl
  have hc : (Finset.univ : Finset (Fin 1)).val.map c =
      essentialPart (dgm (ZMod 2) (Cech.filter TwoPoints.pts) 0).points := by
    simp [essentialPart, c, twoPoints_cech_dgm_zero] ; rfl
  rw [bottleneck_eq_presentation _ _ x y b c hx hy hb hc]
  apply le_antisymm
  · let M : OccurrenceMatching (Fin 1) (Fin 1) (Fin 1) (Fin 1) :=
      ⟨fun _ => none, by simp, Equiv.refl _⟩
    have hcost : M.cost x y b c = 1 := by
      simp [OccurrenceMatching.cost, M, x, y, b, c, diagonalCost,
        essentialPairCost]
    exact (presentationBottleneck_le_cost x y b c M).trans_eq hcost
  · unfold presentationBottleneck
    apply le_iInf
    intro M
    have hsource := M.source_le_cost x y b c 0
    cases h : M.finite 0 with
    | none =>
        calc
          1 = diagonalCost (x 0) := by norm_num [x, diagonalCost]
          _ ≤ M.cost x y b c := by simpa [h] using hsource
    | some j =>
        have hj : j = 0 := Fin.eq_zero j
        subst j
        calc
          1 = finitePairCost (x 0) (y 0) := by norm_num [x, y, finitePairCost]
          _ ≤ M.cost x y b c := by simpa [h] using hsource

/-- In every positive degree, the two-point radius-level bottleneck distance is zero. -/
theorem twoPoints_bottleneck_pos {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (dgm (ZMod 2) (Rips.filter TwoPoints.metric) n)
        (dgm (ZMod 2) (Cech.filter TwoPoints.pts) n) = 0 := by
  have hD : dgm (ZMod 2) (Rips.filter TwoPoints.metric) n =
      dgm (ZMod 2) (Cech.filter TwoPoints.pts) n := by
    apply Diagram.ext
    rw [twoPoints_rips_dgm_pos (ZMod 2) hn, twoPoints_cech_dgm_pos (ZMod 2) hn]
  rw [hD]
  exact bottleneck_self _

/-- In every positive degree, the two-point log-scale bottleneck distance is zero. -/
theorem twoPoints_logBottleneck_pos {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n)
        (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n) = 0 := by
  have hD : logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n =
      logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n := by
    apply Diagram.ext
    rw [twoPoints_rips_logDgm_pos hn, twoPoints_cech_logDgm_pos hn]
  rw [hD]
  exact bottleneck_self _

/-! ### Certified positive-degree examples and a translated negative control -/

private theorem filledReal_dgm_one_points :
    (dgm (ZMod 2) filledReal 1).points =
      {((1 : ℝ), ((2 : ℝ) : WithTop ℝ))} := by
  rw [← moduleDiagram_sublevelModule (ZMod 2) 1 filledReal]
  exact filledReal_moduleDiagram_one

private theorem hollowReal_dgm_one_points :
    (dgm (ZMod 2) hollowReal 1).points = {((1 : ℝ), (⊤ : WithTop ℝ))} := by
  rw [← moduleDiagram_sublevelModule (ZMod 2) 1 hollowReal]
  exact hollowReal_moduleDiagram_one

/-- The filled certified triangle has a nontrivial degree-one log bar. -/
theorem filledReal_logDgm_one :
    (logDgm (ZMod 2) filledReal 1).points =
      {((0 : ℝ), ((Real.log 2 : ℝ) : WithTop ℝ))} := by
  rw [logDgm_points_eq_map_log (ZMod 2) le_rfl filledReal_positive,
    filledReal_dgm_one_points]
  simp [Real.log_one]

/-- The hollow certified triangle retains an essential degree-one log bar. -/
theorem hollowReal_logDgm_one :
    (logDgm (ZMod 2) hollowReal 1).points = {((0 : ℝ), (⊤ : WithTop ℝ))} := by
  rw [logDgm_points_eq_map_log (ZMod 2) le_rfl hollowReal_positive,
    hollowReal_dgm_one_points]
  simp [Real.log_one]

/-- Every degree-one filled-triangle radius-level birth is positive. -/
theorem filledReal_dgm_one_pos {p : ℝ × WithTop ℝ}
    (hp : p ∈ (dgm (ZMod 2) filledReal 1).points) : 0 < p.1 :=
  dgm_birth_pos (ZMod 2) le_rfl filledReal_positive hp

/-- The filled triangle shifted by `-2` has its degree-one bar at `(-1,0)`. -/
noncomputable def shiftedReal : FilterFunction FilledTriangle.C.toPre ℝ :=
  filledReal.map (OrderIso.addRight (-2 : ℝ)).toOrderEmbedding

/-- The shifted filled-triangle degree-one diagram has its bar at `(-1, 0)`, with negative birth. -/
theorem shiftedReal_dgm_one :
    (dgm (ZMod 2) shiftedReal 1).points =
      {((-1 : ℝ), ((0 : ℝ) : WithTop ℝ))} := by
  rw [shiftedReal, dgm_map, Diagram.map_points, filledReal_dgm_one_points]
  norm_num [OrderIso.addRight_apply]

/-- Positivity on edges fails for the shifted filled triangle. -/
theorem shiftedReal_not_positive : ¬ PositiveOnEdges shiftedReal := by
  intro hpos
  have hv := hpos
    (⟨({0, 1} : Finset (Fin 3)), by decide⟩ : TotalFace FilledTriangle.C.toPre)
    (by decide)
  norm_num [shiftedReal, filledReal, FilterFunction.map, FilledTriangle.f,
    OrderIso.addRight_apply] at hv

/-- The shifted degree-one birth is negative, giving the required positivity counterexample. -/
theorem shiftedReal_birth_neg :
    ((-1 : ℝ), ((0 : ℝ) : WithTop ℝ)) ∈
        (dgm (ZMod 2) shiftedReal 1).points ∧ ¬ (0 : ℝ) < -1 := by
  rw [shiftedReal_dgm_one]
  simp

/-! ### Boundary control for degree zero -/

/-- Degree zero has a birth at zero even though the two-point Rips filter is positive on edges. -/
theorem twoPoints_rips_dgm_zero_birth :
    ((0 : ℝ), (⊤ : WithTop ℝ)) ∈
        (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points ∧
      ¬ (0 : ℝ) < 0 ∧ PositiveOnEdges (Rips.filter TwoPoints.metric) := by
  refine ⟨?_, by norm_num, twoPoints_rips_positive⟩
  rw [twoPoints_rips_dgm_zero]
  simp

end TDA.Persistence.LogScaleDiagramComparisonExamples
