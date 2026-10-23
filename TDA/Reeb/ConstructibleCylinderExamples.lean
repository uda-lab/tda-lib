import TDA.Reeb.ConstructibleCylinder
import TDA.Reeb.ConstructibleSpaceExamples

/-!
# Examples: local cylinder comparisons and constructibility

All fixtures compute the `intervalComponents` of realized finite data
(`ofFiniteData`).

* `n = 0`: two vertices at one level give the value `2` on `ℝ`, and the inclusion of `(-1, 1)`
  into `ℝ` is bijective; the lower tail has an empty value.
* Pinch: two edges over `(0, 1)` whose bottom ends both go to vertex `0`, a noninjective left
  endpoint map. The gap and the ray star `J 0 = (-∞, 1)` both have two components; both branches
  map to the class of vertex `0` (a star with two incident branches), and the right incidence
  `K 0 ≤ J 1` sends edge `y` to vertex `y`.
* The proper inclusion `K 0 ≤ J 0` into the ray crosses the level `0`, outside the
  equal-level condition, and merges the two branches: it is not injective.
* The regular interval `(1/4, 3/4)` avoids every level, has a nonempty inverse image with two
  components, and its inclusion into the gap is bijective.
* Empty values: on the lower tail for `n = 0` and on `(2, 3)` above all levels of the pinch.
* Height independence: the realized map of the pinch reversing the edges has the same regular
  fiber map, the reversal, at the heights `1/2` and `3/4`; it is not the identity.
  The edge component bijections at the two heights agree.
* `n = 2`: in the bounded middle star `J 1 = (0, 2)` one edge comes from below (right incidence)
  and one from above (left incidence); they land in different components.
-/

open Set CategoryTheory

namespace TDA.Reeb

noncomputable section

namespace Examples.ConstructibleCylinder

open CylinderPresentation OpenInterval TDA.Reeb.Examples.Cylinder

theorem natCard_zerothHomotopy_discrete (A : Type*) [TopologicalSpace A] [DiscreteTopology A] :
    Nat.card (ZerothHomotopy A) = Nat.card A :=
  Nat.card_congr (zerothHomotopyEquivOfDiscrete A)

/-! #### `n = 0`: two points at one level -/

/-- One level `0`. -/
def S0 : CriticalValues 0 where
  value _ := 0
  strictMono a b h := absurd h (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; exact lt_irrefl _)

/-- Two vertices, no edges. -/
def D0 : FiniteReebData.{0} 0 :=
  ⟨fun _ => Fin 2, fun e => e.elim0, fun _ => inferInstance, fun e => e.elim0,
    fun e => e.elim0, fun e => e.elim0⟩

/-- The value on `ℝ` has two elements. -/
theorem n0_card_top : Nat.card ((intervalComponents ((ofFiniteData D0).height S0)).obj ⊤) = 2 := by
  rw [← S0.J_eq_top_of_zero, ← Nat.card_congr ((ofFiniteData D0).vertexComponentsEquiv S0 0),
    natCard_zerothHomotopy_discrete]
  exact Nat.card_fin 2

/-- Inclusion into `ℝ` of a bounded interval with the same level is bijective. -/
theorem n0_bijective_into_top :
    Function.Bijective ((intervalComponents ((ofFiniteData D0).height S0)).map
      (homOfLE (le_top : ioo (-1) 1 ≤ ⊤))) :=
  (ofFiniteData D0).intervalComponents_map_bijective S0 le_top ⟨0, show (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1 by norm_num⟩
    fun i => iff_of_true (by simp [S0, mem_ioo]) trivial

/-- Exterior values are empty. -/
theorem n0_lowerTail_isEmpty :
    IsEmpty ((intervalComponents ((ofFiniteData D0).height S0)).obj S0.lowerTail) :=
  (ofFiniteData D0).isEmpty_intervalComponents_lowerTail S0

/-! #### Pinch: noninjective left endpoint, two branches at one vertex -/

/-- Two edges over `(0, 1)`; both bottom ends go to vertex `0` at level `0` (vertex `1` at level
`0` is isolated); the top ends go to the two vertices at level `1`. -/
def DP : FiniteReebData.{0} 1 :=
  ⟨fun _ => Fin 2, fun _ => Fin 2, fun _ => inferInstance, fun _ => inferInstance,
    fun _ _ => 0, fun _ y => y⟩

/-- Shorthand for the height of the pinch realization. -/
abbrev hP : C((ofFiniteData DP).Realization S01, ℝ) := (ofFiniteData DP).height S01

theorem pinch_card_K : Nat.card ((intervalComponents hP).obj (S01.K 0)) = 2 := by
  rw [← Nat.card_congr ((ofFiniteData DP).edgeComponentsEquiv S01 0 half),
    natCard_zerothHomotopy_discrete]
  exact Nat.card_fin 2

/-- The star `J 0` has two classes: vertex `0` with its two branches, and the isolated
vertex `1`. -/
theorem pinch_card_J0 : Nat.card ((intervalComponents hP).obj (S01.J 0)) = 2 := by
  rw [← Nat.card_congr ((ofFiniteData DP).vertexComponentsEquiv S01 0),
    natCard_zerothHomotopy_discrete]
  exact Nat.card_fin 2

/-- Star with two incident branches: both edge classes over `K 0` map to the class of
vertex `0` in `J 0`. -/
theorem pinch_two_branches (y : Fin 2) :
    (intervalComponents hP).map (homOfLE (S01.K_le_J_castSucc 0))
        ((ofFiniteData DP).edgeComponentsEquiv S01 0 half
          (.mk (show (ofFiniteData DP).E 0 from y))) =
      (ofFiniteData DP).vertexComponentsEquiv S01 0
        (.mk (show (ofFiniteData DP).V 0 from (0 : Fin 2))) :=
  (ofFiniteData DP).map_K_le_J_castSucc_edgeComponentsEquiv S01 0 half _

/-- The star `J 0 = (-∞, 1)` is a ray. -/
theorem pinch_J0_mem_iff (x : ℝ) : x ∈ S01.J 0 ↔ x < 1 := by
  rw [S01.mem_J_iff]
  constructor
  · intro h
    simpa using h.2 1 rfl
  · intro h
    refine ⟨fun k hk => by simp at hk, fun k hk => ?_⟩
    obtain rfl : k = 1 := Fin.ext (by simpa using hk.symm)
    simpa using h

/-- The inclusion `K 0 ≤ J 0` crosses the level `0` (outside the bijectivity clause) and merges
the two branches: it is not injective. -/
theorem pinch_map_not_injective :
    ¬ Function.Injective ((intervalComponents hP).map (homOfLE (S01.K_le_J_castSucc 0))) := by
  intro hinj
  have h0 := (ofFiniteData DP).map_K_le_J_castSucc_edgeComponentsEquiv S01 0 half (.mk (show (ofFiniteData DP).E 0 from (0 : Fin 2)))
  have h1 := (ofFiniteData DP).map_K_le_J_castSucc_edgeComponentsEquiv S01 0 half (.mk (show (ofFiniteData DP).E 0 from (1 : Fin 2)))
  have heq := hinj (h0.trans h1.symm)
  have hmk := Equiv.injective _ heq
  have h01 := joined_eq_of_discrete (A := (ofFiniteData DP).E 0) (Quotient.exact hmk)
  exact absurd h01 (by decide : (0 : Fin 2) ≠ 1)

theorem quarter_le_K : ioo (1 / 4) (3 / 4) ≤ S01.K 0 := fun x hx => by
  rw [S01.mem_K]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
  rw [mem_ioo] at hx
  constructor <;> linarith [hx.1, hx.2]

/-- A regular interval avoiding every level, with nonempty preimage: the inclusion into the gap
is bijective, and the value has two elements. -/
theorem pinch_regular_bijective :
    Function.Bijective ((intervalComponents hP).map (homOfLE quarter_le_K)) :=
  (ofFiniteData DP).intervalComponents_map_bijective S01 quarter_le_K
    ⟨1 / 2, show (1 / 4 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 3 / 4 by norm_num⟩
    fun i => iff_of_false (fun h => S01.value_notMem_K 0 i (quarter_le_K h))
      (S01.value_notMem_K 0 i)

theorem pinch_card_regular : Nat.card ((intervalComponents hP).obj (ioo (1 / 4) (3 / 4))) = 2 :=
  (Nat.card_congr (Equiv.ofBijective _ pinch_regular_bijective)).trans pinch_card_K

theorem pinch_isConstructibleAt : S01.IsConstructibleAt (intervalComponents hP) :=
  finiteData_isConstructibleAt S01 DP

/-- Empty value above the levels. -/
theorem pinch_above_isEmpty : IsEmpty ((intervalComponents hP).obj (ioo 2 3)) :=
  pinch_isConstructibleAt.isEmpty_of_le_upperTail fun x hx => by
    rw [S01.mem_upperTail]
    rw [mem_ioo] at hx
    simp only [Fin.last, S01]
    norm_num
    linarith [hx.1]

/-- Right incidence on the pinch: `K 0 ≤ J 1` sends the class of edge `y` to vertex `y`. -/
theorem pinch_right_incidence (y : Fin 2) :
    (intervalComponents hP).map (homOfLE (S01.K_le_J_succ 0))
        ((ofFiniteData DP).edgeComponentsEquiv S01 0 half
          (.mk (show (ofFiniteData DP).E 0 from y))) =
      (ofFiniteData DP).vertexComponentsEquiv S01 1
        (.mk (show (ofFiniteData DP).V 1 from y)) :=
  (ofFiniteData DP).map_K_le_J_succ_edgeComponentsEquiv S01 0 half _

/-! #### Height independence for a realized map of the pinch -/

/-- The map of the pinch data fixing level `0` and reversing level `1` and the edges. -/
def swapDP : DP.Hom DP where
  v := Fin.cases id fun _ => Fin.rev
  e _ := Fin.rev
  left_comm i _ := by rw [Subsingleton.elim i 0]; rfl
  right_comm i _ := by rw [Subsingleton.elim i 0]; rfl

/-- The regular height `3/4` of the pinch gap. -/
def threeQuarters : (S01.K 0 : Set ℝ) := ⟨3 / 4, by
  show S01.value (Fin.castSucc 0) < 3 / 4 ∧ 3 / 4 < S01.value (Fin.succ 0)
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
  norm_num⟩

/-- At every regular height the realized swap reverses the two edges. -/
theorem pinch_swap_regularFiberMap (t : (S01.K 0 : Set ℝ)) (y : (ofFiniteData DP).E 0) :
    regularFiberMap S01 (realizeHom S01 swapDP) (height_realizeHom S01 swapDP) 0 t y =
      Fin.rev (show Fin 2 from y) := by
  rw [regularFiberMap_realizeHom]
  rfl

/-- Height independence on the pinch: the regular fiber maps of the realized swap at `1/2` and
`3/4` agree, and are not the identity. -/
theorem pinch_swap_regularFiberMap_indep :
    regularFiberMap S01 (realizeHom S01 swapDP) (height_realizeHom S01 swapDP) 0 half =
        regularFiberMap S01 (realizeHom S01 swapDP) (height_realizeHom S01 swapDP) 0
          threeQuarters ∧
      regularFiberMap S01 (realizeHom S01 swapDP) (height_realizeHom S01 swapDP) 0 half ≠
        ContinuousMap.id _ := by
  refine ⟨regularFiberMap_indep_of_discrete S01 _ _ 0 half threeQuarters, fun h => ?_⟩
  have h0 := pinch_swap_regularFiberMap half (show Fin 2 from 0)
  rw [h] at h0
  change (0 : Fin 2) = Fin.rev 0 at h0
  exact absurd h0 (by decide)

/-- The edge component bijection of the pinch is the same at the heights `1/2` and `3/4`. -/
theorem pinch_edgeComponentsEquiv_indep (y : Fin 2) :
    (ofFiniteData DP).edgeComponentsEquiv S01 0 half (.mk (show (ofFiniteData DP).E 0 from y)) =
      (ofFiniteData DP).edgeComponentsEquiv S01 0 threeQuarters
        (.mk (show (ofFiniteData DP).E 0 from y)) := by
  rw [(ofFiniteData DP).edgeComponentsEquiv_indep S01 0 half threeQuarters]

/-! #### `n = 2`: a bounded star with one edge below and one above -/

/-- Levels `0 < 1 < 2`. -/
def S012 : CriticalValues 2 where
  value i := ((i : ℕ) : ℝ)
  strictMono _ _ h := Nat.cast_lt.2 h

/-- Two vertices at each level, one edge per gap. The lower edge ends at vertex `0` of level
`1`; the upper edge starts at vertex `1` of level `1`. -/
def D2 : FiniteReebData.{0} 2 :=
  ⟨fun _ => Fin 2, fun _ => Fin 1, fun _ => inferInstance, fun _ => inferInstance,
    fun _ _ => 1, fun _ _ => 0⟩

/-- Shorthand for the height of the bounded-star realization. -/
abbrev h2 : C((ofFiniteData D2).Realization S012, ℝ) := (ofFiniteData D2).height S012

/-- The regular height `1/2` of the lower gap. -/
def t0 : (S012.K 0 : Set ℝ) := ⟨1 / 2, by
  show S012.value (Fin.castSucc 0) < 1 / 2 ∧ 1 / 2 < S012.value (Fin.succ 0)
  simp [S012]
  norm_num⟩

/-- The regular height `3/2` of the upper gap. -/
def t1 : (S012.K 1 : Set ℝ) := ⟨3 / 2, by
  show S012.value (Fin.castSucc 1) < 3 / 2 ∧ 3 / 2 < S012.value (Fin.succ 1)
  simp [S012]
  norm_num⟩

/-- The middle star `J 1 = (0, 2)` is bounded. -/
theorem bounded_J1_mem_iff (x : ℝ) : x ∈ S012.J 1 ↔ 0 < x ∧ x < 2 := by
  rw [S012.mem_J_iff]
  constructor
  · intro h
    exact ⟨by simpa [S012] using h.1 0 rfl, by simpa [S012] using h.2 2 rfl⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · obtain rfl : k = 0 := Fin.ext (by simpa using hk)
      simpa [S012] using h₁
    · obtain rfl : k = 2 := Fin.ext (by simpa using hk.symm)
      simpa [S012] using h₂

theorem bounded_card_J1 : Nat.card ((intervalComponents h2).obj (S012.J 1)) = 2 := by
  rw [← Nat.card_congr ((ofFiniteData D2).vertexComponentsEquiv S012 1),
    natCard_zerothHomotopy_discrete]
  exact Nat.card_fin 2

/-- Lower edge into the bounded star (right incidence). -/
theorem bounded_lower :
    (intervalComponents h2).map (homOfLE (S012.K_le_J_succ 0))
        ((ofFiniteData D2).edgeComponentsEquiv S012 0 t0
          (.mk (show (ofFiniteData D2).E 0 from (0 : Fin 1)))) =
      (ofFiniteData D2).vertexComponentsEquiv S012 (Fin.succ 0)
        (.mk (show (ofFiniteData D2).V (Fin.succ 0) from (0 : Fin 2))) :=
  (ofFiniteData D2).map_K_le_J_succ_edgeComponentsEquiv S012 0 t0 _

/-- Upper edge into the bounded star (left incidence). -/
theorem bounded_upper :
    (intervalComponents h2).map (homOfLE (S012.K_le_J_castSucc 1))
        ((ofFiniteData D2).edgeComponentsEquiv S012 1 t1
          (.mk (show (ofFiniteData D2).E 1 from (0 : Fin 1)))) =
      (ofFiniteData D2).vertexComponentsEquiv S012 (Fin.castSucc 1)
        (.mk (show (ofFiniteData D2).V (Fin.castSucc 1) from (1 : Fin 2))) :=
  (ofFiniteData D2).map_K_le_J_castSucc_edgeComponentsEquiv S012 1 t1 _

/-- In the bounded star the two incident edges land in different components. -/
theorem bounded_separates :
    (intervalComponents h2).map (homOfLE (S012.K_le_J_succ 0))
        ((ofFiniteData D2).edgeComponentsEquiv S012 0 t0
          (.mk (show (ofFiniteData D2).E 0 from (0 : Fin 1)))) ≠
      (intervalComponents h2).map (homOfLE (S012.K_le_J_castSucc 1))
        ((ofFiniteData D2).edgeComponentsEquiv S012 1 t1
          (.mk (show (ofFiniteData D2).E 1 from (0 : Fin 1)))) := by
  rw [bounded_lower, bounded_upper]
  intro h
  have hmk := ((ofFiniteData D2).vertexComponentsEquiv S012 1).injective h
  have h01 := joined_eq_of_discrete (A := (ofFiniteData D2).V 1) (Quotient.exact hmk)
  exact absurd h01 (by decide : (0 : Fin 2) ≠ 1)

end Examples.ConstructibleCylinder

end

end TDA.Reeb
