import TDA.Mapper.RefinementHomologyDiagram
import TDA.Persistence.DiagramBottleneckLaws
import TDA.Reeb.GraphPLVertexPerturbation

/-!
# Capped centred step towers

Fix a label window `W`, integer labels `ℓ : W → ℤ`, a base `a` and a spacing `s`. The centred
interval of radius `r` about the label `w` is `(a + ℓ w * s - r, a + ℓ w * s + r)`. For a strictly
increasing grid of radii `c : Fin m ↪o ℝ`, the capped centred step data have no labels at stage
`0`, the centred intervals of radius `c j` at stage `j + 1` for `j + 1 < m`, and the whole line
`ℝ` for every label at the last stage. The stage radius `stageRadius c` in `EReal` is `⊥` at
stage `0`, `c j` at stage `j + 1 < m` and `⊤` at the last stage; membership in a stage member is
distance to the centre less than the stage radius, and the stage refinements select the same
label. For `f : C(X, ℝ)` with supplied component orders and finitely many Mapper faces of degree
`n` at every stage, the capped centred diagram is the step diagram of these data; the field, `X`
and `W` lie in one universe.

Let `f g : C(X, ℝ)` satisfy `|f x - g x| ≤ δ` for every `x`. If the stage radius at `t` plus `δ`
is at most the stage radius at `t + η` on a second grid, the pulled-back stages admit cover maps
with identity selectors; in both directions, they bound the bottleneck distance of the two
capped centred diagrams by `η`. Three consequences follow.

* **Perturbation.** On one grid whose consecutive radii differ by at most `μ`, the bottleneck
  distance of the diagrams of `f` and `g` is at most `δ + μ`; on a uniform grid of spacing `h`
  with `δ = p * h` for a natural number `p`, it is at most `δ`.
* **Mesh comparison.** For one map and two grids, each of mesh at most `η`, whose first radii and
  whose last radii differ by at most `η`, the bottleneck distance is at most `η`. Combined with
  the perturbation bound by the triangle inequality, it bounds diagrams of two maps on two grids.
* **Graph-PL heights.** For the piecewise-linear heights of two vertex-height functions on a
  finite graph within `ε` at every vertex and a finite label window, every finiteness hypothesis
  holds by instance and the bottleneck distance is at most `ε + μ`, or `ε` on a uniform grid with
  `ε = p * h`.

The last stage is the cap: without it a member of the largest finite radius for `f` need not lie
in any member of the same radius for `g`. No coverage of the attained range by a capped stage is
claimed. Nothing is stated about diagrams of the `ℤ`-labelled centred tower itself, sharpness of
`δ + μ`, the limit of vanishing mesh, the multiscale Mapper diagrams of `(c, s)`-good towers in
DMW16-v2, step towers whose stages are not centred intervals, independence of the component
orders, multinerve Mapper or executable extraction.
-/

namespace TDA.Mapper

open TDA.Topology
open TDA.Simplicial
open TDA.Persistence
open TDA.Persistence.FiniteConstructible
open TDA.Reeb
open scoped NNReal ENNReal

noncomputable section

universe u

/-! ## Centred intervals and stage radii -/

section Tower

variable {W : Type u} (a s : ℝ) (ℓ : W → ℤ)

/-- The open interval of radius `r` about `a + ℓ w * s`. It is empty when `r ≤ 0`. -/
def centredInterval (r : ℝ) (w : W) : OpenInterval :=
  OpenInterval.ioo (a + ℓ w * s - r) (a + ℓ w * s + r)

/-- Membership in a centred interval is distance less than the radius from its centre. -/
theorem mem_centredInterval_iff {r y : ℝ} {w : W} :
    y ∈ centredInterval a s ℓ r w ↔ |y - (a + ℓ w * s)| < r := by
  change y ∈ Set.Ioo _ _ ↔ _
  rw [Set.mem_Ioo, abs_sub_lt_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- With base `0`, the centred interval of the label `w` is the member of label `ℓ w` of the
centred family `centredCover s r`. -/
theorem coe_centredInterval_zero (r : ℝ) (w : W) :
    (centredInterval 0 s ℓ r w : Set ℝ) = centredCover s r (ℓ w) := by
  simp [centredInterval, centredCover]

variable (W) in
/-- The stage index types: no labels at stage `0` and the label window at every later stage. -/
def cappedIndex {m : ℕ} : Fin (m + 1) → Type u :=
  Fin.cases PEmpty.{u + 1} fun _ => W

/-- Stage `0` has no labels. -/
instance isEmpty_cappedIndex_zero {m : ℕ} : IsEmpty (cappedIndex W (0 : Fin (m + 1))) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- A finite label window gives finitely many labels at every stage. -/
instance finite_cappedIndex [Finite W] {m : ℕ} (i : Fin (m + 1)) : Finite (cappedIndex W i) :=
  Fin.cases (motive := fun i => Finite (cappedIndex W i)) (inferInstanceAs (Finite PEmpty))
    (fun _ => inferInstanceAs (Finite W)) i

variable {m : ℕ} (c : Fin m ↪o ℝ)

/-- The capped centred stages on the grid `c`: no members at stage `0`, the centred intervals of
radius `c j` at stage `j + 1` for `j + 1 < m`, and `ℝ` for every label at the last stage. -/
def cappedCentredCover : (i : Fin (m + 1)) → cappedIndex W i → OpenInterval :=
  Fin.cases (motive := fun i => cappedIndex W i → OpenInterval) (fun e => isEmptyElim e)
    fun j w => if j.val + 1 = m then ⊤ else centredInterval a s ℓ (c j) w

/-- Stage `j + 1 < m + 1` is the centred family of radius `c j`. -/
theorem cappedCentredCover_succ_of_lt (j : Fin m) (hj : j.val + 1 < m) (w : W) :
    cappedCentredCover a s ℓ c j.succ w = centredInterval a s ℓ (c j) w :=
  if_neg hj.ne

/-- The last stage is the full line for every label. -/
theorem cappedCentredCover_last (j : Fin m) (hj : j.val + 1 = m) (w : W) :
    cappedCentredCover a s ℓ c j.succ w = ⊤ :=
  if_pos hj

/-- The stage radii of the grid `c`: `⊥` at stage `0`, `c j` at stage `j + 1` for `j + 1 < m`,
and `⊤` at the last stage. -/
def stageRadius : Fin (m + 1) → EReal :=
  Fin.cases ⊥ fun j => if j.val + 1 = m then ⊤ else (c j : EReal)

/-- Stage `0` has radius `⊥`. -/
@[simp]
theorem stageRadius_zero : stageRadius c 0 = ⊥ :=
  rfl

/-- Stage `j + 1 < m + 1` has radius `c j`. -/
theorem stageRadius_succ_of_lt (j : Fin m) (hj : j.val + 1 < m) :
    stageRadius c j.succ = c j :=
  if_neg hj.ne

/-- The last stage has radius `⊤`. -/
theorem stageRadius_last (j : Fin m) (hj : j.val + 1 = m) : stageRadius c j.succ = ⊤ :=
  if_pos hj

/-- Only stage `0` has radius `⊥`. -/
theorem stageRadius_eq_bot_iff {i : Fin (m + 1)} : stageRadius c i = ⊥ ↔ i = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · rfl
  · by_cases hj : j.val + 1 = m
    · rw [stageRadius_last c j hj] at h
      exact absurd h (by simp)
    · rw [stageRadius_succ_of_lt c j (lt_of_le_of_ne j.isLt hj)] at h
      exact absurd h (EReal.coe_ne_bot _)

/-- Stage radii increase along the stages. -/
theorem stageRadius_mono : Monotone (stageRadius c) := by
  intro i i' h
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · exact bot_le
  obtain rfl | ⟨j', rfl⟩ := i'.eq_zero_or_eq_succ
  · exact absurd h (by simp)
  have hjj' : j ≤ j' := Fin.succ_le_succ_iff.mp h
  by_cases hj' : j'.val + 1 = m
  · rw [stageRadius_last c j' hj']
    exact le_top
  have hlt' : j'.val + 1 < m := lt_of_le_of_ne j'.isLt hj'
  have hlt : j.val + 1 < m := lt_of_le_of_lt (Nat.succ_le_succ hjj') hlt'
  rw [stageRadius_succ_of_lt c j hlt, stageRadius_succ_of_lt c j' hlt']
  exact EReal.coe_le_coe_iff.mpr (c.monotone hjj')

/-- Membership in a positive stage is distance to the centre less than the stage radius. -/
theorem mem_cappedCentredCover_succ_iff (j : Fin m) (w : W) (y : ℝ) :
    y ∈ cappedCentredCover a s ℓ c j.succ w ↔
      ((|y - (a + ℓ w * s)| : ℝ) : EReal) < stageRadius c j.succ := by
  by_cases hj : j.val + 1 = m
  · rw [cappedCentredCover_last a s ℓ c j hj, stageRadius_last c j hj]
    exact ⟨fun _ => EReal.coe_lt_top _, fun _ => Set.mem_univ y⟩
  · have hlt : j.val + 1 < m := lt_of_le_of_ne j.isLt hj
    rw [cappedCentredCover_succ_of_lt a s ℓ c j hlt, stageRadius_succ_of_lt c j hlt,
      EReal.coe_lt_coe_iff]
    exact mem_centredInterval_iff a s ℓ

/-- The label selector between two stages: empty out of stage `0`, the identity of `W`
otherwise. -/
private def stageSelector {m m' : ℕ} (i : Fin (m + 1)) (j : Fin (m' + 1)) (h : j = 0 → i = 0) :
    cappedIndex W i → cappedIndex W j :=
  Fin.cases (motive := fun i => (j = 0 → i = 0) → cappedIndex W i → cappedIndex W j)
    (fun _ e => isEmptyElim e)
    (fun i' h => Fin.cases
      (motive := fun j => (j = 0 → i'.succ = 0) → cappedIndex W i'.succ → cappedIndex W j)
      (fun h => absurd (h rfl) (Fin.succ_ne_zero i')) (fun _ _ w => (w : W)) j h) i h

variable {a s ℓ c}

private theorem eq_zero_of_stageRadius_le {m' : ℕ} {d : Fin m' ↪o ℝ} {δ : ℝ}
    {i : Fin (m + 1)} {j : Fin (m' + 1)} (h : stageRadius c i + δ ≤ stageRadius d j) :
    j = 0 → i = 0 := by
  rintro rfl
  rw [stageRadius_zero, le_bot_iff] at h
  rcases EReal.add_eq_bot_iff.mp h with h | h
  · exact (stageRadius_eq_bot_iff c).mp h
  · exact absurd h (EReal.coe_ne_bot δ)

/-- A point within `δ` of a point of a stage member lies in the member with the same label of a
stage whose radius exceeds the first by at least `δ`. -/
private theorem mem_cappedCentredCover_of_stageRadius_le {m' : ℕ} {d : Fin m' ↪o ℝ} {δ : ℝ}
    {i : Fin (m + 1)} {j : Fin (m' + 1)} (h : stageRadius c i + δ ≤ stageRadius d j)
    (w : cappedIndex W i) {y z : ℝ} (hyz : |z - y| ≤ δ)
    (hy : y ∈ cappedCentredCover a s ℓ c i w) :
    z ∈ cappedCentredCover a s ℓ d j (stageSelector i j (eq_zero_of_stageRadius_le h) w) := by
  obtain rfl | ⟨i', rfl⟩ := i.eq_zero_or_eq_succ
  · exact isEmptyElim w
  obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
  · exact absurd (eq_zero_of_stageRadius_le h rfl) (Fin.succ_ne_zero i')
  have hy' := (mem_cappedCentredCover_succ_iff a s ℓ c i' w y).mp hy
  refine (mem_cappedCentredCover_succ_iff a s ℓ d j' w z).mpr ?_
  have hz : |z - (a + ℓ w * s)| ≤ |y - (a + ℓ w * s)| + δ := by
    calc |z - (a + ℓ w * s)| ≤ |z - y| + |y - (a + ℓ w * s)| := abs_sub_le _ _ _
      _ ≤ |y - (a + ℓ w * s)| + δ := by linarith
  calc ((|z - (a + ℓ w * s)| : ℝ) : EReal) ≤ ((|y - (a + ℓ w * s)| + δ : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr hz
    _ = ((|y - (a + ℓ w * s)| : ℝ) : EReal) + δ := EReal.coe_add _ _
    _ < stageRadius c i'.succ + δ := EReal.add_lt_add_right_coe hy' δ
    _ ≤ stageRadius d j'.succ := h

variable (a s ℓ c)

/-- The refinement of a capped centred stage by a later stage selects the same label. -/
def cappedCentredRefinement {i j : Fin (m + 1)} (h : i ≤ j) :
    Refinement (fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))
      (fun w => (cappedCentredCover a s ℓ c j w : Set ℝ)) where
  selector := stageSelector i j (eq_zero_of_stageRadius_le (δ := 0) (by
    simpa using stageRadius_mono c h))
  subset w _ hy := mem_cappedCentredCover_of_stageRadius_le (δ := 0)
    (by simpa using stageRadius_mono c h) w (by simp) hy

variable {X : Type u} [TopologicalSpace X]

/-- **Cover maps from radius domination.** If `|f x - g x| ≤ δ` for every `x` and the stage
radius of `i` plus `δ` is at most the stage radius of `j` on a grid `d`, then the pulled-back
stage `i` of `f` refines the pulled-back stage `j` of `g` with the same labels. -/
def cappedCentredPullbackRefinement {m' : ℕ} (d : Fin m' ↪o ℝ) {f g : C(X, ℝ)} {δ : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ δ) {i : Fin (m + 1)} {j : Fin (m' + 1)}
    (h : stageRadius c i + (δ : ℝ) ≤ stageRadius d j) :
    Refinement (pullback f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))
      (pullback g fun w => (cappedCentredCover a s ℓ d j w : Set ℝ)) where
  selector := stageSelector i j (eq_zero_of_stageRadius_le h)
  subset w x hx := mem_cappedCentredCover_of_stageRadius_le h w
    (by rw [abs_sub_comm]; exact hfg x) hx

end Tower

/-! ## Capped centred diagrams -/

section Diagram

variable (k : Type u) [Field k] {X : Type u} [TopologicalSpace X] {W : Type u}

/-- The degree-`n` capped centred diagram of `f`: the step diagram of the capped centred stages
on the grid `c`. -/
def cappedCentredDiagram (f : C(X, ℝ)) (a s : ℝ) (ℓ : W → ℤ) {m : ℕ} (c : Fin m ↪o ℝ) (n : ℕ)
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)] :
    Diagram ℝ :=
  stepMapperDiagram k f c (fun i w => (cappedCentredCover a s ℓ c i w : Set ℝ))
    (fun h => cappedCentredRefinement a s ℓ c h) n

variable (f : C(X, ℝ)) (a s : ℝ) (ℓ : W → ℤ) {m : ℕ} (c : Fin m ↪o ℝ) (n : ℕ)
  [hf : ∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
  [hF : ∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]

/-- The capped centred diagram of `f` is the step diagram of the identity of `X` along the
pulled-back stages, with pulled-back refinements and the same component orders. -/
theorem cappedCentredDiagram_eq_pullback :
    cappedCentredDiagram k f a s ℓ c n =
      @stepMapperDiagram X X _ _ k _ (ContinuousMap.id X) m c (cappedIndex W)
        (fun i => pullback f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) hf
        (fun h => pullbackRefinement f (cappedCentredRefinement a s ℓ c h)) n hF :=
  rfl

end Diagram

/-! ## Bottleneck bounds from radius domination -/

section Stability

variable (k : Type u) [Field k] {X : Type u} [TopologicalSpace X] {W : Type u}
  (a s : ℝ) (ℓ : W → ℤ) (n : ℕ)

/-- **Radius domination.** Let `|f x - g x| ≤ δ` for every `x`. If, in both directions, the
stage radius at `t` plus `δ` is at most the stage radius at `t + η` on the other grid, then the
capped centred diagrams of `f` on `c` and of `g` on `d` are at bottleneck distance at most
`η`. -/
theorem bottleneck_cappedCentredDiagram_le_of_stageRadius_le {f g : C(X, ℝ)} {m m' : ℕ}
    {c : Fin m ↪o ℝ} {d : Fin m' ↪o ℝ}
    [hf : ∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [hF : ∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [hg : ∀ i, LinearOrder (ComponentIndex g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ))]
    [hG : ∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ)) n)]
    {δ η : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ δ)
    (hcd : ∀ t, stageRadius c (cellIndex c t) + (δ : ℝ) ≤ stageRadius d (cellIndex d (t + η)))
    (hdc : ∀ t, stageRadius d (cellIndex d t) + (δ : ℝ) ≤ stageRadius c (cellIndex c (t + η))) :
    bottleneck (cappedCentredDiagram k f a s ℓ c n) (cappedCentredDiagram k g a s ℓ d n) ≤ η := by
  have hgf : ∀ x, |g x - f x| ≤ δ := fun x => by rw [abs_sub_comm]; exact hfg x
  rw [cappedCentredDiagram_eq_pullback, cappedCentredDiagram_eq_pullback]
  let : ∀ i, LinearOrder (ComponentIndex (ContinuousMap.id X)
      (pullback f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))) := hf
  let : ∀ i, Finite (Face (mapper (ContinuousMap.id X)
      (pullback f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))) n) := hF
  let : ∀ i, LinearOrder (ComponentIndex (ContinuousMap.id X)
      (pullback g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ))) := hg
  let : ∀ i, Finite (Face (mapper (ContinuousMap.id X)
      (pullback g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ))) n) := hG
  exact bottleneck_stepMapperDiagram_le k (ContinuousMap.id X) n _ _
    (fun t => cappedCentredPullbackRefinement a s ℓ c d hfg (hcd t))
    (fun t => cappedCentredPullbackRefinement a s ℓ d c hgf (hdc t))

/-- The bottleneck distance of the capped centred diagrams of `f` on `c` and of `g` on `d` is the
real interleaving distance of the two step modules. -/
theorem bottleneck_cappedCentredDiagram_eq {f g : C(X, ℝ)} {m m' : ℕ}
    {c : Fin m ↪o ℝ} {d : Fin m' ↪o ℝ}
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ))]
    [∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ)) n)] :
    bottleneck (cappedCentredDiagram k f a s ℓ c n) (cappedCentredDiagram k g a s ℓ d n) =
      realInterleavingDistance
        (mapperHomologyPModule k f (stepTower c fun i w => (cappedCentredCover a s ℓ c i w : Set ℝ))
          (stepRefinement c _ fun h => cappedCentredRefinement a s ℓ c h) n)
        (mapperHomologyPModule k g (stepTower d fun i w => (cappedCentredCover a s ℓ d i w : Set ℝ))
          (stepRefinement d _ fun h => cappedCentredRefinement a s ℓ d h) n) :=
  bottleneck_eq_distance (isConstructible_stepTower c _ k f _ n)
    (isConstructible_stepTower d _ k g _ n) _ _

/-! ### Cells of a grid -/

/-- Every radius lies in the zero cell, in the last cell, or in a cell `j + 1` with `j + 1 < m`
between `c j` and `c (j + 1)`. -/
private theorem cellIndex_cases {m : ℕ} (c : Fin m ↪o ℝ) (t : ℝ) :
    cellIndex c t = 0 ∨ (∃ j : Fin m, j.val + 1 = m ∧ cellIndex c t = j.succ ∧ c j ≤ t) ∨
      ∃ (j : Fin m) (hj : j.val + 1 < m),
        cellIndex c t = j.succ ∧ c j ≤ t ∧ t < c ⟨j.val + 1, hj⟩ := by
  obtain h | ⟨j, hj⟩ := (cellIndex c t).eq_zero_or_eq_succ
  · exact Or.inl h
  have hc := (cellIndex_eq_succ_iff c j t).mp hj
  by_cases hl : j.val + 1 = m
  · exact Or.inr (Or.inl ⟨j, hl, hj, hc.1⟩)
  · have hlt : j.val + 1 < m := lt_of_le_of_ne j.isLt hl
    exact Or.inr (Or.inr ⟨j, hlt, hj, hc.1, hc.2 _ (Fin.lt_def.mpr (Nat.lt_succ_self _))⟩)

/-- A radius at or above the last grid value lies in the last cell, of stage radius `⊤`. -/
private theorem stageRadius_cellIndex_of_last_le {m : ℕ} (c : Fin m ↪o ℝ) (j : Fin m)
    (hj : j.val + 1 = m) {u : ℝ} (hu : c j ≤ u) : stageRadius c (cellIndex c u) = ⊤ := by
  have : cellIndex c u = j.succ := (cellIndex_eq_succ_iff c j u).mpr
    ⟨hu, fun k hk => absurd (Fin.lt_def.mp hk) (by have := k.isLt; omega)⟩
  rw [this, stageRadius_last c j hj]

/-- A grid value at or below `u` bounds the stage radius at `u` from below. -/
private theorem le_stageRadius_cellIndex {m : ℕ} (c : Fin m ↪o ℝ) (q : Fin m) {u : ℝ}
    (hu : c q ≤ u) : (c q : EReal) ≤ stageRadius c (cellIndex c u) := by
  have hq := (lt_cellIndex_iff c q u).mpr hu
  rcases cellIndex_cases c u with h | ⟨j, hj, h, _⟩ | ⟨j, hj, h, _, _⟩
  · rw [h] at hq
    exact absurd hq (by simp)
  · rw [h, stageRadius_last c j hj]
    exact le_top
  · rw [h, stageRadius_succ_of_lt c j hj]
    rw [h, Fin.val_succ] at hq
    exact EReal.coe_le_coe_iff.mpr (c.monotone (Fin.le_def.mpr (by omega)))

/-- **Domination from meshes.** Let `d` have mesh at most `μ`, let `δ + μ ≤ η`, and let the first
and last radii of `d` exceed those of `c` by at most `η`. Then the stage radius of `c` at `t`
plus `δ` is at most the stage radius of `d` at `t + η`. -/
private theorem stageRadius_add_le_of_mesh {m m' : ℕ} (c : Fin (m + 1) ↪o ℝ)
    (d : Fin (m' + 1) ↪o ℝ) {δ μ η : ℝ}
    (hgap : ∀ i j : Fin (m' + 1), j.val = i.val + 1 → d j ≤ d i + μ) (hη : δ + μ ≤ η)
    (hfirst : d 0 ≤ c 0 + η) (hlast : d (Fin.last m') ≤ c (Fin.last m) + η) (t : ℝ) :
    stageRadius c (cellIndex c t) + δ ≤ stageRadius d (cellIndex d (t + η)) := by
  rcases cellIndex_cases c t with h | ⟨i, hi, h, hit⟩ | ⟨i, hi, h, hit, _⟩
  · rw [h, stageRadius_zero, EReal.bot_add]
    exact bot_le
  · have hi' : i = Fin.last m := Fin.ext (by simp; omega)
    subst hi'
    rw [stageRadius_cellIndex_of_last_le d (Fin.last m') (by simp) (by linarith)]
    exact le_top
  · rw [h, stageRadius_succ_of_lt c i hi]
    have hc0 : c 0 ≤ t := (c.monotone (Fin.zero_le i)).trans hit
    rcases cellIndex_cases d (t + η) with h' | ⟨j, hj, h', _⟩ | ⟨j, hj, h', _, hlt⟩
    · have := ((cellIndex_eq_zero_iff d _).mp h') 0
      linarith
    · rw [h', stageRadius_last d j hj]
      exact le_top
    · rw [h', stageRadius_succ_of_lt d j hj, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have := hgap j ⟨j.val + 1, hj⟩ rfl
      linarith

/-- On one grid of mesh at most `μ`, the stage radius at `t` plus `δ` is at most the stage
radius at `t + (δ + μ)`. -/
private theorem stageRadius_add_le_of_gap {m : ℕ} (c : Fin m ↪o ℝ) {δ μ : ℝ} (hδμ : 0 ≤ δ + μ)
    (hgap : ∀ i j : Fin m, j.val = i.val + 1 → c j ≤ c i + μ) (t : ℝ) :
    stageRadius c (cellIndex c t) + δ ≤ stageRadius c (cellIndex c (t + (δ + μ))) := by
  cases m with
  | zero =>
    rw [cellIndex_empty, stageRadius_zero, EReal.bot_add]
    exact bot_le
  | succ m => exact stageRadius_add_le_of_mesh c c hgap le_rfl (by linarith) (by linarith) t

/-! ### Perturbation and mesh comparison -/

/-- **Perturbation bound.** If `|f x - g x| ≤ δ` for every `x` and consecutive radii of the grid
`c` differ by at most `μ`, then the capped centred diagrams of `f` and `g` on `c` are at
bottleneck distance at most `δ + μ`. -/
theorem bottleneck_cappedCentredDiagram_le {f g : C(X, ℝ)} {m : ℕ} {c : Fin m ↪o ℝ}
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex g fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    {δ μ : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ δ)
    (hgap : ∀ i j : Fin m, j.val = i.val + 1 → c j ≤ c i + μ) :
    bottleneck (cappedCentredDiagram k f a s ℓ c n) (cappedCentredDiagram k g a s ℓ c n) ≤
      (δ : ℝ≥0∞) + μ := by
  have h : ∀ t, stageRadius c (cellIndex c t) + ((δ : ℝ≥0) : ℝ) ≤
      stageRadius c (cellIndex c (t + ((δ + μ : ℝ≥0) : ℝ))) := fun t => by
    rw [NNReal.coe_add]
    exact stageRadius_add_le_of_gap c (by positivity) hgap t
  rw [← ENNReal.coe_add]
  exact bottleneck_cappedCentredDiagram_le_of_stageRadius_le k a s ℓ n hfg h h

/-- **Mesh comparison.** For one map `f` and two grids `c`, `d` whose consecutive radii differ by
at most `η`, whose first radii differ by at most `η` and whose last radii differ by at most `η`,
the capped centred diagrams of `f` on `c` and on `d` are at bottleneck distance at most `η`. -/
theorem bottleneck_cappedCentredDiagram_grid_le {f : C(X, ℝ)} {m m' : ℕ}
    {c : Fin (m + 1) ↪o ℝ} {d : Fin (m' + 1) ↪o ℝ}
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ d i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ d i w : Set ℝ)) n)]
    {η : ℝ≥0} (hc : ∀ i j : Fin (m + 1), j.val = i.val + 1 → c j ≤ c i + η)
    (hd : ∀ i j : Fin (m' + 1), j.val = i.val + 1 → d j ≤ d i + η)
    (hfirst : |c 0 - d 0| ≤ η) (hlast : |c (Fin.last m) - d (Fin.last m')| ≤ η) :
    bottleneck (cappedCentredDiagram k f a s ℓ c n) (cappedCentredDiagram k f a s ℓ d n) ≤ η := by
  rw [abs_le] at hfirst hlast
  refine bottleneck_cappedCentredDiagram_le_of_stageRadius_le k a s ℓ n (δ := 0)
    (fun x => by simp) (fun t => ?_) (fun t => ?_)
  · simpa using stageRadius_add_le_of_mesh c d hd (δ := 0) (by simp) (by linarith)
      (by linarith) t
  · simpa using stageRadius_add_le_of_mesh d c hc (δ := 0) (by simp) (by linarith)
      (by linarith) t

/-- **Perturbation and mesh.** Under the hypotheses of the perturbation bound for `f`, `g` on `c`
and of the mesh comparison for `g` on `c` and `d`, the capped centred diagrams of `f` on `c` and
of `g` on `d` are at bottleneck distance at most `(δ + μ) + η`. -/
theorem bottleneck_cappedCentredDiagram_le_add {f g : C(X, ℝ)} {m m' : ℕ}
    {c : Fin (m + 1) ↪o ℝ} {d : Fin (m' + 1) ↪o ℝ}
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex g fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ))]
    [∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a s ℓ d i w : Set ℝ)) n)]
    {δ μ η : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ δ)
    (hgap : ∀ i j : Fin (m + 1), j.val = i.val + 1 → c j ≤ c i + μ)
    (hc : ∀ i j : Fin (m + 1), j.val = i.val + 1 → c j ≤ c i + η)
    (hd : ∀ i j : Fin (m' + 1), j.val = i.val + 1 → d j ≤ d i + η)
    (hfirst : |c 0 - d 0| ≤ η) (hlast : |c (Fin.last m) - d (Fin.last m')| ≤ η) :
    bottleneck (cappedCentredDiagram k f a s ℓ c n) (cappedCentredDiagram k g a s ℓ d n) ≤
      ((δ : ℝ≥0∞) + μ) + η :=
  (bottleneck_triangle _ (cappedCentredDiagram k g a s ℓ c n) _).trans
    (add_le_add (bottleneck_cappedCentredDiagram_le k a s ℓ n hfg hgap)
      (bottleneck_cappedCentredDiagram_grid_le k a s ℓ n hc hd hfirst hlast))

/-! ### Uniform grids -/

/-- The uniform grid of `m` radii `x₀ + i * h` of spacing `h > 0`. -/
def uniformGrid (x₀ h : ℝ) (hh : 0 < h) (m : ℕ) : Fin m ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i => x₀ + (i : ℕ) * h) fun i j hij => by
    have : ((i : ℕ) : ℝ) < (j : ℕ) := Nat.cast_lt.mpr hij
    dsimp only
    nlinarith

/-- The radius of index `i` of a uniform grid. -/
@[simp]
theorem uniformGrid_apply (x₀ h : ℝ) (hh : 0 < h) {m : ℕ} (i : Fin m) :
    uniformGrid x₀ h hh m i = x₀ + (i : ℕ) * h :=
  rfl

/-- Consecutive radii of a uniform grid differ by its spacing. -/
theorem uniformGrid_of_val_eq_succ (x₀ h : ℝ) (hh : 0 < h) {m : ℕ} {i j : Fin m}
    (hij : j.val = i.val + 1) : uniformGrid x₀ h hh m j = uniformGrid x₀ h hh m i + h := by
  simp only [uniformGrid_apply, hij]
  push_cast
  ring

/-- On a uniform grid of spacing `h`, the stage radius at `t` plus `p * h` is at most the stage
radius at `t + p * h`. -/
private theorem stageRadius_add_le_uniformGrid (x₀ h : ℝ) (hh : 0 < h) (m p : ℕ) (t : ℝ) :
    stageRadius (uniformGrid x₀ h hh m) (cellIndex (uniformGrid x₀ h hh m) t) + (p * h : ℝ) ≤
      stageRadius (uniformGrid x₀ h hh m) (cellIndex (uniformGrid x₀ h hh m) (t + p * h)) := by
  set c := uniformGrid x₀ h hh m
  have hp : (0 : ℝ) ≤ p * h := by positivity
  rcases cellIndex_cases c t with h₀ | ⟨j, hj, h₀, hjt⟩ | ⟨j, hj, h₀, hjt, _⟩
  · rw [h₀, stageRadius_zero, EReal.bot_add]
    exact bot_le
  · rw [stageRadius_cellIndex_of_last_le c j hj (u := t + p * h) (by linarith)]
    exact le_top
  · rw [h₀, stageRadius_succ_of_lt c j hj]
    have hjt' : x₀ + (j : ℕ) * h ≤ t := hjt
    by_cases hq : j.val + p < m
    · have hcq : c ⟨j.val + p, hq⟩ = c j + p * h := by
        simp only [c, uniformGrid_apply]
        push_cast
        ring
      have := le_stageRadius_cellIndex c ⟨j.val + p, hq⟩ (u := t + p * h) (by rw [hcq]; linarith)
      rwa [hcq, EReal.coe_add] at this
    · have hm : m - 1 + 1 = m := by omega
      have hL : c ⟨m - 1, by omega⟩ ≤ t + p * h := by
        simp only [c, uniformGrid_apply]
        have : ((m - 1 : ℕ) : ℝ) ≤ (j : ℕ) + p := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          have : (m : ℝ) ≤ (j : ℕ) + p + 1 := by exact_mod_cast (by omega : m ≤ j.val + p + 1)
          linarith
        nlinarith
      rw [stageRadius_cellIndex_of_last_le c ⟨m - 1, by omega⟩ hm hL]
      exact le_top

/-- **Exact multiples on a uniform grid.** If `|f x - g x| ≤ δ` for every `x` and `δ = p * h` for
a natural number `p`, then on the uniform grid of spacing `h` the capped centred diagrams of `f`
and `g` are at bottleneck distance at most `δ`. -/
theorem bottleneck_cappedCentredDiagram_uniformGrid_le {f g : C(X, ℝ)} (x₀ h : ℝ) (hh : 0 < h)
    (m : ℕ)
    [∀ i, LinearOrder (ComponentIndex f fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ)) n)]
    [∀ i, LinearOrder (ComponentIndex g fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ))]
    [∀ i, Finite (Face (mapper g fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hh m) i w : Set ℝ)) n)]
    {δ : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ δ) (p : ℕ) (hδ : (δ : ℝ) = p * h) :
    bottleneck (cappedCentredDiagram k f a s ℓ (uniformGrid x₀ h hh m) n)
      (cappedCentredDiagram k g a s ℓ (uniformGrid x₀ h hh m) n) ≤ δ := by
  have H : ∀ t, stageRadius (uniformGrid x₀ h hh m) (cellIndex (uniformGrid x₀ h hh m) t) +
      ((δ : ℝ≥0) : ℝ) ≤ stageRadius (uniformGrid x₀ h hh m)
        (cellIndex (uniformGrid x₀ h hh m) (t + ((δ : ℝ≥0) : ℝ))) := fun t => by
    rw [hδ]
    exact stageRadius_add_le_uniformGrid x₀ h hh m p t
  exact bottleneck_cappedCentredDiagram_le_of_stageRadius_le k a s ℓ n hfg H H

end Stability

/-! ## Graph-PL heights -/

section GraphPL

variable (k : Type u) [Field k] {V : Type u} [Finite V] (G : SimpleGraph V) {W : Type u}
  [Finite W] (a s : ℝ) (ℓ : W → ℤ) (n : ℕ) {h₁ h₂ : V → ℝ} {ε : ℝ≥0}

/-- **Graph-PL vertex heights.** For vertex heights within `ε` at every vertex of a finite graph,
a finite label window and a grid of mesh at most `μ`, the capped centred diagrams of the two
piecewise-linear heights are at bottleneck distance at most `ε + μ`. -/
theorem bottleneck_cappedCentredDiagram_plHeight_le (hh : ∀ v, |h₁ v - h₂ v| ≤ ε) {m : ℕ}
    {c : Fin m ↪o ℝ}
    [∀ i, LinearOrder (ComponentIndex (GraphPL.plHeight G h₁) fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, LinearOrder (ComponentIndex (GraphPL.plHeight G h₂) fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ))]
    {μ : ℝ≥0} (hgap : ∀ i j : Fin m, j.val = i.val + 1 → c j ≤ c i + μ) :
    bottleneck (cappedCentredDiagram k (GraphPL.plHeight G h₁) a s ℓ c n)
      (cappedCentredDiagram k (GraphPL.plHeight G h₂) a s ℓ c n) ≤ (ε : ℝ≥0∞) + μ :=
  bottleneck_cappedCentredDiagram_le k a s ℓ n (GraphPL.abs_plHeight_sub_le G hh) hgap

/-- **Graph-PL vertex heights on a uniform grid.** For vertex heights within `ε = p * h` at every
vertex of a finite graph and a finite label window, the capped centred diagrams of the two
piecewise-linear heights on the uniform grid of spacing `h` are at bottleneck distance at most
`ε`. -/
theorem bottleneck_cappedCentredDiagram_plHeight_uniformGrid_le (hh : ∀ v, |h₁ v - h₂ v| ≤ ε)
    (x₀ h : ℝ) (hpos : 0 < h) (m : ℕ)
    [∀ i, LinearOrder (ComponentIndex (GraphPL.plHeight G h₁) fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hpos m) i w : Set ℝ))]
    [∀ i, LinearOrder (ComponentIndex (GraphPL.plHeight G h₂) fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hpos m) i w : Set ℝ))]
    (p : ℕ) (hε : (ε : ℝ) = p * h) :
    bottleneck (cappedCentredDiagram k (GraphPL.plHeight G h₁) a s ℓ (uniformGrid x₀ h hpos m) n)
      (cappedCentredDiagram k (GraphPL.plHeight G h₂) a s ℓ (uniformGrid x₀ h hpos m) n) ≤ ε :=
  bottleneck_cappedCentredDiagram_uniformGrid_le k a s ℓ n x₀ h hpos m
    (GraphPL.abs_plHeight_sub_le G hh) p hε

end GraphPL

end

end TDA.Mapper
