import TDA.Persistence.RankErosion
import TDA.Persistence.CoordinateGridKan

/-!
# Finite test grids for rank erosion of grid Kan extensions

The rank of a structure map of the Kan extension of a module on a finite coordinate grid is
the rank of the structure map between the two floors, or zero where the source grade has no
lower grid point. Hence the two inequalities of `RankErosion ε` at a weak pair `a ≤ b` depend
only on which breakpoints — the values of the two grids and their shifts by `±ε` — lie below
each coordinate of `a` and of `b`.

Let `T` be a finite grid containing the breakpoints. If `a` has a lower point of `T`, taking
floors in `T` preserves this information and the order, so the inequalities at `(a, b)` are
those at a comparable pair of points of `T`. If `a` has no lower point of `T`, then the
lowered grade `a - ε` has no lower point of either grid, both left-hand ranks vanish and the
inequalities hold. So `RankErosion ε` is equivalent to its restriction to the points of `T`.

The original grid values alone do not suffice: the shifted values are needed.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.CoordinateGrid

open CategoryTheory
open scoped TDA.Persistence NNReal

variable {n : ℕ} {k : Type u} [Field k]

section Floor

variable (G : CoordinateGrid n)

/-- A grade has a lower grid point exactly when every coordinate has a grid value below it. -/
theorem hasLowerPoint_iff (a : Fin n → ℝ) :
    G.HasLowerPoint a ↔ ∀ i, ∃ g ∈ G i, g ≤ a i := by
  constructor
  · rintro ⟨p, hp⟩ i
    exact ⟨(p i).val, (p i).property, hp i⟩
  · intro h
    choose g hg hle using h
    exact ⟨fun i => ⟨g i, hg i⟩, hle⟩

/-- A grid value lies below a coordinate of the floor exactly when it lies below that
coordinate of the grade. -/
theorem le_floor_apply_iff (a : Fin n → ℝ) (ha : G.HasLowerPoint a) {i : Fin n} {c : ℝ}
    (hc : c ∈ G i) : c ≤ (G.floor a ha i).val ↔ c ≤ a i := by
  constructor
  · exact fun h => h.trans (G.floor_le a ha i)
  · intro h
    have hp : G.embedding (Function.update (G.floor a ha) i ⟨c, hc⟩) ≤ a := by
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using h
      · simpa [Function.update_of_ne hj] using G.floor_le a ha j
    have hle : Function.update (G.floor a ha) i ⟨c, hc⟩ i ≤ G.floor a ha i :=
      G.le_floor a ha hp i
    rw [Function.update_self] at hle
    exact hle

/-- Having a lower grid point depends only on which grid values lie below each coordinate. -/
theorem hasLowerPoint_congr {x y : Fin n → ℝ}
    (h : ∀ i, ∀ g ∈ G i, g ≤ x i ↔ g ≤ y i) : G.HasLowerPoint x ↔ G.HasLowerPoint y := by
  simp only [hasLowerPoint_iff]
  exact forall_congr' fun i => exists_congr fun g => and_congr_right fun hg => h i g hg

/-- The floor depends only on which grid values lie below each coordinate. -/
theorem floor_congr {x y : Fin n → ℝ} (h : ∀ i, ∀ g ∈ G i, g ≤ x i ↔ g ≤ y i)
    (hx : G.HasLowerPoint x) (hy : G.HasLowerPoint y) : G.floor x hx = G.floor y hy := by
  rw [G.floor_eq_iff x hx]
  refine ⟨fun i => (h i _ (G.floor y hy i).property).mpr (G.floor_le y hy i), fun q hq => ?_⟩
  exact G.le_floor y hy fun i => (h i _ (q i).property).mp (hq i)

end Floor

section Rank

variable (G : CoordinateGrid n) (M : PModule.{u,0,u} k G.Point)

/-- The rank of a structure map of the Kan extension is the rank between the two floors. -/
theorem rankOfStructureMap_lan {a b : Fin n → ℝ} (hab : a ≤ b) (ha : G.HasLowerPoint a) :
    rankOfStructureMap (G.lan.obj M) hab =
      rankOfStructureMap M (G.floor_mono hab ha (G.hasLowerPoint_mono hab ha)) := by
  have hb := G.hasLowerPoint_mono hab ha
  let ea : (G.lan.obj M).obj a ≃ₗ[k] M.obj (G.floor a ha) := (G.appIso M a ha).toLinearEquiv
  let eb : (G.lan.obj M).obj b ≃ₗ[k] M.obj (G.floor b hb) := (G.appIso M b hb).toLinearEquiv
  have hcomp : eb.toLinearMap.comp (structureMapLinear (G.lan.obj M) hab) =
      (structureMapLinear M (G.floor_mono hab ha hb)).comp ea.toLinearMap :=
    LinearMap.ext fun x => G.appIso_structureMap_apply M hab ha hb x
  unfold rankOfStructureMap
  have hrange : (LinearMap.range (structureMapLinear (G.lan.obj M) hab)).map eb.toLinearMap =
      LinearMap.range (structureMapLinear M (G.floor_mono hab ha hb)) := by
    rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp, LinearEquiv.range,
      Submodule.map_top]
  rw [← hrange]
  exact (LinearEquiv.finrank_map_eq eb _).symm

/-- Where the source grade has no lower grid point, every structure map of the Kan extension
has rank zero. -/
theorem rankOfStructureMap_lan_eq_zero {a b : Fin n → ℝ} (hab : a ≤ b)
    (ha : ¬ G.HasLowerPoint a) : rankOfStructureMap (G.lan.obj M) hab = 0 := by
  unfold rankOfStructureMap
  have hzero : structureMapLinear (G.lan.obj M) hab = 0 :=
    LinearMap.ext fun x => by rw [G.eq_zero_of_not_hasLowerPoint M a ha x]; simp
  rw [hzero, LinearMap.range_zero, finrank_bot]

open Classical in
/-- The rank of a structure map of the Kan extension, read on the grid in both cases. -/
theorem rankOfStructureMap_lan_eq_dite {a b : Fin n → ℝ} (hab : a ≤ b) :
    rankOfStructureMap (G.lan.obj M) hab =
      if ha : G.HasLowerPoint a then
        rankOfStructureMap M (G.floor_mono hab ha (G.hasLowerPoint_mono hab ha))
      else 0 := by
  split_ifs with ha
  · exact G.rankOfStructureMap_lan M hab ha
  · exact G.rankOfStructureMap_lan_eq_zero M hab ha

private theorem rankOfStructureMap_congr_endpoints {P : Type} [Preorder P]
    (M : PModule.{u,0,u} k P) {p q p' q' : P} (hp : p = p') (hq : q = q')
    (h : p ≤ q) (h' : p' ≤ q') : rankOfStructureMap M h = rankOfStructureMap M h' := by
  subst hp
  subst hq
  rfl

/-- The rank of a structure map of the Kan extension depends only on which grid values lie
below each coordinate of the two grades. -/
theorem rankOfStructureMap_lan_congr {a b a' b' : Fin n → ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    (ha : ∀ i, ∀ g ∈ G i, g ≤ a i ↔ g ≤ a' i) (hb : ∀ i, ∀ g ∈ G i, g ≤ b i ↔ g ≤ b' i) :
    rankOfStructureMap (G.lan.obj M) hab = rankOfStructureMap (G.lan.obj M) hab' := by
  by_cases hl : G.HasLowerPoint a
  · have hl' : G.HasLowerPoint a' := (G.hasLowerPoint_congr ha).mp hl
    rw [G.rankOfStructureMap_lan M hab hl, G.rankOfStructureMap_lan M hab' hl']
    exact rankOfStructureMap_congr_endpoints M (G.floor_congr ha hl hl')
      (G.floor_congr hb (G.hasLowerPoint_mono hab hl) (G.hasLowerPoint_mono hab' hl')) _ _
  · have hl' : ¬ G.HasLowerPoint a' := fun h => hl ((G.hasLowerPoint_congr ha).mpr h)
    rw [G.rankOfStructureMap_lan_eq_zero M hab hl, G.rankOfStructureMap_lan_eq_zero M hab' hl']

end Rank

section Breakpoints

/-- Per coordinate: the values of both grids and their shifts by `±ε`. -/
noncomputable def erosionBreakpoints (G H : CoordinateGrid n) (ε : ℝ≥0) : CoordinateGrid n :=
  fun i =>
    G i ∪ H i ∪ (G i).image (fun x => x + (ε : ℝ)) ∪ (G i).image (fun x => x - (ε : ℝ)) ∪
      (H i).image (fun x => x + (ε : ℝ)) ∪ (H i).image (fun x => x - (ε : ℝ))

variable {G H : CoordinateGrid n} {ε : ℝ≥0}

theorem mem_erosionBreakpoints {i : Fin n} {c : ℝ} :
    c ∈ erosionBreakpoints G H ε i ↔
      c ∈ G i ∨ c ∈ H i ∨ (∃ g ∈ G i, g + (ε : ℝ) = c) ∨ (∃ g ∈ G i, g - (ε : ℝ) = c) ∨
        (∃ h ∈ H i, h + (ε : ℝ) = c) ∨ (∃ h ∈ H i, h - (ε : ℝ) = c) := by
  simp only [erosionBreakpoints, Finset.mem_union, Finset.mem_image, or_assoc]

end Breakpoints

section Criterion

variable (G H : CoordinateGrid n) (M : PModule.{u,0,u} k G.Point)
  (N : PModule.{u,0,u} k H.Point) (ε : ℝ≥0)

/-- **Finite criterion for rank erosion.** For the Kan extensions of modules on two finite
coordinate grids, the weak-pair rank inequalities at radius `ε` hold at all real grades if and
only if they hold at the comparable pairs of points of a grid containing the breakpoints. -/
theorem rankErosion_lan_iff_of_subset {T : CoordinateGrid n}
    (hT : ∀ i, erosionBreakpoints G H ε i ⊆ T i) :
    RankErosion ε (G.lan.obj M) (H.lan.obj N) ↔
      ∀ (p q : T.Point) (hpq : p ≤ q),
        rankOfStructureMap (G.lan.obj M) (erosionWide_le ε (T.embedding.monotone hpq)) ≤
            rankOfStructureMap (H.lan.obj N) (T.embedding.monotone hpq) ∧
          rankOfStructureMap (H.lan.obj N) (erosionWide_le ε (T.embedding.monotone hpq)) ≤
            rankOfStructureMap (G.lan.obj M) (T.embedding.monotone hpq) := by
  constructor
  · intro h p q hpq
    exact ⟨h.1 _ _ (T.embedding.monotone hpq), h.2 _ _ (T.embedding.monotone hpq)⟩
  · intro h
    have key : ∀ (a b : Fin n → ℝ) (hab : a ≤ b),
        (rankOfStructureMap (G.lan.obj M) (erosionWide_le ε hab) ≤
            rankOfStructureMap (H.lan.obj N) hab) ∧
          (rankOfStructureMap (H.lan.obj N) (erosionWide_le ε hab) ≤
            rankOfStructureMap (G.lan.obj M) hab) := by
      intro a b hab
      by_cases hTa : T.HasLowerPoint a
      · have hTb : T.HasLowerPoint b := T.hasLowerPoint_mono hab hTa
        have hpq : T.floor a hTa ≤ T.floor b hTb := T.floor_mono hab hTa hTb
        have hGH := h _ _ hpq
        -- Taking floors in `T` does not move a grade across a breakpoint.
        have hbreak : ∀ (x : Fin n → ℝ) (hx : T.HasLowerPoint x) (i : Fin n) (c : ℝ),
            c ∈ erosionBreakpoints G H ε i →
              (c ≤ x i ↔ c ≤ T.embedding (T.floor x hx) i) :=
          fun x hx i c hc => (T.le_floor_apply_iff x hx (hT i hc)).symm
        have hG : ∀ (x : Fin n → ℝ) (hx : T.HasLowerPoint x) i, ∀ g ∈ G i,
            g ≤ x i ↔ g ≤ T.embedding (T.floor x hx) i :=
          fun x hx i g hg => hbreak x hx i g (mem_erosionBreakpoints.mpr (Or.inl hg))
        have hH : ∀ (x : Fin n → ℝ) (hx : T.HasLowerPoint x) i, ∀ g ∈ H i,
            g ≤ x i ↔ g ≤ T.embedding (T.floor x hx) i :=
          fun x hx i g hg => hbreak x hx i g (mem_erosionBreakpoints.mpr (Or.inr (Or.inl hg)))
        have hGlow : ∀ (x : Fin n → ℝ) (hx : T.HasLowerPoint x) i, ∀ g ∈ G i,
            g ≤ erosionLower ε x i ↔ g ≤ erosionLower ε (T.embedding (T.floor x hx)) i := by
          intro x hx i g hg
          have := hbreak x hx i (g + (ε : ℝ))
            (mem_erosionBreakpoints.mpr (Or.inr (Or.inr (Or.inl ⟨g, hg, rfl⟩))))
          simpa only [erosionLower, le_sub_iff_add_le] using this
        have hGup : ∀ (x : Fin n → ℝ) (hx : T.HasLowerPoint x) i, ∀ g ∈ G i,
            g ≤ erosionUpper ε x i ↔ g ≤ erosionUpper ε (T.embedding (T.floor x hx)) i := by
          intro x hx i g hg
          have := hbreak x hx i (g - (ε : ℝ))
            (mem_erosionBreakpoints.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g, hg, rfl⟩)))))
          simpa only [erosionUpper, ← sub_le_iff_le_add] using this
        have hHlow : ∀ (x : Fin n → ℝ) (hx : T.HasLowerPoint x) i, ∀ g ∈ H i,
            g ≤ erosionLower ε x i ↔ g ≤ erosionLower ε (T.embedding (T.floor x hx)) i := by
          intro x hx i g hg
          have := hbreak x hx i (g + (ε : ℝ))
            (mem_erosionBreakpoints.mpr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g, hg, rfl⟩))))))
          simpa only [erosionLower, le_sub_iff_add_le] using this
        have hHup : ∀ (x : Fin n → ℝ) (hx : T.HasLowerPoint x) i, ∀ g ∈ H i,
            g ≤ erosionUpper ε x i ↔ g ≤ erosionUpper ε (T.embedding (T.floor x hx)) i := by
          intro x hx i g hg
          have := hbreak x hx i (g - (ε : ℝ))
            (mem_erosionBreakpoints.mpr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g, hg, rfl⟩))))))
          simpa only [erosionUpper, ← sub_le_iff_le_add] using this
        constructor
        · rw [G.rankOfStructureMap_lan_congr M (erosionWide_le ε hab)
              (erosionWide_le ε (T.embedding.monotone hpq)) (hGlow a hTa) (hGup b hTb),
            H.rankOfStructureMap_lan_congr N hab (T.embedding.monotone hpq) (hH a hTa)
              (hH b hTb)]
          exact hGH.1
        · rw [H.rankOfStructureMap_lan_congr N (erosionWide_le ε hab)
              (erosionWide_le ε (T.embedding.monotone hpq)) (hHlow a hTa) (hHup b hTb),
            G.rankOfStructureMap_lan_congr M hab (T.embedding.monotone hpq) (hG a hTa)
              (hG b hTb)]
          exact hGH.2
      · -- Below `T` in some coordinate, the lowered grade has no lower point of either grid.
        have hGno : ¬ G.HasLowerPoint (erosionLower ε a) := by
          rintro ⟨p, hp⟩
          refine hTa ((T.hasLowerPoint_iff a).mpr fun i => ⟨(p i).val + (ε : ℝ), hT i
            (mem_erosionBreakpoints.mpr (Or.inr (Or.inr (Or.inl ⟨_, (p i).property, rfl⟩)))),
            ?_⟩)
          have := hp i
          simp only [embedding_apply, erosionLower] at this
          linarith
        have hHno : ¬ H.HasLowerPoint (erosionLower ε a) := by
          rintro ⟨p, hp⟩
          refine hTa ((T.hasLowerPoint_iff a).mpr fun i => ⟨(p i).val + (ε : ℝ), hT i
            (mem_erosionBreakpoints.mpr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, (p i).property, rfl⟩)))))), ?_⟩)
          have := hp i
          simp only [embedding_apply, erosionLower] at this
          linarith
        rw [G.rankOfStructureMap_lan_eq_zero M (erosionWide_le ε hab) hGno,
          H.rankOfStructureMap_lan_eq_zero N (erosionWide_le ε hab) hHno]
        exact ⟨Nat.zero_le _, Nat.zero_le _⟩
    exact ⟨fun a b hab => (key a b hab).1, fun a b hab => (key a b hab).2⟩

/-- The finite criterion at the grid of breakpoints itself. -/
theorem rankErosion_lan_iff :
    RankErosion ε (G.lan.obj M) (H.lan.obj N) ↔
      ∀ (p q : (erosionBreakpoints G H ε).Point) (hpq : p ≤ q),
        rankOfStructureMap (G.lan.obj M)
              (erosionWide_le ε ((erosionBreakpoints G H ε).embedding.monotone hpq)) ≤
            rankOfStructureMap (H.lan.obj N)
              ((erosionBreakpoints G H ε).embedding.monotone hpq) ∧
          rankOfStructureMap (H.lan.obj N)
              (erosionWide_le ε ((erosionBreakpoints G H ε).embedding.monotone hpq)) ≤
            rankOfStructureMap (G.lan.obj M)
              ((erosionBreakpoints G H ε).embedding.monotone hpq) :=
  rankErosion_lan_iff_of_subset G H M N ε fun _ => Finset.Subset.refl _

end Criterion

end TDA.Persistence.CoordinateGrid
