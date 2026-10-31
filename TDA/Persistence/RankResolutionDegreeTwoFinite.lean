import TDA.Persistence.FiniteRankProjectiveResolutionDimension
import TDA.Persistence.FinitePresentationHookKernel
import TDA.Persistence.FiniteRankProjectiveHomDimension
import TDA.Persistence.FiniteRankProjectiveHom
import TDA.Persistence.CoordinateGridHook
import TDA.Persistence.HookEndomorphisms
import Mathlib.Tactic

/-!
# A two-dimensional degree-two rank-projective witness

The finite witness is supported at the three grades `(0,1)`, `(1,0)`, and
`(1,1)` of the `3 × 3` coordinate grid. Its actual minimal rank-projective
resolution has four hooks in degrees zero and one and one hook in degree two.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwo

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence ZeroObject Classical

variable {k : Type u} [Field k]

noncomputable section

/-- The selected coordinate values for the finite two-dimensional witness. -/
def gridValues : Finset ℝ := {0, 1, 2}

/-- The actual nine-point grid used for the finite witness. -/
abbrev grid : CoordinateGrid 2 := fun _ => gridValues

private def gridCoordinate (i : Fin 3) : {x : ℝ // x ∈ gridValues} :=
  ⟨(i.val : ℝ), by fin_cases i <;> norm_num [gridValues]⟩

private def gridPoint (i j : Fin 3) : grid.Point := fun t =>
  if h : t.val = 0 then by simpa [grid] using gridCoordinate i
  else by simpa [grid] using gridCoordinate j

/-- The lower-left corner of the finite grid. -/
abbrev o : grid.Point := gridPoint 0 0

/-- The first arm of the support. -/
abbrev a : grid.Point := gridPoint 0 1

/-- The second arm of the support. -/
abbrev b : grid.Point := gridPoint 1 0

/-- The join of the two support arms. -/
abbrev c : grid.Point := gridPoint 1 1

/-- The first death grade for the augmentation hooks. -/
abbrev d : grid.Point := gridPoint 0 2

/-- The second death grade for the augmentation hooks. -/
abbrev e : grid.Point := gridPoint 2 0

/-- The death of the hook born at `b` in the first syzygy. -/
abbrev f : grid.Point := gridPoint 1 2

/-- The death of the hook born at `a` in the first syzygy. -/
abbrev g : grid.Point := gridPoint 2 1

/-- The top grade of the finite grid. -/
abbrev h : grid.Point := gridPoint 2 2

private theorem gridCoordinate_exists (x : {x : ℝ // x ∈ gridValues}) :
    ∃ i : Fin 3, x = gridCoordinate i := by
  have hx : (x : ℝ) = 0 ∨ (x : ℝ) = 1 ∨ (x : ℝ) = 2 := by
    simpa only [gridValues, Finset.mem_insert, Finset.mem_singleton] using x.property
  rcases hx with hx | hx | hx
  · exact ⟨0, Subtype.ext (by simpa [gridCoordinate] using hx)⟩
  · exact ⟨1, Subtype.ext (by simpa [gridCoordinate] using hx)⟩
  · exact ⟨2, Subtype.ext (by simpa [gridCoordinate] using hx)⟩

private theorem gridPoint_exists (p : grid.Point) :
    ∃ i j : Fin 3, p = gridPoint i j := by
  obtain ⟨i, hi⟩ := gridCoordinate_exists (p 0)
  obtain ⟨j, hj⟩ := gridCoordinate_exists (p 1)
  refine ⟨i, j, ?_⟩
  funext t
  fin_cases t
  · simpa [gridPoint, grid] using hi
  · simpa [gridPoint, grid] using hj

@[simp] private theorem gridPoint_le_iff (i j r s : Fin 3) :
    gridPoint i j ≤ gridPoint r s ↔ i ≤ r ∧ j ≤ s := by
  constructor
  · intro hp
    constructor
    · have h0 := hp 0
      change (gridCoordinate i).val ≤ (gridCoordinate r).val at h0
      have hr : ((i.val : ℝ) ≤ (r.val : ℝ)) := by
        simpa [gridCoordinate] using h0
      exact_mod_cast hr
    · have h1 := hp 1
      change (gridCoordinate j).val ≤ (gridCoordinate s).val at h1
      have hr : ((j.val : ℝ) ≤ (s.val : ℝ)) := by
        simpa [gridCoordinate] using h1
      exact_mod_cast hr
  · rintro ⟨hi, hj⟩ t
    fin_cases t
    · have hr : ((i.val : ℝ) ≤ (r.val : ℝ)) := by exact_mod_cast hi
      simpa [gridPoint, gridCoordinate] using hr
    · have hr : ((j.val : ℝ) ≤ (s.val : ℝ)) := by exact_mod_cast hj
      simpa [gridPoint, gridCoordinate] using hr

@[simp] private theorem gridPoint_eq_iff (i j r s : Fin 3) :
    gridPoint i j = gridPoint r s ↔ i = r ∧ j = s := by
  constructor
  · intro heq
    constructor
    · have h0 := congrArg (fun p : grid.Point => (p 0).val) heq
      have hr : (i.val : ℝ) = (r.val : ℝ) := by
        simpa [gridPoint, gridCoordinate] using h0
      exact Fin.ext (by exact_mod_cast hr)
    · have h1 := congrArg (fun p : grid.Point => (p 1).val) heq
      have hr : (j.val : ℝ) = (s.val : ℝ) := by
        simpa [gridPoint, gridCoordinate] using h1
      exact Fin.ext (by exact_mod_cast hr)
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem gridPoint_cases (p : grid.Point) :
    p = o ∨ p = a ∨ p = b ∨ p = c ∨ p = d ∨ p = e ∨ p = f ∨ p = g ∨ p = h := by
  obtain ⟨i, j, rfl⟩ := gridPoint_exists p
  fin_cases i <;> fin_cases j <;>
    simp [o, a, b, c, d, e, f, g, h, gridPoint, grid]

/-- The support of the finite witness is the union of the two arms below `c`. -/
def support : Set grid.Point := (Set.Ici a ∪ Set.Ici b) ∩ Set.Iic c

private theorem support_ordConnected : support.OrdConnected where
  out' := by
    intro x hx z hz y hy
    refine ⟨?_, hy.2.trans hz.2⟩
    rcases hx.1 with hax | hbx
    · exact Or.inl (hax.trans hy.1)
    · exact Or.inr (hbx.trans hy.1)

/-- The coefficient module on the three-point L-shaped support. -/
abbrev finiteModule : PModule.{u,0,u} k grid.Point :=
  SupportInterval.module (k := k) support support_ordConnected

private theorem support_iff_named (p : grid.Point) :
    p ∈ support ↔ p = a ∨ p = b ∨ p = c := by
  classical
  constructor
  · intro hp
    rcases gridPoint_cases p with hp | hp | hp | hp | hp | hp | hp | hp | hp
    all_goals subst p <;>
      simp [support, o, a, b, c, d, e, f, g, h, gridPoint_le_iff] at hp ⊢
  · rintro (rfl | rfl | rfl) <;> simp [support, a, b, c, gridPoint_le_iff]

private theorem a_mem_support : a ∈ support :=
  (support_iff_named a).2 (Or.inl rfl)

private theorem b_mem_support : b ∈ support :=
  (support_iff_named b).2 (Or.inr (Or.inl rfl))

private theorem c_mem_support : c ∈ support :=
  (support_iff_named c).2 (Or.inr (Or.inr rfl))

private theorem d_not_support : d ∉ support := by
  rw [support_iff_named]
  simp [d, a, b, c, gridPoint_eq_iff]

private theorem e_not_support : e ∉ support := by
  rw [support_iff_named]
  simp [e, a, b, c, gridPoint_eq_iff]

private theorem f_not_support : f ∉ support := by
  rw [support_iff_named]
  simp [f, a, b, c, gridPoint_eq_iff]

private theorem g_not_support : g ∉ support := by
  rw [support_iff_named]
  simp [g, a, b, c, gridPoint_eq_iff]

private theorem a_lt_d : a < d := by
  classical
  simp [a, d, lt_iff_le_not_ge, gridPoint_le_iff]

private theorem a_lt_g : a < g := by
  classical
  simp [a, g, lt_iff_le_not_ge, gridPoint_le_iff]

private theorem b_lt_f : b < f := by
  classical
  simp [b, f, lt_iff_le_not_ge, gridPoint_le_iff]

private theorem b_lt_e : b < e := by
  classical
  simp [b, e, lt_iff_le_not_ge, gridPoint_le_iff]

private theorem a_lt_h : a < h := by
  classical
  simp [a, h, lt_iff_le_not_ge, gridPoint_le_iff]

private theorem b_lt_h : b < h := by
  classical
  simp [b, h, lt_iff_le_not_ge, gridPoint_le_iff]

private theorem c_lt_f : c < f := by
  classical
  simp [c, f, lt_iff_le_not_ge, gridPoint_le_iff]

private theorem c_lt_g : c < g := by
  classical
  simp [c, g, lt_iff_le_not_ge, gridPoint_le_iff]

private theorem c_lt_h : c < h := by
  classical
  simp [c, h, lt_iff_le_not_ge, gridPoint_le_iff]

/-- The embedded center has real coordinates `(1,1)`. -/
theorem grid_embedding_c : grid.embedding c = fun _ : Fin 2 => (1 : ℝ) := by
  funext i
  fin_cases i <;> norm_num [CoordinateGrid.embedding_apply, c, gridPoint,
    gridCoordinate, grid, gridValues]

/-- The embedded top grade has real coordinates `(2,2)`. -/
theorem grid_embedding_h : grid.embedding h = fun _ : Fin 2 => (2 : ℝ) := by
  funext i
  fin_cases i <;> norm_num [CoordinateGrid.embedding_apply, h, gridPoint,
    gridCoordinate, grid, gridValues]

/-- The degree-zero hook `H(a,d)`. -/
abbrev A : PModule.{u,0,u} k grid.Point := Hook.module (k := k) a d

/-- The degree-zero hook `H(a,g)`. -/
abbrev B : PModule.{u,0,u} k grid.Point := Hook.module (k := k) a g

/-- The degree-zero hook `H(b,f)`. -/
abbrev C : PModule.{u,0,u} k grid.Point := Hook.module (k := k) b f

/-- The degree-zero hook `H(b,e)`. -/
abbrev D : PModule.{u,0,u} k grid.Point := Hook.module (k := k) b e

/-- The degree-one hook `H(a,h)`. -/
abbrev E : PModule.{u,0,u} k grid.Point := Hook.module (k := k) a h

/-- The degree-one hook `H(b,h)`. -/
abbrev F : PModule.{u,0,u} k grid.Point := Hook.module (k := k) b h

/-- The degree-one hook `H(c,f)`. -/
abbrev J : PModule.{u,0,u} k grid.Point := Hook.module (k := k) c f

/-- The degree-one hook `H(c,g)`. -/
abbrev K : PModule.{u,0,u} k grid.Point := Hook.module (k := k) c g

/-- The degree-two hook `H(c,h)`. -/
abbrev L : PModule.{u,0,u} k grid.Point := Hook.module (k := k) c h

private abbrev birth0 : Fin 4 → grid.Point
  | 0 => a | 1 => a | 2 => b | 3 => b

private abbrev death0 : Fin 4 → grid.Point
  | 0 => d | 1 => g | 2 => f | 3 => e

private abbrev birth1 : Fin 4 → grid.Point
  | 0 => a | 1 => b | 2 => c | 3 => c

private abbrev death1 : Fin 4 → grid.Point
  | 0 => h | 1 => h | 2 => f | 3 => g

private theorem endpoints0 (i : Fin 4) : birth0 i < death0 i := by
  fin_cases i
  exacts [a_lt_d, a_lt_g, b_lt_f, b_lt_e]

private theorem endpoints1 (i : Fin 4) : birth1 i < death1 i := by
  fin_cases i
  exacts [a_lt_h, b_lt_h, c_lt_f, c_lt_g]

/-- The four degree-zero hook occurrences, in the prescribed order. -/
abbrev hooks0 (i : Fin 4) : PModule.{u,0,u} k grid.Point :=
  Hook.module (k := k) (birth0 i) (death0 i)

/-- The four degree-one hook occurrences, in the prescribed order. -/
abbrev hooks1 (i : Fin 4) : PModule.{u,0,u} k grid.Point :=
  Hook.module (k := k) (birth1 i) (death1 i)

/-- The degree-zero term `A ⊕ B ⊕ C ⊕ D`. -/
abbrev P0 : PModule.{u,0,u} k grid.Point := ⨁ hooks0

/-- The degree-one term `E ⊕ F ⊕ J ⊕ K`. -/
abbrev P1 : PModule.{u,0,u} k grid.Point := ⨁ hooks1

private abbrev hookTag (x y : grid.Point) (hxy : x < y) :
    FiniteRankProjectiveHom.HookTag grid.Point :=
  .inl ⟨(x, y), hxy⟩

private abbrev hookMap {x y z t : grid.Point} (hxy : x < y) (hzt : z < t)
    (hzx : z ≤ x) (hty : t ≤ y) (htx : ¬ t ≤ x) :
    Hook.module (k := k) x y ⟶ Hook.module (k := k) z t :=
  FiniteRankProjectiveHom.normalizedHom (k := k)
    (hookTag x y hxy) (hookTag z t hzt)
    (by simpa [FiniteRankProjectiveHom.HomCondition,
      FiniteRankProjectiveHom.endpoints, FiniteRankProjectiveHom.birth,
      FiniteRankProjectiveHom.death] using And.intro hzx (And.intro hty htx))

private theorem augmentation_dies (x y : grid.Point) (hxy : x < y)
    (hx : x ∈ support) (hy : y ∉ support) :
    structureMapLinear (finiteModule (k := k)) hxy.le
      (SupportInterval.one (k := k) support hx) = 0 := by
  change structureMapLinear
    (SupportInterval.module (k := k) support support_ordConnected) hxy.le
      (SupportInterval.one (k := k) support hx) = 0
  apply Subtype.ext
  rw [SupportInterval.structureMap_val support support_ordConnected hxy.le]
  simp [hy]

private def augmentationComponent (x y : grid.Point) (hxy : x < y)
    (hx : x ∈ support) (hy : y ∉ support) :
    Hook.module (k := k) x y ⟶ finiteModule (k := k) :=
  Hook.fromGenerator hxy (finiteModule (k := k))
    (SupportInterval.one (k := k) support hx)
    (augmentation_dies (k := k) x y hxy hx hy)

private def augmentationEntry : ∀ i : Fin 4, hooks0 i ⟶ finiteModule (k := k)
  | 0 => augmentationComponent (k := k) a d a_lt_d a_mem_support d_not_support
  | 1 => augmentationComponent (k := k) a g a_lt_g a_mem_support g_not_support
  | 2 => augmentationComponent (k := k) b f b_lt_f b_mem_support f_not_support
  | 3 => augmentationComponent (k := k) b e b_lt_e b_mem_support e_not_support

/-- The augmentation sends every degree-zero birth generator to the supported unit. -/
def q0 : P0 (k := k) ⟶ finiteModule (k := k) :=
  biproduct.desc (augmentationEntry (k := k))

private def eToA : E (k := k) ⟶ A (k := k) :=
  hookMap (k := k) (x := a) (y := h) (z := a) (t := d) a_lt_h a_lt_d
    (by simp [a]) (by simp [d, h]) (by simp [d, a])

private def eToB : E (k := k) ⟶ B (k := k) :=
  hookMap (k := k) (x := a) (y := h) (z := a) (t := g) a_lt_h a_lt_g
    (by simp [a]) (by simp [g, h]) (by simp [g, a])

private def fToC : F (k := k) ⟶ C (k := k) :=
  hookMap (k := k) (x := b) (y := h) (z := b) (t := f) b_lt_h b_lt_f
    (by simp [b]) (by simp [f, h]) (by simp [f, b])

private def fToD : F (k := k) ⟶ D (k := k) :=
  hookMap (k := k) (x := b) (y := h) (z := b) (t := e) b_lt_h b_lt_e
    (by simp [b]) (by simp [e, h]) (by simp [e, b])

private def jToA : J (k := k) ⟶ A (k := k) :=
  hookMap (k := k) (x := c) (y := f) (z := a) (t := d) c_lt_f a_lt_d
    (by simp [a, c]) (by simp [d, f]) (by simp [d, c])

private def jToC : J (k := k) ⟶ C (k := k) :=
  hookMap (k := k) (x := c) (y := f) (z := b) (t := f) c_lt_f b_lt_f
    (by simp [b, c]) (by simp [f]) (by simp [f, c])

private def kToB : K (k := k) ⟶ B (k := k) :=
  hookMap (k := k) (x := c) (y := g) (z := a) (t := g) c_lt_g a_lt_g
    (by simp [a, c]) (by simp [g]) (by simp [g, c])

private def kToD : K (k := k) ⟶ D (k := k) :=
  hookMap (k := k) (x := c) (y := g) (z := b) (t := e) c_lt_g b_lt_e
    (by simp [b, c]) (by simp [e, g]) (by simp [e, c])

private def lToE : L (k := k) ⟶ E (k := k) :=
  hookMap (k := k) (x := c) (y := h) (z := a) (t := h) c_lt_h a_lt_h
    (by simp [a, c]) (by simp [h]) (by simp [h, c])

private def lToF : L (k := k) ⟶ F (k := k) :=
  hookMap (k := k) (x := c) (y := h) (z := b) (t := h) c_lt_h b_lt_h
    (by simp [b, c]) (by simp [h]) (by simp [h, c])

private def lToJ : L (k := k) ⟶ J (k := k) :=
  hookMap (k := k) (x := c) (y := h) (z := c) (t := f) c_lt_h c_lt_f
    (by simp [c]) (by simp [f, h]) (by simp [f, c])

private def lToK : L (k := k) ⟶ K (k := k) :=
  hookMap (k := k) (x := c) (y := h) (z := c) (t := g) c_lt_h c_lt_g
    (by simp [c]) (by simp [g, h]) (by simp [g, c])

private def d1ColumnE : E (k := k) ⟶ P0 (k := k) :=
  eToA ≫ biproduct.ι hooks0 0 - eToB ≫ biproduct.ι hooks0 1

private def d1ColumnF : F (k := k) ⟶ P0 (k := k) :=
  fToC ≫ biproduct.ι hooks0 2 - fToD ≫ biproduct.ι hooks0 3

private def d1ColumnJ : J (k := k) ⟶ P0 (k := k) :=
  jToA ≫ biproduct.ι hooks0 0 - jToC ≫ biproduct.ι hooks0 2

private def d1ColumnK : K (k := k) ⟶ P0 (k := k) :=
  kToB ≫ biproduct.ι hooks0 1 - kToD ≫ biproduct.ι hooks0 3

private def d1Column : ∀ i : Fin 4, hooks1 i ⟶ P0 (k := k)
  | 0 => d1ColumnE (k := k)
  | 1 => d1ColumnF (k := k)
  | 2 => d1ColumnJ (k := k)
  | 3 => d1ColumnK (k := k)

/-- The degree-one differential has columns `A−B`, `C−D`, `A−C`, and `B−D`. -/
def d1 : P1 (k := k) ⟶ P0 (k := k) :=
  biproduct.desc (d1Column (k := k))

/-- The degree-two differential has coefficient column `(1,-1,-1,1)`. -/
def j : L (k := k) ⟶ P1 (k := k) :=
  lToE ≫ biproduct.ι hooks1 0 - lToF ≫ biproduct.ι hooks1 1 -
    lToJ ≫ biproduct.ι hooks1 2 + lToK ≫ biproduct.ι hooks1 3

private def scalar (S : Set grid.Point) (p : grid.Point) (r : k) :
    SupportInterval.fiber (k := k) S p := by
  refine ⟨if p ∈ S then r else 0, ?_⟩
  by_cases hp : p ∈ S
  · simpa only [SupportInterval.fiber, if_pos hp] using (Submodule.mem_top : r ∈ (⊤ : Submodule k k))
  · simpa only [SupportInterval.fiber, if_neg hp] using (Submodule.zero_mem (⊥ : Submodule k k))

@[simp] private theorem scalar_val (S : Set grid.Point) (p : grid.Point) (r : k) :
    (scalar S p r : k) = if p ∈ S then r else 0 := rfl

private theorem hookMap_val {x y z t p : grid.Point} (hxy : x < y) (hzt : z < t)
    (hzx : z ≤ x) (hty : t ≤ y) (htx : ¬ t ≤ x)
    (v : (Hook.module (k := k) x y).obj p) :
    (((hookMap hxy hzt hzx hty htx).app p).hom v : k) =
      if p ∈ Hook.support z t then (v : k) else 0 := by
  by_cases hp : x ≤ p
  · unfold hookMap FiniteRankProjectiveHom.normalizedHom
    dsimp [Hook.homEquivKernel, FiniteRankProjectiveHom.hookModule,
      FiniteRankProjectiveHom.unitAt, FiniteRankProjectiveHom.birthUnit]
    erw [Hook.fromGenerator_app hxy _ _ _ hp]
    change (v : k) * (structureMapLinear (Hook.module (k := k) z t) hp
      (structureMapLinear (Hook.module (k := k) z t) hzx
        (SupportInterval.one (Hook.support z t) (Hook.birth_mem hzt))) : k) = _
    rw [SupportInterval.structureMap_val, SupportInterval.structureMap_val]
    simp only [show x ∈ Hook.support z t from ⟨hzx, htx⟩, if_true,
      SupportInterval.one, mul_one]
    split_ifs <;> simp_all [Hook.support]
  · have hv : v = 0 := Subtype.ext (SupportInterval.val_eq_zero _ (fun h => hp h.1) v)
    simp [hv]

private def coords0 {p : grid.Point} (v : (P0 (k := k)).obj p) (i : Fin 4) : k :=
  (((biproduct.π (hooks0 (k := k)) i).app p).hom v : k)

private def coords1 {p : grid.Point} (v : (P1 (k := k)).obj p) (i : Fin 4) : k :=
  (((biproduct.π (hooks1 (k := k)) i).app p).hom v : k)

private def vector0 (p : grid.Point) (v : Fin 4 → k) : (P0 (k := k)).obj p :=
  (FiniteBiproduct.fiberIsoPi hooks0 p).inv.hom
    (fun i => scalar (Hook.support (birth0 i) (death0 i)) p (v i))

private def vector1 (p : grid.Point) (v : Fin 4 → k) : (P1 (k := k)).obj p :=
  (FiniteBiproduct.fiberIsoPi hooks1 p).inv.hom
    (fun i => scalar (Hook.support (birth1 i) (death1 i)) p (v i))

@[simp] private theorem coords0_vector (p : grid.Point) (v : Fin 4 → k) (i : Fin 4) :
    coords0 (vector0 p v) i = if p ∈ Hook.support (birth0 i) (death0 i) then v i else 0 := by
  have he := congrArg (fun f => f.hom (vector0 p v))
    (FiniteBiproduct.fiberIsoPi_hom_π (hooks0 (k := k)) p i)
  change ((FiniteBiproduct.fiberIsoPi hooks0 p).hom.hom (vector0 p v)) i = _ at he
  have hv : (FiniteBiproduct.fiberIsoPi hooks0 p).hom.hom (vector0 p v) =
      fun i => scalar (Hook.support (birth0 i) (death0 i)) p (v i) := by
    exact congrArg (fun f => f.hom
      (fun i => scalar (Hook.support (birth0 i) (death0 i)) p (v i)))
      (FiniteBiproduct.fiberIsoPi (hooks0 (k := k)) p).inv_hom_id
  by_cases hp : p ∈ Hook.support (birth0 i) (death0 i) <;>
    simpa only [coords0, hv, scalar_val, hp, if_true, if_false] using (congrArg Subtype.val he).symm

@[simp] private theorem coords1_vector (p : grid.Point) (v : Fin 4 → k) (i : Fin 4) :
    coords1 (vector1 p v) i = if p ∈ Hook.support (birth1 i) (death1 i) then v i else 0 := by
  have he := congrArg (fun f => f.hom (vector1 p v))
    (FiniteBiproduct.fiberIsoPi_hom_π (hooks1 (k := k)) p i)
  change ((FiniteBiproduct.fiberIsoPi hooks1 p).hom.hom (vector1 p v)) i = _ at he
  have hv : (FiniteBiproduct.fiberIsoPi hooks1 p).hom.hom (vector1 p v) =
      fun i => scalar (Hook.support (birth1 i) (death1 i)) p (v i) := by
    exact congrArg (fun f => f.hom
      (fun i => scalar (Hook.support (birth1 i) (death1 i)) p (v i)))
      (FiniteBiproduct.fiberIsoPi (hooks1 (k := k)) p).inv_hom_id
  by_cases hp : p ∈ Hook.support (birth1 i) (death1 i) <;>
    simpa only [coords1, hv, scalar_val, hp, if_true, if_false] using (congrArg Subtype.val he).symm

private theorem coords0_ext {p : grid.Point} {v w : (P0 (k := k)).obj p}
    (he : ∀ i, coords0 v i = coords0 w i) : v = w := by
  apply FiniteBiproduct.element_ext hooks0 p
  intro i
  exact Subtype.ext (he i)

private theorem coords1_ext {p : grid.Point} {v w : (P1 (k := k)).obj p}
    (he : ∀ i, coords1 v i = coords1 w i) : v = w := by
  apply FiniteBiproduct.element_ext hooks1 p
  intro i
  exact Subtype.ext (he i)

@[simp] private theorem coords0_zero (p : grid.Point) (i : Fin 4) :
    coords0 (0 : (P0 (k := k)).obj p) i = 0 := by simp [coords0]

@[simp] private theorem coords1_zero (p : grid.Point) (i : Fin 4) :
    coords1 (0 : (P1 (k := k)).obj p) i = 0 := by simp [coords1]

private theorem coords0_not_support {p : grid.Point} (i : Fin 4)
    (hp : p ∉ Hook.support (birth0 i) (death0 i)) (v : (P0 (k := k)).obj p) :
    coords0 v i = 0 := SupportInterval.val_eq_zero _ hp _

private theorem coords1_not_support {p : grid.Point} (i : Fin 4)
    (hp : p ∉ Hook.support (birth1 i) (death1 i)) (v : (P1 (k := k)).obj p) :
    coords1 v i = 0 := SupportInterval.val_eq_zero _ hp _

private theorem coords0_map {p q : grid.Point} (hpq : p ≤ q)
    (v : (P0 (k := k)).obj p) (i : Fin 4) :
    coords0 (structureMapLinear (P0 (k := k)) hpq v) i =
      if q ∈ Hook.support (birth0 i) (death0 i) then coords0 v i else 0 := by
  have hn := congrArg (fun f => f.hom v)
    ((biproduct.π (hooks0 (k := k)) i).naturality (homOfLE hpq))
  change ((biproduct.π hooks0 i).app q).hom (structureMapLinear P0 hpq v) =
    structureMapLinear (hooks0 i) hpq (((biproduct.π hooks0 i).app p).hom v) at hn
  rw [show coords0 (structureMapLinear P0 hpq v) i =
    (structureMapLinear (hooks0 i) hpq (((biproduct.π hooks0 i).app p).hom v) : k) from
      congrArg Subtype.val hn]
  simpa only [coords0] using (SupportInterval.structureMap_val
    (Hook.support (birth0 i) (death0 i)) (Hook.support_ordConnected _ _) hpq
      (((biproduct.π (hooks0 (k := k)) i).app p).hom v))

private theorem coords1_map {p q : grid.Point} (hpq : p ≤ q)
    (v : (P1 (k := k)).obj p) (i : Fin 4) :
    coords1 (structureMapLinear (P1 (k := k)) hpq v) i =
      if q ∈ Hook.support (birth1 i) (death1 i) then coords1 v i else 0 := by
  have hn := congrArg (fun f => f.hom v)
    ((biproduct.π (hooks1 (k := k)) i).naturality (homOfLE hpq))
  change ((biproduct.π hooks1 i).app q).hom (structureMapLinear P1 hpq v) =
    structureMapLinear (hooks1 i) hpq (((biproduct.π hooks1 i).app p).hom v) at hn
  rw [show coords1 (structureMapLinear P1 hpq v) i =
    (structureMapLinear (hooks1 i) hpq (((biproduct.π hooks1 i).app p).hom v) : k) from
      congrArg Subtype.val hn]
  simpa only [coords1] using (SupportInterval.structureMap_val
    (Hook.support (birth1 i) (death1 i)) (Hook.support_ordConnected _ _) hpq
      (((biproduct.π (hooks1 (k := k)) i).app p).hom v))

private theorem eval_comp {X Y Z : PModule.{u,0,u} k grid.Point}
    (α : X ⟶ Y) (β : Y ⟶ Z) (p : grid.Point) (x : X.obj p) :
    ((α ≫ β).app p).hom x = (β.app p).hom ((α.app p).hom x) := rfl

@[simp] private theorem eval_ι_desc {F : Fin 4 → PModule.{u,0,u} k grid.Point}
    {Y : PModule.{u,0,u} k grid.Point} (α : ∀ i, F i ⟶ Y)
    (p : grid.Point) (i : Fin 4) (x : (F i).obj p) :
    ((biproduct.desc α).app p).hom (((biproduct.ι F i).app p).hom x) =
      ((α i).app p).hom x := by
  exact congrArg (fun f : F i ⟶ Y => (f.app p).hom x) (biproduct.ι_desc α i)

private theorem decompose {F : Fin 4 → PModule.{u,0,u} k grid.Point}
    {p : grid.Point} (v : (⨁ F).obj p) :
    v = ∑ i : Fin 4, ((biproduct.ι F i).app p).hom
      (((biproduct.π F i).app p).hom v) := by
  have he := congrArg (fun f : (⨁ F) ⟶ (⨁ F) => (f.app p).hom v)
    (biproduct.total (f := F))
  simpa only [NatTrans.app_sum, NatTrans.comp_app, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] using he.symm

private theorem augmentation_val {x y p : grid.Point} (hxy : x < y)
    (hx : x ∈ support) (hy : y ∉ support)
    (v : (Hook.module (k := k) x y).obj p) :
    (((augmentationComponent x y hxy hx hy).app p).hom v : k) =
      if p ∈ support then (v : k) else 0 := by
  by_cases hp : x ≤ p
  · unfold augmentationComponent
    erw [Hook.fromGenerator_app hxy _ _ _ hp]
    change (v : k) * (structureMapLinear (finiteModule (k := k)) hp
      (SupportInterval.one support hx) : k) = _
    rw [SupportInterval.structureMap_val]
    simp [SupportInterval.one]
  · have hv : v = 0 := Subtype.ext (SupportInterval.val_eq_zero _ (fun h => hp h.1) v)
    simp [hv]

private theorem q0_val {p : grid.Point} (v : (P0 (k := k)).obj p) :
    (((q0 (k := k)).app p).hom v : k) =
      if p ∈ support then coords0 v 0 + coords0 v 1 + coords0 v 2 + coords0 v 3 else 0 := by
  conv_lhs => rw [decompose v]
  simp only [map_sum, q0]
  simp only [eval_ι_desc (F := hooks0) (augmentationEntry (k := k))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_empty, add_zero,
    augmentationEntry, Submodule.coe_add]
  erw [augmentation_val, augmentation_val, augmentation_val, augmentation_val]
  split_ifs <;> simp [coords0] <;> ring

private abbrev differentialCoordinates (v : Fin 4 → k) : Fin 4 → k :=
  ![v 0 + v 2, -v 0 + v 3, v 1 - v 2, -v 1 - v 3]


private def differentialRow : ∀ i r : Fin 4, hooks1 r ⟶ hooks0 (k := k) i
  | 0, 0 => eToA | 0, 1 => 0 | 0, 2 => jToA | 0, 3 => 0
  | 1, 0 => -eToB | 1, 1 => 0 | 1, 2 => 0 | 1, 3 => kToB
  | 2, 0 => 0 | 2, 1 => fToC | 2, 2 => -jToC | 2, 3 => 0
  | 3, 0 => 0 | 3, 1 => -fToD | 3, 2 => 0 | 3, 3 => -kToD

private theorem differentialRow_eq (i : Fin 4) :
    d1 (k := k) ≫ biproduct.π hooks0 i = biproduct.desc (differentialRow i) := by
  apply biproduct.hom_ext'
  intro r
  fin_cases i <;> fin_cases r <;>
    simp [d1, d1Column, d1ColumnE, d1ColumnF, d1ColumnJ, d1ColumnK,
      differentialRow, Category.assoc, Preadditive.sub_comp]

private theorem d1_coords {p : grid.Point} (v : (P1 (k := k)).obj p) (i : Fin 4) :
    coords0 (((d1 (k := k)).app p).hom v) i =
      if p ∈ Hook.support (birth0 i) (death0 i)
      then differentialCoordinates (coords1 v) i else 0 := by
  change (((d1 (k := k) ≫ biproduct.π hooks0 i).app p).hom v : k) = _
  rw [differentialRow_eq]
  conv_lhs => rw [decompose v]
  simp only [map_sum, eval_ι_desc (F := hooks1) (differentialRow (k := k) i)]
  fin_cases i
  all_goals
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    dsimp only [Fin.succ, Fin.reduceFinMk, differentialRow]
    simp only [eToA, eToB, fToC, fToD, jToA, jToC, kToB, kToD]
    simp only [NatTrans.app_neg, ModuleCat.hom_neg, LinearMap.neg_apply, map_zero,
      ZeroMemClass.coe_zero, Submodule.coe_add, Submodule.coe_neg, add_zero, zero_add]
    erw [hookMap_val, hookMap_val]
    simp [differentialCoordinates, coords1, birth0, death0] <;> split_ifs <;> ring

private def secondRow : ∀ i : Fin 4, L (k := k) ⟶ hooks1 i
  | 0 => lToE | 1 => -lToF | 2 => -lToJ | 3 => lToK

private theorem secondRow_eq (i : Fin 4) :
    j (k := k) ≫ biproduct.π hooks1 i = secondRow i := by
  fin_cases i <;> simp [j, secondRow, Category.assoc,
    Preadditive.add_comp, Preadditive.sub_comp]

private theorem j_coords {p : grid.Point} (v : (L (k := k)).obj p) (i : Fin 4) :
    coords1 (((j (k := k)).app p).hom v) i =
      if p ∈ Hook.support (birth1 i) (death1 i) then ![(v : k), -(v : k), -(v : k), (v : k)] i else 0 := by
  change (((j (k := k) ≫ biproduct.π hooks1 i).app p).hom v : k) = _
  rw [secondRow_eq]
  fin_cases i <;> simp only [secondRow, lToE, lToF, lToJ, lToK]
  all_goals
    try simp only [NatTrans.app_neg, ModuleCat.hom_neg, LinearMap.neg_apply, Submodule.coe_neg]
    erw [hookMap_val]
    simp [birth1, death1] <;> split_ifs <;> ring

private theorem constraints0 {p : grid.Point} (v : (P0 (k := k)).obj p) :
    (p ∈ Hook.support (birth0 0) (death0 0) ∨ coords0 v 0 = 0) ∧
    (p ∈ Hook.support (birth0 1) (death0 1) ∨ coords0 v 1 = 0) ∧
    (p ∈ Hook.support (birth0 2) (death0 2) ∨ coords0 v 2 = 0) ∧
    (p ∈ Hook.support (birth0 3) (death0 3) ∨ coords0 v 3 = 0) := by
  exact ⟨Classical.or_iff_not_imp_left.mpr (fun hn => coords0_not_support 0 hn v),
    Classical.or_iff_not_imp_left.mpr (fun hn => coords0_not_support 1 hn v),
    Classical.or_iff_not_imp_left.mpr (fun hn => coords0_not_support 2 hn v),
    Classical.or_iff_not_imp_left.mpr (fun hn => coords0_not_support 3 hn v)⟩

private theorem constraints1 {p : grid.Point} (v : (P1 (k := k)).obj p) :
    (p ∈ Hook.support (birth1 0) (death1 0) ∨ coords1 v 0 = 0) ∧
    (p ∈ Hook.support (birth1 1) (death1 1) ∨ coords1 v 1 = 0) ∧
    (p ∈ Hook.support (birth1 2) (death1 2) ∨ coords1 v 2 = 0) ∧
    (p ∈ Hook.support (birth1 3) (death1 3) ∨ coords1 v 3 = 0) := by
  exact ⟨Classical.or_iff_not_imp_left.mpr (fun hn => coords1_not_support 0 hn v),
    Classical.or_iff_not_imp_left.mpr (fun hn => coords1_not_support 1 hn v),
    Classical.or_iff_not_imp_left.mpr (fun hn => coords1_not_support 2 hn v),
    Classical.or_iff_not_imp_left.mpr (fun hn => coords1_not_support 3 hn v)⟩

/-- The prescribed first differential lands in the actual augmentation kernel. -/
theorem d1_comp_q0 : d1 (k := k) ≫ q0 (k := k) = 0 := by
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (((q0 (k := k)).app p).hom (((d1 (k := k)).app p).hom v) : k) = 0
  rw [q0_val]
  have hv := constraints1 v
  rcases gridPoint_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [d1_coords]
    simp_all [birth0, death0, birth1, death1, Hook.support, support, o, a, b, c, d, e, f, g, h, gridPoint_le_iff, gridPoint_eq_iff] <;> ring

/-- The first syzygy is the actual categorical kernel of the augmentation. -/
abbrev K1 : PModule.{u,0,u} k grid.Point := kernel (q0 (k := k))

/-- The quotient onto the actual first syzygy is the kernel lift of `d1`. -/
def q1 : P1 (k := k) ⟶ K1 (k := k) :=
  kernel.lift (q0 (k := k)) (d1 (k := k)) d1_comp_q0

/-- Composing the actual lift with the kernel inclusion recovers the matrix. -/
@[simp] theorem q1_comp_inclusion : q1 (k := k) ≫ kernel.ι (q0 (k := k)) = d1 :=
  kernel.lift_ι _ _ _

/-- The prescribed second column is killed by the first differential. -/
theorem j_comp_d1 : j (k := k) ≫ d1 (k := k) = 0 := by
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply coords0_ext
  intro i
  simp only [eval_comp (j (k := k)) (d1 (k := k)), NatTrans.app_zero,
    ModuleCat.hom_zero, LinearMap.zero_apply, coords0_zero]
  rw [d1_coords]
  have hj := funext (fun r => j_coords (k := k) v r)
  rw [hj]
  fin_cases i
  all_goals
    have hv : p ∈ Hook.support c h ∨ (v : k) = 0 :=
      Classical.or_iff_not_imp_left.mpr (fun hn => SupportInterval.val_eq_zero _ hn v)
    rcases gridPoint_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [differentialCoordinates, birth0, death0, birth1, death1, Hook.support,
      o, a, b, c, d, e, f, g, h, gridPoint_le_iff] <;> ring

/-- The second column also vanishes after the actual first quotient. -/
theorem j_comp_q1 : j (k := k) ≫ q1 (k := k) = 0 := by
  apply (cancel_mono (kernel.ι (q0 (k := k)))).mp
  simp [Category.assoc, j_comp_d1]

private theorem q0_surjective (p : grid.Point) :
    Function.Surjective ((q0 (k := k)).app p).hom := by
  intro v
  refine ⟨vector0 p (if p = b then ![0, 0, (v : k), 0] else ![(v : k), 0, 0, 0]), ?_⟩
  apply Subtype.ext
  rw [q0_val]
  have hv : p ∈ support ∨ (v : k) = 0 :=
    Classical.or_iff_not_imp_left.mpr (fun hn => SupportInterval.val_eq_zero _ hn v)
  rcases gridPoint_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [coords0_vector, birth0, death0, Hook.support, support,
    o, a, b, c, d, e, f, g, h, gridPoint_le_iff, gridPoint_eq_iff]

private def augmentationDyingLift (p q : grid.Point) (r : k) : (P0 (k := k)).obj p :=
  vector0 p (if p = b then
    if f ≤ q then ![0, 0, r, 0] else ![0, 0, 0, r]
    else if d ≤ q then ![r, 0, 0, 0] else ![0, r, 0, 0])

set_option maxHeartbeats 1000000 in
private theorem q0_dyingLift {p q : grid.Point} (hpq : p ≤ q)
    (v : (finiteModule (k := k)).obj p)
    (hdie : structureMapLinear (finiteModule (k := k)) hpq v = 0) :
    ∃ w : (P0 (k := k)).obj p, ((q0 (k := k)).app p).hom w = v ∧
      structureMapLinear (P0 (k := k)) hpq w = 0 := by
  have hd := congrArg Subtype.val hdie
  erw [SupportInterval.structureMap_val] at hd
  simp only [ZeroMemClass.coe_zero] at hd
  by_cases hp : p ∈ support
  · by_cases hq : q ∈ support
    · have hv : v = 0 := by
        apply Subtype.ext
        change (v : k) = 0
        simpa only [if_pos hq] using hd
      exact ⟨0, by simp [hv], by simp⟩
    · refine ⟨augmentationDyingLift p q (v : k), ?_, ?_⟩
      · apply Subtype.ext
        rw [q0_val]
        rcases (support_iff_named p).mp hp with rfl | rfl | rfl
        all_goals rcases gridPoint_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [augmentationDyingLift, coords0_vector,
          birth0, death0, Hook.support, support, o, a, b, c, d, e, f, g, h,
          gridPoint_le_iff, gridPoint_eq_iff]
      · apply coords0_ext
        intro i
        rw [coords0_map, coords0_zero]
        rcases (support_iff_named p).mp hp with rfl | rfl | rfl
        all_goals rcases gridPoint_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals fin_cases i <;> simp_all [augmentationDyingLift, coords0_vector,
          birth0, death0, Hook.support, support, o, a, b, c, d, e, f, g, h,
          gridPoint_le_iff, gridPoint_eq_iff]
        all_goals have horder := hpq
        all_goals simp [o, a, b, c, d, e, f, g, h, gridPoint_le_iff] at horder
  · have hv : v = 0 := Subtype.ext (SupportInterval.val_eq_zero _ hp v)
    exact ⟨0, by simp [hv], by simp⟩

private instance p0_finiteDimensional (p : grid.Point) :
    FiniteDimensional k ((P0 (k := k)).obj p) :=
  FiniteBiproduct.finiteDimensional hooks0 p

private instance p1_finiteDimensional (p : grid.Point) :
    FiniteDimensional k ((P1 (k := k)).obj p) :=
  FiniteBiproduct.finiteDimensional hooks1 p

/-- The augmentation row is rank exact, with same-death lifts at every comparable pair. -/
theorem q0_rankExact : IsRankExact (kernel.ι (q0 (k := k))) q0 :=
  RankKernel.rankExact q0 q0_surjective q0_dyingLift

private abbrev ambient {p : grid.Point} (v : (K1 (k := k)).obj p) : (P0 (k := k)).obj p :=
  ((kernel.ι (q0 (k := k))).app p).hom v

private theorem ambient_injective (p : grid.Point) :
    Function.Injective (ambient (k := k) (p := p)) := RankKernel.injective q0 p

@[simp] private theorem ambient_q1 {p : grid.Point} (v : (P1 (k := k)).obj p) :
    ambient (((q1 (k := k)).app p).hom v) = ((d1 (k := k)).app p).hom v :=
  congrArg (fun f : P1 (k := k) ⟶ P0 => (f.app p).hom v) q1_comp_inclusion

private theorem ambient_relation {p : grid.Point} (v : (K1 (k := k)).obj p) :
    (if p ∈ support then
      coords0 (ambient v) 0 + coords0 (ambient v) 1 +
        coords0 (ambient v) 2 + coords0 (ambient v) 3 else 0) = 0 := by
  have he := congrArg (fun f : K1 (k := k) ⟶ finiteModule => (f.app p).hom v)
    (kernel.condition (q0 (k := k)))
  have hv := congrArg Subtype.val he
  change (((q0 (k := k)).app p).hom (ambient v) : k) = 0 at hv
  rw [q0_val] at hv
  exact hv

private theorem ambient_map {p q : grid.Point} (hpq : p ≤ q)
    (v : (K1 (k := k)).obj p) :
    ambient (structureMapLinear (K1 (k := k)) hpq v) =
      structureMapLinear (P0 (k := k)) hpq (ambient v) := by
  exact congrArg (fun f => f.hom v)
    ((kernel.ι (q0 (k := k))).naturality (homOfLE hpq))

private def firstSyzygyLift (p : grid.Point) (v : Fin 4 → k) : (P1 (k := k)).obj p :=
  vector1 p (if p = c then ![-v 1, -v 3, v 0 + v 1, 0]
    else if p = a then ![v 0, 0, 0, 0]
    else if p = b ∨ p = e then ![0, v 2, 0, 0]
    else if p = g then ![v 0, v 2, 0, 0]
    else ![-v 1, -v 3, 0, 0])

private theorem q1_surjective (p : grid.Point) :
    Function.Surjective ((q1 (k := k)).app p).hom := by
  intro v
  refine ⟨firstSyzygyLift p (coords0 (ambient v)), ?_⟩
  apply ambient_injective p
  rw [ambient_q1]
  apply coords0_ext
  intro i
  rw [d1_coords]
  have hs := ambient_relation v
  have hv := constraints0 (ambient v)
  rcases gridPoint_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals fin_cases i <;>
    simp_all [firstSyzygyLift, differentialCoordinates, coords1_vector,
      birth0, death0, birth1, death1, Hook.support, support,
      o, a, b, c, d, e, f, g, h, gridPoint_le_iff, gridPoint_eq_iff] <;>
    first | (solve | ring) | (solve | linear_combination hs) | linear_combination -hs

private theorem j_injective (p : grid.Point) : Function.Injective ((j (k := k)).app p).hom := by
  intro x y he
  apply Subtype.ext
  by_cases hp : p ∈ Hook.support c h
  · have hpE : p ∈ Hook.support a h := ⟨(show a ≤ c by simp [a, c]).trans hp.1, hp.2⟩
    have hx := j_coords x 0
    have hy := j_coords y 0
    simp only [birth1, death1, if_pos hpE, Matrix.cons_val_zero] at hx hy
    exact hx.symm.trans ((congrArg (fun v => coords1 v 0) he).trans hy)
  · exact (SupportInterval.val_eq_zero _ hp x).trans (SupportInterval.val_eq_zero _ hp y).symm

set_option maxHeartbeats 600000 in
private theorem d1_kernel_lift (p : grid.Point) (v : (P1 (k := k)).obj p)
    (hzero : ((d1 (k := k)).app p).hom v = 0) :
    ∃ z : (L (k := k)).obj p, ((j (k := k)).app p).hom z = v := by
  have hd : ∀ i, (if p ∈ Hook.support (birth0 i) (death0 i)
      then differentialCoordinates (coords1 v) i else 0) = 0 := by
    intro i
    rw [← d1_coords, hzero, coords0_zero]
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  clear hd
  have hv := constraints1 v
  refine ⟨scalar (Hook.support c h) p (coords1 v 0), ?_⟩
  apply coords1_ext
  intro i
  rw [j_coords]
  rcases gridPoint_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals fin_cases i <;>
    simp_all [scalar_val, differentialCoordinates, birth0, death0, birth1, death1,
      Hook.support, o, a, b, c, d, e, f, g, h, gridPoint_le_iff]
  all_goals first
    | (solve | linear_combination h0)
    | (solve | linear_combination -h0)
    | (solve | linear_combination h1)
    | (solve | linear_combination -h1)
    | (solve | linear_combination h2)
    | (solve | linear_combination -h2)
    | (solve | linear_combination h3)
    | (solve | linear_combination -h3)
    | (solve | linear_combination h0 + h2)
    | (solve | linear_combination -h0 - h2)
    | (solve | linear_combination h1 + h3)
    | (solve | linear_combination -h1 - h3)

private theorem row1_shortExact : IsPointwiseShortExact (j (k := k)) q1 where
  injective := j_injective
  surjective := q1_surjective
  range_eq_ker p := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg (fun f : L (k := k) ⟶ K1 => (f.app p).hom z) j_comp_q1
    · intro hv
      have hq : ((q1 (k := k)).app p).hom v = 0 := hv
      have hd : ((d1 (k := k)).app p).hom v = 0 := by
        rw [← ambient_q1, hq]
        exact map_zero _
      exact d1_kernel_lift p v hd

private theorem ambient_dying_coordinates {p q : grid.Point} (hpq : p ≤ q)
    (v : (K1 (k := k)).obj p)
    (hdie : structureMapLinear (K1 (k := k)) hpq v = 0) (i : Fin 4) :
    (if q ∈ Hook.support (birth0 i) (death0 i) then coords0 (ambient v) i else 0) = 0 := by
  have he : structureMapLinear (P0 (k := k)) hpq (ambient v) = 0 := by
    rw [← ambient_map, hdie]
    exact map_zero _
  have hc := congrArg (fun w => coords0 w i) he
  rw [coords0_map, coords0_zero] at hc
  exact hc

set_option maxHeartbeats 600000 in
private theorem scalar_dying_eq_zero {p q : grid.Point} (hpq : p ≤ q)
    (hq : q ≠ h) (hcf : ¬ (p = c ∧ q = f)) (hcg : ¬ (p = c ∧ q = g))
    (x : Fin 4 → k)
    (hsupport : ∀ i, p ∉ Hook.support (birth0 i) (death0 i) → x i = 0)
    (hsum : (if p ∈ support then x 0 + x 1 + x 2 + x 3 else 0) = 0)
    (hdie : ∀ i, (if q ∈ Hook.support (birth0 i) (death0 i) then x i else 0) = 0) :
    ∀ i, x i = 0 := by
  have s0 := hsupport 0
  have s1 := hsupport 1
  have s2 := hsupport 2
  have s3 := hsupport 3
  have h0 := hdie 0
  have h1 := hdie 1
  have h2 := hdie 2
  have h3 := hdie 3
  clear hsupport hdie
  rcases gridPoint_cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases gridPoint_cases q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [o, a, b, c, d, e, f, g, h, gridPoint_le_iff, gridPoint_eq_iff]
    at hpq hq hcf hcg
  all_goals intro i; fin_cases i <;>
    simp_all [birth0, death0, Hook.support, support,
      o, a, b, c, d, e, f, g, h, gridPoint_le_iff]

private theorem syzygy_dying_eq_zero {p q : grid.Point} (hpq : p ≤ q)
    (hq : q ≠ h) (hcf : ¬ (p = c ∧ q = f)) (hcg : ¬ (p = c ∧ q = g))
    (v : (K1 (k := k)).obj p)
    (hdie : structureMapLinear (K1 (k := k)) hpq v = 0) : v = 0 := by
  apply ambient_injective p
  simp only [ambient, map_zero]
  apply coords0_ext
  intro i
  rw [coords0_zero]
  exact scalar_dying_eq_zero hpq hq hcf hcg (coords0 (ambient v))
    (fun i hn => coords0_not_support i hn (ambient v))
    (ambient_relation v) (ambient_dying_coordinates hpq v hdie) i

private theorem syzygy_center_dyingLift {q : grid.Point} (hcq : c ≤ q)
    (hq : q = f ∨ q = g) (v : (K1 (k := k)).obj c)
    (hdie : structureMapLinear (K1 (k := k)) hcq v = 0) :
    ∃ w : (P1 (k := k)).obj c, ((q1 (k := k)).app c).hom w = v ∧
      structureMapLinear (P1 (k := k)) hcq w = 0 := by
  have h0 := ambient_dying_coordinates hcq v hdie 0
  have h1 := ambient_dying_coordinates hcq v hdie 1
  have h2 := ambient_dying_coordinates hcq v hdie 2
  have h3 := ambient_dying_coordinates hcq v hdie 3
  have hs := ambient_relation v
  refine ⟨vector1 c (if q = f then ![0, 0, coords0 (ambient v) 0, 0]
    else ![0, 0, 0, coords0 (ambient v) 1]), ?_, ?_⟩
  · apply ambient_injective c
    rw [ambient_q1]
    apply coords0_ext
    intro i
    rw [d1_coords]
    rcases hq with rfl | rfl
    all_goals fin_cases i <;>
      simp_all [differentialCoordinates, coords1_vector, birth0, death0, birth1, death1,
        Hook.support, support, a, b, c, d, e, f, g, h, gridPoint_le_iff, gridPoint_eq_iff]
    all_goals first | (solve | linear_combination hs) | linear_combination -hs
  · apply coords1_ext
    intro i
    rw [coords1_map, coords1_zero]
    rcases hq with rfl | rfl
    all_goals fin_cases i <;> simp [coords1_vector, birth1, death1,
      Hook.support, a, b, c, f, g, h, gridPoint_le_iff, gridPoint_eq_iff]

private theorem q1_dyingLift {p q : grid.Point} (hpq : p ≤ q)
    (v : (K1 (k := k)).obj p)
    (hdie : structureMapLinear (K1 (k := k)) hpq v = 0) :
    ∃ w : (P1 (k := k)).obj p, ((q1 (k := k)).app p).hom w = v ∧
      structureMapLinear (P1 (k := k)) hpq w = 0 := by
  by_cases hq : q = h
  · subst q
    obtain ⟨w, hw⟩ := q1_surjective p v
    refine ⟨w, hw, ?_⟩
    apply coords1_ext
    intro i
    rw [coords1_map, coords1_zero]
    fin_cases i <;> simp [birth1, death1, Hook.support, a, b, c, f, g, h]
  · by_cases hcf : p = c ∧ q = f
    · rcases hcf with ⟨rfl, rfl⟩
      exact syzygy_center_dyingLift hpq (Or.inl rfl) v hdie
    · by_cases hcg : p = c ∧ q = g
      · rcases hcg with ⟨rfl, rfl⟩
        exact syzygy_center_dyingLift hpq (Or.inr rfl) v hdie
      · have hv := syzygy_dying_eq_zero hpq hq hcf hcg v hdie
        exact ⟨0, by simp [hv], by simp⟩

/-- The literal hook `L` is the rank-exact kernel of the actual first quotient. -/
theorem q1_rankExact : IsRankExact (j (k := k)) q1 where
  toIsPointwiseShortExact := row1_shortExact
  finiteDimensional := p1_finiteDimensional
  rank_add hpq := (row1_shortExact.rank_add_iff_lift_kernel hpq).mpr (q1_dyingLift hpq)

private theorem offDiagonal0 (i r : Fin 4) (hne : i ≠ r)
    (α : hooks0 (k := k) i ⟶ hooks0 r) : α = 0 := by
  by_contra hα
  have ho := FiniteRankProjectiveResolution.hook_hom_nonzero_implies_endpoint_order
    (endpoints0 i) (endpoints0 r) α hα
  fin_cases i <;> fin_cases r <;> simp_all [birth0, death0,
    a, b, d, e, f, g, gridPoint_le_iff]

private theorem offDiagonal1 (i r : Fin 4) (hne : i ≠ r)
    (α : hooks1 (k := k) i ⟶ hooks1 r) : α = 0 := by
  by_contra hα
  have ho := FiniteRankProjectiveResolution.hook_hom_nonzero_implies_endpoint_order
    (endpoints1 i) (endpoints1 r) α hα
  fin_cases i <;> fin_cases r <;> simp_all [birth1, death1,
    a, b, c, f, g, h, gridPoint_le_iff]

private theorem diagonal_endomorphism_eq_id
    (F : Fin 4 → PModule.{u,0,u} k grid.Point)
    (hoff : ∀ i r, i ≠ r → ∀ α : F i ⟶ F r, α = 0)
    (hdiag : ∀ i (α : End (F i)), ∃ r : k, α = r • 𝟙 (F i))
    {N : PModule.{u,0,u} k grid.Point} (q : (⨁ F) ⟶ N)
    (hnonzero : ∀ i, biproduct.ι F i ≫ q ≠ 0)
    (u : End (⨁ F)) (hu : u ≫ q = q) : u = 𝟙 (⨁ F) := by
  apply biproduct.hom_ext'
  intro i
  obtain ⟨r, hr⟩ := hdiag i (biproduct.ι F i ≫ u ≫ biproduct.π F i)
  have hi : biproduct.ι F i ≫ u = (r • 𝟙 (F i)) ≫ biproduct.ι F i := by
    apply biproduct.hom_ext
    intro t
    by_cases hit : i = t
    · subst t
      simpa only [Category.assoc, biproduct.ι_π_self, Category.comp_id] using hr
    · rw [Category.assoc, hoff i t hit (biproduct.ι F i ≫ u ≫ biproduct.π F t)]
      simp [Category.assoc, biproduct.ι_π, hit]
  have he : r • (biproduct.ι F i ≫ q) = biproduct.ι F i ≫ q := by
    calc
      _ = ((r • 𝟙 (F i)) ≫ biproduct.ι F i) ≫ q := by simp
      _ = (biproduct.ι F i ≫ u) ≫ q := by rw [hi]
      _ = _ := by rw [Category.assoc, hu]
  have hr1 : r = 1 := by
    by_contra hne
    have hz : (r - 1) • (biproduct.ι F i ≫ q) = 0 := by
      rw [sub_smul, one_smul, he, sub_self]
    exact hnonzero i ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne))
  simpa only [hr1, one_smul, Category.id_comp, Category.comp_id] using hi

private theorem augmentationComponent_ne_zero {x y : grid.Point} (hxy : x < y)
    (hx : x ∈ support) (hy : y ∉ support) :
    augmentationComponent (k := k) x y hxy hx hy ≠ 0 := by
  intro hz
  have he := congrArg (fun α : Hook.module (k := k) x y ⟶ finiteModule =>
    ((α.app x).hom (SupportInterval.one (Hook.support x y) (Hook.birth_mem hxy)) : k)) hz
  erw [augmentation_val] at he
  simpa [hx, SupportInterval.one] using he

private theorem q0_component_ne_zero (i : Fin 4) :
    biproduct.ι hooks0 i ≫ q0 (k := k) ≠ 0 := by
  rw [q0, biproduct.ι_desc]
  fin_cases i
  · exact augmentationComponent_ne_zero a_lt_d a_mem_support d_not_support
  · exact augmentationComponent_ne_zero a_lt_g a_mem_support g_not_support
  · exact augmentationComponent_ne_zero b_lt_f b_mem_support f_not_support
  · exact augmentationComponent_ne_zero b_lt_e b_mem_support e_not_support

private theorem hookMap_ne_zero {x y z t : grid.Point} (hxy : x < y) (hzt : z < t)
    (hzx : z ≤ x) (hty : t ≤ y) (htx : ¬ t ≤ x) :
    hookMap (k := k) hxy hzt hzx hty htx ≠ 0 := by
  intro hz
  have he := congrArg (fun α : Hook.module (k := k) x y ⟶ Hook.module z t =>
    ((α.app x).hom (SupportInterval.one (Hook.support x y) (Hook.birth_mem hxy)) : k)) hz
  erw [hookMap_val] at he
  simpa [show x ∈ Hook.support z t from ⟨hzx, htx⟩, SupportInterval.one] using he

private theorem q1_component_ne_zero (i : Fin 4) :
    biproduct.ι hooks1 i ≫ q1 (k := k) ≠ 0 := by
  intro hz
  have he : biproduct.ι hooks1 i ≫ d1 (k := k) = 0 := by
    rw [← q1_comp_inclusion, ← Category.assoc, hz, zero_comp]
  have hp := congrArg (fun α => α ≫ biproduct.π (hooks0 (k := k)) (![0, 2, 0, 1] i)) he
  fin_cases i <;>
    simp [d1, d1Column, d1ColumnE, d1ColumnF, d1ColumnJ, d1ColumnK,
      Category.assoc, Preadditive.sub_comp] at hp
  · exact hookMap_ne_zero a_lt_h a_lt_d (by simp [a]) (by simp [d, h]) (by simp [d, a]) hp
  · exact hookMap_ne_zero b_lt_h b_lt_f (by simp [b]) (by simp [f, h]) (by simp [f, b]) hp
  · exact hookMap_ne_zero c_lt_f a_lt_d (by simp [a, c]) (by simp [d, f]) (by simp [d, c]) hp
  · exact hookMap_ne_zero c_lt_g a_lt_g (by simp [a, c]) (by simp [g]) (by simp [g, c]) hp

private theorem p0_rankProjective : IsRankProjective (P0 (k := k)) :=
  IsRankProjective.biproduct hooks0 (fun i => Hook.isRankProjective (endpoints0 i))

private theorem p1_rankProjective : IsRankProjective (P1 (k := k)) :=
  IsRankProjective.biproduct hooks1 (fun i => Hook.isRankProjective (endpoints1 i))

/-- The actual augmentation is a rank-projective cover. -/
theorem q0_isRankProjectiveCover : IsRankProjectiveCover (q0 (k := k)) where
  term_rank_projective := p0_rankProjective
  row_rank_exact := q0_rankExact
  endomorphism_isIso u hu := by
    have he := diagonal_endomorphism_eq_id hooks0 offDiagonal0
      (fun i α => ⟨_, Hook.end_eq_smul_id (endpoints0 i) α⟩) q0 q0_component_ne_zero u hu
    rw [he]
    infer_instance

/-- The actual first-syzygy quotient is a rank-projective cover. -/
theorem q1_isRankProjectiveCover : IsRankProjectiveCover (q1 (k := k)) where
  term_rank_projective := p1_rankProjective
  row_rank_exact := q1_rankExact.isRankDeflation.rankExact_kernel
  endomorphism_isIso u hu := by
    have he := diagonal_endomorphism_eq_id hooks1 offDiagonal1
      (fun i α => ⟨_, Hook.end_eq_smul_id (endpoints1 i) α⟩) q1 q1_component_ne_zero u hu
    rw [he]
    infer_instance

private theorem last_rankExact :
    IsRankExact (0 : (0 : PModule.{u,0,u} k grid.Point) ⟶ L) (𝟙 (L (k := k))) := by
  have hs : IsPointwiseShortExact
      (0 : (0 : PModule.{u,0,u} k grid.Point) ⟶ L) (𝟙 (L (k := k))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p y
      exact ⟨y, by simp⟩
    · intro p
      ext x
      simp
  exact hs.rankExact_of_section (𝟙 (L (k := k))) (by simp)

private abbrev resolutionKernels : Fin 4 → PModule.{u,0,u} k grid.Point
  | 0 => finiteModule | 1 => K1 | 2 => L | 3 => 0

private abbrev resolutionTerms : Fin 3 → PModule.{u,0,u} k grid.Point
  | 0 => P0 | 1 => P1 | 2 => L

private def resolutionInclusions : ∀ i : Fin 3,
    resolutionKernels (k := k) i.succ ⟶ resolutionTerms i
  | 0 => kernel.ι q0 | 1 => j | 2 => 0

private def resolutionQuotients : ∀ i : Fin 3,
    resolutionTerms (k := k) i ⟶ resolutionKernels i.castSucc
  | 0 => q0 | 1 => q1 | 2 => 𝟙 L

/-- The literal length-three minimal resolution has kernels `(M,K1,L,0)`,
terms `(P0,P1,L)`, inclusions `(kernel.ι q0,j,0)`, and quotients `(q0,q1,id)`. -/
def finiteMinimalResolution :
    MinimalFiniteRankProjectiveResolution (k := k) (M := finiteModule) where
  resolution := {
    length := 3
    kernel := resolutionKernels
    term := resolutionTerms
    inclusion := resolutionInclusions
    quotient := resolutionQuotients
    row_rank_exact := by
      intro i
      fin_cases i
      exacts [q0_rankExact, q1_rankExact, last_rankExact]
    initial_iso := Iso.refl _
    terminal_iso := Iso.refl _
    term_rank_projective := by
      intro i
      fin_cases i
      exacts [p0_rankProjective, p1_rankProjective, Hook.isRankProjective c_lt_h]
  }
  quotient_is_cover := by
    intro i
    fin_cases i
    · exact q0_isRankProjectiveCover
    · exact q1_isRankProjectiveCover
    · exact IsRankProjectiveCover.of_identity (fun p => Hook.finiteDimensional c h p)
        (Hook.isRankProjective c_lt_h)

/-- The selected finite resolution stores three rows. -/
@[simp] theorem finiteMinimalResolution_length :
    (finiteMinimalResolution (k := k)).resolution.length = 3 := rfl

/-- The selected kernel objects are literally the prescribed four objects. -/
theorem finiteMinimalResolution_kernels :
    (finiteMinimalResolution (k := k)).resolution.kernel =
      ![finiteModule, K1, L, 0] := by
  funext i
  fin_cases i <;> rfl

/-- The selected term objects are literally the prescribed hook sums and `L`. -/
theorem finiteMinimalResolution_terms :
    (finiteMinimalResolution (k := k)).resolution.term = ![P0, P1, L] := by
  funext i
  fin_cases i <;> rfl

/-- The first quotient of the selected resolution is the actual augmentation. -/
@[simp] theorem finiteMinimalResolution_quotient_zero :
    (finiteMinimalResolution (k := k)).resolution.quotient (0 : Fin 3) = q0 := rfl

/-- The next quotient is the actual categorical kernel lift. -/
@[simp] theorem finiteMinimalResolution_quotient_one :
    (finiteMinimalResolution (k := k)).resolution.quotient (1 : Fin 3) = q1 := rfl

/-- The last quotient is the identity of the given second hook. -/
@[simp] theorem finiteMinimalResolution_quotient_two :
    (finiteMinimalResolution (k := k)).resolution.quotient (2 : Fin 3) = 𝟙 L := rfl

/-- The first inclusion is the actual categorical kernel inclusion. -/
@[simp] theorem finiteMinimalResolution_inclusion_zero :
    (finiteMinimalResolution (k := k)).resolution.inclusion (0 : Fin 3) = kernel.ι q0 := rfl

/-- The second inclusion is the prescribed signed column `j`. -/
@[simp] theorem finiteMinimalResolution_inclusion_one :
    (finiteMinimalResolution (k := k)).resolution.inclusion (1 : Fin 3) = j := rfl

/-- The terminal row has the zero inclusion. -/
@[simp] theorem finiteMinimalResolution_inclusion_two :
    (finiteMinimalResolution (k := k)).resolution.inclusion (2 : Fin 3) = 0 := rfl

/-- The zero-padded second term is literally `H(c,h)`. -/
@[simp] theorem finiteMinimalResolution_termAt_two :
    (finiteMinimalResolution (k := k)).termAt 2 = L := rfl

/-- The given second hook has a nonzero supported unit at the center. -/
theorem secondHook_not_isZero : ¬ IsZero (L (k := k)) := by
  intro hz
  have he := congrArg (fun α : End (L (k := k)) =>
    ((α.app c).hom (SupportInterval.one (Hook.support c h) (Hook.birth_mem c_lt_h)) : k))
    (hz.eq_of_src (𝟙 L) 0)
  exact (one_ne_zero : (1 : k) ≠ 0) (by simpa [SupportInterval.one] using he)

/-- The augmentation is a genuine nonzero morphism. -/
theorem q0_ne_zero : q0 (k := k) ≠ 0 := by
  intro hz
  exact q0_component_ne_zero 0 (by rw [hz, comp_zero])

/-- The first matrix differential is a genuine nonzero morphism. -/
theorem d1_ne_zero : d1 (k := k) ≠ 0 := by
  intro hz
  have hq : q1 (k := k) = 0 := by
    apply (cancel_mono (kernel.ι (q0 (k := k)))).mp
    simp [hz]
  exact q1_component_ne_zero 0 (by rw [hq, comp_zero])

/-- The prescribed second differential is nonzero over every coefficient field. -/
theorem j_ne_zero : j (k := k) ≠ 0 := by
  intro hz
  have hunit : SupportInterval.one (k := k) (Hook.support c h) (Hook.birth_mem c_lt_h) = 0 :=
    j_injective c (by simp [hz])
  exact one_ne_zero (congrArg Subtype.val hunit)

/-- Every certified minimal finite resolution has a nonzero second term,
independently of its recorded terminal zero padding. -/
theorem finiteMinimalResolution_second_term_nonzero
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := finiteModule)) :
    ¬ IsZero (R.termAt 2) := by
  intro hz
  obtain ⟨e⟩ := R.termAt_nonempty_iso finiteMinimalResolution 2
  have hs := IsZero.of_iso hz e.symm
  exact secondHook_not_isZero (by simpa only [finiteMinimalResolution_termAt_two] using hs)

/-- Every certified minimal finite resolution vanishes strictly above degree two. -/
theorem finiteMinimalResolution_terms_vanish_above_two
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := finiteModule))
    (j : ℕ) (hj : 2 < j) : IsZero (R.termAt j) := by
  obtain ⟨e⟩ := R.termAt_nonempty_iso finiteMinimalResolution j
  apply IsZero.of_iso (e := e)
  rw [finiteMinimalResolution.termAt_eq_zero (by change 3 ≤ j; omega)]
  exact isZero_zero _

/-- The coefficient field alone supplies the explicit minimal finite witness. -/
theorem exists_finiteMinimalResolution_degree_two :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := k) (M := finiteModule),
      ¬ IsZero (R.termAt 2) ∧ ∀ j, 2 < j → IsZero (R.termAt j) :=
  ⟨finiteMinimalResolution, finiteMinimalResolution_second_term_nonzero _,
    finiteMinimalResolution_terms_vanish_above_two _⟩

/-- Ordinary projective dimension two for the actual finite hook-generator Hom
object. This computes the dimension after applying the hook-Hom functor. -/
theorem finite_hookHom_projectiveDimension_eq_two :
    projectiveDimension
      ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := grid.Point)).obj finiteModule) = 2 := by
  apply le_antisymm
  · exact (FiniteRankProjectiveHomDimension.projectiveDimension_le_iff
      finiteMinimalResolution 2).mpr (finiteMinimalResolution_terms_vanish_above_two _)
  · apply (projectiveDimension_ge_iff _ 2).mpr
    intro hdim
    have hle : HasProjectiveDimensionLE
        ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := grid.Point)).obj finiteModule) 1 := hdim
    exact finiteMinimalResolution_second_term_nonzero finiteMinimalResolution
      ((FiniteRankProjectiveHomDimension.hasProjectiveDimensionLE_iff
        finiteMinimalResolution 1).mp hle 2 (by decide))

end

end TDA.Persistence.RankResolutionDegreeTwo
