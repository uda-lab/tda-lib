import TDA.Reeb.IntervalSingularHomologyStability
import TDA.Topology.MayerVietorisSequence

/-!
# Mayer–Vietoris sequences of interval squares

For `a + b > 0` write `I_(a,b) = (-a, b)` (`intervalAB`). Increasing the two endpoints
independently, `a ≤ a'` and `b ≤ b'`, gives four intervals: the southwest `I_(a,b)`, the left
`I_(a',b)`, the right `I_(a,b')` and the northeast `I_(a',b')`, with `left ∩ right = southwest`
and `left ∪ right = northeast` (`coe_intervalAB_inter`, `coe_intervalAB_union`). An
`IntervalMVSquare` is four open intervals with these two set identities;
`IntervalMVSquare.ofEndpoints` is the square of `I_(a,b) ≤ I_(a',b), I_(a,b') ≤ I_(a',b')`.

For `f : C(X, ℝ)` and a square `Q`, the preimages `f ⁻¹ left` and `f ⁻¹ right` are open in
`f ⁻¹ NE` and cover it (`IntervalMVSquare.interior_coverSet_union`), so the generic
Mayer–Vietoris sequence of `TDA.Topology.SmallChainsQuasiIso` applies. Through the
homeomorphisms `IntervalMVSquare.coverSetIso` of the pieces with the preimages of the corners,
it becomes the sequence of the functor `intervalSingularHomology k n f`:

`⋯ ⟶ H_{n+1}(f ⁻¹ NE) ⟶ H_n(f ⁻¹ SW) ⟶ H_n(f ⁻¹ left) ⊞ H_n(f ⁻¹ right) ⟶ H_n(f ⁻¹ NE) ⟶ ⋯`

with connecting map `intervalMVδ`, the map `intervalMVInterMap = (inc, -inc)` and the sum map
`intervalMVSumMap`. It is exact at the three places (`intervalMV_exact_inter`,
`intervalMV_exact_sum`, `intervalMV_exact_ne`).

**Naturality.** For two functions `f, g` and squares `Q, Q'` with `f x ∈ Q.left → g x ∈ Q'.left`
and `f x ∈ Q.right → g x ∈ Q'.right`, the identity of `X` maps every corner preimage of `(f, Q)`
into the corresponding one of `(g, Q')` (`intervalPreimageMap`), and the three maps of the
sequence commute with the induced maps (`intervalMVδ_comp_map`, `intervalMVInterMap_comp_map`,
`intervalMVSumMap_comp_map`), by `mayerVietorisδ_naturality`. Two instances:

* **naturality in `(a, b)`**: a morphism of squares `IntervalMVSquare.Hom Q Q'` (componentwise
  inclusions, for instance independent endpoint increases, `IntervalMVSquare.hom_ofEndpoints`)
  gives `intervalMVδ_naturality`, `intervalMVInterMap_naturality` and
  `intervalMVSumMap_naturality` for the maps of `intervalSingularHomology k n f`;
* **compatibility with the thickening witness** of E2: for `|f - g| ≤ ε`, the corners of the
  thickened square `IntervalMVSquare.thickenEndpoints` are literally `thicken ε` of the corners
  (`thicken_intervalAB`), and the three maps commute with the components of
  `intervalSingularHomologyPerturbation` (`intervalMVδ_comp_perturbation_app` and its companions),
  hence with both witnesses `φ` and `ψ` of `intervalSingularHomologyInterleaving`
  (`intervalMVδ_comp_interleaving_φ`, `intervalMVδ_comp_interleaving_ψ`).
-/

open CategoryTheory Limits AlgebraicTopology
open scoped NNReal

universe u

namespace TDA.Reeb

open OpenInterval TDA.Topology

/-! ### The intervals `I_(a,b)` -/

/-- The open interval `I_(a,b) = (-a, b)`. -/
def intervalAB (a b : ℝ) : OpenInterval := ioo (-a) b

@[simp]
theorem coe_intervalAB (a b : ℝ) : (intervalAB a b : Set ℝ) = Set.Ioo (-a) b :=
  rfl

/-- `I_(a,b)` is monotone in both endpoints. -/
theorem intervalAB_mono {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    intervalAB a b ≤ intervalAB a' b' :=
  OpenInterval.le_iff_subset.2 (Set.Ioo_subset_Ioo (by linarith) hb)

/-- Increasing the two endpoints independently: `I_(a',b) ∩ I_(a,b') = I_(a,b)`. -/
theorem coe_intervalAB_inter {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    (intervalAB a' b : Set ℝ) ∩ intervalAB a b' = intervalAB a b := by
  ext x
  simp only [coe_intervalAB, Set.mem_inter_iff, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨_, h₂⟩, h₃, _⟩
    exact ⟨h₃, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨by linarith, h₂⟩, h₁, by linarith⟩

/-- Increasing the two endpoints independently: `I_(a',b) ∪ I_(a,b') = I_(a',b')` when
`a + b > 0`. -/
theorem coe_intervalAB_union {a a' b b' : ℝ} (hab : 0 < a + b) (ha : a ≤ a') (hb : b ≤ b') :
    (intervalAB a' b : Set ℝ) ∪ intervalAB a b' = intervalAB a' b' := by
  ext x
  simp only [coe_intervalAB, Set.mem_union, Set.mem_Ioo]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨h₁, by linarith⟩
    · exact ⟨by linarith, h₂⟩
  · rintro ⟨h₁, h₂⟩
    by_cases h : x < b
    · exact Or.inl ⟨h₁, h⟩
    · exact Or.inr ⟨by linarith, h₂⟩

/-- Thickening `I_(a,b)` by `ε` increases both endpoints by `ε`. -/
theorem thicken_intervalAB {a b : ℝ} (hab : 0 < a + b) (ε : ℝ≥0) :
    thicken ε (intervalAB a b) = intervalAB (a + ε) (b + ε) := by
  rw [intervalAB, thicken_ioo (by linarith)]
  congr 1
  ring

/-! ### Interval squares -/

/-- An interval Mayer–Vietoris square: open intervals with `left ∩ right = sw` and
`left ∪ right = ne` as sets. -/
structure IntervalMVSquare where
  /-- The southwest corner, the intersection. -/
  sw : OpenInterval
  /-- The left piece. -/
  left : OpenInterval
  /-- The right piece. -/
  right : OpenInterval
  /-- The northeast corner, the union. -/
  ne : OpenInterval
  /-- The two pieces meet in the southwest corner. -/
  inter_eq : (left : Set ℝ) ∩ right = sw
  /-- The two pieces cover the northeast corner. -/
  union_eq : (left : Set ℝ) ∪ right = ne

namespace IntervalMVSquare

variable (Q : IntervalMVSquare)

theorem sw_le_left : Q.sw ≤ Q.left :=
  OpenInterval.le_iff_subset.2 (Q.inter_eq ▸ Set.inter_subset_left)

theorem sw_le_right : Q.sw ≤ Q.right :=
  OpenInterval.le_iff_subset.2 (Q.inter_eq ▸ Set.inter_subset_right)

theorem left_le_ne : Q.left ≤ Q.ne :=
  OpenInterval.le_iff_subset.2 (Q.union_eq ▸ Set.subset_union_left)

theorem right_le_ne : Q.right ≤ Q.ne :=
  OpenInterval.le_iff_subset.2 (Q.union_eq ▸ Set.subset_union_right)

/-- The endpoint square `SW = I_(a,b)`, `left = I_(a',b)`, `right = I_(a,b')`,
`NE = I_(a',b')`, for `a + b > 0`, `a ≤ a'` and `b ≤ b'`. -/
def ofEndpoints (a b a' b' : ℝ) (hab : 0 < a + b) (ha : a ≤ a') (hb : b ≤ b') :
    IntervalMVSquare where
  sw := intervalAB a b
  left := intervalAB a' b
  right := intervalAB a b'
  ne := intervalAB a' b'
  inter_eq := coe_intervalAB_inter ha hb
  union_eq := coe_intervalAB_union hab ha hb

/-- The thickened endpoint square: its corners are `thicken ε` of the corners of
`ofEndpoints a b a' b'`, so that the components of E2's thickening witness at the corners have
these corners as targets. -/
def thickenEndpoints (a b a' b' : ℝ) (hab : 0 < a + b) (ha : a ≤ a') (hb : b ≤ b') (ε : ℝ≥0) :
    IntervalMVSquare where
  sw := thicken ε (intervalAB a b)
  left := thicken ε (intervalAB a' b)
  right := thicken ε (intervalAB a b')
  ne := thicken ε (intervalAB a' b')
  inter_eq := by
    rw [thicken_intervalAB (by linarith), thicken_intervalAB (by linarith),
      thicken_intervalAB hab]
    exact coe_intervalAB_inter (by linarith) (by linarith)
  union_eq := by
    rw [thicken_intervalAB (by linarith), thicken_intervalAB (by linarith),
      thicken_intervalAB (by linarith)]
    exact coe_intervalAB_union (by have := ε.coe_nonneg; linarith) (by linarith) (by linarith)

/-- The thickened endpoint square is the endpoint square of the thickened endpoints. -/
theorem thickenEndpoints_eq (a b a' b' : ℝ) (hab : 0 < a + b) (ha : a ≤ a') (hb : b ≤ b')
    (ε : ℝ≥0) :
    thickenEndpoints a b a' b' hab ha hb ε =
      ofEndpoints (a + ε) (b + ε) (a' + ε) (b' + ε) (by have := ε.coe_nonneg; linarith)
        (by linarith) (by linarith) := by
  simp only [thickenEndpoints, ofEndpoints]
  rw [mk.injEq, thicken_intervalAB hab, thicken_intervalAB (by linarith),
    thicken_intervalAB (by linarith), thicken_intervalAB (by linarith)]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A morphism of squares: componentwise inclusions. -/
structure Hom (Q Q' : IntervalMVSquare) : Prop where
  /-- Inclusion of the southwest corners. -/
  sw : Q.sw ≤ Q'.sw
  /-- Inclusion of the left pieces. -/
  left : Q.left ≤ Q'.left
  /-- Inclusion of the right pieces. -/
  right : Q.right ≤ Q'.right
  /-- Inclusion of the northeast corners. -/
  ne : Q.ne ≤ Q'.ne

/-- Independent increases of the endpoints give a morphism of endpoint squares. -/
theorem hom_ofEndpoints {a b a' b' c d c' d' : ℝ} (h₁ : 0 < a + b) (h₂ : a ≤ a') (h₃ : b ≤ b')
    (h₄ : 0 < c + d) (h₅ : c ≤ c') (h₆ : d ≤ d') (hac : a ≤ c) (hbd : b ≤ d) (hac' : a' ≤ c')
    (hbd' : b' ≤ d') :
    Hom (ofEndpoints a b a' b' h₁ h₂ h₃) (ofEndpoints c d c' d' h₄ h₅ h₆) :=
  ⟨intervalAB_mono hac hbd, intervalAB_mono hac' hbd, intervalAB_mono hac hbd',
    intervalAB_mono hac' hbd'⟩

/-- If `g` sends the left and right preimages of `f` into those of `Q'`, it does so for the
southwest corner. -/
theorem mapsTo_sw {X : Type*} {f g : X → ℝ} {Q Q' : IntervalMVSquare}
    (hl : ∀ x, f x ∈ Q.left → g x ∈ Q'.left) (hr : ∀ x, f x ∈ Q.right → g x ∈ Q'.right) :
    ∀ x, f x ∈ Q.sw → g x ∈ Q'.sw := fun x hx => by
  have h : f x ∈ (Q.left : Set ℝ) ∩ Q.right := Q.inter_eq ▸ hx
  have h' : g x ∈ (Q'.left : Set ℝ) ∩ Q'.right := ⟨hl x h.1, hr x h.2⟩
  rw [Q'.inter_eq] at h'
  exact h'

/-- If `g` sends the left and right preimages of `f` into those of `Q'`, it does so for the
northeast corner. -/
theorem mapsTo_ne {X : Type*} {f g : X → ℝ} {Q Q' : IntervalMVSquare}
    (hl : ∀ x, f x ∈ Q.left → g x ∈ Q'.left) (hr : ∀ x, f x ∈ Q.right → g x ∈ Q'.right) :
    ∀ x, f x ∈ Q.ne → g x ∈ Q'.ne := fun x hx => by
  have h : f x ∈ (Q.left : Set ℝ) ∪ Q.right := Q.union_eq ▸ hx
  have h' : g x ∈ (Q'.left : Set ℝ) ∪ Q'.right := h.elim (fun h => Or.inl (hl x h))
    (fun h => Or.inr (hr x h))
  rw [Q'.union_eq] at h'
  exact h'

/-! ### The cover of the northeast preimage -/

variable {X : Type u} [TopologicalSpace X] (f : C(X, ℝ))

/-- The piece `{y ∈ f ⁻¹ NE | f y ∈ J}` of the northeast preimage. -/
def coverSet (J : OpenInterval) : Set ((intervalPreimageTopCat f).obj Q.ne) :=
  {y | f y.1 ∈ J}

theorem isOpen_coverSet (J : OpenInterval) : IsOpen (Q.coverSet f J) :=
  J.isOpen.preimage (f.continuous.comp continuous_subtype_val)

/-- The left and right pieces cover the northeast preimage by their interiors. -/
theorem interior_coverSet_union :
    interior (Q.coverSet f Q.left) ∪ interior (Q.coverSet f Q.right) = Set.univ := by
  rw [(Q.isOpen_coverSet f _).interior_eq, (Q.isOpen_coverSet f _).interior_eq]
  ext y
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  have h : f y.1 ∈ ((Q.left : Set ℝ) ∪ Q.right) := Q.union_eq ▸ y.2
  exact h

/-- A subset `S` of the northeast preimage consisting of the points with `f y ∈ J`, for
`J ≤ NE`, is homeomorphic to the preimage `f ⁻¹ J`; the homeomorphism is the identity on
points of `X`. -/
def coverSetIso {J : OpenInterval} (S : Set ((intervalPreimageTopCat f).obj Q.ne))
    (hS : ∀ y, y ∈ S ↔ f y.1 ∈ J) (hJ : J ≤ Q.ne) :
    TopCat.of S ≅ (intervalPreimageTopCat f).obj J where
  hom := TopCat.ofHom ⟨fun y => ⟨y.1.1, (hS y.1).1 y.2⟩, by fun_prop⟩
  inv := TopCat.ofHom ⟨fun x => ⟨⟨x.1, hJ x.2⟩, (hS _).2 x.2⟩, by fun_prop⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

@[simp]
theorem coverSetIso_hom_apply_val {J : OpenInterval} (S : Set ((intervalPreimageTopCat f).obj Q.ne))
    (hS : ∀ y, y ∈ S ↔ f y.1 ∈ J) (hJ : J ≤ Q.ne) (y : TopCat.of S) :
    ((Q.coverSetIso f S hS hJ).hom y).1 = y.1.1 :=
  rfl

/-- The left piece is homeomorphic to `f ⁻¹ left`. -/
abbrev leftIso : TopCat.of (Q.coverSet f Q.left) ≅ (intervalPreimageTopCat f).obj Q.left :=
  Q.coverSetIso f _ (fun _ => Iff.rfl) Q.left_le_ne

/-- The right piece is homeomorphic to `f ⁻¹ right`. -/
abbrev rightIso : TopCat.of (Q.coverSet f Q.right) ≅ (intervalPreimageTopCat f).obj Q.right :=
  Q.coverSetIso f _ (fun _ => Iff.rfl) Q.right_le_ne

/-- The intersection of the two pieces is homeomorphic to `f ⁻¹ SW`. -/
abbrev swIso : TopCat.of ↥(Q.coverSet f Q.left ∩ Q.coverSet f Q.right) ≅
    (intervalPreimageTopCat f).obj Q.sw :=
  Q.coverSetIso f _ (fun y => by
    change f y.1 ∈ (Q.left : Set ℝ) ∩ Q.right ↔ _
    rw [Q.inter_eq]; rfl) (Q.sw_le_left.trans Q.left_le_ne)

end IntervalMVSquare

/-! ### The Mayer–Vietoris sequence of an interval square -/

section Sequence

variable {X : Type u} [TopologicalSpace X] (f : C(X, ℝ)) (Q : IntervalMVSquare) (k : Type u)
  [Ring k] (n : ℕ)

/-- The **interval Mayer–Vietoris connecting map** `H_{n+1}(f ⁻¹ NE) ⟶ H_n(f ⁻¹ SW)`: the generic
connecting map `mayerVietorisδ` of the cover of `f ⁻¹ NE` by the preimages of the left and right
intervals, followed by the homeomorphism of their intersection with `f ⁻¹ SW`. -/
noncomputable def intervalMVδ :
    ((singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj (ModuleCat.of k k)).obj
        ((intervalPreimageTopCat f).obj Q.ne) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj
        ((intervalPreimageTopCat f).obj Q.sw) :=
  mayerVietorisδ (Q.coverSet f Q.left) (Q.coverSet f Q.right) (ModuleCat.of k k)
      (Q.interior_coverSet_union f) n ≫
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map (Q.swIso f).hom

/-- The map `H_n(f ⁻¹ SW) ⟶ H_n(f ⁻¹ left) ⊞ H_n(f ⁻¹ right)` of the interval Mayer–Vietoris
sequence: the inclusions, with the sign `(inc, -inc)`. -/
noncomputable def intervalMVInterMap :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj
        ((intervalPreimageTopCat f).obj Q.sw) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj
          ((intervalPreimageTopCat f).obj Q.left) ⊞
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj
          ((intervalPreimageTopCat f).obj Q.right) :=
  biprod.lift
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
      ((intervalPreimageTopCat f).map (homOfLE Q.sw_le_left)))
    (-((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
      ((intervalPreimageTopCat f).map (homOfLE Q.sw_le_right)))

/-- The map `H_n(f ⁻¹ left) ⊞ H_n(f ⁻¹ right) ⟶ H_n(f ⁻¹ NE)` of the interval Mayer–Vietoris
sequence: the sum of the inclusions. -/
noncomputable def intervalMVSumMap :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj
          ((intervalPreimageTopCat f).obj Q.left) ⊞
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj
          ((intervalPreimageTopCat f).obj Q.right) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj
        ((intervalPreimageTopCat f).obj Q.ne) :=
  biprod.desc
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
      ((intervalPreimageTopCat f).map (homOfLE Q.left_le_ne)))
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
      ((intervalPreimageTopCat f).map (homOfLE Q.right_le_ne)))

/-- The generic `(inc, -inc)` and the interval one agree under the homeomorphisms of the pieces
with the preimages of the corners. -/
private theorem mayerVietorisInterMap_comp_biprod_map :
    mayerVietorisInterMap (Q.coverSet f Q.left) (Q.coverSet f Q.right) (ModuleCat.of k k) n ≫
        biprod.map
          (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
            (Q.leftIso f).hom)
          (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
            (Q.rightIso f).hom) =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
          (Q.swIso f).hom ≫ intervalMVInterMap f Q k n := by
  apply biprod.hom_ext
  · simp only [mayerVietorisInterMap, intervalMVInterMap, Category.assoc, biprod.map_fst,
      biprod.lift_fst_assoc, biprod.lift_fst, ← Functor.map_comp]
    rfl
  · simp only [mayerVietorisInterMap, intervalMVInterMap, Category.assoc, biprod.map_snd,
      biprod.lift_snd_assoc, biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg,
      ← Functor.map_comp]
    rfl

/-- The generic sum map and the interval one agree under the homeomorphisms of the pieces with
the preimages of the corners. -/
private theorem mayerVietorisSumMap_eq_biprod_map_comp :
    mayerVietorisSumMap (Q.coverSet f Q.left) (Q.coverSet f Q.right) (ModuleCat.of k k) n =
      biprod.map
          (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
            (Q.leftIso f).hom)
          (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
            (Q.rightIso f).hom) ≫ intervalMVSumMap f Q k n := by
  apply biprod.hom_ext'
  · simp only [mayerVietorisSumMap, intervalMVSumMap, biprod.inl_desc, biprod.inl_map_assoc,
      ← Functor.map_comp]
    rfl
  · simp only [mayerVietorisSumMap, intervalMVSumMap, biprod.inr_desc, biprod.inr_map_assoc,
      ← Functor.map_comp]
    rfl

/-- The connecting map followed by `(inc, -inc)` vanishes. -/
theorem intervalMVδ_comp_intervalMVInterMap :
    intervalMVδ f Q k n ≫ intervalMVInterMap f Q k n = 0 := by
  rw [intervalMVδ, Category.assoc, ← mayerVietorisInterMap_comp_biprod_map, ← Category.assoc,
    mayerVietorisδ_comp_mayerVietorisInterMap, zero_comp]

/-- `(inc, -inc)` followed by the sum of the inclusions vanishes. -/
theorem intervalMVInterMap_comp_intervalMVSumMap :
    intervalMVInterMap f Q k n ≫ intervalMVSumMap f Q k n = 0 := by
  have e : (homOfLE Q.sw_le_left ≫ homOfLE Q.left_le_ne : Q.sw ⟶ Q.ne) =
      homOfLE Q.sw_le_right ≫ homOfLE Q.right_le_ne :=
    Subsingleton.elim _ _
  simp only [intervalMVInterMap, intervalMVSumMap, biprod.lift_desc, Preadditive.neg_comp,
    ← Functor.map_comp, e, add_neg_cancel]

/-- The sum of the inclusions followed by the connecting map vanishes. -/
theorem intervalMVSumMap_comp_intervalMVδ :
    intervalMVSumMap f Q k (n + 1) ≫ intervalMVδ f Q k n = 0 := by
  rw [← cancel_epi (biprod.map
      (((singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj (ModuleCat.of k k)).map
        (Q.leftIso f).hom)
      (((singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj (ModuleCat.of k k)).map
        (Q.rightIso f).hom)), comp_zero, ← Category.assoc,
    ← mayerVietorisSumMap_eq_biprod_map_comp, intervalMVδ, ← Category.assoc,
    mayerVietorisSumMap_comp_mayerVietorisδ, zero_comp]

/-- **Exactness at `H_n(f ⁻¹ SW)`** of the interval Mayer–Vietoris sequence
`H_{n+1}(f ⁻¹ NE) ⟶ H_n(f ⁻¹ SW) ⟶ H_n(f ⁻¹ left) ⊞ H_n(f ⁻¹ right)`. -/
theorem intervalMV_exact_inter :
    (ShortComplex.mk _ _ (intervalMVδ_comp_intervalMVInterMap f Q k n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (mayerVietoris_exact_inter (Q.coverSet f Q.left) (Q.coverSet f Q.right) (ModuleCat.of k k)
      (Q.interior_coverSet_union f) n)
  exact ShortComplex.isoMk (Iso.refl _)
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).mapIso (Q.swIso f))
    (biprod.mapIso
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).mapIso (Q.leftIso f))
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).mapIso
        (Q.rightIso f)))
    (Category.id_comp _) (mayerVietorisInterMap_comp_biprod_map f Q k n).symm

/-- **Exactness at `H_n(f ⁻¹ left) ⊞ H_n(f ⁻¹ right)`** of the interval Mayer–Vietoris
sequence. -/
theorem intervalMV_exact_sum :
    (ShortComplex.mk _ _ (intervalMVInterMap_comp_intervalMVSumMap f Q k n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (mayerVietoris_exact_sum (Q.coverSet f Q.left) (Q.coverSet f Q.right) (ModuleCat.of k k)
      (Q.interior_coverSet_union f) n)
  exact ShortComplex.isoMk
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).mapIso (Q.swIso f))
    (biprod.mapIso
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).mapIso (Q.leftIso f))
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).mapIso
        (Q.rightIso f)))
    (Iso.refl _)
    (mayerVietorisInterMap_comp_biprod_map f Q k n).symm
    ((Category.comp_id _).trans (mayerVietorisSumMap_eq_biprod_map_comp f Q k n)).symm

/-- **Exactness at `H_{n+1}(f ⁻¹ NE)`** of the interval Mayer–Vietoris sequence
`H_{n+1}(f ⁻¹ left) ⊞ H_{n+1}(f ⁻¹ right) ⟶ H_{n+1}(f ⁻¹ NE) ⟶ H_n(f ⁻¹ SW)`. -/
theorem intervalMV_exact_ne :
    (ShortComplex.mk _ _ (intervalMVSumMap_comp_intervalMVδ f Q k n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (mayerVietoris_exact_space (Q.coverSet f Q.left) (Q.coverSet f Q.right) (ModuleCat.of k k)
      (Q.interior_coverSet_union f) n)
  exact ShortComplex.isoMk
    (biprod.mapIso
      (((singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj (ModuleCat.of k k)).mapIso
        (Q.leftIso f))
      (((singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj (ModuleCat.of k k)).mapIso
        (Q.rightIso f)))
    (Iso.refl _)
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).mapIso (Q.swIso f))
    ((Category.comp_id _).trans (mayerVietorisSumMap_eq_biprod_map_comp f Q k (n + 1))).symm
    (Category.id_comp _)

end Sequence

/-! ### Naturality -/

section Naturality

variable {X : Type u} [TopologicalSpace X]

/-- The identity of `X` as a map of interval preimages `f ⁻¹ I ⟶ g ⁻¹ J`, when
`f x ∈ I → g x ∈ J` for every `x`. -/
def intervalPreimageMap {f g : C(X, ℝ)} {I J : OpenInterval} (h : ∀ x, f x ∈ I → g x ∈ J) :
    (intervalPreimageTopCat f).obj I ⟶ (intervalPreimageTopCat g).obj J :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.1 x.2⟩, by fun_prop⟩

@[simp]
theorem intervalPreimageMap_apply_val {f g : C(X, ℝ)} {I J : OpenInterval}
    (h : ∀ x, f x ∈ I → g x ∈ J) (x : (intervalPreimageTopCat f).obj I) :
    (intervalPreimageMap h x).1 = x.1 :=
  rfl

/-- The maps of `intervalPreimageTopCat f` are instances of `intervalPreimageMap`. -/
theorem intervalPreimageTopCat_map_eq (f : C(X, ℝ)) {I J : OpenInterval} (i : I ⟶ J) :
    (intervalPreimageTopCat f).map i = intervalPreimageMap (fun _ hx => leOfHom i hx) :=
  rfl

/-- E2's inclusions `perturbationTopHom` are instances of `intervalPreimageMap`. -/
theorem perturbationTopHom_eq {f g : C(X, ℝ)} {ε : ℝ≥0} (h : ∀ x, |f x - g x| ≤ ε)
    (I : OpenInterval) :
    perturbationTopHom h I = intervalPreimageMap (preimage_subset_preimage_thicken h I) :=
  rfl

variable (k : Type u) [Ring k] (n : ℕ) {f g : C(X, ℝ)} {Q Q' : IntervalMVSquare}
  (hl : ∀ x, f x ∈ Q.left → g x ∈ Q'.left) (hr : ∀ x, f x ∈ Q.right → g x ∈ Q'.right)

/-- **Naturality of the connecting map** for the identity of `X` mapping the corner preimages of
`(f, Q)` into those of `(g, Q')`. -/
theorem intervalMVδ_comp_map :
    intervalMVδ f Q k n ≫ ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
        (intervalPreimageMap (IntervalMVSquare.mapsTo_sw hl hr)) =
      ((singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj (ModuleCat.of k k)).map
          (intervalPreimageMap (IntervalMVSquare.mapsTo_ne hl hr)) ≫ intervalMVδ g Q' k n := by
  have hs : Set.MapsTo (intervalPreimageMap (IntervalMVSquare.mapsTo_ne hl hr))
      (Q.coverSet f Q.left) (Q'.coverSet g Q'.left) := fun y hy => hl y.1 hy
  have ht : Set.MapsTo (intervalPreimageMap (IntervalMVSquare.mapsTo_ne hl hr))
      (Q.coverSet f Q.right) (Q'.coverSet g Q'.right) := fun y hy => hr y.1 hy
  have N := mayerVietorisδ_naturality (ModuleCat.of k k)
    (intervalPreimageMap (IntervalMVSquare.mapsTo_ne hl hr)) hs ht (Q.interior_coverSet_union f)
    (Q'.interior_coverSet_union g) n
  have e : (Q.swIso f).hom ≫ intervalPreimageMap (IntervalMVSquare.mapsTo_sw hl hr) =
      subsetRestrict _ (hs.inter_inter ht) ≫ (Q'.swIso g).hom :=
    rfl
  rw [intervalMVδ, intervalMVδ, Category.assoc, ← Functor.map_comp, e, Functor.map_comp,
    ← Category.assoc, N, Category.assoc]

/-- **Naturality of `(inc, -inc)`** for the identity of `X` mapping the corner preimages of
`(f, Q)` into those of `(g, Q')`. -/
theorem intervalMVInterMap_comp_map :
    intervalMVInterMap f Q k n ≫
        biprod.map (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
          (intervalPreimageMap hl))
          (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
            (intervalPreimageMap hr)) =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
        (intervalPreimageMap (IntervalMVSquare.mapsTo_sw hl hr)) ≫
        intervalMVInterMap g Q' k n := by
  apply biprod.hom_ext
  · simp only [intervalMVInterMap, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
      biprod.lift_fst, ← Functor.map_comp]
    rfl
  · simp only [intervalMVInterMap, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg, ← Functor.map_comp]
    rfl

/-- **Naturality of the sum map** for the identity of `X` mapping the corner preimages of
`(f, Q)` into those of `(g, Q')`. -/
theorem intervalMVSumMap_comp_map :
    intervalMVSumMap f Q k n ≫
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
          (intervalPreimageMap (IntervalMVSquare.mapsTo_ne hl hr)) =
      biprod.map (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
        (intervalPreimageMap hl))
          (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
            (intervalPreimageMap hr)) ≫ intervalMVSumMap g Q' k n := by
  apply biprod.hom_ext'
  · simp only [intervalMVSumMap, biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc,
      ← Functor.map_comp]
    rfl
  · simp only [intervalMVSumMap, biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc,
      ← Functor.map_comp]
    rfl

end Naturality

/-! ### Naturality in `(a, b)` -/

section Squares

variable {X : Type u} [TopologicalSpace X] (k : Type u) [Ring k] (n : ℕ) (f : C(X, ℝ))
  {Q Q' : IntervalMVSquare}

/-- **Naturality of the connecting map in the square** (G1): for a morphism of squares, for
instance independent increases of the endpoints (`IntervalMVSquare.hom_ofEndpoints`), the
connecting maps commute with the maps of `intervalSingularHomology`. -/
theorem intervalMVδ_naturality (h : IntervalMVSquare.Hom Q Q') :
    intervalMVδ f Q k n ≫ (intervalSingularHomology k n f).map (homOfLE h.sw) =
      (intervalSingularHomology k (n + 1) f).map (homOfLE h.ne) ≫ intervalMVδ f Q' k n :=
  intervalMVδ_comp_map k n (fun _ hx => h.left hx) (fun _ hx => h.right hx)

/-- Naturality of `(inc, -inc)` in the square. -/
theorem intervalMVInterMap_naturality (h : IntervalMVSquare.Hom Q Q') :
    intervalMVInterMap f Q k n ≫
        biprod.map ((intervalSingularHomology k n f).map (homOfLE h.left))
          ((intervalSingularHomology k n f).map (homOfLE h.right)) =
      (intervalSingularHomology k n f).map (homOfLE h.sw) ≫ intervalMVInterMap f Q' k n :=
  intervalMVInterMap_comp_map k n (fun _ hx => h.left hx) (fun _ hx => h.right hx)

/-- Naturality of the sum map in the square. -/
theorem intervalMVSumMap_naturality (h : IntervalMVSquare.Hom Q Q') :
    intervalMVSumMap f Q k n ≫ (intervalSingularHomology k n f).map (homOfLE h.ne) =
      biprod.map ((intervalSingularHomology k n f).map (homOfLE h.left))
          ((intervalSingularHomology k n f).map (homOfLE h.right)) ≫
        intervalMVSumMap f Q' k n :=
  intervalMVSumMap_comp_map k n (fun _ hx => h.left hx) (fun _ hx => h.right hx)

end Squares

/-! ### Compatibility with the thickening witness -/

section Thickening

variable {X : Type u} [TopologicalSpace X] (k : Type u) [Ring k] (n : ℕ) {f g : C(X, ℝ)}
  {ε : ℝ≥0} (h : ∀ x, |f x - g x| ≤ ε) (a b a' b' : ℝ) (hab : 0 < a + b) (ha : a ≤ a')
  (hb : b ≤ b')

/-- **The connecting map commutes with the thickening witness** (G2): the components of
`intervalSingularHomologyPerturbation` at the corners of the endpoint square map the sequence of
`f` to the sequence of `g` on the thickened square. -/
theorem intervalMVδ_comp_perturbation_app :
    intervalMVδ f (IntervalMVSquare.ofEndpoints a b a' b' hab ha hb) k n ≫
        (intervalSingularHomologyPerturbation k n h).app (intervalAB a b) =
      (intervalSingularHomologyPerturbation k (n + 1) h).app (intervalAB a' b') ≫
        intervalMVδ g (IntervalMVSquare.thickenEndpoints a b a' b' hab ha hb ε) k n := by
  rw [intervalSingularHomologyPerturbation_app, intervalSingularHomologyPerturbation_app,
    perturbationTopHom_eq, perturbationTopHom_eq]
  exact intervalMVδ_comp_map k n (f := f) (g := g)
    (Q := IntervalMVSquare.ofEndpoints a b a' b' hab ha hb)
    (Q' := IntervalMVSquare.thickenEndpoints a b a' b' hab ha hb ε)
    (fun x hx => preimage_subset_preimage_thicken h (intervalAB a' b) hx)
    (fun x hx => preimage_subset_preimage_thicken h (intervalAB a b') hx)

/-- `(inc, -inc)` commutes with the thickening witness. -/
theorem intervalMVInterMap_comp_perturbation_app :
    intervalMVInterMap f (IntervalMVSquare.ofEndpoints a b a' b' hab ha hb) k n ≫
        biprod.map ((intervalSingularHomologyPerturbation k n h).app (intervalAB a' b))
          ((intervalSingularHomologyPerturbation k n h).app (intervalAB a b')) =
      (intervalSingularHomologyPerturbation k n h).app (intervalAB a b) ≫
        intervalMVInterMap g (IntervalMVSquare.thickenEndpoints a b a' b' hab ha hb ε) k n := by
  simp only [intervalSingularHomologyPerturbation_app, perturbationTopHom_eq]
  exact intervalMVInterMap_comp_map k n (f := f) (g := g)
    (Q := IntervalMVSquare.ofEndpoints a b a' b' hab ha hb)
    (Q' := IntervalMVSquare.thickenEndpoints a b a' b' hab ha hb ε)
    (fun x hx => preimage_subset_preimage_thicken h (intervalAB a' b) hx)
    (fun x hx => preimage_subset_preimage_thicken h (intervalAB a b') hx)

/-- The sum map commutes with the thickening witness. -/
theorem intervalMVSumMap_comp_perturbation_app :
    intervalMVSumMap f (IntervalMVSquare.ofEndpoints a b a' b' hab ha hb) k n ≫
        (intervalSingularHomologyPerturbation k n h).app (intervalAB a' b') =
      biprod.map ((intervalSingularHomologyPerturbation k n h).app (intervalAB a' b))
          ((intervalSingularHomologyPerturbation k n h).app (intervalAB a b')) ≫
        intervalMVSumMap g (IntervalMVSquare.thickenEndpoints a b a' b' hab ha hb ε) k n := by
  simp only [intervalSingularHomologyPerturbation_app, perturbationTopHom_eq]
  exact intervalMVSumMap_comp_map k n (f := f) (g := g)
    (Q := IntervalMVSquare.ofEndpoints a b a' b' hab ha hb)
    (Q' := IntervalMVSquare.thickenEndpoints a b a' b' hab ha hb ε)
    (fun x hx => preimage_subset_preimage_thicken h (intervalAB a' b) hx)
    (fun x hx => preimage_subset_preimage_thicken h (intervalAB a b') hx)

/-- The connecting map commutes with the witness `φ` of `intervalSingularHomologyInterleaving`. -/
theorem intervalMVδ_comp_interleaving_φ :
    intervalMVδ f (IntervalMVSquare.ofEndpoints a b a' b' hab ha hb) k n ≫
        (intervalSingularHomologyInterleaving (k := k) (n := n) h).φ.app (intervalAB a b) =
      (intervalSingularHomologyInterleaving (k := k) (n := n + 1) h).φ.app (intervalAB a' b') ≫
        intervalMVδ g (IntervalMVSquare.thickenEndpoints a b a' b' hab ha hb ε) k n :=
  intervalMVδ_comp_perturbation_app k n h a b a' b' hab ha hb

/-- The connecting map commutes with the witness `ψ` of `intervalSingularHomologyInterleaving`,
in the direction from `g` to `f`. -/
theorem intervalMVδ_comp_interleaving_ψ :
    intervalMVδ g (IntervalMVSquare.ofEndpoints a b a' b' hab ha hb) k n ≫
        (intervalSingularHomologyInterleaving (k := k) (n := n) h).ψ.app (intervalAB a b) =
      (intervalSingularHomologyInterleaving (k := k) (n := n + 1) h).ψ.app (intervalAB a' b') ≫
        intervalMVδ f (IntervalMVSquare.thickenEndpoints a b a' b' hab ha hb ε) k n :=
  intervalMVδ_comp_perturbation_app k n (perturbationBound_symm h) a b a' b' hab ha hb

end Thickening

end TDA.Reeb
