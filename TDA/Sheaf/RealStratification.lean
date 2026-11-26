import TDA.Sheaf.AlternatingDiagram
import TDA.Sheaf.RealLine
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Stratifications of the real line by finitely many points

Fix breakpoints `p : Fin m → ℝ`, strictly increasing, with set `breakpoints p`. They cut the
real line into `2m + 1` strata, numbered by the vertices of `Vertex (orient m)`: the even
vertex `2j` is the open cell `(p_{j-1}, p_j)` (with `p_{-1} = -∞` and `p_m = +∞`), the odd
vertex `2i+1` is the point `p_i`.

* `orient m` orients the path on these vertices so that every arrow goes from a point to an
  adjacent cell (`arrow_orient_iff`). No two arrows compose, so the free category
  `Paths (Vertex (orient m))` is thin (`paths_hom_subsingleton`): it is the poset of strata
  ordered by specialisation.
* For a finite set `S ⊆ ℝ`, `IsBasicOpen S U` says that `U` is a nonempty order-connected open
  set meeting `S` in at most one point. These opens form a basis (`isBasis_basicOpen`) that is
  closed under nonempty intersections (`IsBasicOpen.inf`). `BasicCat S` is the full
  subcategory of `Opens realLine` on them, and `basicTopology S` is the Grothendieck topology
  that the inclusion `basicIncl S` induces from the topology of `realLine`.
* `star p v` is the cell `2j` itself, or the open star `(p_{i-1}, p_{i+1})` of the point
  `2i+1`; every star is basic (`isBasicOpen_star`). `tau p U` is the stratum of a basic open
  `U`: the point it contains, if any, and otherwise the cell containing it. It is
  characterised by `tau_eq_iff`. The laws collected in `exists_star_tau` make
  `tauFunctor hp : (BasicCat (breakpoints p))ᵒᵖ ⥤ Paths (Vertex (orient m))` a functor, which
  sends an inclusion with the same breakpoints to an isomorphism (`isIso_tauFunctor_map`).
* `isSheaf_basic_of_isIso_sameStratum`: a presheaf on `BasicCat S`, valued in any category,
  that inverts every inclusion `U ⊆ V` with `U ∩ S = V ∩ S`, is a sheaf for
  `basicTopology S`. In particular `tauFunctor hp ⋙ M` is a sheaf for every diagram `M`
  (`isSheaf_tauFunctor_comp`).
* `basisEquiv S k` is Mathlib's comparison lemma
  `Functor.sheafInducedTopologyEquivOfIsCoverDense` for this basis, between sheaves on
  `BasicCat S` and sheaves of `k`-modules on the real line.

`basisEquiv` fixes the coefficient ring `k : Type`, matching the universe of
`realLine : TopCat.{0}`, so that `ModuleCat.{0} k` has the limits and colimits that sections
and stalks on the real line use.
-/

open CategoryTheory TopologicalSpace Opposite TDA.Sheaf.AlternatingDiagram

namespace TDA.Sheaf.RealStratification

/-! ### The orientation and thinness of its path category -/

/-- The orientation for `m` breakpoints: arrow `a` points from `a + 1` to `a` when `a` is even
and from `a` to `a + 1` when `a` is odd, so every arrow leaves an odd vertex. -/
def orient (m : ℕ) : Fin (2 * m) → Bool := fun a => a.val % 2 == 1

private theorem src_orient_val {m : ℕ} (a : Fin (2 * m)) :
    (src (orient m) a).val = if a.val % 2 = 1 then a.val else a.val + 1 := by
  unfold src orient
  by_cases h : a.val % 2 = 1 <;> simp [h]

private theorem tgt_orient_val {m : ℕ} (a : Fin (2 * m)) :
    (tgt (orient m) a).val = if a.val % 2 = 1 then a.val + 1 else a.val := by
  unfold tgt orient
  by_cases h : a.val % 2 = 1 <;> simp [h]

/-- The arrows of `orient m`: from each odd vertex to its two neighbours. -/
theorem arrow_orient_iff {m : ℕ} {v w : Fin (2 * m + 1)} :
    Arrow (orient m) v w ↔ v.val % 2 = 1 ∧ (w.val + 1 = v.val ∨ w.val = v.val + 1) := by
  constructor
  · rintro ⟨a, rfl, rfl⟩
    rw [src_orient_val, tgt_orient_val]
    split_ifs <;> omega
  · rintro ⟨hv, hw | hw⟩
    · refine ⟨⟨w.val, by omega⟩, Fin.ext ?_, Fin.ext ?_⟩ <;>
        simp only [src_orient_val, tgt_orient_val] <;>
        split_ifs <;> omega
    · refine ⟨⟨v.val, by omega⟩, Fin.ext ?_, Fin.ext ?_⟩ <;>
        simp only [src_orient_val, tgt_orient_val] <;>
        split_ifs <;> omega

private theorem arrow_parity {m : ℕ} {v w : Fin (2 * m + 1)} (h : Arrow (orient m) v w) :
    v.val % 2 = 1 ∧ w.val % 2 = 0 := by
  rw [arrow_orient_iff] at h
  omega

private theorem not_composable {m : ℕ} {i j l : Fin (2 * m + 1)} (h : Arrow (orient m) i j)
    (h' : Arrow (orient m) j l) : False := by
  have := arrow_parity h
  have := arrow_parity h'
  omega

/-- Thinness: parallel morphisms of the free category on `orient m` are equal. -/
instance paths_hom_subsingleton {m : ℕ} (i j : Paths (Vertex (orient m))) :
    Subsingleton (i ⟶ j) := by
  constructor
  intro f g
  change Quiver.Path (V := Vertex (orient m)) i j at f g
  cases f with
  | nil =>
    cases g with
    | nil => rfl
    | cons g' e' =>
      cases g' with
      | nil => exact (Arrow.ne e'.down rfl).elim
      | cons g'' e'' => exact (not_composable e''.down e'.down).elim
  | cons f' e =>
    cases f' with
    | nil =>
      cases g with
      | nil => exact (Arrow.ne e.down rfl).elim
      | cons g' e' =>
        cases g' with
        | nil =>
          obtain ⟨_⟩ := e
          obtain ⟨_⟩ := e'
          rfl
        | cons g'' e'' => exact (not_composable e''.down e'.down).elim
    | cons f'' e₀ => exact (not_composable e₀.down e.down).elim

/-! ### The basis of convex opens with at most one breakpoint -/

/-- Basic opens: nonempty order-connected opens meeting `S` in at most one point. -/
def IsBasicOpen (S : Finset ℝ) (U : Opens realLine) : Prop :=
  (U : Set ℝ).Nonempty ∧ (U : Set ℝ).OrdConnected ∧ ((U : Set ℝ) ∩ S).Subsingleton

/-- The basic opens form a basis of the real line. -/
theorem isBasis_basicOpen (S : Finset ℝ) : Opens.IsBasis {U | IsBasicOpen S U} := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  have hcl : IsClosed ((S : Set ℝ) \ {x}) :=
    (S.finite_toSet.subset Set.sdiff_subset).isClosed
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl x (fun h => h.2 rfl)
  have hr : 0 < min ε δ := lt_min hε hδ
  have key : ∀ y ∈ Metric.ball x (min ε δ) ∩ (S : Set ℝ), y = x := by
    rintro y ⟨hy, hyS⟩
    by_contra hne
    exact hδb (Metric.ball_subset_ball (min_le_right _ _) hy) ⟨hyS, hne⟩
  refine ⟨⟨Metric.ball x (min ε δ), Metric.isOpen_ball⟩,
    ⟨⟨x, Metric.mem_ball_self hr⟩, ?_, ?_⟩, Metric.mem_ball_self hr, ?_⟩
  · show (Metric.ball x (min ε δ)).OrdConnected
    rw [Real.ball_eq_Ioo]
    exact Set.ordConnected_Ioo
  · intro y hy z hz
    exact (key y hy).trans (key z hz).symm
  · intro y hy
    exact hball (Metric.ball_subset_ball (min_le_left _ _) hy)

/-- The basis in the `Set.range` form used by `TopCat.Opens.coverDense_inducedFunctor`. -/
theorem isBasis_range_basicOpen (S : Finset ℝ) :
    Opens.IsBasis (Set.range (Subtype.val : {U // IsBasicOpen S U} → Opens realLine)) := by
  rw [Subtype.range_coe_subtype]
  exact isBasis_basicOpen S

/-- A nonempty intersection of two basic opens is basic. -/
theorem IsBasicOpen.inf {S : Finset ℝ} {U V : Opens realLine} (hU : IsBasicOpen S U)
    (hV : IsBasicOpen S V) (hne : ((U ⊓ V : Opens realLine) : Set ℝ).Nonempty) :
    IsBasicOpen S (U ⊓ V) := by
  refine ⟨hne, ?_, ?_⟩
  · rw [Opens.coe_inf]
    exact hU.2.1.inter hV.2.1
  · rw [Opens.coe_inf]
    exact hU.2.2.anti (Set.inter_subset_inter_left _ Set.inter_subset_left)

/-- The basic opens, as a type. -/
abbrev Basic (S : Finset ℝ) := {U : Opens realLine // IsBasicOpen S U}

/-- The full subcategory of `Opens realLine` on the basic opens. -/
abbrev BasicCat (S : Finset ℝ) :=
  InducedCategory (Opens realLine) (Subtype.val : Basic S → Opens realLine)

/-- The inclusion of the basic opens into all opens. -/
abbrev basicIncl (S : Finset ℝ) : BasicCat S ⥤ Opens realLine := inducedFunctor _

instance basicIncl_isCoverDense (S : Finset ℝ) :
    (basicIncl S).IsCoverDense (Opens.grothendieckTopology realLine) :=
  TopCat.Opens.coverDense_inducedFunctor (isBasis_range_basicOpen S)

/-- The Grothendieck topology on the basic opens induced from the real line. -/
abbrev basicTopology (S : Finset ℝ) : GrothendieckTopology (BasicCat S) :=
  (basicIncl S).inducedTopology (Opens.grothendieckTopology realLine)

/-- Morphisms between basic opens are inclusions, so there is at most one. -/
instance basicCat_hom_subsingleton {S : Finset ℝ} (U V : BasicCat S) :
    Subsingleton (U ⟶ V) :=
  ⟨fun _ _ => InducedCategory.hom_ext (Subsingleton.elim _ _)⟩

/-! ### Stars and strata of basic opens -/

variable {m : ℕ}

/-- The set of breakpoints. -/
noncomputable def breakpoints (p : Fin m → ℝ) : Finset ℝ := Finset.univ.image p

theorem apply_mem_breakpoints (p : Fin m → ℝ) (i : Fin m) : p i ∈ breakpoints p :=
  Finset.mem_image_of_mem p (Finset.mem_univ i)

theorem mem_breakpoints {p : Fin m → ℝ} {x : ℝ} : x ∈ breakpoints p ↔ ∃ i, p i = x := by
  simp [breakpoints]

/-- The star of the vertex `v`: the points lying strictly above every breakpoint below `v`
and strictly below every breakpoint above `v`. For a cell this is the cell itself; for the
point `p_i` it is `(p_{i-1}, p_{i+1})`. -/
def star (p : Fin m → ℝ) (v : Fin (2 * m + 1)) : Opens realLine where
  carrier := {x | ∀ i : Fin m,
    (2 * i.val + 1 < v.val → p i < x) ∧ (v.val < 2 * i.val + 1 → x < p i)}
  is_open' := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    change ∀ᶠ y in nhds x, ∀ i : Fin m,
      (2 * i.val + 1 < v.val → p i < y) ∧ (v.val < 2 * i.val + 1 → y < p i)
    rw [Filter.eventually_all]
    intro i
    refine Filter.Eventually.and ?_ ?_
    · by_cases h : 2 * i.val + 1 < v.val
      · exact (lt_mem_nhds ((hx i).1 h)).mono fun y hy _ => hy
      · exact Filter.Eventually.of_forall fun y h' => (h h').elim
    · by_cases h : v.val < 2 * i.val + 1
      · exact (gt_mem_nhds ((hx i).2 h)).mono fun y hy _ => hy
      · exact Filter.Eventually.of_forall fun y h' => (h h').elim

theorem mem_star {p : Fin m → ℝ} {v : Fin (2 * m + 1)} {x : ℝ} :
    x ∈ star p v ↔ ∀ i : Fin m,
      (2 * i.val + 1 < v.val → p i < x) ∧ (v.val < 2 * i.val + 1 → x < p i) :=
  Iff.rfl

/-- The star of `v` contains the breakpoint `p_j` exactly when `v` is the vertex `2j+1`. -/
theorem apply_mem_star_iff {p : Fin m → ℝ} (hp : StrictMono p) {v : Fin (2 * m + 1)}
    (j : Fin m) : p j ∈ star p v ↔ v.val = 2 * j.val + 1 := by
  rw [mem_star]
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · exact lt_irrefl _ ((h j).2 h1)
    · exact lt_irrefl _ ((h j).1 h1)
  · intro hv i
    constructor
    · intro h
      exact hp (Fin.lt_def.2 (by omega))
    · intro h
      exact hp (Fin.lt_def.2 (by omega))

/-- The breakpoint `p_i` lies in the star of its vertex `2i+1`. -/
theorem apply_mem_star {p : Fin m → ℝ} (hp : StrictMono p) (i : Fin m) :
    p i ∈ star p ⟨2 * i.val + 1, by omega⟩ :=
  (apply_mem_star_iff hp i).2 rfl

private theorem exists_between_finset (A B : Finset ℝ) (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    ∃ x, (∀ a ∈ A, a < x) ∧ ∀ b ∈ B, x < b := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rcases B.eq_empty_or_nonempty with rfl | hB
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨B.min' hB - 1, by simp, fun b hb => by linarith [B.min'_le b hb]⟩
  · rcases B.eq_empty_or_nonempty with rfl | hB
    · exact ⟨A.max' hA + 1, fun a ha => by linarith [A.le_max' a ha], by simp⟩
    · obtain ⟨x, h1, h2⟩ := exists_between (h _ (A.max'_mem hA) _ (B.min'_mem hB))
      exact ⟨x, fun a ha => (A.le_max' a ha).trans_lt h1,
        fun b hb => h2.trans_le (B.min'_le b hb)⟩

/-- Every star is a basic open. -/
theorem isBasicOpen_star {p : Fin m → ℝ} (hp : StrictMono p) (v : Fin (2 * m + 1)) :
    IsBasicOpen (breakpoints p) (star p v) := by
  refine ⟨?_, ⟨fun x hx y hy z hz i => ⟨fun h => ((hx i).1 h).trans_le hz.1,
    fun h => hz.2.trans_lt ((hy i).2 h)⟩⟩, ?_⟩
  · obtain ⟨x, hA, hB⟩ := exists_between_finset
      ((Finset.univ.filter fun i : Fin m => 2 * i.val + 1 < v.val).image p)
      ((Finset.univ.filter fun i : Fin m => v.val < 2 * i.val + 1).image p) (by
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact hp (Fin.lt_def.2 (by omega)))
    refine ⟨x, fun i => ⟨fun h => hA _ ?_, fun h => hB _ ?_⟩⟩ <;>
      exact Finset.mem_image_of_mem p (by simpa using h)
  · rintro a ⟨ha, haS⟩ b ⟨hb, hbS⟩
    obtain ⟨i, rfl⟩ := mem_breakpoints.1 haS
    obtain ⟨j, rfl⟩ := mem_breakpoints.1 hbS
    have hi := (apply_mem_star_iff hp i).1 ha
    have hj := (apply_mem_star_iff hp j).1 hb
    rw [show i = j from Fin.ext (by omega)]

/-- The star of a point contains the stars of its two adjacent cells. -/
theorem star_le_star_of_arrow (p : Fin m → ℝ) {v w : Fin (2 * m + 1)}
    (h : Arrow (orient m) v w) : star p w ≤ star p v := by
  rw [arrow_orient_iff] at h
  intro x hx i
  have := hx i
  exact ⟨fun h' => this.1 (by omega), fun h' => this.2 (by omega)⟩

private theorem star_sep {p : Fin m → ℝ} {v w : Fin (2 * m + 1)} {x : ℝ} (hv : x ∈ star p v)
    (hw : x ∈ star p w) (i : Fin m) (h1 : v.val < 2 * i.val + 1) (h2 : 2 * i.val + 1 < w.val) :
    False :=
  lt_asymm ((hv i).2 h1) ((hw i).1 h2)

private theorem inter_breakpoints_eq_iff {p : Fin m → ℝ} {A B : Set ℝ} :
    A ∩ ↑(breakpoints p) = B ∩ ↑(breakpoints p) ↔ ∀ i, p i ∈ A ↔ p i ∈ B := by
  constructor
  · intro h i
    have := Set.ext_iff.1 h (p i)
    simpa [apply_mem_breakpoints] using this
  · intro h
    ext y
    simp only [Set.mem_inter_iff, Finset.mem_coe, mem_breakpoints]
    constructor
    · rintro ⟨hy, i, rfl⟩
      exact ⟨(h i).1 hy, i, rfl⟩
    · rintro ⟨hy, i, rfl⟩
      exact ⟨(h i).2 hy, i, rfl⟩

private theorem eq_of_apply_mem {p : Fin m → ℝ} (hp : StrictMono p) {U : Opens realLine}
    (hU : IsBasicOpen (breakpoints p) U) {i j : Fin m} (hi : p i ∈ U) (hj : p j ∈ U) :
    i = j :=
  hp.injective (hU.2.2 ⟨hi, apply_mem_breakpoints p i⟩ ⟨hj, apply_mem_breakpoints p j⟩)

/-- A vertex whose star meets the breakpoints like a breakpoint-free set is a cell. -/
private theorem even_of_forall_not_mem {p : Fin m → ℝ} (hp : StrictMono p) {A : Set ℝ}
    {v : Fin (2 * m + 1)} (hA : ∀ i, p i ∉ A) (hv : ∀ i, p i ∈ star p v ↔ p i ∈ A) :
    v.val % 2 = 0 := by
  by_contra h
  exact hA ⟨v.val / 2, by omega⟩ ((hv _).1 ((apply_mem_star_iff hp _).2 (by simp; omega)))

private theorem exists_stratum {p : Fin m → ℝ} (hp : StrictMono p) {U : Opens realLine}
    (hU : IsBasicOpen (breakpoints p) U) :
    ∃ v, U ≤ star p v ∧
      (star p v : Set ℝ) ∩ breakpoints p = (U : Set ℝ) ∩ breakpoints p := by
  by_cases hs : ∃ j, p j ∈ U
  · obtain ⟨j, hj⟩ := hs
    refine ⟨⟨2 * j.val + 1, by omega⟩, ?_, inter_breakpoints_eq_iff.2 fun i => ?_⟩
    · intro x hx i
      constructor
      · intro h
        have hij : p i < p j := hp (Fin.lt_def.2 (by simp at h; omega))
        by_contra hle
        have : p i ∈ U := hU.2.1.out hx hj ⟨le_of_not_gt hle, hij.le⟩
        exact (Fin.lt_def.1 (hp.lt_iff_lt.1 hij)).ne (by rw [eq_of_apply_mem hp hU this hj])
      · intro h
        have hij : p j < p i := hp (Fin.lt_def.2 (by simp at h; omega))
        by_contra hle
        have : p i ∈ U := hU.2.1.out hj hx ⟨hij.le, le_of_not_gt hle⟩
        exact (Fin.lt_def.1 (hp.lt_iff_lt.1 hij)).ne (by rw [eq_of_apply_mem hp hU this hj])
    · rw [SetLike.mem_coe, SetLike.mem_coe, apply_mem_star_iff hp]
      constructor
      · intro h
        rw [show i = j from Fin.ext (by simp at h; omega)]
        exact hj
      · intro hi
        rw [eq_of_apply_mem hp hU hi hj]
  · push Not at hs
    obtain ⟨x₀, hx₀⟩ := hU.1
    classical
    have hex : ∃ n, ∀ i : Fin m, n ≤ i.val → x₀ < p i := ⟨m, fun i h => by omega⟩
    set j := Nat.find hex with hj
    have hjm : j ≤ m := Nat.find_min' hex fun i h => by omega
    have hup : ∀ i : Fin m, j ≤ i.val → x₀ < p i := Nat.find_spec hex
    have hlow : ∀ i : Fin m, i.val < j → p i < x₀ := by
      intro i hi
      have := Nat.find_min hex hi
      push Not at this
      obtain ⟨i', hii', hi'⟩ := this
      refine lt_of_le_of_ne ((hp.monotone (Fin.le_def.2 hii')).trans hi') ?_
      rintro rfl
      exact hs i hx₀
    refine ⟨⟨2 * j, by omega⟩, ?_, inter_breakpoints_eq_iff.2 fun i => ?_⟩
    · intro x hx i
      constructor
      · intro h
        have := hlow i (by simp at h; omega)
        by_contra hle
        exact hs i (hU.2.1.out hx hx₀ ⟨le_of_not_gt hle, this.le⟩)
      · intro h
        have := hup i (by simp at h; omega)
        by_contra hle
        exact hs i (hU.2.1.out hx₀ hx ⟨this.le, le_of_not_gt hle⟩)
    · rw [SetLike.mem_coe, SetLike.mem_coe, apply_mem_star_iff hp]
      simp only [hs i, iff_false]
      omega

private theorem stratum_unique {p : Fin m → ℝ} (hp : StrictMono p) {U : Opens realLine}
    (hne : (U : Set ℝ).Nonempty) {v w : Fin (2 * m + 1)} (hv : U ≤ star p v)
    (hv' : ∀ i, p i ∈ star p v ↔ p i ∈ U) (hw : U ≤ star p w)
    (hw' : ∀ i, p i ∈ star p w ↔ p i ∈ U) : v = w := by
  by_cases hs : ∃ j, p j ∈ U
  · obtain ⟨j, hj⟩ := hs
    have h1 := (apply_mem_star_iff hp j).1 ((hv' j).2 hj)
    have h2 := (apply_mem_star_iff hp j).1 ((hw' j).2 hj)
    exact Fin.ext (by omega)
  · push Not at hs
    have ev := even_of_forall_not_mem hp hs hv'
    have ew := even_of_forall_not_mem hp hs hw'
    obtain ⟨x, hx⟩ := hne
    rcases lt_trichotomy v.val w.val with h | h | h
    · exact (star_sep (hv hx) (hw hx) ⟨v.val / 2, by omega⟩ (by simp; omega)
        (by simp; omega)).elim
    · exact Fin.ext h
    · exact (star_sep (hw hx) (hv hx) ⟨w.val / 2, by omega⟩ (by simp; omega)
        (by simp; omega)).elim

/-- The stratum of a basic open: the vertex `v` whose star contains `U` and meets the
breakpoints exactly as `U` does. This is the breakpoint in `U` if there is one, and otherwise
the cell containing `U`; see `tau_eq_iff`. -/
noncomputable def tau (p : Fin m → ℝ) (U : Basic (breakpoints p)) : Fin (2 * m + 1) :=
  Classical.epsilon fun v => U.1 ≤ star p v ∧
    (star p v : Set ℝ) ∩ breakpoints p = (U.1 : Set ℝ) ∩ breakpoints p

private theorem tau_spec {p : Fin m → ℝ} (hp : StrictMono p) (U : Basic (breakpoints p)) :
    U.1 ≤ star p (tau p U) ∧
      (star p (tau p U) : Set ℝ) ∩ breakpoints p = (U.1 : Set ℝ) ∩ breakpoints p :=
  Classical.epsilon_spec (exists_stratum hp U.2)

/-- Every basic open lies in the star of its stratum. -/
theorem le_star_tau {p : Fin m → ℝ} (hp : StrictMono p) (U : Basic (breakpoints p)) :
    U.1 ≤ star p (tau p U) :=
  (tau_spec hp U).1

/-- The star of the stratum of `U` contains the same breakpoints as `U`. -/
theorem star_tau_inter {p : Fin m → ℝ} (hp : StrictMono p) (U : Basic (breakpoints p)) :
    (star p (tau p U) : Set ℝ) ∩ breakpoints p = (U.1 : Set ℝ) ∩ breakpoints p :=
  (tau_spec hp U).2

/-- Characterisation of the stratum of a basic open. -/
theorem tau_eq_iff {p : Fin m → ℝ} (hp : StrictMono p) (U : Basic (breakpoints p))
    (v : Fin (2 * m + 1)) :
    tau p U = v ↔ U.1 ≤ star p v ∧
      (star p v : Set ℝ) ∩ breakpoints p = (U.1 : Set ℝ) ∩ breakpoints p := by
  constructor
  · rintro rfl
    exact tau_spec hp U
  · rintro ⟨h1, h2⟩
    exact stratum_unique hp U.2.1 (le_star_tau hp U)
      (inter_breakpoints_eq_iff.1 (star_tau_inter hp U)) h1 (inter_breakpoints_eq_iff.1 h2)

/-- The stratum of a star is its vertex. -/
theorem tau_star {p : Fin m → ℝ} (hp : StrictMono p) (v : Fin (2 * m + 1))
    (h : IsBasicOpen (breakpoints p) (star p v)) : tau p ⟨star p v, h⟩ = v :=
  (tau_eq_iff hp _ v).2 ⟨le_rfl, rfl⟩

/-- An inclusion of basic opens with the same breakpoints preserves the stratum. -/
theorem tau_eq_of_le_of_inter_eq {p : Fin m → ℝ} (hp : StrictMono p)
    {U V : Basic (breakpoints p)} (hUV : U.1 ≤ V.1)
    (h : (U.1 : Set ℝ) ∩ breakpoints p = (V.1 : Set ℝ) ∩ breakpoints p) :
    tau p V = tau p U :=
  (tau_eq_iff hp U _).2 ⟨hUV.trans (le_star_tau hp V), (star_tau_inter hp V).trans h.symm⟩ |>.symm

/-- An inclusion of basic opens either preserves the stratum or goes from a cell to an
adjacent point, along an arrow of `orient m`. -/
theorem tau_eq_or_arrow {p : Fin m → ℝ} (hp : StrictMono p) (U V : Basic (breakpoints p))
    (hUV : U.1 ≤ V.1) : tau p V = tau p U ∨ Arrow (orient m) (tau p V) (tau p U) := by
  by_cases h : (U.1 : Set ℝ) ∩ breakpoints p = (V.1 : Set ℝ) ∩ breakpoints p
  · exact Or.inl (tau_eq_of_le_of_inter_eq hp hUV h)
  right
  obtain ⟨j, hjV, hjU⟩ : ∃ j, p j ∈ V.1 ∧ p j ∉ U.1 := by
    by_contra hc
    push Not at hc
    exact h (inter_breakpoints_eq_iff.2 fun i => ⟨fun hi => hUV hi, hc i⟩)
  have hV := (apply_mem_star_iff hp j).1
    ((inter_breakpoints_eq_iff.1 (star_tau_inter hp V) j).2 hjV)
  have hs : ∀ i, p i ∉ U.1 := by
    intro i hi
    rw [eq_of_apply_mem hp V.2 (hUV hi) hjV] at hi
    exact hjU hi
  have ev := even_of_forall_not_mem hp hs (inter_breakpoints_eq_iff.1 (star_tau_inter hp U))
  obtain ⟨x, hx⟩ := U.2.1
  have hxU := le_star_tau hp U hx
  have hxV := le_star_tau hp V (hUV hx)
  rw [arrow_orient_iff]
  refine ⟨by omega, ?_⟩
  by_contra hc
  rcases Nat.lt_or_gt_of_ne (show (tau p U).val ≠ 2 * j.val by omega) with h1 | h1
  · exact star_sep hxU hxV ⟨(tau p U).val / 2, by omega⟩ (by simp; omega) (by simp; omega)
  · exact star_sep hxV hxU ⟨j.val + 1, by omega⟩ (by simp; omega) (by simp; omega)

/-- The stratification combinatorics in one statement: stars `σ` and strata `τ` such that
every star is basic, every basic open lies in the star of its stratum, `τ` retracts `σ`,
inclusions move the stratum at most along one arrow, arrows give inclusions of stars, and the
star of `2i+1` contains `p_i`. -/
theorem exists_star_tau {p : Fin m → ℝ} (hp : StrictMono p) :
    ∃ (σ : Fin (2 * m + 1) → Opens realLine)
      (τ : {U // IsBasicOpen (breakpoints p) U} → Fin (2 * m + 1)),
      (∀ v, IsBasicOpen (breakpoints p) (σ v)) ∧
      (∀ U, U.1 ≤ σ (τ U)) ∧
      (∀ v (h : IsBasicOpen (breakpoints p) (σ v)), τ ⟨σ v, h⟩ = v) ∧
      (∀ U V, U.1 ≤ V.1 → τ V = τ U ∨ Arrow (orient m) (τ V) (τ U)) ∧
      (∀ {v w : Fin (2 * m + 1)}, Arrow (orient m) v w → σ w ≤ σ v) ∧
      (∀ i : Fin m, p i ∈ σ ⟨2 * i.val + 1, by omega⟩) :=
  ⟨star p, tau p, isBasicOpen_star hp, le_star_tau hp, tau_star hp, tau_eq_or_arrow hp,
    star_le_star_of_arrow p, apply_mem_star hp⟩

/-- The stratum assignment as a functor from basic opens to the strata poset: an inclusion
`U ⊆ V` goes to the identity or to the arrow from the stratum of `V` to that of `U`. -/
noncomputable def tauFunctor {p : Fin m → ℝ} (hp : StrictMono p) :
    (BasicCat (breakpoints p))ᵒᵖ ⥤ Paths (Vertex (orient m)) where
  obj U := vtx (orient m) (tau p U.unop)
  map {U V} f :=
    if h : tau p U.unop = tau p V.unop then eqToHom (congrArg (vtx (orient m)) h)
    else gen ((tau_eq_or_arrow hp V.unop U.unop f.unop.hom.le).resolve_left h)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem tauFunctor_obj {p : Fin m → ℝ} (hp : StrictMono p) (U : BasicCat (breakpoints p)) :
    (tauFunctor hp).obj (op U) = vtx (orient m) (tau p U) :=
  rfl

/-- An inclusion with the same breakpoints goes to an isomorphism. -/
theorem isIso_tauFunctor_map {p : Fin m → ℝ} (hp : StrictMono p)
    {U V : BasicCat (breakpoints p)} (f : U ⟶ V)
    (h : (U.1 : Set ℝ) ∩ breakpoints p = (V.1 : Set ℝ) ∩ breakpoints p) :
    IsIso ((tauFunctor hp).map f.op) := by
  have e : (tauFunctor hp).obj (op V) = (tauFunctor hp).obj (op U) := by
    rw [tauFunctor_obj, tauFunctor_obj, tau_eq_of_le_of_inter_eq hp f.hom.le h]
  rw [Subsingleton.elim ((tauFunctor hp).map f.op) (eqToHom e)]
  infer_instance

/-! ### The sheaf condition on the basis -/

section SheafCondition

variable {S : Finset ℝ}

private theorem isSheaf_types {F : (BasicCat S)ᵒᵖ ⥤ Type*}
    (hF : ∀ ⦃U V : BasicCat S⦄ (f : U ⟶ V),
      (U.1 : Set ℝ) ∩ S = (V.1 : Set ℝ) ∩ S → Function.Bijective (F.map f.op)) :
    Presieve.IsSheaf (basicTopology S) F := by
  intro U R hR
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hR
  have cover : ∀ x ∈ (U.1 : Set ℝ), ∃ (V : BasicCat S) (g : V ⟶ U), R g ∧ x ∈ V.1 := by
    intro x hx
    obtain ⟨W, f, ⟨Z, g, h, hg, -⟩, hxW⟩ := hR x hx
    exact ⟨Z, g, hg, h.le hxW⟩
  intro fam hfam
  -- A member of the cover with the same breakpoints as `U`.
  obtain ⟨V₀, g₀, hg₀, hgood⟩ : ∃ (V₀ : BasicCat S) (g₀ : V₀ ⟶ U), R g₀ ∧
      (V₀.1 : Set ℝ) ∩ S = (U.1 : Set ℝ) ∩ S := by
    by_cases hs : ((U.1 : Set ℝ) ∩ S).Nonempty
    · obtain ⟨s, hsU, hsS⟩ := hs
      obtain ⟨V₀, g₀, hg₀, hsV⟩ := cover s hsU
      refine ⟨V₀, g₀, hg₀, Set.Subset.antisymm
        (Set.inter_subset_inter_left _ fun y hy => g₀.hom.le hy) ?_⟩
      rintro y ⟨hyU, hyS⟩
      obtain rfl : y = s := U.2.2.2 ⟨hyU, hyS⟩ ⟨hsU, hsS⟩
      exact ⟨hsV, hsS⟩
    · obtain ⟨x₀, hx₀⟩ := U.2.1
      obtain ⟨V₀, g₀, hg₀, -⟩ := cover x₀ hx₀
      refine ⟨V₀, g₀, hg₀, ?_⟩
      rw [Set.not_nonempty_iff_eq_empty] at hs
      rw [hs]
      exact Set.subset_eq_empty (Set.inter_subset_inter_left _ fun y hy => g₀.hom.le hy) hs
  let e := Equiv.ofBijective _ (hF g₀ hgood)
  let t := e.symm (fam g₀ hg₀)
  have ht : F.map g₀.op t = fam g₀ hg₀ := e.apply_symm_apply _
  refine ⟨t, ?_, fun t' ht' => (hF g₀ hgood).1 ((ht' g₀ hg₀).trans ht.symm)⟩
  -- Agreement propagates across a nonempty intersection that keeps the breakpoints.
  have prop : ∀ (V₁ V₂ : BasicCat S) (g₁ : V₁ ⟶ U) (g₂ : V₂ ⟶ U) (hg₁ : R g₁) (hg₂ : R g₂),
      F.map g₁.op t = fam g₁ hg₁ → ((V₁.1 ⊓ V₂.1 : Opens realLine) : Set ℝ).Nonempty →
      (V₂.1 : Set ℝ) ∩ S ⊆ V₁.1 → F.map g₂.op t = fam g₂ hg₂ := by
    intro V₁ V₂ g₁ g₂ hg₁ hg₂ h₁ hne hsub
    let W : BasicCat S := ⟨V₁.1 ⊓ V₂.1, V₁.2.inf V₂.2 hne⟩
    let i₁ : W ⟶ V₁ := InducedCategory.homMk (homOfLE inf_le_left)
    let i₂ : W ⟶ V₂ := InducedCategory.homMk (homOfLE inf_le_right)
    have hW : (W.1 : Set ℝ) ∩ S = (V₂.1 : Set ℝ) ∩ S := by
      refine Set.Subset.antisymm (Set.inter_subset_inter_left _ fun y hy => hy.2) ?_
      rintro y ⟨hy, hyS⟩
      exact ⟨⟨hsub ⟨hy, hyS⟩, hy⟩, hyS⟩
    apply (hF i₂ hW).1
    calc F.map i₂.op (F.map g₂.op t) = F.map i₁.op (F.map g₁.op t) := by
          rw [← types_comp_apply (F.map g₂.op), ← types_comp_apply (F.map g₁.op),
            ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
            Subsingleton.elim (i₂ ≫ g₂) (i₁ ≫ g₁)]
      _ = F.map i₁.op (fam g₁ hg₁) := by rw [h₁]
      _ = F.map i₂.op (fam g₂ hg₂) := hfam i₁ i₂ hg₁ hg₂ (Subsingleton.elim _ _)
  have hV₀S : ∀ (V : BasicCat S) (g : V ⟶ U), (V.1 : Set ℝ) ∩ S ⊆ V₀.1 := by
    rintro V g y ⟨hy, hyS⟩
    have : y ∈ (V₀.1 : Set ℝ) ∩ S := hgood ▸ ⟨g.hom.le hy, hyS⟩
    exact this.1
  -- A member that disagrees contains no breakpoint.
  have bad : ∀ (V : BasicCat S) (g : V ⟶ U) (hg : R g), F.map g.op t ≠ fam g hg →
      (V.1 : Set ℝ) ∩ S = ∅ := by
    intro V g hg hne
    by_contra hc
    obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.2 hc
    exact hne (prop V₀ V g₀ g hg₀ hg ht ⟨s, hV₀S V g hs, hs.1⟩ (hV₀S V g))
  intro V g hg
  by_contra hne
  let Good : Set ℝ := {y | ∃ (V' : BasicCat S) (g' : V' ⟶ U) (hg' : R g'),
    y ∈ V'.1 ∧ F.map g'.op t = fam g' hg'}
  let Bad : Set ℝ := {y | ∃ (V' : BasicCat S) (g' : V' ⟶ U) (hg' : R g'),
    y ∈ V'.1 ∧ F.map g'.op t ≠ fam g' hg'}
  have hGood : IsOpen Good := isOpen_iff_forall_mem_open.2
    fun y ⟨V', g', hg', hy, h⟩ => ⟨V'.1, fun z hz => ⟨V', g', hg', hz, h⟩, V'.1.isOpen, hy⟩
  have hBad : IsOpen Bad := isOpen_iff_forall_mem_open.2
    fun y ⟨V', g', hg', hy, h⟩ => ⟨V'.1, fun z hz => ⟨V', g', hg', hz, h⟩, V'.1.isOpen, hy⟩
  have hcov : (U.1 : Set ℝ) ⊆ Good ∪ Bad := by
    intro y hy
    obtain ⟨V', g', hg', hyV'⟩ := cover y hy
    by_cases h : F.map g'.op t = fam g' hg'
    · exact Or.inl ⟨V', g', hg', hyV', h⟩
    · exact Or.inr ⟨V', g', hg', hyV', h⟩
  obtain ⟨x₀, hx₀⟩ := V₀.2.1
  obtain ⟨x₁, hx₁⟩ := V.2.1
  obtain ⟨y, -, ⟨V₁, g₁, hg₁, hy₁, h₁⟩, ⟨V₂, g₂, hg₂, hy₂, h₂⟩⟩ :=
    U.2.2.1.isPreconnected Good Bad hGood hBad hcov
      ⟨x₀, g₀.hom.le hx₀, V₀, g₀, hg₀, hx₀, ht⟩ ⟨x₁, g.hom.le hx₁, V, g, hg, hx₁, hne⟩
  exact h₂ (prop V₁ V₂ g₁ g₂ hg₁ hg₂ h₁ ⟨y, hy₁, hy₂⟩
    (by rw [bad V₂ g₂ hg₂ h₂]; exact Set.empty_subset _))

/-- The sheaf condition on the basis: a presheaf on basic opens that inverts every inclusion
`U ⊆ V` with `U ∩ S = V ∩ S` is a sheaf for the induced topology. -/
theorem isSheaf_basic_of_isIso_sameStratum {A : Type*} [Category A]
    (P : (BasicCat S)ᵒᵖ ⥤ A)
    (hP : ∀ ⦃U V : BasicCat S⦄ (f : U ⟶ V),
      (U.1 : Set ℝ) ∩ S = (V.1 : Set ℝ) ∩ S → IsIso (P.map f.op)) :
    Presheaf.IsSheaf (basicTopology S) P := by
  intro E
  refine isSheaf_types fun U V f h => ?_
  have := hP f h
  exact (isIso_iff_bijective _).1
    (inferInstance : IsIso ((coyoneda.obj (op E)).map (P.map f.op)))

end SheafCondition

/-- Every diagram on the strata, composed with the stratum functor, is a sheaf on the basic
opens. -/
theorem isSheaf_tauFunctor_comp {p : Fin m → ℝ} (hp : StrictMono p) {A : Type*} [Category A]
    (M : Paths (Vertex (orient m)) ⥤ A) :
    Presheaf.IsSheaf (basicTopology (breakpoints p)) (tauFunctor hp ⋙ M) :=
  isSheaf_basic_of_isIso_sameStratum _ fun _ _ f h => by
    have := isIso_tauFunctor_map hp f h
    exact (inferInstance : IsIso (M.map ((tauFunctor hp).map f.op)))

/-! ### Reconstruction from the basis -/

/-- Mathlib's comparison lemma for the basis of basic opens: sheaves of `k`-modules on
`BasicCat S` for the induced topology are equivalent to sheaves of `k`-modules on the real
line. Its functor is the right Kan extension along `basicIncl S`. -/
noncomputable def basisEquiv (S : Finset ℝ) (k : Type) [Ring k] :
    Sheaf (basicTopology S) (ModuleCat.{0} k) ≌
      Sheaf (Opens.grothendieckTopology realLine) (ModuleCat.{0} k) :=
  (basicIncl S).sheafInducedTopologyEquivOfIsCoverDense
    (Opens.grothendieckTopology realLine) (ModuleCat.{0} k)

/-- A sheaf extended from the basis inverts the restriction along an inclusion of basic opens
when its basis presheaf inverts that inclusion. -/
theorem isIso_map_basisEquiv (k : Type) [Ring k] {S : Finset ℝ}
    (P : Sheaf (basicTopology S) (ModuleCat.{0} k))
    {U V : BasicCat S} (f : U ⟶ V) (h : IsIso (P.obj.map f.op)) :
    IsIso (((basisEquiv S k).functor.obj P).obj.map (homOfLE f.hom.le).op) :=
  (NatIso.isIso_map_iff ((sheafToPresheaf _ _).mapIso ((basisEquiv S k).unitIso.app P)) f.op).1 h

/-- With no breakpoints, every nonempty convex open is basic. -/
theorem isBasicOpen_empty {U : Opens realLine} (hne : (U : Set ℝ).Nonempty)
    (hc : (U : Set ℝ).OrdConnected) : IsBasicOpen ∅ U :=
  ⟨hne, hc, by simp⟩

end TDA.Sheaf.RealStratification
