import TDA.Sheaf.StrictBasis
import TDA.Sheaf.SpaceTranslation
import TDA.Sheaf.AlexandrovCoordinateTranslation
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Orthant sheaves on coordinate space at the distance level

`WithOrthant n` is the type synonym of `Fin n → ℝ` whose open sets are the upper sets `S` in
which every point admits a common diagonal step down: `s - δ · 1 ∈ S` for some `δ > 0`
(`IsOrthantOpen`). `orthantSpace n` is this space in `TopCat`.

* `orthant x = {s | ∀ i, x i < s i}` is the open orthant at `x`. `exists_diagonal_step` finds
  a common finite diagonal step `δ > 0` below all coordinates of a point strictly above `x`;
  `exists_orthant_mem` covers each point of an open by the orthant at `s - δ · 1`;
  `orthant_inf`: two orthants meet in the orthant at the coordinatewise maximum;
  `isBasis_orthant` and `eq_generateFrom`: the orthants form a basis and generate the topology;
  `isOpen_ofOrthant_preimage_iff`: the open sets are exactly the upper sets of `Fin n → ℝ` that
  are open for the product topology.
* `orthantId : upperSpace (Fin n → ℝ) ⟶ orthantSpace n` is the continuous identity, and
  `orthantBasis n : StrictBasis (Fin n → ℝ) (orthantSpace n)` has basic opens `orthant`; its
  strict order is the all-strict order (`strict_orthantBasis_iff`). So
  `(orthantBasis n).Q C` is the Alexandrov sheaf pushed forward to the orthant space,
  `(orthantBasis n).B C` is `B(F)(t) = F(orthant t)`, and `TDA.Sheaf.StrictBasis` gives the
  projections, `BQ(M)(t) ≅ lim_{s, ∀ i, t i < s i} M(s)`, the unit and `QB ≅ 𝟭`.
* `orthantTranslate ε : x ↦ x - ε · 1` and `orthantTranslation : SpaceTranslation` give the
  sheaf shift, transition and addition isomorphism; `orthant t` pulls back to
  `orthant (t + ε · 1)` (`map_orthantTranslate_orthant`). Pushforward along `orthantId`
  carries the coordinate Alexandrov shift of `TDA.Sheaf.AlexandrovCoordinateTranslation` to
  them at the same radius, and `orthantShiftComparison` carries them under `B` to
  `CoordinateShift.shift`, `CoordinateShift.transition` and `CoordinateShift.compIso`.
* Witnesses at the same radius: `orthantToCoordinateInterleaving` (for `B`),
  `orthantOfSheafInterleaving` and `orthantOfCoordinateInterleaving` (for `Q`). For `ε > 0`,
  `orthantUnitInterleaving M hε` is an actual `ε`-interleaving of `M` and `BQ(M)`: forward
  `M(t ≤ t + ε · 1)` followed by the unit, reverse the projection to `M(t + ε · 1)`.
  Hence `coordinateInterleavingDistance_orthantB_orthantQ`, and the extended distances agree:
  `interleavingDistance_orthantQ` (for `Q M, Q N`) and `coordinateInterleavingDistance_orthantB`
  (for `B F, B G`).

All statements hold for every `n`; for `n = 0` the all-strict order is the full relation, which
`TDA.Sheaf.OrthantLocalization` treats as the identity case. The interleavings use
`C = ModuleCat.{0} R`.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits Opposite TopologicalSpace Topology TopCat Filter
open TDA.Persistence
open scoped NNReal ENNReal

namespace TDA.Sheaf.OrthantSheaf

open TDA.Sheaf.Alexandrov TDA.Sheaf.AlexandrovCoordinateTranslation

noncomputable section

/-! ## The orthant topology -/

/-- The type synonym of `Fin n → ℝ` that carries the orthant topology. -/
def WithOrthant (n : ℕ) : Type :=
  Fin n → ℝ

namespace WithOrthant

variable {n : ℕ}

/-- The identity from `Fin n → ℝ` to the orthant type synonym. -/
def toOrthant : (Fin n → ℝ) ≃ WithOrthant n :=
  Equiv.refl _

/-- The identity from the orthant type synonym to `Fin n → ℝ`. -/
def ofOrthant : WithOrthant n ≃ (Fin n → ℝ) :=
  Equiv.refl _

@[simp]
theorem toOrthant_ofOrthant (x : WithOrthant n) : toOrthant (ofOrthant x) = x :=
  rfl

@[simp]
theorem ofOrthant_toOrthant (x : Fin n → ℝ) : ofOrthant (toOrthant x) = x :=
  rfl

end WithOrthant

open WithOrthant

/-- A set of `Fin n → ℝ` is orthant-open when it is an upper set in which every point `s`
admits a diagonal step down: `s - δ · 1` lies in the set for some `δ > 0`. -/
def IsOrthantOpen {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  IsUpperSet S ∧ ∀ s ∈ S, ∃ δ : ℝ, 0 < δ ∧ (fun i => s i - δ) ∈ S

/-- The orthant topology. -/
instance orthantTopology (n : ℕ) : TopologicalSpace (WithOrthant n) where
  IsOpen S := IsOrthantOpen (toOrthant ⁻¹' S)
  isOpen_univ := ⟨isUpperSet_univ, fun _ _ => ⟨1, one_pos, trivial⟩⟩
  isOpen_inter S T hS hT := by
    refine ⟨hS.1.inter hT.1, fun s hs => ?_⟩
    obtain ⟨δ, hδ, hδS⟩ := hS.2 s hs.1
    obtain ⟨δ', hδ', hδT⟩ := hT.2 s hs.2
    refine ⟨min δ δ', lt_min hδ hδ', hS.1 (fun i => ?_) hδS, hT.1 (fun i => ?_) hδT⟩
    · exact sub_le_sub_left (min_le_left δ δ') (s i)
    · exact sub_le_sub_left (min_le_right δ δ') (s i)
  isOpen_sUnion F hF := by
    refine ⟨fun a b hab ha => ?_, fun s hs => ?_⟩
    · obtain ⟨S, hS, ha⟩ := ha
      exact ⟨S, hS, (hF S hS).1 hab ha⟩
    · obtain ⟨S, hS, hs⟩ := hs
      obtain ⟨δ, hδ, h⟩ := (hF S hS).2 s hs
      exact ⟨δ, hδ, S, hS, h⟩

/-- `Fin n → ℝ` with the orthant topology, as an object of `TopCat`. -/
abbrev orthantSpace (n : ℕ) : TopCat.{0} :=
  TopCat.of (WithOrthant n)

variable {n : ℕ}

/-- The open sets of the orthant space, read on `Fin n → ℝ`, are the orthant-open sets. -/
theorem isOpen_iff (S : Set (WithOrthant n)) : IsOpen S ↔ IsOrthantOpen (toOrthant ⁻¹' S) :=
  Iff.rfl

/-- An open of the orthant space, read on `Fin n → ℝ`, is an upper set. -/
theorem isUpperSet_opens (V : Opens (orthantSpace n)) :
    IsUpperSet (toOrthant ⁻¹' (V : Set (WithOrthant n))) :=
  V.isOpen.1

/-- A common finite diagonal step: for `x` strictly below `s` in every coordinate, some
`δ > 0` keeps `x` strictly below `s - δ · 1`. -/
theorem exists_diagonal_step {x s : Fin n → ℝ} (h : ∀ i, x i < s i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, x i < s i - δ := by
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioi (0 : ℝ) ∧ ∀ i, x i < s i - δ :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (Filter.eventually_all.2 fun i =>
      (gt_mem_nhds (sub_pos.2 (h i))).mono fun δ hδ => by linarith))
  obtain ⟨δ, hδ, h'⟩ := hev.exists
  exact ⟨δ, hδ, h'⟩

/-- The open sets of the orthant space are exactly the upper sets of `Fin n → ℝ` that are open
for the product topology. -/
theorem isOpen_ofOrthant_preimage_iff (S : Set (Fin n → ℝ)) :
    IsOpen (ofOrthant ⁻¹' S : Set (WithOrthant n)) ↔ IsUpperSet S ∧ IsOpen S := by
  change IsOrthantOpen S ↔ _
  constructor
  · rintro ⟨hup, hstep⟩
    refine ⟨hup, isOpen_iff_forall_mem_open.2 fun s hs => ?_⟩
    obtain ⟨δ, hδ, h⟩ := hstep s hs
    refine ⟨Set.pi Set.univ fun i => Set.Ioi (s i - δ),
      fun y hy => hup (fun i => (hy i trivial).le) h,
      isOpen_set_pi Set.finite_univ fun i _ => isOpen_Ioi, fun i _ => ?_⟩
    change s i - δ < s i
    linarith
  · rintro ⟨hup, hS⟩
    refine ⟨hup, fun s hs => ?_⟩
    have hc : Continuous fun δ : ℝ => fun i => s i - δ :=
      continuous_pi fun _ => continuous_const.sub continuous_id
    have h0 : (fun i => s i - (0 : ℝ)) = s := funext fun i => sub_zero (s i)
    have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), (fun i => s i - δ) ∈ S :=
      hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hS.mem_nhds hs)
    obtain ⟨δ, hδ, h⟩ := (eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds hev) :
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioi (0 : ℝ) ∧ (fun i => s i - δ) ∈ S).exists
    exact ⟨δ, hδ, h⟩

/-- The open orthant `{s | ∀ i, x i < s i}` at `x`. -/
def orthant (x : Fin n → ℝ) : Opens (orthantSpace n) :=
  ⟨{s | ∀ i, x i < ofOrthant s i},
    ⟨fun _ _ hab ha i => (ha i).trans_le (hab i), fun _ hs => exists_diagonal_step hs⟩⟩

@[simp]
theorem mem_orthant (x : Fin n → ℝ) (y : WithOrthant n) :
    y ∈ orthant x ↔ ∀ i, x i < ofOrthant y i :=
  Iff.rfl

/-- Orthants are antitone in their vertex. -/
theorem orthant_antitone {x y : Fin n → ℝ} (h : x ≤ y) : orthant y ≤ orthant x :=
  fun _ hs i => (h i).trans_lt (hs i)

/-- Two orthants meet in the orthant at the coordinatewise maximum. -/
theorem orthant_inf (x y : Fin n → ℝ) : orthant x ⊓ orthant y = orthant (x ⊔ y) := by
  ext s
  change (∀ i, x i < ofOrthant s i) ∧ (∀ i, y i < ofOrthant s i) ↔
    ∀ i, max (x i) (y i) < ofOrthant s i
  simp only [max_lt_iff, forall_and]

/-- The orthant at a point of an open is contained in that open. -/
theorem orthant_le {V : Opens (orthantSpace n)} {p : Fin n → ℝ} (hp : toOrthant p ∈ V) :
    orthant p ≤ V :=
  fun s hs => isUpperSet_opens V (show p ≤ ofOrthant s from fun i => (hs i).le) hp

/-- A common diagonal step covers: each point `x` of an open lies in the orthant at
`x - δ · 1`, a point of that open, for some `δ > 0`. -/
theorem exists_orthant_mem {V : Opens (orthantSpace n)} {x : WithOrthant n} (hx : x ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ toOrthant (fun i => ofOrthant x i - δ) ∈ V ∧
      x ∈ orthant (fun i => ofOrthant x i - δ) := by
  obtain ⟨δ, hδ, h⟩ := V.isOpen.2 (ofOrthant x) hx
  exact ⟨δ, hδ, h, fun i => sub_lt_self _ hδ⟩

/-- The continuous identity from the coordinate upper Alexandrov space to the orthant space. -/
def orthantId : upperSpace (Fin n → ℝ) ⟶ orthantSpace n :=
  TopCat.ofHom ⟨fun x => toOrthant (WithUpperSet.ofUpperSet x), by
    rw [continuous_def]
    intro S hS
    exact Topology.IsUpperSet.isOpen_iff_isUpperSet.2 fun _ _ hab ha => hS.1 hab ha⟩

@[simp]
theorem orthantId_apply (x : WithUpperSet (Fin n → ℝ)) :
    orthantId x = toOrthant (WithUpperSet.ofUpperSet x) :=
  rfl

variable (n) in
/-- The orthants as a basis indexed by the points of `Fin n → ℝ`: the strict order is the
all-strict order, two orthants meet at the coordinatewise maximum, and a point strictly above
`t` has the midpoint between them. -/
def orthantBasis : StrictBasis (Fin n → ℝ) (orthantSpace n) where
  ι := orthantId
  U := orthant
  antitone := orthant_antitone
  le_of_mem h i := (h i).le
  U_le := orthant_le
  exists_mem hx := by
    obtain ⟨_, _, h1, h2⟩ := exists_orthant_mem hx
    exact ⟨_, h1, h2⟩
  inf_le s t := (orthant_inf s t).le
  interpolate {t s} h := by
    refine ⟨fun i => (t i + s i) / 2, fun i => ?_, fun i => ?_⟩
    · have hi : t i < s i := h i
      change t i < (t i + s i) / 2
      linarith
    · have hi : t i < s i := h i
      change (t i + s i) / 2 < s i
      linarith

@[simp]
theorem orthantBasis_ι : (orthantBasis n).ι = orthantId :=
  rfl

@[simp]
theorem orthantBasis_U : (orthantBasis n).U = orthant :=
  rfl

/-- The strict order of the orthant basis is the all-strict order. -/
theorem strict_orthantBasis_iff {x y : Fin n → ℝ} :
    (orthantBasis n).Strict x y ↔ ∀ i, x i < y i :=
  Iff.rfl

/-- The orthants form a basis of the orthant space. -/
theorem isBasis_orthant : Opens.IsBasis (Set.range (orthant (n := n))) :=
  (orthantBasis n).isBasis_U

/-- The orthant topology is generated by the open orthants. -/
theorem eq_generateFrom :
    (inferInstance : TopologicalSpace (WithOrthant n)) =
      TopologicalSpace.generateFrom (SetLike.coe '' Set.range (orthant (n := n))) :=
  (isBasis_orthant (n := n)).eq_generateFrom

/-- `t + ε · 1` is strictly above `t` in every coordinate for `ε > 0`. -/
theorem strict_translation {ε : ℝ≥0} (hε : 0 < ε) (t : Fin n → ℝ) :
    (orthantBasis n).Strict t (CoordinateShift.translation ε t) :=
  fun i => lt_add_of_pos_right (t i) (NNReal.coe_pos.2 hε)

/-! ## Diagonal translations -/

section Shift

/-- The continuous map `x ↦ x - ε · 1` of the orthant space. -/
def orthantTranslate (ε : ℝ≥0) : orthantSpace n ⟶ orthantSpace n :=
  TopCat.ofHom ⟨fun x => toOrthant (downTranslation ε (ofOrthant x)), by
    rw [continuous_def]
    rintro S ⟨hup, hstep⟩
    refine ⟨fun a b hab ha => hup (fun i => sub_le_sub_right (hab i) _) ha, fun s hs => ?_⟩
    obtain ⟨δ, hδ, h⟩ := hstep _ hs
    refine ⟨δ, hδ, ?_⟩
    have e : downTranslation ε (fun i => s i - δ) = fun i => downTranslation ε s i - δ :=
      funext fun i => sub_right_comm _ _ _
    change toOrthant (downTranslation ε (fun i => s i - δ)) ∈ S
    rw [e]
    exact h⟩

@[simp]
theorem orthantTranslate_apply (ε : ℝ≥0) (x : WithOrthant n) :
    orthantTranslate ε x = toOrthant (downTranslation ε (ofOrthant x)) :=
  rfl

/-- The orthant at `t` pulls back to the orthant at `t + ε · 1` under `x ↦ x - ε · 1`. -/
theorem map_orthantTranslate_orthant (ε : ℝ≥0) (t : Fin n → ℝ) :
    (Opens.map (orthantTranslate ε)).obj (orthant t) =
      orthant (CoordinateShift.translation ε t) := by
  ext x
  change (∀ i, t i < ofOrthant x i - (ε : ℝ)) ↔ ∀ i, t i + (ε : ℝ) < ofOrthant x i
  exact forall_congr' fun _ => lt_sub_iff_add_lt

variable (n) in
/-- The diagonal translations `x ↦ x - ε · 1` of the orthant space. -/
def orthantTranslation : SpaceTranslation (orthantSpace n) where
  T := orthantTranslate
  map_le ε V x hx := isUpperSet_opens V
    (show downTranslation ε (ofOrthant x) ≤ ofOrthant x from
      fun _ => sub_le_self _ ε.coe_nonneg) hx
  map_comp ε δ V := by
    ext x
    change toOrthant (downTranslation ε (downTranslation δ (ofOrthant x))) ∈ V ↔
      toOrthant (downTranslation (ε + δ) (ofOrthant x)) ∈ V
    have e : downTranslation ε (downTranslation δ (ofOrthant x)) =
        downTranslation (ε + δ) (ofOrthant x) :=
      funext fun i => by
        simp only [downTranslation_apply, NNReal.coe_add]
        ring
    rw [e]

@[simp]
theorem orthantTranslation_T (ε : ℝ≥0) : (orthantTranslation n).T ε = orthantTranslate ε :=
  rfl

/-- The identity to the orthant space intertwines the diagonal translations. -/
theorem translate_comp_orthantId (ε : ℝ≥0) :
    translate ε ≫ orthantId = orthantId (n := n) ≫ orthantTranslate ε :=
  rfl

variable {C : Type u} [Category.{v} C]

/-- Pushing forward along `orthantId` carries the coordinate Alexandrov shift to the orthant
shift at the same radius. -/
theorem pushforward_map_sheafShift_map (ε : ℝ≥0) {F G : (upperSpace (Fin n → ℝ)).Sheaf C}
    (φ : F ⟶ G) :
    (TopCat.Sheaf.pushforward C orthantId).map ((sheafShift C ε).map φ) =
      ((orthantTranslation n).shift C ε).map ((TopCat.Sheaf.pushforward C orthantId).map φ) :=
  rfl

/-- Pushing forward along `orthantId` carries the coordinate Alexandrov transition to the orthant
transition at the same radius. -/
theorem pushforward_map_sheafTransition (ε : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    (TopCat.Sheaf.pushforward C orthantId).map ((sheafTransition C ε).app F) =
      ((orthantTranslation n).transition C ε).app ((TopCat.Sheaf.pushforward C orthantId).obj F) :=
  rfl

/-- Pushing forward along `orthantId` carries the coordinate Alexandrov addition isomorphism to
the orthant one. -/
theorem pushforward_map_sheafCompIso (ε δ : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    (TopCat.Sheaf.pushforward C orthantId).map ((sheafCompIso C ε δ).hom.app F) =
      ((orthantTranslation n).compIso C ε δ).hom.app
        ((TopCat.Sheaf.pushforward C orthantId).obj F) :=
  rfl

/-- A sheaf witness on the coordinate Alexandrov space, pushed forward along `orthantId`, is an
orthant witness at the same radius. -/
def orthantOfSheafInterleaving {ε : ℝ≥0} {F G : (upperSpace (Fin n → ℝ)).Sheaf C}
    (i : SheafInterleaving ε F G) :
    (orthantTranslation n).Interleaving ε ((TopCat.Sheaf.pushforward C orthantId).obj F)
      ((TopCat.Sheaf.pushforward C orthantId).obj G) where
  φ := (TopCat.Sheaf.pushforward C orthantId).map i.φ
  ψ := (TopCat.Sheaf.pushforward C orthantId).map i.ψ
  φ_ψ := by
    have h := (TopCat.Sheaf.pushforward C orthantId).congr_map i.φ_ψ
    rwa [Functor.map_comp, Functor.map_comp, pushforward_map_sheafShift_map,
      pushforward_map_sheafCompIso, pushforward_map_sheafTransition] at h
  ψ_φ := by
    have h := (TopCat.Sheaf.pushforward C orthantId).congr_map i.ψ_φ
    rwa [Functor.map_comp, Functor.map_comp, pushforward_map_sheafShift_map,
      pushforward_map_sheafCompIso, pushforward_map_sheafTransition] at h

end Shift

/-! ## Comparison with the coordinate shift -/

section Comparison

variable (R : Type u) [Ring R]

/-- The comparison `S ε ⋙ B ≅ B ⋙ CoordinateShift.shift ε`: at `F` and `t`, the restriction
along the equality `orthant t + ε · 1 = orthant (t + ε · 1)`. -/
def orthantShiftComparison (ε : ℝ≥0) :
    (orthantTranslation n).shift (ModuleCat.{0} R) ε ⋙ (orthantBasis n).B (ModuleCat.{0} R) ≅
      (orthantBasis n).B (ModuleCat.{0} R) ⋙ CoordinateShift.shift ε :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun t => TDA.Sheaf.restrictIso F.presheaf (map_orthantTranslate_orthant ε t))
      (fun _ => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        exact presheaf_map_comp_map_eq _ _ _ _ _))
    (fun φ => by
      apply NatTrans.ext
      funext t
      exact (φ.hom.naturality _).symm)

variable {R}

@[simp]
theorem orthantShiftComparison_hom_app_app (ε : ℝ≥0)
    (F : (orthantSpace n).Sheaf (ModuleCat.{0} R)) (t : Fin n → ℝ) :
    ((orthantShiftComparison R ε).hom.app F).app t =
      F.presheaf.map (homOfLE (map_orthantTranslate_orthant ε t).ge).op :=
  rfl

/-- Naturality of the comparison in the sheaf. -/
@[reassoc]
theorem orthantShiftComparison_hom_naturality (ε : ℝ≥0)
    {F G : (orthantSpace n).Sheaf (ModuleCat.{0} R)} (φ : F ⟶ G) :
    ((orthantBasis n).B _).map (((orthantTranslation n).shift _ ε).map φ) ≫
        (orthantShiftComparison R ε).hom.app G =
      (orthantShiftComparison R ε).hom.app F ≫
        (CoordinateShift.shift ε).map (((orthantBasis n).B _).map φ) :=
  (orthantShiftComparison R ε).hom.naturality φ

/-- The comparison carries the orthant transition to `CoordinateShift.transition`. -/
@[reassoc]
theorem orthantShiftComparison_transition (ε : ℝ≥0)
    (F : (orthantSpace n).Sheaf (ModuleCat.{0} R)) :
    ((orthantBasis n).B _).map (((orthantTranslation n).transition _ ε).app F) ≫
        (orthantShiftComparison R ε).hom.app F =
      CoordinateShift.transition ε (((orthantBasis n).B _).obj F) := by
  apply NatTrans.ext
  funext t
  exact presheaf_map_comp_map _ _ _ _

/-- The comparison carries the orthant addition isomorphism to `CoordinateShift.compIso`. -/
@[reassoc]
theorem orthantShiftComparison_compIso (ε δ : ℝ≥0)
    (F : (orthantSpace n).Sheaf (ModuleCat.{0} R)) :
    ((orthantBasis n).B _).map (((orthantTranslation n).compIso _ ε δ).hom.app F) ≫
        (orthantShiftComparison R (ε + δ)).hom.app F =
      (orthantShiftComparison R ε).hom.app (((orthantTranslation n).shift _ δ).obj F) ≫
        (CoordinateShift.shift ε).map ((orthantShiftComparison R δ).hom.app F) ≫
          (CoordinateShift.compIso ε δ (((orthantBasis n).B _).obj F)).hom := by
  apply NatTrans.ext
  funext t
  change F.presheaf.map _ ≫ F.presheaf.map _ =
    F.presheaf.map _ ≫ F.presheaf.map _ ≫ F.presheaf.map _
  exact presheaf_map_comp_map_eq_comp _ _ _ _ _ _

variable {ε : ℝ≥0}

/-- Under `B` and the comparison, the orthant double-shift composite becomes the coordinate
one. -/
theorem orthantB_map_doubleShift {F G : (orthantSpace n).Sheaf (ModuleCat.{0} R)}
    (f : F ⟶ ((orthantTranslation n).shift _ ε).obj G)
    (g : G ⟶ ((orthantTranslation n).shift _ ε).obj F) :
    ((orthantBasis n).B _).map
        (f ≫ ((orthantTranslation n).shift _ ε).map g ≫
          ((orthantTranslation n).compIso _ ε ε).hom.app F) ≫
        (orthantShiftComparison R (ε + ε)).hom.app F =
      (((orthantBasis n).B _).map f ≫ (orthantShiftComparison R ε).hom.app G) ≫
        (CoordinateShift.shift ε).map
            (((orthantBasis n).B _).map g ≫ (orthantShiftComparison R ε).hom.app F) ≫
          (CoordinateShift.compIso ε ε (((orthantBasis n).B _).obj F)).hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [orthantShiftComparison_compIso, orthantShiftComparison_hom_naturality_assoc]

/-- `B` is nonexpansive: an orthant witness gives a coordinate witness of the values on
orthants, at the same radius. -/
def orthantToCoordinateInterleaving {F G : (orthantSpace n).Sheaf (ModuleCat.{0} R)}
    (i : (orthantTranslation n).Interleaving ε F G) :
    CoordinateInterleaving ε (((orthantBasis n).B _).obj F) (((orthantBasis n).B _).obj G) where
  φ := ((orthantBasis n).B _).map i.φ ≫ (orthantShiftComparison R ε).hom.app G
  ψ := ((orthantBasis n).B _).map i.ψ ≫ (orthantShiftComparison R ε).hom.app F
  φ_ψ := by
    rw [← orthantB_map_doubleShift, i.φ_ψ, orthantShiftComparison_transition]
  ψ_φ := by
    rw [← orthantB_map_doubleShift, i.ψ_φ, orthantShiftComparison_transition]

/-- `Q` is nonexpansive: a coordinate witness of `M` and `N` gives an orthant witness of `Q M`
and `Q N` at the same radius, through `SheafInterleaving.equivUpperSet` and pushforward along
`orthantId`. -/
def orthantOfCoordinateInterleaving {M N : PModule.{u,0,0} R (Fin n → ℝ)}
    (i : CoordinateInterleaving ε M N) :
    (orthantTranslation n).Interleaving ε (((orthantBasis n).Q _).obj M)
      (((orthantBasis n).Q _).obj N) :=
  orthantOfSheafInterleaving ((SheafInterleaving.equivUpperSet M N).symm i)

end Comparison

/-! ## Positive-radius interleavings of `M` and `BQ(M)` -/

section UnitInterleaving

variable {R : Type u} [Ring R]

/-- For `ε > 0`, the reverse arrow `BQ(M) ⟶ S ε M`: at `t`, the projection to
`M(t + ε · 1)`. -/
def orthantUnitInterleavingψ (M : PModule.{u,0,0} R (Fin n → ℝ)) {ε : ℝ≥0} (hε : 0 < ε) :
    ((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj M) ⟶ (CoordinateShift.shift ε).obj M
    where
  app t := (orthantBasis n).proj M (strict_translation hε t)
  naturality _ _ f :=
    ((orthantBasis n).map_proj M f _).trans ((orthantBasis n).proj_comp_map M _ _).symm

@[simp]
theorem orthantUnitInterleavingψ_app (M : PModule.{u,0,0} R (Fin n → ℝ)) {ε : ℝ≥0}
    (hε : 0 < ε) (t : Fin n → ℝ) :
    (orthantUnitInterleavingψ M hε).app t = (orthantBasis n).proj M (strict_translation hε t) :=
  rfl

/-- For `ε > 0`, an actual `ε`-interleaving of `M` and `BQ(M)`: the forward arrow at `t` is
`M(t ≤ t + ε · 1)` followed by the unit at `t + ε · 1`, and the reverse arrow is the
projection from `BQ(M)(t)` to `M(t + ε · 1)`. The first composite is checked on `M`, the
second after projecting at every `s` strictly above `t + 2ε · 1`. -/
def orthantUnitInterleaving (M : PModule.{u,0,0} R (Fin n → ℝ)) {ε : ℝ≥0} (hε : 0 < ε) :
    CoordinateInterleaving ε M (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj M)) :=
  CoordinateInterleaving.ofApp
    (CoordinateShift.transition ε M ≫
      (CoordinateShift.shift ε).map (((orthantBasis n).unit _).app M))
    (orthantUnitInterleavingψ M hε)
    (fun t => by
      change M.map _ ≫ (((orthantBasis n).unit _).app M).app _ ≫
        (orthantBasis n).proj M _ ≫ M.map _ = M.map _
      exact (congrArg (M.map _ ≫ ·) ((orthantBasis n).unit_app_app_proj_assoc M _ _)).trans
        ((congrArg (M.map _ ≫ ·) (M.map_comp _ _).symm).trans (M.map_comp _ _).symm))
    (fun t => (orthantBasis n).proj_ext M fun s hs => by
      change ((orthantBasis n).proj M _ ≫ M.map _ ≫
          (((orthantBasis n).unit _).app M).app _ ≫
            (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj M)).map _) ≫
          (orthantBasis n).proj M hs =
        (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj M)).map _ ≫
          (orthantBasis n).proj M hs
      refine Eq.trans ?_ ((orthantBasis n).map_proj M _ hs).symm
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((orthantBasis n).proj M _ ≫ ·) ((Category.assoc _ _ _).trans
        (congrArg (M.map _ ≫ ·) ((Category.assoc _ _ _).trans
          (congrArg ((((orthantBasis n).unit _).app M).app _ ≫ ·)
            ((orthantBasis n).map_proj M _ hs)))))).trans ?_
      refine (congrArg ((orthantBasis n).proj M _ ≫ ·) (congrArg (M.map _ ≫ ·)
        ((orthantBasis n).unit_app_app_proj M _))).trans ?_
      exact ((orthantBasis n).proj_comp_map_assoc M _ _ _).trans
        ((orthantBasis n).proj_comp_map M _ _))

@[simp]
theorem orthantUnitInterleaving_φ (M : PModule.{u,0,0} R (Fin n → ℝ)) {ε : ℝ≥0} (hε : 0 < ε) :
    (orthantUnitInterleaving M hε).φ =
      CoordinateShift.transition ε M ≫
        (CoordinateShift.shift ε).map (((orthantBasis n).unit _).app M) :=
  rfl

@[simp]
theorem orthantUnitInterleaving_ψ (M : PModule.{u,0,0} R (Fin n → ℝ)) {ε : ℝ≥0} (hε : 0 < ε) :
    (orthantUnitInterleaving M hε).ψ = orthantUnitInterleavingψ M hε :=
  rfl

/-- `M` and `BQ(M)` are at coordinate interleaving distance zero. -/
theorem coordinateInterleavingDistance_orthantB_orthantQ (M : PModule.{u,0,0} R (Fin n → ℝ)) :
    coordinateInterleavingDistance M
      (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj M)) = 0 :=
  coordinateInterleavingDistance_eq_zero_iff.2 fun _ hε => ⟨orthantUnitInterleaving M hε⟩

end UnitInterleaving

/-! ## Extended distances -/

section Distance

variable {R : Type u} [Ring R]

/-- `B` does not increase distances. -/
theorem coordinateInterleavingDistance_orthantB_le
    (F G : (orthantSpace n).Sheaf (ModuleCat.{0} R)) :
    coordinateInterleavingDistance (((orthantBasis n).B _).obj F) (((orthantBasis n).B _).obj G) ≤
      (orthantTranslation n).interleavingDistance F G :=
  le_iInf₂ fun _ ⟨i⟩ => (orthantToCoordinateInterleaving i).distance_le

/-- `Q` does not increase distances. -/
theorem interleavingDistance_orthantQ_le (M N : PModule.{u,0,0} R (Fin n → ℝ)) :
    (orthantTranslation n).interleavingDistance (((orthantBasis n).Q _).obj M)
        (((orthantBasis n).Q _).obj N) ≤
      coordinateInterleavingDistance M N :=
  le_iInf₂ fun _ ⟨i⟩ => (orthantTranslation n).interleavingDistance_le
    (orthantOfCoordinateInterleaving i)

/-- `Q` preserves extended distances: the coordinate distance of `M` and `N` equals the orthant
distance of `Q M` and `Q N`. The lower bound replaces `M` and `N` by `BQ(M)` and `BQ(N)` at
distance zero. -/
theorem interleavingDistance_orthantQ (M N : PModule.{u,0,0} R (Fin n → ℝ)) :
    (orthantTranslation n).interleavingDistance (((orthantBasis n).Q _).obj M)
        (((orthantBasis n).Q _).obj N) =
      coordinateInterleavingDistance M N := by
  refine le_antisymm (interleavingDistance_orthantQ_le M N) ?_
  calc coordinateInterleavingDistance M N
      ≤ coordinateInterleavingDistance M
            (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj M)) +
          (coordinateInterleavingDistance
              (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj M))
              (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj N)) +
            coordinateInterleavingDistance
              (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj N)) N) :=
        (coordinateInterleavingDistance_triangle _ _ _).trans
          (add_le_add le_rfl (coordinateInterleavingDistance_triangle _ _ _))
    _ = coordinateInterleavingDistance
          (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj M))
          (((orthantBasis n).B _).obj (((orthantBasis n).Q _).obj N)) := by
        rw [coordinateInterleavingDistance_orthantB_orthantQ,
          coordinateInterleavingDistance_comm _ N,
          coordinateInterleavingDistance_orthantB_orthantQ, zero_add, add_zero]
    _ ≤ (orthantTranslation n).interleavingDistance (((orthantBasis n).Q _).obj M)
          (((orthantBasis n).Q _).obj N) :=
        coordinateInterleavingDistance_orthantB_le _ _

/-- `B` preserves extended distances: the orthant distance of `F` and `G` equals the coordinate
distance of `B F` and `B G`, by `QB ≅ 𝟭`. -/
theorem coordinateInterleavingDistance_orthantB
    (F G : (orthantSpace n).Sheaf (ModuleCat.{0} R)) :
    coordinateInterleavingDistance (((orthantBasis n).B _).obj F) (((orthantBasis n).B _).obj G) =
      (orthantTranslation n).interleavingDistance F G := by
  refine le_antisymm (coordinateInterleavingDistance_orthantB_le F G) ?_
  exact ((orthantTranslation n).interleavingDistance_congr
    (((orthantBasis n).counitIso _).app F) (((orthantBasis n).counitIso _).app G)).symm.trans_le
      (interleavingDistance_orthantQ_le _ _)

end Distance

end

end TDA.Sheaf.OrthantSheaf
