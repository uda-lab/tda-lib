import TDA.Sheaf.DerivedPlus
import TDA.Sheaf.RealLine
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Closed real bands and their correspondence functors on `D⁺(Sh(ℝ; k))`

For `a : ℝ`, the closed band `D a = {(x, y) ∈ ℝ × ℝ | dist x y ≤ a}` carries the subspace
topology. Its two projections `p a (x, y) = x` and `q a (x, y) = y` are proper maps to the
real line (`isProperMap_p`, `isProperMap_q`): the preimage of a compact set `K` is closed in
`K × cthickening a K` (or its mirror image). For `a ≤ b`, `incl h : D a ⟶ D b` is the closed
embedding of the smaller band (`isClosedEmbedding_incl`), with `incl h ≫ p b = p a` and
`incl h ≫ q b = q a` definitionally. `shear a : band a ≃ₜ Set.Icc (-a) a × ℝ` sends `(x, y)`
to `(y - x, x)`: under it `p a` is the second projection and `q a` is the sum
(`shear_snd`, `shear_add`).

Fix a ring `k`, a derived category structure on sheaves of `k`-modules on the real line and
one on each band. These are instance arguments; no global instance is installed.

* `T k a := pullbackPlus k (p a) ⋙ pushforwardPlus k (q a)` is the functor `F ↦ R(q_a)_* p_a⁻¹ F`
  on `DerivedCategory.Plus (Sh ℝ)`.
* `restr k h : T k b ⟶ T k a` for `h : a ≤ b` is the radius map: the derived unit of the closed
  inclusion `incl h`, followed by the composition isomorphisms (`corrRestr`). It satisfies
  `restr_refl` and `restr_trans`.
* `T0Iso k : T k 0 ≅ 𝟭` uses that on `D 0` the projections coincide (`p_zero_eq_q_zero`) and
  are a homeomorphism with inverse the diagonal (`diagonalZero`); it is the inverse of the
  derived unit of `q 0` (`T0Iso_inv_app`).
* `aug k h : T k a ⟶ 𝟭` for `h : 0 ≤ a` is the augmentation `restr k h ≫ (T0Iso k).hom`;
  `aug_zero` and `restr_comp_aug` identify it at `a = 0` and along radius maps.

This is the actual derived functor on `D⁺`; boundedness, base change and the composition
`T a ⋙ T b` are not treated here.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace TDA.Sheaf.BandConvolution

/-- The closed band `{(x, y) | dist x y ≤ a}` in `ℝ × ℝ`. -/
def band (a : ℝ) : Set (ℝ × ℝ) := {z | dist z.1 z.2 ≤ a}

/-- Membership in the closed band. -/
@[simp]
lemma mem_band {a : ℝ} {z : ℝ × ℝ} : z ∈ band a ↔ dist z.1 z.2 ≤ a := Iff.rfl

/-- The closed band as a topological space, with the subspace topology. -/
abbrev D (a : ℝ) : TopCat.{0} := TopCat.of (band a)

/-- The band is closed. -/
lemma isClosed_band (a : ℝ) : IsClosed (band a) :=
  isClosed_le (continuous_fst.dist continuous_snd) continuous_const

/-- The first projection `p_a (x, y) = x`. -/
def p (a : ℝ) : D a ⟶ realLine := TopCat.ofHom ⟨fun z => z.1.1, by fun_prop⟩

/-- The second projection `q_a (x, y) = y`. -/
def q (a : ℝ) : D a ⟶ realLine := TopCat.ofHom ⟨fun z => z.1.2, by fun_prop⟩

/-- The closed inclusion `D a ⟶ D b` for `a ≤ b`. -/
def incl {a b : ℝ} (h : a ≤ b) : D a ⟶ D b :=
  TopCat.ofHom ⟨fun z => ⟨z.1, le_trans z.2 h⟩, by fun_prop⟩

@[simp]
lemma p_apply (a : ℝ) (z : D a) : p a z = z.1.1 := rfl

@[simp]
lemma q_apply (a : ℝ) (z : D a) : q a z = z.1.2 := rfl

lemma incl_apply {a b : ℝ} (h : a ≤ b) (z : D a) : ((incl h z : band b) : ℝ × ℝ) = z.1 := rfl

/-- The inclusion commutes with the first projections. -/
lemma incl_p {a b : ℝ} (h : a ≤ b) : incl h ≫ p b = p a := rfl

/-- The inclusion commutes with the second projections. -/
lemma incl_q {a b : ℝ} (h : a ≤ b) : incl h ≫ q b = q a := rfl

/-- The inclusion of a band into itself is the identity. -/
lemma incl_refl (a : ℝ) : incl (le_refl a) = 𝟙 (D a) := rfl

/-- Inclusions compose. -/
lemma incl_trans {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    incl hab ≫ incl hbc = incl (hab.trans hbc) := rfl

/-- The inclusion of a smaller band is a closed embedding. -/
lemma isClosedEmbedding_incl {a b : ℝ} (h : a ≤ b) : Topology.IsClosedEmbedding (incl h) := by
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (incl h).hom.continuous
    (fun x y hxy => Subtype.ext (by
      have := congrArg (fun w : band b => (w : ℝ × ℝ)) hxy
      simpa [incl] using this)) ?_
  intro s hs
  obtain ⟨t, ht, rfl⟩ := (Topology.IsInducing.subtypeVal.isClosed_iff).1 hs
  have : (incl h) '' ((↑) ⁻¹' t) = ((↑) : band b → ℝ × ℝ) ⁻¹' (t ∩ band a) := by
    ext ⟨z, hz⟩
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨w, hw⟩, hwt, hweq⟩
      have := congrArg Subtype.val hweq
      simp [incl] at this
      subst this
      exact ⟨hwt, hw⟩
    · rintro ⟨hzt, hza⟩
      exact ⟨⟨z, hza⟩, hzt, rfl⟩
  rw [this]
  exact (ht.inter (isClosed_band a)).preimage continuous_subtype_val

/-- The first projection of a band is proper. -/
lemma isProperMap_p (a : ℝ) : IsProperMap (p a) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(p a).hom.continuous, fun K hK => ?_⟩
  have hc : IsCompact (band a ∩ Prod.fst ⁻¹' K) :=
    (hK.prod (hK.cthickening (r := a))).of_isClosed_subset
      ((isClosed_band a).inter (hK.isClosed.preimage continuous_fst)) (by
        rintro ⟨x, y⟩ ⟨hb, hx⟩
        refine ⟨hx, Metric.mem_cthickening_of_dist_le y x a K hx ?_⟩
        rw [dist_comm]; exact hb)
  have := (isClosed_band a).isClosedEmbedding_subtypeVal.isCompact_preimage hc
  convert this using 1
  ext z
  simp [p]

/-- The second projection of a band is proper. -/
lemma isProperMap_q (a : ℝ) : IsProperMap (q a) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(q a).hom.continuous, fun K hK => ?_⟩
  have hc : IsCompact (band a ∩ Prod.snd ⁻¹' K) :=
    ((hK.cthickening (r := a)).prod hK).of_isClosed_subset
      ((isClosed_band a).inter (hK.isClosed.preimage continuous_snd)) (by
        rintro ⟨x, y⟩ ⟨hb, hy⟩
        exact ⟨Metric.mem_cthickening_of_dist_le x y a K hy hb, hy⟩)
  have := (isClosed_band a).isClosedEmbedding_subtypeVal.isCompact_preimage hc
  convert this using 1
  ext z
  simp [q]

/-- The shear homeomorphism `band a ≃ₜ [-a, a] × ℝ`, `(x, y) ↦ (y - x, x)`. -/
def shear (a : ℝ) : band a ≃ₜ (Set.Icc (-a) a × ℝ) where
  toFun z := (⟨z.1.2 - z.1.1, by
      obtain ⟨h1, h2⟩ := abs_le.1 (show |z.1.1 - z.1.2| ≤ a by
        simpa [band, Real.dist_eq] using z.2)
      exact ⟨by linarith, by linarith⟩⟩, z.1.1)
  invFun w := ⟨(w.2, w.2 + w.1.1), by
      show dist w.2 (w.2 + w.1.1) ≤ a
      rw [Real.dist_eq, abs_le]
      obtain ⟨h1, h2⟩ := w.1.2
      constructor <;> linarith⟩
  left_inv z := by
    apply Subtype.ext
    ext <;> simp
  right_inv w := by
    refine Prod.ext (Subtype.ext ?_) rfl
    simp
  continuous_toFun :=
    (((continuous_snd.comp continuous_subtype_val).sub
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
      (continuous_fst.comp continuous_subtype_val)
  continuous_invFun :=
    (continuous_snd.prodMk (continuous_snd.add
      (continuous_subtype_val.comp continuous_fst))).subtype_mk _

/-- Under `shear`, the first projection `p a` is the second coordinate. -/
lemma shear_snd (a : ℝ) (z : band a) : (shear a z).2 = p a z := rfl

/-- Under `shear`, the second projection `q a` is the sum of the coordinates. -/
lemma shear_add (a : ℝ) (z : band a) : (shear a z).2 + ((shear a z).1 : ℝ) = q a z := by
  simp [shear, q]

/-- On the zero band the two projections agree. -/
lemma p_zero_eq_q_zero : p 0 = q 0 :=
  TopCat.ext fun z => dist_le_zero.1 z.2

/-- The diagonal `ℝ ⟶ D 0`, `x ↦ (x, x)`. -/
def diagonalZero : realLine ⟶ D 0 :=
  TopCat.ofHom ⟨fun x => ⟨(x, x), by show dist x x ≤ 0; simp⟩,
    (continuous_id.prodMk continuous_id).subtype_mk (fun x => show dist x x ≤ 0 by simp)⟩

/-- The diagonal is inverse to `q 0`: `D 0` is homeomorphic to the real line. -/
instance isIso_q_zero : IsIso (q 0) := by
  refine ⟨⟨diagonalZero, ?_, ?_⟩⟩
  · refine TopCat.ext fun z => Subtype.ext (Prod.ext ?_ ?_)
    · have h : dist (z : ℝ × ℝ).1 (z : ℝ × ℝ).2 ≤ 0 := z.2
      have h' := (dist_le_zero.1 h).symm
      simpa [q, diagonalZero] using h'
    · simp [q, diagonalZero]
  · exact TopCat.ext fun x => by simp [q, diagonalZero]

variable (k : Type) [Ring k] [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]

/-- The band functor `T_a F = R(q_a)_* p_a⁻¹ F` on `D⁺(Sh(ℝ; k))`. -/
abbrev T (a : ℝ) : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k)) ⥤
    DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k)) :=
  pullbackPlus k (p a) ⋙ pushforwardPlus k (q a)

/-- The radius map `T_b ⟶ T_a` for `a ≤ b`: the derived unit of the closed inclusion
`incl h : D a ⟶ D b`, followed by the composition isomorphisms. -/
def restr {a b : ℝ} (h : a ≤ b) : T k b ⟶ T k a :=
  corrRestr k (incl h) (p b) (q b)

/-- The components of the radius map. -/
lemma restr_app {a b : ℝ} (h : a ≤ b)
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (restr k h).app M =
      (pushforwardPlus k (q b)).map ((derivedUnit k (incl h)).app ((pullbackPlus k (p b)).obj M)) ≫
        (pushforwardPlusCompIso k (incl h) (q b)).inv.app
          ((pullbackPlus k (incl h)).obj ((pullbackPlus k (p b)).obj M)) ≫
        (pushforwardPlus k (q a)).map ((pullbackPlusCompIso k (incl h) (p b)).hom.app M) :=
  corrRestr_app k (incl h) (p b) (q b) M

/-- The radius map of `a ≤ a` is the identity. -/
lemma restr_refl (a : ℝ) : restr k (le_refl a) = 𝟙 _ :=
  corrRestr_id k (p a) (q a)

/-- Radius maps compose: `T_c ⟶ T_b ⟶ T_a` is the radius map of `a ≤ c`. -/
lemma restr_trans {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    restr k hbc ≫ restr k hab = restr k (hab.trans hbc) :=
  corrRestr_comp k (incl hab) (incl hbc) (p c) (q c)

/-- `T_0 ≅ 𝟭`: on the zero band `p 0 = q 0` is a homeomorphism, and the derived unit of `q 0`
is invertible. -/
def T0Iso : T k 0 ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (eqToIso (congrArg (pullbackPlus k) p_zero_eq_q_zero))
      (pushforwardPlus k (q 0)) ≪≫
    (asIso (derivedUnit k (q 0))).symm

/-- The inverse of `T0Iso` is the derived unit of `q 0`, transported along `p 0 = q 0`. -/
lemma T0Iso_inv : (T0Iso k).inv = derivedUnit k (q 0) ≫
    Functor.whiskerRight (eqToHom (congrArg (pullbackPlus k) p_zero_eq_q_zero.symm))
      (pushforwardPlus k (q 0)) := rfl

/-- The augmentation `T_a ⟶ 𝟭` for `0 ≤ a`: the radius map to `T_0` followed by `T0Iso`. -/
def aug {a : ℝ} (h : 0 ≤ a) : T k a ⟶ 𝟭 _ :=
  restr k h ≫ (T0Iso k).hom

/-- At `a = 0` the augmentation is `T0Iso`. -/
lemma aug_zero : aug k (le_refl (0 : ℝ)) = (T0Iso k).hom := by
  rw [aug, restr_refl, Category.id_comp]

/-- The augmentation is compatible with the radius maps. -/
lemma restr_comp_aug {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) :
    restr k hab ≫ aug k ha = aug k (ha.trans hab) := by
  rw [aug, ← Category.assoc, restr_trans, aug]

end TDA.Sheaf.BandConvolution
