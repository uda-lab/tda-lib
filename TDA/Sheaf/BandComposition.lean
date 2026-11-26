import TDA.Sheaf.BandStalks

/-!
# The composition isomorphism of the band functors

For `a b : ℝ` let `Z a b = {(x, y, z) ∈ ℝ³ | dist x y ≤ a ∧ dist y z ≤ b}` (`bandChain`), with the
subspace topology, and its three projections

* `pr₁₂ a b : Z a b ⟶ D a`, `(x, y, z) ↦ (x, y)`;
* `pr₂₃ a b : Z a b ⟶ D b`, `(x, y, z) ↦ (y, z)`;
* `pr₁₃ a b : Z a b ⟶ D (a + b)`, `(x, y, z) ↦ (x, z)` (the triangle inequality).

They satisfy `pr₁₂ ≫ q a = pr₂₃ ≫ p b` (`pr₁₂_q`), `pr₁₃ ≫ p (a + b) = pr₁₂ ≫ p a` (`pr₁₃_p`) and
`pr₁₃ ≫ q (a + b) = pr₂₃ ≫ q b` (`pr₁₃_q`), all definitionally. Both `pr₂₃` and `pr₁₃` are proper
(`isProperMap_pr₂₃`, `isProperMap_pr₁₃`) and are interval fibrations
(`TDA.Sheaf.IntervalFibration`), for all `a b : ℝ`:

* `intervalFibration_pr₂₃ a b`: fibre coordinate `x`, fibre `[y - a, y + a]` over `(y, z)`, with
  fibre parametrisation `fibreEmb₂₃ a b (y, z) : x ↦ (x, y, z)`; nonempty for `0 ≤ a`.
* `intervalFibration_pr₁₃ a b`: fibre coordinate `y`, fibre
  `[max (x - a) (z - b), min (x + a) (z + b)]` over `(x, z)`, with fibre parametrisation
  `fibreEmb₁₃ a b (x, z) : y ↦ (x, y, z)`; nonempty for `0 ≤ a`, `0 ≤ b` (`lo_le_hi_pr₁₃`), a
  point when `dist x z = a + b`.

With these:

* `isIso_baseChange_pr₁₂_q`: the base change `R(q a)_* ⋙ (p b)⁻¹ ⟶ pr₁₂⁻¹ ⋙ R(pr₂₃)_*` of the
  central square is an isomorphism (the fibrewise criterion `isIso_baseChange_of_isFibreParam`:
  the fibres of `pr₂₃` are carried by `pr₁₂` onto the fibres `fibreEmb a y` of `q a`).
* `isIso_derivedUnit_pr₁₃`: for `0 ≤ a`, `0 ≤ b` the derived unit `𝟭 ⟶ pr₁₃⁻¹ ⋙ R(pr₁₃)_*` is an
  isomorphism (`IntervalFibration.isIso_derivedUnit`).
* `TCompRestr k a b : T k (a + b) ⟶ (pr₁₂ ≫ p a)⁻¹ ⋙ R(pr₂₃ ≫ q b)_*` is the restriction
  `corrRestr` along `pr₁₃` (`TCompRestr_eq`, `TCompRestr_app`), with its target written through
  `pr₁₃_p` and `pr₁₃_q`; it is invertible for `0 ≤ a`, `0 ≤ b` (`isIso_TCompRestr`).
* `TComp k ha hb : T k a ⋙ T k b ≅ T k (a + b)` for `0 ≤ a`, `0 ≤ b`: the composite of
  `R(q b)_*` of the base change of the central square, `R(pr₂₃)_* ⋙ R(q b)_* ≅ R(pr₂₃ ≫ q b)_*`,
  `pr₁₂⁻¹ ⋙ (p a)⁻¹ ≅ (pr₁₂ ≫ p a)⁻¹`, and the inverse of `TCompRestr k a b`.
  `TComp_hom_app_TCompRestr` and `TComp_inv_app` describe its components through these pieces.

Derived categories are instance arguments: on the real line, on every band `D a`, on every `Z a b`,
on the point and on every compact interval `[u, v]`.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace

namespace TDA.Sheaf.BandConvolution

/-- The set of triples `(x, y, z)` with `dist x y ≤ a` and `dist y z ≤ b`, in `ℝ × ℝ × ℝ`. -/
def bandChain (a b : ℝ) : Set (ℝ × ℝ × ℝ) := {w | dist w.1 w.2.1 ≤ a ∧ dist w.2.1 w.2.2 ≤ b}

/-- Membership in `bandChain a b`. -/
@[simp]
lemma mem_bandChain {a b : ℝ} {w : ℝ × ℝ × ℝ} :
    w ∈ bandChain a b ↔ dist w.1 w.2.1 ≤ a ∧ dist w.2.1 w.2.2 ≤ b := Iff.rfl

/-- `bandChain a b` is closed. -/
lemma isClosed_bandChain (a b : ℝ) : IsClosed (bandChain a b) :=
  (isClosed_le (continuous_fst.dist (continuous_fst.comp continuous_snd)) continuous_const).inter
    (isClosed_le ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd))
      continuous_const)

/-- The space `Z a b = {(x, y, z) | dist x y ≤ a ∧ dist y z ≤ b}`, with the subspace topology. -/
abbrev Z (a b : ℝ) : TopCat.{0} := TopCat.of (bandChain a b)

/-- The triangle inequality on `Z a b`: `dist x z ≤ a + b`. -/
lemma dist_le_add_of_mem_bandChain {a b : ℝ} (w : bandChain a b) :
    dist w.1.1 w.1.2.2 ≤ a + b :=
  (dist_triangle _ _ _).trans (add_le_add w.2.1 w.2.2)

/-- The projection `pr₁₂ (x, y, z) = (x, y)` to `D a`. -/
def pr₁₂ (a b : ℝ) : Z a b ⟶ D a :=
  TopCat.ofHom ⟨fun w => ⟨(w.1.1, w.1.2.1), w.2.1⟩, by fun_prop⟩

/-- The projection `pr₂₃ (x, y, z) = (y, z)` to `D b`. -/
def pr₂₃ (a b : ℝ) : Z a b ⟶ D b :=
  TopCat.ofHom ⟨fun w => ⟨(w.1.2.1, w.1.2.2), w.2.2⟩, by fun_prop⟩

/-- The projection `pr₁₃ (x, y, z) = (x, z)` to `D (a + b)`. -/
def pr₁₃ (a b : ℝ) : Z a b ⟶ D (a + b) :=
  TopCat.ofHom ⟨fun w => ⟨(w.1.1, w.1.2.2), dist_le_add_of_mem_bandChain w⟩, by fun_prop⟩

/-- `pr₁₂ (x, y, z) = (x, y)`. -/
@[simp]
lemma coe_pr₁₂_apply (a b : ℝ) (w : Z a b) : ((pr₁₂ a b w : band a) : ℝ × ℝ) = (w.1.1, w.1.2.1) :=
  rfl

/-- `pr₂₃ (x, y, z) = (y, z)`. -/
@[simp]
lemma coe_pr₂₃_apply (a b : ℝ) (w : Z a b) :
    ((pr₂₃ a b w : band b) : ℝ × ℝ) = (w.1.2.1, w.1.2.2) :=
  rfl

/-- `pr₁₃ (x, y, z) = (x, z)`. -/
@[simp]
lemma coe_pr₁₃_apply (a b : ℝ) (w : Z a b) :
    ((pr₁₃ a b w : band (a + b)) : ℝ × ℝ) = (w.1.1, w.1.2.2) :=
  rfl

/-- **The central square**: `pr₁₂ ≫ q a = pr₂₃ ≫ p b`, both `(x, y, z) ↦ y`. -/
theorem pr₁₂_q (a b : ℝ) : pr₁₂ a b ≫ q a = pr₂₃ a b ≫ p b := rfl

/-- `pr₁₃ ≫ p (a + b) = pr₁₂ ≫ p a`, both `(x, y, z) ↦ x`. -/
theorem pr₁₃_p (a b : ℝ) : pr₁₃ a b ≫ p (a + b) = pr₁₂ a b ≫ p a := rfl

/-- `pr₁₃ ≫ q (a + b) = pr₂₃ ≫ q b`, both `(x, y, z) ↦ z`. -/
theorem pr₁₃_q (a b : ℝ) : pr₁₃ a b ≫ q (a + b) = pr₂₃ a b ≫ q b := rfl

/-- A point within `r` of `c` on both sides is at distance at most `r` from `c`. -/
private lemma dist_le_of_le_of_le {c r y : ℝ} (h₁ : c - r ≤ y) (h₂ : y ≤ c + r) :
    dist y c ≤ r := by
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- A point at distance at most `r` from `c` lies in `[c - r, c + r]`. -/
private lemma le_of_dist_le {c r y : ℝ} (h : dist y c ≤ r) : c - r ≤ y ∧ y ≤ c + r := by
  rw [Real.dist_eq, abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `pr₂₃` is proper: the preimage of a compact `K ⊆ D b` lies in `cthickening a K₁ × K`, where
`K₁` is the set of first coordinates of `K`. -/
lemma isProperMap_pr₂₃ (a b : ℝ) : IsProperMap (pr₂₃ a b) := by
  have : LocallyCompactSpace (D b) := (isClosed_band b).locallyCompactSpace
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(pr₂₃ a b).hom.continuous, fun K hK => ?_⟩
  have hK' : IsCompact (Subtype.val '' K : Set (ℝ × ℝ)) := hK.image continuous_subtype_val
  have hc : IsCompact (bandChain a b ∩ Prod.snd ⁻¹' (Subtype.val '' K)) :=
    (((hK'.image continuous_fst).cthickening (r := a)).prod hK').of_isClosed_subset
      ((isClosed_bandChain a b).inter (hK'.isClosed.preimage continuous_snd)) (by
        rintro ⟨x, y, z⟩ ⟨⟨hxy, -⟩, hyz⟩
        exact ⟨Metric.mem_cthickening_of_dist_le x y a _ ⟨(y, z), hyz, rfl⟩ hxy, hyz⟩)
  have := (isClosed_bandChain a b).isClosedEmbedding_subtypeVal.isCompact_preimage hc
  convert this using 1
  ext w
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  refine ⟨fun h => ⟨w.2, pr₂₃ a b w, h, rfl⟩, fun h => ?_⟩
  exact (Subtype.val_injective.mem_set_image (a := pr₂₃ a b w)).1 h.2

/-- `pr₁₃` is proper: the preimage of a compact `K ⊆ D (a + b)` lies in the image of
`K × cthickening a K₁`, where `K₁` is the set of first coordinates of `K`. -/
lemma isProperMap_pr₁₃ (a b : ℝ) : IsProperMap (pr₁₃ a b) := by
  have : LocallyCompactSpace (D (a + b)) := (isClosed_band (a + b)).locallyCompactSpace
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(pr₁₃ a b).hom.continuous, fun K hK => ?_⟩
  have hK' : IsCompact (Subtype.val '' K : Set (ℝ × ℝ)) := hK.image continuous_subtype_val
  have hc : IsCompact (bandChain a b ∩
      (fun w : ℝ × ℝ × ℝ => (w.1, w.2.2)) ⁻¹' (Subtype.val '' K)) :=
    ((hK'.prod ((hK'.image continuous_fst).cthickening (r := a))).image
      (f := fun u : (ℝ × ℝ) × ℝ => (u.1.1, u.2, u.1.2)) (by fun_prop)).of_isClosed_subset
      ((isClosed_bandChain a b).inter (hK'.isClosed.preimage (by fun_prop))) (by
        rintro ⟨x, y, z⟩ ⟨⟨hxy, -⟩, hxz⟩
        refine ⟨((x, z), y), ⟨hxz, ?_⟩, rfl⟩
        rw [dist_comm] at hxy
        exact Metric.mem_cthickening_of_dist_le y x a _ ⟨(x, z), hxz, rfl⟩ hxy)
  have := (isClosed_bandChain a b).isClosedEmbedding_subtypeVal.isCompact_preimage hc
  convert this using 1
  ext w
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  refine ⟨fun h => ⟨w.2, pr₁₃ a b w, h, rfl⟩, fun h => ?_⟩
  exact (Subtype.val_injective.mem_set_image (a := pr₁₃ a b w)).1 h.2

section fibration

variable (a b : ℝ)

/-- **The fibre coordinate `x` of `pr₂₃`**: `pr₂₃` is proper and `(x, y, z) ↦ ((y, z), x)`
recovers the inclusion of `Z a b` into `ℝ³`. -/
def fibreCoordinate_pr₂₃ : FibreCoordinate (pr₂₃ a b) where
  t := ⟨fun w => w.1.1, by fun_prop⟩
  isInducing := Topology.IsInducing.of_comp (by fun_prop)
    (show Continuous fun u : D b × ℝ => (u.2, u.1.1.1, u.1.1.2) by fun_prop)
    Topology.IsInducing.subtypeVal
  isClosedMap := (isProperMap_pr₂₃ a b).isClosedMap

/-- The fibre coordinate of `pr₂₃` is the first coordinate. -/
@[simp]
lemma fibreCoordinate_pr₂₃_t (w : Z a b) : (fibreCoordinate_pr₂₃ a b).t w = w.1.1 := rfl

/-- The fibre of `pr₂₃` over `(y, z)`, parametrised by `[y - a, y + a]`: `x ↦ (x, y, z)`. -/
def fibreEmb₂₃ (v : D b) : TopCat.of (Set.Icc (v.1.1 - a) (v.1.1 + a)) ⟶ Z a b :=
  TopCat.ofHom ⟨fun x => ⟨(x.1, v.1.1, v.1.2), dist_le_of_le_of_le x.2.1 x.2.2, v.2⟩, by fun_prop⟩

/-- `fibreEmb₂₃ a b (y, z)` sends `x` to `(x, y, z)`. -/
@[simp]
lemma coe_fibreEmb₂₃_apply (v : D b) (x : TopCat.of (Set.Icc (v.1.1 - a) (v.1.1 + a))) :
    ((fibreEmb₂₃ a b v x : bandChain a b) : ℝ × ℝ × ℝ) = (x.1, v.1.1, v.1.2) := rfl

/-- `fibreEmb₂₃ a b v` parametrises the fibre of `pr₂₃` at `v` in the coordinate `x`. -/
theorem isFibreParam_fibreEmb₂₃ (v : D b) :
    (fibreCoordinate_pr₂₃ a b).IsFibreParam v (fibreEmb₂₃ a b v) where
  comp_eq := rfl
  t_apply _ := rfl
  mem_range w hw := by
    obtain ⟨⟨x, y, z⟩, hxy, hyz⟩ := w
    subst hw
    exact ⟨⟨x, le_of_dist_le hxy⟩, rfl⟩

/-- **`pr₂₃` is an interval fibration**, with fibre coordinate `x`, fibre intervals
`[y - a, y + a]` over `(y, z)` and fibre parametrisations `fibreEmb₂₃ a b`. -/
def intervalFibration_pr₂₃ : IntervalFibration (pr₂₃ a b) where
  toFibreCoordinate := fibreCoordinate_pr₂₃ a b
  lo v := v.1.1 - a
  hi v := v.1.1 + a
  e := fibreEmb₂₃ a b
  isFibreParam := isFibreParam_fibreEmb₂₃ a b

/-- The fibre parametrisations of `intervalFibration_pr₂₃ a b` are `fibreEmb₂₃ a b`. -/
@[simp]
lemma intervalFibration_pr₂₃_e (v : D b) : (intervalFibration_pr₂₃ a b).e v = fibreEmb₂₃ a b v :=
  rfl

/-- The fibres of `pr₂₃` are nonempty for `0 ≤ a`. -/
lemma lo_le_hi_pr₂₃ {a : ℝ} (ha : 0 ≤ a) (v : D b) :
    (intervalFibration_pr₂₃ a b).lo v ≤ (intervalFibration_pr₂₃ a b).hi v := by
  change v.1.1 - a ≤ v.1.1 + a
  linarith

/-- **The fibre coordinate `y` of `pr₁₃`**: `pr₁₃` is proper and `(x, y, z) ↦ ((x, z), y)`
recovers the inclusion of `Z a b` into `ℝ³`. -/
def fibreCoordinate_pr₁₃ : FibreCoordinate (pr₁₃ a b) where
  t := ⟨fun w => w.1.2.1, by fun_prop⟩
  isInducing := Topology.IsInducing.of_comp (by fun_prop)
    (show Continuous fun u : D (a + b) × ℝ => (u.1.1.1, u.2, u.1.1.2) by fun_prop)
    Topology.IsInducing.subtypeVal
  isClosedMap := (isProperMap_pr₁₃ a b).isClosedMap

/-- The fibre coordinate of `pr₁₃` is the middle coordinate. -/
@[simp]
lemma fibreCoordinate_pr₁₃_t (w : Z a b) : (fibreCoordinate_pr₁₃ a b).t w = w.1.2.1 := rfl

/-- The fibre of `pr₁₃` over `(x, z)`, parametrised by `[max (x - a) (z - b), min (x + a) (z + b)]`:
`y ↦ (x, y, z)`. -/
def fibreEmb₁₃ (v : D (a + b)) :
    TopCat.of (Set.Icc (max (v.1.1 - a) (v.1.2 - b)) (min (v.1.1 + a) (v.1.2 + b))) ⟶ Z a b :=
  TopCat.ofHom ⟨fun y => ⟨(v.1.1, y.1, v.1.2),
      by
        rw [dist_comm]
        exact dist_le_of_le_of_le ((le_max_left _ _).trans y.2.1) (y.2.2.trans (min_le_left _ _)),
      dist_le_of_le_of_le ((le_max_right _ _).trans y.2.1) (y.2.2.trans (min_le_right _ _))⟩,
    by fun_prop⟩

/-- `fibreEmb₁₃ a b (x, z)` sends `y` to `(x, y, z)`. -/
@[simp]
lemma coe_fibreEmb₁₃_apply (v : D (a + b))
    (y : TopCat.of (Set.Icc (max (v.1.1 - a) (v.1.2 - b)) (min (v.1.1 + a) (v.1.2 + b)))) :
    ((fibreEmb₁₃ a b v y : bandChain a b) : ℝ × ℝ × ℝ) = (v.1.1, y.1, v.1.2) := rfl

/-- `fibreEmb₁₃ a b v` parametrises the fibre of `pr₁₃` at `v` in the coordinate `y`. -/
theorem isFibreParam_fibreEmb₁₃ (v : D (a + b)) :
    (fibreCoordinate_pr₁₃ a b).IsFibreParam v (fibreEmb₁₃ a b v) where
  comp_eq := rfl
  t_apply _ := rfl
  mem_range w hw := by
    obtain ⟨⟨x, y, z⟩, hxy, hyz⟩ := w
    subst hw
    rw [dist_comm] at hxy
    obtain ⟨h₁, h₂⟩ := le_of_dist_le hxy
    obtain ⟨h₃, h₄⟩ := le_of_dist_le hyz
    exact ⟨⟨y, max_le h₁ h₃, le_min h₂ h₄⟩, rfl⟩

/-- **`pr₁₃` is an interval fibration**, with fibre coordinate `y`, fibre intervals
`[max (x - a) (z - b), min (x + a) (z + b)]` over `(x, z)` and fibre parametrisations
`fibreEmb₁₃ a b`. -/
def intervalFibration_pr₁₃ : IntervalFibration (pr₁₃ a b) where
  toFibreCoordinate := fibreCoordinate_pr₁₃ a b
  lo v := max (v.1.1 - a) (v.1.2 - b)
  hi v := min (v.1.1 + a) (v.1.2 + b)
  e := fibreEmb₁₃ a b
  isFibreParam := isFibreParam_fibreEmb₁₃ a b

/-- The fibre parametrisations of `intervalFibration_pr₁₃ a b` are `fibreEmb₁₃ a b`. -/
@[simp]
lemma intervalFibration_pr₁₃_e (v : D (a + b)) :
    (intervalFibration_pr₁₃ a b).e v = fibreEmb₁₃ a b v :=
  rfl

/-- **The fibres of `pr₁₃` are nonempty for `0 ≤ a`, `0 ≤ b`**: over `(x, z)` with
`dist x z ≤ a + b`, `max (x - a) (z - b) ≤ min (x + a) (z + b)`. -/
lemma lo_le_hi_pr₁₃ {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (v : D (a + b)) :
    (intervalFibration_pr₁₃ a b).lo v ≤ (intervalFibration_pr₁₃ a b).hi v := by
  change max (v.1.1 - a) (v.1.2 - b) ≤ min (v.1.1 + a) (v.1.2 + b)
  obtain ⟨h₁, h₂⟩ := le_of_dist_le (show dist v.1.1 v.1.2 ≤ a + b from v.2)
  exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith))

end fibration

variable (k : Type) [Ring k] [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat.{0} k))]

section unit

variable [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]

/-- **The derived unit of `pr₁₃` is an isomorphism** for `0 ≤ a`, `0 ≤ b`:
`R(pr₁₃)_* pr₁₃⁻¹ N ≅ N` for `N ∈ D⁺(Sh(D (a + b)))`, since the fibres of `pr₁₃` are nonempty
compact intervals (`lo_le_hi_pr₁₃`, `IntervalFibration.isIso_derivedUnit`). -/
theorem isIso_derivedUnit_pr₁₃ {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsIso (derivedUnit k (pr₁₃ a b)) :=
  (intervalFibration_pr₁₃ a b).isIso_derivedUnit k (lo_le_hi_pr₁₃ ha hb)

end unit

variable [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]

/-- **Restriction along `pr₁₃`.** `corrRestr k (pr₁₃ a b) (p (a + b)) (q (a + b))`, the derived unit
of `pr₁₃` followed by composition isomorphisms, `T_{a+b} ⟶ (pr₁₂ ≫ p a)⁻¹ ⋙ R(pr₂₃ ≫ q b)_*`. Its
target is written with `pr₁₂ ≫ p a = pr₁₃ ≫ p (a + b)` and `pr₂₃ ≫ q b = pr₁₃ ≫ q (a + b)`
(`pr₁₃_p`, `pr₁₃_q`, definitional), the form in which it meets the base change of the central
square. -/
def TCompRestr (a b : ℝ) :
    T k (a + b) ⟶ pullbackPlus k (pr₁₂ a b ≫ p a) ⋙ pushforwardPlus k (pr₂₃ a b ≫ q b) :=
  corrRestr k (pr₁₃ a b) (p (a + b)) (q (a + b))

/-- `TCompRestr` is `corrRestr` along `pr₁₃`. -/
lemma TCompRestr_eq (a b : ℝ) :
    TCompRestr k a b = corrRestr k (pr₁₃ a b) (p (a + b)) (q (a + b)) := rfl

/-- The components of `TCompRestr`: `R(q (a + b))_*` of the derived unit of `pr₁₃`, then
`R(pr₁₃)_* ⋙ R(q (a + b))_* ≅ R(pr₁₃ ≫ q (a + b))_*`, then `R(pr₁₃ ≫ q (a + b))_*` of
`pr₁₃⁻¹ (p (a + b))⁻¹ ≅ (pr₁₃ ≫ p (a + b))⁻¹`. -/
lemma TCompRestr_app (a b : ℝ) (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (TCompRestr k a b).app M =
      (pushforwardPlus k (q (a + b))).map
          ((derivedUnit k (pr₁₃ a b)).app ((pullbackPlus k (p (a + b))).obj M)) ≫
        (pushforwardPlusCompIso k (pr₁₃ a b) (q (a + b))).inv.app
          ((pullbackPlus k (pr₁₃ a b)).obj ((pullbackPlus k (p (a + b))).obj M)) ≫
        (pushforwardPlus k (pr₁₃ a b ≫ q (a + b))).map
          ((pullbackPlusCompIso k (pr₁₃ a b) (p (a + b))).hom.app M) :=
  corrRestr_app k (pr₁₃ a b) (p (a + b)) (q (a + b)) M

variable [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]

/-- **Base change on the central square.** The base-change morphism of
`pr₁₂ ≫ q a = pr₂₃ ≫ p b`, `R(q a)_* ⋙ (p b)⁻¹ ⟶ pr₁₂⁻¹ ⋙ R(pr₂₃)_*`, is an isomorphism, for all
`a b : ℝ`: `pr₁₂` carries the fibre `x ↦ (x, y, z)` of `pr₂₃` at `(y, z)` onto the fibre
`fibreEmb a y` of `q a` at `p b (y, z) = y` (the fibrewise criterion). -/
instance isIso_baseChange_pr₁₂_q (a b : ℝ) : IsIso (baseChange k (pr₁₂_q a b)) :=
  isIso_baseChange_of_isFibreParam k (pr₁₂_q a b) (fibreCoordinate_q a) (intervalFibration_pr₂₃ a b)
    fun v => isFibreParam_fibreEmb a (p b v)

/-- `TCompRestr` is invertible for `0 ≤ a`, `0 ≤ b` (`isIso_derivedUnit_pr₁₃`). -/
theorem isIso_TCompRestr {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : IsIso (TCompRestr k a b) :=
  haveI := isIso_derivedUnit_pr₁₃ k ha hb
  isIso_corrRestr_of_isIso_derivedUnit k (pr₁₃ a b) (p (a + b)) (q (a + b))

/-- **The composition isomorphism of the band functors** `T_a ⋙ T_b ≅ T_{a + b}` for `0 ≤ a`,
`0 ≤ b`, that is `R(q_b)_* p_b⁻¹ R(q_a)_* p_a⁻¹ F ≅ R(q_{a+b})_* p_{a+b}⁻¹ F` naturally in
`F ∈ D⁺(Sh ℝ)`. It is the composite of

* `R(q b)_*` of the base change of the central square (`isIso_baseChange_pr₁₂_q`),
* `R(pr₂₃)_* ⋙ R(q b)_* ≅ R(pr₂₃ ≫ q b)_*` (`pushforwardPlusCompIso`) and
  `(p a)⁻¹ ⋙ pr₁₂⁻¹ ≅ (pr₁₂ ≫ p a)⁻¹` (`pullbackPlusCompIso`), and
* the inverse of `TCompRestr k a b`, the restriction along `pr₁₃`, invertible because the
  derived unit of `pr₁₃` is (`isIso_TCompRestr`). -/
def TComp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : T k a ⋙ T k b ≅ T k (a + b) :=
  haveI := isIso_TCompRestr k ha hb
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pullbackPlus k (p a)) (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (pullbackPlus k (p a))
      (Functor.isoWhiskerRight (asIso (baseChange k (pr₁₂_q a b))) (pushforwardPlus k (q b))) ≪≫
    Functor.isoWhiskerLeft (pullbackPlus k (p a)) (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (pullbackPlus k (p a) ⋙ pullbackPlus k (pr₁₂ a b))
      (pushforwardPlusCompIso k (pr₂₃ a b) (q b)).symm ≪≫
    Functor.isoWhiskerRight (pullbackPlusCompIso k (pr₁₂ a b) (p a))
      (pushforwardPlus k (pr₂₃ a b ≫ q b)) ≪≫
    (asIso (TCompRestr k a b)).symm

/-- **The components of `TComp`, forwards.** At `M`, the composition isomorphism followed by the
restriction `TCompRestr` along `pr₁₃` is `R(q b)_*` of the base change of the central square, then
`R(pr₂₃)_* ⋙ R(q b)_* ≅ R(pr₂₃ ≫ q b)_*`, then `R(pr₂₃ ≫ q b)_*` of
`pr₁₂⁻¹ (p a)⁻¹ ≅ (pr₁₂ ≫ p a)⁻¹`. -/
lemma TComp_hom_app_TCompRestr {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (TComp k ha hb).hom.app M ≫ (TCompRestr k a b).app M =
      (pushforwardPlus k (q b)).map
          ((baseChange k (pr₁₂_q a b)).app ((pullbackPlus k (p a)).obj M)) ≫
        (pushforwardPlusCompIso k (pr₂₃ a b) (q b)).inv.app
          ((pullbackPlus k (pr₁₂ a b)).obj ((pullbackPlus k (p a)).obj M)) ≫
        (pushforwardPlus k (pr₂₃ a b ≫ q b)).map
          ((pullbackPlusCompIso k (pr₁₂ a b) (p a)).hom.app M) := by
  simp [TComp]

/-- **The components of `TComp`, backwards.** At `M`, the inverse of the composition isomorphism
is the restriction `TCompRestr` along `pr₁₃` (the derived unit of `pr₁₃` with composition
isomorphisms, `TCompRestr_app`), then `R(pr₂₃ ≫ q b)_*` of `(pr₁₂ ≫ p a)⁻¹ ≅ pr₁₂⁻¹ (p a)⁻¹`, then
`R(pr₂₃ ≫ q b)_* ⟶ R(pr₂₃)_* ⋙ R(q b)_*` (`pushforwardPlusComp`), then the inverse of `R(q b)_*` of
the base change of the central square. -/
lemma TComp_inv_app {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (TComp k ha hb).inv.app M =
      (TCompRestr k a b).app M ≫
        (pushforwardPlus k (pr₂₃ a b ≫ q b)).map
          ((pullbackPlusCompIso k (pr₁₂ a b) (p a)).inv.app M) ≫
        (pushforwardPlusComp k (pr₂₃ a b) (q b)).app
          ((pullbackPlus k (pr₁₂ a b)).obj ((pullbackPlus k (p a)).obj M)) ≫
        inv ((pushforwardPlus k (q b)).map
          ((baseChange k (pr₁₂_q a b)).app ((pullbackPlus k (p a)).obj M))) := by
  simp [TComp]

end TDA.Sheaf.BandConvolution
