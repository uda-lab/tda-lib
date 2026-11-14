import TDA.Reeb.InterleavingDistance
import TDA.Reeb.IntervalComponents
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Translation of interval precosheaves

For `c : ℝ`, `translate c I = {y | y + c ∈ I}` is the open interval `I` moved by `-c`; it is
monotone in `I` and commutes with thickening, and `translate_ioo` gives its endpoints. The
orientation makes `f x + c ∈ I` and `f x ∈ translate c I` definitionally equal, so for a height
`f : C(X, ℝ)` the interval components of `f + c` are the precosheaf
`translatePre c (intervalComponents f) = translateFunctor c ⋙ intervalComponents f`
(`intervalComponents_add_const`).

For every precosheaf `F : OpenInterval ⥤ C` into an arbitrary category, `I ⊆ T_ε (I - c)` and
`I - c ⊆ T_ε I` whenever `|c| ≤ ε`, and the images of these inclusions under `F` form the
`‖c‖₊`-interleaving `translationInterleaving c F` of `F` with its translate.

More generally, an interval functor `Φ` with `T_ε (Φ I) ⊆ Φ (T_ε' I)` carries every
`ε`-interleaving of `F` and `G` to an `ε'`-interleaving of `Φ ⋙ F` and `Φ ⋙ G`
(`Interleaving.reindex`), and interval functors with the same values give isomorphic reindexed
precosheaves (`reindexIso`). Translation and scaling of precosheaves are instances.

For `Type`-valued precosheaves, a nonempty value `F(I)` and an empty value `G(T_ε I)` exclude
every `ε`-interleaving (`Interleaving.isEmpty_of_nonempty_of_isEmpty`). With the attained range
of `f` bounded below on a nonempty space, this obstruction at a short interval around the
infimum of the range gives the exact distance
`interleavingDistance (intervalComponents f) (intervalComponents (f + c)) = ‖c‖₊`
(`interleavingDistance_intervalComponents_add_const`). Without the lower bound the distance can
be `0`: translation by `1` is an automorphism of the identity height of `ℝ`.

These are library statements. De Silva–Munch–Patel's expansion `I^ε` (§4.1–4.2) is the
thickening used here; no numbered result of theirs states translation equivariance.
See `docs/math/reeb-graph-pl.md`.
-/

open Set CategoryTheory
open scoped NNReal ENNReal

universe v u w

namespace TDA.Reeb

namespace OpenInterval

/-- The interval `I - c = {y | y + c ∈ I}`. -/
def translate (c : ℝ) (I : OpenInterval) : OpenInterval :=
  ⟨(· + c) ⁻¹' (I : Set ℝ), I.isOpen.preimage (continuous_add_const c),
    I.ordConnected.preimage_mono fun _ _ h => add_le_add_left h c⟩

@[simp] theorem mem_translate {c x : ℝ} {I : OpenInterval} :
    x ∈ translate c I ↔ x + c ∈ I := Iff.rfl

@[simp] theorem coe_translate (c : ℝ) (I : OpenInterval) :
    (translate c I : Set ℝ) = (· + c) ⁻¹' (I : Set ℝ) := rfl

theorem translate_ioo (c p q : ℝ) : translate c (ioo p q) = ioo (p - c) (q - c) := by
  ext x
  change p < x + c ∧ x + c < q ↔ p - c < x ∧ x < q - c
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

@[simp] theorem translate_top (c : ℝ) : translate c ⊤ = ⊤ := rfl

@[simp] theorem translate_bot (c : ℝ) : translate c ⊥ = ⊥ := rfl

@[simp] theorem translate_zero (I : OpenInterval) : translate 0 I = I := by
  ext x; simp

theorem translate_translate (c d : ℝ) (I : OpenInterval) :
    translate c (translate d I) = translate (c + d) I := by
  ext x; simp [add_assoc]

theorem translate_monotone (c : ℝ) : Monotone (translate c) := fun _ _ h _ hx => h hx

theorem translate_thicken (c : ℝ) (ε : ℝ≥0) (I : OpenInterval) :
    translate c (thicken ε I) = thicken ε (translate c I) := by
  ext x
  simp only [mem_translate, mem_thicken]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y - c, by simpa using hy, by rwa [show x - (y - c) = x + c - y by ring]⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y + c, hy, by rwa [show x + c - (y + c) = x - y by ring]⟩

theorem le_translate_thicken {c : ℝ} {ε : ℝ≥0} (h : |c| ≤ ε) (I : OpenInterval) :
    I ≤ translate c (thicken ε I) := fun x hx =>
  mem_thicken.2 ⟨x, hx, by simpa using h⟩

theorem translate_le_thicken {c : ℝ} {ε : ℝ≥0} (h : |c| ≤ ε) (I : OpenInterval) :
    translate c I ≤ thicken ε I := fun x hx =>
  mem_thicken.2 ⟨x + c, hx, by simpa [abs_neg] using h⟩

/-- Translation as an endofunctor of the interval category. -/
def translateFunctor (c : ℝ) : OpenInterval ⥤ OpenInterval := (translate_monotone c).functor

@[simp] theorem translateFunctor_obj (c : ℝ) (I : OpenInterval) :
    (translateFunctor c).obj I = translate c I := rfl

end OpenInterval

open OpenInterval

/-! ### Reindexing along interval functors -/

section Reindex

variable {C : Type u} [Category.{v} C]

/-- Precosheaves reindexed along two interval functors with the same values are isomorphic, by
the images of the equalities of these values. -/
def reindexIso {Φ Ψ : OpenInterval ⥤ OpenInterval} (h : ∀ I, Φ.obj I = Ψ.obj I)
    (F : OpenInterval ⥤ C) : Φ ⋙ F ≅ Ψ ⋙ F :=
  NatIso.ofComponents (fun I => F.mapIso (eqToIso (h I))) fun _ => by
    dsimp
    interval_coherence

@[simp] theorem reindexIso_hom_app {Φ Ψ : OpenInterval ⥤ OpenInterval}
    (h : ∀ I, Φ.obj I = Ψ.obj I) (F : OpenInterval ⥤ C) (I : OpenInterval) :
    (reindexIso h F).hom.app I = F.map (eqToHom (h I)) := rfl

namespace Interleaving

variable {ε ε' : ℝ≥0} {F G : OpenInterval ⥤ C}

/-- Reindexing along an interval functor `Φ` with `T_ε (Φ I) ⊆ Φ (T_ε' I)` carries an
`ε`-interleaving of `F` and `G` to an `ε'`-interleaving of `Φ ⋙ F` and `Φ ⋙ G`, with
components `φ_(Φ I)` and `ψ_(Φ I)` followed by the images of these inclusions. -/
def reindex (Φ : OpenInterval ⥤ OpenInterval)
    (hΦ : ∀ I, thicken ε (Φ.obj I) ≤ Φ.obj (thicken ε' I)) (i : Interleaving ε F G) :
    Interleaving ε' (Φ ⋙ F) (Φ ⋙ G) :=
  ofApp
    { app := fun I => i.φ.app (Φ.obj I) ≫ G.map (homOfLE (hΦ I))
      naturality := fun I J f => by
        dsimp
        erw [reassoc_of% (i.φ.naturality (Φ.map f))]
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        congr 1
        interval_coherence }
    { app := fun I => i.ψ.app (Φ.obj I) ≫ F.map (homOfLE (hΦ I))
      naturality := fun I J f => by
        dsimp
        erw [reassoc_of% (i.ψ.naturality (Φ.map f))]
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        congr 1
        interval_coherence }
    (fun I => by
      dsimp
      rw [Category.assoc, i.φ_map_ψ_assoc]
      interval_coherence)
    (fun I => by
      dsimp
      rw [Category.assoc, i.ψ_map_φ_assoc]
      interval_coherence)

@[simp] theorem reindex_φ_app (Φ : OpenInterval ⥤ OpenInterval)
    (hΦ : ∀ I, thicken ε (Φ.obj I) ≤ Φ.obj (thicken ε' I)) (i : Interleaving ε F G)
    (I : OpenInterval) :
    (i.reindex Φ hΦ).φ.app I = i.φ.app (Φ.obj I) ≫ G.map (homOfLE (hΦ I)) := rfl

@[simp] theorem reindex_ψ_app (Φ : OpenInterval ⥤ OpenInterval)
    (hΦ : ∀ I, thicken ε (Φ.obj I) ≤ Φ.obj (thicken ε' I)) (i : Interleaving ε F G)
    (I : OpenInterval) :
    (i.reindex Φ hΦ).ψ.app I = i.ψ.app (Φ.obj I) ≫ F.map (homOfLE (hΦ I)) := rfl

end Interleaving

end Reindex

section Translation

variable {C : Type u} [Category.{v} C]

/-- The translate `I ↦ F (I - c)` of a precosheaf on the interval category. -/
def translatePre (c : ℝ) (F : OpenInterval ⥤ C) : OpenInterval ⥤ C :=
  translateFunctor c ⋙ F

@[simp] theorem translatePre_obj (c : ℝ) (F : OpenInterval ⥤ C) (I : OpenInterval) :
    (translatePre c F).obj I = F.obj (translate c I) := rfl

@[simp] theorem translatePre_map (c : ℝ) (F : OpenInterval ⥤ C) {I J : OpenInterval}
    (f : I ⟶ J) : (translatePre c F).map f = F.map ((translateFunctor c).map f) := rfl

/-- Translation by `0` is naturally isomorphic to the identity. -/
def translatePreZeroIso (F : OpenInterval ⥤ C) : translatePre 0 F ≅ F :=
  reindexIso (Ψ := 𝟭 _) translate_zero F

private theorem abs_le_nnnorm (c : ℝ) : |c| ≤ ((‖c‖₊ : ℝ≥0) : ℝ) := by
  rw [coe_nnnorm, Real.norm_eq_abs]

/-- `F` and its translate by `c` are `‖c‖₊`-interleaved by the images under `F` of
`I ⊆ T_|c| (I - c)` and `I - c ⊆ T_|c| I`. -/
def translationInterleaving (c : ℝ) (F : OpenInterval ⥤ C) :
    Interleaving ‖c‖₊ F (translatePre c F) :=
  Interleaving.ofApp
    { app := fun I => F.map (homOfLE (le_translate_thicken (abs_le_nnnorm c) I))
      naturality := fun _ _ _ => by dsimp; interval_coherence }
    { app := fun I => F.map (homOfLE (translate_le_thicken (abs_le_nnnorm c) I))
      naturality := fun _ _ _ => by dsimp; interval_coherence }
    (fun _ => by dsimp; interval_coherence) (fun _ => by dsimp; interval_coherence)

theorem interleavingDistance_translatePre_le (c : ℝ) (F : OpenInterval ⥤ C) :
    interleavingDistance F (translatePre c F) ≤ ‖c‖₊ :=
  (translationInterleaving c F).interleavingDistance_le

end Translation

section Obstruction

variable {F G : OpenInterval ⥤ Type w}

/-- A nonempty value `F(I)` and an empty value `G(T_ε I)` exclude every `ε`-interleaving. -/
theorem Interleaving.isEmpty_of_nonempty_of_isEmpty {ε : ℝ≥0} {I : OpenInterval}
    (hF : Nonempty (F.obj I)) (hG : IsEmpty (G.obj (thicken ε I))) :
    IsEmpty (Interleaving ε F G) :=
  ⟨fun i => hG.false (i.φ.app I hF.some)⟩

/-- If below `r` every parameter `ε` has an interval `I` with `F(I)` nonempty and `G(T_ε I)`
empty, the interleaving distance is at least `r`. -/
theorem le_interleavingDistance_of_forall_exists_isEmpty {r : ℝ≥0∞}
    (h : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r →
      ∃ I, Nonempty (F.obj I) ∧ IsEmpty (G.obj (thicken ε I))) :
    r ≤ interleavingDistance F G := by
  refine le_interleavingDistance_iff.2 fun ε ⟨i⟩ => le_of_not_gt fun hε => ?_
  obtain ⟨I, hF, hG⟩ := h ε hε
  exact (Interleaving.isEmpty_of_nonempty_of_isEmpty hF hG).false i

end Obstruction

section Height

variable {X : Type u} [TopologicalSpace X]

/-- The interval components of `f + c` are the translate by `c` of those of `f`. -/
theorem intervalComponents_add_const (f : C(X, ℝ)) (c : ℝ) :
    intervalComponents (f + ContinuousMap.const X c) = translatePre c (intervalComponents f) :=
  rfl

private theorem isEmpty_zerothHomotopy {Y : Type u} [TopologicalSpace Y] (hY : IsEmpty Y) :
    IsEmpty (ZerothHomotopy Y) :=
  ⟨fun p => by
    induction p using ZerothHomotopy.rec with
    | mk y => exact hY.false y⟩

/-- Lower bound for a positive translation. -/
private theorem coe_le_interleavingDistance_add_const [Nonempty X] (f : C(X, ℝ))
    (hf : BddBelow (range f)) {c : ℝ} (hc : 0 < c) :
    ((‖c‖₊ : ℝ≥0) : ℝ≥0∞) ≤ interleavingDistance (intervalComponents f)
      (intervalComponents (f + ContinuousMap.const X c)) := by
  refine le_interleavingDistance_of_forall_exists_isEmpty fun ε hε => ?_
  have hεc : (ε : ℝ) < c := by
    have := ENNReal.coe_lt_coe.1 hε
    rwa [← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_of_nonneg hc.le] at this
  set α := sInf (range f)
  set η := (c - ε) / 2
  have hη : 0 < η := by simp only [η]; linarith
  obtain ⟨_, ⟨x₀, rfl⟩, hx₀⟩ := Real.lt_sInf_add_pos (range_nonempty f) hη
  have hlow : ∀ x, α ≤ f x := fun x => csInf_le hf ⟨x, rfl⟩
  refine ⟨ioo (α - η) (α + η), ⟨ZerothHomotopy.mk ⟨x₀, ?_⟩⟩, isEmpty_zerothHomotopy ⟨?_⟩⟩
  · exact ⟨by linarith [hlow x₀], hx₀⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hxy⟩ := mem_thicken.1 hx
    have hy' : y < α + η := hy.2
    have hfx := hlow x
    have hle := (abs_le.1 hxy).2
    change f x + c - y ≤ ε at hle
    simp only [η] at hy'
    linarith

/-- For a height bounded below on a nonempty space, translation by `c` moves the interval
components by exactly `‖c‖₊`. -/
theorem interleavingDistance_intervalComponents_add_const [Nonempty X] (f : C(X, ℝ))
    (hf : BddBelow (range f)) (c : ℝ) :
    interleavingDistance (intervalComponents f)
      (intervalComponents (f + ContinuousMap.const X c)) = ‖c‖₊ := by
  refine le_antisymm ?_ ?_
  · rw [intervalComponents_add_const]
    exact interleavingDistance_translatePre_le c _
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hf' : BddBelow (range (f + ContinuousMap.const X c)) := by
      obtain ⟨m, hm⟩ := hf
      exact ⟨m + c, by rintro _ ⟨x, rfl⟩; simpa using hm ⟨x, rfl⟩⟩
    have hback : f + ContinuousMap.const X c + ContinuousMap.const X (-c) = f := by ext; simp
    have := coe_le_interleavingDistance_add_const (f + ContinuousMap.const X c) hf' (neg_pos.2 hc)
    rwa [hback, interleavingDistance_comm, nnnorm_neg] at this
  · simp
  · exact coe_le_interleavingDistance_add_const f hf hc

end Height

end TDA.Reeb
