import TDA.Persistence.ERankQTame

/-!
# Coordinatewise q-tameness of real-coordinate persistence modules

A module on `Fin n → ℝ` is coordinatewise q-tame when every structure map `M a → M b` with
`a i < b i` in every coordinate has finite-dimensional image. This is strictness in every
coordinate, not the strict product order `a < b` (`a ≤ b`, `a ≠ b`) used by
`StrictRankErosion`: an axis-parallel pair such as the one from the origin to the first unit
vector is product-strict but not coordinatewise strict, and coordinatewise q-tameness asks
nothing of it.

Equivalently every positive diagonal shift `M a → M (translation δ a)`, `δ > 0`, has
finite-dimensional image, or finite extended rank. For one coordinate the notion is
`PModule.QTame` through `CoordinateRealBridge.fromReal`. With no coordinate the
coordinatewise-strict condition is vacuous, so the only pair is the diagonal one and the
notion is pointwise finite dimensionality.

A coordinate `ε`-interleaving bounds the extended rank of the doubled-shift structure map by
the extended dimension of the middle fibre of the other module. If the other module is
coordinatewise q-tame, every structure map whose gap exceeds `2ε` in every coordinate has
finite extended rank. The gap must be strict: with a gap of exactly `2ε` the factor through `N`
need not be coordinatewise strict.

The helpers `CoordinateShift.le_translation` and `CoordinateShift.exists_pos_translation_le`
live in this module, not in `TDA.Persistence.CoordinateShift`.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory CoordinateShift CoordinateRealBridge
open scoped TDA.Persistence NNReal ENNReal

/-- Every grade lies below its diagonal translate. -/
theorem CoordinateShift.le_translation {n : ℕ} (δ : ℝ≥0) (a : Fin n → ℝ) :
    a ≤ translation δ a :=
  fun _ => le_add_of_nonneg_right δ.coe_nonneg

/-- Between two grades that are strictly ordered in every coordinate there is a positive
diagonal translate of the lower grade below the upper one. -/
theorem CoordinateShift.exists_pos_translation_le {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) : ∃ δ : ℝ≥0, 0 < δ ∧ translation δ a ≤ b := by
  have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i, a i + δ < b i := by
    refine Filter.eventually_all.2 fun i => nhdsWithin_le_nhds ?_
    have hc : Continuous fun δ : ℝ => a i + δ := continuous_const.add continuous_id
    exact (hc.tendsto 0).eventually (gt_mem_nhds (by simpa using hab i))
  obtain ⟨δ, hδ, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨⟨δ, le_of_lt hδpos⟩, hδpos, fun i => (hδ i).le⟩

variable {k : Type u} [Field k] {n : ℕ}

namespace PModule

/-- Coordinatewise q-tameness: every structure map between grades that are strictly ordered
in every coordinate has finite-dimensional image. The module is named `CoordinateQTame`, after
`CoordinateInterleaving` and `CoordinateRealBridge`, while the predicate keeps the shorter name
`CoordQTame`; the difference is deliberate. -/
def CoordQTame (M : PModule.{u,0,w} k (Fin n → ℝ)) : Prop :=
  ∀ (a b : Fin n → ℝ) (hab : ∀ i, a i < b i),
    FiniteDimensional k (LinearMap.range (structureMapLinear M (fun i => (hab i).le)))

/-- Coordinatewise q-tameness is finite extended rank on every coordinatewise-strict pair. -/
theorem coordQTame_iff_eRankOfStructureMap_ne_top (M : PModule.{u,0,w} k (Fin n → ℝ)) :
    M.CoordQTame ↔ ∀ (a b : Fin n → ℝ) (hab : ∀ i, a i < b i),
      eRankOfStructureMap M (fun i => (hab i).le) ≠ ⊤ := by
  simp only [CoordQTame, eRankOfStructureMap_ne_top_iff]

/-- Coordinatewise q-tameness is finite extended rank of every positive diagonal shift. -/
theorem coordQTame_iff_eRankOfStructureMap_translation_ne_top
    (M : PModule.{u,0,w} k (Fin n → ℝ)) :
    M.CoordQTame ↔ ∀ (δ : ℝ≥0), 0 < δ → ∀ a : Fin n → ℝ,
      eRankOfStructureMap M (le_translation δ a) ≠ ⊤ := by
  rw [coordQTame_iff_eRankOfStructureMap_ne_top]
  constructor
  · intro h δ hδ a
    exact h a (translation δ a) fun i => lt_add_of_pos_right (a i) hδ
  · intro h a b hab
    obtain ⟨δ, hδ, hle⟩ := exists_pos_translation_le hab
    exact ne_top_of_le_ne_top (h δ hδ a)
      (eRankOfStructureMap_trans_le_right M (le_translation δ a) hle)

/-- Coordinatewise q-tameness is finite-dimensional image of every positive diagonal shift. -/
theorem coordQTame_iff_finiteDimensional_translation (M : PModule.{u,0,w} k (Fin n → ℝ)) :
    M.CoordQTame ↔ ∀ (δ : ℝ≥0), 0 < δ → ∀ a : Fin n → ℝ,
      FiniteDimensional k (LinearMap.range (structureMapLinear M (le_translation δ a))) := by
  simp only [coordQTame_iff_eRankOfStructureMap_translation_ne_top,
    eRankOfStructureMap_ne_top_iff]

/-- Every coordinatewise-strict structure map of a coordinatewise q-tame module has finite
extended rank. -/
theorem CoordQTame.eRankOfStructureMap_ne_top {M : PModule.{u,0,w} k (Fin n → ℝ)}
    (hM : M.CoordQTame) {a b : Fin n → ℝ} (hab : a ≤ b) (hlt : ∀ i, a i < b i) :
    eRankOfStructureMap M hab ≠ ⊤ :=
  (coordQTame_iff_eRankOfStructureMap_ne_top M).mp hM a b hlt

/-- Every positive diagonal shift of a coordinatewise q-tame module has finite extended
rank. -/
theorem CoordQTame.eRankOfStructureMap_translation_ne_top
    {M : PModule.{u,0,w} k (Fin n → ℝ)} (hM : M.CoordQTame) {δ : ℝ≥0} (hδ : 0 < δ)
    (a : Fin n → ℝ) : eRankOfStructureMap M (le_translation δ a) ≠ ⊤ :=
  (coordQTame_iff_eRankOfStructureMap_translation_ne_top M).mp hM δ hδ a

/-- Pointwise finite-dimensional modules are coordinatewise q-tame. -/
theorem coordQTame_of_finiteDimensional (M : PModule.{u,0,w} k (Fin n → ℝ))
    (hM : ∀ a, FiniteDimensional k (M.obj a)) : M.CoordQTame := by
  intro a b _
  have := hM a
  exact LinearMap.finiteDimensional_range _

/-- With one coordinate, coordinatewise q-tameness of `fromReal M` is q-tameness of `M`. -/
theorem qTame_iff_coordQTame_fromReal (M : PModule.{u,0,w} k ℝ) :
    M.QTame ↔ (fromReal M).CoordQTame := by
  constructor
  · intro h a b hab
    exact h (a 0) (b 0) (hab 0)
  · intro h a b hab
    exact h (diagonal a) (diagonal b) fun _ => hab

/-- With no coordinate, coordinatewise q-tameness is pointwise finite dimensionality: the
coordinatewise-strict condition is vacuous, so the diagonal pair is tested. -/
theorem coordQTame_fin_zero_iff (M : PModule.{u,0,w} k (Fin 0 → ℝ)) :
    M.CoordQTame ↔ ∀ a, FiniteDimensional k (M.obj a) := by
  refine ⟨fun h a => ?_, coordQTame_of_finiteDimensional M⟩
  have hfin := h.eRankOfStructureMap_ne_top (le_refl a) fun i => i.elim0
  rw [eRankOfStructureMap_self, ne_eq, Cardinal.toENat_eq_top, not_le] at hfin
  exact Module.rank_lt_aleph0_iff.mp hfin

end PModule

namespace CoordinateInterleaving

variable {ε : ℝ≥0}

/-- The doubled-shift structure map of `M` factors through the middle fibre of `N`, so its
extended rank is at most the extended dimension of that fibre. -/
theorem eRankOfStructureMap_le_toENat_rank {M N : PModule.{u,0,w} k (Fin n → ℝ)}
    (i : CoordinateInterleaving ε M N) (a : Fin n → ℝ) :
    eRankOfStructureMap M (twice_le ε a) ≤
      (Module.rank k (N.obj (translation ε a))).toENat := by
  let f : M.obj a →ₗ[k] N.obj (translation ε a) := (i.φ.app a).hom
  let g : N.obj (translation ε a) →ₗ[k] M.obj (translation ε (translation ε a)) :=
    (i.ψ.app (translation ε a)).hom
  have hfactor := congrArg (fun φ => (LinearMap.rank φ).toENat)
    (congrArg ModuleCat.Hom.hom (i.φ_ψ_structureMap a)).symm
  refine (le_of_eq hfactor).trans ?_
  change (g.comp f).rank.toENat ≤ _
  exact Cardinal.toENat.monotone'
    ((LinearMap.rank_comp_le_left f g).trans (LinearMap.rank_le_domain g))

/-- The local finite-image bound: with a finite-dimensional middle fibre the doubled-shift
structure map has finite extended rank. -/
theorem eRankOfStructureMap_ne_top {M N : PModule.{u,0,w} k (Fin n → ℝ)}
    (i : CoordinateInterleaving ε M N) (a : Fin n → ℝ)
    [FiniteDimensional k (N.obj (translation ε a))] :
    eRankOfStructureMap M (twice_le ε a) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (i.eRankOfStructureMap_le_toENat_rank a)
  rw [← Module.finrank_eq_rank, Cardinal.toENat_nat]
  exact ENat.natCast_ne_top _

/-- A structure map of `M` ending one shift beyond `y` has extended rank at most that of the
structure map of `N` from the shifted start to `y`. -/
theorem eRankOfStructureMap_le_of_translation_le {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (i : CoordinateInterleaving ε M N) {x y : Fin n → ℝ} (h : translation ε x ≤ y)
    (hxy : x ≤ translation ε y) :
    eRankOfStructureMap M hxy ≤ eRankOfStructureMap N h := by
  have hfactorLinear := congrArg ModuleCat.Hom.hom (i.factor_structureMap h hxy)
  calc
    eRankOfStructureMap M hxy = (structureMap M hxy).hom.rank.toENat := rfl
    _ = (((i.ψ.app y).hom).comp
        ((structureMap N h).hom.comp (i.φ.app x).hom)).rank.toENat := by
      rw [hfactorLinear]
      rfl
    _ ≤ eRankOfStructureMap N h :=
      (Cardinal.toENat.monotone' (LinearMap.rank_comp_le_right _ _)).trans
        (Cardinal.toENat.monotone' (LinearMap.rank_comp_le_left _ _))

/-- If `N` is coordinatewise q-tame, every structure map of an `ε`-interleaved module `M`
whose gap exceeds `2ε` in every coordinate has finite extended rank. -/
theorem eRankOfStructureMap_ne_top_of_coordQTame {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (i : CoordinateInterleaving ε M N) (hN : N.CoordQTame) {a b : Fin n → ℝ} (hab : a ≤ b)
    (hgap : ∀ j, a j + 2 * (ε : ℝ) < b j) :
    eRankOfStructureMap M hab ≠ ⊤ := by
  let y : Fin n → ℝ := erosionLower ε b
  have hy : translation ε y = b := by
    funext j
    simp [y, erosionLower]
  have hlt : ∀ j, translation ε a j < y j := by
    intro j
    simp only [translation_apply, y, erosionLower]
    linarith [hgap j]
  have h : translation ε a ≤ y := fun j => (hlt j).le
  have hxy : a ≤ translation ε y := hy ▸ hab
  have hN' := hN.eRankOfStructureMap_ne_top h hlt
  refine ne_top_of_le_ne_top hN' ?_
  calc
    eRankOfStructureMap M hab = eRankOfStructureMap M (hxy.trans (le_of_eq hy)) := rfl
    _ ≤ eRankOfStructureMap M hxy := eRankOfStructureMap_trans_le_right M hxy (le_of_eq hy)
    _ ≤ eRankOfStructureMap N h := i.eRankOfStructureMap_le_of_translation_le h hxy

end CoordinateInterleaving

end TDA.Persistence
