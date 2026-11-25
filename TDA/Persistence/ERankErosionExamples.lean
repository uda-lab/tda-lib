import TDA.Persistence.ERankErosion
import TDA.Persistence.StructureMapERankExamples
import TDA.Persistence.StrictRankErosionExamples

/-!
# Extended-rank erosion: fixtures

The ephemeral module has an infinite-dimensional fiber at every grade and zero structure
maps between distinct grades. Against zero, its extended-rank erosion fails at radius `0`,
on the diagonal, and holds at every positive radius when there is a coordinate, so the
extended distance is `0` and is not attained. With no coordinate it fails at every radius,
and the extended distance is `⊤`. The infinite constant module against zero has extended
distance `⊤`, while the `ℕ`-valued distance is `0` in both cases. On the pointwise
finite-dimensional one-dimensional constant module and closed box the two distances agree, the
latter with the finite value `c`. The module `split`, with fiber `ℚ × (ℕ →₀ ℚ)` and the
idempotent `inl ∘ fst` between distinct grades, satisfies extended-rank erosion against the
one-dimensional constant module at every positive radius while `RankErosion` fails. Conversely
the ephemeral module satisfies `RankErosion` against zero at radius `0`, where its extended-rank
erosion fails. So neither predicate implies the other without finite dimensionality.
-/

set_option autoImplicit false

namespace TDA.Persistence.ERankErosionExamples

open CategoryTheory TDA.Persistence
open TDA.Persistence.StructureMapERankExamples (infinite line)
open scoped ZeroObject NNReal ENNReal

variable {n : ℕ}

/-- The module with fiber `V` at every grade, the identity on the diagonal and a fixed
idempotent `e` between distinct grades. -/
noncomputable def idempotentModule (V : ModuleCat.{0} ℚ) (e : V ⟶ V) (he : e ≫ e = e) :
    PModule.{0,0,0} ℚ (Fin n → ℝ) where
  obj _ := V
  map {a b} _ := by classical exact if a = b then 𝟙 V else e
  map_id a := by simp
  map_comp {a b c} f g := by
    classical
    have hab : a ≤ b := leOfHom f
    have hbc : b ≤ c := leOfHom g
    by_cases h₁ : a = b
    · subst h₁
      simp
    · have h₂ : a ≠ c := fun h => h₁ (le_antisymm hab (h ▸ hbc))
      by_cases h₃ : b = c
      · subst h₃
        simp [h₁]
      · simp [h₁, h₂, h₃, he]

/-- Off the diagonal the structure map of `idempotentModule V e he` is `e`. -/
theorem structureMapLinear_idempotentModule_of_ne (V : ModuleCat.{0} ℚ) (e : V ⟶ V)
    (he : e ≫ e = e) {a b : Fin n → ℝ} (hab : a ≤ b) (hne : a ≠ b) :
    structureMapLinear (idempotentModule V e he) hab = e.hom := by
  classical
  change (if a = b then 𝟙 V else e : V ⟶ V).hom = e.hom
  simp [hne]

/-- The ephemeral module with fiber `V` at every grade: identities on the diagonal and zero
structure maps between distinct grades. -/
noncomputable abbrev ephemeral (V : ModuleCat.{0} ℚ) : PModule.{0,0,0} ℚ (Fin n → ℝ) :=
  idempotentModule V 0 (by simp)

/-- Between distinct grades the ephemeral module has extended rank `0`. -/
theorem eRankOfStructureMap_ephemeral_of_ne (V : ModuleCat.{0} ℚ) {a b : Fin n → ℝ}
    (hab : a ≤ b) (hne : a ≠ b) :
    eRankOfStructureMap (ephemeral V) hab = 0 := by
  have h0 : structureMapLinear (ephemeral V) hab = 0 :=
    (structureMapLinear_idempotentModule_of_ne _ _ _ hab hne).trans ModuleCat.hom_zero
  rw [eRankOfStructureMap_eq_toENat_rank, h0, LinearMap.range_zero, rank_bot, map_zero]

/-- On the diagonal its extended rank is the extended dimension of `V`. -/
theorem eRankOfStructureMap_ephemeral_self (V : ModuleCat.{0} ℚ) (a : Fin n → ℝ) :
    eRankOfStructureMap (ephemeral V) (le_refl a) = (Module.rank ℚ V).toENat :=
  eRankOfStructureMap_self _ a

/-- The countably-infinite-dimensional ephemeral module. -/
noncomputable abbrev ephemeralInfinite : PModule.{0,0,0} ℚ (Fin n → ℝ) :=
  ephemeral (ModuleCat.of ℚ (ℕ →₀ ℚ))

/-- The countably-infinite-dimensional ephemeral module has extended rank `⊤` on the
diagonal. -/
theorem eRank_ephemeralInfinite_self (a : Fin n → ℝ) :
    eRankOfStructureMap (ephemeralInfinite (n := n)) (le_refl a) = ⊤ := by
  rw [eRankOfStructureMap_ephemeral_self]
  change (Module.rank ℚ (ℕ →₀ ℚ)).toENat = ⊤
  simp

/-- Radius `0` fails on the diagonal, for every number of parameters. -/
theorem ephemeralInfinite_not_eRankErosion_zero :
    ¬ ERankErosion 0 (ephemeralInfinite (n := n)) 0 := by
  intro h
  have h₀ := (eRankErosion_zero_iff.mp h) 0 0 le_rfl
  rw [eRank_ephemeralInfinite_self, eRankOfStructureMap_zero] at h₀
  exact ENat.top_ne_zero h₀

/-- At a positive radius, with at least one coordinate, the widened pair of every weak pair
consists of distinct grades. -/
private theorem erosionLower_ne_erosionUpper_of_pos [NeZero n] {ε : ℝ≥0} (hε : 0 < ε)
    {a b : Fin n → ℝ} (hab : a ≤ b) : erosionLower ε a ≠ erosionUpper ε b := by
  intro h
  have h0 := congrFun h 0
  have := hab 0
  change a 0 - (ε : ℝ) = b 0 + (ε : ℝ) at h0
  have hε' : (0 : ℝ) < ε := hε
  linarith

/-- At a positive radius, with at least one coordinate, every widened pair is a pair of
distinct grades, so erosion against zero holds. -/
theorem ephemeralInfinite_eRankErosion [NeZero n] {ε : ℝ≥0} (hε : 0 < ε) :
    ERankErosion ε (ephemeralInfinite (n := n)) 0 := by
  constructor
  · intro a b hab
    rw [eRankOfStructureMap_ephemeral_of_ne _ _ (erosionLower_ne_erosionUpper_of_pos hε hab)]
    exact zero_le
  · intro a b hab
    rw [eRankOfStructureMap_zero]
    exact zero_le

/-- With at least one coordinate the extended distance from zero is `0`, but it is not
attained. -/
theorem ephemeralInfinite_eRankErosionDistance [NeZero n] :
    eRankErosionDistance (ephemeralInfinite (n := n)) 0 = 0 ∧
      ¬ ERankErosion 0 (ephemeralInfinite (n := n)) 0 := by
  refine ⟨?_, ephemeralInfinite_not_eRankErosion_zero⟩
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  exact eRankErosionDistance_le_of_erosion (ephemeralInfinite_eRankErosion hε)

/-- With no coordinate every widened pair is the diagonal, so erosion against zero fails at
every radius and the extended distance is `⊤`. -/
theorem ephemeralInfinite_eRankErosionDistance_fin_zero :
    eRankErosionDistance (ephemeralInfinite (n := 0)) 0 = ⊤ := by
  rw [eRankErosionDistance_eq_top_iff]
  intro ε h
  have h₀ := h.1 0 0 le_rfl
  have hd : erosionLower ε (0 : Fin 0 → ℝ) = erosionUpper ε 0 := Subsingleton.elim _ _
  have hdiag : eRankOfStructureMap (ephemeralInfinite (n := 0)) (erosionWide_le ε
      (le_refl (0 : Fin 0 → ℝ))) = ⊤ := by
    rw [← eRank_ephemeralInfinite_self (erosionUpper ε (0 : Fin 0 → ℝ))]
    congr 1
  rw [hdiag, eRankOfStructureMap_zero] at h₀
  exact ENat.top_ne_zero (le_antisymm h₀ zero_le)

/-- The `ℕ`-valued ranks of the ephemeral module are all `0`, so its `ℕ`-valued erosion
distance from zero is `0` for every number of parameters, attained at radius `0`. -/
theorem ephemeralInfinite_rankErosion_zero :
    RankErosion 0 (ephemeralInfinite (n := n)) 0 := by
  refine rankErosion_zero_iff.mpr fun a b hab => ?_
  rw [rankOfStructureMap_zero, rankOfStructureMap_eq_toNat_eRankOfStructureMap]
  by_cases h : a = b
  · subst h
    rw [eRank_ephemeralInfinite_self]
    rfl
  · rw [eRankOfStructureMap_ephemeral_of_ne _ _ h]
    rfl

/-- The infinite constant module against zero: extended-rank erosion fails at every radius,
so the extended distance is `⊤`, while the `ℕ`-valued distance is `0`. -/
theorem infinite_vs_zero_distance :
    eRankErosionDistance infinite (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)) = ⊤ ∧
      rankErosionDistance infinite (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)) = 0 := by
  constructor
  · rw [eRankErosionDistance_eq_top_iff]
    intro ε h
    have h₀ := h.1 0 0 le_rfl
    rw [StructureMapERankExamples.eRank_infinite, eRankOfStructureMap_zero] at h₀
    exact ENat.top_ne_zero (le_antisymm h₀ zero_le)
  · exact nonpos_iff_eq_zero.1 (by simpa using (rankErosionDistance_le_of_erosion
      StructureMapERankExamples.rankErosion_zero_infinite))

/-- The fibers of the one-dimensional constant module are finite-dimensional. -/
private instance line_finiteDimensional (p : Fin 1 → ℝ) : FiniteDimensional ℚ (line.obj p) :=
  inferInstanceAs (FiniteDimensional ℚ ℚ)

/-- On the pointwise finite-dimensional line the two distances from zero agree, and both
are `⊤`. -/
theorem line_vs_zero_distance :
    eRankErosionDistance line (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)) =
        rankErosionDistance line 0 ∧
      eRankErosionDistance line (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)) = ⊤ := by
  have := StrictRankErosionExamples.zero_finiteDimensional (n := 1)
  refine ⟨eRankErosionDistance_eq_rankErosionDistance, ?_⟩
  rw [eRankErosionDistance_eq_top_iff]
  intro ε h
  have h₀ := h.1 0 0 le_rfl
  rw [(StructureMapERankExamples.eRank_line _).1, eRankOfStructureMap_zero] at h₀
  exact one_ne_zero (le_antisymm h₀ zero_le)

/-- On the pointwise finite-dimensional closed box `[0, 2c]ⁿ`, with at least one coordinate,
the extended distance from zero is the finite value `c` of the `ℕ`-valued distance. -/
theorem closedBox_eRankErosionDistance [NeZero n] (c : ℝ≥0) :
    eRankErosionDistance (StrictRankErosionExamples.closedBox (n := n) c) 0 = c := by
  have := StrictRankErosionExamples.zero_finiteDimensional (n := n)
  rw [eRankErosionDistance_eq_rankErosionDistance,
    StrictRankErosionExamples.closedBox_rankErosionDistance]

/-- The split fiber `ℚ × (ℕ →₀ ℚ)`. -/
noncomputable abbrev splitFiber : ModuleCat.{0} ℚ := ModuleCat.of ℚ (ℚ × (ℕ →₀ ℚ))

/-- The idempotent `inl ∘ fst` of the split fiber, of rank one. -/
noncomputable def splitIdempotent : splitFiber ⟶ splitFiber :=
  ModuleCat.ofHom ((LinearMap.inl ℚ ℚ (ℕ →₀ ℚ)).comp (LinearMap.fst ℚ ℚ (ℕ →₀ ℚ)))

/-- `inl ∘ fst` is idempotent. -/
theorem splitIdempotent_idem : splitIdempotent ≫ splitIdempotent = splitIdempotent :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The one-parameter module with fiber `ℚ × (ℕ →₀ ℚ)`, the identity on the diagonal and
`inl ∘ fst` between distinct grades: extended rank `⊤` on the diagonal and `1` off it. -/
noncomputable abbrev split : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  idempotentModule splitFiber splitIdempotent splitIdempotent_idem

/-- Between distinct grades `split` has extended rank `1`. -/
theorem eRank_split_of_ne {a b : Fin 1 → ℝ} (hab : a ≤ b) (hne : a ≠ b) :
    eRankOfStructureMap split hab = 1 := by
  rw [eRankOfStructureMap_eq_toENat_rank,
    structureMapLinear_idempotentModule_of_ne _ _ _ hab hne]
  change (Module.rank ℚ (LinearMap.range
    ((LinearMap.inl ℚ ℚ (ℕ →₀ ℚ)).comp (LinearMap.fst ℚ ℚ (ℕ →₀ ℚ))))).toENat = 1
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr LinearMap.fst_surjective,
    Submodule.map_top, rank_range_of_injective _ LinearMap.inl_injective]
  simp

/-- On the diagonal `split` has extended rank `⊤`. -/
theorem eRank_split_self (a : Fin 1 → ℝ) :
    eRankOfStructureMap split (le_refl a) = ⊤ := by
  rw [eRankOfStructureMap_self]
  change (Module.rank ℚ (ℚ × (ℕ →₀ ℚ))).toENat = ⊤
  simp

/-- Without finite dimensionality extended-rank erosion does not imply `RankErosion`: at every
positive radius `split` and `line` satisfy extended-rank erosion, while `RankErosion` fails
because the `ℕ`-valued rank of `split` on the diagonal is `0`. -/
theorem split_line_eRankErosion_not_rankErosion {ε : ℝ≥0} (hε : 0 < ε) :
    ERankErosion ε split line ∧ ¬ RankErosion ε split line := by
  have hsplit_ge {a b : Fin 1 → ℝ} (hab : a ≤ b) : 1 ≤ eRankOfStructureMap split hab := by
    by_cases h : a = b
    · subst h
      rw [eRank_split_self]
      exact le_top
    · rw [eRank_split_of_ne hab h]
  refine ⟨⟨fun a b hab => ?_, fun a b hab => ?_⟩, fun h => ?_⟩
  · rw [eRank_split_of_ne _ (erosionLower_ne_erosionUpper_of_pos hε hab),
      (StructureMapERankExamples.eRank_line hab).1]
  · rw [(StructureMapERankExamples.eRank_line _).1]
    exact hsplit_ge hab
  · have h₀ := h.2 0 0 le_rfl
    rw [(StructureMapERankExamples.eRank_line _).2,
      rankOfStructureMap_eq_toNat_eRankOfStructureMap, eRank_split_self] at h₀
    exact absurd h₀ (by decide)

/-- Extended-rank erosion of the infinite module with itself holds at radius `0` without
finite dimensionality. -/
example : ERankErosion 0 infinite infinite := ERankErosion.refl 0 infinite

/-- The extended distance is bounded by the interleaving distance without finite
dimensionality. -/
example : eRankErosionDistance infinite (ephemeralInfinite (n := 1)) ≤
    coordinateInterleavingDistance infinite ephemeralInfinite :=
  eRankErosionDistance_le_coordinateInterleavingDistance _ _

end TDA.Persistence.ERankErosionExamples
