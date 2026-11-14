import TDA.Persistence.RankErosion

/-!
# Interleaving stability of weak-pair rank erosion

The structure map from the lowered first grade to the raised second grade
factors through the unshifted structure map of the other module. The factorization
uses the actual interleaving maps and their naturality.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CoordinateShift
open scoped TDA.Persistence NNReal ENNReal

variable {k : Type u} [Field k] {n : ℕ}
variable {M N : PModule.{u,0,u} k (Fin n → ℝ)}

theorem translation_erosionLower (ε : ℝ≥0) (a : Fin n → ℝ) :
    translation ε (erosionLower ε a) = a := by
  funext i
  simp [erosionLower]

/-- A structure map ending one shift beyond `y` factors through `N(x+ε→y)`. -/
theorem CoordinateInterleaving.factor_structureMap {ε : ℝ≥0}
    (I : CoordinateInterleaving ε M N)
    {x y : Fin n → ℝ} (h : translation ε x ≤ y)
    (hxy : x ≤ translation ε y) :
    structureMap M hxy =
      I.φ.app x ≫ structureMap N h ≫ I.ψ.app y := by
  have hnat := I.ψ.naturality (homOfLE h)
  change structureMap N h ≫ I.ψ.app y =
    I.ψ.app (translation ε x) ≫
      structureMap M ((translation ε).monotone' h) at hnat
  have hcomp : structureMap M hxy =
      structureMap M (CoordinateInterleaving.twice_le ε x) ≫
        structureMap M ((translation ε).monotone' h) := by
    change M.map _ = M.map _ ≫ M.map _
    rw [← M.map_comp]
    congr 1
  have hfact : structureMap M hxy =
      I.φ.app x ≫ structureMap N h ≫ I.ψ.app y := by
    rw [hcomp, ← I.φ_ψ_structureMap]
    erw [Category.assoc, ← I.ψ.naturality]
    rfl
  exact hfact

/-- Rank domination from the actual interleaving factorization. -/
theorem CoordinateInterleaving.rank_erosion_le {ε : ℝ≥0}
    (I : CoordinateInterleaving ε M N)
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    (a b : Fin n → ℝ) (hab : a ≤ b) :
    rankOfStructureMap M (erosionWide_le ε hab) ≤ rankOfStructureMap N hab := by
  let x := erosionLower ε a
  have hx : translation ε x = a := translation_erosionLower ε a
  let h : translation ε x ≤ b := hx.symm ▸ hab
  have hxy : x ≤ translation ε b := by
    intro i
    change a i - (ε : ℝ) ≤ b i + (ε : ℝ)
    exact (sub_le_self _ ε.coe_nonneg).trans
      ((hab i).trans (le_add_of_nonneg_right ε.coe_nonneg))
  have hfactor := I.factor_structureMap h hxy
  unfold rankOfStructureMap
  have hfactorLinear := congrArg ModuleCat.Hom.hom hfactor
  have hbound : Module.finrank k (LinearMap.range
      (((I.ψ.app b).hom).comp ((structureMap N h).hom.comp (I.φ.app x).hom))) ≤
      Module.finrank k (LinearMap.range (structureMap N h).hom) := by
    letI : FiniteDimensional k (M.obj x) := inferInstance
    letI : FiniteDimensional k (((shift ε).obj N).obj x) := by
      change FiniteDimensional k (N.obj (translation ε x))
      infer_instance
    letI : FiniteDimensional k (N.obj b) := inferInstance
    exact ((finrank_range_comp_le
        ((structureMap N h).hom.comp (I.φ.app x).hom) (I.ψ.app b).hom).1).trans
      ((finrank_range_comp_le (I.φ.app x).hom (structureMap N h).hom).2)
  have same_start {p q : Fin n → ℝ} (e : p = q)
      (hp : p ≤ b) (hq : q ≤ b) :
      Module.finrank k (LinearMap.range (structureMap N hp).hom) =
        Module.finrank k (LinearMap.range (structureMap N hq).hom) := by
    cases e
    rfl
  calc
    Module.finrank k (LinearMap.range (structureMapLinear M (erosionWide_le ε hab))) =
        Module.finrank k (LinearMap.range (structureMap M hxy).hom) := by
      rfl
    _ = Module.finrank k (LinearMap.range
        (((I.ψ.app b).hom).comp ((structureMap N h).hom.comp (I.φ.app x).hom))) := by
      rw [hfactorLinear]
      rfl
    _ ≤ Module.finrank k (LinearMap.range (structureMap N h).hom) := hbound
    _ = Module.finrank k (LinearMap.range (structureMapLinear N hab)) :=
      same_start hx h hab

/-- Every actual interleaving supplies both erosion inequalities. -/
theorem CoordinateInterleaving.rankErosion {ε : ℝ≥0}
    (I : CoordinateInterleaving ε M N)
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)] : RankErosion ε M N :=
  ⟨I.rank_erosion_le, I.symm.rank_erosion_le⟩

/-- Weak-pair rank erosion is bounded by coordinate interleaving distance. -/
theorem rankErosionDistance_le_coordinateInterleavingDistance
    (M N : PModule.{u,0,u} k (Fin n → ℝ))
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)] :
    rankErosionDistance M N ≤ coordinateInterleavingDistance M N := by
  apply le_iInf₂
  intro ε ⟨I⟩
  exact rankErosionDistance_le_of_erosion I.rankErosion

end TDA.Persistence
