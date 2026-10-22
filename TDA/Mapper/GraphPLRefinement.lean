import TDA.Mapper.GraphPLDataRefinement
import TDA.Mapper.UniformMapperReebData

/-!
# Mapper comparisons for graph-PL refinement

This module composes the member-adapted Mapper comparison `uniformMapperIso` with the
refinement of graph-PL finite Reeb data from `TDA.Mapper.GraphPLDataRefinement`.  Adapted
Mapper finite data over a covering list are isomorphic to the refinement of graph-PL data over
any coarser covering list, in particular over the canonical vertex-height list, and the same
holds for the realizations over `ℝ`.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

universe u

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)
  {n m : ℕ} {S : CriticalValues n} {T : CriticalValues m}

/-! ## Mapper and realization corollaries -/

/-- The adapted Mapper finite data are isomorphic to the refinement of graph-PL data over `S`. -/
def uniformMapperRefineIso [Finite V] {a r g : ℝ} (T : CriticalValues m)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hS : CoversVertexHeights S h) (hST : Set.range S.value ⊆ Set.range T.value)
    (hg : 0 < g) (hgr : g ≤ r) :
    uniformMapperData G h a r g m ≅ RGraph.refineData hST (graphPLReebData G h S) :=
  uniformMapperIso G h T hT hcov hg hgr ≪≫ graphPLRefineIso G h hS hST

/-- The adapted Mapper finite data refine to graph-PL data over the canonical list. -/
def uniformMapperCanonicalIso [Fintype V] [Nonempty V] {a r g : ℝ} (T : CriticalValues m)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) :
    uniformMapperData G h a r g m ≅
      RGraph.refineData (range_vertexHeightLevels_subset h hcov)
        (graphPLReebData G h (vertexHeightLevels h)) :=
  uniformMapperRefineIso G h T hT hcov (coversVertexHeights_vertexHeightLevels h)
    (range_vertexHeightLevels_subset h hcov) hg hgr

/-- Every bounded finite graph-PL height has a canonical-list Mapper/refinement isomorphism. -/
theorem exists_uniformMapperCanonicalIso [Fintype V] [Nonempty V] {m₀ M ρ : ℝ}
    (hh : ∀ v, h v ∈ Set.Icc m₀ M) (hρ : 0 < ρ) :
    ∃ (a r g : ℝ) (n : ℕ) (T : CriticalValues n)
      (hST : Set.range (vertexHeightLevels h).value ⊆ Set.range T.value),
      0 < g ∧ 2 * g ≤ r ∧ r < ρ ∧ LevelsAdapted T a r g ∧
        Nonempty (uniformMapperData G h a r g n ≅
          RGraph.refineData hST (graphPLReebData G h (vertexHeightLevels h))) := by
  obtain ⟨a, r, g, n, T, hg, hgr, hrρ, hT, hcov, _hiso⟩ :=
    exists_uniformMapperIso G h hh hρ
  refine ⟨a, r, g, n, T, range_vertexHeightLevels_subset h hcov,
    hg, hgr, hrρ, hT, ?_⟩
  have hgr' : g ≤ r := by linarith
  exact ⟨uniformMapperCanonicalIso G h T hT hcov hg hgr'⟩

section realization

variable {V : Type} (G : SimpleGraph V) (h : V → ℝ)
  {n m : ℕ} {S : CriticalValues n} {T : CriticalValues m}

/-- The adapted Mapper realization is isomorphic to the canonical graph-PL realization. -/
def uniformMapperCanonicalToOverIso [Fintype V] [Nonempty V] {a r g : ℝ}
    (T : CriticalValues m) (hT : LevelsAdapted T a r g)
    (hcov : CoversVertexHeights T h) (hg : 0 < g) (hgr : g ≤ r) :
    RGraph.toOver T (uniformMapperData G h a r g m) ≅
      RGraph.toOver (vertexHeightLevels h)
        (graphPLReebData G h (vertexHeightLevels h)) :=
  (RGraph.realizationFunctor T).mapIso (uniformMapperIso G h T hT hcov hg hgr) ≪≫
    graphPLRefineToOverIso G h (coversVertexHeights_vertexHeightLevels h)
      (range_vertexHeightLevels_subset h hcov)

end realization

end
end TDA.Mapper.GraphPL
