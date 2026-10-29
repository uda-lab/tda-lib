import TDA.Persistence.CoordinateGrid
import TDA.Persistence.FinitePresentationKan
import TDA.Persistence.FinitePresentationGrid
import TDA.Persistence.FinitePresentationFiniteDimensional

/-!
# Finite-grid Kan reconstruction of finitely presented modules

The coordinate values of a finite presentation give a finite product grid
containing every generator and relation grade. The original module is
naturally isomorphic to the actual left Kan extension of its presentation's
restriction to that grid. Over a field the restricted fibers are finite
dimensional. Neither minimality nor a decomposition of the original module
is required.

This proves the reconstruction step in BOOS, arXiv:2208.00300v3,
Appendix A's proof of Theorem 2.7. Over a field, the actual Kan functor also
preserves pointwise finite dimensionality and rank-exact sequences on finite
product grids. The finite-coordinate inclusion also preserves relative hook
projectivity and transports the finite-grid hook deflation to an actual
finite-hook rank-exact cover of every finitely presented real-coordinate
module. Preservation of minimal resolutions remains a separate result.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence

namespace GradedFree

variable {R : Type u} [Ring R] {n : ℕ}

namespace Presentation

variable (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ)) (hD : D.IsFinite)

/-- The presentation coordinates, with zero added to keep every factor nonempty. -/
noncomputable def gridCoordinates : CoordinateGrid n := fun i =>
  insert 0 (D.criticalCoordinates_finite hD i).toFinset

/-- Every factor of the selected grid contains zero, including empty presentations. -/
theorem zero_mem_gridCoordinates (i : Fin n) : 0 ∈ D.gridCoordinates hD i := by
  classical
  exact Finset.mem_insert_self _ _

/-- A generator's original grade determines a grid point without merging occurrences. -/
noncomputable def generatorGridPoint (g : D.generators.Carrier) :
    (D.gridCoordinates hD).Point := fun i =>
  ⟨D.generators.grade g i, by
    classical
    apply Finset.mem_insert_of_mem
    exact (D.criticalCoordinates_finite hD i).mem_toFinset.mpr (Or.inl ⟨g, rfl⟩)⟩

/-- A relation's original grade determines a grid point. -/
noncomputable def relationGridPoint (y : D.relations.Carrier) :
    (D.gridCoordinates hD).Point := fun i =>
  ⟨D.relations.grade y i, by
    classical
    apply Finset.mem_insert_of_mem
    exact (D.criticalCoordinates_finite hD i).mem_toFinset.mpr (Or.inr ⟨y, rfl⟩)⟩

/-- The grid inclusion retains each generator birth exactly. -/
@[simp] theorem embedding_generatorGridPoint (g : D.generators.Carrier) :
    (D.gridCoordinates hD).embedding (D.generatorGridPoint hD g) = D.generators.grade g := rfl

/-- The grid inclusion retains each relation birth exactly. -/
@[simp] theorem embedding_relationGridPoint (y : D.relations.Carrier) :
    (D.gridCoordinates hD).embedding (D.relationGridPoint hD y) = D.relations.grade y := rfl

private theorem generator_mem_grid (g : D.generators.Carrier) :
    D.generators.grade g ∈ Set.range (D.gridCoordinates hD).embedding :=
  ⟨D.generatorGridPoint hD g, rfl⟩

private theorem relation_mem_grid (y : D.relations.Carrier) :
    D.relations.grade y ∈ Set.range (D.gridCoordinates hD).embedding :=
  ⟨D.relationGridPoint hD y, rfl⟩

/-- Restriction of the original presented quotient to its selected finite grid. -/
noncomputable abbrev gridModule : PModule.{u,0,max u w} R (D.gridCoordinates hD).Point :=
  (D.gridCoordinates hD).embedding.monotone.functor ⋙ D.presented

/-- The actual chosen Mathlib Kan extension reconstructs the presented module. -/
noncomputable def gridKanIso :
    (D.gridCoordinates hD).embedding.monotone.functor.leftKanExtension (D.gridModule hD) ≅
      D.presented :=
  D.kanIso (D.gridCoordinates hD).embedding (generator_mem_grid D hD) (relation_mem_grid D hD)

/-- The reconstruction satisfies the standard Kan universal property. -/
theorem grid_isLeftKanExtension : D.presented.IsLeftKanExtension
    (L := (D.gridCoordinates hD).embedding.monotone.functor) (𝟙 (D.gridModule hD)) :=
  D.isLeftKanExtension (D.gridCoordinates hD).embedding
    (generator_mem_grid D hD) (relation_mem_grid D hD)

/-- Natural maps out of the quotient are exactly the natural maps on its selected grid. -/
noncomputable def gridHomEquiv (N : PModule.{u,0,max u w} R (Fin n → ℝ)) :
    (D.presented ⟶ N) ≃
      (D.gridModule hD ⟶ (D.gridCoordinates hD).embedding.monotone.functor ⋙ N) :=
  D.restrictionHomEquiv (D.gridCoordinates hD).embedding
    (generator_mem_grid D hD) (relation_mem_grid D hD) N

/-- The selected-grid map bijection is ordinary restriction in the forward direction. -/
theorem gridHomEquiv_apply (N : PModule.{u,0,max u w} R (Fin n → ℝ)) (f : D.presented ⟶ N) :
    D.gridHomEquiv hD N f = (D.gridCoordinates hD).embedding.monotone.functor.whiskerLeft f :=
  D.restrictionHomEquiv_apply _ _ _ N f

/-- Extending a selected-grid map recovers precisely the supplied restricted map. -/
theorem gridHomEquiv_symm_restrict (N : PModule.{u,0,max u w} R (Fin n → ℝ))
    (α : D.gridModule hD ⟶ (D.gridCoordinates hD).embedding.monotone.functor ⋙ N) :
    (D.gridCoordinates hD).embedding.monotone.functor.whiskerLeft
      ((D.gridHomEquiv hD N).symm α) = α :=
  D.restrictionHomEquiv_symm_restrict _ _ _ N α

end Presentation

/-- Every finitely presented real-coordinate module is an actual left Kan
extension from a finite product grid, up to a natural isomorphism. -/
theorem finitelyPresented_exists_finiteGridKan
    (M : PModule.{u,0,max u w} R (Fin n → ℝ))
    (hM : FinitelyPresented (R := R) (P := Fin n → ℝ) M) :
    ∃ (G : CoordinateGrid n) (N : PModule.{u,0,max u w} R G.Point),
      Nonempty (G.embedding.monotone.functor.leftKanExtension N ≅ M) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  exact ⟨D.gridCoordinates hD, D.gridModule hD, ⟨D.gridKanIso hD ≪≫ e⟩⟩

/-- Over a field the finite-grid reconstruction has finite-dimensional fibers. -/
theorem finitelyPresented_exists_pfd_finiteGridKan
    {k : Type u} [Field k] (M : PModule.{u,0,max u w} k (Fin n → ℝ))
    (hM : FinitelyPresented (R := k) (P := Fin n → ℝ) M) :
    ∃ (G : CoordinateGrid n) (N : PModule.{u,0,max u w} k G.Point),
      (∀ p, FiniteDimensional k (N.obj p)) ∧
        Nonempty (G.embedding.monotone.functor.leftKanExtension N ≅ M) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  refine ⟨D.gridCoordinates hD, D.gridModule hD, ?_, ⟨D.gridKanIso hD ≪≫ e⟩⟩
  intro p
  exact D.finiteDimensional_of_finite_generators hD.1 ((D.gridCoordinates hD).embedding p)

/-- The finite presentation's actual reconstruction grid has nonempty factors.
The same presentation, restriction, and Kan reconstruction as in
`finitelyPresented_exists_pfd_finiteGridKan` are retained, with the already
proved zero membership exposed for each coordinate. -/
theorem finitelyPresented_exists_pfd_nonempty_finiteGridKan
    {k : Type u} [Field k] (M : PModule.{u,0,max u w} k (Fin n → ℝ))
    (hM : FinitelyPresented (R := k) (P := Fin n → ℝ) M) :
    ∃ (G : CoordinateGrid n) (N : PModule.{u,0,max u w} k G.Point),
      (∀ p, FiniteDimensional k (N.obj p)) ∧
        (∀ i : Fin n, (G i).Nonempty) ∧
          Nonempty (G.embedding.monotone.functor.leftKanExtension N ≅ M) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  refine ⟨D.gridCoordinates hD, D.gridModule hD, ?_, ?_, ⟨D.gridKanIso hD ≪≫ e⟩⟩
  · intro p
    exact D.finiteDimensional_of_finite_generators hD.1
      ((D.gridCoordinates hD).embedding p)
  · intro i
    exact ⟨0, D.zero_mem_gridCoordinates hD i⟩

end GradedFree

end TDA.Persistence
