import TDA.Persistence.FiniteSimplicial
import TDA.Persistence.FinitePresentationHookKernel

/-!
# Finite presentation of graded simplicial homology

The finitely many face coordinates define a finite product grid. Sublevels
agree with their grid floors; below the grid they are empty. The canonical
Kan comparison is consequently an isomorphism, including all structure maps.
Finite-dimensional grid fibres then give a finite graded-free presentation of
the actual inclusion-induced homology module.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace TDA.Filtration.FiniteGraded

open TDA.Simplicial TDA.Persistence

variable {m n : ℕ} {C : FiniteComplex m} (g : FiniteGraded C n)

/-- The finite grid contains every face coordinate, together with zero. -/
noncomputable def gridCoordinates : CoordinateGrid n := fun i => by
  classical
  exact insert 0 (Finset.univ.image (fun s : TotalFace C.toPre => g.grade s i))

/-- Each coordinate factor is nonempty, even when the input complex is empty. -/
theorem zero_mem_gridCoordinates (i : Fin n) : 0 ∈ g.gridCoordinates i := by
  classical
  exact Finset.mem_insert_self _ _

/-- Every face grade determines a point in the finite coordinate grid. -/
noncomputable def gridPoint (s : TotalFace C.toPre) : g.gridCoordinates.Point := fun i =>
  ⟨g.grade s i, by
    classical
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)⟩

/-- The finite grid retains each face's original coordinate grade. -/
@[simp] theorem embedding_gridPoint (s : TotalFace C.toPre) :
    g.gridCoordinates.embedding (g.gridPoint s) = g.grade s := rfl

/-- A face lies below a threshold exactly when it lies below its grid floor. -/
theorem grade_le_floor_iff (a : Fin n → ℝ) (ha : g.gridCoordinates.HasLowerPoint a)
    (s : TotalFace C.toPre) :
    g.grade s ≤ g.gridCoordinates.embedding (g.gridCoordinates.floor a ha) ↔
      g.grade s ≤ a := by
  constructor
  · exact fun h => h.trans (g.gridCoordinates.floor_le a ha)
  · intro h
    exact g.gridCoordinates.embedding.monotone (g.gridCoordinates.le_floor a ha (p := g.gridPoint s) h)

/-- The grid-floor sublevel has exactly the faces of the original sublevel. -/
theorem sublevel_floor (a : Fin n → ℝ) (ha : g.gridCoordinates.HasLowerPoint a) :
    g.sublevel (g.gridCoordinates.embedding (g.gridCoordinates.floor a ha)) =
      g.sublevel a :=
  g.sublevel_eq_of_forall_le_iff (g.grade_le_floor_iff a ha)

/-- Without a lower grid point no face is present. This also covers empty inputs. -/
theorem sublevel_eq_bot_of_not_hasLowerPoint (a : Fin n → ℝ)
    (ha : ¬ g.gridCoordinates.HasLowerPoint a) : g.sublevel a = ⊥ := by
  apply (g.sublevel_eq_bot_iff a).mpr
  intro s hs
  exact ha ⟨g.gridPoint s, hs⟩

end TDA.Filtration.FiniteGraded

namespace TDA.Persistence
open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence
variable {n : ℕ} (G : CoordinateGrid n) {R : Type u} [Ring R]
  (M : PModule.{u,0,u} R (Fin n → ℝ))

private noncomputable def gridComparison :
    G.lan.obj (G.embedding.monotone.functor ⋙ M) ⟶ M :=
  (G.embedding.monotone.functor.leftKanExtension
    (G.embedding.monotone.functor ⋙ M)).descOfIsLeftKanExtension
    (G.embedding.monotone.functor.leftKanExtensionUnit
      (G.embedding.monotone.functor ⋙ M)) M (𝟙 _)

private theorem gridComparison_fac :
    G.embedding.monotone.functor.leftKanExtensionUnit (G.embedding.monotone.functor ⋙ M) ≫
      G.embedding.monotone.functor.whiskerLeft (gridComparison G M) = 𝟙 _ := by
  exact Functor.descOfIsLeftKanExtension_fac _ _ _ _

private theorem kanInclusion_gridComparison (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    G.kanInclusion (G.embedding.monotone.functor ⋙ M) a ha ≫
      (gridComparison G M).app a = structureMap M (G.floor_le a ha) := by
  have hf := NatTrans.congr_app (gridComparison_fac G M) (G.floor a ha)
  have hn := (gridComparison G M).naturality (homOfLE (G.floor_le a ha))
  change (G.embedding.monotone.functor.leftKanExtensionUnit
      (G.embedding.monotone.functor ⋙ M)).app (G.floor a ha) ≫
        (gridComparison G M).app (G.embedding (G.floor a ha)) =
          𝟙 (M.obj (G.embedding (G.floor a ha))) at hf
  change structureMap (G.lan.obj (G.embedding.monotone.functor ⋙ M))
      (G.floor_le a ha) ≫ (gridComparison G M).app a =
    (gridComparison G M).app (G.embedding (G.floor a ha)) ≫
      structureMap M (G.floor_le a ha) at hn
  dsimp [CoordinateGrid.kanInclusion]
  rw [Category.assoc, hn, ← Category.assoc, hf, Category.id_comp]

private noncomputable def gridIso
    (hfloor : ∀ (a : Fin n → ℝ) (ha : G.HasLowerPoint a),
      IsIso (structureMap M (G.floor_le a ha)))
    (hzero : ∀ a, ¬ G.HasLowerPoint a → IsZero (M.obj a)) :
    G.lan.obj (G.embedding.monotone.functor ⋙ M) ≅ M := by
  haveI (a : Fin n → ℝ) : IsIso ((gridComparison G M).app a) := by
    by_cases ha : G.HasLowerPoint a
    · let j := G.kanInclusion (G.embedding.monotone.functor ⋙ M) a ha
      have : IsIso j := by
        change IsIso (G.appIso (G.embedding.monotone.functor ⋙ M) a ha).inv
        infer_instance
      have : IsIso (j ≫ (gridComparison G M).app a) := by
        dsimp [j]
        rw [kanInclusion_gridComparison]
        exact hfloor a ha
      exact IsIso.of_isIso_comp_left j ((gridComparison G M).app a)
    · exact IsZero.isIso (G.isZero_obj_of_not_hasLowerPoint _ a ha) (hzero a ha) _
  letI : IsIso (gridComparison G M) := NatIso.isIso_of_isIso_app _
  exact asIso (gridComparison G M)

section FiniteSimplicial

open TDA.Filtration TDA.Simplicial

variable {m n : ℕ} {C : FiniteComplex m} (k : Type u) [Field k]
    (g : FiniteGraded C n) (q : ℕ)

/-- Restriction of the actual simplicial homology module to its finite grade grid. -/
noncomputable abbrev finiteSimplicialGridHomology :
    PModule.{u,0,u} k g.gridCoordinates.Point :=
  g.gridCoordinates.embedding.monotone.functor ⋙ finiteSimplicialHomology k g q

/-- The canonical natural comparison reconstructs all homology fibres and
structure maps from the finite grid, using the actual Mathlib left Kan extension. -/
noncomputable def finiteSimplicialHomology_gridKanIso :
    g.gridCoordinates.lan.obj (finiteSimplicialGridHomology k g q) ≅
      finiteSimplicialHomology k g q := by
  apply gridIso
  · intro a ha
    rw [finiteSimplicialHomology_structureMap]
    exact simplicialHomologyIncl_isIso_of_eq k _ (g.sublevel_floor a ha) q
  · intro a ha
    rw [finiteSimplicialHomology_obj, g.sublevel_eq_bot_of_not_hasLowerPoint a ha]
    exact isZero_simplicialHomology_bot k q

/-- The comparison extends the identity on the restricted homology module. -/
theorem finiteSimplicialHomology_gridKanIso_fac :
    g.gridCoordinates.embedding.monotone.functor.leftKanExtensionUnit
      (finiteSimplicialGridHomology k g q) ≫
        g.gridCoordinates.embedding.monotone.functor.whiskerLeft
          (finiteSimplicialHomology_gridKanIso k g q).hom = 𝟙 _ :=
  gridComparison_fac _ _

/-- Under the comparison, inclusion from the floor is the actual homology
structure morphism from that sublevel. -/
theorem finiteSimplicialHomology_gridKanIso_kanInclusion
    (a : Fin n → ℝ) (ha : g.gridCoordinates.HasLowerPoint a) :
    g.gridCoordinates.kanInclusion (finiteSimplicialGridHomology k g q) a ha ≫
      (finiteSimplicialHomology_gridKanIso k g q).hom.app a =
        structureMap (finiteSimplicialHomology k g q) (g.gridCoordinates.floor_le a ha) :=
  kanInclusion_gridComparison _ _ a ha

/-- Finite graded simplicial input has a finite graded-free presentation in
all degrees over any coefficient field. No reconstruction or finiteness witness
is required from the caller. -/
theorem finiteSimplicialHomology_finitelyPresented :
    GradedFree.FinitelyPresented.{u,0,0} (finiteSimplicialHomology k g q) := by
  have hgrid : GradedFree.FinitelyPresented.{u,0,0}
      (finiteSimplicialGridHomology k g q) :=
    GradedFree.pfd_finitelyPresented_of_finite_poset _ (fun _ =>
      finiteSimplicialHomology_finiteDimensional k g q _)
  exact GradedFree.finitelyPresented_of_iso
    (GradedFree.finitelyPresented_lan_of_finiteGrid g.gridCoordinates hgrid)
    (finiteSimplicialHomology_gridKanIso k g q)

end FiniteSimplicial
end TDA.Persistence
