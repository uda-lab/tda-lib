import TDA.Persistence.IncidenceQuotientBaseChange
import TDA.Persistence.IncidenceQuotientSimple
import TDA.Persistence.RankExact
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Vertex representations of right incidence modules

For the actual right incidence ring on the interval-pair poset, this file
constructs the covariant representation on all vertex fibers. The fibers are
fixed by the actual diagonal matrix units. The construction uses the canonical
restricted field action on every right-incidence module, and includes diagonal
vertices as well as strict vertices.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceVertexRepresentation

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open scoped ModuleCat

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : DecidableLE S := Classical.decRel _
local instance : DecidableLT S := Classical.decRel _
local instance : DecidableEq S := Classical.decEq _
local instance : DecidableEq (WithTop S) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset S) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop S × WithTop S => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset S) := Classical.decRel _
local instance : DecidableLT (PairPoset S) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset S) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset S) := Classical.decEq _
local instance : Fintype (FiniteRankProjectiveEndAlgebra.ComparablePair (S := S)) :=
  Fintype.ofFinite _

abbrev Incidence := FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)
abbrev RightIncidence := (Incidence (k := k) (S := S))ᵐᵒᵖ

/-- The actual underlying right-incidence module with its canonical restricted `k` scalars. -/
abbrev restrictedKModule (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) :
    ModuleCat.{u} k :=
  ModuleCat.of k M

/-- The `k`-linear action of an actual right-incidence matrix unit. -/
noncomputable def rightMatrixUnitAction
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S)))
    (p q : PairPoset S) (hpq : p ≤ q) :
    restrictedKModule (k := k) (S := S) M →ₗ[k]
      restrictedKModule (k := k) (S := S) M :=
  Algebra.lsmul k k M
    (IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq)

@[simp] theorem rightMatrixUnitAction_apply
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S)))
    (p q : PairPoset S) (hpq : p ≤ q) (m : M) :
    rightMatrixUnitAction (k := k) (S := S) M p q hpq m =
      IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq • m := rfl

/-- Opposite multiplication reverses the interval endpoints in the actual unit rule. -/
@[simp] theorem rightIncidenceMatrixUnit_mul
    (p q r s : PairPoset S) (hpq : p ≤ q) (hrs : r ≤ s) :
    IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq *
        IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) r s hrs =
      if h : s = p then
        IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) r q
          (by subst p; exact hrs.trans hpq)
      else 0 := by
  classical
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul,
    IncidenceQuotientBaseChange.rightIncidenceMatrixUnit, MulOpposite.unop_op]
  rw [FiniteRankProjectiveEndAlgebra.delta_mul]
  split_ifs <;> simp_all

/-- The diagonal units sum to the identity of the actual opposite incidence ring. -/
@[simp] theorem rightIncidence_diagonal_sum :
    (∑ p : PairPoset S,
      IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p p le_rfl) =
      (1 : RightIncidence (k := k) (S := S)) := by
  classical
  simp only [IncidenceQuotientBaseChange.rightIncidenceMatrixUnit]
  rw [← Finset.op_sum, IncidenceQuotientSimple.incidence_sum_diagonal_delta]
  simp

/-- The idempotent action of the diagonal unit at `p`. -/
noncomputable def diagonalProjector
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) (p : PairPoset S) :
    restrictedKModule (k := k) (S := S) M →ₗ[k]
      restrictedKModule (k := k) (S := S) M :=
  rightMatrixUnitAction (k := k) (S := S) M p p le_rfl

theorem diagonalProjector_idempotent
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) (p : PairPoset S)
    (m : restrictedKModule (k := k) (S := S) M) :
    diagonalProjector (k := k) (S := S) M p
        (diagonalProjector (k := k) (S := S) M p m) =
      diagonalProjector (k := k) (S := S) M p m := by
  change IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
      p p le_rfl •
        (IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
          p p le_rfl • m) =
      IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
        p p le_rfl • m
  rw [smul_smul, rightIncidenceMatrixUnit_mul]
  simp

/-- The `k`-submodule fixed by the diagonal projector at `p`. -/
def vertexFiber
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) (p : PairPoset S) :
    Submodule k (restrictedKModule (k := k) (S := S) M) :=
  LinearMap.eqLocus (diagonalProjector (k := k) (S := S) M p) LinearMap.id

@[simp] theorem mem_vertexFiber_iff
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) (p : PairPoset S)
    (m : restrictedKModule (k := k) (S := S) M) :
    m ∈ vertexFiber (k := k) (S := S) M p ↔
      diagonalProjector (k := k) (S := S) M p m = m :=
  LinearMap.mem_eqLocus

/-- A vertex fiber as an object of `ModuleCat k`. -/
abbrev VertexSpace
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) (p : PairPoset S) :
    ModuleCat.{u} k :=
  ModuleCat.of k (vertexFiber (k := k) (S := S) M p)

/-- Project a module element onto its fixed fiber at `p`. -/
noncomputable def projectToVertexFiber
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) (p : PairPoset S) :
    restrictedKModule (k := k) (S := S) M →ₗ[k]
      vertexFiber (k := k) (S := S) M p :=
  (diagonalProjector (k := k) (S := S) M p).codRestrict
    (vertexFiber (k := k) (S := S) M p)
    (fun m => mem_vertexFiber_iff (k := k) (S := S) M p
      (diagonalProjector (k := k) (S := S) M p m) |>.2
      (diagonalProjector_idempotent (k := k) (S := S) M p m))

@[simp] theorem projectToVertexFiber_val
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) (p : PairPoset S)
    (m : restrictedKModule (k := k) (S := S) M) :
    (projectToVertexFiber (k := k) (S := S) M p m : M) =
      diagonalProjector (k := k) (S := S) M p m := rfl

@[simp] theorem diagonalProjector_apply_vertex
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) (p q : PairPoset S)
    (x : vertexFiber (k := k) (S := S) M q) :
    diagonalProjector (k := k) (S := S) M p x = if p = q then x else 0 := by
  by_cases hpq : p = q
  · subst q
    simpa using (mem_vertexFiber_iff (k := k) (S := S) M p x).1 x.property
  · have hmul :
        IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p p le_rfl *
            IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) q q le_rfl = 0 := by
      rw [rightIncidenceMatrixUnit_mul]
      have hqp : q ≠ p := fun h => hpq h.symm
      simp [hqp]
    rw [if_neg hpq]
    change IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
        p p le_rfl • (x : M) = 0
    have hx : IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
        q q le_rfl • (x : M) = (x : M) := x.property
    rw [← hx, smul_smul, hmul]
    exact zero_smul (RightIncidence (k := k) (S := S)) (x : M)

/-- The sum of the diagonal projectors reconstructs every module element. -/
theorem diagonalProjector_sum
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S)))
    (m : restrictedKModule (k := k) (S := S) M) :
    (∑ p : PairPoset S, diagonalProjector (k := k) (S := S) M p m) = m := by
  change (∑ p : PairPoset S,
    IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p p le_rfl • m) = m
  rw [← Finset.sum_smul, rightIncidence_diagonal_sum, one_smul]

/-- The actual `k`-linear decomposition of a right-incidence module into all its vertex fibers. -/
noncomputable def vertexDecomposition
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) :
    restrictedKModule (k := k) (S := S) M ≃ₗ[k]
      (p : PairPoset S) → vertexFiber (k := k) (S := S) M p where
  toFun m p := projectToVertexFiber (k := k) (S := S) M p m
  invFun x := ∑ p : PairPoset S, x p
  map_add' x y := by
    ext p
    simp [projectToVertexFiber, diagonalProjector]
  map_smul' c x := by
    ext p
    simp [projectToVertexFiber, diagonalProjector]
  left_inv m := diagonalProjector_sum (k := k) (S := S) M m
  right_inv x := by
    ext p
    simp only [projectToVertexFiber_val]
    change diagonalProjector (k := k) (S := S) M p
        (∑ q : PairPoset S, (x q : M)) = (x p : M)
    rw [map_sum, Finset.sum_eq_single p]
    · exact (x p).property
    · intro q hq hqp
      rw [diagonalProjector_apply_vertex]
      simp [hqp.symm]
    · simp

/-- The covariant structure map induced by an actual comparable-pair matrix unit. -/
noncomputable def vertexStructureMap
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S)))
    {p q : PairPoset S} (hpq : p ≤ q) :
    vertexFiber (k := k) (S := S) M p →ₗ[k]
      vertexFiber (k := k) (S := S) M q :=
  ((rightMatrixUnitAction (k := k) (S := S) M p q hpq).codRestrict
    (vertexFiber (k := k) (S := S) M q) (by
      intro m
      apply (mem_vertexFiber_iff (k := k) (S := S) M q
        (rightMatrixUnitAction (k := k) (S := S) M p q hpq m)).2
      change IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
          q q le_rfl •
            (IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
              p q hpq • m) = _
      rw [smul_smul, rightIncidenceMatrixUnit_mul]
      rw [rightMatrixUnitAction_apply]
      simp
    )).comp (vertexFiber (k := k) (S := S) M p).subtype

@[simp] theorem vertexStructureMap_val
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S)))
    {p q : PairPoset S} (hpq : p ≤ q) (x : vertexFiber (k := k) (S := S) M p) :
    (vertexStructureMap (k := k) (S := S) M hpq x : M) =
      IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq • (x : M) := rfl

/-- The vertex representation associated to an arbitrary actual right-incidence module. -/
noncomputable def vertexRepresentation
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) :
    PModule.{u,0,u} k (PairPoset S) where
  obj p := VertexSpace (k := k) (S := S) M p
  map {p q} hpq := ModuleCat.ofHom
    (vertexStructureMap (k := k) (S := S) M (leOfHom hpq))
  map_id p := by
    ext x
    simp only [vertexStructureMap_val, ModuleCat.id_apply]
    change IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
        p p le_rfl • ((x : vertexFiber (k := k) (S := S) M p) : M) =
      ((x : vertexFiber (k := k) (S := S) M p) : M)
    exact (mem_vertexFiber_iff (k := k) (S := S) M p
      (x : vertexFiber (k := k) (S := S) M p)).1 x.property
  map_comp {p q r} hpq hqr := by
    ext x
    change (vertexStructureMap (k := k) (S := S) M (leOfHom (hpq ≫ hqr)) x : M) =
      (vertexStructureMap (k := k) (S := S) M (leOfHom hqr)
        (vertexStructureMap (k := k) (S := S) M (leOfHom hpq) x) : M)
    rw [vertexStructureMap_val, vertexStructureMap_val, vertexStructureMap_val,
      smul_smul, rightIncidenceMatrixUnit_mul]
    simp

@[simp] theorem vertexRepresentation_obj
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S))) (p : PairPoset S) :
    (vertexRepresentation (k := k) (S := S) M).obj p =
      VertexSpace (k := k) (S := S) M p := rfl

/-- An actual incidence-linear map restricted to one fixed vertex fiber. -/
noncomputable def mapOnVertexFiber
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))} (f : M ⟶ N)
    (p : PairPoset S) :
    vertexFiber (k := k) (S := S) M p →ₗ[k]
      vertexFiber (k := k) (S := S) N p :=
  ((f.hom.restrictScalars k).comp (vertexFiber (k := k) (S := S) M p).subtype).codRestrict
    (vertexFiber (k := k) (S := S) N p) (by
      intro m
      apply (mem_vertexFiber_iff (k := k) (S := S) N p (f.hom m)).2
      change IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
          p p le_rfl • f.hom m = f.hom m
      rw [← f.hom.map_smul]
      exact congrArg f.hom ((mem_vertexFiber_iff (k := k) (S := S) M p m).1 m.property))

@[simp] theorem mapOnVertexFiber_val
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))} (f : M ⟶ N)
    (p : PairPoset S) (x : vertexFiber (k := k) (S := S) M p) :
    (mapOnVertexFiber (k := k) (S := S) f p x : N) = f.hom x := rfl

/-- The additive vertex-fiber functor from right incidence modules. -/
noncomputable def vertexFunctor :
    ModuleCat.{u} (RightIncidence (k := k) (S := S)) ⥤
      PModule.{u,0,u} k (PairPoset S) where
  obj := vertexRepresentation (k := k) (S := S)
  map {M N} (f : M ⟶ N) := {
    app := fun p => ModuleCat.ofHom (mapOnVertexFiber (k := k) (S := S) f p)
    naturality := by
      intro p q hpq
      apply ModuleCat.hom_ext
      ext x
      change ((mapOnVertexFiber (k := k) (S := S) f q).comp
          (vertexStructureMap (k := k) (S := S) M (leOfHom hpq))) x =
        ((vertexStructureMap (k := k) (S := S) N (leOfHom hpq)).comp
          (mapOnVertexFiber (k := k) (S := S) f p)) x
      apply Subtype.ext
      change f.hom
          (IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
            p q (leOfHom hpq) • x.val) =
        IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
          p q (leOfHom hpq) • f.hom x.val
      exact f.hom.map_smul _ _
  }
  map_id M := by
    ext p x
    rfl
  map_comp f g := by
    ext p x
    rfl

noncomputable instance vertexFunctor_additive :
    Functor.Additive (vertexFunctor (k := k) (S := S)) where
  map_add := by
    intro M N f g
    ext p x
    rfl

/-- A comparable-pair unit acts on a fixed vertex fiber only at its source vertex. -/
theorem rightMatrixUnit_smul_vertex
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S)))
    {p q : PairPoset S} (hpq : p ≤ q) {r : PairPoset S}
    (x : vertexFiber (k := k) (S := S) M r) :
    IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq •
        (x : M) =
      if r = p then
        IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq •
          (x : M)
      else 0 := by
  by_cases hr : r = p
  · subst r
    simp
  · have hmul :
        IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq *
            IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) r r le_rfl = 0 := by
      rw [rightIncidenceMatrixUnit_mul]
      simp [hr]
    have hx : IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
        r r le_rfl • (x : M) = (x : M) :=
      (mem_vertexFiber_iff (k := k) (S := S) M r x).1 x.property
    rw [if_neg hr, ← hx, smul_smul, hmul]
    exact zero_smul (RightIncidence (k := k) (S := S)) (x : M)

/-- A comparable-pair unit only sees the corresponding projector of an arbitrary element. -/
theorem rightMatrixUnit_smul_projector
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S)))
    {p q : PairPoset S} (hpq : p ≤ q)
    (m : restrictedKModule (k := k) (S := S) M) :
    IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq • m =
      IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq •
        (projectToVertexFiber (k := k) (S := S) M p m : M) := by
  classical
  have hdecomp :
      (∑ r : PairPoset S, (projectToVertexFiber (k := k) (S := S) M r m : M)) = m := by
    calc
      (∑ r : PairPoset S, (projectToVertexFiber (k := k) (S := S) M r m : M)) =
          ∑ r : PairPoset S, diagonalProjector (k := k) (S := S) M r m := by
        apply Finset.sum_congr rfl
        intro r hr
        exact projectToVertexFiber_val (k := k) (S := S) M r m
      _ = m := diagonalProjector_sum (k := k) (S := S) M m
  calc
    IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq • m =
        IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq •
          ∑ r : PairPoset S, (projectToVertexFiber (k := k) (S := S) M r m : M) := by
            rw [hdecomp]
    _ = ∑ r : PairPoset S,
          IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq •
            (projectToVertexFiber (k := k) (S := S) M r m : M) := by
          change rightMatrixUnitAction (k := k) (S := S) M p q hpq
            (∑ r : PairPoset S, (projectToVertexFiber (k := k) (S := S) M r m : M)) = _
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro r hr
          exact rightMatrixUnitAction_apply (k := k) (S := S) M p q hpq
            (projectToVertexFiber (k := k) (S := S) M r m)
    _ = IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq •
          (projectToVertexFiber (k := k) (S := S) M p m : M) := by
          calc
            (∑ r : PairPoset S,
                IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq •
                  (projectToVertexFiber (k := k) (S := S) M r m : M)) =
                ∑ r : PairPoset S, if r = p then
                  IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq •
                    (projectToVertexFiber (k := k) (S := S) M r m : M) else 0 := by
              apply Finset.sum_congr rfl
              intro r hr
              exact rightMatrixUnit_smul_vertex (k := k) (S := S) M hpq
                (projectToVertexFiber (k := k) (S := S) M r m)
            _ = IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq •
                (projectToVertexFiber (k := k) (S := S) M p m : M) := by simp

/-- The component linear map of a natural transformation on the explicitly named vertex fibers. -/
noncomputable def naturalTransformationComponent
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N) (p : PairPoset S) :
    vertexFiber (k := k) (S := S) M p →ₗ[k]
      vertexFiber (k := k) (S := S) N p :=
  (α.app p).hom

/-- Reconstruct a `k`-linear map from the component maps of a natural transformation. -/
noncomputable def reconstructVertexNaturalTransformation
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N) :
    restrictedKModule (k := k) (S := S) M →ₗ[k]
      restrictedKModule (k := k) (S := S) N :=
  ∑ p : PairPoset S,
    ((vertexFiber (k := k) (S := S) N p).subtype.comp
      (naturalTransformationComponent (k := k) (S := S) α p)).comp
        (projectToVertexFiber (k := k) (S := S) M p)

@[simp] theorem reconstructVertexNaturalTransformation_apply
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N)
    (m : restrictedKModule (k := k) (S := S) M) :
    reconstructVertexNaturalTransformation (k := k) (S := S) α m =
      ∑ p : PairPoset S,
        ((naturalTransformationComponent (k := k) (S := S) α p
          (projectToVertexFiber (k := k) (S := S) M p m)) : N) := by
  simp [reconstructVertexNaturalTransformation]

/-- On an element already in one vertex fiber, reconstruction is the corresponding component. -/
theorem reconstructVertexNaturalTransformation_apply_vertex
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N)
    (p : PairPoset S) (x : vertexFiber (k := k) (S := S) M p) :
    reconstructVertexNaturalTransformation (k := k) (S := S) α x =
      ((naturalTransformationComponent (k := k) (S := S) α p x) : N) := by
  classical
  rw [reconstructVertexNaturalTransformation_apply]
  calc
    (∑ q : PairPoset S,
      ((naturalTransformationComponent (k := k) (S := S) α q
        (projectToVertexFiber (k := k) (S := S) M q x)) : N)) =
        ∑ q : PairPoset S, if q = p then
          ((naturalTransformationComponent (k := k) (S := S) α p x) : N) else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hqp : q = p
      · subst q
        have hproj : projectToVertexFiber (k := k) (S := S) M p x = x := by
          apply Subtype.ext
          simp only [projectToVertexFiber_val]
          exact (mem_vertexFiber_iff (k := k) (S := S) M p x).1 x.property
        simp [hproj]
      · have hzero : projectToVertexFiber (k := k) (S := S) M q x = 0 := by
          apply Subtype.ext
          change diagonalProjector (k := k) (S := S) M q x = 0
          have hx := diagonalProjector_apply_vertex (k := k) (S := S) M q p x
          simpa [hqp] using hx
        rw [hzero]
        simp only [if_neg hqp]
        exact congrArg (fun y : vertexFiber (k := k) (S := S) N q => (y : N))
          ((naturalTransformationComponent (k := k) (S := S) α q).map_zero)
    _ = ((naturalTransformationComponent (k := k) (S := S) α p x) : N) := by simp

/-- Projecting a reconstructed map recovers exactly the corresponding component map. -/
theorem projectToVertexFiber_reconstructVertexNaturalTransformation
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N)
    (p : PairPoset S) (m : restrictedKModule (k := k) (S := S) M) :
    projectToVertexFiber (k := k) (S := S) N p
      (reconstructVertexNaturalTransformation (k := k) (S := S) α m) =
        naturalTransformationComponent (k := k) (S := S) α p
          (projectToVertexFiber (k := k) (S := S) M p m) := by
  apply Subtype.ext
  rw [reconstructVertexNaturalTransformation_apply]
  change diagonalProjector (k := k) (S := S) N p
      (∑ r : PairPoset S,
        (naturalTransformationComponent (k := k) (S := S) α r
          (projectToVertexFiber (k := k) (S := S) M r m) : N)) = _
  rw [map_sum, Finset.sum_eq_single p]
  · simpa using diagonalProjector_apply_vertex (k := k) (S := S) N p p
      (naturalTransformationComponent (k := k) (S := S) α p
        (projectToVertexFiber (k := k) (S := S) M p m))
  · intro r hr hrne
    have hpr : p ≠ r := fun h => hrne h.symm
    have h := diagonalProjector_apply_vertex (k := k) (S := S) N p r
      (naturalTransformationComponent (k := k) (S := S) α r
        (projectToVertexFiber (k := k) (S := S) M r m))
    rw [if_neg hpr] at h
    simpa using h
  · simp

/-- A component of a natural transformation commutes with the vertex structure maps. -/
theorem naturalTransformationComponent_naturality
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N)
    {p q : PairPoset S} (hpq : p ≤ q) (x : vertexFiber (k := k) (S := S) M p) :
    naturalTransformationComponent (k := k) (S := S) α q
        (vertexStructureMap (k := k) (S := S) M hpq x) =
      vertexStructureMap (k := k) (S := S) N hpq
        (naturalTransformationComponent (k := k) (S := S) α p x) := by
  change (α.app q).hom (vertexStructureMap (k := k) (S := S) M hpq x) =
    vertexStructureMap (k := k) (S := S) N hpq ((α.app p).hom x)
  exact congrArg (fun f => f.hom x) (α.naturality (homOfLE hpq))

/-- The reconstructed `k`-linear map commutes with each actual incidence matrix unit. -/
theorem reconstructVertexNaturalTransformation_map_rightMatrixUnit
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N)
    {p q : PairPoset S} (hpq : p ≤ q)
    (m : restrictedKModule (k := k) (S := S) M) :
    reconstructVertexNaturalTransformation (k := k) (S := S) α
        (IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
          p q hpq • m) =
      IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
        p q hpq • reconstructVertexNaturalTransformation (k := k) (S := S) α m := by
  calc
    reconstructVertexNaturalTransformation (k := k) (S := S) α
        (IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
          p q hpq • m) =
        reconstructVertexNaturalTransformation (k := k) (S := S) α
          (vertexStructureMap (k := k) (S := S) M hpq
            (projectToVertexFiber (k := k) (S := S) M p m)) := by
          congr 1
          rw [rightMatrixUnit_smul_projector]
          rw [← vertexStructureMap_val]
    _ = (naturalTransformationComponent (k := k) (S := S) α q
          (vertexStructureMap (k := k) (S := S) M hpq
            (projectToVertexFiber (k := k) (S := S) M p m)) : N) := by
          rw [reconstructVertexNaturalTransformation_apply_vertex]
    _ = (vertexStructureMap (k := k) (S := S) N hpq
          (naturalTransformationComponent (k := k) (S := S) α p
            (projectToVertexFiber (k := k) (S := S) M p m)) : N) := by
          exact congrArg (fun x : vertexFiber (k := k) (S := S) N q => (x : N))
            (naturalTransformationComponent_naturality (k := k) (S := S) α hpq _)
    _ = IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
          p q hpq • reconstructVertexNaturalTransformation (k := k) (S := S) α m := by
          rw [rightMatrixUnit_smul_projector (k := k) (S := S) N hpq
            (reconstructVertexNaturalTransformation (k := k) (S := S) α m)]
          rw [projectToVertexFiber_reconstructVertexNaturalTransformation]
          rw [vertexStructureMap_val]

/-- A scalar multiple of a matrix unit is the corresponding right scalar multiple in the opposite ring. -/
private theorem rightIncidenceMatrixUnit_scalar_mul
    (p q : PairPoset S) (hpq : p ≤ q) (a : k) :
    MulOpposite.op
        (a • FiniteRankProjectiveEndAlgebra.delta (k := k) (S := S) p q hpq) =
      IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S) p q hpq *
        algebraMap k (RightIncidence (k := k) (S := S)) a := by
  rw [Algebra.smul_def]
  change MulOpposite.op
      (algebraMap k (Incidence (k := k) (S := S)) a *
        FiniteRankProjectiveEndAlgebra.delta (k := k) (S := S) p q hpq) = _
  rw [MulOpposite.op_mul]
  simp [IncidenceQuotientBaseChange.rightIncidenceMatrixUnit]

/-- Every element of the actual opposite incidence ring is a finite scalar sum of matrix units. -/
private theorem rightIncidence_eq_matrixUnit_sum
    (r : RightIncidence (k := k) (S := S)) :
    r = ∑ cp : FiniteRankProjectiveEndAlgebra.ComparablePair (S := S),
      IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
          cp.val.1 cp.val.2 cp.property *
        algebraMap k (RightIncidence (k := k) (S := S))
          (MulOpposite.unop r cp.val.1 cp.val.2) := by
  classical
  calc
    r = MulOpposite.op (MulOpposite.unop r) := (MulOpposite.op_unop r).symm
    _ = MulOpposite.op
          (FiniteRankProjectiveEndAlgebra.deltaExpansion (k := k) (S := S)
            (MulOpposite.unop r)) := by
          conv_lhs =>
            rw [FiniteRankProjectiveEndAlgebra.incidence_eq_deltaExpansion
              (k := k) (S := S) (MulOpposite.unop r)]
    _ = ∑ cp : FiniteRankProjectiveEndAlgebra.ComparablePair (S := S),
          IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
              cp.val.1 cp.val.2 cp.property *
            algebraMap k (RightIncidence (k := k) (S := S))
              (MulOpposite.unop r cp.val.1 cp.val.2) := by
          rw [FiniteRankProjectiveEndAlgebra.deltaExpansion, Finset.op_sum]
          apply Finset.sum_congr rfl
          intro cp hcp
          exact rightIncidenceMatrixUnit_scalar_mul (k := k) (S := S)
            cp.val.1 cp.val.2 cp.property
            (MulOpposite.unop r cp.val.1 cp.val.2)

/-- Reconstruct the actual right-incidence-linear map underlying a natural transformation. -/
noncomputable def reconstructVertexNaturalTransformationRLinear
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N) :
    M →ₗ[RightIncidence (k := k) (S := S)] N where
  toFun := reconstructVertexNaturalTransformation (k := k) (S := S) α
  map_add' := (reconstructVertexNaturalTransformation (k := k) (S := S) α).map_add
  map_smul' r m := by
    classical
    rw [rightIncidence_eq_matrixUnit_sum (k := k) (S := S) r]
    simp only [RingHom.id_apply]
    rw [Finset.sum_smul, Finset.sum_smul, map_sum]
    apply Finset.sum_congr rfl
    intro cp hcp
    let u := IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
      cp.val.1 cp.val.2 cp.property
    let c := MulOpposite.unop r cp.val.1 cp.val.2
    change reconstructVertexNaturalTransformation (k := k) (S := S) α
        ((u * algebraMap k (RightIncidence (k := k) (S := S)) c) • m) =
      (u * algebraMap k (RightIncidence (k := k) (S := S)) c) •
        reconstructVertexNaturalTransformation (k := k) (S := S) α m
    have hcomm (y : M) : u • (c • y) = c • (u • y) := by
      calc
        u • (c • y) = u • (algebraMap k (RightIncidence (k := k) (S := S)) c • y) := by
          rw [← IsScalarTower.algebraMap_smul (RightIncidence (k := k) (S := S)) c y]
        _ = (u * algebraMap k (RightIncidence (k := k) (S := S)) c) • y := by
          rw [mul_smul]
        _ = (algebraMap k (RightIncidence (k := k) (S := S)) c * u) • y := by
          rw [← Algebra.commutes c u]
        _ = algebraMap k (RightIncidence (k := k) (S := S)) c • (u • y) := by
          rw [mul_smul]
        _ = c • (u • y) := by
          rw [IsScalarTower.algebraMap_smul (RightIncidence (k := k) (S := S)) c (u • y)]
    have hcommN (y : N) : u • (c • y) = c • (u • y) := by
      calc
        u • (c • y) = u • (algebraMap k (RightIncidence (k := k) (S := S)) c • y) := by
          rw [← IsScalarTower.algebraMap_smul (RightIncidence (k := k) (S := S)) c y]
        _ = (u * algebraMap k (RightIncidence (k := k) (S := S)) c) • y := by
          rw [mul_smul]
        _ = (algebraMap k (RightIncidence (k := k) (S := S)) c * u) • y := by
          rw [← Algebra.commutes c u]
        _ = algebraMap k (RightIncidence (k := k) (S := S)) c • (u • y) := by
          rw [mul_smul]
        _ = c • (u • y) := by
          rw [IsScalarTower.algebraMap_smul (RightIncidence (k := k) (S := S)) c (u • y)]
    calc
      _ = reconstructVertexNaturalTransformation (k := k) (S := S) α
            (u • (c • m)) := by
              rw [mul_smul, IsScalarTower.algebraMap_smul
                (RightIncidence (k := k) (S := S)) c m]
      _ = reconstructVertexNaturalTransformation (k := k) (S := S) α
            (c • (u • m)) := by rw [hcomm]
      _ = c • reconstructVertexNaturalTransformation (k := k) (S := S) α (u • m) := by
            rw [(reconstructVertexNaturalTransformation (k := k) (S := S) α).map_smul]
      _ = c • (u • reconstructVertexNaturalTransformation (k := k) (S := S) α m) := by
            rw [reconstructVertexNaturalTransformation_map_rightMatrixUnit]
      _ = u • (c • reconstructVertexNaturalTransformation (k := k) (S := S) α m) :=
            (hcommN (reconstructVertexNaturalTransformation (k := k) (S := S) α m)).symm
      _ = (u * algebraMap k (RightIncidence (k := k) (S := S)) c) •
            reconstructVertexNaturalTransformation (k := k) (S := S) α m := by
            rw [mul_smul, ← IsScalarTower.algebraMap_smul
              (RightIncidence (k := k) (S := S)) c
              (reconstructVertexNaturalTransformation (k := k) (S := S) α m)]


/-- The actual module morphism reconstructed from a natural transformation. -/
noncomputable def naturalTransformationToRightIncidenceHom
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N) : M ⟶ N :=
  ModuleCat.ofHom (reconstructVertexNaturalTransformationRLinear (k := k) (S := S) α)

/-- Reconstructing the image of an actual module map returns that map. -/
theorem reconstructVertexNaturalTransformationRLinear_vertexFunctor_map
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))} (f : M ⟶ N) :
    reconstructVertexNaturalTransformationRLinear (k := k) (S := S)
      ((vertexFunctor (k := k) (S := S)).map f) = f.hom := by
  let α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N := by
    change vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N
    exact (vertexFunctor (k := k) (S := S)).map f
  apply LinearMap.ext
  intro m
  change reconstructVertexNaturalTransformation (k := k) (S := S) α m = f.hom m
  rw [reconstructVertexNaturalTransformation_apply]
  calc
    (∑ p : PairPoset S,
      (naturalTransformationComponent (k := k) (S := S)
        α p
        (projectToVertexFiber (k := k) (S := S) M p m) : N)) =
      ∑ p : PairPoset S, f.hom (projectToVertexFiber (k := k) (S := S) M p m : M) := by
        apply Finset.sum_congr rfl
        intro p hp
        change (mapOnVertexFiber (k := k) (S := S) f p
          (projectToVertexFiber (k := k) (S := S) M p m) : N) = _
        exact mapOnVertexFiber_val (k := k) (S := S) f p
          (projectToVertexFiber (k := k) (S := S) M p m)
    _ = f.hom m := by
        rw [← map_sum]
        congr 1
        exact diagonalProjector_sum (k := k) (S := S) M m

/-- The component maps of a natural transformation followed by reconstruction recover it. -/
theorem vertexFunctor_map_naturalTransformationToRightIncidenceHom
    {M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))}
    (α : vertexRepresentation (k := k) (S := S) M ⟶
      vertexRepresentation (k := k) (S := S) N) :
    (vertexFunctor (k := k) (S := S)).map
        (naturalTransformationToRightIncidenceHom (k := k) (S := S) α) = α := by
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change VertexSpace (k := k) (S := S) M p at x
  let x' : vertexFiber (k := k) (S := S) M p := x
  apply Subtype.ext
  change reconstructVertexNaturalTransformation (k := k) (S := S) α (x' : M) =
    (naturalTransformationComponent (k := k) (S := S) α p x' : N)
  exact reconstructVertexNaturalTransformation_apply_vertex (k := k) (S := S) α p x'

/-- Actual module morphisms are in bijection with natural transformations of vertex representations. -/
noncomputable def vertexFunctorHomEquiv
    (M N : ModuleCat.{u} (RightIncidence (k := k) (S := S))) :
    (M ⟶ N) ≃
      (vertexRepresentation (k := k) (S := S) M ⟶
        vertexRepresentation (k := k) (S := S) N) where
  toFun := (vertexFunctor (k := k) (S := S)).map
  invFun := naturalTransformationToRightIncidenceHom (k := k) (S := S)
  left_inv f := by
    apply ModuleCat.hom_ext
    exact reconstructVertexNaturalTransformationRLinear_vertexFunctor_map
      (k := k) (S := S) f
  right_inv α := vertexFunctor_map_naturalTransformationToRightIncidenceHom
    (k := k) (S := S) α

/-- The vertex-fiber functor is fully faithful on all actual right-incidence modules. -/
noncomputable def vertexFunctorFullyFaithful :
    (vertexFunctor (k := k) (S := S)).FullyFaithful where
  preimage := naturalTransformationToRightIncidenceHom (k := k) (S := S)
  map_preimage := vertexFunctor_map_naturalTransformationToRightIncidenceHom
    (k := k) (S := S)
  preimage_map f := by
    apply ModuleCat.hom_ext
    exact reconstructVertexNaturalTransformationRLinear_vertexFunctor_map
      (k := k) (S := S) f

noncomputable instance vertexFunctor_full :
    Functor.Full (vertexFunctor (k := k) (S := S)) :=
  (vertexFunctorFullyFaithful (k := k) (S := S)).full

noncomputable instance vertexFunctor_faithful :
    Functor.Faithful (vertexFunctor (k := k) (S := S)) :=
  (vertexFunctorFullyFaithful (k := k) (S := S)).faithful

end

end TDA.Persistence.IncidenceVertexRepresentation
