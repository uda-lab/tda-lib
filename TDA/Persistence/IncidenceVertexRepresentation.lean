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

end

end TDA.Persistence.IncidenceVertexRepresentation
