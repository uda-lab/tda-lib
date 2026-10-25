import TDA.Persistence.CoordinateGridProjective
import TDA.Persistence.FiniteRankProjectiveClassification
import TDA.Persistence.FiniteRankProjectiveResolution

/-!
# Finite rank-projective resolutions under coordinate-grid Kan extension

An actual finite family of rank-exact projective rows on a finite coordinate grid
transfers along the actual left Kan extension. Each row uses the Lan images of its
original maps, rank exactness follows from the grid preservation theorem, and each
projective term remains rank projective. This is the transfer step used after a
finite-grid resolution has been constructed; it makes no resolution-existence claim.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence

variable {k : Type u} [Field k] {n : ℕ}

namespace FiniteRankProjectiveResolution

/-- A nonzero map of finite-death hooks can only move both endpoints down in
the coordinatewise order. This is the finite-poset direction used to prove
termination of minimal hook resolutions. -/
theorem hook_hom_nonzero_implies_endpoint_order
    {P : Type} [PartialOrder P] {i j m n : P} (hij : i < j) (hmn : m < n)
    (f : Hook.module (k := k) i j ⟶ Hook.module (k := k) m n) (hf : f ≠ 0) :
    m ≤ i ∧ n ≤ j := by
  let v := (Hook.homEquivKernel hij (Hook.module (k := k) m n)) f
  have hv : v.val ≠ 0 := by
    intro hzero
    apply hf
    exact (Hook.homEquivKernel hij (Hook.module (k := k) m n)).injective
      (Subtype.ext hzero)
  have hsupport : i ∈ Hook.support m n := v.val.property
  refine ⟨hsupport.1, ?_⟩
  by_contra hnj
  have hdie : structureMapLinear (Hook.module (k := k) m n) hij.le v.val = 0 :=
    v.property
  have hdieval :
      (structureMapLinear (Hook.module (k := k) m n) hij.le v.val).val = 0 :=
    congrArg Subtype.val hdie
  have hjSupport : j ∈ Hook.support m n := ⟨hsupport.1.trans hij.le, hnj⟩
  have hval := SupportInterval.structureMap_val (Hook.support m n)
    (Hook.support_ordConnected m n) hij.le v.val
  rw [if_pos hjSupport] at hval
  have hvzero : v.val = 0 := by
    apply Subtype.ext
    exact hval.symm.trans hdieval
  exact hv hvzero

/-- Endpoint order for every nonzero morphism between finite-poset rank-projective
hook types. A finite hook cannot map nontrivially to an infinite hook; infinite
source hooks use their birth as the only finite endpoint. -/
def rankProjectiveHookHomOrder {P : Type} [PartialOrder P]
    (s t : FiniteRankProjectiveClassification.RankProjectiveHookTag P) : Prop :=
  match s, t with
  | .inl ab, .inl cd => cd.val.1 ≤ ab.val.1 ∧ cd.val.2 ≤ ab.val.2
  | .inl _, .inr _ => False
  | .inr a, .inl cd => cd.val.1 ≤ a
  | .inr a, .inr b => b ≤ a

/-- Every nonzero hook component follows the finite endpoint order. This is the
strictness input for finite termination once minimality rules out equal-hook
components in successive differentials. -/
theorem rankProjectiveHook_hom_nonzero_order
    {P : Type} [PartialOrder P]
    (s t : FiniteRankProjectiveClassification.RankProjectiveHookTag P)
    (f : FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) s ⟶
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) t)
    (hf : f ≠ 0) : rankProjectiveHookHomOrder s t := by
  cases s with
  | inl ab =>
    cases t with
    | inl cd =>
      exact hook_hom_nonzero_implies_endpoint_order ab.property cd.property f hf
    | inr b =>
      let v := (Hook.homEquivKernel ab.property
        (HookInfinity.module (R := k) b)) f
      have hv : v.val ≠ 0 := by
        intro hzero
        apply hf
        exact (Hook.homEquivKernel ab.property
          (HookInfinity.module (R := k) b)).injective (Subtype.ext hzero)
      have hbi : b ≤ ab.val.1 := by
        by_contra hbi
        exact hv (HookInfinity.fiber_eq_zero_of_not_le hbi v.val)
      have hbj : b ≤ ab.val.2 := hbi.trans ab.property.le
      have hdie : structureMapLinear (HookInfinity.module (R := k) b)
          ab.property.le v.val = 0 := v.property
      have hcoeff : HookInfinity.fiberEquivOfLe (R := k) hbj v.val = 0 := by
        calc
          HookInfinity.fiberEquivOfLe (R := k) hbj v.val =
              HookInfinity.fiberEquivOfLe (R := k) hbj
                (structureMapLinear (HookInfinity.module (R := k) b)
                  ab.property.le v.val) := by
                    rw [HookInfinity.fiberEquivOfLe_structureMap hbi ab.property.le]
          _ = 0 := by rw [hdie, map_zero]
      exact (False.elim (hv
        ((HookInfinity.fiberEquivOfLe (R := k) hbi).injective hcoeff)))
  | inr a =>
    cases t with
    | inl cd =>
      let v := (HookInfinity.homEquivFiber (R := k) a
        (Hook.module (k := k) cd.val.1 cd.val.2)) f
      have hv : v ≠ 0 := by
        intro hzero
        apply hf
        exact (HookInfinity.homEquivFiber (R := k) a
          (Hook.module (k := k) cd.val.1 cd.val.2)).injective hzero
      exact v.property.1
    | inr b =>
      let v := (HookInfinity.homEquivFiber (R := k) a
        (HookInfinity.module (R := k) b)) f
      have hv : v ≠ 0 := by
        intro hzero
        apply hf
        exact (HookInfinity.homEquivFiber (R := k) a
          (HookInfinity.module (R := k) b)).injective hzero
      by_contra hba
      exact hv (HookInfinity.fiber_eq_zero_of_not_le hba v)

end FiniteRankProjectiveResolution

namespace FiniteRankProjectiveResolution

/-- Transport a finite rank-projective resolution across an actual module isomorphism. -/
def ofIso {P : Type} [PartialOrder P] {M N : PModule.{u,0,u} k P}
    (R : FiniteRankProjectiveResolution M) (e : M ≅ N) :
    FiniteRankProjectiveResolution N := by
  refine ⟨{
    length := R.length
    kernel := R.kernel
    term := R.term
    inclusion := R.inclusion
    quotient := R.quotient
    row_rank_exact := R.row_rank_exact
    initial_iso := R.initial_iso.trans e
    terminal_iso := R.terminal_iso
  }, R.term_rank_projective⟩

/-- A pointwise finite-dimensional rank-projective module has its actual
one-row identity resolution. -/
noncomputable def ofRankProjective {P : Type} [PartialOrder P]
    (M : PModule.{u,0,u} k P) (hfd : ∀ p, FiniteDimensional k (M.obj p))
    (hM : IsRankProjective M) : FiniteRankProjectiveResolution M := by
  let Z : PModule.{u,0,u} k P := 0
  let kernel : Fin 2 → PModule.{u,0,u} k P :=
    fun i => if i.val = 0 then M else Z
  let term : Fin 1 → PModule.{u,0,u} k P := fun _ => M
  let inclusion : ∀ i : Fin 1, kernel i.succ ⟶ term i := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change Z ⟶ M
    exact 0
  let quotient : ∀ i : Fin 1, term i ⟶ kernel i.castSucc := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change M ⟶ M
    exact 𝟙 M
  have zeroIdRankExact : IsRankExact (0 : Z ⟶ M) (𝟙 M) := by
    letI : ∀ p, FiniteDimensional k (M.obj p) := hfd
    have hshort : IsPointwiseShortExact (0 : Z ⟶ M) (𝟙 M) := by
      constructor
      · intro p x y _
        exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim x y
      · intro p x
        exact ⟨x, rfl⟩
      · intro p
        simp
    exact hshort.rankExact_of_section (𝟙 M) (by simp)
  refine ⟨{
    length := 1
    kernel := kernel
    term := term
    inclusion := inclusion
    quotient := quotient
    row_rank_exact := ?_
    initial_iso := ?_
    terminal_iso := ?_
  }, ?_⟩
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change IsRankExact (0 : Z ⟶ M) (𝟙 M)
    exact zeroIdRankExact
  · change kernel 0 ≅ M
    simp [kernel]
  · change kernel (Fin.last 1) ≅ 0
    simp [kernel, Z]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hM

end FiniteRankProjectiveResolution

namespace CoordinateGrid

/-- The Kan extension of the zero grid module is a zero object. -/
private noncomputable def lanZeroIso (G : CoordinateGrid n) :
    G.lan.obj (0 : PModule.{u,0,u} k G.Point) ≅ 0 := by
  have hzero : IsZero (G.lan.obj (0 : PModule.{u,0,u} k G.Point)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    have hz : (𝟙 (0 : PModule.{u,0,u} k G.Point)) = 0 :=
      (IsZero.iff_id_eq_zero _).mp (isZero_zero _)
    calc
      𝟙 (G.lan.obj (0 : PModule.{u,0,u} k G.Point)) =
          G.lan.map (𝟙 (0 : PModule.{u,0,u} k G.Point)) := by simp
      _ = G.lan.map (0 : (0 : PModule.{u,0,u} k G.Point) ⟶ 0) := by rw [hz]
      _ = 0 := map_zero _
  exact hzero.iso (isZero_zero _)

/-- Transfer every actual row of a finite rank-projective grid resolution through
the coordinate-grid left Kan extension. The same finite occurrence indexing is retained. -/
noncomputable def lanFiniteRankProjectiveResolution (G : CoordinateGrid n)
    {A : PModule.{u,0,u} k G.Point} (R : FiniteRankProjectiveResolution A) :
    FiniteRankProjectiveResolution (G.lan.obj A) := by
  refine ⟨{
    length := R.length
    kernel := fun i => G.lan.obj (R.kernel i)
    term := fun i => G.lan.obj (R.term i)
    inclusion := fun i => G.lan.map (R.inclusion i)
    quotient := fun i => G.lan.map (R.quotient i)
    row_rank_exact := fun i => G.lan_isRankExact (R.row_rank_exact i)
    initial_iso := G.lan.mapIso R.initial_iso
    terminal_iso := (G.lan.mapIso R.terminal_iso).trans (lanZeroIso G)
  }, ?_⟩
  intro i
  exact G.lan_isRankProjective (R.term i) (R.term_rank_projective i)

/-- Transport a finite rank-projective resolution across the presentation-grid
reconstruction isomorphism, retaining all Lan-transferred rows. -/
noncomputable def lanFiniteRankProjectiveResolutionOfReconstruction
    (G : CoordinateGrid n) {A : PModule.{u,0,u} k G.Point}
    (R : FiniteRankProjectiveResolution A)
    {M : PModule.{u,0,u} k (Fin n → ℝ)} (e : G.lan.obj A ≅ M) :
    FiniteRankProjectiveResolution M :=
  FiniteRankProjectiveResolution.ofIso (G.lanFiniteRankProjectiveResolution R) e

end CoordinateGrid

end TDA.Persistence
