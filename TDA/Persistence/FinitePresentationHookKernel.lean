import TDA.Persistence.FinitePresentationHookCover
import TDA.Persistence.FinitePresentationComparison
import TDA.Persistence.RankExactKernel
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite presentation of the finite-hook cover kernel

Pointwise finite-dimensional modules on finite posets admit finite graded-free
presentations. Finite-grid left Kan extension preserves these presentations,
which makes the actual kernel of the canonical finite-hook cover finitely
presented as well.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

namespace GradedFree

variable {k : Type u} [Field k] {P : Type} [PartialOrder P] [Fintype P]

/-- Every pointwise finite-dimensional module on a finite poset has a finite
graded-free presentation. Generators are bases of its fibers, and relations
are bases of the kernels of the resulting free cover. -/
theorem pfd_finitelyPresented_of_finite_poset
    (A : PModule.{u,0,u} k P) (hA : ∀ p, FiniteDimensional k (A.obj p)) :
    FinitelyPresented.{u,0,0} (R := k) (P := P) A := by
  classical
  letI : ∀ p, FiniteDimensional k (A.obj p) := hA
  let W : GradedGenerators.{0,0} P :=
    ⟨Σ p : P, Fin (Module.finrank k (A.obj p)), fun g => g.1⟩
  letI : Fintype W.Carrier := inferInstance
  let B (p : P) := Module.finBasis k (A.obj p)
  let cover : module (R := k) W ⟶ A :=
    GradedFree.lift W A (fun g => B g.1 g.2)
  have cover_birth (p : P) (i : Fin (Module.finrank k (A.obj p))) :
      (cover.app p).hom (GradedFree.birth W ⟨p, i⟩) = B p i := by
    simpa [cover, W, B] using
      (GradedFree.lift_birth W A (fun g => B g.1 g.2) ⟨p, i⟩)
  have cover_surjective (p : P) : Function.Surjective (cover.app p).hom := by
    intro x
    let y : (module (R := k) W).obj p :=
      ∑ i : Fin (Module.finrank k (A.obj p)),
        (B p).repr x i • GradedFree.birth W ⟨p, i⟩
    refine ⟨y, ?_⟩
    dsimp [y]
    rw [map_sum]
    trans ∑ i : Fin (Module.finrank k (A.obj p)), (B p).repr x i • B p i
    · apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, cover_birth]
    · exact (B p).sum_repr x
  have cover_finite (p : P) :
      FiniteDimensional k ((module (R := k) W).obj p) :=
    GradedFree.finiteDimensional_fiber W p
  let Y : GradedGenerators.{0,0} P :=
    ⟨Σ p : P, Fin (Module.finrank k (LinearMap.ker (cover.app p).hom)), fun g => g.1⟩
  letI : Fintype Y.Carrier := inferInstance
  let C (p : P) := Module.finBasis k (LinearMap.ker (cover.app p).hom)
  let rel : module (R := k) Y ⟶ module (R := k) W :=
    GradedFree.lift Y (module (R := k) W) (fun g => (C g.1 g.2).val)
  have rel_birth (p : P)
      (i : Fin (Module.finrank k (LinearMap.ker (cover.app p).hom))) :
      (rel.app p).hom (GradedFree.birth Y ⟨p, i⟩) = (C p i).val := by
    simpa [rel, Y, C] using
      (GradedFree.lift_birth Y (module (R := k) W)
        (fun g => (C g.1 g.2).val) ⟨p, i⟩)
  let D : Presentation.{u,0,0} (R := k) (P := P) :=
    ⟨W, Y, rel⟩
  have rel_comp_cover : rel ≫ cover = 0 := by
    apply GradedFree.hom_ext_birth Y
    intro g
    change (cover.app g.1).hom
      ((rel.app g.1).hom (GradedFree.birth Y g)) = 0
    rw [rel_birth]
    exact (C g.1 g.2).property
  have relation_range_eq_kernel (p : P) :
      LinearMap.range (rel.app p).hom = LinearMap.ker (cover.app p).hom := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have hz := congrArg (fun f : (module (R := k) Y).obj p ⟶ A.obj p => f.hom x)
        (NatTrans.congr_app rel_comp_cover p)
      change (cover.app p).hom ((rel.app p).hom x) = 0 at hz
      exact hz
    · intro y hy
      let Cy := Module.finBasis k (LinearMap.ker (cover.app p).hom)
      let y' : LinearMap.ker (cover.app p).hom := ⟨y, hy⟩
      let x : (module (R := k) Y).obj p :=
        ∑ i : Fin (Module.finrank k (LinearMap.ker (cover.app p).hom)),
          Cy.repr y' i • GradedFree.birth Y ⟨p, i⟩
      refine ⟨x, ?_⟩
      dsimp [x]
      rw [map_sum]
      trans ∑ i : Fin (Module.finrank k (LinearMap.ker (cover.app p).hom)),
          Cy.repr y' i • (Cy i).val
      · apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, rel_birth]
      · simpa only [Submodule.coe_sum, Submodule.coe_smul] using
          congrArg Subtype.val (Cy.sum_repr y')
  let q : D.presented ⟶ A := D.desc cover rel_comp_cover
  have q_cover : D.cover ≫ q = cover := D.cover_desc cover rel_comp_cover
  have q_surjective (p : P) : Function.Surjective (q.app p).hom := by
    intro x
    obtain ⟨y, hy⟩ := cover_surjective p x
    refine ⟨(D.cover.app p).hom y, ?_⟩
    have he := congrArg (fun f : (module (R := k) W).obj p ⟶ A.obj p => f.hom y)
      (NatTrans.congr_app q_cover p)
    change (q.app p).hom ((D.cover.app p).hom y) = (cover.app p).hom y at he
    exact he.trans hy
  have q_injective (p : P) : Function.Injective (q.app p).hom := by
    intro x y hxy
    obtain ⟨x₀, hx₀⟩ := D.cover_surjective p x
    obtain ⟨y₀, hy₀⟩ := D.cover_surjective p y
    have hxy₀ : (cover.app p).hom x₀ = (cover.app p).hom y₀ := by
      calc
        (cover.app p).hom x₀ = (q.app p).hom ((D.cover.app p).hom x₀) := by
          have he := congrArg (fun f : (module (R := k) W).obj p ⟶ A.obj p => f.hom x₀)
            (NatTrans.congr_app q_cover p)
          exact he.symm
        _ = (q.app p).hom x := by rw [hx₀]
        _ = (q.app p).hom y := hxy
        _ = (q.app p).hom ((D.cover.app p).hom y₀) := by rw [hy₀]
        _ = (cover.app p).hom y₀ := by
          have he := congrArg (fun f : (module (R := k) W).obj p ⟶ A.obj p => f.hom y₀)
            (NatTrans.congr_app q_cover p)
          exact he
    have hker : x₀ - y₀ ∈ LinearMap.ker (cover.app p).hom := by
      change (cover.app p).hom (x₀ - y₀) = 0
      rw [map_sub, hxy₀, sub_self]
    have hrel : x₀ - y₀ ∈ LinearMap.range (rel.app p).hom :=
      (relation_range_eq_kernel p).symm ▸ hker
    have hcoverzero :=
      (D.cover_eq_zero_iff_mem_relation_range p (x₀ - y₀)).2 hrel
    have hcovereq : (D.cover.app p).hom x₀ = (D.cover.app p).hom y₀ := by
      exact (sub_eq_zero.mp (by
        change (D.cover.app p).hom (x₀ - y₀) = 0 at hcoverzero
        simpa only [map_sub] using hcoverzero))
    rw [← hx₀, ← hy₀, hcovereq]
  letI (p : P) : IsIso (q.app p) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨q_injective p, q_surjective p⟩
  letI : IsIso q := NatIso.isIso_of_isIso_app q
  refine ⟨D, ?_, ⟨asIso q⟩⟩
  exact ⟨inferInstance, inferInstance⟩

end GradedFree

namespace GradedFree

variable {R : Type u} [Ring R] {P : Type} [Preorder P]

private instance moduleHasFiniteBiproducts :
    HasFiniteBiproducts (PModule.{u,0,u} R P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A finite-family graded-free module is the biproduct of the principal
upsets generated by its individual occurrences. -/
noncomputable def moduleBiproductIso (W : GradedGenerators.{0,0} P)
    [Fintype W.Carrier] :
    module (R := R) W ≅
      ⨁ fun g : W.Carrier => HookInfinity.module (R := R) (W.grade g) := by
  let F : W.Carrier → PModule.{u,0,u} R P :=
    fun g => HookInfinity.module (R := R) (W.grade g)
  let forward : module (R := R) W ⟶ ⨁ F :=
    GradedFree.lift W (⨁ F) (fun g =>
      (biproduct.ι F g).app (W.grade g) (HookInfinity.birth (W.grade g)))
  let backward : (⨁ F) ⟶ module (R := R) W :=
    biproduct.desc (fun g =>
      HookInfinity.fromBirth (W.grade g) (module (R := R) W)
        (GradedFree.birth W g))
  have hbackward_forward : backward ≫ forward = 𝟙 (⨁ F) := by
    apply biproduct.hom_ext'
    intro g
    have hι : biproduct.ι F g ≫ backward =
        HookInfinity.fromBirth (W.grade g) (module (R := R) W)
          (GradedFree.birth W g) := by
      simp [backward]
    calc
      biproduct.ι F g ≫ backward ≫ forward =
          (HookInfinity.fromBirth (W.grade g) (module (R := R) W)
            (GradedFree.birth W g)) ≫ forward := by rw [← Category.assoc, hι]
      _ = biproduct.ι F g := by
        apply GradedFree.hom_ext_birth
          (HookInfinity.generators (W.grade g))
        intro i
        cases i
        change (forward.app (W.grade g)).hom
          (((HookInfinity.fromBirth (W.grade g) (module (R := R) W)
            (GradedFree.birth W g)).app (W.grade g)).hom
              (HookInfinity.birth (W.grade g))) =
          ((biproduct.ι F g).app (W.grade g)).hom (HookInfinity.birth (W.grade g))
        rw [HookInfinity.fromBirth_birth]
        simp [forward, F]
  have hforward_backward : forward ≫ backward = 𝟙 (module (R := R) W) := by
    apply GradedFree.hom_ext_birth W
    intro g
    have hι : biproduct.ι F g ≫ backward =
        HookInfinity.fromBirth (W.grade g) (module (R := R) W)
          (GradedFree.birth W g) := by
      simp [backward]
    calc
      _ = ((biproduct.ι F g ≫ backward).app (W.grade g)).hom
          (HookInfinity.birth (W.grade g)) := by simp [forward, F]
      _ = ((HookInfinity.fromBirth (W.grade g) (module (R := R) W)
          (GradedFree.birth W g)).app (W.grade g)).hom
            (HookInfinity.birth (W.grade g)) := by rw [hι]
      _ = GradedFree.birth W g := by simp [HookInfinity.fromBirth_birth]
  exact ⟨forward, backward, hforward_backward, hbackward_forward⟩

end GradedFree

namespace CoordinateGrid

variable {n : ℕ}

/-- The occurrence family obtained by transporting births through the grid
embedding. -/
def embeddedGenerators (G : CoordinateGrid n)
    (W : GradedFree.GradedGenerators.{0,0} G.Point) :
    GradedFree.GradedGenerators.{0,0} (Fin n → ℝ) where
  Carrier := W.Carrier
  grade g := G.embedding (W.grade g)

end CoordinateGrid

namespace GradedFree

set_option maxHeartbeats 400000

end GradedFree

namespace CoordinateGrid

open CategoryTheory.Limits

variable {k : Type u} [Field k] {n : ℕ}

/-- The actual left Kan extension of a finite graded-free grid module is
the finite graded-free module on the same occurrences at their embedded
births. -/
noncomputable def lanFreeIso (G : CoordinateGrid n)
    (W : GradedFree.GradedGenerators.{0,0} G.Point) [Fintype W.Carrier] :
    G.lan.obj (GradedFree.module (R := k) W) ≅
      GradedFree.module (R := k) (G.embeddedGenerators W) := by
  letI : Fintype (G.embeddedGenerators W).Carrier := ‹Fintype W.Carrier›
  let F : W.Carrier → PModule.{u,0,u} k G.Point :=
    fun g => HookInfinity.module (W.grade g)
  letI :=
    (G.embedding.monotone.functor.lanAdjunction (ModuleCat.{u} k)).leftAdjoint_preservesColimits
  letI : PreservesBiproduct F G.lan :=
    preservesBiproduct_of_preservesCoproduct (F := G.lan) (f := F)
  exact (G.lan.mapIso (GradedFree.moduleBiproductIso (R := k) W)).trans
    ((G.lan.mapBiproduct F).trans
      ((biproduct.mapIso (fun g => G.infinityLanIso (W.grade g))).trans
        (GradedFree.moduleBiproductIso (R := k) (G.embeddedGenerators W)).symm))

end CoordinateGrid

namespace GradedFree

open CategoryTheory.Limits

variable {k : Type u} [Field k] {n : ℕ}

private instance lan_preserves_cokernel (G : CoordinateGrid n)
    {M N : PModule.{u,0,u} k G.Point} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) G.lan := by
  letI :=
    (G.embedding.monotone.functor.lanAdjunction (ModuleCat.{u} k)).leftAdjoint_preservesColimits
  infer_instance

/-- Finite-grid left Kan extension carries every finite graded-free
presentation to a finite graded-free presentation. The relation map is the
actual Kan image conjugated by the free-module occurrence comparisons. -/
theorem finitelyPresented_lan_of_finiteGrid
    (G : CoordinateGrid n)
    {A : PModule.{u,0,u} k G.Point}
    (hA : FinitelyPresented.{u,0,0} (R := k) (P := G.Point) A) :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) (G.lan.obj A) := by
  classical
  obtain ⟨D, hD, ⟨e⟩⟩ := hA
  letI : Finite D.generators.Carrier := hD.1
  letI : Finite D.relations.Carrier := hD.2
  letI : Fintype D.generators.Carrier := Fintype.ofFinite _
  letI : Fintype D.relations.Carrier := Fintype.ofFinite _
  let eW := G.lanFreeIso (k := k) D.generators
  let eY := G.lanFreeIso (k := k) D.relations
  let φ :
      module (R := k) (G.embeddedGenerators D.relations) ⟶
        module (R := k) (G.embeddedGenerators D.generators) :=
    eY.inv ≫ G.lan.map D.relationMap ≫ eW.hom
  let D' : Presentation.{u,0,0} (R := k) (P := Fin n → ℝ) :=
    ⟨G.embeddedGenerators D.generators, G.embeddedGenerators D.relations, φ⟩
  have hSquare : φ ≫ eW.symm.hom = eY.symm.hom ≫ G.lan.map D.relationMap := by
    simp [φ, Category.assoc]
  let quotientIso :=
    cokernel.mapIso (f := φ) (G.lan.map D.relationMap) eY.symm eW.symm hSquare ≪≫
      (PreservesCokernel.iso G.lan D.relationMap).symm
  have hD' : D'.IsFinite := by
    change Finite D'.generators.Carrier ∧ Finite D'.relations.Carrier
    exact ⟨hD.1, hD.2⟩
  refine ⟨D', hD', ?_⟩
  exact ⟨quotientIso ≪≫ G.lan.mapIso e⟩

/-- Every finitely presented real-coordinate module has the actual finite-hook
rank-exact cover from `finitelyPresented_exists_finiteHookRankExactCover`, and
the kernel of that displayed cover map is finitely presented. The proof
constructs a finite-poset presentation of the finite-dimensional grid kernel,
extends that presentation through the actual Lan, then identifies its Lan
with the actual cover kernel using the transported pointwise short-exact
comparison. -/
theorem finitelyPresented_exists_finiteHookRankExactCoverKernel
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (hM : FinitelyPresented (R := k) (P := Fin n → ℝ) M) :
    ∃ (G : CoordinateGrid n) (A : PModule.{u,0,u} k G.Point)
      (hA : ∀ p, FiniteDimensional k (A.obj p))
      (e : G.lan.obj A ≅ M),
      IsRankExact
        (G.lan.map (kernel.ι (FiniteHookDeflation.π A)) ≫
          (G.finiteHookDeflationLanIso A).hom)
        ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom) ∧
      IsRankProjective (⨁ fun t => G.embeddedCoverFamily A t) ∧
      FinitelyPresented.{u,0,0}
        (kernel ((G.finiteHookDeflationLanIso A).inv ≫
          G.lan.map (FiniteHookDeflation.π A) ≫ e.hom)) := by
  obtain ⟨G, A, hA, ⟨e⟩⟩ :=
    TDA.Persistence.GradedFree.finitelyPresented_exists_pfd_finiteGridKan M hM
  letI : ∀ p, FiniteDimensional k (A.obj p) := hA
  let c := G.finiteHookDeflationLanIso A
  let hsGrid := FiniteHookDeflation.rankExact A
  let hsShort := G.lan_isPointwiseShortExact hsGrid.toIsPointwiseShortExact
  let hsLan := G.lan_isRankExact hsGrid
  let left := G.lan.map (kernel.ι (FiniteHookDeflation.π A)) ≫ c.hom
  let right := c.inv ≫ G.lan.map (FiniteHookDeflation.π A) ≫ e.hom
  have hsActualShort : IsPointwiseShortExact left right := by
    simpa [left, right, c, Category.assoc] using
      hsShort.of_iso (Iso.refl _) c e
  have hsActual : IsRankExact left right := by
    simpa [left, right, c, Category.assoc] using
      hsLan.of_iso (Iso.refl _) c e
  have hGridKernel :
      FinitelyPresented.{u,0,0} (R := k) (P := G.Point)
        (kernel (FiniteHookDeflation.π A)) :=
    GradedFree.pfd_finitelyPresented_of_finite_poset
      (kernel (FiniteHookDeflation.π A))
      (FiniteHookDeflation.kernel_finiteDimensional A)
  have hLanKernel := GradedFree.finitelyPresented_lan_of_finiteGrid G hGridKernel
  have hActualKernel :=
    GradedFree.finitelyPresented_of_iso hLanKernel
      (IsPointwiseShortExact.kernelIso hsActualShort)
  refine ⟨G, A, hA, e, hsActual, ?_, ?_⟩
  · exact
      (G.lan_isRankProjective (FiniteHookDeflation.module A)
        (FiniteHookDeflation.isRankProjective A)).of_iso c
  · exact hActualKernel

end GradedFree

end TDA.Persistence
