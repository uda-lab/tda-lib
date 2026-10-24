import TDA.Persistence.CoordinateGridHook
import TDA.Persistence.FinitePresentationGridKan
import TDA.Persistence.RankExactIso

/-!
# Finite-hook rank-exact covers of finitely presented modules

The finite-grid reconstruction and occurrence-indexed hook deflation give an
actual rank-exact cover in the ambient real-coordinate category. The cover is
the finite biproduct of the embedded finite- and infinite-death hooks; its
kernel is pointwise finite dimensional. This does not assert finite
presentation of that kernel or minimality of the cover.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence

variable {k : Type u} [Field k] {n : ℕ}

/-- Every finitely presented real-coordinate module is the quotient of an
actual finite biproduct of embedded finite- and infinite-death hooks by a
rank-exact map. The kernel has pointwise finite-dimensional fibers, and the
cover is relative rank projective. The grid module and reconstruction
isomorphism are exposed as witnesses; no hook decomposition of the original
module is assumed. -/
theorem finitelyPresented_exists_finiteHookRankExactCover
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
      (∀ a : Fin n → ℝ,
        FiniteDimensional k
          ((G.lan.obj (kernel (FiniteHookDeflation.π A))).obj a)) := by
  obtain ⟨G, A, hA, ⟨e⟩⟩ :=
    TDA.Persistence.GradedFree.finitelyPresented_exists_pfd_finiteGridKan
      M hM
  letI : ∀ p, FiniteDimensional k (A.obj p) := hA
  let c := G.finiteHookDeflationLanIso A
  let hsGrid := FiniteHookDeflation.rankExact A
  let hsLan := G.lan_isRankExact hsGrid
  let left :
      G.lan.obj (kernel (FiniteHookDeflation.π A)) ⟶
        ⨁ fun t => G.embeddedCoverFamily A t :=
    G.lan.map (kernel.ι (FiniteHookDeflation.π A)) ≫ c.hom
  let right :
      (⨁ fun t => G.embeddedCoverFamily A t) ⟶ M :=
    c.inv ≫ G.lan.map (FiniteHookDeflation.π A) ≫ e.hom
  have htransport : IsRankExact left right := by
    simpa [left, right, c, Category.assoc] using
      hsLan.of_iso (Iso.refl _) c e
  have hprojective : IsRankProjective (⨁ fun t => G.embeddedCoverFamily A t) :=
    (G.lan_isRankProjective (FiniteHookDeflation.module A)
      (FiniteHookDeflation.isRankProjective A)).of_iso c
  refine ⟨G, A, hA, e, ?_, hprojective, ?_⟩
  · exact htransport
  · intro a
    letI : FiniteDimensional k
        ((G.lan.obj (FiniteHookDeflation.module A)).obj a) :=
      G.lan_finiteDimensional (FiniteHookDeflation.module A) a
    exact FiniteDimensional.of_injective
      ((G.lan.map (kernel.ι (FiniteHookDeflation.π A))).app a).hom
      (hsLan.injective a)

end TDA.Persistence.GradedFree
