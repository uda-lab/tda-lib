import TDA.Persistence.TwoInjectivePresentation
import TDA.Persistence.FiniteInjectiveRankDimension
import TDA.Persistence.FiniteRankProjectiveHomDimension
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Hom left exactness and the two-step dimension shift

Applying the hook-generator Hom functor to the actual two-injective sequence
is left exact. Factoring its final map through its actual image gives two
short exact rows, with the actual cokernel as the terminal object. The
dimension-shift theorem assumes a bound only on that cokernel; the bounds for
the two injective terms are derived from the principal-downset estimate.

This is the categorical part of the upper-bound argument in BOOS v3,
Theorem 5.16. The source's finite-algebra estimate on the final cokernel is a
separate input and is not asserted here.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.TwoInjectiveHomDimension

open CategoryTheory CategoryTheory.Limits
open FiniteInjectiveRankDimension
open FiniteRankProjectiveHomExact
open TwoInjectivePresentation

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]
  [OrderBot S] [OrderTop S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S

private instance : HasFiniteBiproducts (PModule.{u,0,u} k S) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private abbrev H := homFunctor (k := k) (S := S)

private instance : (H (k := k) (S := S)).PreservesZeroMorphisms where
  map_zero M N := by
    apply ModuleCat.hom_ext
    ext f
    simp

/-- The actual Hom map induced by the second differential. -/
abbrev homDifferential (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] := (H (k := k) (S := S)).map (differential M)

/-- The actual categorical cokernel of Hom applied to the differential. -/
def homCokernel (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] := cokernel (homDifferential M)

/-- The actual categorical image of Hom applied to the differential. -/
def homImage (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] := Abelian.image (homDifferential M)

/-- The actual map from Hom of the first injective to the image of its next map. -/
abbrev homImageFactor (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :=
  Abelian.factorThruImage (homDifferential M)

/-- The inclusion of the actual image into Hom of the second injective. -/
abbrev homImageInclusion (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :=
  Abelian.image.ι (homDifferential M)

/-- The actual cokernel projection after Hom of the differential. -/
abbrev homCokernelProjection (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :=
  cokernel.π (homDifferential M)

/-- The module-valued Hom maps induced by the actual two-injective sequence
are exact at the middle term. No rank exactness or Hom-surjectivity is assumed. -/
theorem homMaps_exact_at (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :
    Function.Exact
      ((H (k := k) (S := S)).map (firstEmbedding M)).hom
      (homDifferential M).hom := by
  have hbase : Function.Exact
      (postcompose (k := k) (S := S) (firstEmbedding M))
      (postcompose (k := k) (S := S) (quotientProjection M)) := by
    let hs := cokernelRow M
    have hExact := homShortComplex_exact (k := k) (S := S) hs
    rw [ShortComplex.moduleCat_exact_iff] at hExact
    intro f
    constructor
    · intro hf
      have hfπ : f ≫ quotientProjection M = 0 := by
        simpa only [postcompose_apply] using hf
      have hfπ' : ((H (k := k) (S := S)).map (quotientProjection M)).hom f = 0 := by
        change f ≫ quotientProjection M = 0
        exact hfπ
      obtain ⟨g, hg⟩ := hExact f hfπ'
      exact ⟨g, by
        change ((H (k := k) (S := S)).map (firstEmbedding M)).hom g = f
        exact hg⟩
    · rintro ⟨g, hg⟩
      have hg' : g ≫ firstEmbedding M = f := by
        simpa only [postcompose_apply] using hg
      change f ≫ quotientProjection M = 0
      calc
        f ≫ quotientProjection M = (g ≫ firstEmbedding M) ≫ quotientProjection M := by
          rw [hg']
        _ = g ≫ (firstEmbedding M ≫ quotientProjection M) := Category.assoc _ _ _
        _ = 0 := by rw [(cokernelRow M).comp_eq_zero]; simp
  intro f
  constructor
  · intro hf
    have hδ : f ≫ differential M = 0 := by
      change f ≫ differential M = 0
      exact hf
    haveI : Mono (secondEmbedding M) := secondEmbedding_mono M
    have hπ : f ≫ quotientProjection M = 0 := by
      apply (cancel_mono (secondEmbedding M)).mp
      calc
        (f ≫ quotientProjection M) ≫ secondEmbedding M = f ≫ differential M := by
          simp [differential, Category.assoc]
        _ = 0 := hδ
        _ = 0 ≫ secondEmbedding M := by simp
    obtain ⟨g, hg⟩ := (hbase f).mp (by simpa only [postcompose_apply] using hπ)
    exact ⟨g, by
      change g ≫ firstEmbedding M = f at hg
      exact hg⟩
  · rintro ⟨g, hg⟩
    have hg' : g ≫ firstEmbedding M = f := by
      change g ≫ firstEmbedding M = f at hg
      exact hg
    change f ≫ differential M = 0
    rw [← hg', Category.assoc, firstEmbedding_comp_differential]
    simp

/-- Hom of the first embedding is monic by ordinary left exactness. -/
theorem hom_firstEmbedding_mono (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :
    Mono ((H (k := k) (S := S)).map (firstEmbedding M)) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro f g h
  change f ≫ firstEmbedding M = g ≫ firstEmbedding M at h
  exact (cancel_mono (firstEmbedding M)).mp h

/-- The actual two-row Hom sequence, split at the actual image of Hom(delta). -/
def firstShortComplex (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :
    ShortComplex (ModuleCat.{u} (HomScalars (k := k) (S := S))) :=
  ShortComplex.mk
    ((H (k := k) (S := S)).map (firstEmbedding M))
    (homImageFactor M)
    (by
      apply (cancel_mono (homImageInclusion M)).mp
      calc
        (((H (k := k) (S := S)).map (firstEmbedding M)) ≫ homImageFactor M) ≫
            homImageInclusion M =
              ((H (k := k) (S := S)).map (firstEmbedding M)) ≫
                (homImageFactor M ≫ homImageInclusion M) := by
                  rw [Category.assoc]
        _ = ((H (k := k) (S := S)).map (firstEmbedding M)) ≫
              (homDifferential M) := by rw [Abelian.image.fac]
        _ = (H (k := k) (S := S)).map
              (firstEmbedding M ≫ differential M) := by rw [Functor.map_comp]
        _ = 0 := by
          rw [firstEmbedding_comp_differential]
          exact Functor.map_zero (H (k := k) (S := S)) _ _
        _ = 0 ≫ homImageInclusion M := by simp)

/-- The first actual image row is short exact. -/
theorem firstShortComplex_shortExact (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] : (firstShortComplex M).ShortExact := by
  let f := homDifferential M
  have hex : Function.Exact
      ((H (k := k) (S := S)).map (firstEmbedding M)).hom f.hom :=
    homMaps_exact_at M
  have hExact : (firstShortComplex M).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : (homImageFactor M).hom x = 0 := by
      change (firstShortComplex M).g x = 0 at hx
      exact hx
    have hfx : f.hom x = 0 := by
      have hfac : f.hom x = (Abelian.image.ι f).hom
          ((Abelian.factorThruImage f).hom x) := by
        have h := congrArg (fun q => q.hom x) (Abelian.image.fac f).symm
        calc
          f.hom x = ((Abelian.factorThruImage f ≫ Abelian.image.ι f).hom) x := h
          _ = (Abelian.image.ι f).hom ((Abelian.factorThruImage f).hom x) := by
            rw [ModuleCat.hom_comp]
            exact LinearMap.comp_apply _ _ _
      rw [hfac, hx']
      simp
    exact (hex x).mp hfx
  have hmono : Mono ((H (k := k) (S := S)).map (firstEmbedding M)) :=
    hom_firstEmbedding_mono M
  have hepi : Epi (homImageFactor M) := inferInstance
  haveI : Mono (firstShortComplex M).f := hmono
  haveI : Epi (firstShortComplex M).g := hepi
  exact ⟨hExact⟩

/-- The actual cokernel row on the right side of the image factorization. -/
def secondShortComplex (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :
    ShortComplex (ModuleCat.{u} (HomScalars (k := k) (S := S))) :=
  ShortComplex.mk (homImageInclusion M) (homCokernelProjection M)
    (by
      apply (cancel_epi (homImageFactor M)).mp
      calc
        homImageFactor M ≫ (homImageInclusion M ≫ homCokernelProjection M) =
            (homImageFactor M ≫ homImageInclusion M) ≫ homCokernelProjection M := by
              rw [Category.assoc]
        _ = homDifferential M ≫ homCokernelProjection M := by rw [Abelian.image.fac]
        _ = 0 := cokernel.condition (homDifferential M))

/-- The second actual image row is short exact and ends in the actual
cokernel of Hom(delta). -/
theorem secondShortComplex_shortExact (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] : (secondShortComplex M).ShortExact := by
  let f := homDifferential M
  let Q := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hExact : (secondShortComplex M).Exact := by
    exact (Q.exact_iff_exact_image_ι).mp (ShortComplex.exact_cokernel f)
  have hmono : Mono (homImageInclusion M) := inferInstance
  have hepi : Epi (homCokernelProjection M) := inferInstance
  haveI : Mono (secondShortComplex M).f := hmono
  haveI : Epi (secondShortComplex M).g := hepi
  exact ⟨hExact⟩

/-- Hom of each constructed injective has the maximum-complement projective
dimension bound supplied by the principal-downset construction. -/
theorem hom_firstInjective_hasProjectiveDimensionLE
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)] :
    HasProjectiveDimensionLE ((H (k := k) (S := S)).obj (firstInjective M))
      (maxComplementCard (S := S) - 1) :=
  FiniteInjectiveRankDimension.hasProjectiveDimensionLE_of_max (firstInjective M)

/-- The second actual injective term has the same internally derived Hom bound. -/
theorem hom_secondInjective_hasProjectiveDimensionLE
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)] :
    HasProjectiveDimensionLE ((H (k := k) (S := S)).obj (secondInjective M))
      (maxComplementCard (S := S) - 1) :=
  FiniteInjectiveRankDimension.hasProjectiveDimensionLE_of_max (secondInjective M)

/-- Two applications of Mathlib's short-exact dimension shift reduce the
projective dimension of Hom(M) by two from the actual Hom cokernel bound.
The injective Hom bounds are derived internally from `D - 1 ≤ d`. -/
theorem hom_hasProjectiveDimensionLE_of_actualCokernel
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)] (d : ℕ)
    (hD : maxComplementCard (S := S) - 1 ≤ d)
    (hC : HasProjectiveDimensionLE (homCokernel M) (d + 2)) :
    HasProjectiveDimensionLE ((H (k := k) (S := S)).obj M) d := by
  have hI₀ : HasProjectiveDimensionLT
      ((H (k := k) (S := S)).obj (firstInjective M)) (d + 1) := by
    letI : HasProjectiveDimensionLT ((H (k := k) (S := S)).obj (firstInjective M))
        (maxComplementCard (S := S) - 1 + 1) := hom_firstInjective_hasProjectiveDimensionLE M
    exact hasProjectiveDimensionLT_of_ge _ _ _ (Nat.succ_le_succ hD)
  have hI₁ : HasProjectiveDimensionLT
      ((H (k := k) (S := S)).obj (secondInjective M)) (d + 2) :=
    by
      letI : HasProjectiveDimensionLT ((H (k := k) (S := S)).obj (secondInjective M))
          (maxComplementCard (S := S) - 1 + 1) := hom_secondInjective_hasProjectiveDimensionLE M
      exact hasProjectiveDimensionLT_of_ge _ _ _ (by
        exact (Nat.succ_le_succ hD).trans (Nat.le_succ _))
  have hC' : HasProjectiveDimensionLT (homCokernel M) (d + 3) := hC
  have hImage : HasProjectiveDimensionLT (homImage M) (d + 2) :=
    (secondShortComplex_shortExact M).hasProjectiveDimensionLT_X₁ (d + 2) hI₁ hC'
  exact (firstShortComplex_shortExact M).hasProjectiveDimensionLT_X₁ (d + 1) hI₀ hImage

/-- Under the two stated inputs, every supplied certified minimal
rank-projective resolution has zero-padded terms vanishing above `d`. -/
theorem minimalResolution_termAt_isZero_of_actualCokernel
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)]
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (d : ℕ)
    (hD : maxComplementCard (S := S) - 1 ≤ d)
    (hC : HasProjectiveDimensionLE (homCokernel M) (d + 2)) :
    ∀ j, d < j → IsZero (R.termAt j) :=
  (FiniteRankProjectiveHomDimension.hasProjectiveDimensionLE_iff R d).mp
    (hom_hasProjectiveDimensionLE_of_actualCokernel M d hD hC)

end

end TDA.Persistence.TwoInjectiveHomDimension
