import TDA.Persistence.FiniteInjectiveRankDimension
import TDA.Persistence.FiniteRankProjectiveResolutionKan
import TDA.Persistence.TwoInjectivePresentation
import TDA.Persistence.FiniteLatticeComplementCardinality
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-!
# Ordinary projective dimension on finite lattices

This file bounds ordinary Ext-based projective dimension in the actual
persistence-functor category. The proof first controls hooks and finite rank
resolution rows, then principal-downset injectives, and finally removes the
temporary finite bound using the actual injective-presentation row.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.OrdinaryFiniteLatticeDimension

open CategoryTheory CategoryTheory.Limits
open PrincipalDownsetRankResolution
open TDA.Persistence.FiniteInjectivePresentation
open TDA.Persistence.FiniteRankProjectiveClassification
open TDA.Persistence.FiniteLatticeComplementCardinality
open scoped Classical

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]
  [OrderBot S] [OrderTop S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S

private instance : HasFiniteBiproducts (PModule.{u,0,u} k S) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private def singletonFace : GeneratedUpsetResolution.FaceIndex 1 0 :=
  ⟨{0}, by simp⟩

private theorem inclusion_eq_faceMap {a b : S} (h : a ≤ b) :
    HookCokernel.inclusion (k := k) h =
      GeneratedUpsetResolutionMap.faceMap (k := k)
        (f := fun _ : Fin 1 => b) (g := fun _ : Fin 1 => a)
        (fun _ => h) singletonFace := by
  apply HookInfinity.hom_ext
  simp [HookCokernel.inclusion, GeneratedUpsetResolutionMap.faceMap,
    GeneratedUpsetResolution.faceModule, GeneratedUpsetResolution.faceJoin,
    singletonFace]
  exact congrArg (fun h' : a ≤ b =>
    structureMapLinear (HookInfinity.module (R := k) a) h'
      (HookInfinity.birth (R := k) a)) (Subsingleton.elim _ _)

/-- The actual principal-upset inclusion used to define a finite hook is monic. -/
theorem hookCokernel_inclusion_mono {a b : S} (h : a ≤ b) :
    Mono (HookCokernel.inclusion (k := k) h) := by
  rw [inclusion_eq_faceMap (k := k) h]
  exact GeneratedUpsetResolutionMap.faceMap_mono (k := k)
    (f := fun _ : Fin 1 => b) (g := fun _ => a) (fun _ => h) singletonFace

private theorem hookShortExact {a b : S} (h : a ≤ b) :
    (ShortComplex.mk (HookCokernel.inclusion (k := k) h)
      (HookCokernel.projection (k := k) a b)
      (HookCokernel.inclusion_projection (k := k) h)).ShortExact := by
  let R := ShortComplex.mk (HookCokernel.inclusion (k := k) h)
    (HookCokernel.projection (k := k) a b)
    (HookCokernel.inclusion_projection (k := k) h)
  have hcolim : IsColimit (CokernelCofork.ofπ R.g R.zero) :=
    HookCokernel.isCokernel (k := k) h
  have hexepi : R.Exact ∧ Epi R.g := R.exact_and_epi_g_iff_g_is_cokernel.mpr ⟨hcolim⟩
  exact ShortComplex.ShortExact.mk' hexepi.1 (hookCokernel_inclusion_mono (k := k) h) hexepi.2

/-- Every finite-death hook on a finite lattice has ordinary projective dimension at most one. -/
theorem finiteHook_hasProjectiveDimensionLE_one {a b : S} (h : a ≤ b) :
    HasProjectiveDimensionLE (Hook.module (k := k) a b) 1 := by
  have hrow := hookShortExact (k := k) h
  have h₁ : HasProjectiveDimensionLT (HookInfinity.module (R := k) b) 1 := inferInstance
  have h₂ : HasProjectiveDimensionLT (HookInfinity.module (R := k) a) 2 :=
    hasProjectiveDimensionLT_of_ge _ 1 2 (by omega)
  exact hrow.hasProjectiveDimensionLT_X₃ 1 h₁ h₂

private theorem infiniteHook_hasProjectiveDimensionLE_one (a : S) :
    HasProjectiveDimensionLE (HookInfinity.module (R := k) a) 1 := by
  have hp : Projective (HookInfinity.module (R := k) a) := inferInstance
  have h₀ : HasProjectiveDimensionLT (HookInfinity.module (R := k) a) 1 :=
    projective_iff_hasProjectiveDimensionLT_one.mp hp
  exact hasProjectiveDimensionLT_of_ge _ 1 2 (by omega)

/-- Every pointwise finite-dimensional rank-projective has ordinary dimension at most one. -/
theorem rankProjective_hasProjectiveDimensionLE_one
    (M : PModule.{u,0,u} k S) (hM : ∀ p, FiniteDimensional k (M.obj p))
    (hR : IsRankProjective M) : HasProjectiveDimensionLE M 1 := by
  obtain ⟨J, ⟨e⟩⟩ :=
    (rankProjective_iff_exists_canonical_subfamily (k := k) (P := S) M hM).mp hR
  have hsum : HasProjectiveDimensionLE
      (⨁ fun i : J => FiniteHookDeflation.family M i.1) 1 := by
    apply FiniteInjectiveRankDimension.hasProjectiveDimensionLE_biproduct
      (C := PModule.{u,0,u} k S) (I := J)
      (F := fun i : J => FiniteHookDeflation.family M i.1) 1
    intro i
    cases i.1 with
    | inl t => exact finiteHook_hasProjectiveDimensionLE_one (k := k) t.1.property.le
    | inr t => exact infiniteHook_hasProjectiveDimensionLE_one (k := k) t.1
  letI : HasProjectiveDimensionLT
      (⨁ fun i : J => FiniteHookDeflation.family M i.1) 2 := hsum
  exact hasProjectiveDimensionLT_of_iso e.symm 2

private theorem pointwiseShortExact_toShortExact
    {A B C : PModule.{u,0,u} k S} {f : A ⟶ B} {g : B ⟶ C}
    (hs : IsPointwiseShortExact f g) :
    (ShortComplex.mk f g hs.comp_eq_zero).ShortExact := by
  let Q := ShortComplex.mk f g hs.comp_eq_zero
  have hEpi : Epi g := (NatTrans.epi_iff_epi_app g).2 (fun p =>
    (ModuleCat.epi_iff_surjective _).2 (hs.surjective p))
  let K := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hK : K.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_kernel g) inferInstance hEpi
  have hinv : (hs.kernelIso).inv ≫ f = kernel.ι g := by
    calc
      (hs.kernelIso).inv ≫ f = (hs.kernelIso).inv ≫
          ((hs.kernelIso).hom ≫ kernel.ι g) := by rw [hs.kernelIso_hom_ι]
      _ = kernel.ι g := by simp [Category.assoc]
  let e : K ≅ Q := ShortComplex.isoMk (hs.kernelIso).symm (Iso.refl _)
    (Iso.refl _) hinv
  exact ShortComplex.shortExact_of_iso e hK

private theorem finiteRows_hasProjectiveDimensionLE
    (n : ℕ) (K : Fin (n + 1) → PModule.{u,0,u} k S)
    (P : Fin n → PModule.{u,0,u} k S)
    (f : ∀ i, K i.succ ⟶ P i) (g : ∀ i, P i ⟶ K i.castSucc)
    (w : ∀ i, f i ≫ g i = 0)
    (hex : ∀ i, (ShortComplex.mk (f i) (g i) (w i)).ShortExact)
    (hmiddle : ∀ i, HasProjectiveDimensionLE (P i) 1)
    (hlast : IsZero (K (Fin.last n))) :
    HasProjectiveDimensionLE (K 0) n := by
  induction n with
  | zero =>
      have hz : IsZero (K 0) := by simpa using hlast
      letI : HasProjectiveDimensionLT (K 0) 0 := hz.hasProjectiveDimensionLT_zero
      exact hasProjectiveDimensionLT_of_ge (K 0) 0 1 (by omega)
  | succ n ih =>
      have htail : HasProjectiveDimensionLE (K 1) n := by
        apply ih (fun i => K i.succ) (fun i => P i.succ)
          (fun i => f i.succ) (fun i => g i.succ) (fun i => w i.succ)
          (fun i => hex i.succ) (fun i => hmiddle i.succ) ?_
        simpa using hlast
      have hmid : HasProjectiveDimensionLT (P 0) 2 := hmiddle 0
      have hmid' : HasProjectiveDimensionLT (P 0) (n + 2) :=
        hasProjectiveDimensionLT_of_ge (P 0) 2 (n + 2) (by omega)
      exact (hex 0).hasProjectiveDimensionLT_X₃ (n + 1) htail hmid'

/-- Any actual finite rank-projective resolution gives this loose ordinary
dimension bound by its recorded number of middle terms. -/
theorem finiteRankProjectiveResolution_hasProjectiveDimensionLE
    {M : PModule.{u,0,u} k S} (R : FiniteRankProjectiveResolution M) :
    HasProjectiveDimensionLE M R.length := by
  have hlast : IsZero (R.kernel (Fin.last R.length)) :=
    IsZero.of_iso (isZero_zero _) R.terminal_iso
  have hrows : HasProjectiveDimensionLE (R.kernel 0) R.length :=
    finiteRows_hasProjectiveDimensionLE R.length R.kernel R.term R.inclusion R.quotient
      (fun i => (R.row_rank_exact i).toIsPointwiseShortExact.comp_eq_zero)
      (fun i => pointwiseShortExact_toShortExact (R.row_rank_exact i).toIsPointwiseShortExact)
      (fun i => rankProjective_hasProjectiveDimensionLE_one (k := k) (R.term i)
        (R.row_rank_exact i).finiteDimensional (R.term_rank_projective i)) hlast
  letI : HasProjectiveDimensionLT (R.kernel 0) (R.length + 1) := hrows
  exact hasProjectiveDimensionLT_of_iso R.initial_iso (R.length + 1)

/-- Each principal downset has ordinary projective dimension bounded by its
number of minimal complement generators, including the top downset. -/
theorem principalDownset_hasProjectiveDimensionLE (p : S) :
    HasProjectiveDimensionLE (PrincipalDownsetInjective.module (k := k) p)
      (complementCard (S := S) p) := by
  by_cases hp : p = ⊤
  · subst p
    have hHook : Projective (HookInfinity.module (R := k) (⊥ : S)) := inferInstance
    have hproj : Projective (PrincipalDownsetInjective.module (k := k) (⊤ : S)) :=
      hHook.of_iso (PrincipalDownsetRankResolution.topHookIso (k := k) (S := S)).symm
    have hzero : complementCard (⊤ : S) = 0 :=
      (complementCard_eq_zero_iff (⊤ : S)).mpr rfl
    rw [hzero]
    letI : Projective (PrincipalDownsetInjective.module (k := k) (⊤ : S)) := hproj
    exact (inferInstance : HasProjectiveDimensionLT
      (PrincipalDownsetInjective.module (k := k) (⊤ : S)) 1)
  · have hpos : 0 < complementCard (S := S) p := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hp ((complementCard_eq_zero_iff (S := S) p).mp hz)
    let R := PrincipalDownsetRankResolution.resolution (k := k) p
    have hR := finiteRankProjectiveResolution_hasProjectiveDimensionLE (k := k) R
    have hlen : R.length = complementCard (S := S) p := by
      rw [PrincipalDownsetRankResolution.resolution_length]
      exact max_eq_right (Nat.succ_le_of_lt hpos)
    simpa [hlen] using hR

/-- Every ordinary injective pointwise finite-dimensional module has ordinary
projective dimension at most the lattice complement maximum. -/
theorem injective_hasProjectiveDimensionLE_of_max
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)] [Injective M] :
    HasProjectiveDimensionLE M (FiniteInjectiveRankDimension.maxComplementCard (S := S)) := by
  letI : Fintype (FiniteInjectivePresentation.Index (k := k) (P := S) M) :=
    FiniteInjectivePresentation.indexFintype (k := k) (P := S) M
  let I := FiniteInjectivePresentation.Index (k := k) (P := S) M
  have hsum : HasProjectiveDimensionLE
      (⨁ fun i : I => FiniteInjectivePresentation.family M i)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S)) := by
    apply FiniteInjectiveRankDimension.hasProjectiveDimensionLE_biproduct
      (C := PModule.{u,0,u} k S) (I := I)
      (F := fun i : I => FiniteInjectivePresentation.family M i)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S))
    intro i
    have hp := principalDownset_hasProjectiveDimensionLE (k := k) i.1
    letI : HasProjectiveDimensionLT (FiniteInjectivePresentation.family M i)
        (complementCard (S := S) i.1 + 1) := hp
    exact hasProjectiveDimensionLT_of_ge _ _ _
      (Nat.succ_le_succ (FiniteInjectiveRankDimension.complementCard_le_maxComplementCard
        (S := S) i.1))
  letI : HasProjectiveDimensionLT
      (FiniteInjectivePresentation.module M)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S) + 1) := by
    change HasProjectiveDimensionLT
      (⨁ fun i : I => FiniteInjectivePresentation.family M i)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S) + 1)
    exact hsum
  exact (show Retract M (FiniteInjectivePresentation.module M) from
    ⟨FiniteInjectivePresentation.embedding M,
      FiniteInjectivePresentation.retraction M,
      FiniteInjectivePresentation.embedding_retraction M⟩).hasProjectiveDimensionLT _

private def UniformBound (d : ℕ) : Prop :=
  ∀ (M : PModule.{u,0,u} k S), [∀ p, FiniteDimensional k (M.obj p)] →
    HasProjectiveDimensionLE M d

private theorem uniformBound_improve {d : ℕ}
    (hD : FiniteInjectiveRankDimension.maxComplementCard (S := S) ≤ d)
    (hU : UniformBound (k := k) (S := S) (d + 1)) :
    UniformBound (k := k) (S := S) d := by
  intro M hM
  letI : ∀ p, FiniteDimensional k (M.obj p) := hM
  let Q := TwoInjectivePresentation.quotient M
  letI : ∀ p, FiniteDimensional k (Q.obj p) :=
    TwoInjectivePresentation.quotient_finiteDimensional M
  let R := TwoInjectivePresentation.cokernelRow M
  have hrow := pointwiseShortExact_toShortExact (k := k) R
  have hI : HasProjectiveDimensionLE (TwoInjectivePresentation.firstInjective M)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S)) :=
    injective_hasProjectiveDimensionLE_of_max (k := k)
      (TwoInjectivePresentation.firstInjective M)
  letI : HasProjectiveDimensionLT (TwoInjectivePresentation.firstInjective M)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S) + 1) := hI
  have hI' : HasProjectiveDimensionLT (TwoInjectivePresentation.firstInjective M) (d + 1) :=
    hasProjectiveDimensionLT_of_ge _ _ _ (Nat.succ_le_succ hD)
  have hQ : HasProjectiveDimensionLE Q (d + 1) := hU Q
  letI : HasProjectiveDimensionLT Q (d + 2) := hQ
  exact hrow.hasProjectiveDimensionLT_X₁ (d + 1) hI' inferInstance

private theorem uniformBound_descend (q : ℕ) :
    UniformBound (k := k) (S := S)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S) + q) →
    UniformBound (k := k) (S := S)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S)) := by
  induction q with
  | zero => simpa
  | succ q ih =>
      intro h
      have h' : UniformBound (k := k) (S := S)
          ((FiniteInjectiveRankDimension.maxComplementCard (S := S) + q) + 1) := by
        simpa [Nat.add_assoc] using h
      have hstep := uniformBound_improve (k := k) (S := S)
        (d := FiniteInjectiveRankDimension.maxComplementCard (S := S) + q)
        (by omega) h'
      exact ih hstep

/-- Every pointwise finite-dimensional persistence module over a finite
bounded lattice has ordinary projective dimension at most the maximum
complement cardinality. -/
theorem hasProjectiveDimensionLE
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)] :
    HasProjectiveDimensionLE M (FiniteInjectiveRankDimension.maxComplementCard (S := S)) := by
  let N := 3 * Fintype.card S + 2
  have hfinite : UniformBound (k := k) (S := S) N := by
    intro X hX
    letI : ∀ p, FiniteDimensional k (X.obj p) := hX
    obtain ⟨R, hlen⟩ :=
      TDA.Persistence.FiniteRankProjectiveResolution.exists_finiteRankProjectiveResolution_with_recorded_length
      (k := k) X hX
    have hR := finiteRankProjectiveResolution_hasProjectiveDimensionLE (k := k) R
    simpa [N, hlen] using hR
  have hlift : UniformBound (k := k) (S := S)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S) + N) := by
    intro X hX
    letI : ∀ p, FiniteDimensional k (X.obj p) := hX
    letI : HasProjectiveDimensionLT X (N + 1) := hfinite X
    exact hasProjectiveDimensionLT_of_ge X (N + 1)
      (FiniteInjectiveRankDimension.maxComplementCard (S := S) + N + 1) (by omega)
  exact uniformBound_descend (k := k) (S := S) N hlift M

/-- Every pointwise finite-dimensional representation on an actual finite
coordinate grid has ordinary projective dimension at most the number of axes. -/
theorem hasProjectiveDimensionLE_coordinateGrid
    {n : ℕ} (G : CoordinateGrid n) (hG : ∀ i : Fin n, (G i).Nonempty)
    (M : PModule.{u,0,u} k G.Point) [∀ p, FiniteDimensional k (M.obj p)] :
    letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
    HasProjectiveDimensionLE M n := by
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  have hcount := maxComplementCard_coordinateGrid_le G hG
  letI : HasProjectiveDimensionLT M (FiniteInjectiveRankDimension.maxComplementCard
      (S := G.Point) + 1) := hasProjectiveDimensionLE (k := k) M
  exact hasProjectiveDimensionLT_of_ge M _ _ (Nat.succ_le_succ hcount)

/-- Every pointwise finite-dimensional representation on the actual interval
pair poset of a grid has ordinary projective dimension at most twice the number
of axes. -/
theorem hasProjectiveDimensionLE_pairCoordinateGrid
    {n : ℕ} (G : CoordinateGrid n) (hn : 1 ≤ n)
    (hG : ∀ i : Fin n, (G i).Nonempty)
    (M : PModule.{u,0,u} k (FiniteRankProjectiveEndAlgebra.PairPoset G.Point))
    [∀ p, FiniteDimensional k (M.obj p)] :
    letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
    letI : Lattice (FiniteRankProjectiveEndAlgebra.PairPoset G.Point) :=
      pairPosetLattice (S := G.Point)
    letI : BoundedOrder (FiniteRankProjectiveEndAlgebra.PairPoset G.Point) :=
      pairPosetBoundedOrder (S := G.Point)
    HasProjectiveDimensionLE M (2 * n) := by
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  letI : Lattice (FiniteRankProjectiveEndAlgebra.PairPoset G.Point) :=
    pairPosetLattice (S := G.Point)
  letI : BoundedOrder (FiniteRankProjectiveEndAlgebra.PairPoset G.Point) :=
    pairPosetBoundedOrder (S := G.Point)
  have hcount := maxComplementCard_pair_coordinateGrid_le G hn hG
  letI : HasProjectiveDimensionLT M (FiniteInjectiveRankDimension.maxComplementCard
      (S := FiniteRankProjectiveEndAlgebra.PairPoset G.Point) + 1) :=
    hasProjectiveDimensionLE (k := k) M
  exact hasProjectiveDimensionLT_of_ge M _ _ (Nat.succ_le_succ hcount)

end

end TDA.Persistence.OrdinaryFiniteLatticeDimension
