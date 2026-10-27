import TDA.Persistence.IncidenceQuotientSimple
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.FiniteLength

/-
The finite-length extension argument adapts the quotient-specific part of
`ModuleCat.hasProjectiveDimensionLT_of_isFiniteLength` in TauCeti's
`TauCeti/Algebra/Category/ModuleCat/Projective/Dimension.lean`, revision
7b0d106bf79dbea38ba8819985bd029989181287. Copyright (c) 2026 The Tau Ceti
contributors; Apache-2.0. This file specializes that proof pattern to the actual
diagonal quotient and its #699 simple-module classification; it adds no dependency.
-/

/-!
# Projective dimensions of finite-length quotient modules

For the actual right modules over the diagonal quotient, finite length reduces
projective-dimension bounds to the strict-vertex simples. The proof uses the
simple-module classification for this quotient and Mathlib's Ext criterion for
projective dimension.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceQuotientDimension

open CategoryTheory
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientSimple

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
local instance : Fintype (ComparablePair S) := Fintype.ofFinite _

local instance diagonalIdealTwoSided :
    (IncidenceQuotientSimple.DiagonalIdeal (k := k) (S := S)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := S)

private theorem finiteLength_bound_of_vertex_modules
    (n : ℕ)
    (hvertex : ∀ v : StrictVertex S,
      HasProjectiveDimensionLT (RightVertexModule (k := k) (S := S) v) n)
    (M : ModuleCat.{u} (RightQuotient (k := k) (S := S)))
    (hM : IsFiniteLength (RightQuotient (k := k) (S := S)) M) :
    HasProjectiveDimensionLT M n := by
  let C := RightQuotient (k := k) (S := S)
  suffices h : ∀ (M : Type u) [AddCommGroup M] [Module C M],
      IsFiniteLength C M → HasProjectiveDimensionLT (ModuleCat.of C M) n by
    exact h M.carrier hM
  intro M _ _ hM
  induction hM with
  | @of_subsingleton M _ _ hsub =>
    letI : Subsingleton M := hsub
    have hzero : Limits.IsZero (ModuleCat.of C M) := ModuleCat.isZero_of_subsingleton _
    letI : HasProjectiveDimensionLT (ModuleCat.of C M) 0 :=
      hzero.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 n (Nat.zero_le n)
  | @of_simple_quotient M _ _ N _ _ ih =>
    let T : ShortComplex (ModuleCat C) :=
      ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ) (by
        ext x
        exact (LinearMap.exact_subtype_mkQ N).apply_apply_eq_zero x)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
      (LinearMap.exact_subtype_mkQ N) N.injective_subtype N.mkQ_surjective
    let Q : ModuleCat C := ModuleCat.of C (M ⧸ N)
    letI : IsSimpleModule C (M ⧸ N) := inferInstance
    obtain ⟨v, ⟨e⟩, _⟩ :=
      simpleModule_existsUnique_vertex (k := k) (S := S) Q
    letI : HasProjectiveDimensionLT (RightVertexModule (k := k) (S := S) v) n :=
      hvertex v
    exact hT.hasProjectiveDimensionLT_X₂ n ih
      (hasProjectiveDimensionLT_of_iso e.symm n)

/-- A common Ext-vanishing degree for the actual strict-vertex modules bounds every
finite-length right module over the diagonal quotient. -/
theorem hasProjectiveDimensionLT_of_vertex_bound
    (n : ℕ)
    (hvertex : ∀ v : StrictVertex S,
      HasProjectiveDimensionLT (RightVertexModule (k := k) (S := S) v) n)
    (M : ModuleCat.{u} (RightQuotient (k := k) (S := S)))
    (hM : IsFiniteLength (RightQuotient (k := k) (S := S)) M) :
    HasProjectiveDimensionLT M n :=
  finiteLength_bound_of_vertex_modules n hvertex M hM

/-- A common natural projective-dimension bound on the strict-vertex modules
bounds every finite-length right quotient module. -/
theorem hasProjectiveDimensionLE_of_vertex_bound
    (d : ℕ)
    (hvertex : ∀ v : StrictVertex S,
      HasProjectiveDimensionLE (RightVertexModule (k := k) (S := S) v) d)
    (M : ModuleCat.{u} (RightQuotient (k := k) (S := S)))
    (hM : IsFiniteLength (RightQuotient (k := k) (S := S)) M) :
    HasProjectiveDimensionLE M d := by
  change HasProjectiveDimensionLT M (d + 1)
  exact hasProjectiveDimensionLT_of_vertex_bound (k := k) (S := S) (d + 1)
    hvertex M hM

/-- Every strict-vertex module is finite length, because it is simple. -/
theorem rightVertexModule_isFiniteLength (v : StrictVertex S) :
    IsFiniteLength (RightQuotient (k := k) (S := S))
      (RightVertexModule (k := k) (S := S) v) := by
  let M := RightVertexModule (k := k) (S := S) v
  letI : IsSimpleModule (RightQuotient (k := k) (S := S)) M :=
    rightVertexModule_isSimpleModule (k := k) (S := S) v
  have hbot : IsCoatom (⊥ : Submodule (RightQuotient (k := k) (S := S)) M) :=
    isSimpleOrder_iff_isCoatom_bot.mp inferInstance
  letI : IsSimpleModule (RightQuotient (k := k) (S := S))
      (M ⧸ (⊥ : Submodule (RightQuotient (k := k) (S := S)) M)) :=
    isSimpleModule_iff_isCoatom.mpr hbot
  exact IsFiniteLength.of_simple_quotient (N := (⊥ : Submodule _ M))
    IsFiniteLength.of_subsingleton

/-- The arbitrary-field inequality: the projective dimension of a finite-length
right quotient module is at most the supremum of the actual vertex dimensions. -/
theorem projectiveDimension_le_iSup_vertex
    (M : ModuleCat.{u} (RightQuotient (k := k) (S := S)))
    (hM : IsFiniteLength (RightQuotient (k := k) (S := S)) M) :
    projectiveDimension M ≤
      ⨆ v : StrictVertex S,
        projectiveDimension (RightVertexModule (k := k) (S := S) v) := by
  let D : WithBot ℕ∞ :=
    ⨆ v : StrictVertex S,
      projectiveDimension (RightVertexModule (k := k) (S := S) v)
  change projectiveDimension M ≤ D
  unfold CategoryTheory.projectiveDimension
  apply sInf_le
  simp only [Set.mem_ofPred_eq]
  intro i hi
  apply hasProjectiveDimensionLT_of_vertex_bound (k := k) (S := S) i _ M hM
  intro v
  apply (CategoryTheory.projectiveDimension_lt_iff).mp
  exact (le_iSup
    (fun v : StrictVertex S =>
      projectiveDimension (RightVertexModule (k := k) (S := S) v)) v).trans_lt hi

/-- A uniform natural bound on the vertex modules is equivalent to the same bound
for every finite-length right module over the quotient. -/
theorem finiteLength_uniform_projectiveDimensionLE_iff (d : ℕ) :
    (∀ M : ModuleCat.{u} (RightQuotient (k := k) (S := S)),
      IsFiniteLength (RightQuotient (k := k) (S := S)) M →
        HasProjectiveDimensionLE M d) ↔
    (∀ v : StrictVertex S,
      HasProjectiveDimensionLE (RightVertexModule (k := k) (S := S) v) d) := by
  constructor
  · intro h v
    exact h _ (rightVertexModule_isFiniteLength (k := k) (S := S) v)
  · intro h M hM
    exact hasProjectiveDimensionLE_of_vertex_bound (k := k) (S := S) d h M hM

/-- A quotient module finite-dimensional under its actual restricted `k`-action has finite length
over the quotient. -/
theorem isFiniteLength_of_finiteDimensional
    (M : ModuleCat.{u} (RightQuotient (k := k) (S := S)))
    (hM : FiniteDimensional k
      (restrictRightQuotientModule (k := k) (S := S) M)) :
    IsFiniteLength (RightQuotient (k := k) (S := S)) M := by
  let C := RightQuotient (k := k) (S := S)
  letI : Module k M := (restrictRightQuotientModule (k := k) (S := S) M).isModule
  letI : IsScalarTower k C M := IsScalarTower.of_compHom k C M
  have hfinite : FiniteDimensional k M := hM
  letI : FiniteDimensional k M := hfinite
  have hNoetherian : IsNoetherian k M := inferInstance
  have hArtinian : IsArtinian k M := inferInstance
  letI : IsNoetherian C M := isNoetherian_of_tower k hNoetherian
  letI : IsArtinian C M := isArtinian_of_tower k hArtinian
  exact (isFiniteLength_iff_isNoetherian_isArtinian (R := C) (M := M)).2
    ⟨inferInstance, inferInstance⟩

/-- Each actual vertex module is one-dimensional over the field after restriction
along the existing quotient scalar action. -/
theorem rightVertexModule_finiteDimensional (v : StrictVertex S) :
    FiniteDimensional k
      (restrictRightQuotientModule (k := k) (S := S)
        (RightVertexModule (k := k) (S := S) v)) := by
  exact ((rightVertexModule_restrictKIso (k := k) (S := S) v).symm.toLinearEquiv).finiteDimensional

/-- The dimension inequality also applies to every module finite-dimensional over
the underlying restricted `k`-module. -/
theorem projectiveDimension_le_iSup_vertex_of_finiteDimensional
    (M : ModuleCat.{u} (RightQuotient (k := k) (S := S)))
    (hM : FiniteDimensional k
      (restrictRightQuotientModule (k := k) (S := S) M)) :
    projectiveDimension M ≤
      ⨆ v : StrictVertex S,
        projectiveDimension (RightVertexModule (k := k) (S := S) v) :=
  projectiveDimension_le_iSup_vertex (k := k) (S := S) M
    (isFiniteLength_of_finiteDimensional (k := k) (S := S) M hM)

/-- A uniform natural bound on all finite-dimensional right quotient modules is
equivalent to that bound on the actual strict-vertex modules. -/
theorem finiteDimensional_uniform_projectiveDimensionLE_iff (d : ℕ) :
    (∀ M : ModuleCat.{u} (RightQuotient (k := k) (S := S)),
      FiniteDimensional k (restrictRightQuotientModule (k := k) (S := S) M) →
        HasProjectiveDimensionLE M d) ↔
    (∀ v : StrictVertex S,
      HasProjectiveDimensionLE (RightVertexModule (k := k) (S := S) v) d) := by
  constructor
  · intro h v
    exact h _ (rightVertexModule_finiteDimensional (k := k) (S := S) v)
  · intro h M hM
    exact hasProjectiveDimensionLE_of_vertex_bound (k := k) (S := S) d h M
      (isFiniteLength_of_finiteDimensional (k := k) (S := S) M hM)

end

end TDA.Persistence.IncidenceQuotientDimension
