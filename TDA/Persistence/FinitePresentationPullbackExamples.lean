import TDA.Persistence.FinitePresentationPullback
import TDA.Persistence.FinitePresentationKanExamples

/-!
# Consumers of finite-presentation extension and pullback closure

The examples reuse the repeated-grade presentation with its genuine relation.
They check the ordinary extension theorem and the actual pullback/kernel row
over every field on the trivial row `0 → D → D`, then check the
empty-presentation zero case. The last example uses the non-split row
`0 → relations → generators → D → 0` given by the genuine relation, whose outer
terms are both nonzero. It applies the extension theorem and the pullback of
the quotient map along itself, which contains an off-diagonal pair.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FinitePresentationPullbackExamples

open CategoryTheory CategoryTheory.Limits GradedFree
open scoped ZeroObject

private def emptyGenerators (P : Type) : GradedGenerators.{0,0} P where
  Carrier := Empty
  grade := Empty.elim

private theorem zero_finitelyPresented {k : Type u} [Field k] {P : Type}
    [PartialOrder P] :
    FinitelyPresented.{u,0,0} (R := k) (P := P) (0 : PModule.{u,0,u} k P) := by
  let W : GradedGenerators.{0,0} P := emptyGenerators P
  letI : Finite W.Carrier := inferInstanceAs (Finite Empty)
  have hzero : IsZero (GradedFree.module (R := k) W) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply GradedFree.hom_ext_birth W
    intro g
    exact g.elim
  exact GradedFree.finitelyPresented_of_iso (GradedFree.free_finitelyPresented W)
    hzero.isoZero

private theorem identityQuotient_rankExact
    {k : Type u} [Field k] {P : Type} [PartialOrder P]
    {M : PModule.{u,0,u} k P}
    (hM : FinitelyPresented.{u,0,0} (R := k) (P := P) M) :
    IsRankExact (0 : (0 : PModule.{u,0,u} k P) ⟶ M) (𝟙 M) := by
  letI : ∀ p : P, FiniteDimensional k (M.obj p) :=
    fun p => GradedFree.finitelyPresented_finiteDimensional M hM p
  have hs : IsPointwiseShortExact (0 : (0 : PModule.{u,0,u} k P) ⟶ M) (𝟙 M) := by
    constructor
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p x
      exact ⟨x, rfl⟩
    · intro p
      simp
  exact hs.rankExact_of_section (𝟙 M) (by simp)

/-- The repeated-grade, genuinely related finite presentation supports the
ordinary extension theorem and the actual rank-exact pullback consumer over
every field. The resulting actual pullback has a nonzero fiber. -/
theorem arbitrary_field_repeated_extension_and_pullback
    {k : Type u} [Field k] :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (FinitePresentationKanExamples.presentation k 2).presented ∧
      FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (Limits.pullback (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)) ∧
      FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (Limits.kernel (Limits.pullback.snd
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented))) ∧
      IsRankExact
        (Limits.kernel.ι (Limits.pullback.snd
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)))
        (Limits.pullback.snd
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)) ∧
      ∃ x : (Limits.pullback
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)).obj
          ((FinitePresentationKanExamples.generators 2).grade (0 : Fin 2)),
        x ≠ 0 := by
  let D := FinitePresentationKanExamples.presentation k 2
  have hD : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ) D.presented :=
    D.finitelyPresented (FinitePresentationKanExamples.presentation_finite k 2)
  have hs : IsRankExact (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented)
      (𝟙 D.presented) := identityQuotient_rankExact hD
  have hMiddle := hs.toIsPointwiseShortExact.finitelyPresented_middle
    zero_finitelyPresented hD
  have hPullback := hs.pullback_finitelyPresented (𝟙 D.presented)
    zero_finitelyPresented hD
  let p := (FinitePresentationKanExamples.generators 2).grade (0 : Fin 2)
  let x := PullbackFiber.mk (𝟙 D.presented) (𝟙 D.presented) p
    (FinitePresentationKanExamples.secondValue k 2)
    (FinitePresentationKanExamples.secondValue k 2) (by simp)
  have hx : x ≠ 0 := by
    intro h
    have he := congrArg ((Limits.pullback.fst (𝟙 D.presented) (𝟙 D.presented)).app p).hom h
    have hz : FinitePresentationKanExamples.secondValue k 2 = 0 := by
      simpa [x, PullbackFiber.fst_mk] using he
    exact FinitePresentationKanExamples.surviving_generator 2 hz
  exact ⟨hMiddle, hPullback.1, hPullback.2.1, hPullback.2.2, ⟨x, hx⟩⟩

/-- An empty generator and relation family presents zero; its actual pullback
and canonical kernel row satisfy the same closure result. -/
theorem empty_zero_pullback_finitelyPresented {k : Type u} [Field k] :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (Limits.pullback (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))) ∧
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (Limits.kernel (Limits.pullback.snd
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ))))) ∧
    IsRankExact
      (Limits.kernel.ι (Limits.pullback.snd
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))))
      (Limits.pullback.snd
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))) := by
  have hzero : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := zero_finitelyPresented
  have hs := identityQuotient_rankExact hzero
  exact hs.pullback_finitelyPresented (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
    hzero hzero

private theorem generator_le_relation :
    (FinitePresentationKanExamples.generators 2).grade (0 : Fin 2) ≤
      (FinitePresentationKanExamples.relations 2).grade () := by
  intro i
  norm_num

/-- The relation map sends the relation generator to the first free generator. -/
private theorem relationMap_generator {k : Type u} [Field k] (p : Fin 2 → ℝ)
    (h : (FinitePresentationKanExamples.relations 2).grade () ≤ p) :
    (((FinitePresentationKanExamples.presentation k 2).relationMap.app p).hom
      (GradedFree.generator (R := k) (FinitePresentationKanExamples.relations 2) () h)).val =
      Finsupp.single (0 : Fin 2) (1 : k) := by
  have he := GradedFree.fiberLift_generator (R := k) (FinitePresentationKanExamples.relations 2) p
    (fun g => structureMapLinear (GradedFree.module (R := k) (FinitePresentationKanExamples.generators 2))
      g.property (GradedFree.generator (R := k) (FinitePresentationKanExamples.generators 2)
        (0 : Fin 2) generator_le_relation)) () h
  exact congrArg Subtype.val he

/-- The genuine relation map is injective at every grade. -/
private theorem relationMap_injective {k : Type u} [Field k] (p : Fin 2 → ℝ) :
    Function.Injective
      ((FinitePresentationKanExamples.presentation k 2).relationMap.app p).hom := by
  let D := FinitePresentationKanExamples.presentation k 2
  let Y := FinitePresentationKanExamples.relations 2
  let f₁ : GradedFree.fiber (R := k) Y p →ₗ[k] k :=
    (Finsupp.lapply (0 : Fin 2)) ∘ₗ
      (GradedFree.fiber (R := k) (FinitePresentationKanExamples.generators 2) p).subtype ∘ₗ
        (D.relationMap.app p).hom
  let f₂ : GradedFree.fiber (R := k) Y p →ₗ[k] k :=
    (Finsupp.lapply ()) ∘ₗ (GradedFree.fiber (R := k) Y p).subtype
  have h₁ := GradedFree.fiberLift_unique (R := k) Y p (fun _ => (1 : k)) f₁ (by
    intro g h
    cases g
    change (((D.relationMap.app p).hom (GradedFree.generator (R := k) Y () h)).val) (0 : Fin 2) = 1
    rw [relationMap_generator p h]
    exact Finsupp.single_eq_same)
  have h₂ := GradedFree.fiberLift_unique (R := k) Y p (fun _ => (1 : k)) f₂ (by
    intro g h
    cases g
    change (Finsupp.single () (1 : k)) () = 1
    rw [Finsupp.single_eq_same])
  intro x y hxy
  have hx := LinearMap.congr_fun (h₁.trans h₂.symm) x
  have hy := LinearMap.congr_fun (h₁.trans h₂.symm) y
  have hcoeff : x.val () = y.val () := by
    change f₂ x = f₂ y
    rw [← hx, ← hy]
    change ((D.relationMap.app p).hom x).val (0 : Fin 2) =
      ((D.relationMap.app p).hom y).val (0 : Fin 2)
    rw [hxy]
  apply Subtype.ext
  apply Finsupp.ext
  intro u
  cases u
  exact hcoeff

/-- The quotient by the genuine relation gives a non-split pointwise short
exact row `0 → relations → generators → presented → 0`. -/
private theorem relationRow_shortExact {k : Type u} [Field k] :
    IsPointwiseShortExact (FinitePresentationKanExamples.presentation k 2).relationMap
      (FinitePresentationKanExamples.presentation k 2).cover where
  injective := relationMap_injective
  surjective p := (FinitePresentationKanExamples.presentation k 2).cover_surjective p
  range_eq_ker p := by
    have h := (ShortComplex.exact_cokernel
      (FinitePresentationKanExamples.presentation k 2).relationMap).map_of_epi_of_preservesCokernel
        ((evaluation (Fin 2 → ℝ) (ModuleCat.{u} k)).obj p) inferInstance inferInstance
    exact h.moduleCat_range_eq_ker

/-- The extension and pullback closure theorems on the row given by the
genuine relation, whose outer terms are both nonzero. The ordinary extension
theorem recovers the free middle term. The actual pullback of the quotient map
along itself is finitely presented and, at the relation grade, contains a pair
with distinct coordinates: the first generator paired with zero. -/
theorem arbitrary_field_relation_row_extension_and_pullback {k : Type u} [Field k] :
    (FinitePresentationKanExamples.presentation k 2).relationMap ≠ 0 ∧
      (∃ x : (FinitePresentationKanExamples.presentation k 2).presented.obj
        ((FinitePresentationKanExamples.generators 2).grade (0 : Fin 2)), x ≠ 0) ∧
      FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (GradedFree.module (R := k) (FinitePresentationKanExamples.generators 2)) ∧
      FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (Limits.pullback (FinitePresentationKanExamples.presentation k 2).cover
          (FinitePresentationKanExamples.presentation k 2).cover) ∧
      ∃ x : (Limits.pullback (FinitePresentationKanExamples.presentation k 2).cover
          (FinitePresentationKanExamples.presentation k 2).cover).obj
          ((FinitePresentationKanExamples.relations 2).grade ()),
        ((Limits.pullback.fst (FinitePresentationKanExamples.presentation k 2).cover
            (FinitePresentationKanExamples.presentation k 2).cover).app
            ((FinitePresentationKanExamples.relations 2).grade ())).hom x ≠
          ((Limits.pullback.snd (FinitePresentationKanExamples.presentation k 2).cover
            (FinitePresentationKanExamples.presentation k 2).cover).app
            ((FinitePresentationKanExamples.relations 2).grade ())).hom x := by
  let D := FinitePresentationKanExamples.presentation k 2
  let Y := FinitePresentationKanExamples.relations 2
  let W := FinitePresentationKanExamples.generators 2
  have hs := relationRow_shortExact (k := k)
  have hY : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ) (GradedFree.module (R := k) Y) :=
    GradedFree.free_finitelyPresented Y
  have hW : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ) (GradedFree.module (R := k) W) :=
    GradedFree.free_finitelyPresented W
  have hD : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ) D.presented :=
    D.finitelyPresented (FinitePresentationKanExamples.presentation_finite k 2)
  let q := Y.grade ()
  let g : (GradedFree.module (R := k) D.generators).obj q :=
    GradedFree.generator (R := k) W (0 : Fin 2) generator_le_relation
  have hg : g ≠ 0 := by
    intro h
    have he := congrArg (fun z : (GradedFree.module (R := k) D.generators).obj q =>
      z.val (0 : Fin 2)) h
    change (Finsupp.single (0 : Fin 2) (1 : k)) 0 = 0 at he
    rw [Finsupp.single_eq_same] at he
    exact one_ne_zero he
  have hgdies : (D.cover.app q).hom g = (D.cover.app q).hom 0 := by
    rw [map_zero]
    have hv := congrArg (fun α : GradedFree.module (R := k) Y ⟶ D.presented =>
      (α.app q).hom (GradedFree.birth (R := k) Y ())) D.relations_vanish
    change (D.cover.app q).hom ((D.relationMap.app q).hom
      (GradedFree.generator (R := k) Y () le_rfl)) = 0 at hv
    have hr : (D.relationMap.app q).hom (GradedFree.generator (R := k) Y () le_rfl) = g :=
      Subtype.ext (relationMap_generator q le_rfl)
    rwa [hr] at hv
  refine ⟨FinitePresentationKanExamples.relation_nonzero k 2,
    ⟨FinitePresentationKanExamples.secondValue k 2,
      FinitePresentationKanExamples.surviving_generator 2⟩,
    hs.finitelyPresented_middle hY hD,
    hs.finitelyPresented_pullback D.cover hY hW, ?_⟩
  refine ⟨PullbackFiber.mk D.cover D.cover q g 0 hgdies, ?_⟩
  intro h
  have h₁ := PullbackFiber.fst_mk D.cover D.cover q g 0 hgdies
  have h₂ := PullbackFiber.snd_mk D.cover D.cover q g 0 hgdies
  exact hg (h₁.symm.trans (h.trans h₂))

end TDA.Persistence.FinitePresentationPullbackExamples
