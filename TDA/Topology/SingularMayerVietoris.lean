import TDA.Topology.SmallChains
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# The algebraic core of singular Mayer–Vietoris

A bicartesian square of subcomplexes `A₁ = A₂ ⊓ A₃`, `A₄ = A₂ ⊔ A₃` of a simplicial set gives a
pushout square of chain complexes (`isPushout_chainComplex`): in each degree, the chains are
`sigmaConst.obj R` applied to a pushout of sets of simplices. For a pushout square
`t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, `b : X₃ ⟶ X₄` in an abelian category,
`mvShortComplex h` is the short complex

`X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄`, with first map `(t, -l)` and second map the sum `(r, b)`,

and `shortExact_mvShortComplex` shows that it is short exact when `t` is a monomorphism. For
small singular chains (`TDA.Topology.SmallChains`), `shortExact_smallChains` is the short exact
sequence `0 → C(s ∩ t) → C(s) ⊞ C(t) → C^small(s, t) → 0`, for arbitrary subsets `s` and `t` of
a space and coefficients `R` in any abelian category with coproducts.

`bicartδ R sq n : H_{n+1}(A₄) ⟶ H_n(A₁)` is the connecting map of the homology sequence. Its
sign is fixed by Mathlib's snake lemma and is stated in `bicartδ_eq` (generally in
`mvShortComplex_δ_eq`): if a cycle of `A₄` is `z = a + b` with `a` a chain of `A₂` and `b` a
chain of `A₃`, and `x` is the chain of `A₁` whose image in `A₂` is `∂a`, then `δ[z] = [x]`.
Exchanging the two pieces negates the connecting map (`bicartδ_flip`, `mvShortComplex_δ_flip`),
and `bicartδ_naturality` is naturality for morphisms of bicartesian squares.

This is the algebraic part of the singular Mayer–Vietoris sequence. The comparison of small
chains with all singular chains rests on the iteration criterion `quasiIso_of_iterate_mem` of
`TDA.Topology.QuasiIsoOfIterate`.
-/

open CategoryTheory Limits AlgebraicTopology Opposite HomologicalComplex
open scoped Simplicial

universe u

namespace TDA.Topology

section Pushout

variable {C : Type*} [Category C] [HasCoproducts.{u} C] [Preadditive C] (R : C)

/-- A bicartesian square of subcomplexes gives a pushout square of chain complexes. -/
theorem isPushout_chainComplex {X : SSet.{u}} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) :
    IsPushout (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₂) R)
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₃) R)
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₂₄) R)
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₃₄) R) := by
  have w : SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₂) R ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₂₄) R =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₃) R ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₃₄) R := by
    simp only [SSet.chainComplexMap, ← Functor.map_comp]
    rfl
  refine ⟨⟨w⟩, ⟨HomologicalComplex.isColimitOfEval _ _ fun n => ?_⟩⟩
  have h := (sq.isPushout.map ((evaluation _ _).obj (op ⦋n⦌))).map (sigmaConst.obj R)
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2 h.isColimit

end Pushout

section ShortExact

variable {A : Type*} [Category A] [Abelian A]

/-- The Mayer–Vietoris short complex `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄` of a pushout square, with maps `(t, -l)`
and `(r, b)`. It is reducible, so its objects are syntactically the corners. -/
noncomputable abbrev mvShortComplex {X₁ X₂ X₃ X₄ : A} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (h : IsPushout t l r b) : ShortComplex A :=
  ShortComplex.mk (biprod.lift t (-l)) (biprod.desc r b) (by simp [h.w])

/-- A pushout square with a monomorphic top edge gives a short exact sequence. -/
theorem shortExact_mvShortComplex {X₁ X₂ X₃ X₄ : A} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (h : IsPushout t l r b) [Mono t] :
    (mvShortComplex h).ShortExact where
  exact := h.exact_shortComplex
  mono_f := mono_of_mono_fac (biprod.lift_fst t (-l))
  epi_g := h.epi_shortComplex_g

end ShortExact

section SmallChains

variable {C : Type*} [Category C] [Abelian C] [HasCoproducts.{u} C] (R : C)

/-- The square `simplicesIn (s ∩ t) ≤ simplicesIn s, simplicesIn t ≤ smallSimplices s t` is
bicartesian. -/
theorem bicartSq_simplicesIn {Y : TopCat.{u}} (s t : Set Y) :
    SSet.Subcomplex.BicartSq (simplicesIn (s ∩ t)) (simplicesIn s) (simplicesIn t)
      (smallSimplices s t) :=
  ⟨rfl, (simplicesIn_inter s t).symm⟩

/-- The Mayer–Vietoris pushout square of small chains. -/
theorem isPushout_smallChains {Y : TopCat.{u}} (s t : Set Y) :
    IsPushout (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (bicartSq_simplicesIn s t).le₁₂) R)
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (bicartSq_simplicesIn s t).le₁₃) R)
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (bicartSq_simplicesIn s t).le₂₄) R)
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (bicartSq_simplicesIn s t).le₃₄) R) :=
  isPushout_chainComplex R (bicartSq_simplicesIn s t)

/-- **Short exactness of small chains**, for arbitrary subsets `s` and `t`:
`0 → C(s ∩ t) → C(s) ⊞ C(t) → C^small(s, t) → 0`, with first map `(inc_s, -inc_t)` and second
map the sum. -/
theorem shortExact_smallChains {Y : TopCat.{u}} (s t : Set Y) :
    (mvShortComplex (isPushout_smallChains R s t)).ShortExact :=
  shortExact_mvShortComplex (isPushout_smallChains R s t)

end SmallChains

section Connecting

variable {A : Type*} [Category A] [Abelian A] {ι : Type*} {c : ComplexShape ι}

/-- Two morphisms into a degree of a binary biproduct of complexes agree when their two
projections agree. -/
private theorem biprod_X_hom_ext {X₂ X₃ : HomologicalComplex A c} {W : A} {i : ι}
    {f g : W ⟶ (X₂ ⊞ X₃).X i}
    (h₁ : f ≫ (biprod.fst : X₂ ⊞ X₃ ⟶ X₂).f i = g ≫ (biprod.fst : X₂ ⊞ X₃ ⟶ X₂).f i)
    (h₂ : f ≫ (biprod.snd : X₂ ⊞ X₃ ⟶ X₃).f i = g ≫ (biprod.snd : X₂ ⊞ X₃ ⟶ X₃).f i) :
    f = g := by
  have e : (biprod.fst : X₂ ⊞ X₃ ⟶ X₂).f i ≫ (biprod.inl : X₂ ⟶ X₂ ⊞ X₃).f i +
      (biprod.snd : X₂ ⊞ X₃ ⟶ X₃).f i ≫ (biprod.inr : X₃ ⟶ X₂ ⊞ X₃).f i = 𝟙 _ := by
    rw [← comp_f, ← comp_f, ← add_f_apply, biprod.total, id_f]
  rw [← Category.comp_id f, ← Category.comp_id g, ← e]
  simp only [Preadditive.comp_add, reassoc_of% h₁, reassoc_of% h₂]

/-- **The sign of the Mayer–Vietoris connecting map.** Let `z = a + b` be an `i`-cycle of `X₄`,
with `a` from `X₂` and `b` from `X₃` (as generalized elements `W ⟶ _`), and let `x` be a chain of
`X₁` whose image in `X₂` is `∂a`. Then the connecting map sends the class of `z` to the class
of `x`. -/
theorem mvShortComplex_δ_eq {X₁ X₂ X₃ X₄ : HomologicalComplex A c}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (h : IsPushout t l r b) [Mono t]
    (i j : ι) (hij : c.Rel i j) {W : A} (a : W ⟶ X₂.X i) (b' : W ⟶ X₃.X i)
    (hz : (a ≫ r.f i + b' ≫ b.f i) ≫ X₄.d i j = 0)
    (x : W ⟶ X₁.X j) (hx : x ≫ t.f j = a ≫ X₂.d i j) (k : ι) (hk : c.next j = k) :
    X₄.liftCycles (a ≫ r.f i + b' ≫ b.f i) j (c.next_eq' hij) hz ≫ X₄.homologyπ i ≫
        (shortExact_mvShortComplex h).δ i j hij =
      X₁.liftCycles x k hk (by
        rw [← cancel_mono (t.f k), Category.assoc, ← t.comm, reassoc_of% hx, d_comp_d,
          Limits.comp_zero, Limits.zero_comp]) ≫ X₁.homologyπ j := by
  have hb : Mono b := Abelian.mono_inr_of_isColimit t l h.isColimit
  have hbj : Mono (b.f j) := inferInstance
  let x₂ : W ⟶ (X₂ ⊞ X₃).X i :=
    a ≫ (biprod.inl : X₂ ⟶ X₂ ⊞ X₃).f i + b' ≫ (biprod.inr : X₃ ⟶ X₂ ⊞ X₃).f i
  have hx₂ : x₂ ≫ (mvShortComplex h).g.f i = a ≫ r.f i + b' ≫ b.f i := by
    simp only [x₂, Preadditive.add_comp, Category.assoc, ← comp_f, biprod.inl_desc,
      biprod.inr_desc]
  have hl : x ≫ l.f j = -(b' ≫ X₃.d i j) := by
    rw [← cancel_mono (b.f j), Category.assoc, ← comp_f, ← h.w, comp_f, reassoc_of% hx,
      Preadditive.neg_comp, Category.assoc, ← r.comm, ← b.comm, eq_neg_iff_add_eq_zero]
    simpa only [Preadditive.add_comp, Category.assoc] using hz
  have hx₁ : x ≫ (mvShortComplex h).f.f j = x₂ ≫ (X₂ ⊞ X₃).d i j := by
    apply biprod_X_hom_ext
    · simp only [x₂, Preadditive.add_comp, Category.assoc, Hom.comm_assoc]
      simp only [← comp_f, biprod.lift_fst, biprod.inl_fst, biprod.inr_fst, id_f, zero_f,
        Category.comp_id, Limits.comp_zero, add_zero, hx]
    · simp only [x₂, Preadditive.add_comp, Category.assoc, Hom.comm_assoc]
      simp only [← comp_f, biprod.lift_snd, biprod.inl_snd, biprod.inr_snd, id_f, zero_f,
        Category.comp_id, Limits.comp_zero, zero_add, neg_f_apply, Preadditive.comp_neg, hl,
        neg_neg]
  exact (shortExact_mvShortComplex h).δ_eq i j hij _ hz x₂ hx₂ x hx₁ k hk

/-- The comparison of a pushout square with its flip: `-𝟙`, the braiding and `𝟙`. -/
private noncomputable def flipHom {X₁ X₂ X₃ X₄ : A}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (h : IsPushout t l r b) :
    mvShortComplex h ⟶ mvShortComplex h.flip where
  τ₁ := -𝟙 X₁
  τ₂ := biprod.lift biprod.snd biprod.fst
  τ₃ := 𝟙 X₄
  comm₁₂ := by apply biprod.hom_ext <;> simp
  comm₂₃ := by apply biprod.hom_ext' <;> simp

/-- **Sign reversal.** Exchanging the two pieces of a pushout square negates the connecting
map. -/
theorem mvShortComplex_δ_flip {X₁ X₂ X₃ X₄ : HomologicalComplex A c}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (h : IsPushout t l r b)
    [Mono t] [Mono l] (i j : ι) (hij : c.Rel i j) :
    (shortExact_mvShortComplex h.flip).δ i j hij = -(shortExact_mvShortComplex h).δ i j hij := by
  have e := HomologySequence.δ_naturality (flipHom h) (shortExact_mvShortComplex h)
    (shortExact_mvShortComplex h.flip) i j hij
  simp only [flipHom, homologyMap_neg, homologyMap_id, Preadditive.comp_neg, Category.comp_id,
    Category.id_comp] at e
  exact e.symm

end Connecting

section Bicart

variable {C : Type*} [Category C] [Abelian C] [HasCoproducts.{u} C] (R : C)

/-- The flipped square `A₁ ≤ A₃, A₂ ≤ A₄` of a bicartesian square is bicartesian. -/
theorem bicartSq_flip {X : SSet.{u}} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) : SSet.Subcomplex.BicartSq A₁ A₃ A₂ A₄ :=
  ⟨by rw [sup_comm, sq.sup_eq], by rw [inf_comm, sq.inf_eq]⟩

/-- Short exactness of chains for any bicartesian square of subcomplexes. -/
theorem shortExact_of_bicartSq {X : SSet.{u}} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) :
    (mvShortComplex (isPushout_chainComplex R sq)).ShortExact :=
  shortExact_mvShortComplex (isPushout_chainComplex R sq)

/-- The connecting map `H_{n+1}(A₄) ⟶ H_n(A₁)` of a bicartesian square of subcomplexes. -/
noncomputable def bicartδ {X : SSet.{u}} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) (n : ℕ) :
    ((A₄ : SSet.{u}).chainComplex R).homology (n + 1) ⟶
      ((A₁ : SSet.{u}).chainComplex R).homology n :=
  (shortExact_of_bicartSq R sq).δ (n + 1) n rfl

/-- **The sign of `bicartδ`.** If an `(n + 1)`-cycle of `A₄` is `z = a + b` with `a` a chain of
`A₂` and `b` a chain of `A₃`, and `x` is the `n`-chain of `A₁` whose image in `A₂` is `∂a`, then
`bicartδ` sends the class of `z` to the class of `x`. -/
theorem bicartδ_eq {X : SSet.{u}} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) (n : ℕ) {W : C}
    (a : W ⟶ ((A₂ : SSet.{u}).chainComplex R).X (n + 1))
    (b : W ⟶ ((A₃ : SSet.{u}).chainComplex R).X (n + 1))
    (hz : (a ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₂₄) R).f (n + 1) +
        b ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₃₄) R).f (n + 1)) ≫
        ((A₄ : SSet.{u}).chainComplex R).d (n + 1) n = 0)
    (x : W ⟶ ((A₁ : SSet.{u}).chainComplex R).X n)
    (hx : x ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₂) R).f n =
      a ≫ ((A₂ : SSet.{u}).chainComplex R).d (n + 1) n)
    (k : ℕ) (hk : (ComplexShape.down ℕ).next n = k) :
    ((A₄ : SSet.{u}).chainComplex R).liftCycles
        (a ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₂₄) R).f (n + 1) +
          b ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₃₄) R).f (n + 1)) n
        (by simp) hz ≫
        ((A₄ : SSet.{u}).chainComplex R).homologyπ (n + 1) ≫ bicartδ R sq n =
      ((A₁ : SSet.{u}).chainComplex R).liftCycles x k hk (by
        rw [← cancel_mono ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₂) R).f k),
          Category.assoc, ← Hom.comm, reassoc_of% hx, d_comp_d, Limits.comp_zero,
          Limits.zero_comp]) ≫
        ((A₁ : SSet.{u}).chainComplex R).homologyπ n :=
  mvShortComplex_δ_eq (isPushout_chainComplex R sq) (n + 1) n rfl a b hz x hx k hk

/-- Swapping the two pieces negates `bicartδ`, for all coefficients. -/
theorem bicartδ_flip {X : SSet.{u}} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) (n : ℕ) :
    bicartδ R (bicartSq_flip sq) n = -bicartδ R sq n :=
  mvShortComplex_δ_flip (isPushout_chainComplex R sq) (n + 1) n rfl

/-- **Naturality** of `bicartδ` for a morphism of bicartesian squares: simplicial maps
`φᵢ : Aᵢ ⟶ Aᵢ'` commuting with the four inclusions. -/
theorem bicartδ_naturality {X X' : SSet.{u}} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    {A₁' A₂' A₃' A₄' : X'.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) (sq' : SSet.Subcomplex.BicartSq A₁' A₂' A₃' A₄')
    (φ₁ : (A₁ : SSet.{u}) ⟶ A₁') (φ₂ : (A₂ : SSet.{u}) ⟶ A₂') (φ₃ : (A₃ : SSet.{u}) ⟶ A₃')
    (φ₄ : (A₄ : SSet.{u}) ⟶ A₄')
    (h₁₂ : φ₁ ≫ SSet.Subcomplex.homOfLE sq'.le₁₂ = SSet.Subcomplex.homOfLE sq.le₁₂ ≫ φ₂)
    (h₁₃ : φ₁ ≫ SSet.Subcomplex.homOfLE sq'.le₁₃ = SSet.Subcomplex.homOfLE sq.le₁₃ ≫ φ₃)
    (h₂₄ : φ₂ ≫ SSet.Subcomplex.homOfLE sq'.le₂₄ = SSet.Subcomplex.homOfLE sq.le₂₄ ≫ φ₄)
    (h₃₄ : φ₃ ≫ SSet.Subcomplex.homOfLE sq'.le₃₄ = SSet.Subcomplex.homOfLE sq.le₃₄ ≫ φ₄)
    (n : ℕ) :
    bicartδ R sq n ≫ homologyMap (SSet.chainComplexMap φ₁ R) n =
      homologyMap (SSet.chainComplexMap φ₄ R) (n + 1) ≫ bicartδ R sq' n := by
  let ψ : mvShortComplex (isPushout_chainComplex R sq) ⟶
      mvShortComplex (isPushout_chainComplex R sq') :=
    { τ₁ := SSet.chainComplexMap φ₁ R
      τ₂ := biprod.map (SSet.chainComplexMap φ₂ R) (SSet.chainComplexMap φ₃ R)
      τ₃ := SSet.chainComplexMap φ₄ R
      comm₁₂ := by
        apply biprod.hom_ext
        · simp [SSet.chainComplexMap, ← Functor.map_comp, h₁₂]
        · simp [SSet.chainComplexMap, ← Functor.map_comp, h₁₃]
      comm₂₃ := by
        apply biprod.hom_ext'
        · simp [SSet.chainComplexMap, ← Functor.map_comp, h₂₄]
        · simp [SSet.chainComplexMap, ← Functor.map_comp, h₃₄] }
  exact HomologySequence.δ_naturality ψ (shortExact_of_bicartSq R sq)
    (shortExact_of_bicartSq R sq') (n + 1) n rfl

end Bicart

end TDA.Topology
