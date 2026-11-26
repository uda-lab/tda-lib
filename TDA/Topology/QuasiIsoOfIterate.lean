import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Refinements
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# A quasi-isomorphism criterion by iterating a homotopic endomorphism

Let `i : A ⟶ B` be a monomorphism of complexes of modules over a ring `k`, and let `S : B ⟶ B` be
a chain map with a homotopy `T : S ≃ 𝟙`. Suppose that `S` and `T` carry chains of `A` to chains of
`A`, and that every chain of `B` is carried into `A` by some iterate `S^N`, where `N` may depend on
the chain. Then `quasiIso_of_iterate_mem` shows that `i` is a quasi-isomorphism.

This is the algebraic step of the small-chains theorem: there `A` is the complex of small
singular chains of a cover, `B` all singular chains, `S` barycentric subdivision and `T` its
homotopy to the identity.

The proof composes the homotopy with itself: `S^N ≃ 𝟙` by a homotopy `D_N` which, in each
degree, is `T ∘ (1 + S + ⋯ + S^{N-1})`, so that `S^N - 1 = ∂D_N + D_N∂` and `D_N` carries `A`
to `A`.

* Surjectivity on homology: a cycle `z` of `B` with `S^N z = a ∈ A` satisfies
  `z = a - ∂(D_N z)`, and `a` is a cycle of `A` because `i` is injective.
* Injectivity on homology: if a cycle `z` of `A` is a boundary `∂w` in `B`, choose `N` with
  `S^N w = b ∈ A`. Then `z = S^N z - ∂(D_N z) = ∂b - ∂(D_N z)`, with `b` and `D_N z` in `A`.

Both properties are checked on generalized elements through Mathlib's refinement criteria
`HomologicalComplex.epi_homologyMap_iff_up_to_refinements` and
`HomologicalComplex.mono_homologyMap_iff_up_to_refinements`, refining a module by the free module
on its underlying set. The complexes are indexed by an arbitrary `ComplexShape`; the modules
live in `ModuleCat.{u} k` for `k : Type u`.
-/

open CategoryTheory Limits HomologicalComplex

universe u

namespace TDA.Topology

namespace QuasiIsoOfIterate

variable {k : Type u} [Ring k]

/-- The free module on the underlying set of `W`. -/
private noncomputable abbrev freeCover (W : ModuleCat.{u} k) : ModuleCat.{u} k :=
  ModuleCat.of k (W →₀ k)

/-- The linear extension of a map of sets out of `W`, defined on `freeCover W`. -/
private noncomputable def freeLift {W M : ModuleCat.{u} k} (g : W → M) : freeCover W ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination k g)

@[simp]
private theorem freeLift_single {W M : ModuleCat.{u} k} (g : W → M) (w : W) :
    (freeLift g).hom (Finsupp.single w 1) = g w := by
  simp [freeLift]

/-- The canonical epimorphism from the free module on `W` to `W`. -/
private noncomputable def freeCoverπ (W : ModuleCat.{u} k) : freeCover W ⟶ W :=
  freeLift id

@[simp]
private theorem freeCoverπ_single (W : ModuleCat.{u} k) (w : W) :
    (freeCoverπ W).hom (Finsupp.single w 1) = w :=
  freeLift_single _ w

private theorem epi_freeCoverπ (W : ModuleCat.{u} k) : Epi (freeCoverπ W) :=
  (ModuleCat.epi_iff_surjective _).2 fun w => ⟨Finsupp.single w 1, freeCoverπ_single W w⟩

private theorem freeCover_hom_ext {W M : ModuleCat.{u} k} {f g : freeCover W ⟶ M}
    (h : ∀ w : W, f.hom (Finsupp.single w 1) = g.hom (Finsupp.single w 1)) : f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' fun w => LinearMap.ext_ring (h w))

variable {ι : Type*} {c : ComplexShape ι}

private theorem comp_apply' {X Y Z : ModuleCat.{u} k} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).hom x = g.hom (f.hom x) :=
  rfl

private theorem apply_eq_of_comp_eq {X Y Z : ModuleCat.{u} k} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : X ⟶ Z} (e : f ≫ g = h) (x : X) : g.hom (f.hom x) = h.hom x := by
  rw [← e]
  rfl

/-- An elementwise sufficient condition for surjectivity on homology. -/
private theorem epi_homologyMap_of_forall {K L : HomologicalComplex (ModuleCat.{u} k) c}
    (φ : K ⟶ L) (j : ι)
    (h : ∀ y : L.X j, (L.d j (c.next j)).hom y = 0 → ∃ x : K.X j, (K.d j (c.next j)).hom x = 0 ∧
      ∃ y₁ : L.X (c.prev j), y = (φ.f j).hom x + (L.d (c.prev j) j).hom y₁) :
    Epi (homologyMap φ j) := by
  rw [epi_homologyMap_iff_up_to_refinements φ (c.prev j) j (c.next j) rfl rfl]
  intro W y₂ hy₂
  choose x hx y₁ hxy using fun w => h (y₂.hom w) (apply_eq_of_comp_eq hy₂ w)
  refine ⟨freeCover W, freeCoverπ W, epi_freeCoverπ W, freeLift x, ?_, freeLift y₁, ?_⟩
  · refine freeCover_hom_ext fun w => ?_
    rw [comp_apply', freeLift_single, hx]
    rfl
  · refine freeCover_hom_ext fun w => ?_
    rw [comp_apply', freeCoverπ_single, hxy w, ModuleCat.hom_add, LinearMap.add_apply,
      comp_apply', comp_apply', freeLift_single, freeLift_single]

/-- An elementwise sufficient condition for injectivity on homology. -/
private theorem mono_homologyMap_of_forall {K L : HomologicalComplex (ModuleCat.{u} k) c}
    (φ : K ⟶ L) (j : ι)
    (h : ∀ x : K.X j, (K.d j (c.next j)).hom x = 0 → ∀ y₁ : L.X (c.prev j),
      (φ.f j).hom x = (L.d (c.prev j) j).hom y₁ →
        ∃ x₁ : K.X (c.prev j), x = (K.d (c.prev j) j).hom x₁) :
    Mono (homologyMap φ j) := by
  rw [mono_homologyMap_iff_up_to_refinements φ (c.prev j) j (c.next j) rfl rfl]
  intro W x₂ hx₂ y₁ hxy
  choose x₁ hx₁ using fun w => h (x₂.hom w) (apply_eq_of_comp_eq hx₂ w) (y₁.hom w)
    (apply_eq_of_comp_eq hxy w)
  refine ⟨freeCover W, freeCoverπ W, epi_freeCoverπ W, freeLift x₁, ?_⟩
  refine freeCover_hom_ext fun w => ?_
  rw [comp_apply', freeCoverπ_single, hx₁ w, comp_apply', freeLift_single]

variable {B : HomologicalComplex (ModuleCat.{u} k) c}

/-- The iterates `S^N` of a chain endomorphism. -/
private def iter (S : B ⟶ B) : ℕ → (B ⟶ B)
  | 0 => 𝟙 B
  | N + 1 => iter S N ≫ S

private theorem iter_succ_f_apply (S : B ⟶ B) (N : ℕ) (n : ι) (x : B.X n) :
    ((iter S (N + 1)).f n).hom x = (S.f n).hom (((iter S N).f n).hom x) :=
  rfl

private theorem iter_f_apply (S : B ⟶ B) (N : ℕ) (n : ι) (x : B.X n) :
    ((iter S N).f n).hom x = (⇑(S.f n).hom)^[N] x := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', ← ih, iter_succ_f_apply]

/-- The composite homotopy `S^N ≃ 𝟙`; its components are `T ∘ (S^{N-1} + ⋯ + S + 1)`. -/
private noncomputable def iterHomotopy {S : B ⟶ B} (T : Homotopy S (𝟙 B)) :
    ∀ N, Homotopy (iter S N) (𝟙 B)
  | 0 => Homotopy.refl _
  | N + 1 => (T.compLeftId (iter S N)).trans (iterHomotopy T N)

private theorem iterHomotopy_zero_hom {S : B ⟶ B} (T : Homotopy S (𝟙 B)) (n m : ι) :
    (iterHomotopy T 0).hom n m = 0 :=
  rfl

private theorem iterHomotopy_succ_hom_apply {S : B ⟶ B} (T : Homotopy S (𝟙 B)) (N : ℕ)
    (n m : ι) (x : B.X n) :
    ((iterHomotopy T (N + 1)).hom n m).hom x =
      (T.hom n m).hom (((iter S N).f n).hom x) + ((iterHomotopy T N).hom n m).hom x := by
  simp [iterHomotopy]

/-- The homotopy identity `S^N y = D_N (∂y) + ∂(D_N y) + y`, elementwise. -/
private theorem iter_apply_eq {S : B ⟶ B} (T : Homotopy S (𝟙 B)) (N : ℕ) (j : ι) (y : B.X j) :
    ((iter S N).f j).hom y =
      ((iterHomotopy T N).hom (c.next j) j).hom ((B.d j (c.next j)).hom y) +
        (B.d (c.prev j) j).hom (((iterHomotopy T N).hom j (c.prev j)).hom y) + y := by
  rw [(iterHomotopy T N).comm j]
  rfl

end QuasiIsoOfIterate

open QuasiIsoOfIterate

variable {k : Type u} [Ring k] {ι : Type*} {c : ComplexShape ι}

/-- **Quasi-isomorphism by iteration.** Let `i : A ⟶ B` be a monomorphism of complexes of
`k`-modules, `S : B ⟶ B` a chain map and `T` a homotopy from `S` to the identity. If `S` and `T`
carry the image of `i` into the image of `i`, and every chain of `B` is carried into the image of
`i` by some iterate of `S`, then `i` is a quasi-isomorphism. -/
theorem quasiIso_of_iterate_mem {A B : HomologicalComplex (ModuleCat.{u} k) c}
    (i : A ⟶ B) [Mono i] (S : B ⟶ B) (T : Homotopy S (𝟙 B))
    (hS : ∀ n (a : A.X n), (S.f n).hom ((i.f n).hom a) ∈ LinearMap.range (i.f n).hom)
    (hT : ∀ n m (a : A.X n), (T.hom n m).hom ((i.f n).hom a) ∈ LinearMap.range (i.f m).hom)
    (hsmall : ∀ n (b : B.X n), ∃ N : ℕ, (⇑(S.f n).hom)^[N] b ∈ LinearMap.range (i.f n).hom) :
    QuasiIso i := by
  have hinj : ∀ n, Function.Injective (i.f n).hom := fun n =>
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hcomm : ∀ n m (a : A.X n), (i.f m).hom ((A.d n m).hom a) = (B.d n m).hom ((i.f n).hom a) :=
    fun n m a => (apply_eq_of_comp_eq (i.comm n m).symm a).trans rfl
  -- Iterates of `S` and the composite homotopies preserve the image of `i`.
  have hSN : ∀ N n (a : A.X n),
      ((iter S N).f n).hom ((i.f n).hom a) ∈ LinearMap.range (i.f n).hom := by
    intro N n
    induction N with
    | zero => exact fun a => ⟨a, rfl⟩
    | succ N ih =>
      intro a
      obtain ⟨a', ha'⟩ := ih a
      rw [iter_succ_f_apply, ← ha']
      exact hS n a'
  have hDN : ∀ N n m (a : A.X n),
      ((iterHomotopy T N).hom n m).hom ((i.f n).hom a) ∈ LinearMap.range (i.f m).hom := by
    intro N n m
    induction N with
    | zero => exact fun a => by rw [iterHomotopy_zero_hom]; exact Submodule.zero_mem _
    | succ N ih =>
      intro a
      obtain ⟨a', ha'⟩ := hSN N n a
      rw [iterHomotopy_succ_hom_apply, ← ha']
      exact Submodule.add_mem _ (hT n m a') (ih a)
  have hiterd : ∀ N n m (y : B.X n),
      ((iter S N).f m).hom ((B.d n m).hom y) = (B.d n m).hom (((iter S N).f n).hom y) :=
    fun N n m y => (apply_eq_of_comp_eq ((iter S N).comm n m).symm y).trans rfl
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hepi : Epi (homologyMap i j) := by
    refine epi_homologyMap_of_forall i j fun y hy => ?_
    obtain ⟨N, a, ha⟩ := hsmall j y
    rw [← iter_f_apply] at ha
    have key := iter_apply_eq T N j y
    rw [hy, map_zero, zero_add] at key
    refine ⟨a, hinj _ ?_, -((iterHomotopy T N).hom j (c.prev j)).hom y, ?_⟩
    · rw [hcomm, map_zero, ha, ← hiterd, hy, map_zero]
    · rw [map_neg, ha, key]
      abel
  have hmono : Mono (homologyMap i j) := by
    refine mono_homologyMap_of_forall i j fun x hx y₁ hxy => ?_
    obtain ⟨N, b, hb⟩ := hsmall (c.prev j) y₁
    rw [← iter_f_apply] at hb
    obtain ⟨d, hd⟩ := hDN N j (c.prev j) x
    have key := iter_apply_eq T N j ((i.f j).hom x)
    have h0 : (B.d j (c.next j)).hom ((i.f j).hom x) = 0 := by rw [← hcomm, hx, map_zero]
    have lhs : ((iter S N).f j).hom ((i.f j).hom x) =
        (B.d (c.prev j) j).hom ((i.f (c.prev j)).hom b) := by
      rw [hxy, hiterd, hb]
    rw [h0, map_zero, zero_add, ← hd, lhs] at key
    refine ⟨b - d, hinj _ ?_⟩
    rw [map_sub, map_sub, hcomm, hcomm, key]
    abel
  exact isIso_of_mono_of_epi _

end TDA.Topology
