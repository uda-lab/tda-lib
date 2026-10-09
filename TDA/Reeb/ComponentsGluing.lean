import TDA.Topology.Cosheaf
import TDA.Reeb.Components
import TDA.Reeb.ComponentsCover

/-!
# Gluing of the open-set path-component functor

For `f : C(X, Y)` and opens `U i` covering an open `W`, a family of maps
`a i : (componentFunctor f).obj (U i) → A` that agrees after both inclusions from every overlap
`(componentFunctor f).obj (U i ⊓ U j)` has a unique extension
`g : (componentFunctor f).obj W → A` (`componentFunctor_existsUnique_glue`). The empty cover is
included.

The proof factors through the elementary form of the cosheaf condition in
`TDA.Topology.Cosheaf`:

* surjectivity, `componentFunctor_exists_map_eq`: every class over `W` comes from a class over a
  member containing the image of one of its points;
* the kernel, `componentFunctor_map_eq_iff_eqvGen`: two local classes have the same image over
  `W` iff they are related by the equivalence closure of `overlapRel (componentFunctor f) U`.
  The forward direction uses the chain of `componentFunctor_reflTransGen_of_mk_eq`, and
  `overlapRel_mk` turns each shared point into an overlap step.

The colimit forms are `componentFunctor_isColimit` (any cocone over the pairwise-intersection
diagram with covered apex), `componentFunctor_isColimit_coverCocone` and
`componentFunctor_isPairwiseCosheaf`. `componentFunctor_glue_natTrans` states naturality of the
glue under a continuous map commuting with the base maps.

Universes: carrier `X : Type u`, base `Y : Type v`, cover index `ι : Type w`, and test objects
in any `Sort` for the raw form. A `Sort`-indexed cover is reindexed through `PLift`
(`Examples.existsUnique_glue_sort`). See `docs/math/reeb-components-gluing.md`.
-/

open CategoryTheory Limits

universe u v w

namespace TDA.Reeb

open TDA.Topology

section components

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {ι : Type w}

/-- A point lying in two members gives an overlap step between its two local classes. -/
theorem overlapRel_mk (f : C(X, Y)) (U : ι → TopologicalSpace.Opens Y) {p q : ι} (z : X)
    (hp : f z ∈ U p) (hq : f z ∈ U q) :
    overlapRel (componentFunctor f) U ⟨p, ZerothHomotopy.mk ⟨z, hp⟩⟩
      ⟨q, ZerothHomotopy.mk ⟨z, hq⟩⟩ :=
  ⟨ZerothHomotopy.mk ⟨z, TopologicalSpace.Opens.mem_inf.2 ⟨hp, hq⟩⟩, rfl, rfl⟩

/-- Surjectivity: every class over `W` is the image of a class over some member. -/
theorem componentFunctor_exists_map_eq (f : C(X, Y)) {W : TopologicalSpace.Opens Y}
    (U : ι → TopologicalSpace.Opens Y) (hU : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i)
    (x : (componentFunctor f).obj W) :
    ∃ i, ∃ e : (componentFunctor f).obj (U i), (componentFunctor f).map (homOfLE (hU i)) e = x := by
  induction x using ZerothHomotopy.rec with
  | mk a =>
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov a.2)
    exact ⟨i, ZerothHomotopy.mk ⟨a.1, hi⟩, rfl⟩

/-- Class form (coequaliser kernel): two local classes have the same image over `W` iff they are
related by the equivalence closure of `overlapRel`. -/
theorem componentFunctor_map_eq_iff_eqvGen (f : C(X, Y)) {W : TopologicalSpace.Opens Y}
    (U : ι → TopologicalSpace.Opens Y) (hU : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i) {i j : ι}
    (e : (componentFunctor f).obj (U i)) (e' : (componentFunctor f).obj (U j)) :
    (componentFunctor f).map (homOfLE (hU i)) e = (componentFunctor f).map (homOfLE (hU j)) e' ↔
      Relation.EqvGen (overlapRel (componentFunctor f) U) ⟨i, e⟩ ⟨j, e'⟩ := by
  constructor
  · intro h
    induction e using ZerothHomotopy.rec with
    | mk a =>
    induction e' using ZerothHomotopy.rec with
    | mk b =>
    have hR := componentFunctor_reflTransGen_of_mk_eq f U hcov h
    have key : ∀ z : {x : X // f x ∈ W},
        Relation.ReflTransGen
          (fun a b : {x : X // f x ∈ W} => ∃ i, ∃ (ha : f a.1 ∈ U i) (hb : f b.1 ∈ U i),
            (ZerothHomotopy.mk ⟨a.1, ha⟩ : (componentFunctor f).obj (U i)) =
              ZerothHomotopy.mk ⟨b.1, hb⟩) ⟨a.1, hU i a.2⟩ z →
        ∀ (k : ι) (hz : f z.1 ∈ U k),
          Relation.EqvGen (overlapRel (componentFunctor f) U) ⟨i, ZerothHomotopy.mk a⟩
            ⟨k, ZerothHomotopy.mk ⟨z.1, hz⟩⟩ := by
      intro z hz
      induction hz with
      | refl => intro k hk; exact .rel _ _ (overlapRel_mk f U a.1 a.2 hk)
      | tail _ hst ih =>
        obtain ⟨i', hs, ht, hst⟩ := hst
        intro k hk
        refine .trans _ _ _ (ih i' hs) ?_
        rw [hst]
        exact .rel _ _ (overlapRel_mk f U _ ht hk)
    exact key _ hR j b.2
  · intro h
    have key : ∀ p q : Σ i, (componentFunctor f).obj (U i),
        Relation.EqvGen (overlapRel (componentFunctor f) U) p q →
        (componentFunctor f).map (homOfLE (hU p.1)) p.2 =
          (componentFunctor f).map (homOfLE (hU q.1)) q.2 := by
      intro p q hpq
      induction hpq with
      | rel p q hpq =>
        obtain ⟨c, hcp, hcq⟩ := hpq
        rw [← hcp, ← hcq]
        induction c using ZerothHomotopy.rec with
        | mk z => rfl
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact key _ _ h

/-- Raw gluing universal property: for an open cover `U` of `W`, a family of maps
`a i : C_f(U i) → A` agreeing after both inclusions from `C_f(U i ⊓ U j)` has a unique
`g : C_f(W) → A` with `g ∘ C_f(U i ≤ W) = a i`. `A : Sort*`; the empty cover is included. -/
theorem componentFunctor_existsUnique_glue (f : C(X, Y)) {W : TopologicalSpace.Opens Y}
    (U : ι → TopologicalSpace.Opens Y) (hU : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i) {A : Sort*}
    (a : ∀ i, (componentFunctor f).obj (U i) → A)
    (ha : ∀ i j (c : (componentFunctor f).obj (U i ⊓ U j)),
      a i ((componentFunctor f).map (homOfLE inf_le_left) c) =
        a j ((componentFunctor f).map (homOfLE inf_le_right) c)) :
    ∃! g : (componentFunctor f).obj W → A,
      ∀ i (e : (componentFunctor f).obj (U i)),
        g ((componentFunctor f).map (homOfLE (hU i)) e) = a i e :=
  existsUnique_glue_of_surjective_of_eqvGen (componentFunctor f) U (coverCocone U hU)
    (componentFunctor_exists_map_eq f U hU hcov)
    (fun _ _ e e' h => (componentFunctor_map_eq_iff_eqvGen f U hU hcov e e').1 h) a ha

/-- Colimit form for any cocone over the pairwise-intersection diagram whose apex is covered. -/
theorem componentFunctor_isColimit (f : C(X, Y)) (U : ι → TopologicalSpace.Opens Y)
    (c : Cocone (Pairwise.diagram U)) (hcov : c.pt ≤ ⨆ i, U i) :
    Nonempty (IsColimit ((componentFunctor f).mapCocone c)) := by
  have hU : ∀ i, U i ≤ c.pt := fun i => (c.ι.app (.single i)).le
  refine (nonempty_isColimit_mapCocone_iff _ U c).2
    ⟨componentFunctor_exists_map_eq f U hU hcov, fun _ _ e e' h => ?_⟩
  exact (componentFunctor_map_eq_iff_eqvGen f U hU hcov e e').1 h

/-- Colimit form for an open cover `U` of `W` (`coverCocone`, apex `W`). -/
theorem componentFunctor_isColimit_coverCocone (f : C(X, Y)) {W : TopologicalSpace.Opens Y}
    (U : ι → TopologicalSpace.Opens Y) (hU : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i) :
    Nonempty (IsColimit ((componentFunctor f).mapCocone (coverCocone U hU))) :=
  componentFunctor_isColimit f U _ hcov

/-- The component functor is a cosheaf in the pairwise-intersection sense, for every cover-index
universe `w`. -/
theorem componentFunctor_isPairwiseCosheaf (f : C(X, Y)) :
    IsPairwiseCosheaf.{w} (componentFunctor f) :=
  fun _ U => componentFunctor_isColimit f U (Pairwise.cocone U) le_rfl

/-- Naturality of gluing under a continuous commuting map `h` (`g ∘ h = f`): the glue of the
pulled-back family is the glue for `g` precomposed with `componentNatTrans h`. -/
theorem componentFunctor_glue_natTrans {Z : Type u} [TopologicalSpace Z] {f : C(X, Y)}
    {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x) {W : TopologicalSpace.Opens Y}
    (U : ι → TopologicalSpace.Opens Y) (hU : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i) {A : Sort*}
    (a : ∀ i, (componentFunctor g).obj (U i) → A) (G : (componentFunctor g).obj W → A)
    (hG : ∀ i (e : (componentFunctor g).obj (U i)),
      G ((componentFunctor g).map (homOfLE (hU i)) e) = a i e)
    (G' : (componentFunctor f).obj W → A)
    (hG' : ∀ i (e : (componentFunctor f).obj (U i)),
      G' ((componentFunctor f).map (homOfLE (hU i)) e) =
        a i ((componentNatTrans h comm).app (U i) e)) :
    G' = G ∘ (componentNatTrans h comm).app W := by
  funext x
  obtain ⟨i, e, rfl⟩ := componentFunctor_exists_map_eq f U hU hcov x
  rw [hG', Function.comp_apply, ← hG]
  induction e using ZerothHomotopy.rec with
  | mk z => rfl

end components

end TDA.Reeb
