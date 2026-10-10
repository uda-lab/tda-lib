import Mathlib.CategoryTheory.Category.Pairwise
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.Topology.Sets.Opens

/-!
# Pairwise-intersection cosheaf condition

For a family `U : ι → α` in a meet-semilattice `α`, mathlib's `Pairwise.diagram U` has the
members `U i` and the overlaps `U i ⊓ U j` as objects. A functor `F : α ⥤ Type w₀` satisfies the
cosheaf condition for the cover when it sends a cocone over this diagram to a colimit: the
value over the apex is the coequalizer of the two inclusion families out of the overlaps. This
is the dual of mathlib's `TopCat.Presheaf.IsSheafPairwiseIntersections`.

* `coverCocone U hU`: the pairwise-intersection cocone with an explicit upper bound `W` as apex;
  it needs only `SemilatticeInf`, so the union of the members need not exist in `α`.
* `overlapRel F U`: two local values are related when they are the two restrictions of one value
  over the actual overlap `U i ⊓ U j`. Agreement is on the overlap object, not on labels.
* `nonempty_isColimit_mapCocone_iff`: `F` sends a cocone to a colimit iff every value over the
  apex comes from a member and two local values with the same image are related by the
  equivalence closure of `overlapRel F U`. The proof goes through mathlib's bijectivity
  criterion `Types.isColimit_iff_coconeTypesIsColimit`.
* `existsUnique_glue_of_surjective_of_eqvGen`: the raw universal property, for a test object in
  an arbitrary `Sort`.
* `IsPairwiseCosheaf.{w} F`: `F : Opens Y ⥤ Type wF` sends `Pairwise.cocone U` to a colimit for
  every cover indexed by `κ : Type w`.
* `map_apply_eq_of_thin`, `map_map_apply_of_thin`: a `Type`-valued functor out of a preorder
  identifies parallel morphisms, and composites with the same ends, pointwise.

Universes: cover index `ι : Type w`, values `F : α ⥤ Type w₀`, and test objects in any `Sort`
for the raw form. No `Small`, `UnivLE` or `HasColimit` assumption is used. The module depends on
mathlib only and does not import the Reeb modules; see `docs/math/cosheaf.md`.
-/

open CategoryTheory Limits

universe w w₀

namespace TDA.Topology

section generic

variable {α : Type*} [SemilatticeInf α] {ι : Type w}

/-- The pairwise-intersection cocone of a family `U` with apex an upper bound `W`. For `Opens`
and `W = ⨆ i, U i` this is mathlib's `Pairwise.cocone U` up to the (unique) legs. -/
def coverCocone (U : ι → α) {W : α} (hU : ∀ i, U i ≤ W) : Cocone (Pairwise.diagram U) where
  pt := W
  ι :=
    { app := fun o =>
        match o with
        | .single i => homOfLE (hU i)
        | .pair i _ => homOfLE (inf_le_left.trans (hU i))
      naturality := fun _ _ _ => Subsingleton.elim _ _ }

/-- Overlap relation on local values: `p` and `q` are restrictions of one value over the actual
overlap `U p.1 ⊓ U q.1` (agreement on the overlap object, not on labels). -/
def overlapRel (F : α ⥤ Type w₀) (U : ι → α) (p q : Σ i, F.obj (U i)) : Prop :=
  ∃ c : F.obj (U p.1 ⊓ U q.1),
    F.map (homOfLE inf_le_left) c = p.2 ∧ F.map (homOfLE inf_le_right) c = q.2

/-- Invariance of a compatible family along the equivalence closure of `overlapRel`. -/
theorem eqvGen_overlapRel_apply_eq (F : α ⥤ Type w₀) (U : ι → α) {A : Sort*}
    (a : ∀ i, F.obj (U i) → A)
    (ha : ∀ i j (c : F.obj (U i ⊓ U j)),
      a i (F.map (homOfLE inf_le_left) c) = a j (F.map (homOfLE inf_le_right) c))
    {p q : Σ i, F.obj (U i)} (h : Relation.EqvGen (overlapRel F U) p q) :
    a p.1 p.2 = a q.1 q.2 := by
  induction h with
  | rel p q hpq =>
    obtain ⟨c, hcp, hcq⟩ := hpq
    rw [← hcp, ← hcq]
    exact ha _ _ c
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Elementary form of the cosheaf condition for one cover: `F` sends a cocone `c` over the
pairwise-intersection diagram to a colimit in `Type w₀` iff every value over `c.pt` comes from a
member and two local values have the same image iff they are related by the equivalence closure
of `overlapRel`. The cocone legs are arbitrary, so this covers `coverCocone` and
`Pairwise.cocone`. Condition (ii) is stated as an implication only: its converse holds for every
cocone, because `α` is thin, so both images over the apex of an overlap value `c` over
`U i ⊓ U j` equal its image along the leg at `pair i j`. -/
theorem nonempty_isColimit_mapCocone_iff (F : α ⥤ Type w₀) (U : ι → α)
    (c : Cocone (Pairwise.diagram U)) :
    Nonempty (IsColimit (F.mapCocone c)) ↔
      (∀ x : F.obj c.pt, ∃ i, ∃ e : F.obj (U i), F.map (c.ι.app (.single i)) e = x) ∧
      ∀ (i j : ι) (e : F.obj (U i)) (e' : F.obj (U j)),
        F.map (c.ι.app (.single i)) e = F.map (c.ι.app (.single j)) e' →
          Relation.EqvGen (overlapRel F U) ⟨i, e⟩ ⟨j, e'⟩ := by
  rw [Types.isColimit_iff_coconeTypesIsColimit]
  set G := Pairwise.diagram U ⋙ F
  -- every element of the colimit type is represented over a single member
  have hsingle : ∀ t : G.ColimitType, ∃ i, ∃ e : F.obj (U i),
      G.ιColimitType (.single i) e = t := by
    intro t
    obtain ⟨o, x, rfl⟩ := G.ιColimitType_jointly_surjective t
    cases o with
    | single i => exact ⟨i, x, rfl⟩
    | pair i j => exact ⟨i, G.map (Pairwise.Hom.left i j) x, G.ιColimitType_map _ _⟩
  -- overlap steps become equalities in the colimit type
  have hstep : ∀ p q : Σ i, F.obj (U i), Relation.EqvGen (overlapRel F U) p q →
      G.ιColimitType (.single p.1) p.2 = G.ιColimitType (.single q.1) q.2 := by
    intro p q h
    induction h with
    | rel p q hpq =>
      obtain ⟨x, hxp, hxq⟩ := hpq
      rw [← hxp, ← hxq]
      exact (G.ιColimitType_map (Pairwise.Hom.left p.1 q.1) x).trans
        (G.ιColimitType_map (Pairwise.Hom.right p.1 q.1) x).symm
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  -- generating relation of the colimit type, read on members
  let φ : (Σ o, G.obj o) → Σ i, F.obj (U i) := fun p =>
    match p with
    | ⟨.single i, x⟩ => ⟨i, x⟩
    | ⟨.pair i _, x⟩ => ⟨i, F.map (homOfLE inf_le_left) x⟩
  have hφ : ∀ p q, Relation.EqvGen G.ColimitTypeRel p q →
      Relation.EqvGen (overlapRel F U) (φ p) (φ q) := by
    intro p q h
    induction h with
    | rel p q hpq =>
      obtain ⟨o, x⟩ := p
      obtain ⟨o', x'⟩ := q
      obtain ⟨g, hg⟩ := hpq
      cases g with
      | id_single i =>
        have : x' = x := hg.trans (by erw [F.map_id]; rfl)
        rw [this]; exact .refl _
      | id_pair i j =>
        have : x' = x := hg.trans (by erw [F.map_id]; rfl)
        rw [this]; exact .refl _
      | left i j =>
        have hg' : x' = G.map (Pairwise.Hom.left i j) x := hg
        rw [hg']; exact .refl _
      | right i j =>
        have hg' : x' = G.map (Pairwise.Hom.right i j) x := hg
        rw [hg']; exact .rel _ _ ⟨x, rfl, rfl⟩
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  constructor
  · rintro ⟨hbij⟩
    refine ⟨fun x => ?_, fun i j e e' h => ?_⟩
    · obtain ⟨t, rfl⟩ := hbij.2 x
      obtain ⟨i, e, rfl⟩ := hsingle t
      exact ⟨i, e, rfl⟩
    · have := hbij.1 (a₁ := G.ιColimitType (.single i) e) (a₂ := G.ιColimitType (.single j) e') h
      exact hφ _ _ ((G.ιColimitType_eq_iff _ _).1 this)
  · rintro ⟨hsurj, hker⟩
    refine ⟨⟨fun t₁ t₂ h => ?_, fun x => ?_⟩⟩
    · obtain ⟨i, e, rfl⟩ := hsingle t₁
      obtain ⟨j, e', rfl⟩ := hsingle t₂
      exact hstep ⟨i, e⟩ ⟨j, e'⟩ (hker i j e e' h)
    · obtain ⟨i, e, rfl⟩ := hsurj x
      exact ⟨G.ιColimitType (.single i) e, rfl⟩

/-- Raw universal property from the elementary form: a family `a i : F (U i) → A` that agrees on
every overlap object glues uniquely along `c`. The test object `A : Sort*` is unrestricted. -/
theorem existsUnique_glue_of_surjective_of_eqvGen (F : α ⥤ Type w₀) (U : ι → α)
    (c : Cocone (Pairwise.diagram U))
    (hsurj : ∀ x : F.obj c.pt, ∃ i, ∃ e : F.obj (U i), F.map (c.ι.app (.single i)) e = x)
    (hker : ∀ (i j : ι) (e : F.obj (U i)) (e' : F.obj (U j)),
      F.map (c.ι.app (.single i)) e = F.map (c.ι.app (.single j)) e' →
        Relation.EqvGen (overlapRel F U) ⟨i, e⟩ ⟨j, e'⟩)
    {A : Sort*} (a : ∀ i, F.obj (U i) → A)
    (ha : ∀ i j (c : F.obj (U i ⊓ U j)),
      a i (F.map (homOfLE inf_le_left) c) = a j (F.map (homOfLE inf_le_right) c)) :
    ∃! g : F.obj c.pt → A, ∀ i (e : F.obj (U i)), g (F.map (c.ι.app (.single i)) e) = a i e := by
  choose i₀ e₀ he₀ using hsurj
  have key : ∀ i (e : F.obj (U i)), a (i₀ (F.map (c.ι.app (.single i)) e))
      (e₀ (F.map (c.ι.app (.single i)) e)) = a i e := fun i e =>
    eqvGen_overlapRel_apply_eq F U a ha (hker _ _ _ _ (he₀ _))
  refine ⟨fun x => a (i₀ x) (e₀ x), key, fun g hg => funext fun x => ?_⟩
  rw [← he₀ x, hg, key]

/-- The cosheaf condition on `Opens Y` over pairwise intersections: the dual of mathlib's
`TopCat.Presheaf.IsSheafPairwiseIntersections`. The cover-index universe `wκ` is the first
universe parameter, so callers write `IsPairwiseCosheaf.{w} F`; it is independent of `Y` and of
the value universe. -/
def IsPairwiseCosheaf.{wκ, vY, wF} {Y : Type vY} [TopologicalSpace Y]
    (F : TopologicalSpace.Opens Y ⥤ Type wF) : Prop :=
  ∀ ⦃κ : Type wκ⦄ (U : κ → TopologicalSpace.Opens Y),
    Nonempty (IsColimit (F.mapCocone (Pairwise.cocone U)))

end generic

section thin

universe u

variable {α : Type*} [Preorder α] (F : α ⥤ Type u)

/-- A `Type`-valued functor out of a preorder identifies parallel morphisms pointwise. -/
theorem map_apply_eq_of_thin {a b : α} (f g : a ⟶ b) (x : F.obj a) : F.map f x = F.map g x := by
  rw [Subsingleton.elim f g]

/-- A composite of images of preorder morphisms, applied to an element, is the image of any
morphism with the same ends. -/
theorem map_map_apply_of_thin {a b c : α} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (x : F.obj a) :
    F.map g (F.map f x) = F.map h x := by
  change (F.map f ≫ F.map g) x = _
  rw [← F.map_comp, Subsingleton.elim (f ≫ g) h]

end thin

end TDA.Topology
