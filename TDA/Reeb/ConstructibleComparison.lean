import TDA.Reeb.ConstructibleQuotient
import TDA.Reeb.RGraphCosheafEquivalence

/-!
# The canonical comparison on constructible inputs

The comparison `η_f : C_f ⟶ C_{f̄}` between the path components of a space over `ℝ` and those of its
Reeb quotient, restricted to open intervals, is a natural isomorphism on constructible inputs
(de Silva, Munch and Patel, *Categorified Reeb Graphs*, Theorem 3.17).

## The map

`ReebQuotient.intervalComponentComparison f` is, by definition, `ReebQuotient.componentComparison f`
precomposed with `OpenInterval.toOpensFunctor`: the path component of `x` in `f ⁻¹ I` goes to the
path component of `q_f x` in `f̄ ⁻¹ I`. The identity with `componentComparison f` holds by `rfl`
(`intervalComponentComparison_eq`, `intervalComponentComparison_app`). Its naturality in
height-preserving maps is `componentComparison_natural`, precomposed. On the real slice it is
`componentComparisonOver ℝ` followed by precomposition with `toOpensFunctor`, a transformation
`intervalComponentsOver ⟶ quotientFunctor ℝ ⋙ intervalComponentsOver`
(`intervalComponentComparisonOver`). The comparison `componentComparisonOver ℝ` at `A` is the
path-component map of the projection `ρ_A` (`componentComparisonOver_app_eq_map`, the source's
`η = 𝒞ρ`); on open intervals this follows by precomposition.

## The theorem

For `S : CriticalValues n` and a presentation `P` whose pieces are locally path-connected with
finitely many path components, the comparison is an isomorphism at `h = P.height S`
(`CylinderPresentation.isIso_intervalComponentComparison`). Compactness is not used, and nothing is
assumed of Hausdorffness or of the endpoint maps. On the real slice, the comparison at every
constructible ℝ-space is an isomorphism (`isIso_intervalComponentComparison_of_constructible`).

On `ConstructibleSpaceCat`, with all continuous height-preserving maps, the comparison is a natural
isomorphism in two forms:

* `constructibleComponentComparisonIso`, between functors to precosheaves on open intervals;
* `constructibleCosheafComparisonIso : constructibleCosheafFunctor ≅ quotientRGraphFunctor ⋙
  RGraph.cosheafFunctor`, between functors to `ConstructibleCosheafCat.{0}`, which is the source's
  `𝒞' ≅ 𝒞''ℛ`.

Both have the comparison itself as components (`constructibleComponentComparisonIso_hom_app`,
`constructibleCosheafComparisonIso_hom_app_hom`). No hypothesis or statement claims the comparison
invertible in general, and no instance supplies `IsIso` for an arbitrary map. The source's
Example 3.21, the topologist's sine curve, is a nonconstructible ℝ-space at which the comparison is
not injective; it is not formalized here.

## Proof

Write `Φ = componentGraphMap : X → G` and `θ = quotientComponentGraphMap : Q → G` for the maps to
the component graph `G`, so `θ ∘ ρ = Φ` and `π₀(θ) ∘ η = π₀(Φ)` on every interval
(`intervalComponentComparison_comp`).

1. `π₀(Φ)` is a natural isomorphism. Its source and target are the path-component cosheaves of two
   realizations over the same `S`, both constructible at `S` and interval cosheaves. At a star,
   `π₀(Φ)` carries the component bijection of `P` (the cylinder principle, DMP Lemma 2.4) to that
   of the component graph, precomposed with `c ↦ [c]` on its discrete vertex set
   (`componentGraphMap_star`), and likewise at a gap (`componentGraphMap_gap`). All three maps are
   bijections, so every short component is bijective. The short-interval test
   `CriticalValues.isIso_iff_shortIntervals` (DMP Corollary 3.14) extends this to all intervals.
2. `η` is bijective at every interval: injective because `π₀(θ) ∘ η = π₀(Φ)` is injective, and
   surjective by `componentComparison_app_surjective`.
3. Hence `η` is a natural isomorphism, and the quotient cosheaf is constructible at `S`
   (`isConstructibleAt_intervalComponents_reebQuotient`). For a constructible ℝ-space both
   cosheaves are constructible at a common list of levels
   (`exists_isConstructibleAt_of_isConstructibleSpace`), as in the source's proof.

This is the source's proof with the projection `ρ` replaced by `Φ = θ ∘ ρ`, whose source and target
are both realizations over `S`. At stars and gaps, `π₀(θ) ∘ η` is the map taking each piece to its
set of path components (`intervalComponentComparison_star`, `intervalComponentComparison_gap`). No
lifting of paths along general quotient maps is used.

Source: de Silva, Munch and Patel, *Categorified Reeb Graphs*, Theorem 3.17; see
`docs/math/reeb-constructible-comparison.md`.
-/

open Set Topology CategoryTheory

universe u

namespace TDA.Reeb

noncomputable section

/-! ### Path-component maps on open intervals -/

section natTrans

variable {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]

/-- `componentNatTrans h comm` precomposed with `OpenInterval.toOpensFunctor`, typed between the
interval restrictions `intervalComponents`. -/
def intervalComponentNatTrans {f : C(X, ℝ)} {g : C(Z, ℝ)} (h : C(X, Z))
    (comm : ∀ x, g (h x) = f x) : intervalComponents f ⟶ intervalComponents g :=
  Functor.whiskerLeft OpenInterval.toOpensFunctor (componentNatTrans h comm)

@[simp]
theorem intervalComponentNatTrans_app_mk {f : C(X, ℝ)} {g : C(Z, ℝ)} (h : C(X, Z))
    (comm : ∀ x, g (h x) = f x) (I : OpenInterval) (x : {x : X // f x ∈ OpenInterval.toOpens I}) :
    (intervalComponentNatTrans h comm).app I (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨h x.1, by rw [comm]; exact x.2⟩ :
        {z : Z // g z ∈ OpenInterval.toOpens I}) := rfl

end natTrans

/-- `intervalComponentsOver` on a slice morphism, spelled with `intervalComponentNatTrans`. -/
theorem intervalComponentsOver_map_eq_intervalComponentNatTrans {A B : Over (TopCat.of ℝ)}
    (φ : A ⟶ B) :
    intervalComponentsOver.map φ = intervalComponentNatTrans φ.left.hom (overBaseMap_comm φ) :=
  rfl

namespace ReebQuotient

/-! ### The comparison on open intervals -/

section interval

variable {X : Type u} [TopologicalSpace X]

/-- `η_f` on open intervals: the comparison `componentComparison f` precomposed with
`OpenInterval.toOpensFunctor`. It sends the path component of `x` in `f ⁻¹ I` to the path
component of `q_f x` in `f̄ ⁻¹ I`. It is surjective at every interval; it need not be injective
(de Silva, Munch and Patel, Example 3.21). -/
def intervalComponentComparison (f : C(X, ℝ)) :
    intervalComponents f ⟶ intervalComponents (height f) :=
  Functor.whiskerLeft OpenInterval.toOpensFunctor (componentComparison f)

/-- The comparison map is the actual map `componentComparison f`, precomposed. -/
theorem intervalComponentComparison_eq (f : C(X, ℝ)) :
    intervalComponentComparison f =
      Functor.whiskerLeft OpenInterval.toOpensFunctor (componentComparison f) := rfl

/-- At an interval `I`, it is the component of `componentComparison f` at the open set `I`. -/
theorem intervalComponentComparison_app (f : C(X, ℝ)) (I : OpenInterval) :
    (intervalComponentComparison f).app I = (componentComparison f).app (OpenInterval.toOpens I) :=
  rfl

/-- Representative formula. -/
@[simp]
theorem intervalComponentComparison_app_mk (f : C(X, ℝ)) (I : OpenInterval)
    (x : {x : X // f x ∈ OpenInterval.toOpens I}) :
    (intervalComponentComparison f).app I (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk
        (⟨mk f x.1, x.2⟩ : {q : ReebQuotient f // height f q ∈ OpenInterval.toOpens I}) :=
  rfl

/-- Surjectivity at every interval, from `componentComparison_app_surjective`. -/
theorem intervalComponentComparison_app_surjective (f : C(X, ℝ)) (I : OpenInterval) :
    Function.Surjective ((intervalComponentComparison f).app I) :=
  componentComparison_app_surjective f (OpenInterval.toOpens I)

/-- Naturality in a height-preserving map `h`, from `componentComparison_natural`:
`C_h ≫ η_g = η_f ≫ C_{Q_h}` on open intervals. -/
theorem intervalComponentComparison_natural {Z : Type u} [TopologicalSpace Z] {f : C(X, ℝ)}
    {g : C(Z, ℝ)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x) :
    intervalComponentNatTrans h comm ≫ intervalComponentComparison g =
      intervalComponentComparison f ≫
        intervalComponentNatTrans (map h comm) (height_map_apply h comm) := by
  have key := congrArg (Functor.whiskerLeft OpenInterval.toOpensFunctor)
    (componentComparison_natural h comm)
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp] at key
  exact key

/-- Naturality of the inverses, whenever both comparisons are isomorphisms. -/
theorem inv_intervalComponentComparison_natural {Z : Type u} [TopologicalSpace Z]
    {f : C(X, ℝ)} {g : C(Z, ℝ)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x)
    [IsIso (intervalComponentComparison f)] [IsIso (intervalComponentComparison g)] :
    intervalComponentNatTrans (map h comm) (height_map_apply h comm) ≫
        inv (intervalComponentComparison g) =
      inv (intervalComponentComparison f) ≫ intervalComponentNatTrans h comm := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, ← intervalComponentComparison_natural, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

end interval

/-! ### The real slice -/

section over

/-- The source's `η = 𝒞ρ`: the comparison at `A` is the path-component map of the projection
`ρ_A`. -/
theorem componentComparisonOver_app_eq_map (Y : Type u) [TopologicalSpace Y]
    (A : Over (TopCat.of Y)) :
    (componentComparisonOver Y).app A = (componentFunctorOver Y).map ((projNatTrans Y).app A) :=
  rfl

/-- `componentComparisonOver ℝ` followed by precomposition with `toOpensFunctor`: the comparison
as a transformation of interval-component functors on the real slice. -/
def intervalComponentComparisonOver :
    intervalComponentsOver ⟶ quotientFunctor ℝ ⋙ intervalComponentsOver :=
  Functor.whiskerRight (componentComparisonOver ℝ)
    ((Functor.whiskeringLeft _ _ _).obj OpenInterval.toOpensFunctor)

/-- Its component at `A` is the comparison of the structure map of `A`. -/
theorem intervalComponentComparisonOver_app (A : Over (TopCat.of ℝ)) :
    intervalComponentComparisonOver.app A = intervalComponentComparison (overBaseMap A) := rfl

end over

end ReebQuotient

/-! ### Constructible presentations -/

namespace CylinderPresentation

section comparison

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{u} n)
  [∀ i, Finite (ZerothHomotopy (P.V i))] [∀ e, Finite (ZerothHomotopy (P.E e))]
  [∀ i, LocallyPathConnectedSpace (P.V i)] [∀ e, LocallyPathConnectedSpace (P.E e)]

/-- `π₀(θ) ∘ η = π₀(Φ)` on open intervals, from `θ ∘ ρ = Φ`. -/
theorem intervalComponentComparison_comp :
    ReebQuotient.intervalComponentComparison (P.height S) ≫
        intervalComponentNatTrans (P.quotientComponentGraphMap S)
          (P.height_quotientComponentGraphMap S) =
      intervalComponentNatTrans (P.componentGraphMap S) (P.height_componentGraphMap S) := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- Pointwise form of `intervalComponentComparison_comp`. -/
theorem intervalComponentComparison_comp_apply (I : OpenInterval)
    (x : (intervalComponents (P.height S)).obj I) :
    (intervalComponentNatTrans (P.quotientComponentGraphMap S)
        (P.height_quotientComponentGraphMap S)).app I
        ((ReebQuotient.intervalComponentComparison (P.height S)).app I x) =
      (intervalComponentNatTrans (P.componentGraphMap S) (P.height_componentGraphMap S)).app I
        x := by
  induction x using ZerothHomotopy.rec with
  | mk x => rfl

/-- At the star `J i`, `π₀(Φ)` carries the component bijection of `P` to that of the component
graph, precomposed with `c ↦ [c]` on its discrete vertex set: `[v] ↦ [(i, [v])]`. -/
theorem componentGraphMap_star (i : Fin (n + 1)) (c : ZerothHomotopy (P.V i)) :
    (intervalComponentNatTrans (P.componentGraphMap S) (P.height_componentGraphMap S)).app (S.J i)
        (P.vertexComponentsEquiv S i c) =
      (ofFiniteData P.componentData).vertexComponentsEquiv S i
        (ZerothHomotopy.mk (X := (ofFiniteData P.componentData).V i) c) := by
  induction c using ZerothHomotopy.rec with
  | mk v => rfl

/-- At the gap `K e`, `π₀(Φ)` carries the component bijection of `P` at a regular height `t` to that
of the component graph at `t`, precomposed with `c ↦ [c]`: `[y] ↦ [(e, [y], t)]`. -/
theorem componentGraphMap_gap (e : Fin n) (t : (S.K e : Set ℝ)) (c : ZerothHomotopy (P.E e)) :
    (intervalComponentNatTrans (P.componentGraphMap S) (P.height_componentGraphMap S)).app (S.K e)
        (P.edgeComponentsEquiv S e t c) =
      (ofFiniteData P.componentData).edgeComponentsEquiv S e t
        (ZerothHomotopy.mk (X := (ofFiniteData P.componentData).E e) c) := by
  induction c using ZerothHomotopy.rec with
  | mk y => rfl

/-- **`π₀(Φ)` is a natural isomorphism** on open intervals: its star and gap components are
bijective, and the short-interval test `CriticalValues.isIso_iff_shortIntervals` (DMP
Corollary 3.14) applies because both sides are constructible at `S` and interval cosheaves. -/
theorem isIso_intervalComponentNatTrans_componentGraphMap :
    IsIso (intervalComponentNatTrans (P.componentGraphMap S) (P.height_componentGraphMap S)) := by
  refine (S.isIso_iff_shortIntervals (P.intervalComponents_isConstructibleAt S)
    (intervalComponents_isIntervalCosheaf _) (finiteData_isConstructibleAt S P.componentData)
    (intervalComponents_isIntervalCosheaf _) _).2 ⟨fun i => ?_, fun e => ?_⟩
  · constructor
    · intro x y hxy
      obtain ⟨c, rfl⟩ := (P.vertexComponentsEquiv S i).surjective x
      obtain ⟨d, rfl⟩ := (P.vertexComponentsEquiv S i).surjective y
      rw [P.componentGraphMap_star S i c, P.componentGraphMap_star S i d] at hxy
      have hcd := ((ofFiniteData P.componentData).vertexComponentsEquiv S i).injective hxy
      exact congrArg _
        (joined_eq_of_discrete (A := (ofFiniteData P.componentData).V i) (Quotient.exact hcd))
    · intro z
      obtain ⟨w, rfl⟩ := ((ofFiniteData P.componentData).vertexComponentsEquiv S i).surjective z
      obtain ⟨c, rfl⟩ := ZerothHomotopy.mk_surjective w
      exact ⟨P.vertexComponentsEquiv S i c, P.componentGraphMap_star S i c⟩
  · constructor
    · intro x y hxy
      obtain ⟨c, rfl⟩ := (P.edgeComponentsEquiv S e (RGraph.basePt S e)).surjective x
      obtain ⟨d, rfl⟩ := (P.edgeComponentsEquiv S e (RGraph.basePt S e)).surjective y
      rw [P.componentGraphMap_gap S e _ c, P.componentGraphMap_gap S e _ d] at hxy
      have hcd :=
        ((ofFiniteData P.componentData).edgeComponentsEquiv S e (RGraph.basePt S e)).injective hxy
      exact congrArg _
        (joined_eq_of_discrete (A := (ofFiniteData P.componentData).E e) (Quotient.exact hcd))
    · intro z
      obtain ⟨w, rfl⟩ :=
        ((ofFiniteData P.componentData).edgeComponentsEquiv S e (RGraph.basePt S e)).surjective z
      obtain ⟨c, rfl⟩ := ZerothHomotopy.mk_surjective w
      exact ⟨P.edgeComponentsEquiv S e (RGraph.basePt S e) c, P.componentGraphMap_gap S e _ c⟩

/-- The comparison is bijective at **every** open interval, including `⊥`, rays and `⊤`. -/
theorem bijective_intervalComponentComparison_app (I : OpenInterval) :
    Function.Bijective ((ReebQuotient.intervalComponentComparison (P.height S)).app I) := by
  refine ⟨fun x y hxy => ?_, ReebQuotient.intervalComponentComparison_app_surjective _ I⟩
  have := P.isIso_intervalComponentNatTrans_componentGraphMap S
  have hinj := ((isIso_iff_bijective ((intervalComponentNatTrans (P.componentGraphMap S)
    (P.height_componentGraphMap S)).app I)).1 inferInstance).1
  apply hinj
  rw [← P.intervalComponentComparison_comp_apply S I x,
    ← P.intervalComponentComparison_comp_apply S I y, hxy]

/-- **DMP Theorem 3.17 for presentations.** For pieces that are locally path-connected with finitely
many path components, the comparison `componentComparison` restricted to open intervals is a
natural isomorphism. Compactness is not used. -/
instance isIso_intervalComponentComparison :
    IsIso (ReebQuotient.intervalComponentComparison (P.height S)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro I
  rw [isIso_iff_bijective]
  exact P.bijective_intervalComponentComparison_app S I

/-- The comparison as a natural isomorphism. -/
def intervalComponentComparisonIso :
    intervalComponents (P.height S) ≅ intervalComponents (ReebQuotient.height (P.height S)) :=
  asIso (ReebQuotient.intervalComponentComparison (P.height S))

@[simp]
theorem intervalComponentComparisonIso_hom :
    (P.intervalComponentComparisonIso S).hom =
      ReebQuotient.intervalComponentComparison (P.height S) := rfl

/-- The path-component cosheaf of the Reeb quotient is constructible at the same `S`. -/
theorem isConstructibleAt_intervalComponents_reebQuotient :
    S.IsConstructibleAt (intervalComponents (ReebQuotient.height (P.height S))) :=
  CriticalValues.IsConstructibleAt.of_iso (P.intervalComponentComparisonIso S)
    (P.intervalComponents_isConstructibleAt S)

/-- `π₀(θ)` of the comparison `θ : Q → G` with the component graph is a natural isomorphism as
well. -/
theorem isIso_intervalComponentNatTrans_quotientComponentGraphMap :
    IsIso (intervalComponentNatTrans (P.quotientComponentGraphMap S)
      (P.height_quotientComponentGraphMap S)) := by
  have := P.isIso_intervalComponentNatTrans_componentGraphMap S
  have : IsIso (ReebQuotient.intervalComponentComparison (P.height S) ≫
      intervalComponentNatTrans (P.quotientComponentGraphMap S)
        (P.height_quotientComponentGraphMap S)) := by
    rw [P.intervalComponentComparison_comp S]
    infer_instance
  exact IsIso.of_isIso_comp_left (ReebQuotient.intervalComponentComparison (P.height S)) _

/-- The source's left diagram: at the star `J i`, `π₀(θ) ∘ η` carries the component bijection of
`P` to that of the component graph by `[v] ↦ [(i, [v])]`. -/
theorem intervalComponentComparison_star (i : Fin (n + 1)) (c : ZerothHomotopy (P.V i)) :
    (intervalComponentNatTrans (P.quotientComponentGraphMap S)
        (P.height_quotientComponentGraphMap S)).app (S.J i)
        ((ReebQuotient.intervalComponentComparison (P.height S)).app (S.J i)
          (P.vertexComponentsEquiv S i c)) =
      (ofFiniteData P.componentData).vertexComponentsEquiv S i
        (ZerothHomotopy.mk (X := (ofFiniteData P.componentData).V i) c) := by
  induction c using ZerothHomotopy.rec with
  | mk v => rfl

/-- The source's right diagram: at the gap `K e`, `π₀(θ) ∘ η` carries the component bijection of
`P` at `t` to that of the component graph at `t` by `[y] ↦ [(e, [y], t)]`. -/
theorem intervalComponentComparison_gap (e : Fin n) (t : (S.K e : Set ℝ))
    (c : ZerothHomotopy (P.E e)) :
    (intervalComponentNatTrans (P.quotientComponentGraphMap S)
        (P.height_quotientComponentGraphMap S)).app (S.K e)
        ((ReebQuotient.intervalComponentComparison (P.height S)).app (S.K e)
          (P.edgeComponentsEquiv S e t c)) =
      (ofFiniteData P.componentData).edgeComponentsEquiv S e t
        (ZerothHomotopy.mk (X := (ofFiniteData P.componentData).E e) c) := by
  induction c using ZerothHomotopy.rec with
  | mk y => rfl

end comparison

/-! ### Graph case: agreement with the projection homeomorphism -/

section graph

variable {n : ℕ} (S : CriticalValues n)

/-- The inverse projection `RGraph.projInv` preserves height. -/
theorem height_projInv (D : FiniteReebData.{u} n)
    (q : ReebQuotient ((ofFiniteData D).height S)) :
    (ofFiniteData D).height S (RGraph.projInv S D q) = ReebQuotient.height _ q := by
  induction q using ReebQuotient.ind with
  | h x => rfl

/-- For finite data, the comparison is the path-component map of the projection homeomorphism
`RGraph.projHomeomorph`. -/
theorem intervalComponentComparison_ofFiniteData (D : FiniteReebData.{u} n) :
    ReebQuotient.intervalComponentComparison ((ofFiniteData D).height S) =
      intervalComponentNatTrans (RGraph.projHomeomorph S D : C(_, _))
        (RGraph.height_projHomeomorph S D) := rfl

/-- Its inverse is the path-component map of the inverse projection `RGraph.projInv`. -/
theorem inv_intervalComponentComparison_ofFiniteData (D : FiniteReebData.{u} n) :
    inv (ReebQuotient.intervalComponentComparison ((ofFiniteData D).height S)) =
      intervalComponentNatTrans (RGraph.projInv S D) (height_projInv S D) := by
  refine IsIso.inv_eq_of_hom_inv_id ?_
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

end graph

end CylinderPresentation

/-! ### Constructible ℝ-spaces -/

/-- **DMP Theorem 3.17, objectwise.** At every constructible ℝ-space, the comparison
`componentComparison` restricted to open intervals is an isomorphism. -/
theorem isIso_intervalComponentComparison_of_constructible {A : Over (TopCat.of ℝ)}
    (hA : IsConstructibleSpace A) :
    IsIso (ReebQuotient.intervalComponentComparison (overBaseMap A)) := by
  obtain ⟨n, S, P, h1, h2, h3, h4, ⟨i⟩⟩ := hA
  have hB : IsIso (ReebQuotient.intervalComponentComparisonOver.app
      (Over.mk (TopCat.ofHom (P.height S)))) :=
    P.isIso_intervalComponentComparison S
  exact (NatTrans.isIso_app_iff_of_iso ReebQuotient.intervalComponentComparisonOver i).2 hB

/-- **DMP Theorem 3.17, objectwise and intervalwise.** For every constructible `ℝ`-space and
every open interval, the comparison from path components of the space to path components of its
Reeb quotient is a bijection. -/
theorem bijective_intervalComponentComparison_app_of_constructible {A : Over (TopCat.of ℝ)}
    (hA : IsConstructibleSpace A) (I : OpenInterval) :
    Function.Bijective ((ReebQuotient.intervalComponentComparison (overBaseMap A)).app I) := by
  let _ := isIso_intervalComponentComparison_of_constructible hA
  exact (isIso_iff_bijective _).1 inferInstance

/-- DMP, proof of Theorem 3.17: for a constructible ℝ-space, the path-component cosheaves of the
space and of its Reeb quotient are constructible at a common list of levels. -/
theorem exists_isConstructibleAt_of_isConstructibleSpace {A : Over (TopCat.of ℝ)}
    (hA : IsConstructibleSpace A) :
    ∃ (n : ℕ) (S : CriticalValues n), S.IsConstructibleAt (intervalComponents (overBaseMap A)) ∧
      S.IsConstructibleAt (intervalComponents (ReebQuotient.height (overBaseMap A))) := by
  obtain ⟨n, S, P, h1, h2, h3, h4, ⟨i⟩⟩ := hA
  exact ⟨n, S,
    CriticalValues.IsConstructibleAt.of_iso
      (intervalComponentsOver.mapIso i).symm
      (P.intervalComponents_isConstructibleAt S),
    CriticalValues.IsConstructibleAt.of_iso
      ((ReebQuotient.quotientFunctor ℝ ⋙ intervalComponentsOver).mapIso i).symm
      (P.isConstructibleAt_intervalComponents_reebQuotient S)⟩

/-- On graph objects the comparison is an isomorphism by the projection isomorphism alone: it is
`𝒞` applied to `RGraph.projNatIso`. -/
theorem isIso_intervalComponentComparison_of_isRGraph {A : Over (TopCat.of ℝ)}
    (hA : RGraph.IsRGraph A) :
    IsIso (ReebQuotient.intervalComponentComparison (overBaseMap A)) :=
  (intervalComponentsOver.mapIso (RGraph.projNatIso.app ⟨A, hA⟩)).isIso_hom

/-- The comparison `componentComparisonOver ℝ` on the full subcategory of constructible ℝ-spaces,
on open intervals. -/
def constructibleComponentComparison :
    IsConstructibleSpace.ι ⋙ intervalComponentsOver ⟶
      IsConstructibleSpace.ι ⋙ ReebQuotient.quotientFunctor ℝ ⋙ intervalComponentsOver :=
  Functor.whiskerLeft IsConstructibleSpace.ι ReebQuotient.intervalComponentComparisonOver

theorem constructibleComponentComparison_app (A : ConstructibleSpaceCat) :
    constructibleComponentComparison.app A =
      ReebQuotient.intervalComponentComparison (overBaseMap A.obj) := rfl

instance isIso_constructibleComponentComparison : IsIso constructibleComponentComparison := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  exact isIso_intervalComponentComparison_of_constructible A.property

/-- **DMP Theorem 3.17**: on constructible ℝ-spaces with all continuous height-preserving maps, the
comparison `componentComparison` restricted to open intervals is a natural isomorphism
`𝒞 ≅ 𝒞ℛ`. -/
def constructibleComponentComparisonIso :
    IsConstructibleSpace.ι ⋙ intervalComponentsOver ≅
      IsConstructibleSpace.ι ⋙ ReebQuotient.quotientFunctor ℝ ⋙ intervalComponentsOver :=
  asIso constructibleComponentComparison

@[simp]
theorem constructibleComponentComparisonIso_hom_app (A : ConstructibleSpaceCat) :
    constructibleComponentComparisonIso.hom.app A =
      ReebQuotient.intervalComponentComparison (overBaseMap A.obj) := rfl

/-- The naturality square for every morphism of constructible ℝ-spaces, derived from
`componentComparison_natural`. -/
theorem constructibleComponentComparison_naturality {A B : ConstructibleSpaceCat} (g : A ⟶ B) :
    intervalComponentsOver.map g.hom ≫
        ReebQuotient.intervalComponentComparison (overBaseMap B.obj) =
      ReebQuotient.intervalComponentComparison (overBaseMap A.obj) ≫
        intervalComponentsOver.map ((ReebQuotient.quotientFunctor ℝ).map g.hom) :=
  ReebQuotient.intervalComponentComparison_natural g.hom.left.hom (overBaseMap_comm g.hom)

/-- On graph objects the natural isomorphism is `𝒞` applied to the projection isomorphism
`RGraph.projNatIso`. -/
theorem constructibleComponentComparisonIso_app_of_isRGraph {A : Over (TopCat.of ℝ)}
    (hA : RGraph.IsRGraph A) :
    constructibleComponentComparisonIso.app ⟨A, isConstructibleSpace_of_isRGraph hA⟩ =
      intervalComponentsOver.mapIso (RGraph.projNatIso.app ⟨A, hA⟩) :=
  Iso.ext rfl

/-! ### The comparison as a natural isomorphism of constructible cosheaves -/

/-- The source's `𝒞'`: interval path components of constructible ℝ-spaces, as constructible
cosheaves. Both cosheaf conditions hold because the path components of every space over `ℝ` form an
interval cosheaf and those of a constructible ℝ-space are constructible. -/
def constructibleCosheafFunctor : ConstructibleSpaceCat ⥤ ConstructibleCosheafCat.{0} :=
  ObjectProperty.lift IsConstructibleCosheaf.{0}
    (IsConstructibleSpace.ι ⋙ intervalComponentsOver) fun A => by
      obtain ⟨n, S, h, -⟩ := exists_isConstructibleAt_of_isConstructibleSpace A.property
      exact IsConstructibleCosheaf.of_isConstructibleAt h (intervalComponents_isIntervalCosheaf _)

/-- **DMP Theorem 3.17**, in the source's form `𝒞' ≅ 𝒞''ℛ`: a natural isomorphism of functors from
constructible ℝ-spaces to constructible cosheaves, with `ℛ = quotientRGraphFunctor` and
`𝒞'' = RGraph.cosheafFunctor`. Its components are the comparison itself
(`constructibleCosheafComparisonIso_hom_app_hom`). -/
def constructibleCosheafComparisonIso :
    constructibleCosheafFunctor ≅ quotientRGraphFunctor ⋙ RGraph.cosheafFunctor :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ (constructibleComponentComparisonIso.app A))
    (fun g => by
      ext1
      exact constructibleComponentComparison_naturality g)

/-- The component at `A` is the comparison of the structure map of `A`, that is,
`componentComparison` precomposed with `toOpensFunctor` (`intervalComponentComparison_eq`). -/
theorem constructibleCosheafComparisonIso_hom_app_hom (A : ConstructibleSpaceCat) :
    (constructibleCosheafComparisonIso.hom.app A).hom =
      ReebQuotient.intervalComponentComparison (overBaseMap A.obj) := rfl

end

end TDA.Reeb
