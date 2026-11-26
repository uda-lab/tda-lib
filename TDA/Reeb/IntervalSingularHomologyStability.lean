import TDA.Reeb.IntervalSingularHomology
import TDA.Reeb.GeometricEnlargement
import TDA.Reeb.Stability

/-!
# Perturbation stability of interval singular homology

For continuous `f g : C(X, ℝ)` with `∀ x, |f x - g x| ≤ ε`, the interval functors
`intervalSingularHomology k n f` and `intervalSingularHomology k n g` are `ε`-interleaved, in
every degree `n` and over every ring `k`, with no compactness, tameness or finiteness
assumption. The witness is singular homology applied to the continuous inclusions
`perturbationInclusion h I : f ⁻¹ I → g ⁻¹ T_ε I` and, for the reverse direction, to the
inclusions of the swapped bound `perturbationBound_symm h`.

* `intervalSingularHomologyPerturbation k n h` is the natural transformation
  `H_n(f ⁻¹ I) ⟶ H_n(g ⁻¹ T_ε I)` into the smoothing `S_ε (intervalSingularHomology k n g)` of
  the category-polymorphic `TDA.Reeb.smoothing`.
* `intervalSingularHomologyInterleaving k n h` is the `ε`-interleaving built with
  `Interleaving.ofApp`. Both interleaving triangles are functoriality of singular homology: the
  composed inclusions are the same subtype inclusions as `thickenUnit`, so the two
  `TopCat` morphisms agree by extensionality on points.
* The witness is compatible with the interleaving laws exactly as `perturbationInterleaving`:
  `_self`, `_symm`, `_mono` and `_trans` follow from the corresponding equalities of subtype
  inclusions.
* `interleavingDistance_intervalSingularHomology_le` is the radius inequality
  `d(H_n f, H_n g) ≤ ε`, and `interleavingDistance_intervalSingularHomology_le_edist` the
  extended supremum bound `d(H_n f, H_n g) ≤ ‖f − g‖∞ ∈ [0, ∞]`, via
  `edist_uniformFun_ofFun_le_coe_iff` as for the component functors.
* In degree zero, `linearizedPerturbationInterleaving` is the existing path-component witness
  `perturbationInterleaving` pushed along `sigmaConst.obj (ModuleCat.of k k)`
  (`Interleaving.postcomp`). `intervalSingularHomologyPerturbation_zero` shows that the degree-zero
  witness is the linearized one conjugated by `intervalSingularHomologyIso₀`, the key step being
  the naturality `singularHomology₀Iso_hom_naturality` of the isomorphism for the inclusion.
  `intervalSingularHomologyInterleaving_zero` states the same for the interleaving.

The bound is pointwise, as in `TDA.Reeb.Perturbation`. Higher degrees are not compared with
path components, and Mayer–Vietoris compatibility is a separate result. See
`docs/math/reeb-interval-singular-homology.md`.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped NNReal ENNReal UniformConvergence

universe u

namespace TDA.Reeb

open OpenInterval

/-! ### Post-composition of interleavings -/

section Postcomp

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- Post-composing the two witnesses of an interleaving with a functor `G : C ⥤ D` gives an
interleaving of the post-composed precosheaves: `G` preserves the two triangle identities. -/
def Interleaving.postcomp {ε : ℝ≥0} {F F' : OpenInterval ⥤ C} (i : Interleaving ε F F')
    (G : C ⥤ D) : Interleaving ε (F ⋙ G) (F' ⋙ G) :=
  Interleaving.ofApp (Functor.whiskerRight i.φ G) (Functor.whiskerRight i.ψ G)
    (fun I => by
      change G.map (i.φ.app I) ≫ G.map (i.ψ.app (thicken ε I)) = G.map _
      rw [← G.map_comp, i.φ_ψ_app])
    (fun I => by
      change G.map (i.ψ.app I) ≫ G.map (i.φ.app (thicken ε I)) = G.map _
      rw [← G.map_comp, i.ψ_φ_app])

@[simp]
theorem Interleaving.postcomp_φ {ε : ℝ≥0} {F F' : OpenInterval ⥤ C} (i : Interleaving ε F F')
    (G : C ⥤ D) : (i.postcomp G).φ = Functor.whiskerRight i.φ G := rfl

@[simp]
theorem Interleaving.postcomp_ψ {ε : ℝ≥0} {F F' : OpenInterval ⥤ C} (i : Interleaving ε F F')
    (G : C ⥤ D) : (i.postcomp G).ψ = Functor.whiskerRight i.ψ G := rfl

end Postcomp

/-! ### The witness in every degree -/

section Perturbation

variable {X : Type u} [TopologicalSpace X] (k : Type u) [Ring k] (n : ℕ)

/-- Singular homology in degree `n` with coefficients `ModuleCat.of k k`, as a functor on `TopCat`;
the functor behind `intervalSingularHomology`. -/
private noncomputable abbrev singHom : TopCat.{u} ⥤ ModuleCat.{u} k :=
  (singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)

/-- The inclusion `f ⁻¹ I → g ⁻¹ T_ε I` as a morphism of `TopCat`. -/
def perturbationTopHom {f g : C(X, ℝ)} {ε : ℝ≥0} (h : ∀ x, |f x - g x| ≤ ε) (I : OpenInterval) :
    (intervalPreimageTopCat f).obj I ⟶ (intervalPreimageTopCat g).obj (thicken ε I) :=
  TopCat.ofHom (perturbationInclusion h I)

@[simp]
theorem perturbationTopHom_apply_val {f g : C(X, ℝ)} {ε : ℝ≥0} (h : ∀ x, |f x - g x| ≤ ε)
    (I : OpenInterval) (x : (intervalPreimageTopCat f).obj I) :
    (perturbationTopHom h I x).1 = x.1 := rfl

/-- Two morphisms of interval preimages are equal when they are the identity on points. -/
theorem intervalPreimageTopCat_hom_ext {f g : C(X, ℝ)} {I J : OpenInterval}
    (a b : (intervalPreimageTopCat f).obj I ⟶ (intervalPreimageTopCat g).obj J)
    (h : ∀ x, (a x).1 = (b x).1) : a = b := by
  ext x
  exact Subtype.ext (h x)

/-- The inclusions `perturbationTopHom` are natural in the interval. -/
theorem perturbationTopHom_naturality {f g : C(X, ℝ)} {ε : ℝ≥0} (h : ∀ x, |f x - g x| ≤ ε)
    {I J : OpenInterval} (i : I ⟶ J) :
    (intervalPreimageTopCat f).map i ≫ perturbationTopHom h J =
      perturbationTopHom h I ≫ (intervalPreimageTopCat g).map ((thickenFunctor ε).map i) :=
  intervalPreimageTopCat_hom_ext _ _ fun _ => rfl

/-- The witness `H_n(f ⁻¹ I) ⟶ H_n(g ⁻¹ T_ε I)`: singular homology applied to the continuous
inclusions `perturbationInclusion`. -/
noncomputable def intervalSingularHomologyPerturbation {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    intervalSingularHomology k n f ⟶ (smoothing ε).obj (intervalSingularHomology k n g) where
  app I := (singHom k n).map (perturbationTopHom h I)
  naturality _ _ i :=
    ((singHom k n).map_comp _ _).symm.trans
      ((congrArg (singHom k n).map (perturbationTopHom_naturality h i)).trans
        ((singHom k n).map_comp _ _))

variable {k n}

@[simp]
theorem intervalSingularHomologyPerturbation_app {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) (I : OpenInterval) :
    (intervalSingularHomologyPerturbation k n h).app I =
      (singHom k n).map (perturbationTopHom h I) := rfl

/-- **Perturbation stability of interval singular homology.** A uniform bound `ε` on `f − g`
gives an `ε`-interleaving of `intervalSingularHomology k n f` and
`intervalSingularHomology k n g`, in every degree and over every ring. -/
noncomputable def intervalSingularHomologyInterleaving {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    Interleaving ε (intervalSingularHomology k n f) (intervalSingularHomology k n g) :=
  Interleaving.ofApp (intervalSingularHomologyPerturbation k n h)
    (intervalSingularHomologyPerturbation k n (perturbationBound_symm h))
    (fun _ => ((singHom k n).map_comp _ _).symm.trans
      (congrArg (singHom k n).map (intervalPreimageTopCat_hom_ext _ _ fun _ => rfl)))
    (fun _ => ((singHom k n).map_comp _ _).symm.trans
      (congrArg (singHom k n).map (intervalPreimageTopCat_hom_ext _ _ fun _ => rfl)))

@[simp]
theorem intervalSingularHomologyInterleaving_φ {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    (intervalSingularHomologyInterleaving (k := k) (n := n) h).φ =
      intervalSingularHomologyPerturbation k n h := rfl

@[simp]
theorem intervalSingularHomologyInterleaving_ψ {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    (intervalSingularHomologyInterleaving (k := k) (n := n) h).ψ =
      intervalSingularHomologyPerturbation k n (perturbationBound_symm h) := rfl

/-- Existence form of `intervalSingularHomologyInterleaving`. -/
theorem nonempty_interleaving_intervalSingularHomology {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    Nonempty (Interleaving ε (intervalSingularHomology k n f) (intervalSingularHomology k n g)) :=
  ⟨intervalSingularHomologyInterleaving h⟩

/-- `f = g`: the witnesses are the identity (unit) witnesses at every `ε`. -/
theorem intervalSingularHomologyInterleaving_self (f : C(X, ℝ)) {ε : ℝ≥0}
    (h : ∀ x, |f x - f x| ≤ ε) :
    intervalSingularHomologyInterleaving (k := k) (n := n) h =
      Interleaving.refl ε (intervalSingularHomology k n f) := by
  have e : ∀ I : OpenInterval, perturbationTopHom h I =
      (intervalPreimageTopCat f).map ((thickenUnit ε).app I) := fun I =>
    intervalPreimageTopCat_hom_ext _ _ fun _ => rfl
  refine Interleaving.ext (NatTrans.ext (funext fun I => ?_)) (NatTrans.ext (funext fun I => ?_))
  · exact congrArg (singHom k n).map (e I)
  · exact congrArg (singHom k n).map (e I)

/-- Symmetry is the swapped bound. -/
theorem intervalSingularHomologyInterleaving_symm {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    (intervalSingularHomologyInterleaving (k := k) (n := n) h).symm =
      intervalSingularHomologyInterleaving (perturbationBound_symm h) :=
  rfl

/-- Enlargement is the weakened bound. -/
theorem intervalSingularHomologyInterleaving_mono {f g : C(X, ℝ)} {ε ε' : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) (hε : ε ≤ ε') :
    (intervalSingularHomologyInterleaving (k := k) (n := n) h).mono hε =
      intervalSingularHomologyInterleaving (fun x => (h x).trans (by exact_mod_cast hε)) := by
  have e : ∀ {f g : C(X, ℝ)} (h : ∀ x, |f x - g x| ≤ ε) (h' : ∀ x, |f x - g x| ≤ ε')
      (I : OpenInterval),
      perturbationTopHom h I ≫ (intervalPreimageTopCat g).map ((thickenMap hε).app I) =
        perturbationTopHom h' I := fun h h' I =>
    intervalPreimageTopCat_hom_ext _ _ fun _ => rfl
  refine Interleaving.ext (NatTrans.ext (funext fun I => ?_)) (NatTrans.ext (funext fun I => ?_))
  · exact ((singHom k n).map_comp _ _).symm.trans (congrArg (singHom k n).map (e h _ I))
  · exact ((singHom k n).map_comp _ _).symm.trans
      (congrArg (singHom k n).map (e (perturbationBound_symm h) _ I))

/-- Composition is the triangle-inequality bound. -/
theorem intervalSingularHomologyInterleaving_trans {f g h : C(X, ℝ)} {ε δ : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) (hgh : ∀ x, |g x - h x| ≤ δ)
    (hfh : ∀ x, |f x - h x| ≤ (ε + δ : ℝ≥0)) :
    (intervalSingularHomologyInterleaving (k := k) (n := n) hfg).trans
        (intervalSingularHomologyInterleaving hgh) =
      intervalSingularHomologyInterleaving hfh := by
  refine Interleaving.ext (NatTrans.ext (funext fun I => ?_)) (NatTrans.ext (funext fun I => ?_))
  · show (singHom k n).map _ ≫ (singHom k n).map _ ≫ (singHom k n).map _ =
      (singHom k n).map _
    erw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (singHom k n).map (intervalPreimageTopCat_hom_ext _ _ fun _ => rfl)
  · show (singHom k n).map _ ≫ (singHom k n).map _ ≫ (singHom k n).map _ ≫ (singHom k n).map _ =
      (singHom k n).map _
    erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (singHom k n).map (intervalPreimageTopCat_hom_ext _ _ fun _ => rfl)

/-! #### Distance bounds -/

/-- **Radius inequality.** `d(H_n f, H_n g) ≤ ε` when `|f x - g x| ≤ ε` for all `x`. -/
theorem interleavingDistance_intervalSingularHomology_le {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    interleavingDistance (intervalSingularHomology k n f) (intervalSingularHomology k n g) ≤ ε :=
  (intervalSingularHomologyInterleaving h).interleavingDistance_le

/-- **Extended supremum bound.** `d(H_n f, H_n g) ≤ ‖f − g‖∞`, with `‖f − g‖∞ ∈ [0, ∞]` mathlib's
uniform extended distance. No compactness, boundedness, finiteness or nonemptiness of `X` is
assumed; an infinite distance gives the trivial bound. -/
theorem interleavingDistance_intervalSingularHomology_le_edist (f g : C(X, ℝ)) :
    interleavingDistance (intervalSingularHomology k n f) (intervalSingularHomology k n g) ≤
      edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) := by
  by_cases htop : edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) = ⊤
  · rw [htop]
    exact le_top
  · rw [← ENNReal.coe_toNNReal htop]
    exact interleavingDistance_intervalSingularHomology_le
      (edist_uniformFun_ofFun_le_coe_iff.1 (ENNReal.coe_toNNReal htop).ge)

end Perturbation

/-! ### Degree zero: conjugation by the path-component comparison -/

section DegreeZero

variable {X : Type u} [TopologicalSpace X] (k : Type u) [Ring k]

/-- The existing path-component witness `perturbationInterleaving`, linearized over `k`: the
interleaving of `linearizedIntervalComponents k f` and `linearizedIntervalComponents k g` obtained
by post-composing with `sigmaConst.obj (ModuleCat.of k k)`. -/
noncomputable def linearizedPerturbationInterleaving {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    Interleaving ε (linearizedIntervalComponents k f) (linearizedIntervalComponents k g) :=
  (perturbationInterleaving h).postcomp (sigmaConst.obj (ModuleCat.of k k))

variable {k}

@[simp]
theorem linearizedPerturbationInterleaving_φ {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    (linearizedPerturbationInterleaving k h).φ =
      Functor.whiskerRight (perturbationNatTrans h) (sigmaConst.obj (ModuleCat.of k k)) := rfl

@[simp]
theorem linearizedPerturbationInterleaving_ψ {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    (linearizedPerturbationInterleaving k h).ψ =
      Functor.whiskerRight (perturbationNatTrans (perturbationBound_symm h))
        (sigmaConst.obj (ModuleCat.of k k)) := rfl

/-- Naturality of the degree-zero comparison for one perturbation inclusion: the degree-zero
homology of `perturbationInclusion` is the linearized map of path components. -/
theorem intervalSingularHomologyPerturbation_app_comp_iso₀ {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) (I : OpenInterval) :
    (intervalSingularHomologyPerturbation k 0 h).app I ≫
        (intervalSingularHomologyIso₀ k g).hom.app (thicken ε I) =
      (intervalSingularHomologyIso₀ k f).hom.app I ≫
        ((linearizedPerturbationInterleaving k h).φ).app I :=
  singularHomology₀Iso_hom_naturality (perturbationTopHom h I) (ModuleCat.of k k)

/-- Map rule: the degree-zero witness sends the class of a point of `f ⁻¹ I` to the class of the
same point in `g ⁻¹ T_ε I`. -/
theorem intervalClass_comp_intervalSingularHomologyPerturbation_app {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) (I : OpenInterval) (x : (intervalPreimageTopCat f).obj I) :
    intervalClass k f I x ≫ (intervalSingularHomologyPerturbation k 0 h).app I =
      intervalClass k g (thicken ε I) (perturbationTopHom h I x) :=
  singularHomology₀Class_comp_map _ _ _

/-- **Degree zero, matching maps.** The degree-zero witness is the linearized path-component
witness conjugated by `intervalSingularHomologyIso₀`: the first map is
`iso₀ f ≫ (linearized φ) ≫ S_ε (iso₀ g)⁻¹`. -/
theorem intervalSingularHomologyPerturbation_zero {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    intervalSingularHomologyPerturbation k 0 h =
      (intervalSingularHomologyIso₀ k f).hom ≫ (linearizedPerturbationInterleaving k h).φ ≫
        (smoothing ε).map (intervalSingularHomologyIso₀ k g).inv := by
  ext I
  dsimp only [NatTrans.comp_app, smoothing_map_app]
  rw [← Category.assoc, ← intervalSingularHomologyPerturbation_app_comp_iso₀, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- **Degree zero, interleaving form.** The degree-zero witness is the linearized
path-component witness transported along `intervalSingularHomologyIso₀`. -/
theorem intervalSingularHomologyInterleaving_zero {f g : C(X, ℝ)} {ε : ℝ≥0}
    (h : ∀ x, |f x - g x| ≤ ε) :
    intervalSingularHomologyInterleaving (k := k) (n := 0) h =
      (((linearizedPerturbationInterleaving k h).isoRight
          (intervalSingularHomologyIso₀ k g).symm).symm.isoRight
        (intervalSingularHomologyIso₀ k f).symm).symm := by
  refine Interleaving.ext ?_ ?_
  · rw [intervalSingularHomologyInterleaving_φ, intervalSingularHomologyPerturbation_zero]
    rfl
  · rw [intervalSingularHomologyInterleaving_ψ,
      intervalSingularHomologyPerturbation_zero (perturbationBound_symm h)]
    rfl

end DegreeZero

end TDA.Reeb
