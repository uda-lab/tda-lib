import TDA.Reeb.IntervalSingularHomology
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Paths and functionals on singular homology of degree zero

`TDA.Reeb.IntervalSingularHomology` defines the class `singularHomology₀Class X R x : R ⟶ H₀(X; R)`
of a point, identifies it with a coproduct injection under Mathlib's
`TopCat.singularHomology₀Iso` and proves its naturality. This module adds two generic facts used to
compute with these classes, for any space `X` and coefficients `R` in a preadditive category with
coproducts and homology (for instance `ModuleCat.of k k` over a ring `k`):

* **Paths.** The two endpoints of a path have the same class
  (`singularHomology₀Class_eq_of_path`).
* **Functionals from locally constant functions.** A locally constant `g : X → (R ⟶ T)` induces
  `singularHomology₀Desc X R g hg : H₀(X; R) ⟶ T`, with value `g x` on the class of `x`
  (`singularHomology₀Class_comp_singularHomology₀Desc`). Through `TopCat.singularHomology₀Iso` it
  is `g` on the summand of each path component; this is how a class in `H₀` is shown to be
  nonzero.
-/

open CategoryTheory Limits AlgebraicTopology

universe w

namespace TDA.Reeb

variable {C : Type*} [Category C] [HasCoproducts.{w} C] [Preadditive C] [CategoryWithHomology C]
  (X : TopCat.{w}) (R : C)

/-- **The endpoints of a path have the same class** in `H₀`. -/
theorem singularHomology₀Class_eq_of_path {x y : X} (γ : Path x y) :
    singularHomology₀Class X R x = singularHomology₀Class X R y := by
  rw [← cancel_mono (TopCat.singularHomology₀Iso X R).hom,
    singularHomology₀Class_comp_singularHomology₀Iso_hom,
    singularHomology₀Class_comp_singularHomology₀Iso_hom, ZerothHomotopy.sound γ]

/-- A locally constant function is constant along every path. -/
private theorem apply_eq_of_path {Z : Type*} [TopologicalSpace Z] {T : Type*} {g : Z → T}
    (hg : IsLocallyConstant g) {x y : Z} (γ : Path x y) : g x = g y :=
  hg.apply_eq_of_isPreconnected (isPreconnected_range γ.continuous) ⟨0, γ.source⟩
    ⟨1, γ.target⟩

/-- The functional `H₀(X; R) ⟶ T` induced by a locally constant function `g : X → (R ⟶ T)`:
through `TopCat.singularHomology₀Iso`, it is `g` on the summand of each path component. -/
noncomputable def singularHomology₀Desc {T : C} (g : X → (R ⟶ T)) (hg : IsLocallyConstant g) :
    ((singularHomologyFunctor C 0).obj R).obj X ⟶ T :=
  (TopCat.singularHomology₀Iso X R).hom ≫
    Sigma.desc (ZerothHomotopy.lift g fun _ _ γ => apply_eq_of_path hg γ)

/-- **The value of the functional on a point class**: the functional induced by a locally constant
`g` takes the value `g x` on the class of `x`. -/
@[reassoc (attr := simp)]
theorem singularHomology₀Class_comp_singularHomology₀Desc {T : C} (g : X → (R ⟶ T))
    (hg : IsLocallyConstant g) (x : X) :
    singularHomology₀Class X R x ≫ singularHomology₀Desc X R g hg = g x := by
  simp [singularHomology₀Desc]

end TDA.Reeb
