import TDA.Reeb.IntervalComponents
import TDA.Reeb.Smoothing
import TDA.Reeb.InterleavingDistance
import TDA.Reeb.Perturbation
import TDA.Topology.PathComponents

/-!
# Interleavings from height-controlled map pairs

For continuous heights `f : C(X, ℝ)` and `g : C(X', ℝ)` on spaces in one universe, a
`HeightMapPair f g ε` consists of continuous maps in both directions whose height errors are at
most `ε`. Each composite is also required to join every point to its image by a path whose `f`-
or `g`-height stays within `ε + ε` of the starting height. These data induce an explicit
`ε`-interleaving of the interval path-component precosheaves, hence a bound on their
interleaving distance. Identity maps and constant paths recover the usual pointwise perturbation
interleaving on one space. The hypotheses are sufficient; no converse, functional-distortion
identity, or map between Reeb graph objects is established here. -/

open Set CategoryTheory TDA.Topology
open scoped NNReal

universe u

namespace TDA.Reeb

open OpenInterval

/-- Continuous maps between two height spaces whose map errors are at most `ε` and whose
composites are joined to the identity by paths with height deviation at most `ε + ε`. -/
structure HeightMapPair {X X' : Type u} [TopologicalSpace X] [TopologicalSpace X']
    (f : C(X, ℝ)) (g : C(X', ℝ)) (ε : ℝ≥0) where
  /-- The map from the `f`-space to the `g`-space. -/
  φ : C(X, X')
  /-- The map from the `g`-space to the `f`-space. -/
  ψ : C(X', X)
  /-- The forward map changes height by at most `ε`. -/
  hφ : ∀ x, |g (φ x) - f x| ≤ ε
  /-- The reverse map changes height by at most `ε`. -/
  hψ : ∀ y, |f (ψ y) - g y| ≤ ε
  /-- The first composite is joined to the identity through heights within `ε + ε`. -/
  hψφ : ∀ x, ∃ γ : Path x (ψ (φ x)), ∀ t, |f (γ t) - f x| ≤ ε + ε
  /-- The second composite is joined to the identity through heights within `ε + ε`. -/
  hφψ : ∀ y, ∃ γ : Path y (φ (ψ y)), ∀ t, |g (γ t) - g y| ≤ ε + ε

namespace HeightMapPair

variable {X X' : Type u} [TopologicalSpace X] [TopologicalSpace X']
  {f : C(X, ℝ)} {g : C(X', ℝ)} {ε : ℝ≥0}

private def forwardOnInterval (P : HeightMapPair f g ε) (I : OpenInterval) :
    C({x : X // f x ∈ I}, {y : X' // g y ∈ thicken ε I}) where
  toFun x := ⟨P.φ x.1, mem_thicken_of_abs_sub_le x.2 (P.hφ x.1)⟩
  continuous_toFun := by fun_prop

private def reverseOnInterval (P : HeightMapPair f g ε) (I : OpenInterval) :
    C({y : X' // g y ∈ I}, {x : X // f x ∈ thicken ε I}) where
  toFun y := ⟨P.ψ y.1, mem_thicken_of_abs_sub_le y.2 (P.hψ y.1)⟩
  continuous_toFun := by fun_prop

/-- The forward map pair induces a natural transformation on interval path components. -/
def natTrans (P : HeightMapPair f g ε) :
    intervalComponents f ⟶ (smoothing ε).obj (intervalComponents g) where
  app I := TypeCat.ofHom (componentMap (forwardOnInterval P I))
  naturality I J i := by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

/-- The reverse map pair induces a natural transformation on interval path components. -/
def natTransSymm (P : HeightMapPair f g ε) :
    intervalComponents g ⟶ (smoothing ε).obj (intervalComponents f) where
  app I := TypeCat.ofHom (componentMap (reverseOnInterval P I))
  naturality I J i := by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk y => rfl

@[simp]
theorem natTrans_app_mk (P : HeightMapPair f g ε) (I : OpenInterval)
    (x : {x : X // f x ∈ toOpens I}) :
    (P.natTrans.app I) (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨P.φ x.1, mem_thicken_of_abs_sub_le x.2 (P.hφ x.1)⟩ :
        {y : X' // g y ∈ toOpens (thicken ε I)}) := rfl

@[simp]
theorem natTransSymm_app_mk (P : HeightMapPair f g ε) (I : OpenInterval)
    (y : {y : X' // g y ∈ toOpens I}) :
    (P.natTransSymm.app I) (ZerothHomotopy.mk y) =
      ZerothHomotopy.mk (⟨P.ψ y.1, mem_thicken_of_abs_sub_le y.2 (P.hψ y.1)⟩ :
        {x : X // f x ∈ toOpens (thicken ε I)}) := rfl

private theorem joinedIn_doubleThicken_f (P : HeightMapPair f g ε) (I : OpenInterval)
    (x : {x : X // f x ∈ I}) :
    JoinedIn (f ⁻¹' (thicken ε (thicken ε I) : Set ℝ)) x.1 (P.ψ (P.φ x.1)) := by
  obtain ⟨γ, hγ⟩ := P.hψφ x.1
  refine ⟨γ, fun t => ?_⟩
  have hmem := mem_thicken_of_abs_sub_le (ε := ε + ε) x.2 (hγ t)
  rw [← thicken_thicken ε ε I] at hmem
  exact hmem

private theorem joinedIn_doubleThicken_g (P : HeightMapPair f g ε) (I : OpenInterval)
    (y : {y : X' // g y ∈ I}) :
    JoinedIn (g ⁻¹' (thicken ε (thicken ε I) : Set ℝ)) y.1 (P.φ (P.ψ y.1)) := by
  obtain ⟨γ, hγ⟩ := P.hφψ y.1
  refine ⟨γ, fun t => ?_⟩
  have hmem := mem_thicken_of_abs_sub_le (ε := ε + ε) y.2 (hγ t)
  rw [← thicken_thicken ε ε I] at hmem
  exact hmem

/-- The pair maps define an `ε`-interleaving of the two interval path-component precosheaves. -/
def interleaving (P : HeightMapPair f g ε) :
    Interleaving ε (intervalComponents f) (intervalComponents g) :=
  Interleaving.ofApp P.natTrans P.natTransSymm
    (fun I => by
      ext c
      induction c using ZerothHomotopy.rec with
      | mk x =>
        have hx : f x.1 ∈ thicken ε (thicken ε I) :=
          ((le_thicken ε I).trans (le_thicken ε _)) x.2
        exact (mk_eq_of_joinedIn f (thicken ε (thicken ε I))
          (joinedIn_doubleThicken_f P I x) hx
          (joinedIn_doubleThicken_f P I x).target_mem).symm)
    (fun I => by
      ext c
      induction c using ZerothHomotopy.rec with
      | mk y =>
        have hy : g y.1 ∈ thicken ε (thicken ε I) :=
          ((le_thicken ε I).trans (le_thicken ε _)) y.2
        exact (mk_eq_of_joinedIn g (thicken ε (thicken ε I))
          (joinedIn_doubleThicken_g P I y) hy
          (joinedIn_doubleThicken_g P I y).target_mem).symm)

@[simp]
theorem interleaving_φ (P : HeightMapPair f g ε) :
    P.interleaving.φ = P.natTrans := rfl

@[simp]
theorem interleaving_ψ (P : HeightMapPair f g ε) :
    P.interleaving.ψ = P.natTransSymm := rfl

/-- Swap the spaces and the two maps. -/
def symm (P : HeightMapPair f g ε) : HeightMapPair g f ε where
  φ := P.ψ
  ψ := P.φ
  hφ := P.hψ
  hψ := P.hφ
  hψφ := P.hφψ
  hφψ := P.hψφ

/-- An explicit map-pair interleaving bounds the interval-component distance. -/
theorem interleavingDistance_le (P : HeightMapPair f g ε) :
    interleavingDistance (intervalComponents f) (intervalComponents g) ≤ ε :=
  P.interleaving.interleavingDistance_le

variable {X : Type u} [TopologicalSpace X] {f g : C(X, ℝ)}

/-- The identity maps and constant paths form a height-map pair from a pointwise perturbation
bound. -/
def ofUniformBound {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε) : HeightMapPair f g ε where
  φ := ContinuousMap.id X
  ψ := ContinuousMap.id X
  hφ x := (abs_sub_comm _ _).trans_le (hfg x)
  hψ x := hfg x
  hψφ x := by
    refine ⟨Path.refl x, fun t => ?_⟩
    change |f x - f x| ≤ ((ε + ε : ℝ≥0) : ℝ)
    rw [sub_self, abs_zero]
    exact NNReal.coe_nonneg _
  hφψ x := by
    refine ⟨Path.refl x, fun t => ?_⟩
    change |g x - g x| ≤ ((ε + ε : ℝ≥0) : ℝ)
    rw [sub_self, abs_zero]
    exact NNReal.coe_nonneg _

/-- For the identity-map pair, the induced interleaving is the pointwise perturbation
interleaving. -/
theorem interleaving_eq_perturbationInterleaving {ε : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) :
    (ofUniformBound hfg).interleaving = perturbationInterleaving hfg := by
  apply Interleaving.ext
  · ext I c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  · ext I c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

end HeightMapPair

end TDA.Reeb
