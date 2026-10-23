import TDA.Persistence.QTame
import TDA.Persistence.RipsRelationInterleaving
import TDA.Simplicial.FiniteDimensionalHomology
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Q-tameness of Rips homology on totally bounded spaces

For every strict gap `a < b`, a finite `(b-a)/4`-net yields a
`(b-a)/2`-interleaving with its Rips homology. The interleaving law factors
the structure map from `a` to `b` through a finite-dimensional middle fiber.
This proves q-tameness in every degree, including for empty spaces and negative
source times, with closed diameter sublevels and the library's empty negative tail.

The argument is the Rips part of Chazal--de Silva--Oudot,
*Persistence stability for geometric complexes*, arXiv:1207.3885v3,
Proposition 5.1, using their Lemma 4.3 through `relationInterleaving`.
-/

universe u v

namespace TDA.Persistence.Rips

open CategoryTheory TDA.Filtration TDA.Simplicial Set Metric
open scoped NNReal

noncomputable section

variable {X : Type u} [LinearOrder X] [MetricSpace X]

/-- Isometric relabelling gives naturally isomorphic Rips homology modules,
even for infinite types and for unrelated auxiliary vertex orders. -/
def sublevelModuleIsoOfIsometryEquiv {Y : Type u} [LinearOrder Y] [MetricSpace Y]
    (R : Type v) [Ring R] (e : X ≃ᵢ Y) (n : ℕ) :
    sublevelModule R (Rips.filter (inferInstance : MetricSpace X)) n ≅
      sublevelModule R (Rips.filter (inferInstance : MetricSpace Y)) n :=
  (relationInterleaving R (inferInstance : MetricSpace X) (inferInstance : MetricSpace Y)
    (C := Function.graph e) (ε := 0)
    (fun x => ⟨e x, rfl⟩)
    (fun y => ⟨e.symm y, e.apply_symm_apply y⟩)
    (by
      rintro x x' y y' rfl rfl
      simp only [e.dist_eq, sub_self, abs_zero, NNReal.coe_zero, le_refl]) n).toIso

omit [LinearOrder X] in
/-- The near-point relation of a finite net is total in both directions and has
distortion at most twice the net radius. Empty nets cover the empty space. -/
theorem exists_finite_net_relation (hX : TotallyBounded (univ : Set X))
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ F : Set X, F.Finite ∧ ∃ C : SetRel X F,
      Relator.LeftTotal (fun x y => (x, y) ∈ C) ∧
      Relator.LeftTotal (fun y x => (y, x) ∈ C.inv) ∧
      ∀ x x' y y', (x, y) ∈ C → (x', y') ∈ C →
        |dist x x' - dist y y'| ≤ (ε : ℝ) := by
  obtain ⟨F, hF, hcover⟩ := Metric.totallyBounded_iff.mp hX
    ((ε : ℝ) / 2) (by exact half_pos hε)
  let C : SetRel X F := {p | dist p.1 p.2.val < (ε : ℝ) / 2}
  refine ⟨F, hF, C, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover (mem_univ x))
    exact ⟨⟨y, hy⟩, hxy⟩
  · intro y
    exact ⟨y.val, by change dist y.val y.val < (ε : ℝ) / 2; simpa using half_pos hε⟩
  · intro x x' y y' hxy hx'y'
    have hdist := dist_dist_dist_le x x' y.val y'.val
    rw [Real.dist_eq] at hdist
    change dist x y.val < (ε : ℝ) / 2 at hxy
    change dist x' y'.val < (ε : ℝ) / 2 at hx'y'
    exact hdist.trans (by linarith)

/-- Closed diameter Rips homology of a totally bounded metric space is q-tame,
in every degree and over every field. No inhabitedness or finite-fiber premise is needed. -/
theorem qTame_of_totallyBounded (k : Type v) [Field k]
    (hX : TotallyBounded (univ : Set X)) (n : ℕ) :
    (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n).QTame := by
  intro a b hab
  let ε : ℝ≥0 := ⟨(b - a) / 2, by linarith⟩
  have hε : 0 < ε := by change 0 < (b - a) / 2; linarith
  obtain ⟨F, hF, C, hCT, hIT, hC⟩ := exists_finite_net_relation hX ε hε
  let : Fintype F := hF.fintype
  let i := relationInterleaving k (inferInstance : MetricSpace X)
    (inferInstance : MetricSpace F) hCT hIT hC n
  have hmid : FiniteDimensional k
      ((sublevelModule k (Rips.filter (inferInstance : MetricSpace F)) n).obj
        (a + (ε : ℝ))) := by
    change FiniteDimensional k (simplicialHomology _ k n)
    infer_instance
  have h := i.finiteDimensional_range_structureMap a
  have hb : (a + (ε : ℝ)) + (ε : ℝ) = b := by
    change (a + (b - a) / 2) + (b - a) / 2 = b
    ring
  have h' : ∀ ha : a ≤ (a + (ε : ℝ)) + (ε : ℝ),
      FiniteDimensional k (LinearMap.range (structureMapLinear
        (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n) ha)) :=
    fun _ => h
  rw [hb] at h'
  exact h' hab.le

/-- For an infinite metric space, unreduced Rips `H₀` at the closed threshold zero
is infinite-dimensional: distinct vertices have no edges at this threshold. -/
theorem not_finiteDimensional_zero_homology [Infinite X] (k : Type v) [Field k] :
    ¬ FiniteDimensional k
      ((sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) 0).obj 0) := by
  classical
  let K := (Rips.filter (inferInstance : MetricSpace X)).sublevel 0
  let vertex : X → Face K 0 := fun x => ⟨{x},
    (Rips.mem_sublevel_iff _ _ _).2 ⟨by simp, by simp⟩, by simp⟩
  have hinj : Function.Injective vertex := by
    intro x y h
    exact Finset.singleton_injective (congrArg Subtype.val h)
  let : Infinite (Face K 0) := Infinite.of_injective vertex hinj
  let : IsEmpty (Face K 1) := ⟨by
    intro σ
    have hcard : 1 < σ.val.card := by have := σ.property.2; omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
    have hd := ((Rips.mem_sublevel_iff _ _ _).mp σ.property.1).2 x hx y hy
    exact hxy (dist_le_zero.mp hd)⟩
  let S := (simplicialChainComplex K k).sc 0
  have hf : S.f = 0 := by
    change (simplicialChainComplex K k).d ((ComplexShape.down ℕ).prev 0) 0 = 0
    rw [ChainComplex.prev]
    apply ModuleCat.hom_ext
    ext c
    change Chain K k 1 at c
    change boundary K k 0 c = 0
    have hc : c = 0 := Subsingleton.elim _ _
    rw [hc, map_zero]
  have hg : S.g = 0 := by
    change (simplicialChainComplex K k).d 0 ((ComplexShape.down ℕ).next 0) = 0
    rw [ChainComplex.next_nat_zero]
    exact simplicialChainComplex_d_zero K k 0
  intro hdim
  let : FiniteDimensional k S.homology := hdim
  let : FiniteDimensional k (Chain K k 0) :=
    (ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyIso.toLinearEquiv.finiteDimensional
  have hfinite : Finite (Face K 0) := Module.Finite.finite_basis
    (Finsupp.basisSingleOne : Module.Basis (Face K 0) k (Chain K k 0))
  exact @_root_.not_finite (Face K 0) inferInstance hfinite

end
end TDA.Persistence.Rips
