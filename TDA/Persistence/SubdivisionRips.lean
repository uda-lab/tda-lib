import TDA.Filtration.SubdivisionRips
import TDA.Persistence.Simplicial
import TDA.Simplicial.VertexChainMap
import TDA.Topology.MeasureBifiltration
import Mathlib.SetTheory.Cardinal.Order

/-!
# Homology of normalized subdivision-Rips

Homology is taken using the library's ordered simplicial chain complex in
every degree and over every coefficient ring. A fixed chosen order on the
ambient finite-subset vertices orients chains; subset comparisons defining
flags do not use that order. The open Čech/Rips comparison in finite sup-norm
space is an equality of entire diagrams, and therefore respects every
structure map, rather than merely giving separate homology isomorphisms.
-/

open scoped NNReal ENNReal

universe u v w
namespace TDA.Persistence.SubdivisionRips

open TDA.Filtration.SubdivisionRips TDA.Simplicial CategoryTheory

/-- A fixed orientation order on finite-subset vertices. It is independent of
the metric and of both filtration parameters. -/
@[instance_reducible]
noncomputable def vertexOrder (V : Type u) : LinearOrder (Finset V) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

attribute [local instance] vertexOrder

variable {V : Type u} [Fintype V]
variable (R : Type v) [Ring R]

/-- The actual normalized subdivision-Rips homology persistence module. -/
noncomputable def homology (d : MetricSpace V) (n : ℕ) :
    PModule.{v,0,max u v} R Index :=
  simplicialHomologyPModule R (bifiltration d) n

/-- The module value is the homology of the concrete normalized flag complex. -/
theorem homology_obj (d : MetricSpace V) (n : ℕ) (p : Index) :
    (homology R d n).obj p = simplicialHomology (bifiltration d p) R n := rfl

/-- Structure maps are induced by the flag inclusions. -/
theorem homology_structureMap (d : MetricSpace V) (n : ℕ)
    {p q : Index} (hpq : p ≤ q) :
    structureMap (homology R d n) hpq =
      simplicialHomologyIncl R ((bifiltration d).monotone hpq) n := rfl

/-- The sup-norm open Čech flag filtration, on the same labelled vertices. -/
def cechBifiltration {ι : Type w} [Fintype ι] (p : V → ι → ℝ) :
    TDA.Filtration.SimplicialFiltration Index (Finset V) where
  toFun a := subdivision (openCech p (radius a)) (mass a)
  monotone' := by
    intro a b hab
    apply subdivision_mono ?_ hab.1
    exact TDA.Topology.nerve_mono (fun _ => Metric.ball_subset_ball hab.2)

/-- The Čech/Rips identification is equality of bifiltrations and hence natural
simultaneously in mass and radius. -/
theorem cechBifiltration_eq {ι : Type w} [Fintype ι] (d : MetricSpace V)
    (p : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    cechBifiltration p = bifiltration d := by
  apply OrderHom.ext
  funext a
  exact subdivision_openCech_eq d p hd a

/-- Applying actual simplicial homology preserves the whole natural equality,
including all structure maps in every degree. -/
theorem cechHomology_eq {ι : Type w} [Fintype ι] (d : MetricSpace V)
    (p : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ) :
    simplicialHomologyPModule R (cechBifiltration p) n = homology R d n := by
  rw [cechBifiltration_eq d p hd]
  rfl

/-- Every finite metric input has a concrete sup-norm Čech realization whose
normalized flag homology diagram is exactly its subdivision-Rips module. -/
theorem distanceCoordinates_cechHomology_eq (d : MetricSpace V) (n : ℕ) :
    simplicialHomologyPModule R (cechBifiltration (distanceCoordinates d)) n =
      homology R d n :=
  cechHomology_eq R d (distanceCoordinates d)
    (fun v w => (distanceCoordinates_dist d v w).symm) n

open TDA.Topology.MeasureBifiltration

/-- The concrete two-copy flag filtration for a perturbation of a finite
labelled metric. This is a distance-matrix estimate, separate from GP stability. -/
def metricInterleavingFiltration (d e : MetricSpace V) (δ : ℝ≥0)
    (hde : ∀ v w, |d.dist v w - e.dist v w| ≤ 2 * δ) :
    TDA.Filtration.SimplicialFiltration (InterleavingIndex δ) (Finset V) where
  toFun p := bifiltration (if p.side then e else d) p.point
  monotone' := by
    intro a b hab
    rcases a with ⟨p, a⟩
    rcases b with ⟨q, b⟩
    have hδ := δ.coe_nonneg
    cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
    · exact (bifiltration d).monotone (by simpa [interleavingIndex_le_iff, penalty] using hab)
    · apply bifiltration_le_of_dist_le d e δ ?_ ?_ hab.2
      · intro v w
        have := (abs_sub_le_iff.mp (hde v w)).2
        linarith
      · change mass q + penalty δ false true ≤ mass p ∧ _ at hab
        simp only [penalty, Bool.false_eq_true, ↓reduceIte] at hab
        linarith [hab.1]
    · apply bifiltration_le_of_dist_le e d δ ?_ ?_ hab.2
      · intro v w
        have := (abs_sub_le_iff.mp (hde v w)).1
        linarith
      · change mass q + penalty δ true false ≤ mass p ∧ _ at hab
        simp only [penalty, Bool.true_eq_false, ↓reduceIte] at hab
        linarith [hab.1]
    · exact (bifiltration e).monotone (by simpa [interleavingIndex_le_iff, penalty] using hab)

/-- Actual subdivision-Rips homology is interleaved over the restricted
positive index whenever the distance matrices differ by at most `2δ`.
Every mixed composition and naturality equation is inherited from the
simplicial homology functor on this concrete flag filtration. -/
noncomputable def metricInterleaving (d e : MetricSpace V) (δ : ℝ≥0)
    (hde : ∀ v w, |d.dist v w - e.dist v w| ≤ 2 * δ) (n : ℕ) :
    PModule R (InterleavingIndex δ) :=
  simplicialHomologyPModule R (metricInterleavingFiltration d e δ hde) n

/-- The first restriction is the actual module of `d`. -/
theorem metricInterleaving_left (d e : MetricSpace V) (δ : ℝ≥0)
    (hde : ∀ v w, |d.dist v w - e.dist v w| ≤ 2 * δ) (n : ℕ) :
    (copy δ false).toFunctor ⋙ metricInterleaving R d e δ hde n = homology R d n := rfl

/-- The second restriction is the actual module of `e`. -/
theorem metricInterleaving_right (d e : MetricSpace V) (δ : ℝ≥0)
    (hde : ∀ v w, |d.dist v w - e.dist v w| ≤ 2 * δ) (n : ℕ) :
    (copy δ true).toFunctor ⋙ metricInterleaving R d e δ hde n = homology R e n := rfl

/-- Half the maximum discrepancy of the two finite distance matrices. -/
noncomputable def perturbationParam (d e : MetricSpace V) : ℝ≥0 :=
  ⟨TDA.Filtration.Rips.pairwiseDiscrepancy d e / 2,
    div_nonneg (TDA.Filtration.Rips.pairwiseDiscrepancy_nonneg d e) (by norm_num)⟩

/-- The canonical restricted homology interleaving is obtained directly from
two finite metric inputs, without a separate simplex-level stability premise. -/
noncomputable def pairwiseInterleaving (d e : MetricSpace V) (n : ℕ) :
    PModule R (InterleavingIndex (perturbationParam d e)) :=
  metricInterleaving R d e (perturbationParam d e) (fun v w => by
    change |d.dist v w - e.dist v w| ≤
      2 * (TDA.Filtration.Rips.pairwiseDiscrepancy d e / 2)
    nlinarith [TDA.Filtration.Rips.abs_dist_sub_le_pairwiseDiscrepancy d e v w]) n

/-- The canonical perturbation consumer recovers the first input homology. -/
theorem pairwiseInterleaving_left (d e : MetricSpace V) (n : ℕ) :
    (copy (perturbationParam d e) false).toFunctor ⋙ pairwiseInterleaving R d e n =
      homology R d n := rfl

/-- The canonical perturbation consumer recovers the second input homology. -/
theorem pairwiseInterleaving_right (d e : MetricSpace V) (n : ℕ) :
    (copy (perturbationParam d e) true).toFunctor ⋙ pairwiseInterleaving R d e n =
      homology R e n := rfl

section Relabel

variable {W : Type u} [Fintype W]

/-- The vertexwise relabelling acts on every normalized flag complex. -/
noncomputable def relabelMap (e : V ≃ W) (d : MetricSpace V) (f : MetricSpace W)
    (h : ∀ v w, f.dist (e v) (e w) = d.dist v w) (p : Index) :
    VertexMap (bifiltration d p) (bifiltration f p) where
  toFun := relabelVertex e
  map_face S hS := by
    classical
    rw [← @Finset.map_eq_image (Finset V) (Finset W) (Classical.decEq _)
      (relabelVertex e) S]
    exact (mem_bifiltration_relabel_iff e d f h p S).2 hS

/-- Isometric relabelling gives a natural transformation of the actual
homology diagrams. -/
noncomputable def relabelHom (e : V ≃ W) (d : MetricSpace V) (f : MetricSpace W)
    (h : ∀ v w, f.dist (e v) (e w) = d.dist v w) (n : ℕ) :
    homology R d n ⟶ homology R f n where
  app p := simplicialHomologyMap R (relabelMap e d f h p) n
  naturality {p q} a := by
    change simplicialHomologyIncl R _ n ≫ simplicialHomologyMap R _ n =
      simplicialHomologyMap R _ n ≫ simplicialHomologyIncl R _ n
    rw [← simplicialHomologyMap_inclusion, ← simplicialHomologyMap_inclusion,
      ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp]
    exact congrArg (fun g => simplicialHomologyMap R g n) (VertexMap.ext (fun _ => rfl))

omit [Fintype V] [Fintype W] in
/-- The two relabelling functions compose to the identity on finite subsets. -/
theorem relabelVertex_symm_apply (e : V ≃ W) (s : Finset V) :
    relabelVertex e.symm (relabelVertex e s) = s := by
  simp [relabelVertex, Finset.map_map]

/-- Isometric relabelling preserves the entire normalized subdivision-Rips
homology module up to natural isomorphism. The relabelling need not preserve
the fixed orientation orders on the two ambient vertex types. -/
noncomputable def relabelIso (e : V ≃ W) (d : MetricSpace V) (f : MetricSpace W)
    (h : ∀ v w, f.dist (e v) (e w) = d.dist v w) (n : ℕ) :
    homology R d n ≅ homology R f n where
  hom := relabelHom R e d f h n
  inv := relabelHom R e.symm f d
    (fun v w => by simpa using (h (e.symm v) (e.symm w)).symm) n
  hom_inv_id := by
    apply NatTrans.ext
    funext p
    change simplicialHomologyMap R _ n ≫ simplicialHomologyMap R _ n =
      𝟙 (simplicialHomology (bifiltration d p) R n)
    rw [← simplicialHomologyMap_comp]
    have hm : (relabelMap e d f h p).comp (relabelMap e.symm f d
        (fun v w => by simpa using (h (e.symm v) (e.symm w)).symm) p) =
        VertexMap.id (bifiltration d p) := by
      apply VertexMap.ext
      exact relabelVertex_symm_apply e
    rw [hm, simplicialHomologyMap_id]
  inv_hom_id := by
    apply NatTrans.ext
    funext p
    change simplicialHomologyMap R _ n ≫ simplicialHomologyMap R _ n =
      𝟙 (simplicialHomology (bifiltration f p) R n)
    rw [← simplicialHomologyMap_comp]
    have hm : (relabelMap e.symm f d
        (fun v w => by simpa using (h (e.symm v) (e.symm w)).symm) p).comp
        (relabelMap e d f h p) = VertexMap.id (bifiltration f p) := by
      apply VertexMap.ext
      exact relabelVertex_symm_apply e.symm
    rw [hm, simplicialHomologyMap_id]

end Relabel

end TDA.Persistence.SubdivisionRips
