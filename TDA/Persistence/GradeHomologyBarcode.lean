import TDA.Simplicial.FiniteDimensionalHomology
import TDA.Filtration.CriticalValues
import TDA.Persistence.Simplicial
import TDA.Persistence.RankBarcode

universe u w
namespace TDA.Persistence
open TDA.Simplicial
variable {V : Type u} [LinearOrder V] (k : Type u) [Field k]
variable {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TDA.Simplicial.TotalFace K)]

noncomputable instance gradeHomology_finiteDimensional
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ)
    (i : Fin f.criticalValues.card) :
    FiniteDimensional k ((simplicialHomologyPModule k f.gradeFiltration n).obj i) := by
  have h : f.gradeFiltration i ≤ K := by
    rw [f.gradeFiltration_apply]
    exact f.sublevel_le _
  letI : Finite (Face K n) := faceFiniteOfTotalFinite K n
  letI : Finite (Face (f.gradeFiltration i) n) :=
    Finite.of_injective (faceIncl h n) (by
      intro a b hab
      have hv : a.1 = b.1 := congrArg (fun t : Face K n => t.1) hab
      exact Subtype.ext hv)
  change FiniteDimensional k (simplicialHomology (f.gradeFiltration i) k n)
  infer_instance

noncomputable def gradeHomologyBarcode
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ) :
    Multiset (FiniteInterval f.criticalValues.card) :=
  rankBarcode (simplicialHomologyPModule k f.gradeFiltration n)

theorem rank_gradeHomologyMap
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ)
    (i j : Fin f.criticalValues.card) (hij : i ≤ j) :
    Module.finrank k (LinearMap.range
      (TDA.Simplicial.simplicialHomologyIncl k
        (f.gradeFiltration.monotone hij) n).hom) =
      (gradeHomologyBarcode k f n).countP
        (fun I => I.birth ≤ i.val ∧ j.val < I.death) := by
  change structureMapRank (simplicialHomologyPModule k f.gradeFiltration n) i j hij = _
  exact (structureMapRank_rankBarcode
    (simplicialHomologyPModule k f.gradeFiltration n) i j hij).symm.trans
      (rank_barcodeMap (gradeHomologyBarcode k f n) i j hij)

end TDA.Persistence
