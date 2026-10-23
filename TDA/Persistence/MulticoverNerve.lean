import TDA.Persistence.SubdivisionRips
import TDA.Topology.MulticoverCover

/-!
# The concrete multicover nerve comparison on homology

The normalized Čech flag complex includes into the nerve of its large-face
cover. This inclusion induces a natural morphism of actual simplicial homology
bifiltrations. Finite sup-norm coordinates identify its source with normalized
subdivision-Rips homology. Invertibility is not asserted here.
-/

universe u v
noncomputable section
namespace TDA.Persistence.SubdivisionRips
open CategoryTheory TDA.Simplicial TDA.Filtration.SubdivisionRips
open TDA.Topology.MeasureBifiltration
attribute [local instance] vertexOrder
variable {V : Type v} [Fintype V]
variable (R : Type u) [Ring R]

/-- The concrete flag-to-cover-nerve inclusion induces a natural morphism of
actual simplicial homology bifiltrations; no component is assumed invertible. -/
noncomputable def cechHomologyToLargeFaceNerve {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (n : ℕ) :
    simplicialHomologyPModule R (cechBifiltration p) n ⟶
      simplicialHomologyPModule R (largeFaceNerveBifiltration p) n where
  app a := simplicialHomologyIncl R (subdivision_openCech_le_largeFaceNerve p a) n
  naturality := by
    intro a b f
    change simplicialHomologyIncl R _ n ≫ simplicialHomologyIncl R _ n =
      simplicialHomologyIncl R _ n ≫ simplicialHomologyIncl R _ n
    let h₁ := (cechBifiltration p).monotone (leOfHom f)
    let h₂ := subdivision_openCech_le_largeFaceNerve p b
    let h₃ := subdivision_openCech_le_largeFaceNerve p a
    let h₄ := (largeFaceNerveBifiltration p).monotone (leOfHom f)
    exact (simplicialHomologyIncl_comp R h₁ h₂ n).symm.trans
      (simplicialHomologyIncl_comp R h₃ h₄ n)

/-- For isometric finite sup-norm coordinates, the source of the natural
cover-nerve comparison is exactly the concrete normalized subdivision-Rips module. -/
noncomputable def ripsHomologyToLargeFaceNerve {ι : Type*} [Fintype ι]
    (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ) :
    homology R d n ⟶ simplicialHomologyPModule R (largeFaceNerveBifiltration p) n := by
  rw [← cechHomology_eq R d p hd n]
  exact cechHomologyToLargeFaceNerve R p n

end TDA.Persistence.SubdivisionRips

end
