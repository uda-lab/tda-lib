import TDA.Persistence.Simplicial
import TDA.Persistence.RealInterleavingDistance
import TDA.Persistence.FiniteFilterStability

set_option autoImplicit false

/-!
# Inclusion-induced interleavings of simplicial persistence modules

A pointwise inclusion of simplicial filtrations induces a natural transformation of their
homology persistence modules, whose components are the homology inclusions. Two real
filtrations, each contained in the other after a shift by `ε`, give a real
`ε`-interleaving: every map in both double-shift equations is a homology inclusion, so both
equations reduce to the functoriality of homology inclusions. For two real filters on the
same complex whose face values differ by at most `ε`, this is an `ε`-interleaving of their
sublevel modules.

These are library extensions proved from the merged definitions. No statement about
diagrams or the bottleneck distance is made here.
-/

universe u v w x

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration
open scoped NNReal ENNReal

variable {V : Type u} [LinearOrder V]
variable (R : Type v) [Ring R] (n : ℕ)

/-! ### Inclusion morphisms -/

section Inclusion

variable {P : Type w} [Preorder P] {F G H : SimplicialFiltration P V}

/-- A pointwise inclusion of filtrations induces the morphism of homology persistence modules
whose components are the homology inclusions. -/
noncomputable def inclusionHom (h : ∀ p, F p ≤ G p) :
    simplicialHomologyPModule R F n ⟶ simplicialHomologyPModule R G n where
  app p := simplicialHomologyIncl R (h p) n
  naturality p q f := by
    change simplicialHomologyIncl R (F.monotone (leOfHom f)) n ≫
        simplicialHomologyIncl R (h q) n =
      simplicialHomologyIncl R (h p) n ≫ simplicialHomologyIncl R (G.monotone (leOfHom f)) n
    rw [← simplicialHomologyIncl_comp, ← simplicialHomologyIncl_comp]

/-- The component of the inclusion morphism is the homology inclusion. -/
@[simp] theorem inclusionHom_app (h : ∀ p, F p ≤ G p) (p : P) :
    (inclusionHom R n h).app p = simplicialHomologyIncl R (h p) n := rfl

/-- The inclusion morphism of the reflexive inclusion is the identity. -/
theorem inclusionHom_refl (F : SimplicialFiltration P V) :
    inclusionHom R n (fun p => le_refl (F p)) = 𝟙 _ := by
  apply NatTrans.ext
  funext p
  exact simplicialHomologyIncl_id R (F p) n

/-- Inclusion morphisms compose to the inclusion morphism of the composite inclusion. -/
theorem inclusionHom_comp (hFG : ∀ p, F p ≤ G p) (hGH : ∀ p, G p ≤ H p) :
    inclusionHom R n hFG ≫ inclusionHom R n hGH =
      inclusionHom R n (fun p => (hFG p).trans (hGH p)) := by
  apply NatTrans.ext
  funext p
  exact (simplicialHomologyIncl_comp R (hFG p) (hGH p) n).symm

/-- The homology module of a reindexed filtration is the reindexed homology module. -/
theorem simplicialHomologyPModule_reindex {Q : Type x} [Preorder Q] (u : Q →o P)
    (F : SimplicialFiltration P V) :
    simplicialHomologyPModule R (Filtration.reindex u F) n =
      reindex u (simplicialHomologyPModule R F n) := rfl

/-- Reindexing an inclusion morphism gives the inclusion morphism of the reindexed
filtrations. -/
theorem reindexNatTrans_inclusionHom {Q : Type x} [Preorder Q] (u : Q →o P)
    (h : ∀ p, F p ≤ G p) :
    reindexNatTrans u (inclusionHom R n h) =
      inclusionHom R n (F := Filtration.reindex u F) (G := Filtration.reindex u G)
        (fun q => h (u q)) := rfl

end Inclusion

/-! ### The inclusion interleaving -/

section Interleaving

open RealShift

/-- Three composable homology inclusions compose to the homology inclusion of the outer
inclusion. -/
private theorem incl_comp_comp {K L M N : PreAbstractSimplicialComplex V}
    (h₁ : K ≤ L) (h₂ : L ≤ M) (h₃ : M ≤ N) (h : K ≤ N) :
    simplicialHomologyIncl R h₁ n ≫ simplicialHomologyIncl R h₂ n ≫
      simplicialHomologyIncl R h₃ n = simplicialHomologyIncl R h n := by
  rw [← simplicialHomologyIncl_comp, ← simplicialHomologyIncl_comp]

variable {F G : SimplicialFiltration ℝ V} {ε : ℝ≥0}

/-- Two real filtrations, each contained in the other after a shift by `ε`, give a real `ε`-interleaving of their homology modules, with homology inclusions as maps. -/
noncomputable def inclusionInterleaving (hFG : ∀ t, F t ≤ G (t + ε))
    (hGF : ∀ t, G t ≤ F (t + ε)) :
    RealInterleaving ε (simplicialHomologyPModule R F n) (simplicialHomologyPModule R G n) :=
  RealInterleaving.ofApp
    (inclusionHom R n (F := F) (G := Filtration.reindex (translation ε) G) hFG)
    (inclusionHom R n (F := G) (G := Filtration.reindex (translation ε) F) hGF)
    (fun t => by
      rw [compIso_hom_app, transition_app]
      exact incl_comp_comp R n _ _ _ _)
    (fun t => by
      rw [compIso_hom_app, transition_app]
      exact incl_comp_comp R n _ _ _ _)

/-- The first map of the inclusion interleaving is the homology inclusion into the shifted
second filtration. -/
@[simp] theorem inclusionInterleaving_φ_app (hFG : ∀ t, F t ≤ G (t + ε))
    (hGF : ∀ t, G t ≤ F (t + ε)) (t : ℝ) :
    (inclusionInterleaving R n hFG hGF).φ.app t = simplicialHomologyIncl R (hFG t) n := rfl

/-- The second map of the inclusion interleaving is the homology inclusion into the shifted
first filtration. -/
@[simp] theorem inclusionInterleaving_ψ_app (hFG : ∀ t, F t ≤ G (t + ε))
    (hGF : ∀ t, G t ≤ F (t + ε)) (t : ℝ) :
    (inclusionInterleaving R n hFG hGF).ψ.app t = simplicialHomologyIncl R (hGF t) n := rfl

end Interleaving

/-! ### Sublevel modules and the additive interleaving -/

section Sublevel

variable {K : PreAbstractSimplicialComplex V}

/-- The homology persistence module of the sublevel filtration of a filter. -/
noncomputable abbrev sublevelModule {α : Type w} [LinearOrder α] (f : FilterFunction K α)
    (n : ℕ) : PModule R α :=
  simplicialHomologyPModule R f.sublevelFiltration n

omit [LinearOrder V] in
/-- A pointwise value bound `g ≤ f` gives the sublevel inclusion at every threshold. -/
theorem sublevel_le_sublevel_of_le {α : Type w} [LinearOrder α]
    {f g : FilterFunction K α} (h : ∀ s, g.value s ≤ f.value s) (r : α) :
    f.sublevel r ≤ g.sublevel r := by
  intro s hs
  obtain ⟨hsK, hsr⟩ := (FilterFunction.mem_sublevel_iff f r s).1 hs
  exact (FilterFunction.mem_sublevel_iff g r s).2 ⟨hsK, (h _).trans hsr⟩

omit [LinearOrder V] in
/-- A value bound `g ≤ f + ε` gives the inclusion of the `r`-sublevel of `f` in the
`(r + ε)`-sublevel of `g`, for every real `ε`. -/
theorem sublevel_le_sublevel_add {f g : FilterFunction K ℝ} {ε : ℝ}
    (h : ∀ s, g.value s ≤ f.value s + ε) (r : ℝ) :
    f.sublevel r ≤ g.sublevel (r + ε) := by
  intro s hs
  obtain ⟨hsK, hsr⟩ := (FilterFunction.mem_sublevel_iff f r s).1 hs
  exact (FilterFunction.mem_sublevel_iff g _ s).2 ⟨hsK, (h _).trans (add_le_add hsr le_rfl)⟩

variable {f g : FilterFunction K ℝ} {ε : ℝ≥0}

/-- Two real filters whose face values differ by at most `ε` have `ε`-interleaved sublevel
modules, with homology inclusions as maps. -/
noncomputable def sublevelInterleaving (h : ∀ s, |f.value s - g.value s| ≤ ε) :
    RealInterleaving ε (sublevelModule R f n) (sublevelModule R g n) :=
  inclusionInterleaving R n
    (F := f.sublevelFiltration) (G := g.sublevelFiltration)
    (sublevel_le_sublevel_add (fun s => by
      have := (abs_sub_le_iff.1 (h s)).2
      linarith))
    (sublevel_le_sublevel_add (fun s => by
      have := (abs_sub_le_iff.1 (h s)).1
      linarith))

/-- The first map of the sublevel interleaving is the homology inclusion. -/
@[simp] theorem sublevelInterleaving_φ_app (h : ∀ s, |f.value s - g.value s| ≤ ε) (t : ℝ) :
    (sublevelInterleaving R n h).φ.app t =
      simplicialHomologyIncl R (K := f.sublevel t) (L := g.sublevel (t + ε))
        (sublevel_le_sublevel_add (fun s => by
          have := (abs_sub_le_iff.1 (h s)).2
          linarith) t) n := rfl

/-- The second map of the sublevel interleaving is the homology inclusion. -/
@[simp] theorem sublevelInterleaving_ψ_app (h : ∀ s, |f.value s - g.value s| ≤ ε) (t : ℝ) :
    (sublevelInterleaving R n h).ψ.app t =
      simplicialHomologyIncl R (K := g.sublevel t) (L := f.sublevel (t + ε))
        (sublevel_le_sublevel_add (fun s => by
          have := (abs_sub_le_iff.1 (h s)).1
          linarith) t) n := rfl

/-- Face values within `ε` bound the interleaving distance of the sublevel modules by `ε`. -/
theorem realInterleavingDistance_sublevel_le (h : ∀ s, |f.value s - g.value s| ≤ ε) :
    realInterleavingDistance (sublevelModule R f n) (sublevelModule R g n) ≤ ε :=
  (sublevelInterleaving R n h).distance_le

/-- On a finite complex, the interleaving distance of the sublevel modules is at most the
maximal face-value difference. -/
theorem realInterleavingDistance_sublevel_le_faceSupDifference [Fintype (TotalFace K)]
    (f g : FilterFunction K ℝ) :
    realInterleavingDistance (sublevelModule R f n) (sublevelModule R g n) ≤
      ENNReal.ofReal (faceSupDifference f g) :=
  realInterleavingDistance_sublevel_le R n (ε := Real.toNNReal (faceSupDifference f g))
    (fun s => (abs_face_difference_le f g s).trans (Real.le_coe_toNNReal _))

end Sublevel

end TDA.Persistence
