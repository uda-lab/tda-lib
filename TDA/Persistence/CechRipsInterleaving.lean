import TDA.Persistence.SublevelInterleaving
import TDA.Filtration.Cech
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

/-!
# The log-scale Čech–Rips interleaving

Reindexing a sublevel filtration along `exp` turns a multiplicative value sandwich
`g ≤ f ≤ c · g` with `1 ≤ c` into inclusions shifted by `log c`, hence into an actual real
`log c`-interleaving of the log-scale homology modules. The merged value bounds
`čech ≤ rips ≤ 2 · čech` give the log-scale Čech–Rips interleaving with parameter `log 2`,
in every degree, over every ring and in every pseudometric ambient space.

At radius level, the inclusions `Rips_r ⊆ Čech_r ⊆ Rips_{2r}` are morphisms of sublevel
modules, the second into the module reindexed along `r ↦ 2r`. Their composites are the
inclusion morphisms `Rips_r ⊆ Rips_{2r}` and `Čech_r ⊆ Čech_{2r}`, for every real `r`.
For `0 ≤ r` these components are the actual structure maps; for `r < 0` both sublevels are
empty.

The Čech side is the radius-filter sublevel; no properness of the ambient space is used.
These are library extensions; no diagram or bottleneck statement is made.
-/

universe u v u'

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration
open scoped NNReal ENNReal

variable {V : Type u} [LinearOrder V]
variable (R : Type v) [Ring R] (n : ℕ)

/-! ### Log scale and the multiplicative sandwich -/

/-- The exponential as a monotone reindexing of real parameters. -/
noncomputable def expHom : ℝ →o ℝ := ⟨Real.exp, Real.exp_monotone⟩

@[simp] theorem expHom_apply (t : ℝ) : expHom t = Real.exp t := rfl

section LogScale

variable {K : PreAbstractSimplicialComplex V}

/-- The log-scale module of a real filter: the homology of the sublevel at `exp t`. -/
noncomputable abbrev logModule (f : FilterFunction K ℝ) (n : ℕ) : PModule R ℝ :=
  simplicialHomologyPModule R (Filtration.reindex expHom f.sublevelFiltration) n

/-- The log-scale module at `t` is the homology of the sublevel at `exp t`. -/
theorem logModule_obj (f : FilterFunction K ℝ) (t : ℝ) :
    (logModule R f n).obj t = simplicialHomology (f.sublevel (Real.exp t)) R n := rfl

/-- The log-scale module is the sublevel module reindexed along `exp`. -/
theorem logModule_eq_reindex (f : FilterFunction K ℝ) :
    logModule R f n = reindex expHom (sublevelModule R f n) :=
  simplicialHomologyPModule_reindex R n expHom f.sublevelFiltration

end LogScale

/-- The interleaving parameter of a multiplicative factor `c`, namely `log c` for `1 ≤ c`. -/
noncomputable def logParam (c : ℝ) : ℝ≥0 := Real.toNNReal (Real.log c)

theorem coe_logParam {c : ℝ} (hc : 1 ≤ c) : (logParam c : ℝ) = Real.log c :=
  Real.coe_toNNReal _ (Real.log_nonneg hc)

/-- Shifting a log time by `logParam c` multiplies the radius by `c`. -/
theorem exp_add_logParam {c : ℝ} (hc : 1 ≤ c) (t : ℝ) :
    Real.exp (t + logParam c) = c * Real.exp t := by
  rw [coe_logParam hc, Real.exp_add, Real.exp_log (by linarith), mul_comm]

section LogScale

variable {K : PreAbstractSimplicialComplex V} {f g : FilterFunction K ℝ} {c : ℝ}

omit [LinearOrder V] in
/-- `g ≤ f` gives `f_{exp t} ⊆ g_{exp (t + log c)}`. -/
theorem log_sublevel_le_of_le (hgf : ∀ s, g.value s ≤ f.value s) (t : ℝ) :
    f.sublevel (Real.exp t) ≤ g.sublevel (Real.exp (t + logParam c)) :=
  (sublevel_le_sublevel_of_le hgf _).trans
    (g.sublevel_mono (Real.exp_le_exp.2 (le_add_of_nonneg_right (NNReal.coe_nonneg _))))

omit [LinearOrder V] in
/-- `f ≤ c · g` with `1 ≤ c` gives `g_{exp t} ⊆ f_{exp (t + log c)}`. -/
theorem log_sublevel_le_of_le_mul (hc : 1 ≤ c) (hfc : ∀ s, f.value s ≤ c * g.value s)
    (t : ℝ) : g.sublevel (Real.exp t) ≤ f.sublevel (Real.exp (t + logParam c)) := by
  intro s hs
  obtain ⟨hsK, hsr⟩ := (FilterFunction.mem_sublevel_iff g _ s).1 hs
  refine (FilterFunction.mem_sublevel_iff f _ s).2 ⟨hsK, ?_⟩
  rw [exp_add_logParam hc]
  exact (hfc _).trans (mul_le_mul_of_nonneg_left hsr (by linarith))

/-- A multiplicative sandwich `g ≤ f ≤ c · g` with `1 ≤ c` gives an actual real
`log c`-interleaving of the log-scale modules, with homology inclusions as maps. -/
noncomputable def logInterleaving (hc : 1 ≤ c) (hgf : ∀ s, g.value s ≤ f.value s)
    (hfc : ∀ s, f.value s ≤ c * g.value s) :
    RealInterleaving (logParam c) (logModule R f n) (logModule R g n) :=
  inclusionInterleaving R n
    (F := Filtration.reindex expHom f.sublevelFiltration)
    (G := Filtration.reindex expHom g.sublevelFiltration)
    (log_sublevel_le_of_le hgf) (log_sublevel_le_of_le_mul hc hfc)

/-- The first map of the log-scale interleaving is the homology inclusion. -/
@[simp] theorem logInterleaving_φ_app (hc : 1 ≤ c) (hgf : ∀ s, g.value s ≤ f.value s)
    (hfc : ∀ s, f.value s ≤ c * g.value s) (t : ℝ) :
    (logInterleaving R n hc hgf hfc).φ.app t =
      simplicialHomologyIncl R (log_sublevel_le_of_le hgf t) n := rfl

/-- The second map of the log-scale interleaving is the homology inclusion. -/
@[simp] theorem logInterleaving_ψ_app (hc : 1 ≤ c) (hgf : ∀ s, g.value s ≤ f.value s)
    (hfc : ∀ s, f.value s ≤ c * g.value s) (t : ℝ) :
    (logInterleaving R n hc hgf hfc).ψ.app t =
      simplicialHomologyIncl R (log_sublevel_le_of_le_mul hc hfc t) n := rfl

/-- A multiplicative sandwich bounds the log-scale interleaving distance by `log c`. -/
theorem realInterleavingDistance_log_le (hc : 1 ≤ c) (hgf : ∀ s, g.value s ≤ f.value s)
    (hfc : ∀ s, f.value s ≤ c * g.value s) :
    realInterleavingDistance (logModule R f n) (logModule R g n) ≤
      ENNReal.ofReal (Real.log c) :=
  (logInterleaving R n hc hgf hfc).distance_le

end LogScale

/-! ### Čech and Rips -/

/-- Doubling of real parameters as a monotone reindexing. -/
def twoMul : ℝ →o ℝ := ⟨fun r => 2 * r, fun _ _ h => by simp only; linarith⟩

@[simp] theorem twoMul_apply (r : ℝ) : twoMul r = 2 * r := rfl

namespace Cech

variable {X : Type u'} [PseudoMetricSpace X]

/-- The log-scale Rips and Čech modules are `log 2`-interleaved by homology inclusions. -/
noncomputable def ripsCechLogInterleaving (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    RealInterleaving (logParam 2) (logModule R (Rips.filter d) n)
      (logModule R (Cech.filter p) n) :=
  logInterleaving R n one_le_two (Cech.filter_value_le_rips d p hd)
    (Cech.rips_le_two_mul_filter_value d p hd)

/-- The log-scale Rips and Čech modules are at interleaving distance at most `log 2`. -/
theorem realInterleavingDistance_rips_cech_log_le (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    realInterleavingDistance (logModule R (Rips.filter d) n)
        (logModule R (Cech.filter p) n) ≤ ENNReal.ofReal (Real.log 2) :=
  (ripsCechLogInterleaving R n d p hd).distance_le

omit [LinearOrder V] in
/-- A filter with nonnegative values has `sublevel r ⊆ sublevel (2r)` for every real `r`. -/
private theorem sublevel_le_sublevel_two_mul {K : PreAbstractSimplicialComplex V}
    (f : FilterFunction K ℝ) (hf : ∀ s, 0 ≤ f.value s) (r : ℝ) :
    f.sublevel r ≤ f.sublevel (2 * r) := by
  intro s hs
  obtain ⟨hsK, hsr⟩ := (FilterFunction.mem_sublevel_iff f r s).1 hs
  refine (FilterFunction.mem_sublevel_iff f _ s).2 ⟨hsK, ?_⟩
  have := hf ⟨s, hsK⟩
  linarith

omit [LinearOrder V] in
/-- `Čech_r ⊆ Rips_{2r}` for every real `r`, from `rips ≤ 2 · čech`. -/
theorem cech_sublevel_le_rips_two_mul (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (r : ℝ) :
    (Cech.filter p).sublevel r ≤ (Rips.filter d).sublevel (2 * r) := by
  intro s hs
  obtain ⟨hsK, hsr⟩ := (FilterFunction.mem_sublevel_iff _ r s).1 hs
  refine (FilterFunction.mem_sublevel_iff _ _ s).2 ⟨hsK, ?_⟩
  have := Cech.rips_le_two_mul_filter_value d p hd ⟨s, hsK⟩
  linarith

/-- The inclusion morphism `Rips_r ⊆ Čech_r` of sublevel modules. -/
noncomputable def ripsToCech (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    sublevelModule R (Rips.filter d) n ⟶ sublevelModule R (Cech.filter p) n :=
  inclusionHom R n (sublevel_le_sublevel_of_le (Cech.filter_value_le_rips d p hd))

/-- The inclusion morphism `Čech_r ⊆ Rips_{2r}`, into the Rips module reindexed by doubling;
the inclusion holds for every real `r`. -/
noncomputable def cechToRips (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    sublevelModule R (Cech.filter p) n ⟶ reindex twoMul (sublevelModule R (Rips.filter d) n) :=
  inclusionHom R n (F := (Cech.filter p).sublevelFiltration)
    (G := Filtration.reindex twoMul (Rips.filter d).sublevelFiltration)
    (cech_sublevel_le_rips_two_mul d p hd)

/-- The inclusion morphism `Rips_r ⊆ Rips_{2r}`, defined for every real `r`. -/
noncomputable def ripsDouble (d : MetricSpace V) :
    sublevelModule R (Rips.filter d) n ⟶ reindex twoMul (sublevelModule R (Rips.filter d) n) :=
  inclusionHom R n (F := (Rips.filter d).sublevelFiltration)
    (G := Filtration.reindex twoMul (Rips.filter d).sublevelFiltration)
    (sublevel_le_sublevel_two_mul _ fun s => Rips.diameter_nonneg d s.val)

/-- The inclusion morphism `Čech_r ⊆ Čech_{2r}`, defined for every real `r`. -/
noncomputable def cechDouble (p : V → X) :
    sublevelModule R (Cech.filter p) n ⟶ reindex twoMul (sublevelModule R (Cech.filter p) n) :=
  inclusionHom R n (F := (Cech.filter p).sublevelFiltration)
    (G := Filtration.reindex twoMul (Cech.filter p).sublevelFiltration)
    (sublevel_le_sublevel_two_mul _ (Cech.filter_value_nonneg p))

@[simp] theorem ripsToCech_app (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (r : ℝ) :
    (ripsToCech R n d p hd).app r = simplicialHomologyIncl R
      (sublevel_le_sublevel_of_le (Cech.filter_value_le_rips d p hd) r) n := rfl

/-- Through Čech, the Rips inclusion `Rips_r ⊆ Rips_{2r}` factors, for every real `r`. -/
theorem ripsToCech_comp_cechToRips (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    ripsToCech R n d p hd ≫ cechToRips R n d p hd = ripsDouble R n d :=
  inclusionHom_comp R n _ _

/-- Through Rips, the Čech inclusion `Čech_r ⊆ Čech_{2r}` factors, for every real `r`. -/
theorem cechToRips_comp_ripsToCech (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    cechToRips R n d p hd ≫ reindexNatTrans twoMul (ripsToCech R n d p hd) =
      cechDouble R n p :=
  inclusionHom_comp R n (H := Filtration.reindex twoMul (Cech.filter p).sublevelFiltration)
    _ _

/-- For `0 ≤ r`, the Rips doubling component is the actual structure map. -/
theorem ripsDouble_app_of_nonneg (d : MetricSpace V) {r : ℝ} (hr : 0 ≤ r) :
    (ripsDouble R n d).app r =
      structureMap (sublevelModule R (Rips.filter d) n) (show r ≤ 2 * r by linarith) := rfl

/-- For `0 ≤ r`, the Čech doubling component is the actual structure map. -/
theorem cechDouble_app_of_nonneg (p : V → X) {r : ℝ} (hr : 0 ≤ r) :
    (cechDouble R n p).app r =
      structureMap (sublevelModule R (Cech.filter p) n) (show r ≤ 2 * r by linarith) := rfl

end Cech

end TDA.Persistence
