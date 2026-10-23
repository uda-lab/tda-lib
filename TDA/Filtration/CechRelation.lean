import TDA.Filtration.Cech
import TDA.Filtration.ShiftedSimplicialMap

/-!
# Ambient Čech faces under relations between labels

Configurations share a fixed ambient pseudometric space. A distance bound on related
points controls every finite part of a relational image at radius scale, with constant
one. The radius-filter argument takes an infimum over centers and requires no minimizing
center. For closed-ball complexes, the source center itself witnesses the target face.
-/

universe u v w

namespace TDA.Filtration.Cech

open TDA.Simplicial

variable {Z : Type u} {V : Type v} {W : Type w} [PseudoMetricSpace Z]

/-- Closed ambient Čech complexes, with the existing empty negative tail, form an
inclusion filtration. -/
def complexFiltration (p : V → Z) : SimplicialFiltration ℝ V where
  toFun := complex p
  monotone' := fun _ _ h => complex_mono p h

@[simp] theorem complexFiltration_apply (p : V → Z) (r : ℝ) :
    complexFiltration p r = complex p r := rfl

/-- Properness identifies the infimum-radius filtration with the closed-ball nerve. -/
theorem sublevelFiltration_eq_complexFiltration [ProperSpace Z] (p : V → Z) :
    (filter p).sublevelFiltration = complexFiltration p := by
  apply OrderHom.ext
  funext r
  exact sublevel_eq_complex p r

/-- Every point in a finite relational image stays within the source enclosing radius
plus the relation's displacement budget. Empty source faces are permitted here. -/
theorem radiusAt_le_add_of_relation (p : V → Z) (q : W → Z)
    {C : SetRel V W} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ v w, (v, w) ∈ C → dist (p v) (q w) ≤ ε)
    (z : Z) {σ : Finset V} {τ : Finset W}
    (hsub : (↑τ : Set W) ⊆ C.image ↑σ) :
    radiusAt q z τ ≤ radiusAt p z σ + ε := by
  refine (radiusAt_le_iff q z τ _).2
    ⟨add_nonneg (radiusAt_nonneg p z σ) hε, ?_⟩
  intro w hw
  obtain ⟨v, hv, hvw⟩ := hsub hw
  calc
    dist z (q w) ≤ dist z (p v) + dist (p v) (q w) := dist_triangle _ _ _
    _ ≤ radiusAt p z σ + ε := add_le_add (dist_le_radiusAt p z hv) (h v w hvw)

/-- Infimal enclosing radii satisfy the same bound even when no optimal center exists. -/
theorem filter_value_le_add_of_relation (p : V → Z) (q : W → Z)
    {C : SetRel V W} {ε : ℝ}
    (h : ∀ v w, (v, w) ∈ C → dist (p v) (q w) ≤ ε)
    (σ : TotalFace (Rips.fullComplex V)) (τ : TotalFace (Rips.fullComplex W))
    (hsub : (↑τ.val : Set W) ⊆ C.image ↑σ.val) :
    (filter q).value τ ≤ (filter p).value σ + ε := by
  obtain ⟨w, hw⟩ := τ.property
  obtain ⟨v, _, hvw⟩ := hsub hw
  have hε := dist_nonneg.trans (h v w hvw)
  have : Nonempty Z := ⟨p v⟩
  have key : (filter q).value τ - ε ≤ (filter p).value σ := by
    rw [filter_value p]
    refine le_ciInf fun z => ?_
    have := (filter_value_le_radiusAt q τ z).trans
      (radiusAt_le_add_of_relation p q hε h z hsub)
    linarith
  linarith

/-- A displacement bound sends finite relational face images into shifted radius-filter
sublevels. Neither label totality nor label finiteness is needed. -/
theorem isShiftedSimplicialRelation_of_dist_le (p : V → Z) (q : W → Z)
    {C : SetRel V W} {ε : ℝ}
    (h : ∀ v w, (v, w) ∈ C → dist (p v) (q w) ≤ ε) :
    IsShiftedSimplicialRelation (filter p).sublevelFiltration
      (filter q).sublevelFiltration ε C := by
  intro r σ hσ τ hτ hsub
  obtain ⟨hσn, hσr⟩ := (FilterFunction.mem_sublevel_iff _ r σ).1 hσ
  exact (FilterFunction.mem_sublevel_iff _ (r + ε) τ).2
    ⟨hτ, (filter_value_le_add_of_relation p q h ⟨σ, hσn⟩ ⟨τ, hτ⟩ hsub).trans
      (add_le_add hσr le_rfl)⟩

/-- The exact closed-ball nerve has the same relation geometry: retain its witness
center instead of appealing to infimum attainment. -/
theorem isShiftedSimplicialRelation_complex_of_dist_le (p : V → Z) (q : W → Z)
    {C : SetRel V W} {ε : ℝ}
    (h : ∀ v w, (v, w) ∈ C → dist (p v) (q w) ≤ ε) :
    IsShiftedSimplicialRelation (complexFiltration p) (complexFiltration q) ε C := by
  intro r σ hσ τ hτ hsub
  obtain ⟨_, z, hz⟩ := (mem_complex_iff p r σ).1 hσ
  refine (mem_complex_iff q (r + ε) τ).2 ⟨hτ, z, ?_⟩
  intro w hw
  obtain ⟨v, hv, hvw⟩ := hsub hw
  exact (dist_triangle z (p v) (q w)).trans (add_le_add (hz v hv) (h v w hvw))

end TDA.Filtration.Cech
