import TDA.Simplicial.Collapse
import TDA.Simplicial.FiniteComplex

set_option autoImplicit false

/-!
# Checking supplied collapse sequences on finite face tables

A face table is a `Finset (Finset V)`. A step of a certificate is a pair `(σ, τ)`, to be read as
"delete the free face `σ` together with its coface `τ`". `IsFreePairTable F σ τ` is the decidable
test that `(σ, τ)` is free in the table `F`: both faces are listed, `σ ⊆ τ` and `τ \ σ` is a
single vertex, and `τ` is the only listed face strictly containing `σ`. `collapseTable F σ τ`
erases the two faces. `runSteps F steps` applies the steps in order and returns `none` at the
first step that is not free; `checkSteps F steps T` accepts exactly when it returns `some T`, so
the endpoint is the supplied table `T` itself (`checkSteps_eq_true_iff`, `eq_of_checkSteps`).

The tables are related to the library relation through any complex `K` whose faces are exactly
the faces listed in `F` (`∀ s, s ∈ K ↔ s ∈ F`). The table test agrees with `IsFreePair`
(`isFreePair_iff_isFreePairTable`), and erasing the two faces of a free pair lists the faces of
`deletion K σ` (`mem_deletion_iff_mem_collapseTable`). An accepted certificate therefore gives
`CollapsesTo K L` for every `L` with face table `T` (`collapsesTo_of_checkSteps`). Conversely,
every collapse of `K` onto `L` has an accepted certificate (`exists_checkSteps_of_collapsesTo`),
so acceptance of some certificate characterizes `CollapsesTo` for complexes with finite face
tables (`collapsesTo_iff_exists_checkSteps`). For `FiniteComplex m`, the table is the stored
face set (`FiniteComplex.collapsesTo_of_checkSteps`).

No closure property of `F` is checked: it is supplied by `K`. The checker is a plain recursive
function over `Finset` operations, intended for `decide +kernel` on small tables.
-/

namespace TDA.Simplicial

variable {V : Type*} [DecidableEq V]

/-- The step `(σ, τ)` is free in the face table `F`: both faces are listed, `τ` adds exactly one
vertex to `σ`, and `τ` is the only listed face strictly containing `σ`. -/
def IsFreePairTable (F : Finset (Finset V)) (σ τ : Finset V) : Prop :=
  σ ∈ F ∧ τ ∈ F ∧ σ ⊆ τ ∧ (τ \ σ).card = 1 ∧ ∀ ω ∈ F, σ ⊂ ω → ω = τ

/-- The table test is decidable: every clause is a finite `Finset` check. -/
instance instDecidableIsFreePairTable (F : Finset (Finset V)) (σ τ : Finset V) :
    Decidable (IsFreePairTable F σ τ) := by
  unfold IsFreePairTable
  infer_instance

/-- The face table after the step `(σ, τ)`: the two faces are erased. -/
def collapseTable (F : Finset (Finset V)) (σ τ : Finset V) : Finset (Finset V) :=
  (F.erase σ).erase τ

/-- Run the steps in order. The result is the final table, or `none` as soon as a step is not
free in the current table. -/
def runSteps : Finset (Finset V) → List (Finset V × Finset V) → Option (Finset (Finset V))
  | F, [] => some F
  | F, (σ, τ) :: steps =>
    if IsFreePairTable F σ τ then runSteps (collapseTable F σ τ) steps else none

/-- Accept the certificate `steps` from the table `F` to the table `T`: every step is free in the
current table, and the final table is exactly `T`. -/
def checkSteps (F : Finset (Finset V)) (steps : List (Finset V × Finset V))
    (T : Finset (Finset V)) : Bool :=
  decide (runSteps F steps = some T)

/-- Acceptance means that the run succeeds and ends exactly at `T`. -/
theorem checkSteps_eq_true_iff {F T : Finset (Finset V)} {steps : List (Finset V × Finset V)} :
    checkSteps F steps T = true ↔ runSteps F steps = some T :=
  decide_eq_true_iff

/-- The endpoint of an accepted certificate is determined by the start and the steps. -/
theorem eq_of_checkSteps {F T T' : Finset (Finset V)} {steps : List (Finset V × Finset V)}
    (h : checkSteps F steps T = true) (h' : checkSteps F steps T' = true) : T = T' := by
  rw [checkSteps_eq_true_iff] at h h'
  exact Option.some_injective _ (h.symm.trans h')

/-- The empty certificate is accepted exactly when the target is the start. -/
@[simp] theorem checkSteps_nil {F T : Finset (Finset V)} :
    checkSteps F [] T = true ↔ F = T := by
  rw [checkSteps_eq_true_iff, runSteps, Option.some_inj]

/-- A nonempty certificate is accepted exactly when its first step is free and the rest is
accepted from the table after that step. -/
@[simp] theorem checkSteps_cons {F T : Finset (Finset V)} {σ τ : Finset V}
    {steps : List (Finset V × Finset V)} :
    checkSteps F ((σ, τ) :: steps) T = true ↔
      IsFreePairTable F σ τ ∧ checkSteps (collapseTable F σ τ) steps T = true := by
  simp only [checkSteps_eq_true_iff, runSteps]
  split_ifs with h
  · exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
  · exact ⟨fun e => absurd e (by simp), fun e => absurd e.1 h⟩

variable {K L : PreAbstractSimplicialComplex V} {F T : Finset (Finset V)}

/-- On a complex whose faces are listed by `F`, the table test is the free-pair relation. -/
theorem isFreePair_iff_isFreePairTable (hK : ∀ s, s ∈ K ↔ s ∈ F) {σ τ : Finset V} :
    IsFreePair K σ τ ↔ IsFreePairTable F σ τ := by
  constructor
  · intro h
    exact ⟨(hK σ).1 h.lower_mem, (hK τ).1 h.upper_mem,
      (Finset.covBy_iff_card_sdiff_eq_one.1 h.covBy).1,
      (Finset.covBy_iff_card_sdiff_eq_one.1 h.covBy).2,
      fun ω hω hσω => h.eq_upper ((hK ω).2 hω) hσω⟩
  · rintro ⟨hσ, hτ, hsub, hcard, hup⟩
    exact ⟨(hK σ).2 hσ, (hK τ).2 hτ, Finset.covBy_iff_card_sdiff_eq_one.2 ⟨hsub, hcard⟩,
      fun ω hω hσω => hup ω ((hK ω).1 hω) hσω⟩

/-- Erasing the two faces of a free pair lists the faces of the deletion of the free face. -/
theorem mem_deletion_iff_mem_collapseTable (hK : ∀ s, s ∈ K ↔ s ∈ F) {σ τ : Finset V}
    (h : IsFreePair K σ τ) (s : Finset V) :
    s ∈ deletion K σ ↔ s ∈ collapseTable F σ τ := by
  rw [h.mem_deletion_iff, collapseTable, Finset.mem_erase, Finset.mem_erase, hK]
  tauto

/-- Soundness: if `K` and `L` have face tables `F` and `T` and the certificate is accepted,
then `K` collapses to `L`. -/
theorem collapsesTo_of_checkSteps (hK : ∀ s, s ∈ K ↔ s ∈ F) (hL : ∀ s, s ∈ L ↔ s ∈ T)
    {steps : List (Finset V × Finset V)} (h : checkSteps F steps T = true) :
    CollapsesTo K L := by
  induction steps generalizing K F with
  | nil =>
    have e : K = L := SetLike.ext fun s => by rw [hK, hL, checkSteps_nil.1 h]
    rw [e]
    exact Relation.ReflTransGen.refl
  | cons step steps ih =>
    obtain ⟨σ, τ⟩ := step
    obtain ⟨hfree, hrest⟩ := checkSteps_cons.1 h
    have hp := (isFreePair_iff_isFreePairTable hK).2 hfree
    exact Relation.ReflTransGen.head hp.elementaryCollapsesTo
      (ih (mem_deletion_iff_mem_collapseTable hK hp) hrest)

/-- Completeness: every collapse of a complex with face table `F` onto a complex with face table
`T` has a certificate accepted by the checker. -/
theorem exists_checkSteps_of_collapsesTo (hK : ∀ s, s ∈ K ↔ s ∈ F)
    (hL : ∀ s, s ∈ L ↔ s ∈ T) (h : CollapsesTo K L) :
    ∃ steps, checkSteps F steps T = true := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing F with
  | refl =>
    refine ⟨[], checkSteps_nil.2 (Finset.ext fun s => ?_)⟩
    rw [← hK, hL]
  | head hstep _ ih =>
    obtain ⟨σ, τ, hp, rfl⟩ := hstep
    obtain ⟨steps, hsteps⟩ := ih (mem_deletion_iff_mem_collapseTable hK hp)
    exact ⟨(σ, τ) :: steps,
      checkSteps_cons.2 ⟨(isFreePair_iff_isFreePairTable hK).1 hp, hsteps⟩⟩

/-- For complexes with face tables `F` and `T`, `K` collapses to `L` exactly when some
certificate from `F` to `T` is accepted. -/
theorem collapsesTo_iff_exists_checkSteps (hK : ∀ s, s ∈ K ↔ s ∈ F)
    (hL : ∀ s, s ∈ L ↔ s ∈ T) : CollapsesTo K L ↔ ∃ steps, checkSteps F steps T = true :=
  ⟨exists_checkSteps_of_collapsesTo hK hL,
    fun ⟨_, h⟩ => collapsesTo_of_checkSteps hK hL h⟩

/-- Soundness for stored finite complexes: an accepted certificate between their face sets is a
collapse of the converted complexes. -/
theorem FiniteComplex.collapsesTo_of_checkSteps {m : ℕ} {C D : FiniteComplex m}
    {steps : List (Finset (Fin m) × Finset (Fin m))} (h : checkSteps C.faces steps D.faces = true) :
    CollapsesTo C.toPre D.toPre :=
  TDA.Simplicial.collapsesTo_of_checkSteps C.mem_toPre D.mem_toPre h

end TDA.Simplicial
