import TDA.Persistence.FaceOrderTemplate
import TDA.Filtration.CompatibleOrderExistence

set_option autoImplicit false

/-!
# General monotone reparametrisations of sublevel diagrams

These are library extensions proved from the merged face-template and rank-diagram
definitions. A monotone reparametrisation may identify finite endpoints, so the
diagonal filter is retained explicitly.
-/

universe u v w

namespace TDA.Persistence

open TDA.Simplicial TDA.Filtration CategoryTheory CategoryTheory.Limits

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {α : Type v} {β : Type w} [LinearOrder α] [LinearOrder β]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TDA.Simplicial.TotalFace K)]

/-- A monotone change of filter values maps finite and essential face-template bars,
discarding exactly the finite bars that become diagonal. -/
theorem dgm_points_map_of_monotoneOn (f : FilterFunction K α) (g : FilterFunction K β)
    (φ : α → β) (hφ : MonotoneOn φ (Set.range f.value))
    (hvalue : ∀ s, g.value s = φ (f.value s)) (n : ℕ) :
    (dgm k g n).points =
      ((dgm k f n).points.map (fun p => (φ p.1, WithTop.map φ p.2))).filter
        (fun p => (p.1 : WithTop β) ≠ p.2) := by
  classical
  rcases exists_compatibleOrder f with ⟨e⟩
  have hg : Monotone (g.value ∘ e.enum) := by
    intro a b hab
    calc
      g.value (e.enum a) = φ (f.value (e.enum a)) := hvalue _
      _ ≤ φ (f.value (e.enum b)) :=
        hφ ⟨e.enum a, rfl⟩ ⟨e.enum b, rfl⟩ (e.monotone hab)
      _ = g.value (e.enum b) := (hvalue _).symm
  rw [← evaluateFaceTemplate_eq_dgm k e f e.monotone n,
    ← evaluateFaceTemplate_eq_dgm k e g hg n]
  have hpair :
      (faceTemplatePairs k e n).map (pairValues g e) =
        ((faceTemplatePairs k e n).map (pairValues f e)).map (Prod.map φ φ) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro p hp
    simp [pairValues, hvalue]
  have hbirth :
      (faceTemplateEssential k e n).map (birthValue g e) =
        ((faceTemplateEssential k e n).map (birthValue f e)).map φ := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro i hi
    simp [birthValue, hvalue]
  have hfinite (P : Multiset (α × α)) :
      ((P.map (Prod.map φ φ)).filter (fun p : β × β => p.1 ≠ p.2)).map
          (fun p => (p.1, (p.2 : WithTop β))) =
        (((P.filter (fun p : α × α => p.1 ≠ p.2)).map
          (fun p => (p.1, (p.2 : WithTop α)))).map
            (fun p => (φ p.1, WithTop.map φ p.2))).filter
          (fun p => (p.1 : WithTop β) ≠ p.2) := by
    induction P using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      obtain ⟨a₁, a₂⟩ := a
      by_cases h1 : a₁ = a₂
      · subst h1
        simpa [Multiset.filter_cons] using ih
      · by_cases h2 : φ a₁ = φ a₂
        · simpa [Multiset.filter_cons, h1, h2] using ih
        · simpa [Multiset.filter_cons, h1, h2] using ih
  have hessential (P : Multiset α) :
      (P.map φ).map (fun b => (b, (⊤ : WithTop β))) =
        ((P.map (fun b => (b, (⊤ : WithTop α)))).map
          (fun p => (φ p.1, WithTop.map φ p.2))).filter
            (fun p => (p.1 : WithTop β) ≠ p.2) := by
    induction P using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simpa [Multiset.filter_cons] using ih
  change
    (((faceTemplatePairs k e n).map (pairValues g e)).filter
        (fun p => p.1 ≠ p.2)).map
        (fun p => (p.1, (p.2 : WithTop β))) +
      ((faceTemplateEssential k e n).map (birthValue g e)).map
        (fun b => (b, (⊤ : WithTop β))) =
      (((((faceTemplatePairs k e n).map (pairValues f e)).filter
        (fun p => p.1 ≠ p.2)).map
        (fun p => (p.1, (p.2 : WithTop α))) +
      ((faceTemplateEssential k e n).map (birthValue f e)).map
        (fun b => (b, (⊤ : WithTop α)))).map
        (fun p => (φ p.1, WithTop.map φ p.2))).filter
        (fun p => (p.1 : WithTop β) ≠ p.2)
  rw [hpair, hbirth, Multiset.map_add, Multiset.filter_add, hfinite,
    hessential]

/-- The homology rank at a threshold is the number of diagram bars alive there. -/
theorem finrank_sublevelHomology_eq_countP (f : FilterFunction K α) (n : ℕ) (t : α) :
    Module.finrank k (simplicialHomology (f.sublevel t) k n) =
      (dgm k f n).points.countP
        (fun p => p.1 ≤ t ∧ (t : WithTop α) < p.2) := by
  rw [← rank_sublevelHomologyMap k f n t t le_rfl]
  have h : simplicialHomologyIncl k (f.sublevel_mono (le_refl t)) n = 𝟙 _ :=
    simplicialHomologyIncl_id k (f.sublevel t) n
  rw [h, ModuleCat.hom_id, LinearMap.range_id, finrank_top]

/-- A diagram birth has nonzero sublevel homology in its degree. -/
theorem not_isZero_sublevelHomology_of_mem_dgm (f : FilterFunction K α) {n : ℕ}
    {p : α × WithTop α} (hp : p ∈ (dgm k f n).points) :
    ¬ IsZero (simplicialHomology (f.sublevel p.1) k n) := by
  intro hz
  have hcount : 0 <
      (dgm k f n).points.countP
        (fun q => q.1 ≤ p.1 ∧ (p.1 : WithTop α) < q.2) :=
    Multiset.countP_pos.2 ⟨p, hp, ⟨le_rfl, (dgm_isPositive k f n p hp)⟩⟩
  have hfin : 0 < Module.finrank k (simplicialHomology (f.sublevel p.1) k n) := by
    rw [finrank_sublevelHomology_eq_countP k f n p.1]
    exact hcount
  haveI : Subsingleton (simplicialHomology (f.sublevel p.1) k n) :=
    ModuleCat.subsingleton_of_isZero hz
  have hzero : Module.finrank k (simplicialHomology (f.sublevel p.1) k n) = 0 :=
    Module.finrank_zero_of_subsingleton (R := k)
  exact (Nat.not_lt_zero _ (hzero ▸ hfin))

/-- If every sublevel homology group in a degree is zero, its actual diagram is empty. -/
theorem dgm_points_eq_zero_of_isZero (f : FilterFunction K α) {n : ℕ}
    (h : ∀ t, IsZero (simplicialHomology (f.sublevel t) k n)) :
    (dgm k f n).points = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro p hp
  exact not_isZero_sublevelHomology_of_mem_dgm k f hp (h p.1)

end TDA.Persistence
