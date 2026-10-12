import TDA.Persistence.SublevelDiagramTransport
import TDA.Persistence.SmoothFaceLift
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.ULift

set_option autoImplicit false

/-!
Actual diagram transport regression fixtures.
All data and proofs are private and use public simplicial homology and inclusion APIs.
-/

universe u v w
namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration

private def prepEmptyFilter (V : Type u) (α : Type v) [LinearOrder α] :
    FilterFunction (⊥ : PreAbstractSimplicialComplex V) α where
  value := fun s => ((mem_bot_iff s.val).mp s.property).elim
  mono := by
    intro τ σ _
    exact ((mem_bot_iff τ.val).mp τ.property).elim

private instance prepEmptyFaces (V : Type u) :
    Fintype (TotalFace (⊥ : PreAbstractSimplicialComplex V)) := by
  letI : IsEmpty (TotalFace (⊥ : PreAbstractSimplicialComplex V)) :=
    ⟨fun s => ((mem_bot_iff s.val).mp s.property).elim⟩
  exact Fintype.ofIsEmpty

private theorem prepEmptyOrdering (V : Type u)
    (α : Type v) (β : Type w) [LinearOrder α] [LinearOrder β] :
    OrderingEquivalent (prepEmptyFilter V α) (prepEmptyFilter V β) := by
  intro s _
  exact ((mem_bot_iff s.val).mp s.property).elim

/-- F0 consumes the first law and checks its common occurrence multiset is zero. -/
private theorem f0_empty_common (V : Type u) [LinearOrder V]
    (k : Type u) [Field k] (α : Type v) (β : Type w)
    [LinearOrder α] [LinearOrder β] (n : ℕ) :
    ∃ E : Multiset (TotalFace (⊥ : PreAbstractSimplicialComplex V) ×
        Option (TotalFace (⊥ : PreAbstractSimplicialComplex V))),
      E = 0 ∧
      (dgm k (prepEmptyFilter V α) n).points = E.map (fun p =>
        ((prepEmptyFilter V α).value p.1,
          p.2.elim (⊤ : WithTop α)
            (fun t => ((prepEmptyFilter V α).value t : WithTop α)))) ∧
      (dgm k (prepEmptyFilter V β) n).points = E.map (fun p =>
        ((prepEmptyFilter V β).value p.1,
          p.2.elim (⊤ : WithTop β)
            (fun t => ((prepEmptyFilter V β).value t : WithTop β)))) := by
  obtain ⟨E, hf, hg⟩ := dgm_common_face_endpoints_of_orderingEquivalent k
    (prepEmptyFilter V α) (prepEmptyFilter V β) (prepEmptyOrdering V α β) n
  have hz : E = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro p _
    exact ((mem_bot_iff p.1.val).mp p.1.property).elim
  exact ⟨E, hz, hf, hg⟩

private theorem f0_empty_diagrams (V : Type u) [LinearOrder V]
    (k : Type u) [Field k] (α : Type v) (β : Type w)
    [LinearOrder α] [LinearOrder β] (n : ℕ) :
    (dgm k (prepEmptyFilter V α) n).points = 0 ∧
      (dgm k (prepEmptyFilter V β) n).points = 0 := by
  obtain ⟨E, hE, hf, hg⟩ := f0_empty_common V k α β n
  subst E
  simpa using And.intro hf hg

/-- F0: inhabited source grades and Empty target grades, without a total phi. -/
private theorem f0_inhabited_to_empty (n : ℕ) :
    (dgm (ZMod 2) (prepEmptyFilter (Fin 2) ℚ) n).points = 0 ∧
      (dgm (ZMod 2) (prepEmptyFilter (Fin 2) Empty) n).points = 0 :=
  f0_empty_diagrams (Fin 2) (ZMod 2) ℚ Empty n

/-- F0: the second law uses an actual empty-domain total function. -/
private theorem f0_empty_domain_phi (n : ℕ) :
    (dgm (ZMod 2) (prepEmptyFilter (Fin 2) ℚ) n).points =
      (dgm (ZMod 2) (prepEmptyFilter (Fin 2) Empty) n).points.map
        (fun p => ((Empty.elim p.1 : ℚ), WithTop.map (Empty.elim : Empty → ℚ) p.2)) := by
  apply dgm_points_map_of_strictMonoOn (ZMod 2)
    (prepEmptyFilter (Fin 2) Empty) (prepEmptyFilter (Fin 2) ℚ)
    (Empty.elim : Empty → ℚ)
  · intro a
    exact a.elim
  · intro s
    exact ((mem_bot_iff s.val).mp s.property).elim

private abbrev prepEdgeK : PreAbstractSimplicialComplex (Fin 2) := ⊤

private instance prepEdgeMem (s : Finset (Fin 2)) : Decidable (s ∈ prepEdgeK) := by
  change Decidable s.Nonempty
  infer_instance

private instance prepEdgeFaces : Fintype (TotalFace prepEdgeK) := inferInstance

private theorem prepEdgeFaceCases (s : TotalFace prepEdgeK) :
    s.val = ({0} : Finset (Fin 2)) ∨
    s.val = ({1} : Finset (Fin 2)) ∨
    s.val = ({0, 1} : Finset (Fin 2)) := by
  have h : ∀ t : Finset (Fin 2), t.Nonempty →
      t = ({0} : Finset (Fin 2)) ∨ t = ({1} : Finset (Fin 2)) ∨
      t = ({0, 1} : Finset (Fin 2)) := by decide
  exact h s.val s.property

/-- The source F2/F3 filter has genuine births 2,5 and edge grade 9. -/
private def prepEdgeSource : FilterFunction prepEdgeK ℚ where
  value := fun s =>
    if s.val = ({0} : Finset (Fin 2)) then 2
    else if s.val = ({1} : Finset (Fin 2)) then 5
    else 9
  mono := by
    intro τ σ hsub
    rcases prepEdgeFaceCases τ with hτ | hτ | hτ <;>
      rcases prepEdgeFaceCases σ with hσ | hσ | hσ <;>
      simp [hτ, hσ, Finset.subset_iff] at hsub ⊢
    all_goals norm_num [Finset.ext_iff] at *

/-- The target F2/F3 filter has genuine births 3,6 and edge grade 10. -/
private def prepEdgeTarget : FilterFunction prepEdgeK ℚ where
  value := fun s =>
    if s.val = ({0} : Finset (Fin 2)) then 3
    else if s.val = ({1} : Finset (Fin 2)) then 6
    else 10
  mono := by
    intro τ σ hsub
    rcases prepEdgeFaceCases τ with hτ | hτ | hτ <;>
      rcases prepEdgeFaceCases σ with hσ | hσ | hσ <;>
      simp [hτ, hσ, Finset.subset_iff] at hsub ⊢
    all_goals norm_num [Finset.ext_iff] at *

private def prepEdgeV0 : TotalFace prepEdgeK := ⟨{0}, by decide⟩
private def prepEdgeV1 : TotalFace prepEdgeK := ⟨{1}, by decide⟩
private def prepEdgeE01 : TotalFace prepEdgeK := ⟨{0, 1}, by decide⟩

private theorem prepEdgeValues :
    prepEdgeSource.value prepEdgeV0 = 2 ∧
    prepEdgeSource.value prepEdgeV1 = 5 ∧
    prepEdgeSource.value prepEdgeE01 = 9 ∧
    prepEdgeTarget.value prepEdgeV0 = 3 ∧
    prepEdgeTarget.value prepEdgeV1 = 6 ∧
    prepEdgeTarget.value prepEdgeE01 = 10 := by
  norm_num [prepEdgeSource, prepEdgeTarget, prepEdgeV0, prepEdgeV1, prepEdgeE01,
    Finset.ext_iff]

private theorem prepEdgeRange : Set.range prepEdgeSource.value = ({2, 5, 9} : Set ℚ) := by
  ext b
  constructor
  · rintro ⟨s, rfl⟩
    rcases prepEdgeFaceCases s with h | h | h <;>
      norm_num [prepEdgeSource, h, Finset.ext_iff]
  · intro hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl
    · exact ⟨prepEdgeV0, prepEdgeValues.1⟩
    · exact ⟨prepEdgeV1, prepEdgeValues.2.1⟩
    · exact ⟨prepEdgeE01, prepEdgeValues.2.2.1⟩

/-- F3 is strictly increasing only at the attained grades. -/
private def prepSupportPhi (x : ℚ) : ℚ :=
  if x = 2 then 3 else if x = 5 then 6 else if x = 9 then 10 else 0

private theorem f3_support_strict : StrictMonoOn prepSupportPhi (Set.range prepEdgeSource.value) := by
  rw [prepEdgeRange]
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    norm_num [prepSupportPhi] at *

private theorem f3_away_collision : prepSupportPhi 0 = prepSupportPhi 1 := by
  norm_num [prepSupportPhi]

private theorem f3_not_global_monotone : ¬ Monotone prepSupportPhi := by
  intro h
  have hc := h (show (2 : ℚ) ≤ 3 by norm_num)
  norm_num [prepSupportPhi] at hc

private theorem f3_value_transport (s : TotalFace prepEdgeK) :
    prepEdgeTarget.value s = prepSupportPhi (prepEdgeSource.value s) := by
  rcases prepEdgeFaceCases s with h | h | h <;>
    norm_num [prepEdgeSource, prepEdgeTarget, prepSupportPhi, h, Finset.ext_iff]

private theorem f3_ordering : OrderingEquivalent prepEdgeSource prepEdgeTarget := by
  intro s t
  rw [f3_value_transport s, f3_value_transport t]
  exact (f3_support_strict.le_iff_le ⟨s, rfl⟩ ⟨t, rfl⟩).symm

/-- F3 genuine edge consumer of the common-face-endpoint occurrence law. -/
private theorem f3_common_face_endpoints (n : ℕ) :
    ∃ E : Multiset (TotalFace prepEdgeK × Option (TotalFace prepEdgeK)),
      (dgm (ZMod 2) prepEdgeSource n).points = E.map (fun p =>
        (prepEdgeSource.value p.1, p.2.elim (⊤ : WithTop ℚ)
          (fun t => (prepEdgeSource.value t : WithTop ℚ)))) ∧
      (dgm (ZMod 2) prepEdgeTarget n).points = E.map (fun p =>
        (prepEdgeTarget.value p.1, p.2.elim (⊤ : WithTop ℚ)
          (fun t => (prepEdgeTarget.value t : WithTop ℚ)))) :=
  dgm_common_face_endpoints_of_orderingEquivalent (ZMod 2)
    prepEdgeSource prepEdgeTarget f3_ordering n

/-- F3 genuine edge consumer of the raw points.map law, with no global monotonicity. -/
private theorem f3_points_map (n : ℕ) :
    (dgm (ZMod 2) prepEdgeTarget n).points =
      (dgm (ZMod 2) prepEdgeSource n).points.map
        (fun p => (prepSupportPhi p.1, WithTop.map prepSupportPhi p.2)) :=
  dgm_points_map_of_strictMonoOn (ZMod 2) prepEdgeSource prepEdgeTarget
    prepSupportPhi f3_support_strict f3_value_transport n

/-- F3 exhibits the stated obstruction to arbitrary ambient-threshold naturality. -/
private theorem f3_ambient_threshold_failure :
    prepEdgeSource.sublevel 3 ≠ ⊥ ∧
      prepEdgeTarget.sublevel (prepSupportPhi 3) = ⊥ := by
  constructor
  · intro h
    have hm : prepEdgeV0.val ∈ prepEdgeSource.sublevel 3 := by
      apply (prepEdgeSource.mem_sublevel_iff_of_mem 3 prepEdgeV0).mpr
      rw [prepEdgeValues.1]
      norm_num
    rw [h] at hm
    exact (mem_bot_iff _).mp hm
  · apply prepEdgeTarget.sublevel_eq_bot_of_forall_lt
    intro s
    rcases prepEdgeFaceCases s with h | h | h <;>
      norm_num [prepEdgeTarget, prepSupportPhi, h, Finset.ext_iff]

/-- F5 the first public type is consumed with independent V/k, alpha and beta universes. -/
private theorem f5_generic_common {V : Type u} [LinearOrder V]
    (k : Type u) [Field k] {α : Type v} {β : Type w}
    [LinearOrder α] [LinearOrder β] {K : PreAbstractSimplicialComplex V}
    [Fintype (TotalFace K)] (f : FilterFunction K α) (g : FilterFunction K β)
    (hfg : OrderingEquivalent f g) (n : ℕ) :
    ∃ E : Multiset (TotalFace K × Option (TotalFace K)),
      (dgm k f n).points = E.map (fun p =>
        (f.value p.1, p.2.elim (⊤ : WithTop α) (fun t => (f.value t : WithTop α)))) ∧
      (dgm k g n).points = E.map (fun p =>
        (g.value p.1, p.2.elim (⊤ : WithTop β) (fun t => (g.value t : WithTop β)))) :=
  dgm_common_face_endpoints_of_orderingEquivalent k f g hfg n

/-- F5 the second public type is consumed with independent V/k, alpha and beta universes. -/
private theorem f5_generic_points_map {V : Type u} [LinearOrder V]
    (k : Type u) [Field k] {α : Type v} {β : Type w}
    [LinearOrder α] [LinearOrder β] {K : PreAbstractSimplicialComplex V}
    [Fintype (TotalFace K)] (f : FilterFunction K α) (g : FilterFunction K β)
    (φ : α → β) (hφ : StrictMonoOn φ (Set.range f.value))
    (hvalue : ∀ s : TotalFace K, g.value s = φ (f.value s)) (n : ℕ) :
    (dgm k g n).points = (dgm k f n).points.map
      (fun p => (φ p.1, WithTop.map φ p.2)) :=
  dgm_points_map_of_strictMonoOn k f g φ hφ hvalue n

private instance prepSingletonMem (s : Finset (Fin 2)) :
    Decidable (s ∈ singletonFace (0 : Fin 2)) :=
  decidable_of_iff (s = {0}) (mem_singletonFace_iff 0 s).symm

private instance prepSingletonFaces : Fintype (TotalFace (singletonFace (0 : Fin 2))) :=
  inferInstance

private def f5_lifted_source :
    FilterFunction (singletonFace (0 : Fin 2)) (ULift.{v} ℚ) where
  value := fun _ => ULift.up 2
  mono := by intro _ _ _; exact le_rfl

private def f5_lifted_target :
    FilterFunction (singletonFace (0 : Fin 2)) (ULift.{w} ℚ) where
  value := fun _ => ULift.up 3
  mono := by intro _ _ _; exact le_rfl

private def f5_lifted_phi (x : ULift.{v} ℚ) : ULift.{w} ℚ :=
  ULift.up (x.down + 1)

private theorem f5_lifted_strict :
    StrictMonoOn f5_lifted_phi.{v,w} (Set.range f5_lifted_source.{v}.value) := by
  intro a _ b _ hab
  change a.down + 1 < b.down + 1
  have hab' : a.down < b.down := hab
  simpa only [add_comm] using add_lt_add_right hab' (1 : ℚ)

private theorem f5_lifted_value (s : TotalFace (singletonFace (0 : Fin 2))) :
    f5_lifted_target.{w}.value s = f5_lifted_phi.{v,w} (f5_lifted_source.{v}.value s) := by
  apply ULift.ext
  norm_num [f5_lifted_target, f5_lifted_phi, f5_lifted_source]

private theorem f5_nonempty_face :
    Nonempty (TotalFace (singletonFace (0 : Fin 2))) :=
  ⟨⟨{0}, (mem_singletonFace_iff _ _).mpr rfl⟩⟩

private theorem f5_lifted_ordering :
    OrderingEquivalent f5_lifted_source.{v} f5_lifted_target.{w} := by
  intro s t
  constructor <;> intro _ <;> exact le_rfl

/-- F5 is nonempty and instantiates both laws at separately lifted rational grade types. -/
private theorem f5_lifted_common (n : ℕ) :
    ∃ E : Multiset (TotalFace (singletonFace (0 : Fin 2)) ×
        Option (TotalFace (singletonFace (0 : Fin 2)))),
      (dgm (ZMod 2) f5_lifted_source.{v} n).points = E.map (fun p =>
        (f5_lifted_source.{v}.value p.1,
          p.2.elim (⊤ : WithTop (ULift.{v} ℚ))
            (fun t => (f5_lifted_source.{v}.value t : WithTop (ULift.{v} ℚ))))) ∧
      (dgm (ZMod 2) f5_lifted_target.{w} n).points = E.map (fun p =>
        (f5_lifted_target.{w}.value p.1,
          p.2.elim (⊤ : WithTop (ULift.{w} ℚ))
            (fun t => (f5_lifted_target.{w}.value t : WithTop (ULift.{w} ℚ))))) :=
  f5_generic_common (ZMod 2) f5_lifted_source.{v} f5_lifted_target.{w}
    f5_lifted_ordering n

private theorem f5_lifted_points_map (n : ℕ) :
    (dgm (ZMod 2) f5_lifted_target.{w} n).points =
      (dgm (ZMod 2) f5_lifted_source.{v} n).points.map
        (fun p => (f5_lifted_phi.{v,w} p.1, WithTop.map f5_lifted_phi.{v,w} p.2)) :=
  f5_generic_points_map (ZMod 2) f5_lifted_source.{v} f5_lifted_target.{w}
    f5_lifted_phi.{v,w} f5_lifted_strict f5_lifted_value n


open CategoryTheory

/-- A private genuine constant filter used by the numerical one-grade fixtures. -/
private def f1_constant (K : PreAbstractSimplicialComplex (Fin 2)) (b : ℚ) :
    FilterFunction K ℚ where
  value := fun _ => b
  mono := by intro _ _ _; exact le_rfl

private theorem f1_constant_critical {K : PreAbstractSimplicialComplex (Fin 2)}
    [Fintype (TotalFace K)] (s : TotalFace K) (b : ℚ) :
    (f1_constant K b).criticalValues = {b} := by
  ext x
  rw [FilterFunction.mem_criticalValues, Finset.mem_singleton]
  constructor
  · rintro ⟨t, h⟩
    exact h.symm
  · intro h
    subst x
    exact ⟨s, rfl⟩

private theorem f1_constant_card {K : PreAbstractSimplicialComplex (Fin 2)}
    [Fintype (TotalFace K)] (s : TotalFace K) (b : ℚ) :
    (f1_constant K b).criticalValues.card = 1 := by
  rw [f1_constant_critical s b]
  simp

private theorem f1_constant_value {K : PreAbstractSimplicialComplex (Fin 2)}
    [Fintype (TotalFace K)] (s : TotalFace K) (b : ℚ)
    (i : Fin (f1_constant K b).criticalValues.card) :
    (f1_constant K b).criticalValue i = b := by
  have h := (f1_constant K b).criticalValue_mem i
  simpa only [f1_constant_critical s b, Finset.mem_singleton] using h

private theorem f1_constant_stage {K : PreAbstractSimplicialComplex (Fin 2)}
    [Fintype (TotalFace K)] (s : TotalFace K) (b : ℚ)
    (i : Fin (f1_constant K b).criticalValues.card) :
    (f1_constant K b).gradeFiltration i = K := by
  rw [FilterFunction.gradeFiltration_apply, f1_constant_value s b i]
  apply le_antisymm ((f1_constant K b).sublevel_le b)
  intro t ht
  exact ((f1_constant K b).mem_sublevel_iff_of_mem b ⟨t, ht⟩).mpr le_rfl

private noncomputable def f1_constant_bar {K : PreAbstractSimplicialComplex (Fin 2)}
    [Fintype (TotalFace K)] (s : TotalFace K) (b : ℚ) :
    FiniteInterval (f1_constant K b).criticalValues.card :=
  ⟨0, 1, by decide, by rw [f1_constant_card s b]⟩

/-- Compute a one-grade barcode from the rank of its actual homology identity map. -/
private theorem f1_constant_barcode {K : PreAbstractSimplicialComplex (Fin 2)}
    [Fintype (TotalFace K)] (s : TotalFace K) (b : ℚ) (d : ℕ)
    (hd : Module.finrank (ZMod 2) (simplicialHomology K (ZMod 2) 0) = d) :
    gradeHomologyBarcode (ZMod 2) (f1_constant K b) 0 =
      Multiset.replicate d (f1_constant_bar s b) := by
  calc
    gradeHomologyBarcode (ZMod 2) (f1_constant K b) 0 =
        rankBarcode (barcodeModule (k := ZMod 2)
          (Multiset.replicate d (f1_constant_bar s b))) := by
      apply (rankBarcode_eq_iff
        (simplicialHomologyPModule (ZMod 2) (f1_constant K b).gradeFiltration 0)
        (barcodeModule (k := ZMod 2)
          (Multiset.replicate d (f1_constant_bar s b)))).mpr
      intro i j hij
      have hc := f1_constant_card s b
      have hi : i.val = 0 := by have := i.isLt; omega
      have hj : j.val = 0 := by have := j.isLt; omega
      have he : j = i := Fin.ext (hj.trans hi.symm)
      subst j
      have hr : structureMapRank
          (simplicialHomologyPModule (ZMod 2) (f1_constant K b).gradeFiltration 0)
          i i hij = d := by
        unfold structureMapRank
        rw [structureMapLinear_self, LinearMap.range_id, finrank_top,
          simplicialHomologyPModule_obj, f1_constant_stage s b i]
        exact hd
      rw [hr, rank_barcodeMap]
      symm
      calc
        _ = (Multiset.replicate d (f1_constant_bar s b)).card := by
          apply Multiset.countP_eq_card.mpr
          intro I hI
          have heI : I = f1_constant_bar s b := Multiset.eq_of_mem_replicate hI
          rw [heI]
          simp [f1_constant_bar, hi]
        _ = d := Multiset.card_replicate _ _
    _ = _ := rankBarcode_barcodeModule _

private theorem f1_constant_points {K : PreAbstractSimplicialComplex (Fin 2)}
    [Fintype (TotalFace K)] (s : TotalFace K) (b : ℚ) (d : ℕ)
    (hd : Module.finrank (ZMod 2) (simplicialHomology K (ZMod 2) 0) = d) :
    (dgm (ZMod 2) (f1_constant K b) 0).points =
      Multiset.replicate d (b, (⊤ : WithTop ℚ)) := by
  rw [dgm, f1_constant_barcode s b d hd]
  change (Multiset.replicate d (f1_constant_bar s b)).map
    (fun I => ((f1_constant K b).criticalValue
      ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
      if hd' : I.death < (f1_constant K b).criticalValues.card then
        ((f1_constant K b).criticalValue ⟨I.death, hd'⟩ : WithTop ℚ)
      else (⊤ : WithTop ℚ))) = _
  simp [Multiset.map_replicate, f1_constant_bar, f1_constant_card s b,
    f1_constant_value s b]

private def f1_face : TotalFace (singletonFace (0 : Fin 2)) :=
  ⟨{0}, (mem_singletonFace_iff _ _).mpr rfl⟩

private def f1_source : FilterFunction (singletonFace (0 : Fin 2)) ℚ :=
  f1_constant _ 2
private def f1_target : FilterFunction (singletonFace (0 : Fin 2)) ℚ :=
  f1_constant _ 3
private def f1_phi (x : ℚ) : ℚ := x + 1

private theorem f1_dimension :
    Module.finrank (ZMod 2)
      (simplicialHomology (singletonFace (0 : Fin 2)) (ZMod 2) 0) = 1 :=
  (simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).finrank_eq.trans
    (Module.finrank_self (ZMod 2))

private theorem f1_source_points :
    (dgm (ZMod 2) f1_source 0).points =
      ({((2 : ℚ), (⊤ : WithTop ℚ))} : Multiset (ℚ × WithTop ℚ)) := by
  simpa [f1_source] using f1_constant_points f1_face 2 1 f1_dimension

private theorem f1_target_points :
    (dgm (ZMod 2) f1_target 0).points =
      ({((3 : ℚ), (⊤ : WithTop ℚ))} : Multiset (ℚ × WithTop ℚ)) := by
  simpa [f1_target] using f1_constant_points f1_face 3 1 f1_dimension

private theorem f1_no_finite (x y : ℚ) :
    (x, (y : WithTop ℚ)) ∉ (dgm (ZMod 2) f1_source 0).points ∧
      (x, (y : WithTop ℚ)) ∉ (dgm (ZMod 2) f1_target 0).points := by
  rw [f1_source_points, f1_target_points]
  simp

private theorem f1_ordering : OrderingEquivalent f1_source f1_target := by
  intro s t
  constructor <;> intro _ <;> exact le_rfl

private theorem f1_strict : StrictMonoOn f1_phi (Set.range f1_source.value) := by
  intro a _ b _ hab
  simpa only [f1_phi, add_comm] using add_lt_add_right hab (1 : ℚ)

private theorem f1_value (s : TotalFace (singletonFace (0 : Fin 2))) :
    f1_target.value s = f1_phi (f1_source.value s) := by
  norm_num [f1_source, f1_target, f1_constant, f1_phi]

/-- F1 consumes the common-face occurrence law on the actual numerical singleton diagrams. -/
private theorem f1_common :
    ∃ E : Multiset (TotalFace (singletonFace (0 : Fin 2)) ×
        Option (TotalFace (singletonFace (0 : Fin 2)))),
      (dgm (ZMod 2) f1_source 0).points = E.map (fun p =>
        (f1_source.value p.1, p.2.elim (⊤ : WithTop ℚ)
          (fun t => (f1_source.value t : WithTop ℚ)))) ∧
      (dgm (ZMod 2) f1_target 0).points = E.map (fun p =>
        (f1_target.value p.1, p.2.elim (⊤ : WithTop ℚ)
          (fun t => (f1_target.value t : WithTop ℚ)))) :=
  dgm_common_face_endpoints_of_orderingEquivalent (ZMod 2)
    f1_source f1_target f1_ordering 0

private theorem f1_points_map :
    (dgm (ZMod 2) f1_target 0).points =
      (dgm (ZMod 2) f1_source 0).points.map
        (fun p => (f1_phi p.1, WithTop.map f1_phi p.2)) :=
  dgm_points_map_of_strictMonoOn (ZMod 2) f1_source f1_target
    f1_phi f1_strict f1_value 0

/-- F4 uses a genuine complex of two isolated vertices, with tied births. -/
private abbrev f4_K : PreAbstractSimplicialComplex (Fin 2) :=
  singletonFace (0 : Fin 2) ⊔ singletonFace (1 : Fin 2)

private theorem f4_mem (s : Finset (Fin 2)) :
    s ∈ f4_K ↔ s = {0} ∨ s = {1} := by
  change s ∈ singletonFace (0 : Fin 2) ∨ s ∈ singletonFace (1 : Fin 2) ↔ _
  rw [mem_singletonFace_iff, mem_singletonFace_iff]

private instance f4_decidableMem (s : Finset (Fin 2)) : Decidable (s ∈ f4_K) :=
  decidable_of_iff (s = {0} ∨ s = {1}) (f4_mem s).symm
private instance f4_faces : Fintype (TotalFace f4_K) := inferInstance

private def f4_face : TotalFace f4_K :=
  ⟨{0}, (f4_mem _).mpr (Or.inl rfl)⟩
private def f4_source : FilterFunction f4_K ℚ := f1_constant _ 2
private def f4_target : FilterFunction f4_K ℚ := f1_constant _ 3

private instance f4_no_edges : IsEmpty (Face f4_K 1) :=
  ⟨fun σ => by
    have hs := (f4_mem σ.val).mp σ.property.1
    have hc := σ.property.2
    rcases hs with h | h <;> simp [h] at hc⟩

private theorem f4_vertices_card : Fintype.card (Face f4_K 0) = 2 := by decide

private theorem f4_short_f_zero :
    ((simplicialChainComplex f4_K (ZMod 2)).sc 0).f = 0 := by
  have hf : (simplicialChainComplex f4_K (ZMod 2)).d 1 0 = 0 := by
    apply ModuleCat.hom_ext
    ext c
    change (boundary f4_K (ZMod 2) 0) c = 0
    have hc : c = 0 := by
      change Chain f4_K (ZMod 2) 1 at c
      exact Subsingleton.elim c 0
    rw [hc]
    exact map_zero _
  change (simplicialChainComplex f4_K (ZMod 2)).d
    ((ComplexShape.down ℕ).prev 0) 0 = 0
  rw [ChainComplex.prev]
  exact hf

private theorem f4_short_g_zero :
    ((simplicialChainComplex f4_K (ZMod 2)).sc 0).g = 0 := by
  change (simplicialChainComplex f4_K (ZMod 2)).d
    0 ((ComplexShape.down ℕ).next 0) = 0
  rw [ChainComplex.next_nat_zero]
  exact simplicialChainComplex_d_zero f4_K (ZMod 2) 0

private noncomputable def f4_H0_equiv :
    simplicialHomology f4_K (ZMod 2) 0 ≃ₗ[ZMod 2] Chain f4_K (ZMod 2) 0 :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((simplicialChainComplex f4_K (ZMod 2)).sc 0)
    f4_short_f_zero f4_short_g_zero).homologyIso.toLinearEquiv

private theorem f4_dimension :
    Module.finrank (ZMod 2) (simplicialHomology f4_K (ZMod 2) 0) = 2 := by
  rw [f4_H0_equiv.finrank_eq]
  rw [Module.finrank_finsupp_self]
  exact f4_vertices_card

/-- The one actual critical-grade structure map has rank two. -/
private theorem f4_actual_rank (i j : Fin f4_source.criticalValues.card) (hij : i ≤ j) :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) (f4_source.gradeFiltration.monotone hij) 0).hom) = 2 := by
  change structureMapRank
    (simplicialHomologyPModule (ZMod 2) f4_source.gradeFiltration 0) i j hij = 2
  have hc : f4_source.criticalValues.card = 1 := f1_constant_card f4_face 2
  have he : j = i := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  subst j
  unfold structureMapRank
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top,
    simplicialHomologyPModule_obj]
  change Module.finrank (ZMod 2)
    (simplicialHomology ((f1_constant f4_K 2).gradeFiltration i) (ZMod 2) 0) = 2
  rw [f1_constant_stage f4_face 2 i]
  exact f4_dimension

private theorem f4_source_points :
    (dgm (ZMod 2) f4_source 0).points =
      ({((2 : ℚ), (⊤ : WithTop ℚ)), ((2 : ℚ), (⊤ : WithTop ℚ))} :
        Multiset (ℚ × WithTop ℚ)) := by
  simpa [f4_source, Multiset.replicate_succ] using
    f1_constant_points f4_face 2 2 f4_dimension

private theorem f4_target_points :
    (dgm (ZMod 2) f4_target 0).points =
      ({((3 : ℚ), (⊤ : WithTop ℚ)), ((3 : ℚ), (⊤ : WithTop ℚ))} :
        Multiset (ℚ × WithTop ℚ)) := by
  simpa [f4_target, Multiset.replicate_succ] using
    f1_constant_points f4_face 3 2 f4_dimension

/-- Multiplicity is a natural count, even with coefficient field ZMod 2. -/
private theorem f4_counts :
    (dgm (ZMod 2) f4_source 0).points.count ((2 : ℚ), (⊤ : WithTop ℚ)) = 2 ∧
      (dgm (ZMod 2) f4_target 0).points.count ((3 : ℚ), (⊤ : WithTop ℚ)) = 2 := by
  rw [f4_source_points, f4_target_points]
  simp

/-- Two isolated vertices keep two equal essential births as a multiset. -/
private def f4_moving (x : ℝ) : FilterFunction f4_K ℝ where
  value := fun _ => 2 + x
  mono := by intros; exact le_rfl

private theorem f4_moving_points (x : ℝ) :
    (dgm (ZMod 2) (f4_moving x) 0).points =
      ({(2 + x, (⊤ : WithTop ℝ)), (2 + x, (⊤ : WithTop ℝ))} :
        Multiset (ℝ × WithTop ℝ)) := by
  have hmap := dgm_points_map_of_strictMonoOn (ZMod 2)
    f4_source (f4_moving x) (fun q : ℚ => (q : ℝ) + x)
    (by intro a _ b _ hab; simpa [add_comm] using (add_lt_add_right (show (a : ℝ) < (b : ℝ) by exact_mod_cast hab) x))
    (by intro s; simp [f4_source, f1_constant, f4_moving]) 0
  rw [hmap, f4_source_points]
  simp

private theorem f4_moving_smooth_lift :
    ∃ (m l : ℕ) (L : ℝ → (Fin m → ℝ × ℝ) × (Fin l → ℝ)),
      (∀ x : ℝ, dgm (ZMod 2) (f4_moving x) 0 = orderedQ m l (L x) ∧
        (dgm (ZMod 2) (f4_moving x) 0).points.count
          (2 + x, (⊤ : WithTop ℝ)) = 2) ∧
      ContDiffOn ℝ 1 L Set.univ := by
  have hF : ∀ s : TotalFace f4_K,
      ContDiffOn ℝ 1 (fun x : ℝ => (f4_moving x).value s) Set.univ := by
    intro s
    change ContDiffOn ℝ 1 (fun x : ℝ => 2 + x) Set.univ
    exact contDiffOn_const.add contDiffOn_id
  have horder : ∀ x ∈ (Set.univ : Set ℝ),
      OrderingEquivalent (f4_moving 0) (f4_moving x) := by
    intro x _ s t
    simp [f4_moving]
  obtain ⟨m, l, L, hfactor, hsmooth⟩ :=
    exists_smooth_face_lift (ZMod 2) f4_moving
      (x₀ := 0) isOpen_univ (Set.mem_univ 0) hF horder 0
  refine ⟨m, l, L, ?_, hsmooth⟩
  intro x
  constructor
  · exact hfactor x (Set.mem_univ x)
  · rw [f4_moving_points]
    simp

#print axioms f4_moving_points
#print axioms f4_moving_smooth_lift

private theorem f4_no_finite (x y : ℚ) :
    (x, (y : WithTop ℚ)) ∉ (dgm (ZMod 2) f4_source 0).points ∧
      (x, (y : WithTop ℚ)) ∉ (dgm (ZMod 2) f4_target 0).points := by
  rw [f4_source_points, f4_target_points]
  simp

private theorem f4_ordering : OrderingEquivalent f4_source f4_target := by
  intro s t
  constructor <;> intro _ <;> exact le_rfl

private theorem f4_strict : StrictMonoOn f1_phi (Set.range f4_source.value) := by
  intro a _ b _ hab
  simpa only [f1_phi, add_comm] using add_lt_add_right hab (1 : ℚ)

private theorem f4_value (s : TotalFace f4_K) :
    f4_target.value s = f1_phi (f4_source.value s) := by
  norm_num [f4_source, f4_target, f1_constant, f1_phi]

private theorem f4_common :
    ∃ E : Multiset (TotalFace f4_K × Option (TotalFace f4_K)),
      (dgm (ZMod 2) f4_source 0).points = E.map (fun p =>
        (f4_source.value p.1, p.2.elim (⊤ : WithTop ℚ)
          (fun t => (f4_source.value t : WithTop ℚ)))) ∧
      (dgm (ZMod 2) f4_target 0).points = E.map (fun p =>
        (f4_target.value p.1, p.2.elim (⊤ : WithTop ℚ)
          (fun t => (f4_target.value t : WithTop ℚ)))) :=
  dgm_common_face_endpoints_of_orderingEquivalent (ZMod 2)
    f4_source f4_target f4_ordering 0

private theorem f4_points_map :
    (dgm (ZMod 2) f4_target 0).points =
      (dgm (ZMod 2) f4_source 0).points.map
        (fun p => (f1_phi p.1, WithTop.map f1_phi p.2)) :=
  dgm_points_map_of_strictMonoOn (ZMod 2) f4_source f4_target
    f1_phi f4_strict f4_value 0

open CategoryTheory

/-! Actual three-grade filtered-edge H0 computation from chains, quotient classes
and inclusion maps. -/

private theorem f2_edge_values :
    prepEdgeSource.value prepEdgeV0 = 2 ∧
    prepEdgeSource.value prepEdgeV1 = 5 ∧
    prepEdgeSource.value prepEdgeE01 = 9 :=
  ⟨prepEdgeValues.1, prepEdgeValues.2.1, prepEdgeValues.2.2.1⟩

private theorem f2_edge_critical_set :
    prepEdgeSource.criticalValues = ({2, 5, 9} : Finset ℚ) := by
  ext b
  constructor
  · intro hb
    obtain ⟨σ, hσ⟩ := (prepEdgeSource.mem_criticalValues b).1 hb
    rcases prepEdgeFaceCases σ with h | h | h <;>
      simp [prepEdgeSource, h, Finset.ext_iff] at hσ ⊢
    all_goals (subst b; simp_all)
  · intro hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · exact (prepEdgeSource.mem_criticalValues 2).2 ⟨prepEdgeV0, f2_edge_values.1⟩
    · exact (prepEdgeSource.mem_criticalValues 5).2 ⟨prepEdgeV1, f2_edge_values.2.1⟩
    · exact (prepEdgeSource.mem_criticalValues 9).2 ⟨prepEdgeE01, f2_edge_values.2.2⟩

private theorem f2_edge_card : prepEdgeSource.criticalValues.card = 3 := by
  rw [f2_edge_critical_set]
  norm_num

private noncomputable def f2_edge_i0 : Fin prepEdgeSource.criticalValues.card :=
  ⟨0, by rw [f2_edge_card]; decide⟩

private noncomputable def f2_edge_i1 : Fin prepEdgeSource.criticalValues.card :=
  ⟨1, by rw [f2_edge_card]; decide⟩

private noncomputable def f2_edge_i2 : Fin prepEdgeSource.criticalValues.card :=
  ⟨2, by rw [f2_edge_card]; decide⟩

private theorem f2_edge_critical :
    prepEdgeSource.criticalValue f2_edge_i0 = 2 ∧
    prepEdgeSource.criticalValue f2_edge_i1 = 5 ∧
    prepEdgeSource.criticalValue f2_edge_i2 = 9 := by
  have h0 := prepEdgeSource.criticalValue_mem f2_edge_i0
  have h1 := prepEdgeSource.criticalValue_mem f2_edge_i1
  have h2 := prepEdgeSource.criticalValue_mem f2_edge_i2
  have h01 : prepEdgeSource.criticalValue f2_edge_i0 < prepEdgeSource.criticalValue f2_edge_i1 :=
    prepEdgeSource.criticalValue.strictMono (by apply Fin.lt_def.mpr; decide)
  have h12 : prepEdgeSource.criticalValue f2_edge_i1 < prepEdgeSource.criticalValue f2_edge_i2 :=
    prepEdgeSource.criticalValue.strictMono (by apply Fin.lt_def.mpr; decide)
  simp only [f2_edge_critical_set, Finset.mem_insert, Finset.mem_singleton] at h0 h1 h2
  rcases h0 with h0 | h0 | h0 <;>
    rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;>
    simp_all <;> linarith

private theorem f2_edge_mem_sublevel (r : ℚ) (s : Finset (Fin 2)) :
    s ∈ prepEdgeSource.sublevel r ↔
      (s = {0} ∧ (2 : ℚ) ≤ r) ∨
      (s = {1} ∧ (5 : ℚ) ≤ r) ∨
      (s = {0, 1} ∧ (9 : ℚ) ≤ r) := by
  constructor
  · intro hs
    obtain ⟨hsK, hv⟩ := (prepEdgeSource.mem_sublevel_iff r s).1 hs
    rcases prepEdgeFaceCases (⟨s, hsK⟩ : TotalFace prepEdgeK) with h | h | h
    · left
      refine ⟨h, ?_⟩
      have hs : (⟨s, hsK⟩ : TotalFace prepEdgeK) = prepEdgeV0 := Subtype.ext h
      rw [hs, f2_edge_values.1] at hv
      exact hv
    · right; left
      refine ⟨h, ?_⟩
      have hs : (⟨s, hsK⟩ : TotalFace prepEdgeK) = prepEdgeV1 := Subtype.ext h
      rw [hs, f2_edge_values.2.1] at hv
      exact hv
    · right; right
      refine ⟨h, ?_⟩
      have hs : (⟨s, hsK⟩ : TotalFace prepEdgeK) = prepEdgeE01 := Subtype.ext h
      rw [hs, f2_edge_values.2.2] at hv
      exact hv
  · rintro (⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩)
    · exact (prepEdgeSource.mem_sublevel_iff r _).2
        ⟨prepEdgeV0.property, by simpa [prepEdgeSource, prepEdgeV0] using hr⟩
    · exact (prepEdgeSource.mem_sublevel_iff r _).2
        ⟨prepEdgeV1.property, by simpa [prepEdgeSource, prepEdgeV1, Finset.ext_iff] using hr⟩
    · exact (prepEdgeSource.mem_sublevel_iff r _).2
        ⟨prepEdgeE01.property, by simpa [prepEdgeSource, prepEdgeE01, Finset.ext_iff] using hr⟩

private abbrev f2_edge_twoVertices : PreAbstractSimplicialComplex (Fin 2) :=
  singletonFace (0 : Fin 2) ⊔ singletonFace (1 : Fin 2)

private theorem f2_edge_region0 (r : ℚ) (hlo : (2 : ℚ) ≤ r) (hhi : r < 5) :
    prepEdgeSource.sublevel r = singletonFace (0 : Fin 2) := by
  ext s
  change s ∈ prepEdgeSource.sublevel r ↔ s ∈ singletonFace (0 : Fin 2)
  rw [f2_edge_mem_sublevel]
  have h9 : ¬ (9 : ℚ) ≤ r := by linarith
  simp [mem_singletonFace_iff, hlo, not_le.mpr hhi, h9]

private theorem f2_edge_region1 (r : ℚ) (hlo : (5 : ℚ) ≤ r) (hhi : r < 9) :
    prepEdgeSource.sublevel r = f2_edge_twoVertices := by
  ext s
  change s ∈ prepEdgeSource.sublevel r ↔ s ∈ f2_edge_twoVertices
  rw [f2_edge_mem_sublevel]
  have h2 : (2 : ℚ) ≤ r := by linarith
  have h9 : ¬ (9 : ℚ) ≤ r := by linarith
  simp only [h2, hlo, h9, and_true, and_false, or_false]
  change (s = {0} ∨ s = {1}) ↔ (s = {0} ∨ s = {1})
  rfl

private theorem f2_edge_region2 (r : ℚ) (hlo : (9 : ℚ) ≤ r) :
    prepEdgeSource.sublevel r = prepEdgeK := by
  apply prepEdgeSource.sublevel_eq_self_of_last_le
    (by rw [f2_edge_card]; decide) r
  have hlast : (⟨prepEdgeSource.criticalValues.card - 1,
      Nat.sub_lt (show 0 < prepEdgeSource.criticalValues.card by rw [f2_edge_card]; decide)
        (by decide)⟩ : Fin prepEdgeSource.criticalValues.card) = f2_edge_i2 := by
    apply Fin.ext
    change prepEdgeSource.criticalValues.card - 1 = 2
    have hc := f2_edge_card
    omega
  rw [hlast, f2_edge_critical.2.2]
  exact hlo

private theorem f2_edge_stage0 : prepEdgeSource.gradeFiltration f2_edge_i0 =
    singletonFace (0 : Fin 2) := by
  rw [prepEdgeSource.gradeFiltration_apply, f2_edge_critical.1]
  exact f2_edge_region0 2 le_rfl (by norm_num)

private theorem f2_edge_stage1 : prepEdgeSource.gradeFiltration f2_edge_i1 = f2_edge_twoVertices := by
  rw [prepEdgeSource.gradeFiltration_apply, f2_edge_critical.2.1]
  exact f2_edge_region1 5 le_rfl (by norm_num)

private theorem f2_edge_stage2 : prepEdgeSource.gradeFiltration f2_edge_i2 = prepEdgeK := by
  rw [prepEdgeSource.gradeFiltration_apply, f2_edge_critical.2.2]
  exact f2_edge_region2 9 le_rfl

private instance f2_edgeTwoMem (s : Finset (Fin 2)) : Decidable (s ∈ f2_edge_twoVertices) := by
  change Decidable (s = {0} ∨ s = {1})
  infer_instance

private instance f2_edgeTwoFaces : Fintype (TotalFace f2_edge_twoVertices) := inferInstance

private instance f2_edgeTwoNoEdges : IsEmpty (Face f2_edge_twoVertices 1) :=
  ⟨fun σ => by
    have hs : σ.1 = ({0} : Finset (Fin 2)) ∨ σ.1 = {1} := σ.2.1
    have hc := σ.2.2
    rcases hs with h | h <;> simp [h] at hc⟩

private theorem f2_edgeTwo_face0_card : Fintype.card (Face f2_edge_twoVertices 0) = 2 := by
  decide

private theorem f2_edgeTwo_short_f_zero :
    ((simplicialChainComplex f2_edge_twoVertices (ZMod 2)).sc 0).f = 0 := by
  have hf : (simplicialChainComplex f2_edge_twoVertices (ZMod 2)).d 1 0 = 0 := by
    apply ModuleCat.hom_ext
    ext c
    change (boundary f2_edge_twoVertices (ZMod 2) 0) c = 0
    have hc : c = 0 := by
      change Chain f2_edge_twoVertices (ZMod 2) 1 at c
      exact Subsingleton.elim c 0
    rw [hc]
    exact map_zero _
  change (simplicialChainComplex f2_edge_twoVertices (ZMod 2)).d
    ((ComplexShape.down ℕ).prev 0) 0 = 0
  rw [ChainComplex.prev]
  exact hf

private theorem f2_edgeTwo_short_g_zero :
    ((simplicialChainComplex f2_edge_twoVertices (ZMod 2)).sc 0).g = 0 := by
  change (simplicialChainComplex f2_edge_twoVertices (ZMod 2)).d
    0 ((ComplexShape.down ℕ).next 0) = 0
  rw [ChainComplex.next_nat_zero]
  exact simplicialChainComplex_d_zero f2_edge_twoVertices (ZMod 2) 0

private noncomputable def f2_edgeTwoH0Equiv :
    simplicialHomology f2_edge_twoVertices (ZMod 2) 0 ≃ₗ[ZMod 2]
      Chain f2_edge_twoVertices (ZMod 2) 0 :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((simplicialChainComplex f2_edge_twoVertices (ZMod 2)).sc 0)
    f2_edgeTwo_short_f_zero f2_edgeTwo_short_g_zero).homologyIso.toLinearEquiv

private theorem f2_edge_H0_stage0 :
    Module.finrank (ZMod 2)
      ((simplicialHomologyPModule (ZMod 2) prepEdgeSource.gradeFiltration 0).obj f2_edge_i0) = 1 := by
  rw [simplicialHomologyPModule_obj, f2_edge_stage0]
  exact (simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).finrank_eq.trans
    (Module.finrank_self (ZMod 2))

private theorem f2_edge_H0_stage1 :
    Module.finrank (ZMod 2)
      ((simplicialHomologyPModule (ZMod 2) prepEdgeSource.gradeFiltration 0).obj f2_edge_i1) = 2 := by
  rw [simplicialHomologyPModule_obj, f2_edge_stage1]
  rw [f2_edgeTwoH0Equiv.finrank_eq]
  rw [Module.finrank_finsupp_self]
  exact f2_edgeTwo_face0_card

private def f2_edge_vertex (i : Fin 2) : Face prepEdgeK 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 2)).Nonempty; simp, by simp⟩

private def f2_edge_face : Face prepEdgeK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 2)).Nonempty; decide, by decide⟩

private theorem f2_edge_vertex_bijective : Function.Bijective f2_edge_vertex := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> first | rfl | simp [f2_edge_vertex] at hv
  · intro σ
    have hc : σ.1 = {(0 : Fin 2)} ∨ σ.1 = {(1 : Fin 2)} := by
      have h : ∀ t : Finset (Fin 2), t.card = 1 →
          t = {0} ∨ t = {1} := by decide
      exact h σ.1 σ.2.2
    rcases hc with hc | hc
    · exact ⟨0, Subtype.ext (by simpa [f2_edge_vertex] using hc.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [f2_edge_vertex] using hc.symm)⟩

private theorem f2_edge_face_unique (σ : Face prepEdgeK 1) : σ = f2_edge_face := by
  apply Subtype.ext
  have h : ∀ t : Finset (Fin 2), t.card = 2 → t = {0, 1} := by decide
  exact h σ.1 σ.2.2

private theorem f2_edge_face_orderEmb :
    f2_edge_face.1.orderEmbOfFin f2_edge_face.2.2 =
      Fin.castLEOrderEmb (by decide : 2 ≤ 2) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [f2_edge_face]

private theorem f2_edge_deleted0 : deletedFace prepEdgeK 0 f2_edge_face 0 = f2_edge_vertex 1 := by
  apply Subtype.ext
  change f2_edge_face.1.erase (f2_edge_face.1.orderEmbOfFin f2_edge_face.2.2 0) =
    (f2_edge_vertex 1).1
  rw [f2_edge_face_orderEmb]
  decide

private theorem f2_edge_deleted1 : deletedFace prepEdgeK 0 f2_edge_face 1 = f2_edge_vertex 0 := by
  apply Subtype.ext
  change f2_edge_face.1.erase (f2_edge_face.1.orderEmbOfFin f2_edge_face.2.2 1) =
    (f2_edge_vertex 0).1
  rw [f2_edge_face_orderEmb]
  decide

private theorem f2_edge_boundary (a : ZMod 2) :
    boundary prepEdgeK (ZMod 2) 0 (Finsupp.single f2_edge_face a) =
      Finsupp.single (f2_edge_vertex 1) a - Finsupp.single (f2_edge_vertex 0) a := by
  rw [boundary_single]
  simp only [Fin.sum_univ_succ, f2_edge_deleted0]
  have hdel : deletedFace prepEdgeK 0 f2_edge_face (Fin.succ 0) = f2_edge_vertex 0 := by
    simpa using f2_edge_deleted1
  rw [hdel]
  norm_num
  rw [sub_eq_add_neg]

private theorem f2_edge_vertex_ne : f2_edge_vertex 0 ≠ f2_edge_vertex 1 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [f2_edge_vertex] at hv

private theorem f2_edge_face0_card : Fintype.card (Face prepEdgeK 0) = 2 := by
  exact Fintype.card_congr (Equiv.ofBijective f2_edge_vertex f2_edge_vertex_bijective).symm

private theorem f2_edge_face1_card : Fintype.card (Face prepEdgeK 1) = 1 := by
  decide

private theorem f2_edge_chain0_finrank :
    Module.finrank (ZMod 2) (Chain prepEdgeK (ZMod 2) 0) = 2 := by
  rw [Module.finrank_finsupp_self]
  exact f2_edge_face0_card

private theorem f2_edge_chain1_finrank :
    Module.finrank (ZMod 2) (Chain prepEdgeK (ZMod 2) 1) = 1 := by
  rw [Module.finrank_finsupp_self]
  exact f2_edge_face1_card

private theorem f2_edge_boundary_nonzero :
    boundary prepEdgeK (ZMod 2) 0 (Finsupp.single f2_edge_face 1) ≠ 0 := by
  intro h
  have hc := congrArg (fun c : Chain prepEdgeK (ZMod 2) 0 => c (f2_edge_vertex 1)) h
  rw [f2_edge_boundary] at hc
  simp [f2_edge_vertex_ne.symm] at hc

private theorem f2_edge_boundaries_finrank :
    Module.finrank (ZMod 2) (simplicialBoundaries prepEdgeK (ZMod 2) 0) = 1 := by
  let S := (simplicialChainComplex prepEdgeK (ZMod 2)).sc 0
  let : FiniteDimensional (ZMod 2) (↑S.X₁) := by
    change FiniteDimensional (ZMod 2)
      (Chain prepEdgeK (ZMod 2) ((ComplexShape.down ℕ).prev 0))
    rw [ChainComplex.prev]
    exact finiteDimensional_finsupp
  let : FiniteDimensional (ZMod 2) (LinearMap.range S.moduleCatToCycles) :=
    inferInstance
  have hpos : 0 < Module.finrank (ZMod 2)
      (LinearMap.range S.moduleCatToCycles) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    let z : simplicialCycles prepEdgeK (ZMod 2) 0 :=
      ⟨boundary prepEdgeK (ZMod 2) 0 (Finsupp.single f2_edge_face 1), by
        rw [simplicialCycles_zero]; trivial⟩
    have hz : z ∈ simplicialBoundaries prepEdgeK (ZMod 2) 0 :=
      (mem_simplicialBoundaries_iff (ZMod 2) prepEdgeK 0 z).2
        ⟨Finsupp.single f2_edge_face 1, rfl⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    intro hz
    have hc : z = 0 := congrArg Subtype.val hz
    apply f2_edge_boundary_nonzero
    exact congrArg (fun t : simplicialCycles prepEdgeK (ZMod 2) 0 =>
      (t : Chain prepEdgeK (ZMod 2) 0)) hc
  have hle := LinearMap.finrank_range_le S.moduleCatToCycles
  have hdim := f2_edge_chain1_finrank
  have hsource : Module.finrank (ZMod 2) (↑S.X₁) = 1 := by
    change Module.finrank (ZMod 2)
      (Chain prepEdgeK (ZMod 2) ((ComplexShape.down ℕ).prev 0)) = 1
    rw [ChainComplex.prev]
    exact hdim
  rw [hsource] at hle
  change Module.finrank (ZMod 2) (LinearMap.range S.moduleCatToCycles) = 1
  omega

private theorem f2_edge_H0_stage2 :
    Module.finrank (ZMod 2)
      ((simplicialHomologyPModule (ZMod 2) prepEdgeSource.gradeFiltration 0).obj f2_edge_i2) = 1 := by
  rw [simplicialHomologyPModule_obj, f2_edge_stage2]
  let : Finite (Face prepEdgeK 0) := inferInstance
  let : FiniteDimensional (ZMod 2) (Chain prepEdgeK (ZMod 2) 0) :=
    finiteDimensional_finsupp
  let : FiniteDimensional (ZMod 2) (simplicialCycles prepEdgeK (ZMod 2) 0) :=
    inferInstance
  let : HasQuotient (simplicialCycles prepEdgeK (ZMod 2) 0)
      (Submodule (ZMod 2) (simplicialCycles prepEdgeK (ZMod 2) 0)) :=
    Submodule.hasQuotient (R := ZMod 2) (M := simplicialCycles prepEdgeK (ZMod 2) 0)
  change Module.finrank (ZMod 2)
    ((simplicialChainComplex prepEdgeK (ZMod 2)).homology 0) = 1
  rw [(homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex prepEdgeK (ZMod 2)) 0).toLinearEquiv.finrank_eq]
  change Module.finrank (ZMod 2)
    (simplicialCycles prepEdgeK (ZMod 2) 0 ⧸ simplicialBoundaries prepEdgeK (ZMod 2) 0) = 1
  have hq : Module.finrank (ZMod 2)
      (simplicialCycles prepEdgeK (ZMod 2) 0 ⧸ simplicialBoundaries prepEdgeK (ZMod 2) 0) +
      Module.finrank (ZMod 2) (simplicialBoundaries prepEdgeK (ZMod 2) 0) =
      Module.finrank (ZMod 2) (simplicialCycles prepEdgeK (ZMod 2) 0) := by
    exact Submodule.finrank_quotient_add_finrank _
  have hc : Module.finrank (ZMod 2) (simplicialCycles prepEdgeK (ZMod 2) 0) = 2 := by
    rw [simplicialCycles_zero, finrank_top]
    exact f2_edge_chain0_finrank
  have hb := f2_edge_boundaries_finrank
  omega

private noncomputable def f2_edge_coeffSum :
    Chain prepEdgeK (ZMod 2) 0 →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.lsum (ZMod 2) (fun _ => LinearMap.id)

private theorem f2_edge_coeffSum_single (i : Fin 2) (a : ZMod 2) :
    f2_edge_coeffSum (Finsupp.single (f2_edge_vertex i) a) = a := by
  exact Finsupp.lsum_single (ZMod 2)
    (fun _ : Face prepEdgeK 0 => LinearMap.id) _ _

private theorem f2_edge_coeffSum_boundary :
    f2_edge_coeffSum.comp (boundary prepEdgeK (ZMod 2) 0) = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  have hσ : σ = f2_edge_face := f2_edge_face_unique σ
  subst σ
  change f2_edge_coeffSum (boundary prepEdgeK (ZMod 2) 0
      (Finsupp.single f2_edge_face a)) = 0
  rw [f2_edge_boundary, map_sub, f2_edge_coeffSum_single, f2_edge_coeffSum_single]
  exact sub_self a

private noncomputable def f2_edge_vertex0_cycle : simplicialCycles prepEdgeK (ZMod 2) 0 :=
  ⟨Finsupp.single (f2_edge_vertex 0) 1, by rw [simplicialCycles_zero]; trivial⟩

private theorem f2_edge_vertex0_not_boundary :
    f2_edge_vertex0_cycle ∉ simplicialBoundaries prepEdgeK (ZMod 2) 0 := by
  intro hz
  obtain ⟨c, hc⟩ :=
    (mem_simplicialBoundaries_iff (ZMod 2) prepEdgeK 0 f2_edge_vertex0_cycle).1 hz
  have hs := congrArg f2_edge_coeffSum hc
  have hzero := congrArg (fun f : Chain prepEdgeK (ZMod 2) 1 →ₗ[ZMod 2] ZMod 2 => f c)
    f2_edge_coeffSum_boundary
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hzero
  rw [hzero] at hs
  change 0 = f2_edge_coeffSum (Finsupp.single (f2_edge_vertex 0) 1) at hs
  rw [f2_edge_coeffSum_single] at hs
  exact one_ne_zero hs.symm

private theorem f2_edge_vertex0_class_nonzero :
    (simplicialBoundaries prepEdgeK (ZMod 2) 0).mkQ f2_edge_vertex0_cycle ≠ 0 := by
  intro hz
  exact f2_edge_vertex0_not_boundary
    ((Submodule.Quotient.mk_eq_zero _).1 hz)

private theorem f2_edge_singleton_le : singletonFace (0 : Fin 2) ≤ prepEdgeK := by
  intro s hs
  have h : s = ({0} : Finset (Fin 2)) :=
    (mem_singletonFace_iff 0 s).1 hs
  subst s
  change ({0} : Finset (Fin 2)).Nonempty
  simp

private theorem f2_edge_two_le : f2_edge_twoVertices ≤ prepEdgeK := by
  intro s hs
  rcases (show s = ({0} : Finset (Fin 2)) ∨ s = {1} from hs) with h | h
  · subst s
    change ({0} : Finset (Fin 2)).Nonempty
    simp
  · subst s
    change ({1} : Finset (Fin 2)).Nonempty
    simp

private theorem f2_edge_singleton_two : singletonFace (0 : Fin 2) ≤ f2_edge_twoVertices :=
  le_sup_left

private noncomputable def f2_edge_source_cycle :
    simplicialCycles (singletonFace (0 : Fin 2)) (ZMod 2) 0 :=
  ⟨Finsupp.single (singletonVertex (0 : Fin 2)) 1, by
    rw [simplicialCycles_zero]; trivial⟩

private theorem f2_edge_cycle_inclusion :
    simplicialCycleIncl (ZMod 2) f2_edge_singleton_le 0 f2_edge_source_cycle =
      f2_edge_vertex0_cycle := by
  apply Subtype.ext
  rw [simplicialCycleIncl_coe]
  change chainIncl (ZMod 2) f2_edge_singleton_le 0
      (Finsupp.single (singletonVertex (0 : Fin 2)) 1) =
    Finsupp.single (f2_edge_vertex 0) 1
  rw [chainIncl_single]
  have hface : faceIncl f2_edge_singleton_le 0 (singletonVertex (0 : Fin 2)) =
      f2_edge_vertex 0 := Subtype.ext rfl
  rw [hface]

private theorem f2_edge_singleton_map_nonzero :
    (simplicialHomologyIncl (ZMod 2) f2_edge_singleton_le 0).hom ≠ 0 := by
  let : HasQuotient (simplicialCycles (singletonFace (0 : Fin 2)) (ZMod 2) 0)
      (Submodule (ZMod 2)
        (simplicialCycles (singletonFace (0 : Fin 2)) (ZMod 2) 0)) :=
    Submodule.hasQuotient (R := ZMod 2)
      (M := simplicialCycles (singletonFace (0 : Fin 2)) (ZMod 2) 0)
  let : HasQuotient (simplicialCycles prepEdgeK (ZMod 2) 0)
      (Submodule (ZMod 2) (simplicialCycles prepEdgeK (ZMod 2) 0)) :=
    Submodule.hasQuotient (R := ZMod 2)
      (M := simplicialCycles prepEdgeK (ZMod 2) 0)
  let q := (simplicialBoundaries (singletonFace (0 : Fin 2)) (ZMod 2) 0).mkQ
    f2_edge_source_cycle
  let e0 := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex (singletonFace (0 : Fin 2)) (ZMod 2)) 0).toLinearEquiv
  let e1 := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex prepEdgeK (ZMod 2)) 0).toLinearEquiv
  let x := e0.symm q
  have hnat : e1 ((simplicialHomologyIncl (ZMod 2) f2_edge_singleton_le 0).hom x) =
      (simplicialBoundaries prepEdgeK (ZMod 2) 0).mkQ f2_edge_vertex0_cycle := by
    have hh := simplicialHomologyIncl_quotient_naturality
      (ZMod 2) f2_edge_singleton_le 0
    have hx := congrArg (fun f : simplicialHomology
      (singletonFace (0 : Fin 2)) (ZMod 2) 0 ⟶
      ModuleCat.of (ZMod 2) (simplicialCycles prepEdgeK (ZMod 2) 0 ⧸
        simplicialBoundaries prepEdgeK (ZMod 2) 0) => f.hom x) hh
    change e1 ((simplicialHomologyIncl (ZMod 2) f2_edge_singleton_le 0).hom x) =
      simplicialQuotientIncl (ZMod 2) f2_edge_singleton_le 0 (e0 x) at hx
    rw [show e0 x = q from e0.apply_symm_apply q,
      simplicialQuotientIncl_mkQ, f2_edge_cycle_inclusion] at hx
    exact hx
  intro hz
  rw [hz] at hnat
  change e1 (0 : simplicialHomology prepEdgeK (ZMod 2) 0) = _ at hnat
  have he : e1 (0 : simplicialHomology prepEdgeK (ZMod 2) 0) = 0 := e1.map_zero
  exact f2_edge_vertex0_class_nonzero (hnat.symm.trans he)

private theorem f2_edge_map_comp :
    simplicialHomologyIncl (ZMod 2) f2_edge_singleton_le 0 =
      simplicialHomologyIncl (ZMod 2) f2_edge_singleton_two 0 ≫
        simplicialHomologyIncl (ZMod 2) f2_edge_two_le 0 := by
  have h : f2_edge_singleton_le = f2_edge_singleton_two.trans f2_edge_two_le :=
    Subsingleton.elim _ _
  rw [h]
  exact simplicialHomologyIncl_comp (ZMod 2) f2_edge_singleton_two f2_edge_two_le 0

private theorem f2_edge_singleton_two_nonzero :
    (simplicialHomologyIncl (ZMod 2) f2_edge_singleton_two 0).hom ≠ 0 := by
  intro hz
  apply f2_edge_singleton_map_nonzero
  have hc := congrArg (fun f : simplicialHomology
    (singletonFace (0 : Fin 2)) (ZMod 2) 0 ⟶
    simplicialHomology prepEdgeK (ZMod 2) 0 => f.hom) f2_edge_map_comp
  simpa [hz] using hc

private theorem f2_edge_two_full_nonzero :
    (simplicialHomologyIncl (ZMod 2) f2_edge_two_le 0).hom ≠ 0 := by
  intro hz
  apply f2_edge_singleton_map_nonzero
  have hc := congrArg (fun f : simplicialHomology
    (singletonFace (0 : Fin 2)) (ZMod 2) 0 ⟶
    simplicialHomology prepEdgeK (ZMod 2) 0 => f.hom) f2_edge_map_comp
  simpa [hz] using hc

private theorem f2_rank_one_of_nonzero
    {A B : Type} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup B] [Module (ZMod 2) B]
    [FiniteDimensional (ZMod 2) A]
    (hA : Module.finrank (ZMod 2) A = 1)
    (f : A →ₗ[ZMod 2] B) (hf : f ≠ 0) :
    Module.finrank (ZMod 2) (LinearMap.range f) = 1 := by
  have hx : ∃ x : A, f x ≠ 0 := by
    by_contra h
    apply hf
    ext x
    simpa using (not_not.mp (not_exists.mp h x))
  obtain ⟨x, hx⟩ := hx
  have hpos : 0 < Module.finrank (ZMod 2) (LinearMap.range f) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨f x, ⟨x, rfl⟩⟩, ?_⟩
    exact fun he => hx (congrArg Subtype.val he)
  have hle := LinearMap.finrank_range_le f
  rw [hA] at hle
  omega

private theorem f2_edge_rank_01 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) f2_edge_singleton_two 0).hom) = 1 := by
  exact f2_rank_one_of_nonzero
    ((simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).finrank_eq.trans
      (Module.finrank_self (ZMod 2))) _ f2_edge_singleton_two_nonzero

private theorem f2_edge_rank_02 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) f2_edge_singleton_le 0).hom) = 1 := by
  exact f2_rank_one_of_nonzero
    ((simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).finrank_eq.trans
      (Module.finrank_self (ZMod 2))) _ f2_edge_singleton_map_nonzero

private theorem f2_edge_rank_12 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) f2_edge_two_le 0).hom) = 1 := by
  have hle := LinearMap.finrank_range_le
    (simplicialHomologyIncl (ZMod 2) f2_edge_two_le 0).hom
  have hpos : 0 < Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) f2_edge_two_le 0).hom) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    have hx : ∃ x, (simplicialHomologyIncl (ZMod 2) f2_edge_two_le 0).hom x ≠ 0 := by
      by_contra h
      apply f2_edge_two_full_nonzero
      ext x
      simpa using (not_not.mp (not_exists.mp h x))
    obtain ⟨x, hx⟩ := hx
    refine ⟨⟨_, ⟨x, rfl⟩⟩, ?_⟩
    exact fun he => hx (congrArg Subtype.val he)
  have htarget : Module.finrank (ZMod 2)
      (simplicialHomology prepEdgeK (ZMod 2) 0) = 1 := by
    have hh := f2_edge_H0_stage2
    change Module.finrank (ZMod 2)
      (simplicialHomology (prepEdgeSource.gradeFiltration f2_edge_i2) (ZMod 2) 0) = 1 at hh
    rw [f2_edge_stage2] at hh
    exact hh
  have hle' := Submodule.finrank_le
    (LinearMap.range (simplicialHomologyIncl (ZMod 2) f2_edge_two_le 0).hom)
  rw [htarget] at hle'
  omega

private theorem f2_edge_rank_congr {A B A' B' : PreAbstractSimplicialComplex (Fin 2)}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) h 0).hom) =
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) h' 0).hom) := by
  cases hA
  cases hB
  rfl

private theorem f2_edge_grade_rank_00 (h : f2_edge_i0 ≤ f2_edge_i0) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      prepEdgeSource.gradeFiltration 0) f2_edge_i0 f2_edge_i0 h = 1 := by
  unfold structureMapRank
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  exact f2_edge_H0_stage0

private theorem f2_edge_grade_rank_11 (h : f2_edge_i1 ≤ f2_edge_i1) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      prepEdgeSource.gradeFiltration 0) f2_edge_i1 f2_edge_i1 h = 2 := by
  unfold structureMapRank
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  exact f2_edge_H0_stage1

private theorem f2_edge_grade_rank_22 (h : f2_edge_i2 ≤ f2_edge_i2) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      prepEdgeSource.gradeFiltration 0) f2_edge_i2 f2_edge_i2 h = 1 := by
  unfold structureMapRank
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  exact f2_edge_H0_stage2

private theorem f2_edge_grade_rank_01 (h : f2_edge_i0 ≤ f2_edge_i1) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      prepEdgeSource.gradeFiltration 0) f2_edge_i0 f2_edge_i1 h = 1 := by
  change Module.finrank (ZMod 2) (LinearMap.range
    (simplicialHomologyIncl (ZMod 2) (prepEdgeSource.gradeFiltration.monotone h) 0).hom) = 1
  exact (f2_edge_rank_congr f2_edge_stage0 f2_edge_stage1 _ f2_edge_singleton_two).trans
    f2_edge_rank_01

private theorem f2_edge_grade_rank_02 (h : f2_edge_i0 ≤ f2_edge_i2) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      prepEdgeSource.gradeFiltration 0) f2_edge_i0 f2_edge_i2 h = 1 := by
  change Module.finrank (ZMod 2) (LinearMap.range
    (simplicialHomologyIncl (ZMod 2) (prepEdgeSource.gradeFiltration.monotone h) 0).hom) = 1
  exact (f2_edge_rank_congr f2_edge_stage0 f2_edge_stage2 _ f2_edge_singleton_le).trans
    f2_edge_rank_02

private theorem f2_edge_grade_rank_12 (h : f2_edge_i1 ≤ f2_edge_i2) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      prepEdgeSource.gradeFiltration 0) f2_edge_i1 f2_edge_i2 h = 1 := by
  change Module.finrank (ZMod 2) (LinearMap.range
    (simplicialHomologyIncl (ZMod 2) (prepEdgeSource.gradeFiltration.monotone h) 0).hom) = 1
  exact (f2_edge_rank_congr f2_edge_stage1 f2_edge_stage2 _ f2_edge_two_le).trans
    f2_edge_rank_12

private noncomputable def f2_edge_bar03 : FiniteInterval prepEdgeSource.criticalValues.card :=
  ⟨0, 3, by omega, by rw [f2_edge_card]⟩

private noncomputable def f2_edge_bar12 : FiniteInterval prepEdgeSource.criticalValues.card :=
  ⟨1, 2, by omega, by rw [f2_edge_card]; decide⟩

private theorem f2_edge_barcode :
    gradeHomologyBarcode (ZMod 2) prepEdgeSource 0 =
      ({f2_edge_bar03, f2_edge_bar12} :
        Multiset (FiniteInterval prepEdgeSource.criticalValues.card)) := by
  calc
    gradeHomologyBarcode (ZMod 2) prepEdgeSource 0 =
        rankBarcode (barcodeModule (k := ZMod 2)
          ({f2_edge_bar03, f2_edge_bar12} :
            Multiset (FiniteInterval prepEdgeSource.criticalValues.card))) := by
      apply (rankBarcode_eq_iff
        (simplicialHomologyPModule (ZMod 2) prepEdgeSource.gradeFiltration 0)
        (barcodeModule (k := ZMod 2)
          ({f2_edge_bar03, f2_edge_bar12} :
            Multiset (FiniteInterval prepEdgeSource.criticalValues.card)))).mpr
      intro i j hij
      have hi : i = f2_edge_i0 ∨ i = f2_edge_i1 ∨ i = f2_edge_i2 := by
        have hv := i.isLt
        have hc := f2_edge_card
        rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      have hj : j = f2_edge_i0 ∨ j = f2_edge_i1 ∨ j = f2_edge_i2 := by
        have hv := j.isLt
        have hc := f2_edge_card
        rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 by omega) with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
      all_goals simp only [f2_edge_i0, f2_edge_i1, f2_edge_i2, Fin.mk_le_mk] at hij
      all_goals simp at hij
      all_goals rw [rank_barcodeMap]
      all_goals first
        | rw [f2_edge_grade_rank_00]
        | rw [f2_edge_grade_rank_01]
        | rw [f2_edge_grade_rank_02]
        | rw [f2_edge_grade_rank_11]
        | rw [f2_edge_grade_rank_12]
        | rw [f2_edge_grade_rank_22]
      all_goals
        rw [show ({f2_edge_bar03, f2_edge_bar12} :
          Multiset (FiniteInterval prepEdgeSource.criticalValues.card)) =
            f2_edge_bar03 ::ₘ f2_edge_bar12 ::ₘ 0 by rfl,
          Multiset.countP_cons, Multiset.countP_cons]
        simp [f2_edge_bar03, f2_edge_bar12, f2_edge_i0, f2_edge_i1, f2_edge_i2]
      all_goals rfl
    _ = _ := rankBarcode_barcodeModule _

private theorem f2_edge_points :
    (dgm (ZMod 2) prepEdgeSource 0).points =
      ({((2 : ℚ), (⊤ : WithTop ℚ)), ((5 : ℚ), (9 : WithTop ℚ))} :
        Multiset (ℚ × WithTop ℚ)) := by
  rw [dgm, f2_edge_barcode]
  change ({f2_edge_bar03, f2_edge_bar12} :
    Multiset (FiniteInterval prepEdgeSource.criticalValues.card)).map
      (fun I =>
        (prepEdgeSource.criticalValue
          ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
          if hd : I.death < prepEdgeSource.criticalValues.card then
            (prepEdgeSource.criticalValue ⟨I.death, hd⟩ : WithTop ℚ)
          else (⊤ : WithTop ℚ))) = _
  simp [f2_edge_bar03, f2_edge_bar12, f2_edge_card]
  have hc0 : ∀ h : 0 < prepEdgeSource.criticalValues.card,
      prepEdgeSource.criticalValue ⟨0, h⟩ = 2 := by
    intro h
    have he : (⟨0, h⟩ : Fin prepEdgeSource.criticalValues.card) = f2_edge_i0 := Fin.ext rfl
    rw [he]
    exact f2_edge_critical.1
  have hc1 : ∀ h : 1 < prepEdgeSource.criticalValues.card,
      prepEdgeSource.criticalValue ⟨1, h⟩ = 5 := by
    intro h
    have he : (⟨1, h⟩ : Fin prepEdgeSource.criticalValues.card) = f2_edge_i1 := Fin.ext rfl
    rw [he]
    exact f2_edge_critical.2.1
  have hc2 : ∀ h : 2 < prepEdgeSource.criticalValues.card,
      prepEdgeSource.criticalValue ⟨2, h⟩ = 9 := by
    intro h
    have he : (⟨2, h⟩ : Fin prepEdgeSource.criticalValues.card) = f2_edge_i2 := Fin.ext rfl
    rw [he]
    exact f2_edge_critical.2.2
  simp [hc0, hc1, hc2]

private theorem f2_edge_incl_eq_square {A B A' B' : PreAbstractSimplicialComplex (Fin 2)}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') :
    simplicialHomologyIncl (ZMod 2) h 0 ≫
        eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0) hB) =
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0) hA) ≫
        simplicialHomologyIncl (ZMod 2) h' 0 := by
  subst A'
  subst B'
  simp

/-- F2 computes the target using the attained-only F3 specialization. -/
private theorem f2_target_points :
    (dgm (ZMod 2) prepEdgeTarget 0).points =
      ({((3 : ℚ), (⊤ : WithTop ℚ)), ((6 : ℚ), (10 : WithTop ℚ))} :
        Multiset (ℚ × WithTop ℚ)) := by
  rw [f3_points_map, f2_edge_points]
  norm_num [prepSupportPhi]

/-- F2 records both computed actual diagrams alongside the points.map law. -/
private theorem f2_numerical_points_map :
    (dgm (ZMod 2) prepEdgeSource 0).points =
      ({((2 : ℚ), (⊤ : WithTop ℚ)), ((5 : ℚ), (9 : WithTop ℚ))} :
        Multiset (ℚ × WithTop ℚ)) ∧
    (dgm (ZMod 2) prepEdgeTarget 0).points =
      ({((3 : ℚ), (⊤ : WithTop ℚ)), ((6 : ℚ), (10 : WithTop ℚ))} :
        Multiset (ℚ × WithTop ℚ)) ∧
    (dgm (ZMod 2) prepEdgeTarget 0).points =
      (dgm (ZMod 2) prepEdgeSource 0).points.map
        (fun p => (prepSupportPhi p.1, WithTop.map prepSupportPhi p.2)) :=
  ⟨f2_edge_points, f2_target_points, f3_points_map 0⟩

/-- F2 consumes the common occurrence law alongside both numerical computations. -/
private theorem f2_numerical_common_endpoints :
    ∃ E : Multiset (TotalFace prepEdgeK × Option (TotalFace prepEdgeK)),
      (dgm (ZMod 2) prepEdgeSource 0).points =
        ({((2 : ℚ), (⊤ : WithTop ℚ)), ((5 : ℚ), (9 : WithTop ℚ))} :
          Multiset (ℚ × WithTop ℚ)) ∧
      (dgm (ZMod 2) prepEdgeTarget 0).points =
        ({((3 : ℚ), (⊤ : WithTop ℚ)), ((6 : ℚ), (10 : WithTop ℚ))} :
          Multiset (ℚ × WithTop ℚ)) ∧
      (dgm (ZMod 2) prepEdgeSource 0).points = E.map (fun p =>
        (prepEdgeSource.value p.1, p.2.elim (⊤ : WithTop ℚ)
          (fun t => (prepEdgeSource.value t : WithTop ℚ)))) ∧
      (dgm (ZMod 2) prepEdgeTarget 0).points = E.map (fun p =>
        (prepEdgeTarget.value p.1, p.2.elim (⊤ : WithTop ℚ)
          (fun t => (prepEdgeTarget.value t : WithTop ℚ)))) := by
  obtain ⟨E, hf, hg⟩ := f3_common_face_endpoints 0
  exact ⟨E, f2_edge_points, f2_target_points, hf, hg⟩

private theorem f2_matched_first : prepEdgeSource.sublevel 2 = prepEdgeTarget.sublevel 3 := by
  have h := f3_ordering.sublevel_eq prepEdgeV0
  simpa only [prepEdgeValues.1, prepEdgeValues.2.2.2.1] using h

private theorem f2_matched_second : prepEdgeSource.sublevel 5 = prepEdgeTarget.sublevel 6 := by
  have h := f3_ordering.sublevel_eq prepEdgeV1
  simpa only [prepEdgeValues.2.1, prepEdgeValues.2.2.2.2.1] using h

private theorem f2_matched_third : prepEdgeSource.sublevel 9 = prepEdgeTarget.sublevel 10 := by
  have h := f3_ordering.sublevel_eq prepEdgeE01
  simpa only [prepEdgeValues.2.2.1, prepEdgeValues.2.2.2.2.2] using h

/-- Actual equality-induced square, at matched first and second critical grades. -/
private theorem f2_matched_inclusion_square :
    simplicialHomologyIncl (ZMod 2)
        (prepEdgeSource.sublevel_mono (show (2 : ℚ) ≤ 5 by norm_num)) 0 ≫
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0) f2_matched_second) =
    eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0) f2_matched_first) ≫
      simplicialHomologyIncl (ZMod 2)
        (prepEdgeTarget.sublevel_mono (show (3 : ℚ) ≤ 6 by norm_num)) 0 :=
  f2_edge_incl_eq_square f2_matched_first f2_matched_second _ _

/-- Rank 1 into dimension 2 in the source filtration; dimensions do not determine the map. -/
private theorem f2_source_rank_dimension :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (prepEdgeSource.sublevel_mono (show (2 : ℚ) ≤ 5 by norm_num)) 0).hom) = 1 ∧
    Module.finrank (ZMod 2)
      (simplicialHomology (prepEdgeSource.sublevel 5) (ZMod 2) 0) = 2 := by
  constructor
  · exact (f2_edge_rank_congr
      (f2_edge_region0 2 le_rfl (by norm_num))
      (f2_edge_region1 5 le_rfl (by norm_num)) _ f2_edge_singleton_two).trans
        f2_edge_rank_01
  · have h := f2_edge_H0_stage1
    change Module.finrank (ZMod 2)
      (simplicialHomology (prepEdgeSource.gradeFiltration f2_edge_i1) (ZMod 2) 0) = 2 at h
    rw [f2_edge_stage1] at h
    rw [f2_edge_region1 5 le_rfl (by norm_num)]
    exact h

/-- The matched target has the same rank 1 inclusion and second-object dimension 2. -/
private theorem f2_target_rank_dimension :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (prepEdgeTarget.sublevel_mono (show (3 : ℚ) ≤ 6 by norm_num)) 0).hom) = 1 ∧
    Module.finrank (ZMod 2)
      (simplicialHomology (prepEdgeTarget.sublevel 6) (ZMod 2) 0) = 2 := by
  constructor
  · exact (f2_edge_rank_congr f2_matched_first f2_matched_second _ _).symm.trans
      f2_source_rank_dimension.1
  · rw [← f2_matched_second]
    exact f2_source_rank_dimension.2

/-- Actual inclusion composition through all three source critical grades. -/
private theorem f2_source_inclusion_composition :
    simplicialHomologyIncl (ZMod 2)
        (prepEdgeSource.sublevel_mono (show (2 : ℚ) ≤ 9 by norm_num)) 0 =
      simplicialHomologyIncl (ZMod 2)
          (prepEdgeSource.sublevel_mono (show (2 : ℚ) ≤ 5 by norm_num)) 0 ≫
        simplicialHomologyIncl (ZMod 2)
          (prepEdgeSource.sublevel_mono (show (5 : ℚ) ≤ 9 by norm_num)) 0 := by
  simpa using simplicialHomologyIncl_comp (ZMod 2)
    (prepEdgeSource.sublevel_mono (show (2 : ℚ) ≤ 5 by norm_num))
    (prepEdgeSource.sublevel_mono (show (5 : ℚ) ≤ 9 by norm_num)) 0

/-- Actual inclusion composition through all three target critical grades. -/
private theorem f2_target_inclusion_composition :
    simplicialHomologyIncl (ZMod 2)
        (prepEdgeTarget.sublevel_mono (show (3 : ℚ) ≤ 10 by norm_num)) 0 =
      simplicialHomologyIncl (ZMod 2)
          (prepEdgeTarget.sublevel_mono (show (3 : ℚ) ≤ 6 by norm_num)) 0 ≫
        simplicialHomologyIncl (ZMod 2)
          (prepEdgeTarget.sublevel_mono (show (6 : ℚ) ≤ 10 by norm_num)) 0 := by
  simpa using simplicialHomologyIncl_comp (ZMod 2)
    (prepEdgeTarget.sublevel_mono (show (3 : ℚ) ≤ 6 by norm_num))
    (prepEdgeTarget.sublevel_mono (show (6 : ℚ) ≤ 10 by norm_num)) 0

/-- The composed inclusion commutes with the attained first/third-grade identification. -/
private theorem f2_matched_composition_square :
    (simplicialHomologyIncl (ZMod 2)
        (prepEdgeSource.sublevel_mono (show (2 : ℚ) ≤ 5 by norm_num)) 0 ≫
      simplicialHomologyIncl (ZMod 2)
        (prepEdgeSource.sublevel_mono (show (5 : ℚ) ≤ 9 by norm_num)) 0) ≫
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0) f2_matched_third) =
    eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0) f2_matched_first) ≫
      (simplicialHomologyIncl (ZMod 2)
          (prepEdgeTarget.sublevel_mono (show (3 : ℚ) ≤ 6 by norm_num)) 0 ≫
        simplicialHomologyIncl (ZMod 2)
          (prepEdgeTarget.sublevel_mono (show (6 : ℚ) ≤ 10 by norm_num)) 0) := by
  rw [← f2_source_inclusion_composition, ← f2_target_inclusion_composition]
  exact f2_edge_incl_eq_square f2_matched_first f2_matched_third _ _

end TDA.Persistence
